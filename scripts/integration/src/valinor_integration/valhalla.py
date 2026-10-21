"""Runs stock C++ Valhalla in Docker (with docker-py) against a tile extract."""

from __future__ import annotations

import io
import json
import logging
import subprocess
import tarfile
import tempfile
import time
from pathlib import Path
from types import TracebackType
from typing import IO, Any

import docker
import docker.errors
import requests
from docker.models.containers import Container

from valinor_integration.errors import HarnessError
from valinor_integration.settings import Settings

log = logging.getLogger(__name__)

#: The directory in the container that holds the extract and the config.
CONTAINER_DATA_DIR = "/valinor"
CONTAINER_EXTRACT = f"{CONTAINER_DATA_DIR}/tiles.tar"
CONTAINER_CONFIG = f"{CONTAINER_DATA_DIR}/valhalla.json"
#: The port of valhalla_service in the container.
SERVICE_PORT = 8002

READINESS_TIMEOUT_SECONDS = 90
REQUEST_TIMEOUT_SECONDS = 30


def connect() -> docker.DockerClient:
    """Connects to the Docker daemon.

    If the default connection fails, this uses the endpoint of the current Docker CLI context,
    which docker-py does not read (for example, the socket of colima).
    """
    try:
        client = docker.from_env()
        client.ping()
        return client
    except docker.errors.DockerException as default_error:
        try:
            endpoint = subprocess.run(
                ["docker", "context", "inspect", "--format", "{{.Endpoints.docker.Host}}"],
                check=True,
                capture_output=True,
                text=True,
            ).stdout.strip()
            client = docker.DockerClient(base_url=endpoint)
            client.ping()
            log.info("connected to Docker through the CLI context endpoint %s", endpoint)
            return client
        except (OSError, subprocess.CalledProcessError, docker.errors.DockerException):
            raise HarnessError(
                f"cannot connect to Docker ({default_error}); is the Docker daemon running?"
            ) from None


def ensure_image(client: docker.DockerClient, settings: Settings) -> None:
    """Pulls ``latest`` every time, and a pinned tag only if it is not present."""
    if not settings.is_pinned:
        log.warning(
            "VALHALLA_VERSION is not set, so the harness uses %s; "
            "set VALHALLA_VERSION to pin a release",
            settings.image_ref,
        )
    else:
        try:
            client.images.get(settings.image_ref)
            return
        except docker.errors.ImageNotFound:
            pass

    log.info("pulling %s", settings.image_ref)
    try:
        client.images.pull(settings.valhalla_image, tag=settings.image_tag)
    except docker.errors.APIError as e:
        raise HarnessError(f"cannot pull {settings.image_ref}: {e}") from None


def build_config(client: docker.DockerClient, image: str) -> dict[str, Any]:
    """Makes a config for the extract at ``CONTAINER_EXTRACT`` with the image's own tool."""
    try:
        output = client.containers.run(
            image,
            entrypoint="valhalla_build_config",
            command=["--mjolnir-tile-extract", CONTAINER_EXTRACT],
            remove=True,
            stdout=True,
            stderr=False,
        )
    except docker.errors.DockerException as e:
        raise HarnessError(f"valhalla_build_config failed: {e}") from None
    config = json.loads(output)

    mjolnir = config["mjolnir"]
    mjolnir["tile_extract"] = CONTAINER_EXTRACT
    # Do not enable shortcut_caching: Valhalla then asserts at startup that every
    # level 0 and level 1 tile exists, so a partial extract fails to start.
    mjolnir["shortcut_caching"] = False
    return config


class ValhallaServer:
    """A ``valhalla_service`` container which serves one extract.

    Use it as a context manager: the container starts on entry,
    and is removed on exit (also after an error or Ctrl-C).
    Call ``logs`` before the exit to keep the logs.
    """

    def __init__(
        self,
        client: docker.DockerClient,
        image: str,
        name: str,
        extract: Path,
        config: dict[str, Any],
        host_port: int | None = None,
    ) -> None:
        """``host_port`` ``None`` lets Docker choose a free port."""
        self.client = client
        self.image = image
        self.name = name
        self.extract = extract
        self.config = config
        self.host_port = host_port
        self.container_name = f"valinor-integration-{name}"
        self._container: Container | None = None
        self.base_url = ""

    def __enter__(self) -> ValhallaServer:
        try:
            self._start()
        except BaseException:
            self._remove()
            raise
        return self

    def __exit__(
        self,
        exc_type: type[BaseException] | None,
        exc: BaseException | None,
        traceback: TracebackType | None,
    ) -> None:
        self._remove()

    def _start(self) -> None:
        self._remove_stale_container()
        log.info("starting valhalla_service for the %s extract", self.name)
        self._container = self.client.containers.create(
            self.image,
            name=self.container_name,
            entrypoint="valhalla_service",
            command=[CONTAINER_CONFIG, "1"],
            ports={f"{SERVICE_PORT}/tcp": self.host_port},
        )
        # Copy the data in place of a bind mount, which fails for a directory
        # that the Docker VM does not share (such as /tmp with colima).
        with tempfile.TemporaryFile() as archive:
            self._write_data_archive(archive)
            archive.seek(0)
            if not self._container.put_archive("/", archive):
                raise HarnessError(f"cannot copy the {self.name} extract into the container")
        self._container.start()

        self._container.reload()
        bindings = self._container.ports.get(f"{SERVICE_PORT}/tcp") or []
        if not bindings:
            raise HarnessError(f"Docker did not publish the port of the {self.name} container")
        self.base_url = f"http://localhost:{bindings[0]['HostPort']}"
        self._wait_until_ready()

    def _write_data_archive(self, archive: IO[bytes]) -> None:
        """Writes a tar archive with the extract and the config, in ``CONTAINER_DATA_DIR``."""
        with tarfile.open(fileobj=archive, mode="w") as tar:
            directory = tarfile.TarInfo(CONTAINER_DATA_DIR.lstrip("/"))
            directory.type = tarfile.DIRTYPE
            directory.mode = 0o755
            tar.addfile(directory)

            tar.add(self.extract, arcname=CONTAINER_EXTRACT.lstrip("/"), filter=_readable)

            config_bytes = json.dumps(self.config, indent=2).encode("utf-8")
            config_info = tarfile.TarInfo(CONTAINER_CONFIG.lstrip("/"))
            config_info.size = len(config_bytes)
            config_info.mode = 0o644
            tar.addfile(config_info, io.BytesIO(config_bytes))

    def _wait_until_ready(self) -> None:
        assert self._container is not None
        deadline = time.monotonic() + READINESS_TIMEOUT_SECONDS
        while time.monotonic() < deadline:
            try:
                status = requests.get(f"{self.base_url}/status", timeout=2)
                if status.ok:
                    version = status.json().get("version", "unknown")
                    log.info(
                        "the %s extract is served at %s (Valhalla %s)",
                        self.name,
                        self.base_url,
                        version,
                    )
                    return
            except (requests.RequestException, ValueError):
                pass
            self._container.reload()
            if self._container.status not in ("created", "running"):
                break
            time.sleep(0.5)

        raise HarnessError(
            f"valhalla_service did not become ready for the {self.name} extract; "
            f"logs:\n{self.logs()}"
        )

    def logs(self) -> str:
        if self._container is None:
            return ""
        return self._container.logs().decode("utf-8", errors="replace")

    def _remove_stale_container(self) -> None:
        """Removes a container with the same name, left by an earlier run that crashed."""
        try:
            self.client.containers.get(self.container_name).remove(force=True)
            log.info("removed the stale container %s", self.container_name)
        except docker.errors.NotFound:
            pass

    def _remove(self) -> None:
        if self._container is None:
            return
        try:
            self._container.remove(force=True)
        except docker.errors.NotFound:
            pass
        except docker.errors.APIError as e:
            log.warning("cannot remove the container %s: %s", self.container_name, e)
        self._container = None


def _readable(info: tarfile.TarInfo) -> tarfile.TarInfo:
    """Makes a file in the data archive readable by any user of the container."""
    info.mode = 0o644
    info.uid = info.gid = 0
    info.uname = info.gname = ""
    return info
