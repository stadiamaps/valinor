"""Settings of the harness, from environment variables.

Every setting has a default, so ``valinor-integration`` runs with no configuration.
See README.md for the variables.
"""

from __future__ import annotations

import os
from collections.abc import Mapping
from dataclasses import dataclass
from pathlib import Path

from valinor_integration.errors import HarnessError

DEFAULT_VALHALLA_IMAGE = "ghcr.io/valhalla/valhalla"
LATEST_TAG = "latest"
DEFAULT_SERVE_PORT = 8002

# This file is scripts/integration/src/valinor_integration/settings.py.
HARNESS_DIR = Path(__file__).resolve().parents[2]
REPO_ROOT = HARNESS_DIR.parents[1]

DEFAULT_FULL_EXTRACT = REPO_ROOT / "valhalla-graphtile" / "fixtures" / "andorra-tiles.tar"
DEFAULT_WORKDIR = REPO_ROOT / "target" / "integration"
DEFAULT_TILE_LIST = HARNESS_DIR / "sub-extract-tiles.txt"
DEFAULT_COLLECTION = HARNESS_DIR / "bruno"


@dataclass(frozen=True)
class Settings:
    """The settings which come from environment variables."""

    valhalla_image: str
    #: The image tag, or ``None`` to use ``latest``.
    valhalla_version: str | None
    valinor_cli: Path | None
    serve_port: int

    @property
    def image_tag(self) -> str:
        return self.valhalla_version or LATEST_TAG

    @property
    def image_ref(self) -> str:
        return f"{self.valhalla_image}:{self.image_tag}"

    @property
    def is_pinned(self) -> bool:
        return self.valhalla_version is not None

    @classmethod
    def from_env(cls, env: Mapping[str, str] | None = None) -> Settings:
        """Reads the settings from ``env`` (by default, the process environment).

        An empty variable is the same as an unset variable.
        """
        env = os.environ if env is None else env

        def get(name: str) -> str | None:
            value = env.get(name, "").strip()
            return value or None

        version = get("VALHALLA_VERSION")
        if version is not None and ("/" in version or ":" in version or "@" in version):
            raise HarnessError(
                f"VALHALLA_VERSION must be an image tag such as 3.8.2, not {version!r}; "
                "set VALHALLA_IMAGE to change the repository"
            )

        cli = get("VALINOR_CLI")
        valinor_cli = Path(cli).expanduser() if cli is not None else None
        if valinor_cli is not None and not valinor_cli.is_file():
            raise HarnessError(f"VALINOR_CLI is not a file: {valinor_cli}")

        port_value = get("VALHALLA_PORT")
        serve_port = DEFAULT_SERVE_PORT
        if port_value is not None:
            try:
                serve_port = int(port_value)
            except ValueError:
                raise HarnessError(f"VALHALLA_PORT is not a number: {port_value!r}") from None
            # serve mode also uses the next port, for the sub-extract.
            if not 1 <= serve_port <= 65534:
                raise HarnessError(f"VALHALLA_PORT must be from 1 to 65534, not {serve_port}")

        return cls(
            valhalla_image=get("VALHALLA_IMAGE") or DEFAULT_VALHALLA_IMAGE,
            valhalla_version=version,
            valinor_cli=valinor_cli,
            serve_port=serve_port,
        )
