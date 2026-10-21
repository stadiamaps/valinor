from pathlib import Path

import pytest

from valinor_integration.errors import HarnessError
from valinor_integration.settings import DEFAULT_COLLECTION, DEFAULT_FULL_EXTRACT, Settings


def test_defaults_use_latest() -> None:
    settings = Settings.from_env({})
    assert settings.image_ref == "ghcr.io/valhalla/valhalla:latest"
    assert not settings.is_pinned
    assert settings.valinor_cli is None
    assert settings.serve_port == 8002


def test_empty_values_are_unset() -> None:
    assert Settings.from_env({"VALHALLA_VERSION": " ", "VALINOR_CLI": ""}) == Settings.from_env({})


def test_pinned_version_and_image(tmp_path: Path) -> None:
    cli = tmp_path / "valinor-cli"
    cli.touch()
    settings = Settings.from_env(
        {
            "VALHALLA_VERSION": "3.8.2",
            "VALHALLA_IMAGE": "example.com/valhalla",
            "VALINOR_CLI": str(cli),
            "VALHALLA_PORT": "9000",
        }
    )
    assert settings.image_ref == "example.com/valhalla:3.8.2"
    assert settings.is_pinned
    assert settings.valinor_cli == cli
    assert settings.serve_port == 9000


@pytest.mark.parametrize(
    "env",
    [
        {"VALHALLA_VERSION": "ghcr.io/valhalla/valhalla:3.8.2"},
        {"VALHALLA_VERSION": "3.8.2@sha256:abc"},
        {"VALHALLA_PORT": "http"},
        {"VALHALLA_PORT": "65535"},
        {"VALHALLA_PORT": "0"},
        {"VALINOR_CLI": "/does/not/exist"},
    ],
)
def test_invalid_values(env: dict[str, str]) -> None:
    with pytest.raises(HarnessError):
        Settings.from_env(env)


def test_default_paths_exist() -> None:
    assert DEFAULT_FULL_EXTRACT.is_file()
    assert DEFAULT_COLLECTION.is_dir()
