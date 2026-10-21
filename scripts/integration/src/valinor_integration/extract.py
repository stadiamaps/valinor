"""Writes the sub-extract with ``valinor-cli extract``, and checks it against the full extract."""

from __future__ import annotations

import logging
import subprocess
import tarfile
from pathlib import Path

from valinor_integration.errors import HarnessError
from valinor_integration.settings import REPO_ROOT, Settings

log = logging.getLogger(__name__)


def read_tile_list(path: Path) -> list[str]:
    """Reads a tile list: one ``level/tile_id`` on each line.

    ``#`` starts a comment, and blank lines are ignored.
    ``valinor-cli`` checks the form of each tile.
    """
    tiles = []
    for line in path.read_text(encoding="utf-8").splitlines():
        tile = line.split("#", 1)[0].strip()
        if tile:
            tiles.append(tile.replace(" ", ""))
    if not tiles:
        raise HarnessError(f"the tile list contains no tiles: {path}")
    return tiles


def valinor_cli_command(settings: Settings) -> list[str]:
    """The command which runs ``valinor-cli``."""
    if settings.valinor_cli is not None:
        return [str(settings.valinor_cli)]
    return [
        "cargo",
        "run",
        "--quiet",
        "--release",
        "--manifest-path",
        str(REPO_ROOT / "Cargo.toml"),
        "--package",
        "valinor-cli",
        "--",
    ]


def write_sub_extract(
    settings: Settings, full_extract: Path, tiles: list[str], output: Path
) -> None:
    """Writes a sub-extract of ``full_extract`` which contains ``tiles``."""
    command = [
        *valinor_cli_command(settings),
        "extract",
        str(full_extract),
        str(output),
        "--tile",
        ",".join(tiles),
    ]
    log.info("writing the sub-extract: %s", " ".join(command))
    try:
        subprocess.run(command, check=True)
    except FileNotFoundError as e:
        raise HarnessError(f"cannot run {command[0]}: {e}") from None
    except subprocess.CalledProcessError as e:
        raise HarnessError(f"valinor-cli extract failed with exit status {e.returncode}") from None


def check_proper_subset(full_extract: Path, sub_extract: Path) -> list[str]:
    """Makes sure that the sub-extract is a proper subset of the full extract.

    Returns the entries that are only in the full extract.
    """
    full_entries = _entry_names(full_extract)
    sub_entries = _entry_names(sub_extract)

    extra = sorted(sub_entries - full_entries)
    if extra:
        raise HarnessError(
            f"the sub-extract contains entries which are not in the full extract: {extra}"
        )
    removed = sorted(full_entries - sub_entries)
    if not removed:
        raise HarnessError(
            "the sub-extract contains every entry of the full extract, "
            "so the comparison would prove nothing"
        )
    return removed


def _entry_names(archive: Path) -> set[str]:
    try:
        with tarfile.open(archive) as tar:
            return set(tar.getnames())
    except (OSError, tarfile.TarError) as e:
        raise HarnessError(f"cannot read the tar archive {archive}: {e}") from None
