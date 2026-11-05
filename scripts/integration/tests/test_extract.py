import tarfile
from pathlib import Path

import pytest

from valinor_integration.errors import HarnessError
from valinor_integration.extract import check_proper_subset, read_tile_list
from valinor_integration.settings import DEFAULT_TILE_LIST


def _archive(path: Path, names: list[str]) -> Path:
    with tarfile.open(path, "w") as tar:
        for name in names:
            tar.addfile(tarfile.TarInfo(name))
    return path


def test_read_tile_list(tmp_path: Path) -> None:
    tile_list = tmp_path / "tiles.txt"
    tile_list.write_text("# comment\n\n0/3015\n 2 / 762485  # inline comment\n")
    assert read_tile_list(tile_list) == ["0/3015", "2/762485"]


def test_empty_tile_list_is_an_error(tmp_path: Path) -> None:
    tile_list = tmp_path / "tiles.txt"
    tile_list.write_text("# only a comment\n")
    with pytest.raises(HarnessError, match="no tiles"):
        read_tile_list(tile_list)


def test_the_repository_tile_list_reads() -> None:
    assert len(read_tile_list(DEFAULT_TILE_LIST)) == 6


def test_proper_subset(tmp_path: Path) -> None:
    full = _archive(tmp_path / "full.tar", ["index.bin", "0/a.gph", "2/b.gph"])
    sub = _archive(tmp_path / "sub.tar", ["index.bin", "0/a.gph"])
    assert check_proper_subset(full, sub) == ["2/b.gph"]


def test_identical_extracts_prove_nothing(tmp_path: Path) -> None:
    full = _archive(tmp_path / "full.tar", ["index.bin", "0/a.gph"])
    sub = _archive(tmp_path / "sub.tar", ["index.bin", "0/a.gph"])
    with pytest.raises(HarnessError, match="would prove nothing"):
        check_proper_subset(full, sub)


def test_extra_entries_are_an_error(tmp_path: Path) -> None:
    full = _archive(tmp_path / "full.tar", ["index.bin", "0/a.gph"])
    sub = _archive(tmp_path / "sub.tar", ["index.bin", "1/c.gph"])
    with pytest.raises(HarnessError, match="not in the full extract"):
        check_proper_subset(full, sub)
