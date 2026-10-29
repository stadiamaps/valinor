from pathlib import Path

import pytest

from valinor_integration import cli, runner


@pytest.fixture
def calls(monkeypatch: pytest.MonkeyPatch) -> list[tuple[str, runner.Inputs]]:
    recorded: list[tuple[str, runner.Inputs]] = []
    monkeypatch.setattr(
        runner, "run", lambda settings, inputs: recorded.append(("run", inputs)) or True
    )
    monkeypatch.setattr(
        runner, "serve", lambda settings, inputs: recorded.append(("serve", inputs))
    )
    monkeypatch.delenv("VALINOR_CLI", raising=False)
    return recorded


def test_run_is_the_default_command(calls: list[tuple[str, runner.Inputs]]) -> None:
    assert cli.main([]) == 0
    assert cli.main(["--workdir", "somewhere"]) == 0
    assert [command for command, _ in calls] == ["run", "run"]
    assert calls[1][1].workdir == Path("somewhere").resolve()


def test_serve_keeps_its_options(calls: list[tuple[str, runner.Inputs]]) -> None:
    assert cli.main(["serve", "--workdir", "somewhere"]) == 0
    assert calls == [("serve", calls[0][1])]
    assert calls[0][1].workdir == Path("somewhere").resolve()


def test_failed_run_exits_with_one(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(runner, "run", lambda settings, inputs: False)
    assert cli.main([]) == 1
