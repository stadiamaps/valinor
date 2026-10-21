"""Integration tests of Valinor tile extracts with stock C++ Valhalla.

``valinor-integration run`` (the default) compares a sub-extract with the full extract.
``valinor-integration serve`` serves both extracts until Ctrl-C.
See README.md for the environment variables.
"""

from __future__ import annotations

import argparse
import logging
import signal
import sys
from pathlib import Path

from valinor_integration import runner
from valinor_integration.errors import HarnessError
from valinor_integration.settings import (
    DEFAULT_COLLECTION,
    DEFAULT_FULL_EXTRACT,
    DEFAULT_TILE_LIST,
    DEFAULT_WORKDIR,
    Settings,
)

log = logging.getLogger("valinor_integration")

COMMANDS = ("run", "serve")


def _parser() -> argparse.ArgumentParser:
    common = argparse.ArgumentParser(add_help=False)
    common.add_argument(
        "--extract",
        type=Path,
        default=DEFAULT_FULL_EXTRACT,
        help="the full extract tarball (default: the Andorra fixture)",
    )
    common.add_argument(
        "--workdir",
        type=Path,
        default=DEFAULT_WORKDIR,
        help="the directory for the sub-extract, responses, and logs (default: target/integration)",
    )
    common.add_argument(
        "--tiles",
        type=Path,
        default=DEFAULT_TILE_LIST,
        help="the tile list of the sub-extract (default: sub-extract-tiles.txt)",
    )
    common.add_argument(
        "--collection",
        type=Path,
        default=DEFAULT_COLLECTION,
        help="the Bruno collection of requests (default: bruno/)",
    )

    parser = argparse.ArgumentParser(
        prog="valinor-integration",
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("run", parents=[common], help="run the integration test (the default)")
    subparsers.add_parser("serve", parents=[common], help="serve both extracts until Ctrl-C")
    return parser


def _interrupt(signum: int, frame: object) -> None:
    raise KeyboardInterrupt


def main(argv: list[str] | None = None) -> int:
    logging.basicConfig(level=logging.INFO, format="%(levelname)s %(name)s: %(message)s")
    # Remove the containers on SIGTERM (for example, a cancelled CI job), as on Ctrl-C.
    signal.signal(signal.SIGTERM, _interrupt)
    argv = sys.argv[1:] if argv is None else argv
    # Make `run` the default command.
    if not argv or argv[0] not in (*COMMANDS, "-h", "--help"):
        argv = ["run", *argv]
    args = _parser().parse_args(argv)
    inputs = runner.Inputs(
        full_extract=args.extract.resolve(),
        workdir=args.workdir.resolve(),
        tile_list=args.tiles.resolve(),
        collection=args.collection.resolve(),
    )

    try:
        settings = Settings.from_env()
        log.info("Valhalla image: %s", settings.image_ref)
        if args.command == "serve":
            runner.serve(settings, inputs)
            return 0
        if runner.run(settings, inputs):
            log.info("integration: PASS")
            return 0
        log.error("integration: FAIL (responses and logs are in %s)", inputs.workdir)
        return 1
    except HarnessError as e:
        log.error("%s", e)
        return 1
    except KeyboardInterrupt:
        log.info("stopped")
        return 130


if __name__ == "__main__":
    sys.exit(main())
