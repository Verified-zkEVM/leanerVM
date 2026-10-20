#!/usr/bin/env python3
"""Regression tests for the dependency-free build timing helper."""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
SCRIPT = ROOT / "scripts" / "build_timing.py"


def invoke(*arguments: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(SCRIPT), *arguments],
        check=False,
        text=True,
        capture_output=True,
    )


def main() -> int:
    with tempfile.TemporaryDirectory() as directory:
        temporary = Path(directory)
        results = temporary / "results.jsonl"
        success_log = temporary / "success.log"
        failure_log = temporary / "failure.log"

        success = invoke(
            "run",
            "--label",
            "fixture",
            "--results",
            str(results),
            "--log",
            str(success_log),
            "--",
            sys.executable,
            "-c",
            "print('timing fixture')",
        )
        assert success.returncode == 0, success.stderr
        assert success_log.read_text(encoding="utf-8") == "timing fixture\n"

        failure = invoke(
            "run",
            "--label",
            "failure fixture",
            "--results",
            str(results),
            "--log",
            str(failure_log),
            "--",
            sys.executable,
            "-c",
            "raise SystemExit(7)",
        )
        assert failure.returncode == 7

        records = [json.loads(line) for line in results.read_text(encoding="utf-8").splitlines()]
        assert [record["exitCode"] for record in records] == [0, 7]
        assert all(record["seconds"] >= 0 for record in records)
        assert all(record["userSeconds"] >= 0 for record in records)
        assert all(record["systemSeconds"] >= 0 for record in records)

        report = invoke("render", "--results", str(results))
        assert report.returncode == 0, report.stderr
        assert "| fixture |" in report.stdout
        assert "| failure fixture |" in report.stdout

    print("Build timing helper tests passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
