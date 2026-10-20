#!/usr/bin/env python3
"""Measure commands into a small, portable JSONL benchmark record."""

from __future__ import annotations

import argparse
import json
import os
import shlex
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


def run_command(args: argparse.Namespace) -> int:
    command = args.command
    if command and command[0] == "--":
        command = command[1:]
    if not command:
        print("build_timing.py run: a command is required after --", file=sys.stderr)
        return 2

    results = Path(args.results)
    log = Path(args.log)
    results.parent.mkdir(parents=True, exist_ok=True)
    log.parent.mkdir(parents=True, exist_ok=True)

    started_at = datetime.now(timezone.utc).isoformat()
    process_times_before = os.times()
    started = time.perf_counter()
    with log.open("w", encoding="utf-8") as output:
        process = subprocess.Popen(
            command,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
        )
        assert process.stdout is not None
        for line in process.stdout:
            print(line, end="")
            output.write(line)
        exit_code = process.wait()
    elapsed = time.perf_counter() - started
    process_times_after = os.times()

    record = {
        "schemaVersion": 1,
        "label": args.label,
        "seconds": round(elapsed, 3),
        "userSeconds": round(
            process_times_after.children_user - process_times_before.children_user, 3
        ),
        "systemSeconds": round(
            process_times_after.children_system - process_times_before.children_system, 3
        ),
        "exitCode": exit_code,
        "command": shlex.join(command),
        "startedAt": started_at,
        "gitSha": os.environ.get("GITHUB_SHA"),
        "runner": os.environ.get("RUNNER_NAME"),
    }
    with results.open("a", encoding="utf-8") as output:
        json.dump(record, output, sort_keys=True)
        output.write("\n")

    print(f"{args.label}: {elapsed:.3f}s (exit {exit_code})")
    return exit_code


def read_records(path: Path) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        try:
            record = json.loads(line)
        except json.JSONDecodeError as error:
            raise ValueError(f"{path}:{line_number}: invalid JSON: {error}") from error
        required = {"label", "seconds", "exitCode", "command"}
        missing = required.difference(record)
        if missing:
            raise ValueError(f"{path}:{line_number}: missing fields: {sorted(missing)}")
        records.append(record)
    return records


def markdown_cell(value: object) -> str:
    return str(value).replace("|", "\\|").replace("\n", " ")


def render(args: argparse.Namespace) -> int:
    path = Path(args.results)
    if not path.is_file():
        print(f"No timing results found at {path}", file=sys.stderr)
        return 1
    try:
        records = read_records(path)
    except ValueError as error:
        print(error, file=sys.stderr)
        return 1
    if not records:
        print(f"No timing records found in {path}", file=sys.stderr)
        return 1

    print("## Build timing")
    print()
    print("| Benchmark | Wall (s) | User (s) | System (s) | Exit | Command |")
    print("| --- | ---: | ---: | ---: | ---: | --- |")
    for record in records:
        print(
            f"| {markdown_cell(record['label'])} "
            f"| {float(record['seconds']):.3f} "
            f"| {float(record.get('userSeconds', 0)):.3f} "
            f"| {float(record.get('systemSeconds', 0)):.3f} "
            f"| {int(record['exitCode'])} "
            f"| `{markdown_cell(record['command'])}` |"
        )
    return 0


def parser() -> argparse.ArgumentParser:
    top = argparse.ArgumentParser(description=__doc__)
    subcommands = top.add_subparsers(dest="subcommand", required=True)

    run = subcommands.add_parser("run", help="measure one command")
    run.add_argument("--label", required=True)
    run.add_argument("--results", required=True)
    run.add_argument("--log", required=True)
    run.add_argument("command", nargs=argparse.REMAINDER)
    run.set_defaults(function=run_command)

    report = subcommands.add_parser("render", help="render JSONL results as Markdown")
    report.add_argument("--results", required=True)
    report.set_defaults(function=render)
    return top


def main() -> int:
    args = parser().parse_args()
    return args.function(args)


if __name__ == "__main__":
    raise SystemExit(main())
