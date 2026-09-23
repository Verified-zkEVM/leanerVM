#!/usr/bin/env python3
"""Reject protected set_option forms, including comment-separated tokens.

This is a conservative source policy, not a Lean parser: like the previous lexical
gate, it also checks command-shaped text in comments, strings and syntax quotations.
Only the separator after each set_option candidate is lexed. This avoids mistaking
comment delimiters in strings for comments that could hide a later real command.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path


COMMAND = re.compile(r"\bset_option\b")
NAME_PART = re.compile(r"«([^»]*)»|([A-Za-z_][A-Za-z0-9_']*)")
PROTECTED = {"autoImplicit", "relaxedAutoImplicit", "warningAsError"}


def skip_separators(source: str, offset: int) -> int:
    """Skip whitespace, line comments and arbitrarily nested block comments."""
    while offset < len(source):
        if source[offset].isspace():
            offset += 1
        elif source.startswith("--", offset):
            end = source.find("\n", offset + 2)
            offset = len(source) if end == -1 else end + 1
        elif source.startswith("/-", offset):
            depth = 1
            offset += 2
            while depth and offset < len(source):
                # Quotes and line-comment markers are ordinary block-comment text.
                if source.startswith("/-", offset):
                    depth += 1
                    offset += 2
                elif source.startswith("-/", offset):
                    depth -= 1
                    offset += 2
                else:
                    offset += 1
            if depth:
                raise ValueError("unterminated block comment after set_option")
        else:
            break
    return offset


def option_name(source: str, offset: int) -> tuple[str, ...]:
    """Read the option name, including Lean's escaped identifier components."""
    parts = []
    while match := NAME_PART.match(source, offset):
        parts.append(match[1] if match[1] is not None else match[2])
        offset = match.end()
        if offset == len(source) or source[offset] != ".":
            break
        offset += 1
    return tuple(parts)


def check(path: Path) -> list[str]:
    source = path.read_text(encoding="utf-8")
    failures = []
    for command in COMMAND.finditer(source):
        line = source.count("\n", 0, command.start()) + 1
        try:
            name = option_name(source, skip_separators(source, command.end()))
        except ValueError as error:
            failures.append(f"{path}:{line}: {error}")
            continue
        if (len(name) == 1 and name[0] in PROTECTED) or name[:1] == ("linter",) or (
            name[:2] == ("weak", "linter")
        ):
            failures.append(f"{path}:{line}: set_option {'.'.join(name)}")
    return failures


def main() -> int:
    if len(sys.argv) < 2:
        raise SystemExit("usage: check-lean-options.py <Lean source file or directory> ...")
    failures = []
    for argument in sys.argv[1:]:
        path = Path(argument)
        paths = sorted(path.rglob("*.lean")) if path.is_dir() else [path]
        for source_path in paths:
            failures.extend(check(source_path))
    if failures:
        print("Repository-wide Lean options must not be overridden in source files:", file=sys.stderr)
        print("\n".join(failures), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
