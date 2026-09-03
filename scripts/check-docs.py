#!/usr/bin/env python3
"""Fail when a Markdown link points to a missing repository path."""

from __future__ import annotations

import re
import sys
from pathlib import Path
from urllib.parse import unquote, urlsplit


ROOT = Path(__file__).resolve().parent.parent
LINK = re.compile(r"!?\[[^\]]*\]\((?P<target>[^)\s]+)(?:\s+['\"][^'\"]*['\"])?\)")
IGNORED_SCHEMES = {"http", "https", "mailto"}


def markdown_files() -> list[Path]:
    ignored_parts = {".git", ".lake"}
    return sorted(
        path
        for path in ROOT.rglob("*.md")
        if not ignored_parts.intersection(path.relative_to(ROOT).parts)
    )


def missing_links(path: Path) -> list[tuple[int, str]]:
    failures: list[tuple[int, str]] = []
    for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        for match in LINK.finditer(line):
            raw_target = match.group("target")
            parsed = urlsplit(raw_target)
            if parsed.scheme in IGNORED_SCHEMES or raw_target.startswith("#"):
                continue
            if parsed.scheme or raw_target.startswith("/"):
                failures.append((line_number, raw_target))
                continue
            target = (path.parent / unquote(parsed.path)).resolve()
            try:
                target.relative_to(ROOT)
            except ValueError:
                failures.append((line_number, raw_target))
                continue
            if parsed.path and not target.exists():
                failures.append((line_number, raw_target))
    return failures


def main() -> int:
    failures: list[str] = []
    for path in markdown_files():
        for line_number, target in missing_links(path):
            relative = path.relative_to(ROOT)
            failures.append(f"{relative}:{line_number}: missing or unsafe link: {target}")

    if failures:
        print("\n".join(failures), file=sys.stderr)
        return 1

    print("Documentation links are valid.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
