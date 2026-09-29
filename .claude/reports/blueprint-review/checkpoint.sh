#!/usr/bin/env bash
# Stage the review's record for a checkpoint commit on the review branch.
# `.claude/` is git-ignored by the repository, so paths are force-added one by one; a plain
# `git add -f <dir>` would also take the build outputs and the upstream clones.
set -euo pipefail
R=.claude/reports/blueprint-review
git add -f "$R/BRIEF.md" "$R/NOTES.md" "$R/.gitignore" "$R/checkpoint.sh" "$R/dossiers"
git add -f "$R/tex/main.tex" "$R/tex/preamble.tex" "$R/tex/refs.bib" "$R/tex/sections"
find "$R/probes" \( -path '*/upstream/*-main' -o -name '__pycache__' \) -prune -o -type f -print0 \
  | xargs -0 git add -f
[ -f "$R/tex/report.pdf" ] && git add -f "$R/tex/report.pdf"
git status --short | awk '{print $1}' | sort | uniq -c
