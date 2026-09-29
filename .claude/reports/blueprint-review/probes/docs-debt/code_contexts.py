#!/usr/bin/env python3
"""Probe (read-only): print every occurrence of the given codes in the core documents with
its document, line and a window of context, for manual classification by meaning."""
import re, os, sys
root = "/home/scaraven/Documents/Verified-zkEVM/leanerVM"
P = os.path.join(root, ".claude/reports/blueprint-review/probes/docs-debt")
docs = [("blueprint","docs/roadmap/protocol-blueprint.md"),("status","docs/roadmap/protocol-status.md"),
 ("tracker-body",P+"/issue-12-body.md"),("hole-comment",P+"/issue-12-comment-5833669972.md"),
 ("c-5749712916",P+"/issue-12-comment-5749712916.md"),("c-5749874958",P+"/issue-12-comment-5749874958.md"),
 ("c-5813452703",P+"/issue-12-comment-5813452703.md"),("c-5872015097",P+"/issue-12-comment-5872015097.md"),
 ("review-spine","docs/reviews/protocol-spine.md"),("review-layer1","docs/reviews/protocol-layer1.md"),
 ("review-public-input","docs/reviews/public-input-phase.md")]
codes = sys.argv[1:]
for code in codes:
    rx = re.compile(r"(?<![A-Za-z0-9_.^`/=\-\[])%s(?![A-Za-z0-9_\]]|\.\d|\^|/)" % re.escape(code))
    print("=================", code)
    for name, p in docs:
        path = p if p.startswith("/") else os.path.join(root, p)
        for i, l in enumerate(open(path).read().split("\n"), 1):
            for m in rx.finditer(l):
                s = max(0, m.start()-70); e = min(len(l), m.end()+60)
                print(f"{name}:{i}: …{l[s:e]}…")
