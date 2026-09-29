#!/usr/bin/env python3
"""Probe (read-only): every letter-number code in the proof-system documents, with counts and
line numbers per document. Documents: the blueprint, the status, the tracker body, the hole
comment, the other comments of the tracker, the three review handoffs of the proof system.
Also counted, for cross-family collisions: architecture.md, leanvm-target.md, leanth-reuse.md,
the two leanISA roadmap files, dependencies.md, development.md, docs/README.md."""
import re, os, json, collections, sys
root = "/home/scaraven/Documents/Verified-zkEVM/leanerVM"
P = os.path.join(root, ".claude/reports/blueprint-review/probes/docs-debt")
docs = collections.OrderedDict([
 ("blueprint", os.path.join(root,"docs/roadmap/protocol-blueprint.md")),
 ("status", os.path.join(root,"docs/roadmap/protocol-status.md")),
 ("tracker-body", os.path.join(P,"issue-12-body.md")),
 ("hole-comment", os.path.join(P,"issue-12-comment-5833669972.md")),
 ("tracker-other-comments", None),
 ("review-spine", os.path.join(root,"docs/reviews/protocol-spine.md")),
 ("review-layer1", os.path.join(root,"docs/reviews/protocol-layer1.md")),
 ("review-public-input", os.path.join(root,"docs/reviews/public-input-phase.md")),
 ("leanth-reuse", os.path.join(root,"docs/roadmap/leanth-reuse.md")),
 ("architecture", os.path.join(root,"docs/architecture.md")),
 ("leanvm-target", os.path.join(root,"docs/leanvm-target.md")),
 ("leanisa-blueprint", os.path.join(root,"docs/roadmap/leanisa-blueprint.md")),
 ("leanisa-status", os.path.join(root,"docs/roadmap/leanisa-status.md")),
 ("dependencies", os.path.join(root,"docs/dependencies.md")),
 ("development", os.path.join(root,"docs/development.md")),
 ("docs-README", os.path.join(root,"docs/README.md")),
])
def load(name, path):
    if path is None:
        out=[]
        for c in ["5749712916","5749874958","5813452703","5872015097"]:
            out += open(os.path.join(P,f"issue-12-comment-{c}.md")).read().split("\n")
        return out
    return open(path).read().split("\n")
code_re = re.compile(r"(?<![A-Za-z0-9_.^`/=\-\[])([A-Z])(\d{1,2})(?![A-Za-z0-9_\]]|\.\d|\^|/)")
# hole S standing alone
holeS_re = re.compile(r"(?:hole \*{0,2}S\*{0,2}\b|\(S\)|\bS, I1\b|\| S \||\*\*S — |### S:|\bS and C1\b|, S\)|, S \||\bG2, S\b)")
res = collections.defaultdict(lambda: collections.defaultdict(list))
for name, path in docs.items():
    ls = load(name, path)
    infence = False
    for i, l in enumerate(ls, 1):
        for m in code_re.finditer(l):
            code = m.group(1)+m.group(2)
            res[code][name].append(i)
        for m in holeS_re.finditer(l):
            res["S(hole)"][name].append(i)
json.dump({k:{d:v for d,v in dv.items()} for k,dv in res.items()}, open(os.path.join(P,"codes.json"),"w"), indent=0)
def key(c):
    m = re.match(r"([A-Z])(\d+)", c)
    return (m.group(1), int(m.group(2))) if m else ("S", -1)
core = ["blueprint","status","tracker-body","hole-comment","tracker-other-comments","review-spine","review-layer1","review-public-input"]
others = [d for d in docs if d not in core]
print("code | " + " | ".join(core) + " | core total || " + " | ".join(others))
for c in sorted(res, key=key):
    row = [str(len(res[c].get(d, []))) for d in core]
    tot = sum(len(res[c].get(d, [])) for d in core)
    row2 = [str(len(res[c].get(d, []))) for d in others]
    if tot == 0 and sum(map(int,row2)) == 0: continue
    print(f"{c} | " + " | ".join(row) + f" | {tot} || " + " | ".join(row2))
