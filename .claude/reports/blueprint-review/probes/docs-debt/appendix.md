
## Appendix: the probes

Every probe is a read-only Python script or shell command over text; no Lean was run. The
scripts are under `.claude/reports/blueprint-review/probes/docs-debt/` and are run from that
directory with `python3 <script>`. They read the working tree, so the recorded outputs below
were produced at `b435631`, before the merge of `144c5aa` into the checkout (a re-run today
reads the blueprint of `144c5aa`, which differs by 6 lines; where that changes a figure, the
dossier says so, for example `unlisted_public.py`: 198 at `b435631`, 197 at `144c5aa`, obtained
by running a copy of the script on `git archive b435631` in the scratchpad).

### `extract_codes.py`

Every letter-number code of the eight texts, counted per document (section D). Output: `codes.json` and the table below (`codes_table.txt`). The pattern skips codes inside backticks, so the counts are lower bounds (§D).

Command: `python3 extract_codes.py`

```python
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
```

Output:

```text
code | blueprint | status | tracker-body | hole-comment | tracker-other-comments | review-spine | review-layer1 | review-public-input | core total || leanth-reuse | architecture | leanvm-target | leanisa-blueprint | leanisa-status | dependencies | development | docs-README
A1 | 3 | 9 | 2 | 0 | 1 | 9 | 3 | 5 | 32 || 3 | 0 | 0 | 0 | 2 | 0 | 0 | 1
A2 | 7 | 9 | 2 | 3 | 2 | 8 | 3 | 5 | 39 || 7 | 0 | 0 | 0 | 1 | 0 | 0 | 0
A3 | 1 | 6 | 1 | 0 | 0 | 11 | 2 | 3 | 24 || 5 | 0 | 0 | 0 | 1 | 0 | 0 | 0
A4 | 1 | 4 | 0 | 0 | 0 | 6 | 3 | 2 | 16 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
A5 | 4 | 2 | 1 | 1 | 0 | 7 | 2 | 0 | 17 || 1 | 0 | 0 | 0 | 1 | 0 | 0 | 0
A6 | 2 | 3 | 1 | 2 | 0 | 5 | 3 | 0 | 16 || 2 | 0 | 0 | 0 | 1 | 0 | 0 | 0
A7 | 2 | 2 | 1 | 1 | 0 | 0 | 0 | 0 | 6 || 3 | 0 | 0 | 0 | 1 | 0 | 0 | 0
A8 | 4 | 1 | 1 | 1 | 0 | 0 | 0 | 0 | 7 || 2 | 0 | 0 | 0 | 1 | 0 | 0 | 0
A9 | 1 | 2 | 1 | 1 | 0 | 0 | 0 | 0 | 5 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
A10 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
A11 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
A12 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
A13 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
A14 | 0 | 2 | 0 | 0 | 0 | 0 | 0 | 0 | 2 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
A15 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
A16 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
A17 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
A18 | 0 | 3 | 1 | 0 | 0 | 0 | 0 | 0 | 4 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
A19 | 0 | 3 | 0 | 0 | 0 | 0 | 0 | 0 | 3 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
B0 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
B1 | 0 | 2 | 0 | 0 | 0 | 2 | 4 | 5 | 13 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
B2 | 0 | 1 | 0 | 0 | 0 | 2 | 5 | 2 | 10 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
B3 | 0 | 1 | 0 | 0 | 0 | 0 | 2 | 2 | 5 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
B4 | 0 | 1 | 0 | 0 | 0 | 0 | 3 | 0 | 4 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
B6 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
C1 | 5 | 9 | 5 | 4 | 3 | 6 | 4 | 5 | 41 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
C2 | 0 | 2 | 1 | 0 | 0 | 2 | 2 | 2 | 9 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
C3 | 0 | 1 | 1 | 0 | 0 | 0 | 1 | 2 | 5 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
C4 | 0 | 1 | 1 | 0 | 0 | 0 | 1 | 2 | 5 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
C5 | 1 | 1 | 0 | 0 | 0 | 0 | 1 | 0 | 3 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
C6 | 1 | 1 | 0 | 0 | 0 | 0 | 1 | 0 | 3 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
C7 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | 1 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
C8 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | 1 || 0 | 0 | 0 | 0 | 9 | 1 | 0 | 0
C9 | 0 | 0 | 0 | 0 | 0 | 0 | 3 | 0 | 3 || 0 | 0 | 0 | 0 | 2 | 0 | 0 | 0
C10 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 || 0 | 0 | 0 | 0 | 4 | 0 | 0 | 0
C11 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 || 0 | 0 | 0 | 0 | 2 | 0 | 0 | 0
D1 | 0 | 2 | 0 | 0 | 0 | 0 | 3 | 0 | 5 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
D2 | 0 | 0 | 0 | 0 | 0 | 0 | 2 | 0 | 2 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
D4 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
D5 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | 1 || 0 | 0 | 0 | 1 | 1 | 0 | 0 | 0
D7 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
D8 | 0 | 0 | 0 | 0 | 0 | 0 | 2 | 0 | 2 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
D9 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
D10 | 0 | 0 | 0 | 0 | 0 | 0 | 2 | 0 | 2 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
D11 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
D12 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
D13 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
D14 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
D15 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
D16 | 0 | 0 | 0 | 0 | 0 | 0 | 2 | 0 | 2 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
D17 | 0 | 0 | 0 | 0 | 0 | 0 | 3 | 0 | 3 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
E1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
E2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
E3 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
E4 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 2 | 0 | 0 | 0
E5 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 1 | 7 | 0 | 0 | 0
E6 | 0 | 2 | 0 | 0 | 0 | 0 | 0 | 0 | 2 || 0 | 0 | 0 | 0 | 7 | 1 | 0 | 0
E7 | 0 | 1 | 1 | 0 | 0 | 1 | 0 | 0 | 3 || 0 | 0 | 0 | 0 | 3 | 0 | 0 | 0
E8 | 0 | 1 | 1 | 0 | 0 | 1 | 0 | 0 | 3 || 0 | 0 | 0 | 2 | 5 | 0 | 0 | 0
E9 | 0 | 1 | 1 | 0 | 0 | 2 | 0 | 0 | 4 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
E10 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 1 | 2 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
E11 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
E12 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 2 | 3 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
E13 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 2 | 3 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
E14 | 0 | 3 | 0 | 0 | 0 | 0 | 0 | 1 | 4 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
E15 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 1 | 2 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
E16 | 0 | 5 | 0 | 0 | 0 | 0 | 0 | 1 | 6 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
E17 | 0 | 3 | 0 | 0 | 0 | 0 | 1 | 2 | 6 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
E18 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 1 | 2 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
F1 | 4 | 3 | 1 | 1 | 0 | 0 | 0 | 0 | 9 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
F2 | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 2 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
F3 | 4 | 2 | 1 | 1 | 0 | 0 | 0 | 0 | 8 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
F4 | 1 | 2 | 0 | 1 | 0 | 0 | 0 | 0 | 4 || 0 | 0 | 0 | 0 | 2 | 0 | 0 | 0
F5 | 3 | 1 | 1 | 1 | 0 | 0 | 0 | 0 | 6 || 0 | 0 | 0 | 0 | 4 | 0 | 0 | 0
F6 | 4 | 3 | 2 | 0 | 0 | 0 | 0 | 0 | 9 || 0 | 0 | 0 | 0 | 6 | 0 | 0 | 0
F7 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 || 0 | 0 | 0 | 0 | 4 | 0 | 0 | 0
F8 | 2 | 1 | 1 | 1 | 0 | 0 | 0 | 0 | 5 || 0 | 0 | 0 | 0 | 5 | 0 | 0 | 1
F9 | 0 | 2 | 1 | 0 | 0 | 0 | 0 | 0 | 3 || 0 | 0 | 0 | 0 | 6 | 0 | 0 | 0
F10 | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 2 || 0 | 0 | 0 | 0 | 7 | 0 | 0 | 0
F11 | 0 | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 2 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
F12 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
F13 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
F14 | 0 | 1 | 0 | 1 | 0 | 0 | 0 | 0 | 2 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
F15 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
F16 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
F17 | 0 | 4 | 0 | 0 | 0 | 0 | 1 | 2 | 7 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
F18 | 0 | 5 | 0 | 0 | 0 | 0 | 0 | 2 | 7 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
F64 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 2 | 0 | 0 | 0 | 0
G1 | 7 | 8 | 7 | 3 | 1 | 0 | 0 | 0 | 26 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
G2 | 3 | 4 | 4 | 1 | 0 | 0 | 0 | 0 | 12 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
G3 | 2 | 7 | 5 | 1 | 0 | 0 | 0 | 0 | 15 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
G4 | 2 | 5 | 4 | 1 | 0 | 0 | 0 | 0 | 12 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
G5 | 2 | 4 | 4 | 4 | 0 | 0 | 0 | 0 | 14 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
G6 | 5 | 2 | 2 | 4 | 1 | 0 | 0 | 0 | 14 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
H1 | 0 | 2 | 0 | 0 | 0 | 5 | 0 | 16 | 23 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
H2 | 0 | 0 | 0 | 0 | 0 | 3 | 0 | 7 | 10 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
H3 | 0 | 0 | 0 | 0 | 0 | 4 | 0 | 8 | 12 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
H4 | 0 | 0 | 0 | 0 | 0 | 4 | 0 | 4 | 8 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
H5 | 0 | 0 | 0 | 0 | 0 | 4 | 0 | 8 | 12 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
H6 | 0 | 2 | 0 | 0 | 0 | 7 | 0 | 9 | 18 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
I1 | 3 | 5 | 6 | 1 | 2 | 9 | 0 | 0 | 26 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
I2 | 5 | 8 | 11 | 6 | 3 | 15 | 1 | 0 | 49 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
I3 | 0 | 0 | 0 | 0 | 0 | 3 | 0 | 0 | 3 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
K1 | 4 | 8 | 9 | 3 | 1 | 0 | 0 | 0 | 25 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
K2 | 4 | 4 | 5 | 3 | 1 | 0 | 0 | 0 | 17 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
K3 | 4 | 7 | 7 | 6 | 0 | 5 | 0 | 0 | 29 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
K4 | 2 | 1 | 2 | 3 | 0 | 2 | 0 | 0 | 10 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
L1 | 5 | 6 | 7 | 0 | 0 | 0 | 2 | 0 | 20 || 0 | 0 | 0 | 0 | 7 | 0 | 0 | 0
L2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
L3 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
M3 | 7 | 0 | 1 | 0 | 0 | 1 | 0 | 0 | 9 || 1 | 0 | 3 | 8 | 3 | 0 | 0 | 1
P1 | 4 | 5 | 4 | 3 | 1 | 2 | 0 | 2 | 21 || 0 | 0 | 0 | 1 | 6 | 0 | 0 | 0
P2 | 4 | 2 | 3 | 4 | 0 | 0 | 0 | 0 | 13 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
P3 | 4 | 6 | 3 | 3 | 1 | 0 | 0 | 2 | 19 || 0 | 0 | 0 | 0 | 5 | 0 | 1 | 0
P4 | 4 | 2 | 2 | 4 | 0 | 0 | 0 | 0 | 12 || 0 | 0 | 0 | 0 | 2 | 0 | 0 | 0
P5 | 2 | 15 | 3 | 3 | 3 | 7 | 0 | 2 | 35 || 0 | 0 | 0 | 0 | 2 | 0 | 0 | 0
P6 | 2 | 4 | 4 | 3 | 2 | 4 | 0 | 0 | 19 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
P7 | 2 | 6 | 5 | 4 | 0 | 1 | 0 | 2 | 20 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
P8 | 5 | 2 | 3 | 4 | 0 | 2 | 0 | 0 | 16 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
P17 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
R1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 5 | 0 | 0 | 0
R2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 3 | 0 | 0 | 0
R3 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 3 | 0 | 0 | 0
R4 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R5 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R6 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R7 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R8 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R9 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R10 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R11 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R12 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R13 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R14 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R15 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R16 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R17 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R18 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R19 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R20 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R21 | 1 | 0 | 0 | 1 | 0 | 0 | 0 | 0 | 2 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R22 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R23 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R24 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 3 | 0 | 0 | 0
R25 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 2 | 0 | 0 | 0
R26 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R27 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
R28 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
S(hole) | 7 | 4 | 4 | 3 | 1 | 1 | 0 | 7 | 27 || 29 | 0 | 0 | 0 | 0 | 0 | 0 | 0
S1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 4 | 0 | 0 | 1 | 0 | 0 | 0
S2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 6 | 0 | 0 | 1 | 0 | 0 | 0
S3 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 2 | 0 | 0 | 1 | 0 | 0 | 0
S4 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 5 | 0 | 0 | 1 | 0 | 0 | 0
S5 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 2 | 0 | 0 | 0
S6 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
S7 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
S8 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
S9 | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 2 || 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0
S10 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
S11 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
S12 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
S13 | 0 | 2 | 1 | 0 | 0 | 5 | 0 | 0 | 8 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
S14 | 0 | 2 | 1 | 0 | 0 | 1 | 0 | 0 | 4 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
S15 | 0 | 2 | 0 | 0 | 0 | 0 | 1 | 0 | 3 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
S16 | 0 | 2 | 0 | 0 | 0 | 0 | 1 | 0 | 3 || 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
T1 | 4 | 1 | 2 | 0 | 0 | 0 | 0 | 0 | 7 || 0 | 11 | 6 | 8 | 11 | 0 | 0 | 0
T2 | 2 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 3 || 0 | 5 | 2 | 3 | 4 | 0 | 0 | 0
T3 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 1 | 5 | 3 | 0 | 0 | 0 | 0 | 0
T4 | 11 | 1 | 2 | 3 | 0 | 4 | 0 | 0 | 21 || 1 | 5 | 2 | 0 | 0 | 0 | 0 | 0
T5 | 5 | 0 | 0 | 1 | 0 | 0 | 0 | 0 | 6 || 0 | 4 | 2 | 0 | 0 | 0 | 0 | 0
T6 | 4 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 4 || 2 | 11 | 4 | 0 | 0 | 0 | 0 | 0
T7 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 5 | 4 | 0 | 0 | 0 | 0 | 0
T8 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 || 0 | 6 | 2 | 1 | 0 | 0 | 0 | 0
```

### `code_contexts.py`

Every occurrence of the given codes with its context, for classification by meaning by hand (§D.3). Output: `ctx_A.txt`, `ctx_C.txt`, `ctx_F.txt`, `ctx_I.txt`, `ctx_P.txt`, `ctx_misc.txt` (not reproduced: they are the texts themselves, cut into windows).

Command: `python3 code_contexts.py`

```python
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
```

### `check_anchors.py`

Local Markdown links and their anchors, computed the GitHub way (§B.10).

Command: `python3 check_anchors.py`

```python
#!/usr/bin/env python3
"""Probe (read-only): Markdown links with anchors in the tracked documentation, including
links broken across lines (which scripts/check-docs.py, a per-line matcher, does not see).
Anchors are computed the GitHub way (lowercase, punctuation dropped, spaces to hyphens)."""
import re, os, subprocess
root="/home/scaraven/Documents/Verified-zkEVM/leanerVM"
files=subprocess.run(["git","ls-files","*.md"],cwd=root,capture_output=True,text=True).stdout.split()
def anchors(path):
    out=set(); infence=False
    for l in open(path,encoding="utf-8").read().split("\n"):
        if l.startswith("```"): infence=not infence
        if infence: continue
        m=re.match(r"^(#{1,6})\s+(.*)$",l)
        if m:
            t=m.group(2).strip()
            t=re.sub(r"\[([^\]]*)\]\([^)]*\)",r"\1",t)
            t=t.replace("`","")
            a=re.sub(r"[^\w\- ]","",t.lower(),flags=re.UNICODE).replace(" ","-")
            out.add(a)
    return out
link=re.compile(r"\[([^\]]*)\]\(([^)\s]+)\)",re.S)
n=0; bad=[]; multiline=0
for f in files:
    p=os.path.join(root,f); txt=open(p,encoding="utf-8").read()
    for m in link.finditer(txt):
        target=m.group(2)
        if target.startswith("http") or target.startswith("mailto"): continue
        line=txt[:m.start()].count("\n")+1
        if "\n" in m.group(1): multiline+=1
        path,_,frag=target.partition("#")
        tp=p if path=="" else os.path.normpath(os.path.join(os.path.dirname(p),path))
        n+=1
        if not os.path.exists(tp):
            bad.append(f"{f}:{line}: missing file {target}"); continue
        if frag and tp.endswith(".md"):
            if frag not in anchors(tp):
                bad.append(f"{f}:{line}: missing anchor #{frag} in {os.path.relpath(tp,root)}")
print(f"{len(files)} tracked Markdown files, {n} local links checked ({multiline} span two lines), {len(bad)} broken")
for b in bad: print("  ",b)
```

Output:

```text
24 tracked Markdown files, 150 local links checked (0 span two lines), 0 broken
```

### `check_interface_names.py`

Each name of the blueprint's list "Interfaces supplied to later work" looked up under `LeanerVM/` (§B.5). Output `interface_names.out` (195 lines); reproduced: its summary line and the 64 absent names.

Command: `python3 check_interface_names.py`

```python
#!/usr/bin/env python3
"""Probe (read-only): for each name in the blueprint's 'Interfaces supplied to later work'
list (docs/roadmap/protocol-blueprint.md:1366-1416), report whether a declaration with that
final name component exists under LeanerVM/ in the working tree (main at b435631).
DECL   = a def/theorem/structure/abbrev/instance/inductive whose declared name ends with the
         final component was found (the namespace is not resolved: see the file shown)
FIELD  = only a structure field of that name was found
ABSENT = neither."""
import re, os, glob
root = "/home/scaraven/Documents/Verified-zkEVM/leanerVM"
lines = open(os.path.join(root, "docs/roadmap/protocol-blueprint.md")).read().split("\n")
block = lines[1365:1416]
group = None
names = []
for l in block:
    m = re.match(r"^([A-Z][A-Za-z ()]+):\s+(.*)$", l)
    if m:
        group = m.group(1).strip(); rest = m.group(2)
    else:
        rest = l.strip()
    rest = rest.replace("(each with .Holds)", " ").replace("(and their .append)", " ").replace("(Layer 2)", " ")
    rest = rest.replace("Component.Security.{witMid, extractor, kSF, rbr}",
                        "Component.Security.witMid Component.Security.extractor Component.Security.kSF Component.Security.rbr")
    for tok in rest.split():
        names.append((group, tok))
files = [f for f in glob.glob(os.path.join(root, "LeanerVM/**/*.lean"), recursive=True)]
src = {f: open(f).read().split("\n") for f in files}
KW = r"(?:def|theorem|lemma|structure|inductive|abbrev|instance|class|opaque)"
def find(short):
    decl = re.compile(r"(?:^|\s)%s\s+(?:[^\s.]+\.)*%s(?=\s|$|\{|\(|\[|:)" % (KW, re.escape(short)))
    fld = re.compile(r"^\s+%s\s*:(?!=)" % re.escape(short))
    d, f = [], []
    for fn, ls in src.items():
        for i, l in enumerate(ls, 1):
            if decl.search(l): d.append(f"{os.path.relpath(fn, root)}:{i}: {l.strip()[:90]}")
            elif fld.search(l): f.append(f"{os.path.relpath(fn, root)}:{i}: {l.strip()[:90]}")
    return d, f
seen = set(); counts = {"DECL":0, "FIELD":0, "ABSENT":0}
for g, n in names:
    if (g, n) in seen: continue
    seen.add((g, n))
    d, f = find(n.split(".")[-1])
    status = "DECL" if d else ("FIELD" if f else "ABSENT")
    counts[status] += 1
    print(f"{status:7} | {g:20} | {n:68} | {(d or f or [''])[0]}")
print(counts)
```

Output:

```text
ABSENT  | Spine                | Ensemble.toM3                                                        | 
ABSENT  | Protocol (generic)   | Virtual                                                              | 
ABSENT  | Protocol (generic)   | sumcheck                                                             | 
ABSENT  | Protocol (generic)   | sumcheck_rbrKnowledgeSoundness                                       | 
ABSENT  | Protocol (generic)   | batchClaims                                                          | 
ABSENT  | Protocol (generic)   | fingerprint                                                          | 
ABSENT  | Protocol (generic)   | sideProduct                                                          | 
ABSENT  | Protocol (generic)   | sideProduct_poly_eq_iff                                              | 
ABSENT  | Protocol (generic)   | sideProduct_collision                                                | 
ABSENT  | Protocol (generic)   | ProductTree                                                          | 
ABSENT  | Protocol (generic)   | gkr                                                                  | 
ABSENT  | Protocol (generic)   | gkrError                                                             | 
ABSENT  | Protocol (generic)   | gkr_rbrKnowledgeSoundness                                            | 
ABSENT  | Protocol (generic)   | openingPhase                                                         | 
ABSENT  | Protocol (generic)   | encode                                                               | 
ABSENT  | Protocol (generic)   | encode_column_weight                                                 | 
ABSENT  | Protocol (generic)   | whirOpen                                                             | 
ABSENT  | Protocol (generic)   | whirError                                                            | 
ABSENT  | Protocol (generic)   | whirOpen_rbrSoundness                                                | 
ABSENT  | Protocol (generic)   | McaJohnson                                                           | 
ABSENT  | Protocol (generic)   | merkleRoot                                                           | 
ABSENT  | Protocol (generic)   | merkleVerify                                                         | 
ABSENT  | Protocol (generic)   | blake2sBytes                                                         | 
ABSENT  | Arithmetization      | Expression.toMvPolynomial                                            | 
ABSENT  | Arithmetization      | degreeBound                                                          | 
ABSENT  | Arithmetization      | M3Table                                                              | 
ABSENT  | Arithmetization      | Component.toM3                                                       | 
ABSENT  | Arithmetization      | Ensemble.toM3                                                        | 
ABSENT  | Arithmetization      | toM3_constraints_iff                                                 | 
ABSENT  | Arithmetization      | toM3_flushes_eq                                                      | 
ABSENT  | Protocol (leanVM)    | Sizes                                                                | 
ABSENT  | Protocol (leanVM)    | Sizes.Admissible                                                     | 
ABSENT  | Protocol (leanVM)    | leanIsaInstance                                                      | 
ABSENT  | Protocol (leanVM)    | stackOf                                                              | 
ABSENT  | Protocol (leanVM)    | witnessOf                                                            | 
ABSENT  | Protocol (leanVM)    | satisfiedBy_witnessOf                                                | 
ABSENT  | Protocol (leanVM)    | m3Holds_stackOf                                                      | 
ABSENT  | Protocol (leanVM)    | witnessOf_stackOf                                                    | 
ABSENT  | Protocol (leanVM)    | busPhase                                                             | 
ABSENT  | Protocol (leanVM)    | leaf_decomposition                                                   | 
ABSENT  | Protocol (leanVM)    | tableSumcheck                                                        | 
ABSENT  | Protocol (leanVM)    | tableSummand                                                         | 
ABSENT  | Protocol (leanVM)    | FlockInterface                                                       | 
ABSENT  | Protocol (leanVM)    | piopError_le                                                         | 
ABSENT  | Protocol (leanVM)    | leanVmIopp                                                           | 
ABSENT  | Protocol (leanVM)    | FsState                                                              | 
ABSENT  | Protocol (leanVM)    | Proof                                                                | 
ABSENT  | Protocol (leanVM)    | verify                                                               | 
ABSENT  | Protocol (leanVM)    | settleFixedClaims                                                    | 
ABSENT  | Protocol (leanVM)    | verify_iff_compiled                                                  | 
ABSENT  | Protocol (leanVM)    | FiatShamirSecurity                                                   | 
ABSENT  | Protocol (leanVM)    | BcsSecurity                                                          | 
ABSENT  | Protocol (leanVM)    | verify_knowledgeSound                                                | 
ABSENT  | Protocol (leanVM)    | niError                                                              | 
ABSENT  | Protocol (leanVM)    | baseVerifier_extractsExecution                                       | 
ABSENT  | Protocol (leanVM)    | baseProver_complete                                                  | 
ABSENT  | Parameters           | initialFold                                                          | 
ABSENT  | Parameters           | subsequentFold                                                       | 
ABSENT  | Parameters           | initialReduction                                                     | 
ABSENT  | Parameters           | subsequentReduction                                                  | 
ABSENT  | Parameters           | residualMaxLog                                                       | 
ABSENT  | Parameters           | queryGrindingBits                                                    | 
ABSENT  | Parameters           | ladder                                                               | 
ABSENT  | Parameters           | novelBasis                                                           | 
{'DECL': 127, 'FIELD': 3, 'ABSENT': 64}
```

### `unlisted_public.py`

Non-private declarations under `LeanerVM/Protocol/` that the interface list omits (§B.5, item 1; finding H.13). Output `unlisted_public.out`; reproduced: its per-file summary.

Command: `python3 unlisted_public.py`

```python
#!/usr/bin/env python3
"""Probe (read-only): non-private declarations under LeanerVM/Protocol/ whose final name
component does not occur anywhere in the blueprint's interface list (lines 1366-1416).
The blueprint says 'Everything not listed is a proof, a helper, or a test.'"""
import re, os, glob
root="/home/scaraven/Documents/Verified-zkEVM/leanerVM"
bp=open(os.path.join(root,"docs/roadmap/protocol-blueprint.md")).read().split("\n")
listed=" ".join(bp[1365:1416])
listed_names=set(t.split(".")[-1].strip("{},()") for t in listed.split())
whole=" ".join(bp)
KW=r"(def|theorem|lemma|structure|inductive|abbrev|instance|class)"
rx=re.compile(r"^(?P<mods>(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|public)\s+)*)"+KW+r"\s+(?P<name>[^\s:({\[]+)")
tot=0; unl=[]; perfile={}
for f in sorted(glob.glob(os.path.join(root,"LeanerVM/Protocol/**/*.lean"),recursive=True)):
    rel=os.path.relpath(f,root)
    for i,l in enumerate(open(f).read().split("\n"),1):
        m=rx.match(l)
        if not m or "private" in m.group("mods"): continue
        kind=m.group(2); name=m.group("name")
        if kind=="instance" and name in (":",): continue
        short=name.split(".")[-1]
        tot+=1
        perfile.setdefault(rel,[0,0])[0]+=1
        if short not in listed_names:
            inbp = short in whole
            unl.append((rel,i,kind,name,inbp)); perfile[rel][1]+=1
print(f"non-private declarations under LeanerVM/Protocol: {tot}; not in the interface list: {len(unl)}")
for rel,(a,b) in perfile.items(): print(f"  {rel}: {a} declarations, {b} unlisted")
print()
for rel,i,kind,name,inbp in unl:
    if kind in ("def","structure","abbrev","inductive","class") :
        print(f"  {rel}:{i}: {kind} {name}" + ("" if inbp else "   [name appears nowhere in the blueprint]"))
```

Output:

```text
non-private declarations under LeanerVM/Protocol: 333; not in the interface list: 198
  LeanerVM/Protocol/BlockClaims.lean: 8 declarations, 7 unlisted
  LeanerVM/Protocol/ClaimWeights.lean: 4 declarations, 2 unlisted
  LeanerVM/Protocol/Field.lean: 11 declarations, 7 unlisted
  LeanerVM/Protocol/FixedColumns.lean: 13 declarations, 6 unlisted
  LeanerVM/Protocol/Padding.lean: 6 declarations, 2 unlisted
  LeanerVM/Protocol/PublicInput.lean: 21 declarations, 18 unlisted
  LeanerVM/Protocol/Spine/Compose.lean: 19 declarations, 0 unlisted
  LeanerVM/Protocol/Spine/Instance.lean: 22 declarations, 4 unlisted
  LeanerVM/Protocol/Spine/Phase.lean: 6 declarations, 0 unlisted
  LeanerVM/Protocol/Spine/Seams.lean: 23 declarations, 2 unlisted
  LeanerVM/Protocol/Spine/Toy.lean: 11 declarations, 6 unlisted
  LeanerVM/Protocol/Stack.lean: 9 declarations, 3 unlisted
  LeanerVM/Protocol/ToArkLib/Component.lean: 9 declarations, 3 unlisted
  LeanerVM/Protocol/ToArkLib/GuardedVerdict.lean: 2 declarations, 2 unlisted
  LeanerVM/Protocol/ToArkLib/KeepOracles.lean: 2 declarations, 2 unlisted
  LeanerVM/Protocol/ToArkLib/KnowledgeAppend.lean: 25 declarations, 23 unlisted
  LeanerVM/Protocol/ToArkLib/Oracles.lean: 3 declarations, 1 unlisted
  LeanerVM/Protocol/ToArkLib/PassThrough.lean: 11 declarations, 8 unlisted
  LeanerVM/Protocol/ToArkLib/Refinement.lean: 5 declarations, 2 unlisted
  LeanerVM/Protocol/ToArkLib/SendOracle.lean: 17 declarations, 16 unlisted
  LeanerVM/Protocol/ToCompPoly/AmbientStacking.lean: 10 declarations, 9 unlisted
  LeanerVM/Protocol/ToCompPoly/BitProductTable.lean: 13 declarations, 9 unlisted
  LeanerVM/Protocol/ToCompPoly/Multilinear.lean: 43 declarations, 35 unlisted
  LeanerVM/Protocol/ToCompPoly/Stacking.lean: 38 declarations, 29 unlisted
  LeanerVM/Protocol/ToVCVio/UniformSample.lean: 2 declarations, 2 unlisted

  LeanerVM/Protocol/BlockClaims.lean:69: def ambientPoint   [name appears nowhere in the blueprint]
  LeanerVM/Protocol/BlockClaims.lean:73: def weight
  LeanerVM/Protocol/BlockClaims.lean:78: def IsValid   [name appears nowhere in the blueprint]
  LeanerVM/Protocol/Field.lean:65: structure rather
  LeanerVM/Protocol/Field.lean:74: def finEquivK   [name appears nowhere in the blueprint]
  LeanerVM/Protocol/Field.lean:86: def limbsEquiv   [name appears nowhere in the blueprint]
  LeanerVM/Protocol/FixedColumns.lean:56: def idxColumnEval
  LeanerVM/Protocol/FixedColumns.lean:75: def bytecodeSlotColumn   [name appears nowhere in the blueprint]
  LeanerVM/Protocol/FixedColumns.lean:108: def bytecodeColumnEval
  LeanerVM/Protocol/PublicInput.lean:65: def linePoint
  LeanerVM/Protocol/PublicInput.lean:99: def pSpec
  LeanerVM/Protocol/PublicInput.lean:111: def error
  LeanerVM/Protocol/PublicInput.lean:119: def lineValue
```

### `check_leanvm_citations.py`

Every citation `file:line` into the pinned leanVM sources in the blueprint and the status: the candidate files at `a386121f` and whether the cited range lies inside each (§B.10). The check is range-in-file and a look at the first cited line, not a reading of the content. Output `leanvm_citations.out`; reproduced: its two summary lines. Its "unresolved or out of range" counts candidates in other crates or in `doc/leanvm/drafts/`; a regrouping of the output by citation (below) finds that every one of the 89 citation groups has at least one candidate in range.

Command: `python3 check_leanvm_citations.py`

```python
#!/usr/bin/env python3
"""Probe (read-only): every citation `file.ext:N[-M][, N-M]` into the pinned leanVM sources in
the blueprint and the status. Reports: the file resolved in the leanVM checkout (at the pin),
its length, whether each cited range lies inside it, and the first cited line (trimmed)."""
import re, os, sys, subprocess, collections
lv="/home/scaraven/Documents/leanEthereum/leanVM"
root="/home/scaraven/Documents/Verified-zkEVM/leanerVM"
allfiles=subprocess.run(["git","ls-files"],cwd=lv,capture_output=True,text=True).stdout.split("\n")
def resolve(path):
    path=path.strip("`")
    c=[f for f in allfiles if f.endswith("/"+path) or f==path]
    if not c:
        base=os.path.basename(path)
        c=[f for f in allfiles if os.path.basename(f)==base and (os.path.dirname(path)=="" or os.path.dirname(path).split("/")[-1] in f)]
    return c
rx=re.compile(r"`?((?:[A-Za-z0-9_\-]+/)*[A-Za-z0-9_\-]+\.(?:rs|py|tex)):(\d+(?:[-–]\d+)?(?:, ?\d+(?:[-–]\d+)?)*)`?")
for doc in ["docs/roadmap/protocol-blueprint.md","docs/roadmap/protocol-status.md"]:
    print("=====",doc)
    seen=collections.OrderedDict()
    for i,l in enumerate(open(os.path.join(root,doc)).read().split("\n"),1):
        for m in rx.finditer(l):
            seen.setdefault((m.group(1),m.group(2)),[]).append(i)
    bad=0; amb=0; n=0
    for (path,ranges),lines in seen.items():
        n+=1
        c=resolve(path)
        if len(c)==0:
            print(f"  UNRESOLVED {path}:{ranges}  (doc lines {lines})"); bad+=1; continue
        if len(c)>1:
            amb+=1
            print(f"  AMBIGUOUS  {path}:{ranges} -> {c}  (doc lines {lines})"); 
        for f in c[:3]:
            ls=open(os.path.join(lv,f),errors="replace").read().split("\n")
            for r in re.split(r", ?",ranges):
                a=r.replace("–","-").split("-"); lo=int(a[0]); hi=int(a[-1])
                ok = 1<=lo<=hi<=len(ls)
                first=ls[lo-1].strip()[:80] if lo<=len(ls) else ""
                flag="ok " if ok else "OUT"
                if not ok: bad+=1
                print(f"  {flag} {f}:{r} [{len(ls)} lines] (doc {lines[0]}) | {first}")
    print(f"  -- {n} distinct citations, {bad} unresolved or out of range, {amb} ambiguous")
```

Output:

```text
===== docs/roadmap/protocol-blueprint.md
  -- 38 distinct citations, 2 unresolved or out of range, 4 ambiguous
===== docs/roadmap/protocol-status.md
  -- 43 distinct citations, 12 unresolved or out of range, 18 ambiguous
```

### `check_lib_citations.py`

Every library declaration the blueprint cites with a file and line, looked up in `.lake/packages/` at the old pins (§B.10).

Command: `python3 check_lib_citations.py`

```python
#!/usr/bin/env python3
"""Probe (read-only): the blueprint's citations into the pinned libraries
(docs/roadmap/protocol-blueprint.md:234-251, 273-279, 290-295). For each (file, cited lines,
declaration names) report where the declaration actually is in the pinned sources under
.lake/packages/."""
import re, os
root="/home/scaraven/Documents/Verified-zkEVM/leanerVM/.lake/packages"
A="Arklib/ArkLib/"; C="CompPoly/CompPoly/"; CL="Clean/Clean/"; V="VCVio/VCVio/"
checks=[
 (A+"OracleReduction/ProtocolSpec/Basic.lean", "", ["ProtocolSpec","Direction","MessageIdx","ChallengeIdx","FullTranscript","Transcript"]),
 (A+"OracleReduction/OracleInterface.lean","53-73",["OracleInterface"]),
 (A+"OracleReduction/OracleInterface.lean","93 (status E8)",["instDefault"]),
 (A+"OracleReduction/Basic.lean","222-669",["Prover","Verifier","OracleVerifier","Reduction","OracleReduction","OracleProof"]),
 (A+"OracleReduction/Basic.lean","1011 (status)",["PureForm"]),
 (A+"OracleReduction/Security/Basic.lean","89-103, 460-469",["completeness","perfectCompleteness"]),
 (A+"OracleReduction/Security/Basic.lean","248-359",["knowledgeSoundness","Straightline"]),
 (A+"OracleReduction/Security/Basic.lean","193 (status)",["perfectCompleteness_of_run_support"]),
 (A+"OracleReduction/Security/RoundByRound.lean","77-190, 416, 534, 606, 553",["KnowledgeStateFunction","RoundByRound","rbrKnowledgeSoundness","rbrKnowledgeSoundnessWorstCase","rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness","rbrKnowledgeSoundnessWorstCaseWith"]),
 (A+"OracleReduction/Security/Implications.lean","85",["rbrKnowledgeSoundness_implies_rbrSoundness","rbrKnowledgeSoundness_implies_knowledgeSoundness","rbrSoundness_implies_soundness"]),
 (A+"OracleReduction/Composition/Sequential/Append/Basic.lean","709",["append"]),
 (A+"OracleReduction/Composition/Sequential/General.lean","255",["seqCompose"]),
 (A+"OracleReduction/Composition/Sequential/Completeness.lean","",["seqCompose_perfectCompleteness_of_pure"]),
 (A+"OracleReduction/Composition/Sequential/Append/Completeness.lean","",["append_perfectCompleteness_of_pure_verifiers","append_perfectCompleteness_of_guarded_verifiers"]),
 (A+"OracleReduction/Composition/Sequential/GuardedNary.lean","",["seqCompose_completeness_of_guarded_verifiers"]),
 (A+"OracleReduction/Composition/Sequential/Append/RoundByRound.lean","37",["append_rbrSoundnessWorstCase_of_pure_first"]),
 (A+"OracleReduction/Composition/Sequential/Append/StateFunction.lean","292, 75",["append"]),
 (A+"OracleReduction/Composition/Sequential/Append/Security.lean","(status: 4 sorries)",["append_knowledgeSoundness","append_rbrKnowledgeSoundness"]),
 (A+"OracleReduction/Security/CoordinateWiseSpecialSoundness/Guarded.lean","112 (status)",["GuardedForm"]),
 (A+"ProofSystem/Sumcheck/Spec/General.lean","171",["reduction"]),
 (A+"ProofSystem/Sumcheck/Spec/SingleRound.lean","130-144",["StatementRound","relationRound","verifier_rbrKnowledgeSoundness"]),
 (A+"ProofSystem/Sumcheck/Spec/Domain.lean","",["Domain"]),
 (A+"Data/MvPolynomial/Multilinear.lean","",["MLE","eqPolynomial","eqTilde","eqTilde_append","MLE_eq_zero_iff","MLEEquivFin"]),
 (A+"ToCompPoly/Multilinear/Basic.lean","56",["eval_eq_MvPolynomial_MLE"]),
 (A+"Data/MvPolynomial/SchwartzZippelCounting.lean","",["schwartz_zippel_counting","prob_eval_zero_le_div"]),
 (A+"OracleReduction/FiatShamir/Basic.lean","114-138",["fiatShamir","fsChallengeOracle","fiatShamir_completeness"]),
 (A+"Commitments/Functional/Basic.lean","",["Scheme","binding","perfectCorrectness_of_opening_perfectCompleteness","extractability"]),
 (A+"ProofSystem/ToyProblem/Codegen.lean","",[]),
 (A+"Data/Fin/Basic.lean","93 (status)",["induction_two"]),
 (A+"OracleReduction/Execution.lean","642, 663, 343 (status)",["run_of_verifier_first","run_of_prover_first","support_run_pure_verifier"]),
 (V+"OracleComp/Constructions/SampleableType.lean","44; 225 (status)",["SampleableType","probEvent_uniformSample"]),
 (V+"OracleComp/SimSemantics/OptionT/Basic.lean","49, 214 (status)",["simulateQ_optionT_bind_run","simulateQ_optionT_failure"]),
 (C+"Multilinear/Basic.lean","47; 410-632; status 475,499,520,543,600,632,482,512",["CMlPolynomialEval","evalMle","evalMleLayer","evalMle_succ","eval₂Mle","eval_mle_eq_eval","eqTilde","eqTilde_eq_prod","eqTilde_append","lagrangeBasis","evalMleLayer_get"]),
 (C+"Multilinear/Equiv.lean","",["toMvPolynomialDeg1","equivMvPolynomialDeg1"]),
 (C+"Multivariate/CMvPolynomial.lean","55-85; 231 (review)",["totalDegree"]),
 (C+"Fields/Binary/BF64/Ext3.lean","171, 199 (status)",["card_ext3"]),
 (C+"Fields/Binary/BF64/Impl.lean","391 (status)",["Fintype"]),
 (CL+"Circuit/Expression.lean","6-90; 71",["Expression","eval","fromArray"]),
 (CL+"Air/FlatComponent.lean","21; 151-186",["operations","Table","Constraints","environment"]),
 (CL+"Circuit/Operations.lean","404-432; 168-182",["constraints","interactions","constraintsHold_iff_forall_mem"]),
 (CL+"Circuit/Channel.lean","101-105, 305-329",["AbstractInteraction","Interaction"]),
 (CL+"Air/FlatEnsemble.lean","19-25; 361; 342; 353-360",["EnsembleWitness","Statement","BalancedChannels"]),
 (CL+"Circuit/WitnessGeneration.lean","82",["witgen"]),
]
KW=r"(?:def|theorem|lemma|structure|inductive|abbrev|instance|class|opaque)"
for f,cited,names in checks:
    p=os.path.join(root,f)
    if not os.path.exists(p):
        print(f"MISSING FILE  {f}   (cited {cited})"); continue
    ls=open(p).read().split("\n")
    print(f"{f}  [{len(ls)} lines]  cited: {cited}")
    for n in names:
        rx=re.compile(r"(?:^|\s)%s\s+(?:[^\s.]+\.)*%s(?=\s|$|\{|\(|\[|:)"%(KW,re.escape(n)))
        hits=[i for i,l in enumerate(ls,1) if rx.search(l)]
        sor=""
        print(f"    {n}: decl at {hits[:8] if hits else 'NOT FOUND as a declaration'}")
    ns=sum(1 for l in ls if re.search(r"\bsorry\b",l))
    if ns: print(f"    (lines containing 'sorry': {ns})")
```

Output:

```text
Arklib/ArkLib/OracleReduction/ProtocolSpec/Basic.lean  [976 lines]  cited: 
    ProtocolSpec: decl at [31]
    Direction: decl at NOT FOUND as a declaration
    MessageIdx: decl at [52]
    ChallengeIdx: decl at [57]
    FullTranscript: decl at [105]
    Transcript: decl at [262]
Arklib/ArkLib/OracleReduction/OracleInterface.lean  [410 lines]  cited: 53-73
    OracleInterface: decl at [55]
Arklib/ArkLib/OracleReduction/OracleInterface.lean  [410 lines]  cited: 93 (status E8)
    instDefault: decl at [93]
Arklib/ArkLib/OracleReduction/Basic.lean  [1025 lines]  cited: 222-669
    Prover: decl at [223]
    Verifier: decl at [248]
    OracleVerifier: decl at [323]
    Reduction: decl at [625]
    OracleReduction: decl at [633]
    OracleProof: decl at [669]
    (lines containing 'sorry': 2)
Arklib/ArkLib/OracleReduction/Basic.lean  [1025 lines]  cited: 1011 (status)
    PureForm: decl at [1011]
    (lines containing 'sorry': 2)
Arklib/ArkLib/OracleReduction/Security/Basic.lean  [766 lines]  cited: 89-103, 460-469
    completeness: decl at [89, 460, 537, 566]
    perfectCompleteness: decl at [103, 469, 542, 575]
    (lines containing 'sorry': 1)
Arklib/ArkLib/OracleReduction/Security/Basic.lean  [766 lines]  cited: 248-359
    knowledgeSoundness: decl at [344, 500, 553, 593]
    Straightline: decl at [248]
    (lines containing 'sorry': 1)
Arklib/ArkLib/OracleReduction/Security/Basic.lean  [766 lines]  cited: 193 (status)
    perfectCompleteness_of_run_support: decl at [193]
    (lines containing 'sorry': 1)
Arklib/ArkLib/OracleReduction/Security/RoundByRound.lean  [903 lines]  cited: 77-190, 416, 534, 606, 553
    KnowledgeStateFunction: decl at [164, 719, 789]
    RoundByRound: decl at [77]
    rbrKnowledgeSoundness: decl at [416, 738, 777, 809]
    rbrKnowledgeSoundnessWorstCase: decl at [534]
    rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness: decl at [606]
    rbrKnowledgeSoundnessWorstCaseWith: decl at [553]
Arklib/ArkLib/OracleReduction/Security/Implications.lean  [417 lines]  cited: 85
    rbrKnowledgeSoundness_implies_rbrSoundness: decl at [87]
    rbrKnowledgeSoundness_implies_knowledgeSoundness: decl at [223]
    rbrSoundness_implies_soundness: decl at [79]
    (lines containing 'sorry': 12)
Arklib/ArkLib/OracleReduction/Composition/Sequential/Append/Basic.lean  [724 lines]  cited: 709
    append: decl at [58, 212, 236, 243, 619, 709]
Arklib/ArkLib/OracleReduction/Composition/Sequential/General.lean  [553 lines]  cited: 255
    seqCompose: decl at [42, 80, 109, 140, 187, 255]
    (lines containing 'sorry': 3)
Arklib/ArkLib/OracleReduction/Composition/Sequential/Completeness.lean  [82 lines]  cited: 
    seqCompose_perfectCompleteness_of_pure: decl at [66]
Arklib/ArkLib/OracleReduction/Composition/Sequential/Append/Completeness.lean  [273 lines]  cited: 
    append_perfectCompleteness_of_pure_verifiers: decl at [163, 259]
    append_perfectCompleteness_of_guarded_verifiers: decl at NOT FOUND as a declaration
Arklib/ArkLib/OracleReduction/Composition/Sequential/GuardedNary.lean  [94 lines]  cited: 
    seqCompose_completeness_of_guarded_verifiers: decl at [45]
Arklib/ArkLib/OracleReduction/Composition/Sequential/Append/RoundByRound.lean  [145 lines]  cited: 37
    append_rbrSoundnessWorstCase_of_pure_first: decl at [37]
Arklib/ArkLib/OracleReduction/Composition/Sequential/Append/StateFunction.lean  [692 lines]  cited: 292, 75
    append: decl at [39, 75, 292]
Arklib/ArkLib/OracleReduction/Composition/Sequential/Append/Security.lean  [197 lines]  cited: (status: 4 sorries)
    append_knowledgeSoundness: decl at [58, 148]
    append_rbrKnowledgeSoundness: decl at [94, 180]
    (lines containing 'sorry': 4)
Arklib/ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Guarded.lean  [674 lines]  cited: 112 (status)
    GuardedForm: decl at [112]
Arklib/ArkLib/ProofSystem/Sumcheck/Spec/General.lean  [238 lines]  cited: 171
    reduction: decl at [172]
Arklib/ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean  [1285 lines]  cited: 130-144
    StatementRound: decl at [130]
    relationRound: decl at [144]
    verifier_rbrKnowledgeSoundness: decl at [729, 1091]
    (lines containing 'sorry': 15)
MISSING FILE  Arklib/ArkLib/ProofSystem/Sumcheck/Spec/Domain.lean   (cited )
Arklib/ArkLib/Data/MvPolynomial/Multilinear.lean  [427 lines]  cited: 
    MLE: decl at [151]
    eqPolynomial: decl at [88]
    eqTilde: decl at [95]
    eqTilde_append: decl at [116]
    MLE_eq_zero_iff: decl at [252]
    MLEEquivFin: decl at [421]
Arklib/ArkLib/ToCompPoly/Multilinear/Basic.lean  [88 lines]  cited: 56
    eval_eq_MvPolynomial_MLE: decl at [56]
Arklib/ArkLib/Data/MvPolynomial/SchwartzZippelCounting.lean  [215 lines]  cited: 
    schwartz_zippel_counting: decl at [30]
    prob_eval_zero_le_div: decl at [131]
Arklib/ArkLib/OracleReduction/FiatShamir/Basic.lean  [180 lines]  cited: 114-138
    fiatShamir: decl at [114, 130, 140]
    fsChallengeOracle: decl at NOT FOUND as a declaration
    fiatShamir_completeness: decl at [163]
    (lines containing 'sorry': 1)
Arklib/ArkLib/Commitments/Functional/Basic.lean  [364 lines]  cited: 
    Scheme: decl at [67]
    binding: decl at [220]
    perfectCorrectness_of_opening_perfectCompleteness: decl at [128]
    extractability: decl at [250]
Arklib/ArkLib/ProofSystem/ToyProblem/Codegen.lean  [102 lines]  cited: 
Arklib/ArkLib/Data/Fin/Basic.lean  [356 lines]  cited: 93 (status)
    induction_two: decl at [93]
    (lines containing 'sorry': 1)
Arklib/ArkLib/OracleReduction/Execution.lean  [726 lines]  cited: 642, 663, 343 (status)
    run_of_verifier_first: decl at [642]
    run_of_prover_first: decl at [653, 663]
    support_run_pure_verifier: decl at [343]
    (lines containing 'sorry': 1)
VCVio/VCVio/OracleComp/Constructions/SampleableType.lean  [757 lines]  cited: 44; 225 (status)
    SampleableType: decl at [44, 270]
    probEvent_uniformSample: decl at [225]
VCVio/VCVio/OracleComp/SimSemantics/OptionT/Basic.lean  [264 lines]  cited: 49, 214 (status)
    simulateQ_optionT_bind_run: decl at [49]
    simulateQ_optionT_failure: decl at [214]
CompPoly/CompPoly/Multilinear/Basic.lean  [1106 lines]  cited: 47; 410-632; status 475,499,520,543,600,632,482,512
    CMlPolynomialEval: decl at [47]
    evalMle: decl at [499]
    evalMleLayer: decl at [475]
    evalMle_succ: decl at [512]
    eval₂Mle: decl at [520]
    eval_mle_eq_eval: decl at [586]
    eqTilde: decl at [543]
    eqTilde_eq_prod: decl at [600]
    eqTilde_append: decl at [632]
    lagrangeBasis: decl at [410]
    evalMleLayer_get: decl at [482]
CompPoly/CompPoly/Multilinear/Equiv.lean  [358 lines]  cited: 
    toMvPolynomialDeg1: decl at [183, 342]
    equivMvPolynomialDeg1: decl at [200]
CompPoly/CompPoly/Multivariate/CMvPolynomial.lean  [304 lines]  cited: 55-85; 231 (review)
    totalDegree: decl at [231]
CompPoly/CompPoly/Fields/Binary/BF64/Ext3.lean  [203 lines]  cited: 171, 199 (status)
    card_ext3: decl at [199]
CompPoly/CompPoly/Fields/Binary/BF64/Impl.lean  [459 lines]  cited: 391 (status)
    Fintype: decl at NOT FOUND as a declaration
Clean/Clean/Circuit/Expression.lean  [212 lines]  cited: 6-90; 71
    Expression: decl at [12]
    eval: decl at [86]
    fromArray: decl at [71]
Clean/Clean/Air/FlatComponent.lean  [519 lines]  cited: 21; 151-186
    operations: decl at [21]
    Table: decl at [151]
    Constraints: decl at [184, 496]
    environment: decl at [163]
Clean/Clean/Circuit/Operations.lean  [1314 lines]  cited: 404-432; 168-182
    constraints: decl at [68, 404]
    interactions: decl at [78, 428]
    constraintsHold_iff_forall_mem: decl at [176]
Clean/Clean/Circuit/Channel.lean  [427 lines]  cited: 101-105, 305-329
    AbstractInteraction: decl at [101]
    Interaction: decl at [305]
Clean/Clean/Air/FlatEnsemble.lean  [544 lines]  cited: 19-25; 361; 342; 353-360
    EnsembleWitness: decl at [19]
    Statement: decl at [361]
    BalancedChannels: decl at [342]
Clean/Clean/Circuit/WitnessGeneration.lean  [108 lines]  cited: 82
    witgen: decl at [55, 82]
```

### `vocab_counts.py`

Whole-word counts of the competing terms (§C).

Command: `python3 vocab_counts.py`

```python
#!/usr/bin/env python3
"""Probe (read-only): occurrences of competing terms, per document (case-insensitive,
whole words)."""
import re, os
root="/home/scaraven/Documents/Verified-zkEVM/leanerVM"
P=os.path.join(root,".claude/reports/blueprint-review/probes/docs-debt")
docs=[("blueprint","docs/roadmap/protocol-blueprint.md"),("status","docs/roadmap/protocol-status.md"),
("tracker",P+"/issue-12-body.md"),("holes",P+"/issue-12-comment-5833669972.md"),
("rev-spine","docs/reviews/protocol-spine.md"),("rev-L1","docs/reviews/protocol-layer1.md"),("rev-PI","docs/reviews/public-input-phase.md"),
("arch","docs/architecture.md"),("reuse","docs/roadmap/leanth-reuse.md")]
terms=[
 ("roadmap",r"\broadmaps?\b"),("blueprint",r"\bblueprints?\b"),
 ("hole(s)",r"\bholes?\b"),("layer(s)",r"\blayers?\b"),("unit(s) of work",r"\bunits? of work\b|\bunit\b"),("slice(s)",r"\bslices?\b"),("leaf/leaves",r"\bleaf\b|\bleaves\b"),("half/halves",r"\bhalf\b|\bhalves\b"),
 ("dashboard",r"\bdashboard\b"),("tracker",r"\btracker\b"),("tracking issue",r"\btracking issue\b"),
 ("ledger",r"\bledger\b"),("upstream ledger",r"\bupstream ledger\b"),("upstream watch",r"\bupstream[- ]watch\b"),
 ("seam(s)",r"\bseams?\b"),("interface(s)",r"\binterfaces?\b"),("boundary",r"\bboundar(?:y|ies)\b"),
 ("phase(s)",r"\bphases?\b"),("reduction(s)",r"\breductions?\b"),("component(s)",r"\bcomponents?\b"),("stage(s)",r"\bstages?\b"),
 ("stack",r"\bstack\b"),("stacked",r"\bstacked\b"),("oracle",r"\boracle\b"),("committed column/polynomial",r"\bcommitted (?:column|polynomial)\b"),
 ("limb(s)",r"\blimbs?\b"),("lane(s)",r"\blanes?\b"),
 ("claim pool",r"\bclaim pool\b"),("pool/pooled",r"\bpool(?:ed|s)?\b"),
 ("landed/lands",r"\bland(?:ed|s)\b"),("built",r"\bbuilt\b"),("on `main`",r"on `main`"),("merged",r"\bmerged\b"),("claimed",r"\bclaimed\b"),("met",r"\bmet\b"),
 ("the wall",r"\bthe wall\b|\*The wall\*"),
 ("adaptor",r"\badaptor\b"),("adapter",r"\badapter\b"),("bridge",r"\bbridge\b"),("refinement",r"\brefinement\b"),
 ("oracle protocol",r"\boracle protocol\b"),("PIOP/piop",r"piop"),("IOR",r"\bIOR\b"),("IOPP",r"\bIOPP\b|Iopp"),
 ("flush(es)",r"\bflush(?:es)?\b"),("interaction(s)",r"\binteractions?\b"),
 ("side",r"\bsides?\b"),("direction",r"\bdirections?\b"),
 ("public input",r"\bpublic[- ]input\b"),("public statement",r"\bpublic statement\b"),("public words",r"\bpublic words?\b"),("public line(s)",r"\bpublic lines?\b"),
 ("pin/pinned",r"\bpin(?:ned|s)?\b"),
 ("Category A/B",r"\bCategory [AB]\b"),
 ("finding(s)",r"\bfindings?\b"),("decision(s)",r"\bdecisions?\b"),("acceptance test",r"\bacceptance tests?\b"),
 ("M3",r"\bM3\b"),
]
print("term | "+" | ".join(d for d,_ in docs))
for name,rx in terms:
    row=[]
    for d,p in docs:
        path=p if p.startswith("/") else os.path.join(root,p)
        row.append(str(len(re.findall(rx,open(path).read(),flags=re.I))))
    print(f"{name} | "+" | ".join(row))
```

Output:

```text
term | blueprint | status | tracker | holes | rev-spine | rev-L1 | rev-PI | arch | reuse
roadmap | 25 | 16 | 13 | 2 | 9 | 7 | 7 | 1 | 22
blueprint | 5 | 3 | 3 | 11 | 16 | 9 | 12 | 0 | 3
hole(s) | 48 | 19 | 29 | 21 | 18 | 1 | 4 | 0 | 0
layer(s) | 172 | 57 | 20 | 40 | 27 | 13 | 21 | 9 | 40
unit(s) of work | 29 | 1 | 2 | 2 | 4 | 0 | 2 | 0 | 0
slice(s) | 9 | 4 | 1 | 3 | 8 | 1 | 0 | 0 | 4
leaf/leaves | 26 | 10 | 5 | 5 | 7 | 5 | 0 | 0 | 1
half/halves | 10 | 12 | 8 | 9 | 10 | 2 | 1 | 0 | 4
dashboard | 7 | 2 | 0 | 1 | 0 | 1 | 0 | 0 | 0
tracker | 2 | 0 | 1 | 1 | 0 | 0 | 0 | 0 | 0
tracking issue | 1 | 2 | 0 | 0 | 0 | 0 | 0 | 0 | 0
ledger | 24 | 10 | 5 | 8 | 1 | 0 | 1 | 0 | 12
upstream ledger | 2 | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 0
upstream watch | 3 | 1 | 2 | 5 | 0 | 0 | 0 | 0 | 0
seam(s) | 62 | 14 | 20 | 23 | 46 | 1 | 16 | 0 | 2
interface(s) | 28 | 3 | 5 | 5 | 3 | 1 | 1 | 12 | 3
boundary | 17 | 0 | 2 | 4 | 11 | 0 | 0 | 12 | 3
phase(s) | 131 | 67 | 32 | 33 | 69 | 9 | 31 | 0 | 4
reduction(s) | 17 | 7 | 0 | 3 | 1 | 0 | 3 | 0 | 2
component(s) | 60 | 17 | 10 | 6 | 27 | 0 | 8 | 8 | 10
stage(s) | 3 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 2
stack | 41 | 7 | 4 | 3 | 16 | 10 | 12 | 1 | 7
stacked | 6 | 8 | 2 | 0 | 0 | 0 | 0 | 2 | 0
oracle | 51 | 9 | 2 | 4 | 12 | 1 | 1 | 7 | 7
committed column/polynomial | 2 | 0 | 1 | 0 | 1 | 0 | 0 | 0 | 1
limb(s) | 24 | 13 | 1 | 6 | 20 | 1 | 10 | 0 | 0
lane(s) | 5 | 1 | 0 | 1 | 0 | 0 | 0 | 1 | 0
claim pool | 5 | 1 | 0 | 2 | 0 | 0 | 2 | 0 | 1
pool/pooled | 19 | 12 | 1 | 12 | 6 | 0 | 33 | 0 | 2
landed/lands | 9 | 9 | 13 | 4 | 4 | 1 | 2 | 0 | 0
built | 8 | 5 | 0 | 2 | 3 | 2 | 0 | 0 | 1
on `main` | 0 | 10 | 5 | 2 | 0 | 1 | 1 | 0 | 1
merged | 1 | 16 | 4 | 1 | 0 | 0 | 1 | 0 | 4
claimed | 7 | 5 | 7 | 0 | 1 | 1 | 3 | 2 | 0
met | 0 | 7 | 0 | 0 | 13 | 15 | 11 | 0 | 0
the wall | 7 | 4 | 2 | 1 | 0 | 6 | 0 | 0 | 0
adaptor | 29 | 11 | 8 | 6 | 10 | 3 | 3 | 0 | 0
adapter | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 2
bridge | 11 | 1 | 1 | 0 | 1 | 0 | 0 | 6 | 4
refinement | 13 | 4 | 2 | 2 | 10 | 0 | 0 | 2 | 3
oracle protocol | 11 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | 0
PIOP/piop | 55 | 7 | 8 | 6 | 22 | 0 | 0 | 0 | 3
IOR | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
IOPP | 5 | 0 | 0 | 1 | 0 | 0 | 0 | 0 | 0
flush(es) | 12 | 2 | 1 | 1 | 8 | 0 | 0 | 0 | 0
interaction(s) | 8 | 10 | 1 | 0 | 0 | 0 | 0 | 5 | 1
side | 12 | 2 | 0 | 1 | 2 | 2 | 1 | 0 | 0
direction | 6 | 1 | 1 | 0 | 5 | 0 | 0 | 6 | 0
public input | 12 | 23 | 1 | 4 | 8 | 0 | 3 | 6 | 1
public statement | 3 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0
public words | 6 | 4 | 0 | 0 | 0 | 0 | 3 | 0 | 0
public line(s) | 4 | 4 | 4 | 1 | 3 | 0 | 2 | 0 | 0
pin/pinned | 31 | 44 | 14 | 5 | 27 | 11 | 25 | 6 | 13
Category A/B | 9 | 0 | 2 | 4 | 5 | 0 | 2 | 0 | 0
finding(s) | 18 | 30 | 3 | 5 | 10 | 7 | 10 | 0 | 2
decision(s) | 4 | 10 | 6 | 4 | 10 | 1 | 4 | 1 | 4
acceptance test | 13 | 4 | 1 | 7 | 3 | 3 | 4 | 0 | 4
M3 | 9 | 0 | 1 | 0 | 1 | 0 | 0 | 0 | 1
```

### `coverage_from_blueprint.py`

The blueprint's hole table read as a coverage check: which of each hole's "Produces" names are declared (§E.4, §B.5 item 6).

Command: `python3 coverage_from_blueprint.py`

```python
#!/usr/bin/env python3
"""Feasibility probe (read-only): derive the coverage table from the repository instead of
maintaining it by hand. Input: the blueprint's table 'The holes'
(docs/roadmap/protocol-blueprint.md:595-615), column 'Produces'. For every name in backticks
there, look for a declaration of that name under LeanerVM/. Output: per unit, how many of the
produced names are declared. No Lean is run; the repository forbids `sorry`, so a declared
theorem is a proved one."""
import re, os, glob
root="/home/scaraven/Documents/Verified-zkEVM/leanerVM"
bp=open(os.path.join(root,"docs/roadmap/protocol-blueprint.md")).read().split("\n")
rows=[l for l in bp[596:615] if l.startswith("|")]
src={f:open(f).read().split("\n") for f in glob.glob(os.path.join(root,"LeanerVM/**/*.lean"),recursive=True)}
KW=r"(?:def|theorem|lemma|structure|inductive|abbrev|instance|class|opaque)"
def declared(name):
    short=name.split(".")[-1]
    rx=re.compile(r"(?:^|\s)%s\s+(?:[^\s.]+\.)*%s(?=\s|$|\{|\(|\[|:)"%(KW,re.escape(short)))
    return any(rx.search(l) for ls in src.values() for l in ls)
print(f"{'code':8} {'unit':58} declared/produced   missing")
for r in rows:
    cells=[c.strip() for c in r.strip().strip("|").split(" | ")]
    code,unit,produces=cells[0],cells[1],cells[2]
    names=[n for n in re.findall(r"`([^`]+)`",produces) if re.match(r"^[A-Za-z_][\w.₂']*$",n) and "/" not in n]
    have=[n for n in names if declared(n)]
    miss=[n for n in names if n not in have]
    print(f"{code:8} {unit[:58]:58} {len(have):2}/{len(names):2}              {', '.join(miss)[:90]}")
```

Output:

```text
code     unit                                                       declared/produced   missing
S        the spine                                                   0/ 0              
G1       virtual sumcheck, `Sumcheck.Def` and completeness (Layer 4  0/ 3              Virtual, sumcheck, sumcheck_perfectCompleteness
G2       sumcheck rbr knowledge, `Sumcheck.Security` (Layer 4, A1)   0/ 1              sumcheck_rbrKnowledgeSoundness
G3       batching by powers, `Batch.Def` and `Security` (Layer 4)    0/ 1              batchClaims
G4       fingerprint, Lemma 5.1, the collision bound (Layer 5)       0/ 4              fingerprint, sideProduct, sideProduct_poly_eq_iff, sideProduct_collision
G5, G6   GKR: `Gkr.Def` and completeness; `Gkr.Security` (Layer 5)   0/ 2              gkr, gkrError
L1       Layer 1: tables, stacking, the fixed columns               15/15              
I1       Clean components as polynomials (Layer 2)                   0/ 4              Expression.toMvPolynomial, degreeBound, Component.toM3, Ensemble.toM3
I2       the adaptor (Layer 3)                                       0/ 6              leanIsaInstance, stackOf, witnessOf, satisfiedBy_witnessOf, m3Holds_stackOf, witnessOf_sta
P1, P2   the bus phase (Layer 6)                                     1/ 4              busPhase, leaf_decomposition, busError
P3, P4   the table sumcheck phase (Layer 7)                          1/ 4              tableSummand, tableSummand_target, tableSumcheck
P5       the public-input phase (Layer 8)                            1/ 1              
P6       the Flock phase at the flock seam (Layer 9)                 1/ 3              limbColumns, flockError_le
P7, P8   the claim pool and the opening phase (Layer 10)             3/ 4              openingPhase
C1       the knowledge-soundness append (ledger A2)                  2/ 2              
K1       WHIR over binary Reed–Solomon codes (Layer 11)              0/ 4              encode, whirOpen, whirOpen_rbrSoundness, McaJohnson
K2       Merkle, BLAKE2s bytes, the WHIR parameters (Layer 11)       0/ 4              merkleRoot, merkleVerify, blake2sBytes, ladder
K3       transcript, `Proof`, `verify`, `verify_iff_compiled`, the   0/ 0              
K4       T4 (Layer 13)                                               0/ 2              baseVerifier_extractsExecution, baseProver_complete
```

Regrouping of `leanvm_citations.out` by citation (run in this directory):

```python
import re,collections
cur=None; groups=collections.defaultdict(list)
for l in open("leanvm_citations.out"):
    if l.startswith("====="): cur=l.strip(); continue
    m=re.match(r"\s+(ok|OUT|MISSING|\?\?)\s+(\S+?):(\S+)\s.*\(doc (\d+)\)",l)
    if m:
        st,path,rng,doc=m.groups()
        groups[(cur,doc,path.split("/")[-1],rng)].append(st)
bad=[k for k,v in groups.items() if "ok" not in v]
print(len(groups),"citation groups;", len(bad),"with no resolving candidate")
```

Output: `89 citation groups; 0 with no resolving candidate`.

### Shell probes of the second pass

Run from the repository root unless stated.

```sh
# the independent recount of thirteen codes (section D); OC is the four other comments concatenated
for c in L1 G4 P5 K2 A4 C1 A18 F17 E16 S16 T4 I2 E7; do printf "%-4s" $c
  for f in docs/roadmap/protocol-blueprint.md docs/roadmap/protocol-status.md $P/issue-12-body.md \
           $P/issue-12-comment-5833669972.md $OC docs/reviews/protocol-spine.md \
           docs/reviews/protocol-layer1.md docs/reviews/public-input-phase.md; do
    printf " %3s" $(grep -oP "(?<![A-Za-z0-9_])$c(?![A-Za-z0-9_])" $f | wc -l); done; echo; done
```

```text
L1     6   6   7   0   0   0   2   0
G4     2   5   4   1   0   0   0   0
P5     2  15   3   3   3   7   0   3
K2     4   4   5   3   1   0   0   0
A4     1   4   0   0   0   6   3   2
C1     5   9   5   4   3   6   4   5
A18    0   3   1   0   0   0   0   0
F17    0   4   0   0   0   0   1   2
E16    0   5   0   0   0   0   0   1
S16    0   2   0   0   0   0   1   0
T4    11   1   2   3   0   4   0   0
I2     5   8  11   6   3  15   1   0
E7     0   1   1   0   0   1   0   0
(order: BP ST TB HC OC RS RL RP)
```

```sh
grep -rn "import LeanerVM.Arithmetization" LeanerVM/Protocol        # at b435631 and at 144c5aa
```

```text
LeanerVM/Protocol/Basic.lean:3:public import LeanerVM.Arithmetization.Basic
LeanerVM/Protocol/FixedColumns.lean:11:public import LeanerVM.Arithmetization.Bytecode
```

```sh
# VCVio at its former pin, read before the upgrade replaced the package (section B.9)
(cd .lake/packages/VCVio && git rev-parse --short HEAD)             # f9dc47d9 at the time
find .lake/packages/VCVio/VCVio/CryptoFoundations/MerkleTree -name '*.lean' | wc -l    # 19
grep -rn sorry .lake/packages/VCVio/VCVio/CryptoFoundations/MerkleTree | wc -l         # 0
# ArkLib's distance from the former pin, in the sibling checkout
(cd ../ArkLib && git rev-parse --short origin/main && git rev-list --count dca90385..origin/main \
  && git rev-list --count dca90385..66f39b4)                        # 7653a901e, 347, 246
# the tracker texts, re-read without writing
gh issue view 12 --json body -q .body | diff - probes/docs-debt/issue-12-body.md   # a trailing newline only
gh api repos/Verified-zkEVM/leanerVM/issues/comments/5833669972 -q .updated_at       # 2026-09-28T14:28:11Z
gh pr list --state open --json number,labels                        # 39, 42, 43; no labels
```
