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
