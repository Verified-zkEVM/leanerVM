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
