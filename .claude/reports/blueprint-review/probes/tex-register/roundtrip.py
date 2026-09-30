"""Check that the fragment keeps the register's wording: strip the markup from every generated
text and compare it with the register's field (backticks dropped; `.md` dropped after a dossier
name in the where and dossier columns; the added \\cref parentheticals removed)."""
import re
from load import rows, NEG, UNV
import gen, boxes

UNESC = [(r"\textbackslash{}", "\\"), (r"\textasciitilde{}", "~"), (r"\textasciicircum{}", "^"),
         (r"\{", "{"), (r"\}", "}"), (r"\_", "_"), (r"\&", "&"), (r"\%", "%"), (r"\#", "#"), (r"\$", "$")]

def untx(s):
    s = re.sub(r" \(\\cref\{[^}]*\}\)", "", s)
    s = re.sub(r"; \\cref\{[^}]*\}", "", s)
    s = s.replace(r"\allowbreak{}", "")
    s = re.sub(r"\\ensuremath\{(.)\}", r"\1", s)
    s = re.sub(r"\\code\{([^}]*)\}", r"\1", s)
    s = re.sub(r"\\texttt\{((?:\\[{}]|[^{}]|\{\})*)\}", r"\1", s)
    s = re.sub(r"\\textcolor\{\w+\}\{(\w+)\}", r"\1", s)
    s = s.replace("-{}-", "--").replace("``", '"').replace("''", '"')
    for a, b in UNESC:
        s = s.replace(a, b)
    return s

bad = 0
def chk(label, got, want):
    global bad
    if untx(got) != want:
        bad += 1
        print("MISMATCH", label, "\n  got :", untx(got)[:200], "\n  want:", want[:200])

nomd = lambda s: boxes.DOSS_RE.sub(lambda m: m.group(1), s)
for r in rows:
    for f in ("name", "cls", "status", "claim", "evid", "change", "note"):
        chk((r["id"], f), gen.tx(r[f]), r[f].replace("`", ""))
    chk((r["id"], "sev"), gen.sev_cell(r["sev"]), r["sev"].replace("`", ""))
    chk((r["id"], "where"), gen.where_cell(r)[0], nomd(r["where"]).replace("`", ""))
for n in NEG:
    for f in n:
        chk(("N", f), gen.dossier_plain(n[f]) if f == "dossier" else gen.tx(n[f]), (nomd(n[f]) if f == "dossier" else n[f]).replace("`", ""))
for u in UNV:
    for f in u:
        chk(("U", f), gen.dossier_plain(u[f]) if f == "dossier" else gen.tx(u[f]), (nomd(u[f]) if f == "dossier" else u[f]).replace("`", ""))
print("mismatches", bad)
