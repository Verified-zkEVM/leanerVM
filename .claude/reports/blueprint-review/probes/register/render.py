"""Render the register (dossiers/register.md) from rows.py. Run from this directory:
python3 -B render.py
"""
import runpy
import collections

D = runpy.run_path("rows.py")
SUBJECTS = D["SUBJECTS"]
SUBJ_IDX = {k: i for i, (k, _) in enumerate(SUBJECTS)}
SUBJ_NAME = dict(SUBJECTS)
FIND = D["FINDINGS"]
NEG = D["NEG"]
UNV = D["UNV"]
CONTRA = D["CONTRA"]
HEADER = open("header.md").read()
FOOTER_PARTS = {}

RANK_NAME = {0: "critical", 1: "major", 2: "minor", 3: "note"}


def esc(s):
    return s.replace("|", "\\|").replace("\n", " ")


def is_position(r):
    return r["sev"].startswith("—")


early = sorted([t for t in enumerate(FIND) if not t[1]["late"]],
               key=lambda t: (t[1]["rank"], SUBJ_IDX[t[1]["subj"]], t[0]))
early = [r for _, r in early]
late = [r for r in FIND if r["late"]]
for i, r in enumerate(early + late, 1):
    r["id"] = f"R{i}"
# display order: within each severity, the early rows (by subject) then the late rows
rows = []
for rank in (0, 1, 2, 3):
    rows += [r for r in early if r["rank"] == rank] + [r for r in late if r["rank"] == rank]

import re
KEYS = D["KEYS"]
KEYID = {}
for k, sub in KEYS.items():
    hits = [r for r in rows if sub in r["name"]]
    assert len(hits) == 1, (k, sub, [h["name"] for h in hits])
    KEYID[k] = hits[0]["id"]


def res(t):
    def f(m):
        k = m.group(1)
        assert k in KEYID, k
        return KEYID[k]
    return re.sub(r"\[\[([A-Za-z0-9]+)\]\]", f, t)


for r in rows:
    for fld in ("name", "sev", "where", "cls", "claim", "evid", "change", "status", "note"):
        r[fld] = res(r[fld])
for n in NEG:
    for fld in n:
        n[fld] = res(n[fld])
for u in UNV:
    for fld in u:
        u[fld] = res(u[fld])

out = [HEADER.rstrip(), ""]

# ---------------------------------------------------------------- Part 1
out.append("## Part 1. Register of findings")
out.append("")
out.append("Columns: `R#`; short name; severity as the dossiers give it (merged rows show each "
           "dossier's); subject; where the full text is (dossier and section or finding heading); "
           "classification as the dossier gives it (`—` for a finding about the code, the status, a "
           "source, or where the dossier gives none); the claim; the decisive evidence (at the pins "
           "named; Lean lines at `b435631`, blueprint lines at `b435631`, leanVM at `a386121f`); the "
           "proposed change, with a pointer to the full text; status; notes (merges, relations, "
           "`DISAGREEMENT`). Two rows are not findings but positions of one dossier that another "
           "dossier's finding contradicts; they carry no severity and sit beside the row they "
           "dispute.")
out.append("")
cols = ["R#", "Short name", "Severity", "Subject", "Where", "Classification", "Claim",
        "Decisive evidence", "Proposed change", "Status", "Notes"]
for rank in (0, 1, 2, 3):
    sel = [r for r in rows if r["rank"] == rank]
    if not sel:
        continue
    nf = len([r for r in sel if not is_position(r)])
    npos = len([r for r in sel if is_position(r)])
    out.append(f"### {RANK_NAME[rank].capitalize()} ({nf} finding{'s' if nf != 1 else ''}"
               + (f", {npos} position{'s' if npos != 1 else ''}" if npos else "")
               + ")")
    out.append("")
    out.append("| " + " | ".join(cols) + " |")
    out.append("|" + "---|" * len(cols))
    for r in sel:
        cells = [r["id"], r["name"], r["sev"], SUBJ_NAME[r["subj"]], r["where"], r["cls"],
                 r["claim"], r["evid"], r["change"], r["status"], r["note"] or "—"]
        out.append("| " + " | ".join(esc(c) for c in cells) + " |")
    out.append("")

# ---------------------------------------------------------------- Part 2
out.append("## Part 2. Negative results")
out.append("")
out.append("What a dossier says it checked and found right, with how and any caveat. Grouped by "
           "dossier, in the order the dossiers were processed.")
out.append("")
out.append("| # | Dossier | What was checked and found right | How | Caveat |")
out.append("|---|---|---|---|---|")
for i, n in enumerate(NEG, 1):
    out.append("| " + " | ".join(esc(c) for c in [f"N{i}", n["dossier"], n["what"], n["how"], n["caveat"] or "—"]) + " |")
out.append("")

# ---------------------------------------------------------------- Part 3
out.append("## Part 3. Not verified")
out.append("")
out.append("What a dossier marks unverified, written and not run, out of task, or not checkable "
           "after the upgrade, with what would verify it.")
out.append("")
out.append("| # | Dossier | Claim | Status | What would verify it |")
out.append("|---|---|---|---|---|")
for i, u in enumerate(UNV, 1):
    out.append("| " + " | ".join(esc(c) for c in [f"U{i}", u["dossier"], u["claim"], u["status"], u["verify"]]) + " |")
out.append("")
out.append("### Contradictions with the brief that the dossiers report")
out.append("")
for d, t in CONTRA:
    out.append(f"- {d}: {t}")
out.append("")

# ---------------------------------------------------------------- Part 4
out.append("## Part 4. Counts")
out.append("")
findings = [r for r in rows if not is_position(r)]
positions = [r for r in rows if is_position(r)]
cnt = collections.Counter(r["rank"] for r in findings)
out.append("### By severity (the row's place: the highest severity any dossier gives it)")
out.append("")
out.append("| Severity | Rows |")
out.append("|---|---|")
for rank in (0, 1, 2, 3):
    out.append(f"| {RANK_NAME[rank]} | {cnt[rank]} |")
out.append(f"| positions (not findings, no severity) | {len(positions)} |")
out.append(f"| **total findings** | **{len(findings)}** |")
out.append("")

out.append("### By subject and severity")
out.append("")
out.append("| Subject | critical | major | minor | note | total |")
out.append("|---|---|---|---|---|---|")
tot = collections.Counter()
for k, name in SUBJECTS:
    c = collections.Counter(r["rank"] for r in findings if r["subj"] == k)
    t = sum(c.values())
    tot.update(c)
    out.append(f"| {name} | {c[0]} | {c[1]} | {c[2]} | {c[3]} | {t} |")
out.append(f"| **all** | {tot[0]} | {tot[1]} | {tot[2]} | {tot[3]} | {sum(tot.values())} |")
out.append("")


def tags(r):
    s = r["status"]
    return {t for t in ("cited-checked", "probe-run", "paper", "unverified") if t in s}


out.append("### Critical and major rows resting on paper or with an unverified part")
out.append("")
out.append("A row is listed when its status contains `paper` or `unverified`. `probe` says whether a "
           "probe that ran also supports part of it; `cited` whether a citation check covered it.")
out.append("")
out.append("| R# | Short name | Status | probe | cited |")
out.append("|---|---|---|---|---|")
for r in findings:
    if r["rank"] > 1:
        continue
    t = tags(r)
    if "paper" in t or "unverified" in t:
        out.append("| " + " | ".join(esc(c) for c in [r["id"], r["name"], r["status"],
                   "yes" if "probe-run" in t else "no", "yes" if "cited-checked" in t else "no"]) + " |")
out.append("")

out.append("### Disagreements between dossiers")
out.append("")
for r in rows:
    if "DISAGREEMENT" in r["note"]:
        out.append(f"- {r['id']} ({r['name']}): {r['note']}")
out.append("")

out.append("### Merged rows (one finding stated by two or more dossiers)")
out.append("")
dossiers = ["gt-table-pub", "gt-bus", "gt-flock-ring", "code-spine", "code-pubinput", "code-layer1",
            "lib-arklib", "lib-others", "docs-debt", "literature", "boundary-adaptor", "gt-opening-compile",
            "obligations"]
def cites(text, d):
    return re.search(r"(?<![\w-])" + re.escape(d) + r"\.md", text) is not None


for r in rows:
    ds = [d for d in dossiers if cites(r["where"], d)]
    if len(ds) >= 2:
        out.append(f"- {r['id']} ({r['name']}): {', '.join(ds)}")
out.append("")

per = collections.Counter()
for r in findings:
    for d in dossiers:
        if cites(r["where"], d):
            per[d] += 1
out.append("### Rows per dossier (a merged row counts for each dossier it cites)")
out.append("")
out.append("| Dossier | Rows citing it |")
out.append("|---|---|")
for d in dossiers:
    out.append(f"| {d} | {per[d]} |")
out.append("")
out.append(res(open("footer.md").read().rstrip()))
out.append("")

open("../../dossiers/register.md", "w").write("\n".join(out))
print("rows", len(rows), "findings", len(findings), "positions", len(positions), "neg", len(NEG), "unv", len(UNV))
print({RANK_NAME[k]: v for k, v in sorted(cnt.items())})
