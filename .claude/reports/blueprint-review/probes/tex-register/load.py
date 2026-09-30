"""Load the register data exactly as render.py orders and resolves it."""
import runpy, re, os
HERE = os.path.dirname(os.path.abspath(__file__))
D = runpy.run_path(os.path.join(HERE, "../register/rows.py"))
SUBJECTS = D["SUBJECTS"]
SUBJ_IDX = {k: i for i, (k, _) in enumerate(SUBJECTS)}
SUBJ_NAME = dict(SUBJECTS)
FIND = D["FINDINGS"]; NEG = D["NEG"]; UNV = D["UNV"]; CONTRA = D["CONTRA"]; KEYS = D["KEYS"]
RANK_NAME = {0: "critical", 1: "major", 2: "minor", 3: "note"}
def is_position(r): return r["sev"].startswith("—")
rows = sorted(enumerate(FIND), key=lambda t: (t[1]["rank"], SUBJ_IDX[t[1]["subj"]], t[0]))
rows = [dict(r) for _, r in rows]
for i, r in enumerate(rows, 1): r["id"] = f"R{i}"
KEYID = {}
for k, sub in KEYS.items():
    hits = [r for r in rows if sub in r["name"]]
    assert len(hits) == 1, (k, sub)
    KEYID[k] = hits[0]["id"]
def res(t):
    return re.sub(r"\[\[([A-Za-z0-9]+)\]\]", lambda m: KEYID[m.group(1)], t)
for r in rows:
    for fld in ("name", "sev", "where", "cls", "claim", "evid", "change", "status", "note"):
        r[fld] = res(r[fld])
NEG = [{k: res(v) for k, v in n.items()} for n in NEG]
UNV = [{k: res(v) for k, v in u.items()} for u in UNV]
CONTRA = [(res(d), res(t)) for d, t in CONTRA]
