"""Check each (dossier, section) -> box match against the dossier's own heading."""
import re, os, difflib
from load import rows
import boxes

def lines(d):
    return open(os.path.join(boxes.DOSS, d + ".md")).read().split("\n")

def heading(d, tok):
    L = lines(d)
    def find(pat, start=0):
        for i in range(start, len(L)):
            m = re.match(pat, L[i])
            if m:
                return m.group(1)
    if d == "gt-bus":
        n = re.search(r"G(\d+)", tok).group(1); return find(rf"### G{n}\. (.*)")
    if d == "gt-flock-ring":
        n = re.search(r"8\.(\d+)", tok).group(1); return find(rf"### 8\.{n} (.*)")
    if d == "boundary-adaptor":
        n = re.search(r"G\.(\d+)", tok).group(1)
        g = next(i for i, l in enumerate(L) if l.startswith("## G. Findings"))
        return find(rf"### {n}\. (.*)", g)
    if d == "docs-debt":
        n = re.search(r"H\.(\d+)", tok).group(1); return find(rf"### H\.{n} (.*)")
    if d in ("code-pubinput", "code-layer1", "lib-arklib", "lib-others"):
        m = re.search(r"(G|F)\.(\d+)", tok)
        b = re.search(r"\((\w+) bullet\)", tok)
        if b:
            g = next(i for i, l in enumerate(L) if l.startswith(f"### G.{m.group(2)} "))
            bullets = [l for l in L[g:g + 30] if l.startswith("- **")]
            return bullets[boxes.BULLET[b.group(1)] - 1]
        return find(rf"### {m.group(1)}\.{m.group(2)} (.*)")
    if d == "gt-opening-compile":
        m = re.search(r"I\.(\d+)", tok)
        if m:
            return find(rf"### I\.{m.group(1)} (.*)")
        b = re.search(r"\((\w+) bullet\)", tok).group(1)
        g = next(i for i, l in enumerate(L) if l.startswith("### Notes") and i > 1600)
        return [l for l in L[g:g + 15] if l.startswith("- **")][boxes.BULLET[b] - 1]
    if d == "code-spine":
        return tok
    if d == "gt-table-pub":
        return tok
    return None

bad = 0
for r in rows:
    _, labs = boxes.where_with_refs(r["id"], r["name"], r["where"])
    for d, tok, lab in labs:
        h = heading(d, tok) or ""
        hn = boxes.norm(re.sub(r"\*\*", "", h))
        bn = boxes.norm(boxes.LABELNAME[lab])
        ratio = difflib.SequenceMatcher(None, hn[:len(bn)], bn).ratio()
        flag = "" if ratio >= 0.8 else "  <<<"
        if flag: bad += 1
        print(f"{r['id']:5} {ratio:.2f} {d}:{tok[:30]} -> {lab}{flag}\n   head: {hn[:120]}\n   box : {bn[:120]}")
print("flagged", bad)
