"""Finding boxes of tex/sections/gen/findings-*.tex, and the map from a register row's
"where" citations to the box that states that dossier finding. Run standalone to print the
matches for review."""
import os, re, glob, difflib
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, "../.."))
GEN = os.path.join(ROOT, "tex/sections/gen")
DOSS = os.path.join(ROOT, "dossiers")


def read_boxes(path):
    s = open(path).read()
    out = []
    for m in re.finditer(r"\\begin\{finding\}\{(\w+)\}\{([^}]+)\}\{", s):
        i, depth = m.end(), 1
        while depth:
            c = s[i]
            depth += (c == "{") - (c == "}")
            i += 1
        out.append((m.group(2), s[m.end():i - 1]))
    return out


BOXES = {os.path.basename(p)[len("findings-"):-4]: read_boxes(p)
         for p in sorted(glob.glob(os.path.join(GEN, "findings-*.tex")))}
LABELNAME = {l: n for bs in BOXES.values() for l, n in bs}


def norm(s):
    s = re.sub(r"\\texorpdfstring\{((?:[^{}]|\{[^{}]*\})*)\}\{[^{}]*\}", r"\1", s)
    s = s.replace("\\allowbreak{}", "").replace("\\_", "_").replace("\\#", "#")
    s = re.sub(r"\\(texttt|lean|code|file)\{", "", s)
    s = re.sub(r"[`{}$\\]|``|''", "", s).replace("--", "–")
    return re.sub(r"\s+", " ", s).strip().lower()


def box(file, n):
    return BOXES[file][n - 1][0]


def headings(dossier, start, stop):
    hs = []
    for ln, line in enumerate(open(os.path.join(DOSS, dossier + ".md")), 1):
        if start <= ln < stop and line.startswith("### "):
            hs.append(line[4:].strip())
    return hs


# code-spine §F and gt-table-pub §8: findings named by heading, boxes in heading order
SPINE_F = headings("code-spine", 1171, 1372)          # 9 headings, boxes 1-9 of findings-code
TABLE_8 = headings("gt-table-pub", 681, 857)[:9]       # 9 findings before "Notes", boxes 1-9
LIB = {("lib-arklib", "G.1"): "f:lib-existential-rbr", ("lib-arklib", "G.2"): "f:lib-completeness-error",
       ("lib-arklib", "G.3"): "f:lib-legacy-framework", ("lib-arklib", "G.4"): "f:lib-fs-bcs",
       ("lib-arklib", "G.5"): "f:lib-err-noncomputable", ("lib-arklib", "G.6"): "f:lib-arklib-table-names",
       ("lib-arklib", "G.7"): "f:lib-side-conditions-derivable", ("lib-arklib", "G.8"): "f:lib-reimplemented",
       ("lib-arklib", "F.5"): "f:lib-status-dates",
       ("lib-others", "G.1"): "f:lib-ladder-conflates", ("lib-others", "G.2"): "f:lib-k-sampler-unused",
       ("lib-others", "G.3"): "f:lib-evaloracle-answer-n", ("lib-others", "G.4"): "f:lib-scalar-interfaces",
       ("lib-others", "G.5"): "f:lib-layer0-stale", ("lib-others", "G.6"): "f:lib-eager-fintype",
       ("lib-others", "G.7"): "f:lib-simp-misreads-k", ("lib-others", "G.8"): "f:lib-numerals-changed",
       ("lib-others", "G.9"): "f:lib-mle-bridge-unimportable", ("lib-others", "G.10"): "f:lib-counting-bound-redundant"}
# gt-table-pub "§8 Notes": the notes boxes, chosen by the row's name (checked by ratio below)
TABLE_NOTES = {"R101": "f:table-pub-slot-not-pinned", "R108": "f:table-pub-spec-errors",
               "R109": "f:table-pub-stale-comments"}
BULLET = {"first": 1, "second": 2, "third": 3, "fourth": 4, "fifth": 5}

PATTERNS = {
    "gt-bus": r"(?<![\w.§])G(\d+)\b",
    "gt-flock-ring": r"§8\.(\d+)",
    "boundary-adaptor": r"§G\.(\d+)",
    "docs-debt": r"§H\.(\d+)",
    "code-pubinput": r"§G\.(\d+)",
    "code-layer1": r"§G\.(\d+)(?: \((first|second|third|fourth|fifth) bullet\))?",
    "lib-arklib": r"§(G\.\d+|F\.5)",
    "lib-others": r"§(G\.\d+)",
    "code-spine": r'§F "([^"]+)"',
    "gt-table-pub": r'§8 \((first|second|third) finding\)|§8 "([^"]+)"|§8 Notes',
    "gt-opening-compile": r"§I\.(\d+)|§I Notes \((first|second|third) bullet\)",
}
DOSSIERS = sorted((os.path.basename(p)[:-3] for p in glob.glob(os.path.join(DOSS, "*.md"))),
                  key=len, reverse=True)
DOSS_RE = re.compile(r"(?<![\w-])(" + "|".join(map(re.escape, DOSSIERS)) + r")\.md")


def target(rid, rowname, d, m):
    g = m.groups()
    if d == "gt-bus":
        return box("bus", int(g[0]))
    if d == "gt-flock-ring":
        return box("flock-ring", int(g[0]))
    if d == "boundary-adaptor":
        return box("boundary", int(g[0]))
    if d == "docs-debt":
        n = int(g[0])
        return box("docs", n) if n <= 19 else None     # H.20 is the negative results
    if d == "code-pubinput":
        return box("code", 9 + int(g[0]))
    if d == "code-layer1":
        n = int(g[0])
        if n <= 9:
            return box("code", 15 + n)
        return box("code", 24 + BULLET[g[1]]) if g[1] else None
    if d in ("lib-arklib", "lib-others"):
        return LIB.get((d, g[0]))
    if d == "code-spine":
        want = g[0].lower()
        hits = [i for i, h in enumerate(SPINE_F, 1) if h.replace("`", "").lower().startswith(want)]
        assert len(hits) == 1, (rid, g[0], hits)
        return box("code", hits[0])
    if d == "gt-table-pub":
        if g[0]:
            return box("table-pub", BULLET[g[0]])
        if g[1]:
            want = g[1].lower()
            hits = [i for i, h in enumerate(TABLE_8, 1) if h.lower().startswith(want)]
            assert len(hits) == 1, (rid, g[1], hits)
            return box("table-pub", hits[0])
        return TABLE_NOTES.get(rid)
    if d == "gt-opening-compile" and "opening" in BOXES:
        if g[0]:
            return box("opening", int(g[0]))      # I.1 to I.17 are boxes 1 to 17
        return box("opening", 17 + BULLET[g[1]])  # the notes' first three bullets: boxes 18-20
    return None


def where_with_refs(rid, rowname, where):
    """Return (where text with \\x00label\\x01 markers after each matched citation, labels)."""
    spans = [(m.start(), m.end(), m.group(1)) for m in DOSS_RE.finditer(where)]
    inserts, labels = [], []
    for k, (a, b, d) in enumerate(spans):
        end = spans[k + 1][0] if k + 1 < len(spans) else len(where)
        if d not in PATTERNS:
            continue
        for m in re.finditer(PATTERNS[d], where[b:end]):
            lab = target(rid, rowname, d, m)
            if not lab:
                continue
            pos = b + m.end()
            rest = where[pos:end]
            pm = re.match(r" \(([^()]*)\)", rest)
            if pm:
                inserts.append((pos + pm.end() - 1, "; \x00" + lab + "\x01"))
            else:
                inserts.append((pos, " (\x00" + lab + "\x01)"))
            labels.append((d, m.group(0), lab))
    out = where
    for pos, txt in sorted(inserts, reverse=True):
        out = out[:pos] + txt + out[pos:]
    return out, labels


if __name__ == "__main__":
    import sys
    sys.path.insert(0, HERE)
    from load import rows
    used = set()
    n = 0
    for r in rows:
        w, labs = where_with_refs(r["id"], r["name"], r["where"])
        if labs:
            n += 1
        for d, tok, lab in labs:
            used.add(lab)
            ratio = difflib.SequenceMatcher(None, norm(r["name"]), norm(LABELNAME[lab])).ratio()
            print(f"{r['id']:5} {ratio:.2f} {d}:{tok[:40]:40} -> {lab}\n      row: {r['name'][:110]}\n      box: {norm(LABELNAME[lab])[:110]}")
    print("rows with a cref:", n)
    print("boxes never cited:", sorted(set(LABELNAME) - used))
