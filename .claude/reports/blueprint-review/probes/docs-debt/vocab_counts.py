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
