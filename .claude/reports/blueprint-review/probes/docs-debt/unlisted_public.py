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
