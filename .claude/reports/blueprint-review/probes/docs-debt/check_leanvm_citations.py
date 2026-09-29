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
