#!/usr/bin/env python3
"""Probe (read-only): Markdown links with anchors in the tracked documentation, including
links broken across lines (which scripts/check-docs.py, a per-line matcher, does not see).
Anchors are computed the GitHub way (lowercase, punctuation dropped, spaces to hyphens)."""
import re, os, subprocess
root="/home/scaraven/Documents/Verified-zkEVM/leanerVM"
files=subprocess.run(["git","ls-files","*.md"],cwd=root,capture_output=True,text=True).stdout.split()
def anchors(path):
    out=set(); infence=False
    for l in open(path,encoding="utf-8").read().split("\n"):
        if l.startswith("```"): infence=not infence
        if infence: continue
        m=re.match(r"^(#{1,6})\s+(.*)$",l)
        if m:
            t=m.group(2).strip()
            t=re.sub(r"\[([^\]]*)\]\([^)]*\)",r"\1",t)
            t=t.replace("`","")
            a=re.sub(r"[^\w\- ]","",t.lower(),flags=re.UNICODE).replace(" ","-")
            out.add(a)
    return out
link=re.compile(r"\[([^\]]*)\]\(([^)\s]+)\)",re.S)
n=0; bad=[]; multiline=0
for f in files:
    p=os.path.join(root,f); txt=open(p,encoding="utf-8").read()
    for m in link.finditer(txt):
        target=m.group(2)
        if target.startswith("http") or target.startswith("mailto"): continue
        line=txt[:m.start()].count("\n")+1
        if "\n" in m.group(1): multiline+=1
        path,_,frag=target.partition("#")
        tp=p if path=="" else os.path.normpath(os.path.join(os.path.dirname(p),path))
        n+=1
        if not os.path.exists(tp):
            bad.append(f"{f}:{line}: missing file {target}"); continue
        if frag and tp.endswith(".md"):
            if frag not in anchors(tp):
                bad.append(f"{f}:{line}: missing anchor #{frag} in {os.path.relpath(tp,root)}")
print(f"{len(files)} tracked Markdown files, {n} local links checked ({multiline} span two lines), {len(bad)} broken")
for b in bad: print("  ",b)
