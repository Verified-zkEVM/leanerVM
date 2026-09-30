#!/usr/bin/env python3
"""Attribute non-box warnings of an unwrapped log to input files and pages."""
import re, sys
log = open(sys.argv[1], encoding='utf-8', errors='replace').read().split('\n')
stack=[]; page=0; skip=False
file_re = re.compile(r'\(((?:\./|/)[^\s()]+)')
for ln in log:
    if re.match(r'^(Overfull|Underfull) \\[hv]box', ln): skip=True; continue
    if skip:
        if ln.strip()=='' : skip=False
        continue
    if re.search(r'Warning|Missing character|Token not allowed', ln):
        cur = next((f for f in reversed(stack) if f), '?')
        print(f"{cur}\tpage~{page+1}\t{ln[:200]}")
    i=0
    while i<len(ln):
        c=ln[i]
        if c=='(':
            fm=file_re.match(ln,i)
            if fm: stack.append(fm.group(1)); i=fm.end(); continue
            stack.append(None)
        elif c==')':
            if stack: stack.pop()
        elif c=='[':
            pm=re.match(r'\[(\d+)', ln[i:])
            if pm and (i==0 or ln[i-1] in ' )]'): page=int(pm.group(1)); i+=pm.end(); continue
        i+=1
