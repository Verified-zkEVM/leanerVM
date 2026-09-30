#!/usr/bin/env python3
"""Attribute box warnings of an unwrapped LuaLaTeX log to input files and pages.
Usage: parselog.py build/lintjob.log   (log written with max_print_line=100000)."""
import re, sys
log = open(sys.argv[1], encoding='utf-8', errors='replace').read().split('\n')
stack = []          # file names or None for non-file parens
page = 0            # last shipped page number
out = []
skip = False
file_re = re.compile(r'\(((?:\./|/)[^\s()]+)')
warn_re = re.compile(r'^(Overfull|Underfull) \\([hv])box \(([^)]*)\) (?:in paragraph at lines (\d+)--(\d+)|in alignment at lines (\d+)--(\d+)|has occurred while \\output is active|detected at line (\d+))')
for ln in log:
    m = warn_re.match(ln)
    if m:
        cur = next((f for f in reversed(stack) if f), '?')
        lines = m.group(4) and f"{m.group(4)}-{m.group(5)}" or m.group(6) and f"{m.group(6)}-{m.group(7)} (alignment)" or m.group(8) and f"{m.group(8)}" or 'output'
        out.append((m.group(1), m.group(2), m.group(3), cur, lines, page + 1))
        skip = True
        continue
    if skip:
        if ln.strip() == '':
            skip = False
        continue
    i = 0
    while i < len(ln):
        c = ln[i]
        if c == '(':
            fm = file_re.match(ln, i)
            if fm:
                stack.append(fm.group(1)); i = fm.end(); continue
            stack.append(None)
        elif c == ')':
            if stack: stack.pop()
        elif c == '[':
            pm = re.match(r'\[(\d+)', ln[i:])
            if pm and (i == 0 or ln[i-1] in ' )]\n'):
                page = int(pm.group(1)); i += pm.end(); continue
        i += 1
for kind, hv, amount, f, lines, pg in out:
    print(f"{kind}\t{hv}\t{amount}\t{f}\t{lines}\tpage~{pg}")
