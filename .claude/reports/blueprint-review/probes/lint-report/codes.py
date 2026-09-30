#!/usr/bin/env python3
"""List letter-code tokens in the report's .tex sources outside verbatim environments.
Output: file:line<TAB>token<TAB>context<TAB>verdict-hint"""
import re, sys, glob, os
root = sys.argv[1]
files = sorted(glob.glob(os.path.join(root, 'main.tex')) + glob.glob(os.path.join(root, 'preamble.tex'))
               + glob.glob(os.path.join(root, 'sections/*.tex')) + glob.glob(os.path.join(root, 'sections/gen/*.tex')))
verb_begin = re.compile(r'\\begin\{(leancode|srccode|shellcode|Verbatim|verbatim|lstlisting)\}')
verb_end = re.compile(r'\\end\{(leancode|srccode|shellcode|Verbatim|verbatim|lstlisting)\}')
tok = re.compile(r'(?<![A-Za-z0-9_\\.:/-])([A-Z][0-9]{1,2}[a-z]?)(?![0-9A-Za-z_])'
                 r'|\b(Layers? \d+(?:\s*(?:to|and|,|–|--)\s*\d+)*)'
                 r'|\b([Hh]oles? [A-Z][0-9A-Za-z.-]*)'
                 r'|\b([Dd]ecisions? \d+)'
                 r'|\b(acceptance tests? \d+)'
                 r'|\b(T[1-8](?:\s*(?:–|--|to)\s*T[1-8])?)')
for f in files:
    rel = os.path.relpath(f, root)
    inverb = False
    for n, line in enumerate(open(f, encoding='utf-8'), 1):
        if verb_begin.search(line): inverb = True
        if inverb:
            if verb_end.search(line): inverb = False
            continue
        s = line.rstrip('\n')
        if s.lstrip().startswith('%'): continue
        for m in tok.finditer(s):
            t = next(g for g in m.groups() if g)
            # context: preceding char
            pre = s[max(0, m.start()-40):m.start()]
            post = s[m.end():m.end()+40]
            print(f"{rel}:{n}\t{t}\t{pre}[[{t}]]{post}")
