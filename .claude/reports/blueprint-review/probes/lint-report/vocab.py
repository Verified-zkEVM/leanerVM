#!/usr/bin/env python3
"""Vocabulary scan outside verbatim environments. Prints file:line, pattern, context."""
import re, sys, glob, os
root = sys.argv[1]
files = sorted(glob.glob(os.path.join(root, 'sections/*.tex')) + glob.glob(os.path.join(root, 'sections/gen/*.tex')))
files = [f for f in files if not os.path.basename(f).startswith('index-')]
vb = re.compile(r'\\begin\{(leancode|srccode|shellcode|Verbatim|verbatim)\}'); ve = re.compile(r'\\end\{(leancode|srccode|shellcode|Verbatim|verbatim)\}')
pats = {
 'roadmap': re.compile(r'[Rr]oadmap'),
 'dashboard': re.compile(r'[Dd]ashboard'),
 'unit of work': re.compile(r'units? of work'),
 'slice': re.compile(r'\bslices?\b'),
 'PIOP': re.compile(r'\bPIOP|\bpiop(?![A-Z_a-z])'),
 'Category': re.compile(r'Category [AB]'),
 'the Rust': re.compile(r'\b[Tt]he Rust\b(?!\s*(verifier|prover|code|crate|implementation|source|side|function|parameter|file|loop|and the Python verifier|and Python verifiers|, the Python))'),
 'the spec': re.compile(r'\b[Tt]he spec\b|\bspec\.'),
 'pin': re.compile(r'\bpin(s|ned)?\b'),
 'zerocheck': re.compile(r'[Zz]ero-?check'),
 'evalOracle': re.compile(r'evalOracle|evaluation oracle'),
}
for f in files:
    rel = os.path.relpath(f, root); inv = False
    for n, s in enumerate(open(f, encoding='utf-8'), 1):
        if vb.search(s): inv = True
        if inv:
            if ve.search(s): inv = False
            continue
        if s.lstrip().startswith('%'): continue
        for k, p in pats.items():
            for m in p.finditer(s):
                print(f"{k}\t{rel}:{n}\t{s[max(0,m.start()-70):m.end()+60].strip()}")
