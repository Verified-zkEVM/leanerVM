#!/usr/bin/env python3
"""Classify codes-raw.tsv lines. Classes:
  reg       register row number R<n>
  inventory inside the code inventories (docs-codes.tex, code-index.tex)
  paren     inside an open parenthesis on the same line (spot-check that a name precedes)
  cmd       inside \\code{}/\\lean{}/\\file{} (identifier, e.g. a probe or file name)
  bare      everything else: a candidate violation"""
import re, sys
for ln in open(sys.argv[1], encoding='utf-8'):
    loc, tok, ctx = ln.rstrip('\n').split('\t', 2)
    pre = ctx.split('[[', 1)[0]
    f = loc.split(':')[0]
    if re.fullmatch(r'R\d+', tok): c = 'reg'
    elif f.endswith(('docs-codes.tex', 'code-index.tex')): c = 'inventory'
    elif re.search(r'\\(code|lean|file)\{[^}]*$', pre): c = 'cmd'
    elif pre.count('(') > pre.count(')'): c = 'paren'
    else: c = 'bare'
    print(f"{c}\t{loc}\t{tok}\t{ctx}")
