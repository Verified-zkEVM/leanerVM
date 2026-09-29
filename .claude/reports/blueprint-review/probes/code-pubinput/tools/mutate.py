#!/usr/bin/env python3
"""Make a mutated copy of LeanerVM/Protocol/PublicInput.lean.

usage: mutate.py <out.lean> <namespace-suffix> <edits.py>
edits.py defines EDITS = [(old, new), ...] (exact, each must occur once) and TAIL (appended).
"""
import sys, runpy
src = open('LeanerVM/Protocol/PublicInput.lean').read()
out, ns, edits = sys.argv[1], sys.argv[2], sys.argv[3]
d = runpy.run_path(edits)
src = src.replace('\nnamespace LeanerVM.Protocol\n', f'\nnamespace LeanerVM.Protocol.{ns}\n')
src = src.replace('\nend LeanerVM.Protocol\n', f'\nend LeanerVM.Protocol.{ns}\n')
for old, new in d['EDITS']:
    n = src.count(old)
    assert n == 1, (n, old)
    src = src.replace(old, new)
src += d.get('TAIL', '').replace('@NS@', ns)
open(out, 'w').write(src)
