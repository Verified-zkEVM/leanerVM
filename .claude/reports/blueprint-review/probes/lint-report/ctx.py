#!/usr/bin/env python3
"""ctx.py ROOT REGEX WIDTH file:line ... -> print context around each match on that line (and the previous line)."""
import re, sys
root, pat, w = sys.argv[1], re.compile(sys.argv[2]), int(sys.argv[3])
for loc in sys.argv[4:]:
    f, l = loc.rsplit(':', 1); l = int(l)
    lines = open(f"{root}/{f}", encoding='utf-8').read().split('\n')
    s = lines[l-1]
    for m in pat.finditer(s):
        print(f"== {loc}: ...{s[max(0,m.start()-w):m.end()+w//2]}...")
