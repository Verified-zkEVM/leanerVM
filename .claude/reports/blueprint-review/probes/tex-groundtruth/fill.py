#!/usr/bin/env python3
"""Replace @@CODE:<dossier>:<first>:<last>[:strip]@@ lines with verbatim dossier lines."""
import re, sys
base = "/home/scaraven/Documents/Verified-zkEVM/leanerVM/.claude/reports/blueprint-review/"
src, dst = sys.argv[1], sys.argv[2]
cache = {}
out = []
for line in open(src, encoding="utf-8"):
    m = re.fullmatch(r"@@CODE:([\w.-]+):(\d+):(\d+)(?::(\d+))?@@\n?", line)
    if not m:
        out.append(line)
        continue
    name, a, b, strip = m.group(1), int(m.group(2)), int(m.group(3)), int(m.group(4) or 0)
    if name not in cache:
        cache[name] = open(base + "dossiers/" + name, encoding="utf-8").read().split("\n")
    for l in cache[name][a - 1:b]:
        out.append((l[strip:] if l[:strip].strip() == "" else l) + "\n")
open(dst, "w", encoding="utf-8").write("".join(out))
