import runpy, re, collections
D = runpy.run_path("../register/rows.py")
F = D["FINDINGS"]; N = D["NEG"]; U = D["UNV"]; C = D["CONTRA"]
txt = []
for r in F: txt += [str(v) for k,v in r.items()]
for r in N: txt += list(r.values())
for r in U: txt += list(r.values())
for d,t in C: txt += [d,t]
out = collections.Counter(); inn = collections.Counter()
ex = collections.defaultdict(list)
for s in txt:
    parts = s.split("`")
    if len(parts) % 2 == 0: print("ODD BACKTICKS:", s[:200])
    for i,p in enumerate(parts):
        for c in p:
            if not c.isascii() or c in "|#$*<>^_&%{}~\\[]":
                (inn if i%2 else out)[c]+=1
                if i%2==0 and len(ex[c])<3: ex[c].append(p[max(0,p.index(c)-30):p.index(c)+30])
print("outside", out); print("inside", inn)
for c,e in ex.items():
    if c not in "§—–…[]'\"·": print(repr(c), e)
