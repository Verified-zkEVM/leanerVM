import runpy, re, collections
D = runpy.run_path("../register/rows.py")
F = D["FINDINGS"]; N = D["NEG"]; U = D["UNV"]; C = D["CONTRA"]
txt = []
for r in F: txt += [str(v) for v in r.values()]
for r in N: txt += list(r.values())
for r in U: txt += list(r.values())
for d,t in C: txt += [d,t]
all_ = "\n".join(txt)
chars = collections.Counter(c for c in all_ if not c.isalnum() and c not in " ")
print(sorted(chars.items(), key=lambda t:-t[1]))
print("bold", len(re.findall(r"\*\*", all_)), "star", all_.count("*"))
print("links", re.findall(r"\[[^\[\]]+\]\([^)]+\)", all_)[:5])
print("len F N U C", len(F), len(N), len(U), len(C))
