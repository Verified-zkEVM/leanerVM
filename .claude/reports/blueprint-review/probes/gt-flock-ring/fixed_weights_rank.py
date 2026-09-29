"""Probe for the dossier gt-flock-ring (scratch).

The seven fixed zerocheck coordinates of Flock (specification Annex C.2, c-flock-protocol.tex:54;
python-verifier/verifier.py:1095-1100) give 2^7 equality weights eq(a, b), b in {0,1}^7.
Lemma "partially fixed zerocheck" (03-proving-primitives.tex:95-100) needs them linearly
independent over F_2. This computes their rank over F_2 with the pinned Python field, and checks
the facts used in the dossier: no fixed coordinate is 1, and the six ring-switching exponents.
"""
import importlib.util, sys

sys.dont_write_bytecode = True   # the pinned checkout must stay untouched
spec = importlib.util.spec_from_file_location(
    "verifier", "/home/scaraven/Documents/leanEthereum/leanVM/python-verifier/verifier.py")
v = importlib.util.module_from_spec(spec); sys.modules["verifier"] = v; spec.loader.exec_module(v)
E, ONE = v.E, v.ONE

a = list(v.FIXED_CHALLENGES)
assert len(a) == 7
print("fixed coordinates equal to 1:", sum(x == ONE for x in a))
print("fixed coordinates equal to 0:", sum(x == v.ZERO for x in a))

rows = []
for b in range(1 << 7):
    w = ONE
    for i, ai in enumerate(a):
        w = w * (ai if (b >> i) & 1 else ONE + ai)
    rows.append(int(w.c0) | (int(w.c1) << 64) | (int(w.c2) << 128))

rank = 0
basis = []
for r in rows:
    for p in basis:
        r = min(r, r ^ p)
    if r:
        basis.append(r); basis.sort(reverse=True); rank += 1
print("rank over F_2 of the 128 equality weights:", rank)

D = sum(2 ** (s - 1) for s in v.RING_MAP_SHIFTS)
print("ring-switching degree 2^31+2^15+2^7+2^3+2+1 =", D, "< 2^32:", D < 2 ** 32)
for k in (3, 32):
    print(f"k_batch={k}: 4k+163 = {4*k+163}; stream scalars of the reduction = {64 + 2*(8+k) + 2 + 16 + 64}; challenges = {(k+1)+1+(8+k)+1+8+6}")
