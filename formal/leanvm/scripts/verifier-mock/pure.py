import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import *
from functools import reduce
from operator import mul

out = []
def g(lhs, rhs):
    out.append(f"#guard ({lhs}) =\n    {rhs}")

fes = lambda ks: [fe(k) for k in ks]

g("powers (fe 1) 6", llist(V.powers(fe(1), 6)))
g("eqKernel [fe 2, fe 3, fe 4]", llist(V.eq_kernel(fes([2, 3, 4]))))
g("multilinearEval ((List.range 8).map fe) [fe 10, fe 11, fe 12]",
  le(V.multilinear_eval(fes(range(8)), fes([10, 11, 12]))))
g("multilinearEval kTable (fes 13 4)",
  le(V.multilinear_eval([K(fw(i, 5)) for i in range(16)], fes([13, 14, 15, 16]))))
g("eqEval [fe 20, fe 21, fe 22] [fe 23, fe 24, fe 25]", le(V.eq_eval(fes([20, 21, 22]), fes([23, 24, 25]))))
g("dot [fe 26, fe 27, fe 28] [fe 29, fe 30, fe 31]", le(V.dot(fes([26, 27, 28]), fes([29, 30, 31]))))
g("indexMle [fe 32, fe 33, fe 34, fe 35]", le(V.index_mle(fes([32, 33, 34, 35]))))
g("polyEval [fe 40, fe 41, fe 42, fe 43, fe 44] (fe 45)", le(V.poly_eval(fes(range(40, 45)), fe(45))))
g("gpow 5", le(V._gpow(5)))
g("gpow (2 ^ 32 - 1)", le(V._gpow(2**32 - 1)))
g("lagrangeWeights 64 (fe 50)", llist(V.lagrange_weights(64, fe(50))))
g("lagrangeInterpolate 128 ((List.range 128).map fe) (fe 51)", le(V.lagrange_interpolate(128, fes(range(128)), fe(51))))
g("windowDenominator 64", le(V._window_denominator(64)))
g("windowDenominator 128", le(V._window_denominator(128)))
g("(List.range 128).map phi", llist(V.PHI[:128]))
g("fixedChallenges", llist(V.FIXED_CHALLENGES))
g("[1, 2, 3, 5, 64, 65, 2 ^ 20].map log2Ceil", lnat([V.log2_ceil(v) for v in [1, 2, 3, 5, 64, 65, 2**20]]))
g("selectorPoint 13 6", llist(V._selector_point(13, 6)))
g("subspaceRoots 12", llist(V._subspace_roots(12)))
g("inducedWeight 5 [3, 17, 30, 0] (powers (fe 60) 4) [fe 61, fe 62, fe 63, fe 64, fe 65]",
  le(V._induced_weight(5, [3, 17, 30, 0], V.powers(fe(60), 4), fes(range(61, 66)))))
words = [K(fw(i, 6)) for i in range(6)]
g("extRow ((List.range 6).map fun i ↦ K.ofBits (fw i 6))", llist(V._ext_row(words)))
rows = [[K(fw(10 * q + j, 7)) for j in range(4)] for q in range(3)]
g("enforcedSum kRows [fe 66, fe 67] [fe 68, fe 69, fe 70]",
  le(V._enforced_sum(rows, fes([66, 67]), fes([68, 69, 70]))))
coeffs = fes(range(100, 164))
g("ringWeight (fes 71 4) (fes 75 4) (fes 100 64)",
  le(V._ring_weight(fes([71, 72, 73, 74]), fes([75, 76, 77, 78]), coeffs)))
ch = fes(range(80, 86))
rc = [reduce(mul, (f ** (2 ** (k % s)) for f, s in zip(ch, V.RING_MAP_SHIFTS) if k & s), V.ONE) for k in range(64)]
g("ringCoefficients (fes 80 6)", llist(rc))
g("phiMap (fe 86) (fes 80 6)", le(V._phi(fe(86), ch)))
# ring switch target identity: Phi(a) = sum_k c_k a^(2^k)
a = fe(87)
assert V._phi(a, ch) == E.sum(c * a ** (2 ** k) for k, c in enumerate(rc))

# derive_config for every admissible pair
cfgs = []
for rate in range(1, 5):
    for log_n in range(15, 29):
        c = V.derive_config(log_n, rate)
        cfgs.append(f"({log_n}, {rate}, {lnat(c.folds)}, {lnat(c.log_inv_rates)}, {lnat(c.queries)})")
out.append("/-- `derive_config(log_n, rate)` for every admissible pair: folds, rates, queries. -/\n"
           "def pythonConfigs : List (ℕ × ℕ × List ℕ × List ℕ × List ℕ) :=\n  [" + ",\n   ".join(cfgs) + "]")

sizes = [3, 5, 5, 0, 2, 5, 1]
offs, tl = V.stack_offsets(sizes)
g("stackOffsets [3, 5, 5, 0, 2, 5, 1]", f"({lnat(offs)}, {tl})")
p = V.Placement(3, 0b1011001, 2)
g("samplePlacement.stackPoint [fe 90, fe 91, fe 92] 9",
  llist(p.stack_point(fes([90, 91, 92]), 9)))
g("samplePlacement.eqAbove (fes 93 9)",
  le(p.eq_above(fes(range(93, 102)))))

# BLAKE2s row vectors
cw = [E(fw(i, 7)) for i in range(2 ** 14)]
rw = [E(fw(i, 8)) for i in range(2 ** 14)]
lv, rv = V.blake2s_row_values(cw)
g("bilinearProbe", f"({le(E.sum(lv))},\n     {le(E.sum(rv))},\n     {le(V.blake2s_bilinear(fe(110), rw, cw))})")

# Layout
bytecode = [K(fw(i, 9)) for i in range(32)]
heights = [2, 1, 1, 2, 2, 3]
L = V.build_layout(bytecode, 16, heights)
g("sampleLayout.stackLog", str(L.stack_log))
g("sampleLayout.logBytecode", str(L.log_bytecode))
g("sampleLayout.placements.map fun p ↦ (p.vars, p.index, p.low)",
  wrap([f"({q.variables}, {q.index}, {q.low})" for q in L.placements]))
pw = V.powers(fe(300), 16)
cols = fes(range(200, 240))
def probe(blocks):
    return wrap([f"({b.log_rows}, {b.owner}, {len(b.coordinates)}, {le(V.dot(pw[:len(b.coordinates)], [f.evaluate(lambda i: cols[i]) for f in b.coordinates]))})" for b in blocks])
g("blockProbe sampleLayout.push", probe(L.push))
g("blockProbe sampleLayout.pull", probe(L.pull))
g("blockProbe sampleLayout.count", probe(L.count))
g("tableWidths", lnat(V.TABLE_WIDTHS))
g("globalColumnBases", lnat(V.GLOBAL_COLUMN_BASES))
g("tables.map Table.nConstraints", lnat([t.n_constraints for t in V.TABLES]))
g("tables.map Table.countColumns", wrap([lnat(t.count_columns) for t in V.TABLES]))
g("jumpConstraints (fes 400 14)", llist(V._jump_constraints(fes(range(400, 414)))))
# Bus layouts of the sample
for name, fw_rows, blocks in (("push", (0, 16, L.log_bytecode), L.push), ("pull", (0, 16, L.log_bytecode), L.pull), ("count", (), L.count)):
    bl = V.bus_layout(fw_rows, blocks)
    g(f"busProbe {lnat(list(fw_rows))} sampleLayout.{name}",
      f"({bl.depth},\n     " + wrap([f"({q.variables}, {q.index})" for q in bl.framework + bl.tables], "     ") + ")")

# Seed
pi_bytes = bytes(fw(i, 10) % 256 for i in range(32))
iv = V.blake2s_hash(b"leanvm" + V.pack("<Q", len(V.R1CS_DIGEST)) + V.R1CS_DIGEST + V.blake2s_hash(b"".join(w.to_bytes() for w in bytecode)).value)
st = V.Transcript(V.Proof((), b""), iv, V.Digest(pi_bytes)).state
words32 = []
for w in st:
    words32 += [w & 0xFFFFFFFF, w >> 32]
g("(seed sampleBytecode samplePublicInput).toList", wrap([f"0x{w:08x}" for w in words32]))
# halves of the public input
h0, h1 = V.Digest(pi_bytes).halves()
g("[(digestScalars samplePublicInput).1, (digestScalars samplePublicInput).2]", llist([h0, h1]))

open(sys.argv[1], "w").write("\n\n".join(out) + "\n")
