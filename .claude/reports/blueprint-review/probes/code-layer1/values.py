"""Probe for task code-layer1, deliverables B.3, B.5, B.6, B.7 and C.

Reference numbers from the pinned leanVM (a386121f), to be compared with Layer 1's Lean
definitions in `ValuesProbe.lean`. Every evaluation below is made by a function of the pinned
Python verifier (`multilinear_eval`, `index_mle`, `eq_eval`, `stack_offsets`, `Placement`),
imported read-only. The bytecode table is built by a line-by-line transcription of the Rust
`bytecode_columns` (crates/lean_vm/src/cpu/layout.rs:229-309) and `stacked_bytecode_table`
(crates/lean_vm/src/leaf.rs:585-604): the Python verifier takes that table as an input file and
has no encoder of its own.

Run:  python3 -B .claude/reports/blueprint-review/probes/code-layer1/values.py
"""

import sys

sys.dont_write_bytecode = True
sys.path.insert(0, "/home/scaraven/Documents/leanEthereum/leanVM/python-verifier")
import verifier as V  # noqa: E402

K, E = V.K, V.E


def limbs(x):
    return (x.c0.value, x.c1.value, x.c2.value)


def gk(i):
    """g^i in K (primitives/field/mod.rs:82, g_pow)."""
    r = K(1)
    for _ in range(i):
        r = r * K(2)
    return r


# ---- the bytecode table ---------------------------------------------------------------
OP = {"xor": gk(0), "mul": gk(1), "set": gk(2), "deref": gk(3), "jump": gk(4), "blake2s": gk(5)}  # tables.rs:95-100


def bytecode_columns(prog):
    """layout.rs:229-309: (opcode, o1, o2, o3, fpc, ffp, extra0, extra1) per instruction."""
    cols = [[] for _ in range(8)]
    for op in prog:
        kind = op[0]
        z = K(0)
        if kind in ("xor", "mul"):
            _, a, b, c = op
            row = [OP[kind], gk(a), gk(b), gk(c), z, z, z, z]
        elif kind == "set":
            _, o, k = op  # k = (c0, c1, c2)
            row = [OP[kind], gk(o), K(k[0]), K(k[1]), K(k[2]), z, z, z]  # :257, :270
        elif kind == "deref":
            _, o1, o2, o3, mode = op
            f_pc = K(1) if mode == "pc" else z  # isa.rs:69-74
            f_fp = K(1) if mode == "fp" else z
            row = [OP[kind], gk(o1), gk(o2), gk(o3), f_pc, f_fp, z, z]
        elif kind == "jump":
            _, oc, od, of = op
            row = [OP[kind], gk(oc), gk(od), gk(of), z, z, z, z]
        elif kind == "blake2s":
            _, ins, cv, out, md = op
            row = [OP[kind], gk(ins[0]), gk(ins[1]), gk(ins[2]), gk(ins[3]), gk(cv), gk(out), gk(md)]
        for c in range(8):
            cols[c].append(row[c])
    return cols


def stacked_bytecode_table(cols, kbc):
    """leaf.rs:585-604: column i at slot 3 + i, `table[(slot << kbc)..((slot+1) << kbc)]`."""
    table = [K(0)] * (1 << (4 + kbc))
    for i, vals in enumerate(cols):
        slot = 3 + i
        assert len(vals) == 1 << kbc
        table[(slot << kbc):((slot + 1) << kbc)] = vals
    return table


PAD = ("set", 0, (0, 0, 0))  # lean_compiler/src/lib.rs:162
prog = [
    ("xor", 1, 2, 3),
    ("mul", 4, 5, 6),
    ("set", 7, (11, 12, 13)),
    ("deref", 8, 9, 10, "pc"),
    ("deref", 21, 22, 23, "fp"),
    ("deref", 24, 25, 26, "cell"),
    ("jump", 27, 28, 29),
    ("blake2s", (14, 15, 16, 17), 18, 19, 20),
] + [PAD] * 8
kbc = 4
table = stacked_bytecode_table(bytecode_columns(prog), kbc)
print("== bytecode table, 16 instructions, 256 cells (cell i + 16*s holds slot s of instruction i)")
print([w.value for w in table])

zeta = (E(3, 1, 0), E(5, 0, 7), E(2, 2, 2), E(0, 1, 0))
alpha = (E(9, 0, 1), E(0, 4, 0), E(6, 6, 0), E(1, 2, 3))
print("== bytecode multilinear at (zeta, alpha), as verifier.py:566 evaluates it")
print(limbs(V.multilinear_eval(table, (*zeta, *alpha))))
print("== with alpha reversed")
print(limbs(V.multilinear_eval(table, (*zeta, *reversed(alpha)))))

# ---- the index column ----------------------------------------------------------------
print("== index_mle at zeta (4 variables) and at its first 2 coordinates")
print(limbs(V.index_mle(zeta)), limbs(V.index_mle(zeta[:2])))
print("== the MLE of [g^0 .. g^15] at zeta, by multilinear_eval")
print(limbs(V.multilinear_eval([gk(i) for i in range(16)], zeta)))

# ---- stacking: selectors, the zero-padded and the one-padded stack ----------------------
sizes = [2, 1, 0]
tables = [[1, 2, 3, 4], [5, 6], [7]]
offsets, mu = V.stack_offsets(sizes)
print("== blocks of sizes 2, 1, 0: offsets", offsets, "mu", mu)
z3 = zeta[:3]
placements = [V.Placement(k, off) for k, off in zip(sizes, offsets)]
sel = [p.eq_above(z3) for p in placements]
print("eq(sel_b, zeta_hi) per block:", [limbs(s) for s in sel])
blocks_at = [V.multilinear_eval([K(v) for v in t], z3[:k]) for t, k in zip(tables, sizes)]
print("block b at zeta_lo:", [limbs(b) for b in blocks_at])
covered = E.sum(s * b for s, b in zip(sel, blocks_at))
ones_padding = E.sum(sel) + V.ONE  # verifier.py:589
print("covered part:", limbs(covered), " ones padding:", limbs(ones_padding))
stack0 = [K(v) for v in [1, 2, 3, 4, 5, 6, 7, 0]]
stack1 = [K(v) for v in [1, 2, 3, 4, 5, 6, 7, 1]]
print("zero-padded stack at zeta:", limbs(V.multilinear_eval(stack0, z3)))
print("one-padded stack at zeta :", limbs(V.multilinear_eval(stack1, z3)))
assert V.multilinear_eval(stack0, z3) == covered
assert V.multilinear_eval(stack1, z3) == covered + ones_padding

# ---- a column claim as a weight on the stack (verifier.py:520-522) -------------------------
point = (E(3, 1, 0),)  # a claim on block 1 (size 1)
lifted = placements[1].stack_point(point, mu)
print("== claim on block 1 at", [limbs(p) for p in point], "lifts to", [limbs(p) for p in lifted])
kernel = V.eq_kernel(lifted)
print("weight eq(lifted, .) on the cube paired with the arbitrary stack [9,8,7,6,5,4,3,2]:")
arbitrary = [K(v) for v in [9, 8, 7, 6, 5, 4, 3, 2]]
print(limbs(V.dot(arbitrary, kernel)), "  block 1 of it, [5,4], at the point:", limbs(V.multilinear_eval([K(5), K(4)], point)))
r = (E(1, 1, 0), E(0, 2, 0), E(7, 0, 0))
print("the weight's extension at r, eq_eval(lifted, r):", limbs(V.eq_eval(lifted, r)))

# ---- back-loaded padding (verifier.py:609-614) -------------------------------------------
# a table on 1 variable in a sumcheck on 3: the summand's weight at the final point carries
# `challenge` for each variable the table lacks.
print("== back-loaded padding: [3,5] lifted by two variables, at (7 | 11, 13) over K-embedded points")
pt = (E(7), E(11), E(13))
short = V.multilinear_eval([K(3), K(5)], pt[:1])
print("table at 7 times 11*13:", limbs(short * pt[1] * pt[2]))
print("MLE of [0,0,0,0,0,0,3,5] at the point:", limbs(V.multilinear_eval([K(v) for v in [0, 0, 0, 0, 0, 0, 3, 5]], pt)))
