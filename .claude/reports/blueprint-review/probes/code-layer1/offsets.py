"""Probe for task code-layer1, deliverable B.2.

Runs the pinned Python verifier's own `stack_offsets` and `build_layout` (imported read-only
from the leanVM checkout at a386121f; no bytecode cache is written) and a line-by-line
transcription of the Rust `stack_offsets` (crates/lean_vm/src/witness.rs:67-79), and prints
the offsets and selectors of two configurations.

Run:  python3 -B .claude/reports/blueprint-review/probes/code-layer1/offsets.py
"""

import sys

sys.dont_write_bytecode = True
sys.path.insert(0, "/home/scaraven/Documents/leanEthereum/leanVM/python-verifier")
import verifier as V  # noqa: E402


def rust_stack_offsets(kappas):
    """witness.rs:67-79, transcribed: `order.sort_by(|a,b| kappas[b].cmp(kappas[a]).then(a.cmp(b)))`."""
    n = len(kappas)
    order = [i for i in range(n) if kappas[i] is not None]
    order.sort(key=lambda i: (-kappas[i], i))
    offsets = [0] * n
    off = 0
    for i in order:
        offsets[i] = off
        off += 1 << kappas[i]
    return offsets, off, order


def report(name, kappas, names=None):
    print(f"== {name}")
    print("sizes in column-index order:", kappas)
    r_off, r_total, order = rust_stack_offsets(kappas)
    p_off, p_log = V.stack_offsets(kappas)
    print("Rust transcription offsets :", r_off, "total", r_total)
    print("Python verifier offsets    :", p_off, "log2_ceil(total)", p_log)
    assert r_off == p_off
    print("stacking order (column indices, first block first):", order)
    print("sorted sizes (the Blocks.size sequence)           :", [kappas[i] for i in order])
    print("offset per block, in stacking order               :", [r_off[i] for i in order])
    print("selector per block (offset >> size)               :", [r_off[i] >> kappas[i] for i in order])
    if names:
        for i in order:
            print(f"   block of column {i:3d} {names[i]:<14s} size {kappas[i]:2d} offset {r_off[i]:8d} selector {r_off[i] >> kappas[i]}")
    print()


# 1. The small configuration of the dossier: six shared columns and two table columns.
names = ["mem_0", "mem_1", "mem_2", "cntfin_mem", "cntfin_bc", "q_flock", "table col a", "table col b"]
report("small configuration", [4, 4, 4, 4, 2, 5, 4, 4], names)

# 2. The pinned verifier's real layout for one admissible announcement:
#    log_memory 16, table log-heights (xor, mul, set, deref, jump, blake2s) = (3, 16, 0, 5, 16, 3),
#    a bytecode of 2^4 instructions (the table has 2^(4+4) words; its content is irrelevant here).
bytecode = [V.K(0)] * (1 << 8)
layout = V.build_layout(bytecode, 16, (3, 16, 0, 5, 16, 3))
cols = []
for column, p in enumerate(layout.placements):
    cols.append((column, p.variables, p.index, p.low))
committed = [(c, k, off) for (c, k, off, low) in cols if low == 0]
virtual = [(c, k, off, low) for (c, k, off, low) in cols if low != 0]
print("== the pinned Python verifier's build_layout(log_memory=16, taus=(3,16,0,5,16,3), kbc=4)")
print("columns:", len(cols), "committed blocks:", len(committed), "strided (BLAKE2S limb) columns:", len(virtual))
print("stack_log:", layout.stack_log)
order = sorted(committed, key=lambda t: t[2])
print("stacking order, as (column index, size, offset):")
print(order)
print("sorted sizes:", [k for (_, k, _) in order])
print("offsets     :", [off for (_, _, off) in order])
print("column index of each block:", [c for (c, _, _) in order])
# the same sizes through the Rust transcription, virtual columns as None
kappas = [None if low != 0 else k for (_, k, _, low) in cols]
r_off, r_total, r_order = rust_stack_offsets(kappas)
assert [r_off[c] for (c, _, _) in committed] == [off for (_, _, off) in committed]
assert r_order == [c for (c, _, _) in order]
print("Rust transcription agrees on every committed column; total", r_total, "log2_ceil", V.log2_ceil(r_total))
print("global column bases of the six tables:", V.GLOBAL_COLUMN_BASES, "widths", V.TABLE_WIDTHS)
