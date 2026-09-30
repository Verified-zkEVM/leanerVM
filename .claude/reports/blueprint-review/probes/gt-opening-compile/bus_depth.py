# Scratch: bus depth and blueprint error sums at admissible sizes, from the pinned Python
# verifier's own layout code (python-verifier/verifier.py at a386121f).
import sys, math, itertools
sys.dont_write_bytecode = True
sys.path.insert(0, ".")
import verifier_pinned as V

print("tables:", [(t.opcode, t.width, len(t.flushes.push), len(t.flushes.pull), len(t.count_columns), t.n_constraints) for t in V.TABLES])

def depths(log_mem, taus, kbc):
    lay = V.build_layout(range(16 * 2**kbc), log_mem, taus)
    fr = (0, lay.log_memory, lay.log_bytecode)
    push = V.bus_layout(fr, lay.push)
    pull = V.bus_layout(fr, lay.pull)
    cnt = V.bus_layout((), lay.count)
    return lay.stack_log, push.depth, pull.depth, cnt.depth

best = None
# exhaustive over a coarse but covering grid: all taus equal to t or at the floor, memory, bytecode
for log_mem in range(16, 27):
    for kbc in range(0, 29):
        for t in range(0, 27):
            for pattern in itertools.product([0, 1], repeat=6):
                taus = [t if b else 0 for b in pattern]
                taus[5] = max(taus[5], 3)
                try:
                    mu, dp, dl, dc = depths(log_mem, taus, kbc)
                except V.VerificationError:
                    continue
                if not (15 <= mu <= 28):
                    continue
                if best is None or dp > best[0]:
                    best = (dp, mu, log_mem, tuple(taus), kbc, dl, dc)
print("max bus depth found under the window mu<=28:", best)
# at the per-log caps alone (ignoring the stack window)
mu, dp, dl, dc = depths(32, [32]*6, 28)
print("per-log caps (mem 32, tau 32, kbc 28), ignoring the window: stack_log", mu, "bus depth", dp, dl, dc)
