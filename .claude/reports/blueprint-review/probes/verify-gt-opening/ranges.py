# verify-gt-opening: ranges over all 56 supported (mu, log_inv_rate) pairs of the quantities the
# dossier gt-opening-compile quotes from a sample of six sizes. Imports the dossier's own port
# (probes/gt-opening-compile/whir_params.py) unchanged.
import sys, math
sys.dont_write_bytecode = True
sys.path.insert(0, "../gt-opening-compile")
import whir_params as W

rows = []
for lir in range(1, 5):
    for mu in range(15, 29):
        levels, _ = W.derive(mu, lir)
        for i, l in enumerate(levels):
            rows.append((mu, lir, i, l))

def extreme(key, name):
    lo = min(rows, key=lambda r: r[3][key]); hi = max(rows, key=lambda r: r[3][key])
    print(f"{name}: min {lo[3][key]:.2f} at (mu={lo[0]}, log_inv_rate={lo[1]}, level {lo[2]}); "
          f"max {hi[3][key]:.2f} at (mu={hi[0]}, log_inv_rate={hi[1]}, level {hi[2]})")

l0 = [r for r in rows if r[2] == 0]
lo = min(l0, key=lambda r: r[3]["L"]); hi = max(l0, key=lambda r: r[3]["L"])
print(f"L_0 (level 0 Johnson list bound): min {lo[3]['L']:.2f} at (mu={lo[0]}, log_inv_rate={lo[1]}); "
      f"max {hi[3]['L']:.2f} at (mu={hi[0]}, log_inv_rate={hi[1]}) = 2^{math.log2(hi[3]['L']):.2f}")
extreme("L", "L (all levels)")
extreme("pg", "fold (MCA) bits")
extreme("alg", "list-unioned algebraic bits")
extreme("oodbits", "OOD bits")
extreme("qbits", "query bits before grinding")
m28 = [r for r in rows if r[0] == 28 and r[1] == 1]
print("min fold bits at mu=28, log_inv_rate=1:", round(min(r[3]["pg"] for r in m28), 2))
