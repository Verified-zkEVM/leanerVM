# Scratch port of crates/pcs/src/whir_config.rs (pin a386121f) parameter derivation,
# to reproduce the query table of python-verifier/verifier.py:910 and to read off
# eta, m, the Johnson list bound L and the per-term security bits.
import math, sys
sys.dont_write_bytecode = True
sys.path.insert(0, "/home/scaraven/Documents/leanEthereum/leanVM/python-verifier")

SECURITY_BITS = 128
QUERY_GRINDING_BITS = 17
INITIAL_FOLDING_FACTOR = 6
SUBSEQUENT_FOLDING_FACTOR = 4
RS_INIT_RED = 3
RS_SUB_RED = 1
RESIDUAL_MAX_LOG = 5
LOG_Q = 192.0
RING_DEG = (1 << 31) + (1 << 15) + (1 << 7) + (1 << 3) + (1 << 1) + 1
M_MAX = 4096

def reduced_rate(lir, cols):
    dim = 2.0 ** cols
    return (dim - 1.0) / 2.0 ** (cols + lir)

def m_param(lir, cols, eta):
    s = math.sqrt(reduced_rate(lir, cols))
    return float(max(math.ceil(s / eta), 3))

def thm_log_a(lir, eta, cols):
    rho = reduced_rate(lir, cols)
    s = math.sqrt(rho)
    gamma = 1.0 - s - eta
    m = m_param(lir, cols, eta)
    half = m + 0.5
    num = 2.0 * half ** 5 + 3.0 * half * gamma * rho
    den = 3.0 * rho ** 1.5
    n = 2.0 ** (cols + lir)
    a = (num / den) * n + half / s
    return math.log2(a)

def log_a(lir, eta, cols, ilv):
    return thm_log_a(lir, eta, cols) + max(ilv - 1.0, 0.0)

def per_q(lir, cols, eta):
    rho = reduced_rate(lir, cols)
    gamma = 1.0 - math.sqrt(rho) - eta
    return math.log2(1.0 / (1.0 - gamma))

def list_log2(lir, cols, eta):
    rho = reduced_rate(lir, cols)
    return math.log2(1.0 / (2.0 * eta * math.sqrt(rho)))

def alg_bits(lir, cols, eta, prevq, ood):
    deg = max(RING_DEG, prevq + ood, 2)
    return LOG_Q - math.log2(deg) - list_log2(lir, cols, eta)

def ood_bits(lir, cols, eta, mu, s):
    l = list_log2(lir, cols, eta)
    lm = math.log2(mu)
    if s == 0:
        return LOG_Q - l - lm
    return s * (LOG_Q - lm) - (2.0 * l - 1.0)

def eta_for_m(lir, cols, m):
    s = math.sqrt(reduced_rate(lir, cols))
    eta = s / m
    import struct
    while m_param(lir, cols, eta) > m:
        eta = math.nextafter(eta, math.inf)
    return eta

def optimize(level, lir, cols, ilv, prevq):
    target = float(SECURITY_BITS)
    qtarget = float(max(SECURITY_BITS - QUERY_GRINDING_BITS, 1))
    mu = cols + ilv
    block = 1 << (cols + lir)
    best = None
    for m in range(3, M_MAX + 1):
        eta = eta_for_m(lir, cols, m)
        max_eta = 1.0 - math.sqrt(reduced_rate(lir, cols))
        if eta >= max_eta:
            continue
        pg = LOG_Q - log_a(lir, eta, cols, ilv)
        if pg + 1e-12 < target:
            break
        pq = per_q(lir, cols, eta)
        if not math.isfinite(pq) or pq <= 0:
            continue
        q = math.ceil(qtarget / pq)
        if q > block:
            continue
        if level == 0:
            s = 0
        else:
            s = next((s for s in range(1, 9) if ood_bits(lir, cols, eta, mu, s) + 1e-12 >= target), None)
            if s is None:
                continue
        if ood_bits(lir, cols, eta, mu, s) + 1e-12 < target or alg_bits(lir, cols, eta, prevq, s) + 1e-12 < target:
            continue
        if best is None or q < best["queries"]:
            best = dict(eta=eta, queries=q, ood=s, m=m, pg=pg, pq=pq,
                        L=2.0 ** list_log2(lir, cols, eta),
                        oodbits=ood_bits(lir, cols, eta, mu, s),
                        alg=alg_bits(lir, cols, eta, prevq, s),
                        qbits=q * pq, rho=reduced_rate(lir, cols),
                        gamma=1.0 - math.sqrt(reduced_rate(lir, cols)) - eta)
    return best

def ladder(log_n, lir):
    rates, cols, ilv, ks = [lir], [log_n - INITIAL_FOLDING_FACTOR], [INITIAL_FOLDING_FACTOR], [INITIAL_FOLDING_FACTOR]
    n_run, r_run, f_run, red = log_n - INITIAL_FOLDING_FACTOR, lir, INITIAL_FOLDING_FACTOR, RS_INIT_RED
    while n_run > RESIDUAL_MAX_LOG:
        k = min(SUBSEQUENT_FOLDING_FACTOR, n_run)
        nxt = n_run - k
        rate = r_run + (f_run - red)
        red = RS_SUB_RED
        rates.append(rate); cols.append(nxt); ilv.append(k); ks.append(k)
        n_run -= k; r_run = rate; f_run = k
    return rates, cols, ilv, ks, n_run

def derive(log_n, lir):
    rates, cols, ilv, ks, yr = ladder(log_n, lir)
    levels, prevq = [], 0
    for i in range(len(rates)):
        b = optimize(i, rates[i], cols[i], ilv[i], prevq)
        assert b is not None, (log_n, lir, i)
        b.update(rate=rates[i], cols=cols[i], ilv=ilv[i], k=ks[i])
        levels.append(b)
        prevq = b["queries"]
    return levels, yr

if __name__ == "__main__":
    import verifier as V
    ok = True
    for lir in range(1, 5):
        for mu in range(15, 29):
            levels, yr = derive(mu, lir)
            mine = tuple(l["queries"] for l in levels)
            tab = V.WHIR_QUERIES[lir - 1][mu - 15]
            cfg = V.derive_config(mu, lir)
            same = (mine == tab) and tuple(l["rate"] for l in levels) == cfg.log_inv_rates and tuple(l["k"] for l in levels) == cfg.folds
            ok &= same
            if not same:
                print("MISMATCH", lir, mu, mine, tab)
    print("query table of verifier.py:910 reproduced from the whir_config.rs derivation:", ok)
    for (mu, lir) in [(15, 1), (18, 1), (22, 1), (28, 1), (28, 2), (28, 4)]:
        levels, yr = derive(mu, lir)
        print(f"\nmu={mu} log_inv_rate={lir} residual={yr}")
        for i, l in enumerate(levels):
            print(f"  L{i}: fold k={l['k']} rate=2^-{l['rate']} msg_cols=2^{l['cols']} rho_red={l['rho']:.6f} "
                  f"m={l['m']} eta={l['eta']:.5f} gamma={l['gamma']:.5f} L<= {l['L']:.2f} "
                  f"queries={l['queries']} ood={l['ood']} | bits: mca-fold={l['pg']:.2f} query={l['qbits']:.2f}(+17 grind) "
                  f"ood={l['oodbits']:.2f} algebraic(list-unioned)={l['alg']:.2f}")
