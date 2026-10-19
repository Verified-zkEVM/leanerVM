#!/usr/bin/env python3
"""Does ArkLib's proved Johnson MCA constant meet Annex B's per-level budget?

Reproduces leanVM's per-level eta search (`crates/pcs/src/whir_config.rs` at
`a386121f`, IEEE doubles as the Rust computes them), cross-checks the query
counts against the Python verifier's `WHIR_QUERIES` (`verifier.py:910`), and
then evaluates, in exact rational arithmetic (`fractions`) with 80-digit
decimals only for the irrational square roots and logarithms:

  * Annex B's `a` (`thm:mca-johnson`, the printed [BCHKS25] Thm 4.6 constant),
  * ArkLib's `johnsonExceptionCount n D ⌈a n⌉₊ η` (the constant of the proved
    `ReedSolomon.mcaError_affineLine_johnson_le`),
  * the fold-challenge error of `thm:rbr` with each constant,

at every level of every admissible `(mu, R)` pair.  No float enters a verdict:
the exact-rational comparisons `E0 <= 2^k` and `E0 <= a` are decided exactly.

Usage: python3 scripts/whir-mca-budget.py [--json FILE] [--full]
"""
from fractions import Fraction as Fr
from decimal import Decimal, getcontext
import math, sys, json, argparse

getcontext().prec = 80

# --- constants, whir_config.rs:38-86, pack.rs:7, ring_switch.rs:80 ----------
SECURITY_BITS = 128
QUERY_GRINDING_BITS = 17
LOG_Q = 192.0
INITIAL_K = 6
SUBSEQ_K = 4
INIT_RED = 3
SUBSEQ_RED = 1
RESIDUAL_MAX_LOG = 5
JOHNSON_ETA_SEARCH_MAX_M = 4096
RING_SWITCH_SOUNDNESS_DEGREE = (1 << 31) + (1 << 15) + (1 << 7) + (1 << 3) + (1 << 1) + 1
MIN_MU, MAX_MU = 15, 28
MIN_R, MAX_R = 1, 4

# verifier.py:910, verbatim
WHIR_QUERIES = (((223,55), (223,56,30), (223,56,31), (224,56,32), (224,56,32), (224,56,32,22), (224,56,32,22), (225,56,32,23), (225,56,32,23), (225,56,32,23,17), (226,56,32,23,17), (226,56,32,23,18), (227,56,32,23,18), (228,56,32,23,18,14)), ((112,45), (112,45,27), (112,45,28), (112,45,28), (112,45,28), (112,45,28,20), (112,45,28,20), (112,45,28,21), (112,45,28,21), (113,45,28,21,16), (113,45,28,21,16), (113,45,28,21,16), (113,45,28,21,16), (113,45,28,21,17,13)), ((75,37), (75,37,24), (75,38,25), (75,38,25), (75,38,25), (75,38,25,18), (75,38,25,19), (75,38,25,19), (75,38,25,19), (75,38,25,19,15), (75,38,25,19,15), (75,38,25,19,15), (75,38,25,19,15), (76,38,25,19,16,13)), ((56,32), (56,32,22), (56,32,22), (56,32,23), (56,32,23), (56,32,23,17), (56,32,23,17), (56,32,23,18), (56,32,23,18), (57,32,23,18,14), (57,32,23,18,14), (57,32,23,18,15), (57,33,23,18,15), (57,33,23,18,15,12)))  # fmt: skip


# --- the Rust, in doubles ----------------------------------------------------
def exp2i(x: int) -> float:
    return math.ldexp(1.0, x)


def reduced_rate(rate: int, cols: int) -> float:
    return (exp2i(cols) - 1.0) / exp2i(cols + rate)


def johnson_m_param(rate: int, cols: int, eta: float) -> float:
    sqrt_rho = math.sqrt(reduced_rate(rate, cols))
    return float(max(math.ceil(sqrt_rho / eta), 3))


def powi5(x: float) -> float:
    # compiler-rt __powidf2 / LLVM powi expansion for exponent 5: x * (x^2)^2
    x2 = x * x
    x4 = x2 * x2
    return x * x4


def paper_thm_ca_johnson_log_a(rate: int, eta: float, cols: int) -> float:
    rho = reduced_rate(rate, cols)
    sqrt_rho = math.sqrt(rho)
    gamma = 1.0 - sqrt_rho - eta
    half = johnson_m_param(rate, cols, eta) + 0.5
    numerator = 2.0 * powi5(half) + 3.0 * half * gamma * rho
    denominator = 3.0 * math.pow(rho, 1.5)
    n = exp2i(cols + rate)
    a = (numerator / denominator) * n + half / sqrt_rho
    return math.log2(a)


def paper_johnson_log_a(rate: int, eta: float, cols: int, ilv: int) -> float:
    return paper_thm_ca_johnson_log_a(rate, eta, cols) + max(float(ilv) - 1.0, 0.0)


def paper_per_query_bits(rate: int, cols: int, eta: float) -> float:
    rho = reduced_rate(rate, cols)
    gamma = 1.0 - math.sqrt(rho) - eta
    return math.log2(1.0 / (1.0 - gamma))


def johnson_interleaved_list_log2(rate: int, cols: int, eta: float) -> float:
    rho = reduced_rate(rate, cols)
    return math.log2(1.0 / (2.0 * eta * math.sqrt(rho)))


def johnson_algebraic_bits_for(rate, cols, eta, prev_queries, ood_samples) -> float:
    log2_l = johnson_interleaved_list_log2(rate, cols, eta)
    degree = max(RING_SWITCH_SOUNDNESS_DEGREE, prev_queries + ood_samples, 2)
    return LOG_Q - math.log2(float(degree)) - log2_l


def paper_ood_bits(rate, cols, eta, mu_vars, ood_samples) -> float:
    log2_l = johnson_interleaved_list_log2(rate, cols, eta)
    log2_mu = math.log2(float(mu_vars))
    if ood_samples == 0:
        return LOG_Q - log2_l - log2_mu
    return ood_samples * (LOG_Q - log2_mu) - (2.0 * log2_l - 1.0)


def johnson_eta_for_m(rate: int, cols: int, m: int) -> float:
    sqrt_rho = math.sqrt(reduced_rate(rate, cols))
    eta = sqrt_rho / float(m)
    while johnson_m_param(rate, cols, eta) > float(m):
        eta = math.nextafter(eta, math.inf)
    assert johnson_m_param(rate, cols, eta) == float(m)
    return eta


def optimize_johnson_level(level, rate, cols, ilv, target_bits, query_grinding_bits, prev_queries,
                           log_a_fn=paper_johnson_log_a):
    """whir_config.rs `optimize_johnson_level`.  `log_a_fn` lets the search be
    rerun with another MCA constant; the default is the Rust's."""
    target = float(target_bits)
    query_target = float(max(target_bits - query_grinding_bits, 1))
    mu = cols + ilv
    block_len = 1 << (cols + rate)
    best = None
    for m in range(3, JOHNSON_ETA_SEARCH_MAX_M + 1):
        eta = johnson_eta_for_m(rate, cols, m)
        max_eta = 1.0 - math.sqrt(reduced_rate(rate, cols))
        if eta >= max_eta:
            continue
        eps_pg = LOG_Q - log_a_fn(rate, eta, cols, ilv)
        if eps_pg + 1e-12 < target:
            break
        per_q = paper_per_query_bits(rate, cols, eta)
        if not math.isfinite(per_q) or per_q <= 0.0:
            continue
        queries = math.ceil(query_target / per_q)
        if queries > block_len:
            continue
        if level == 0:
            ood = 0
        else:
            ood = next((s for s in range(1, 9)
                        if paper_ood_bits(rate, cols, eta, mu, s) + 1e-12 >= target), None)
            if ood is None:
                continue
        if paper_ood_bits(rate, cols, eta, mu, ood) + 1e-12 < target:
            continue
        if johnson_algebraic_bits_for(rate, cols, eta, prev_queries, ood) + 1e-12 < target:
            continue
        cand = dict(m=m, eta=eta, queries=queries, ood=ood, eps_pg=eps_pg)
        if best is None or cand["queries"] < best["queries"]:
            best = cand
    if best is None:
        raise RuntimeError(f"L{level}: no eta candidate")
    return best


def derive_ladder_shape(log_n: int, rate0: int):
    """whir_config.rs `derive_ladder` + `derive_ladder_shape`: per level
    (log_inv_rate, log_msg_cols, log_num_interleaved, k)."""
    assert log_n > INITIAL_K
    levels = [dict(rate=rate0, cols=log_n - INITIAL_K, ilv=INITIAL_K, k=INITIAL_K)]
    n_running = log_n - INITIAL_K
    rate_running, fold_running, reduction = rate0, INITIAL_K, INIT_RED
    while n_running > RESIDUAL_MAX_LOG:
        k = min(SUBSEQ_K, n_running)
        rate = rate_running + (fold_running - reduction)
        reduction = SUBSEQ_RED
        levels.append(dict(rate=rate, cols=n_running - k, ilv=k, k=k))
        n_running -= k
        rate_running, fold_running = rate, k
    assert len(levels) >= 2
    return levels, n_running


def derive_config(mu: int, rate0: int, log_a_fn=paper_johnson_log_a):
    levels, yr = derive_ladder_shape(mu, rate0)
    prev_q = 0
    for i, lv in enumerate(levels):
        opt = optimize_johnson_level(i, lv["rate"], lv["cols"], lv["ilv"], SECURITY_BITS,
                                     QUERY_GRINDING_BITS, prev_q, log_a_fn)
        lv.update(opt)
        prev_q = opt["queries"]
    return levels, yr


# --- exact arithmetic ---------------------------------------------------------
def floor_sqrt(x: Fr) -> int:
    """⌊√x⌋ for a nonnegative rational `x`."""
    assert x >= 0
    return math.isqrt(x.numerator * x.denominator) // x.denominator


def ceil_sqrt(x: Fr) -> int:
    """⌈√x⌉ for a nonnegative rational `x`, exactly."""
    s = floor_sqrt(x)
    return s if Fr(s) ** 2 == x else s + 1


def ceil_fr(x: Fr) -> int:
    return -((-x.numerator) // x.denominator)


def dec(x: Fr) -> Decimal:
    return Decimal(x.numerator) / Decimal(x.denominator)


LN2 = Decimal(2).ln()


def log2d(x) -> Decimal:
    if isinstance(x, Fr):
        x = dec(x)
    return x.ln() / LN2


def exact_level(lv: dict) -> dict:
    """ArkLib's `johnsonExceptionCount n D ⌈a n⌉₊ η` and Annex B's `a` at the
    level's deployed `eta` (the Rust double, as an exact dyadic rational)."""
    cols, rate, ilv = lv["cols"], lv["rate"], lv["ilv"]
    n = 1 << (cols + rate)
    D = (1 << cols) - 1                       # degree bound: dimension 2^cols = D + 1
    rho = Fr(D, n)                            # = johnsonRhoMinus n D = Annex B's (k-1)/n
    eta = Fr(lv["eta"])                       # exact value of the deployed double
    # Annex B / Rust: theta = max(⌈√ρ/η⌉, 3), exactly: ⌈√(ρ/η²)⌉
    m_exact = max(ceil_sqrt(rho / eta ** 2), 3)
    # ArkLib: M = max ⌈√ρ/(2η)⌉₊ 3
    M = max(ceil_sqrt(rho / (4 * eta ** 2)), 3)
    t = Fr(M) + Fr(1, 2)
    mu_ark = ceil_sqrt(t ** 2 / rho) - 1      # ⌈t/√ρ⌉₊ - 1
    h = ceil_fr(t ** 2 / (3 * rho)) - 1       # ⌈t²/(3ρ)⌉₊ - 1
    # A = ⌈(√ρ + η) n⌉₊: the least A with A - ηn ≥ 0 and (A - ηn)² ≥ ρ n²
    A = floor_sqrt(rho * n * n) + math.floor(eta * n)
    while not (Fr(A) - eta * n >= 0 and (Fr(A) - eta * n) ** 2 >= rho * n * n):
        A += 1
    assert (Fr(A - 1) - eta * n) < 0 or (Fr(A - 1) - eta * n) ** 2 < rho * n * n
    theta = Fr(n - D, A - D)
    E0 = (2 * mu_ark - 1) * h + theta * (h + mu_ark + 4 * D * mu_ark * h) + (n - D - 1) * mu_ark
    E0ref = ((2 * mu_ark - 1) * h + theta * (h + mu_ark + (2 * D - 1) * h * (2 * mu_ark - 1))
             + (n - D - 1) * mu_ark)
    # Annex B's a, 80 digits
    sr = dec(rho).sqrt()
    tB = Decimal(m_exact) + Decimal("0.5")
    gamma = 1 - sr - dec(eta)
    a = (2 * tB ** 5 + 3 * tB * gamma * dec(rho)) / (3 * sr ** 3) * n + tB / sr
    # the ArkLib closed bound (8/3) n t^3 / ρ, for reference
    closed = Fr(8, 3) * n * t ** 3 / rho
    L = 1 / (2 * dec(eta) * sr)               # Johnson list size, thm:johnson-interleaved
    p = max(ilv - 1, 0)                       # row-union exponent, lem:fold-list at j = 1
    q = Decimal(2) ** 192
    fold_a = (2 * L + Decimal(2) ** p * a) / q
    fold_E = (2 * L + Decimal(2) ** p * dec(E0)) / q
    hyp = dict(
        D_ge_1=D >= 1, D_le_n_minus_2=D <= n - 2, eta_pos=eta > 0,
        agreement_le_1=(Fr(1) - eta >= 0 and (Fr(1) - eta) ** 2 >= rho),  # √ρ + η ≤ 1
    )
    return dict(
        n=n, D=D, rho=rho, eta=eta, m_exact=m_exact, m_float=int(lv["m"]), M_ark=M,
        mu_ark=mu_ark, h=h, A=A, theta=theta, E0=E0, E0ref=E0ref, a=a, closed=closed,
        log2_E0=log2d(E0), log2_a=log2d(a), log2_a_float=Decimal(paper_thm_ca_johnson_log_a(rate, lv["eta"], cols)),
        log2_E0ref=log2d(E0ref), log2_closed=log2d(closed),
        p=p, margin_a=192 - log2d(a) - p, margin_E=192 - log2d(E0) - p,
        bits_fold_a=-log2d(fold_a), bits_fold_E=-log2d(fold_E), log2_L=log2d(L),
        E0_le_a=(dec(E0) <= a), E0_le_16_49_a=(dec(E0) * 49 <= 16 * a),
        E0_within_budget=(E0 * (1 << p) <= 1 << 64),          # exact: 2^{p} E0 / 2^192 ≤ 2^-128
        hyp=hyp,
    )


# --- weighted Johnson certificate (informational) ------------------------------
def weighted_best(n, D, A, m_max=40, B_max=400):
    """Least `johnsonWeightedRefinedExceptionCount n D A B H` over certificates
    `IsJohnsonWeightedCertificate n D A m B H` with m ≤ m_max, B ≤ min(2D+1, B_max)."""
    best = None
    for m in range(1, m_max + 1):
        for B in range(1, min(2 * D + 1, B_max) + 1):
            if not (D * B < m * A):
                break
            u = min(B, m - 1)
            N = (B + 1) * m * A - D * B * (B + 1) // 2
            W = m * A * B * (B + 1) // 2 - D * B * (B + 1) * (2 * B + 1) // 6
            R = (u + 1) * m - u * (u + 1) // 2
            T = m * u * (u + 1) // 2 - u * (u + 1) * (2 * u + 1) // 6
            slope = N - n * R
            if slope <= 0:
                continue
            H = max(B, (W - n * T) // slope)
            cnt = (2 * B - 1) * H + Fr(n - D, A - D) * (H + B + (2 * D - 1) * H * (2 * B - 1)) + (n - D - 1) * B
            if best is None or cnt < best[0]:
                best = (cnt, m, B, H)
    return best


# --- main ---------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", help="write the per-level data here")
    ap.add_argument("--full", action="store_true", help="print every level")
    ap.add_argument("--weighted", action="store_true", help="search weighted certificates (slow)")
    ap.add_argument("--rechoose", action="store_true", help="rerun the eta search with ArkLib's E0")
    args = ap.parse_args()

    rows = []
    mismatches = []
    for R in range(MIN_R, MAX_R + 1):
        for mu in range(MIN_MU, MAX_MU + 1):
            levels, yr = derive_config(mu, R)
            table = WHIR_QUERIES[R - 1][mu - MIN_MU]
            got = tuple(lv["queries"] for lv in levels)
            if got != table:
                mismatches.append((mu, R, got, table))
            for i, lv in enumerate(levels):
                ex = exact_level(lv)
                rows.append(dict(mu=mu, R=R, level=i, rate=lv["rate"], cols=lv["cols"], ilv=lv["ilv"],
                                 queries=lv["queries"], ood=lv["ood"], eps_pg_float=lv["eps_pg"], **ex))

    print(f"levels: {len(rows)} over {len(range(MIN_MU, MAX_MU+1)) * len(range(MIN_R, MAX_R+1))} (mu, R) pairs")
    print(f"query-table mismatches vs verifier.py:910: {len(mismatches)}")
    for mm in mismatches:
        print("  MISMATCH", mm)
    off = sum(r['m_float'] != r['m_exact'] for r in rows)
    print(f"levels whose float ceil(sqrt(rho)/eta) differs from the exact one: {off} of {len(rows)}")
    print(f"all hypotheses of mcaError_affineLine_johnson_le hold: {all(all(r['hyp'].values()) for r in rows)}")
    print(f"E0 <= a at every level (exact):           {all(r['E0_le_a'] for r in rows)}")
    print(f"E0 <= (16/49) a at every level (exact):   {all(r['E0_le_16_49_a'] for r in rows)}")
    print(f"2^(l-1) E0 <= 2^64 at every level (exact): {all(r['E0_within_budget'] for r in rows)}")
    print(f"max |log2 a (float, Rust) - log2 a (exact)|: {max(abs(r['log2_a_float'] - r['log2_a']) for r in rows):.3e}")
    gain = [r["log2_a"] - r["log2_E0"] for r in rows]
    print(f"log2(a / E0): min {min(gain):.3f}  max {max(gain):.3f}")
    print(f"min margin (bits) with a : {min(r['margin_a'] for r in rows):.4f}   with E0: {min(r['margin_E'] for r in rows):.4f}")
    print(f"min fold-row bits (2L + 2^(l-1) a)/|E| with a : {min(r['bits_fold_a'] for r in rows):.4f}   with E0: {min(r['bits_fold_E'] for r in rows):.4f}")
    print(f"levels whose full fold row is below 128 bits with a : {sum(1 for r in rows if r['bits_fold_a'] < 128)}   with E0: {sum(1 for r in rows if r['bits_fold_E'] < 128)}")

    print("\nWorst level per rate exponent (least margin with ArkLib's E0):")
    print("| R | (mu, level) | n | D | theta | M_ark | log2 a | log2 E0 | margin a | margin E0 | fold row a | fold row E0 |")
    print("|---|---|---|---|---|---|---|---|---|---|---|---|")
    for R in range(MIN_R, MAX_R + 1):
        r = min((r for r in rows if r["R"] == R), key=lambda r: r["margin_E"])
        print(f"| {R} | ({r['mu']}, {r['level']}) | 2^{r['n'].bit_length()-1} | {r['D']} | {r['m_exact']} | {r['M_ark']} | "
              f"{r['log2_a']:.3f} | {r['log2_E0']:.3f} | {r['margin_a']:.3f} | {r['margin_E']:.3f} | "
              f"{r['bits_fold_a']:.3f} | {r['bits_fold_E']:.3f} |")
    worst = min(rows, key=lambda r: r["margin_E"])
    print(f"\nWorst overall: (mu, R, level) = ({worst['mu']}, {worst['R']}, {worst['level']}), "
          f"n = 2^{worst['n'].bit_length()-1}, D = {worst['D']}, eta = {worst['eta']} "
          f"(~{float(worst['eta']):.6e}), theta = {worst['m_exact']}, M_ark = {worst['M_ark']}, "
          f"mu = {worst['mu_ark']}, h = {worst['h']}, A = {worst['A']}, E0 = {worst['E0']}")
    first = next(r for r in rows if r["mu"] == 15 and r["R"] == 1 and r["level"] == 0)
    print(f"\n(15, 1) level 0: n = {first['n']}, D = {first['D']}, eta = {first['eta']} (~{float(first['eta']):.6e}), "
          f"theta = {first['m_exact']}, M_ark = {first['M_ark']}, mu = {first['mu_ark']}, h = {first['h']}, A = {first['A']}, "
          f"incidence ratio = {first['theta']}, E0 = {first['E0']} (log2 {first['log2_E0']:.3f}), log2 a = {first['log2_a']:.3f}, "
          f"queries = {first['queries']}")

    if args.full:
        print("\nAll levels:")
        print("| mu | R | lvl | rate | cols | l | q | eta | m | M | log2 a | log2 E0 | gain | margin a | margin E0 |")
        print("|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|")
        for r in rows:
            print(f"| {r['mu']} | {r['R']} | {r['level']} | {r['rate']} | {r['cols']} | {r['ilv']} | {r['queries']} | "
                  f"{float(r['eta']):.4e} | {r['m_exact']} | {r['M_ark']} | {r['log2_a']:.3f} | {r['log2_E0']:.3f} | "
                  f"{r['log2_a'] - r['log2_E0']:.3f} | {r['margin_a']:.3f} | {r['margin_E']:.3f} |")

    if args.weighted:
        print("\nWeighted certificate (informational), worst level and (15,1,0):")
        for r in (worst, first):
            b = weighted_best(r["n"], r["D"], r["A"])
            if b is None:
                print(f"  ({r['mu']},{r['R']},{r['level']}): no certificate in the searched range")
            else:
                print(f"  ({r['mu']},{r['R']},{r['level']}): best weighted count log2 {float(log2d(b[0])):.3f} at m={b[1]}, B={b[2]}, H={b[3]} "
                      f"(vs log2 E0 {r['log2_E0']:.3f})")

    if args.rechoose:
        # Rerun the Rust's search with ArkLib's constant in place of Annex B's a.
        def log_a_E0(rate, eta, cols, ilv):
            ex = exact_level(dict(rate=rate, cols=cols, ilv=ilv, eta=eta, m=0))
            return float(ex["log2_E0"]) + max(ilv - 1, 0)
        total_old = total_new = 0
        changed = []
        for R in range(MIN_R, MAX_R + 1):
            for mu in range(MIN_MU, MAX_MU + 1):
                old, _ = derive_config(mu, R)
                new, _ = derive_config(mu, R, log_a_E0)
                qo = [lv["queries"] for lv in old]
                qn = [lv["queries"] for lv in new]
                total_old += sum(qo); total_new += sum(qn)
                if qo != qn:
                    changed.append((mu, R, qo, qn, [lv["m"] for lv in old], [lv["m"] for lv in new]))
        print(f"\nRe-choosing eta with ArkLib's E0: total queries {total_old} -> {total_new} "
              f"({len(changed)} of 56 pairs change)")
        for c in changed[:12]:
            print("  ", c)

    if args.json:
        def conv(v):
            if isinstance(v, Fr):
                return {"num": v.numerator, "den": v.denominator}
            if isinstance(v, Decimal):
                return float(v)
            return v
        with open(args.json, "w") as f:
            json.dump([{k: conv(v) for k, v in r.items()} for r in rows], f, indent=1)


if __name__ == "__main__":
    main()
