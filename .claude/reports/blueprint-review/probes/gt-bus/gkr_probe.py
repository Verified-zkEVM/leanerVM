"""Probe for the dossier gt-bus: the batched grand-product GKR of leanVM at the pin a386121f.

It drives the PINNED Python verifier's own function `verify_gkr_grand_products`
(`pinned_verifier.py` is a byte-identical copy of `python-verifier/verifier.py`, sha256 checked
by the caller) with

  1. an all-zero stream, to COUNT the scalars read and the challenges drawn as a function of the
     depth mu, and to record which challenge becomes which coordinate of the final point zeta;
  2. an honest prover written here from the specification (section 5.3), to check that the
     verifier's returned leaf values are the multilinear extensions of the leaves at the returned
     point (so that the reading of the normalized round check and of the order of zeta is right);
  3. a cheating prover against a verifier WITHOUT the per-layer check, to confirm the attack of
     part B of the dossier (wrong roots accepted once one layer check is dropped).

Challenges are drawn from a seeded generator instead of the BLAKE2s chain: the questions asked
here are about the interactive protocol, not about Fiat-Shamir.
"""

import random
import sys
from functools import reduce
from operator import mul

sys.dont_write_bytecode = True
import pinned_verifier as pv  # noqa: E402

E, ZERO, ONE = pv.E, pv.ZERO, pv.ONE


class FakeTranscript(pv.Transcript):
    """The pinned transcript with the hash chain replaced by a seeded generator.

    Every other method (next_scalar, next_scalars, samples, sumcheck_round_poly) is the pinned one."""

    def __init__(self, stream, seed):
        self.proof = pv.Proof(tuple(stream), b"")
        self.stream_offset = 0
        self.opening_offset = 0
        self.rng = random.Random(seed)
        self.drawn = []  # every challenge, in the order drawn

    def observe(self, value):
        pass

    def sample(self):
        c = E(self.rng.getrandbits(64), self.rng.getrandbits(64), self.rng.getrandbits(64))
        self.drawn.append(c)
        return c


class ZeroStream(tuple):
    """An endless stream of zeros (for counting)."""

    def __len__(self):
        return 10**9

    def __getitem__(self, i):
        return ZERO


def count(mu):
    t = FakeTranscript([], seed=mu)
    t.proof = pv.Proof(ZeroStream(), b"")
    root_c, point, values = pv.verify_gkr_grand_products(mu, t)
    # which draw is each coordinate of zeta
    where = [next(i for i, c in enumerate(t.drawn) if c is z) for z in point]
    return t.stream_offset, len(t.drawn), where


def scalars_formula(mu):
    return 2 + (mu * mu + 4 * mu + (1 if mu % 2 else 0) if mu > 0 else 0)


def challenges_formula(mu):
    if mu == 0:
        return 1
    if mu % 2 == 0:
        return 1 + mu * mu // 4 + mu
    m = mu - 1  # after the binary layer: layers with 1, 3, ..., mu-2 rounds
    return 1 + 2 + (m // 2) ** 2 + 3 * (m // 2)


# ---------------------------------------------------------------- honest prover (spec 5.3)


def poly_mul(p, q):
    out = [ZERO] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i + j] = out[i + j] + a * b
    return out


def poly_add(p, q):
    n = max(len(p), len(q))
    p = p + [ZERO] * (n - len(p))
    q = q + [ZERO] * (n - len(q))
    return [a + b for a, b in zip(p, q)]


def layers_of(leaves, mu):
    """layers[i] has 2^(mu-i) nodes; node x of layer i is the product of nodes 2x, 2x+1 of layer i-1."""
    layers = [list(leaves)]
    for _ in range(mu):
        prev = layers[-1]
        layers.append([prev[2 * x] * prev[2 * x + 1] for x in range(len(prev) // 2)])
    return layers


def prove(trees, mu, seed, skip_layer=None, lie_root=None):
    """The honest prover of the batched GKR, three trees, one root for the first two.

    `lie_root`, `skip_layer`: the cheating prover of part B. It announces `lie_root` for the first
    two trees; above `skip_layer` it sends round polynomials and children that pass every check of
    that layer (one equation, solved for one child); at `skip_layer` it sends the TRUE children."""
    t = FakeTranscript([], seed)  # draws the same challenges as the verifier will
    stream = []
    layers = [layers_of(tr, mu) for tr in trees]
    roots = [ly[mu][0] for ly in layers]
    shared = roots[0] if lie_root is None else lie_root
    stream += [shared, roots[2]]
    values = [shared, shared, roots[2]]
    lam = t.sample()
    point = []
    layer = mu
    while layer > 0:
        step = 1 if layer % 2 else 2
        width = 1 << step
        k = len(point)
        claim = pv.poly_eval(values, lam)
        # child tables: tabs[s][c][n] = layer-below node c + width * n
        tabs = [[[ly[layer - step][c + width * n] for n in range(1 << k)] for c in range(width)] for ly in layers]
        eq = pv.eq_kernel(point)  # eq(point, n), LSB first
        chis = []
        cheating_here = lie_root is not None and (skip_layer is None or layer >= skip_layer)
        for j in range(k):
            half = 1 << (k - j - 1)
            # the cofactor h_j(Y): the eq weight of coordinate j is factored out
            eq_rest = pv.eq_kernel(point[j + 1 :])
            h = [ZERO]
            for s in range(3):
                acc = [ZERO]
                for x in range(half):
                    term = [eq_rest[x]]
                    for c in range(width):
                        a, b = tabs[s][c][2 * x], tabs[s][c][2 * x + 1]
                        term = poly_mul(term, [a, a + b])  # (1+Y) a + Y b
                    acc = poly_add(acc, term)
                h = poly_add(h, [lam**s * co for co in acc])
            h = h + [ZERO] * (width + 1 - len(h))
            stream += h[1:]  # c0 is derived by the verifier from the running claim
            r = point[j]
            if cheating_here:
                derived0 = claim + r * E.sum(h[1:])
                hh = [derived0] + h[1:]
            else:
                hh = h
                assert h[0] + r * E.sum(h[1:]) == claim, "honest round identity"
            chi = t.sample()
            chis.append(chi)
            claim = pv.poly_eval(hh, chi)
            for s in range(3):
                for c in range(width):
                    tb = tabs[s][c]
                    tabs[s][c] = [tb[2 * x] + chi * (tb[2 * x] + tb[2 * x + 1]) for x in range(half)]
        children = [[tabs[s][c][0] for c in range(width)] for s in range(3)]
        if lie_root is not None and layer != skip_layer and cheating_here:
            # pass this layer's check with a false claim: solve the one equation for one child
            p1 = reduce(mul, children[1])
            p2 = reduce(mul, children[2])
            need0 = claim + lam * p1 + lam * lam * p2
            children[0] = [need0] + [ONE] * (width - 1)
        for s in range(3):
            stream += children[s]
        y = t.samples(step)
        values = [pv.multilinear_eval(ch, y) for ch in children]
        lam = t.sample()
        point = [*y, *chis]
        layer -= step
    return stream, roots


def rand_e(rng):
    return E(rng.getrandbits(64), rng.getrandbits(64), rng.getrandbits(64))


def honest_run(mu, seed):
    rng = random.Random(1000 + seed)
    push = [rand_e(rng) for _ in range(1 << mu)]
    pull = push[:]
    rng.shuffle(pull)  # the same multiset: the bus balances
    cnt = [rand_e(rng) for _ in range(1 << mu)]
    stream, roots = prove([push, pull, cnt], mu, seed)
    t = FakeTranscript(stream, seed)
    root_c, point, values = pv.verify_gkr_grand_products(mu, t)
    assert t.stream_offset == len(stream)
    assert root_c == roots[2]
    for leaves, v in zip([push, pull, cnt], values):
        assert v == pv.multilinear_eval(leaves, point), "leaf claim is the extension at zeta"
    return True


def verify_without_layer_check(depth, transcript, skipped):
    """`verify_gkr_grand_products` of the pinned verifier, verbatim, with the check of one layer removed."""
    shared, count_ = transcript.next_scalar(), transcript.next_scalar()
    combiner = transcript.sample()
    point = []
    values = (shared, shared, count_)
    layer = depth
    while layer > 0:
        step = 1 if layer % 2 else 2
        claim = pv.poly_eval(values, combiner)
        x, claim = pv.sumcheck(transcript, claim, 2**step + 1, point)
        children = [transcript.next_scalars(2**step) for _ in range(3)]
        products = [reduce(mul, child) for child in children]
        if layer != skipped:
            pv.require(claim == pv.poly_eval(products, combiner), f"GKR layer {layer}")
        y = transcript.samples(step)
        values = [pv.multilinear_eval(child, y) for child in children]
        combiner = transcript.sample()
        point = [*y, *x]
        layer -= step
    return count_, tuple(point), (values[0], values[1], values[2])


def attack(mu, skipped, seed):
    """An UNBALANCED bus: the pull tree is not a permutation of the push tree."""
    rng = random.Random(2000 + seed)
    push = [rand_e(rng) for _ in range(1 << mu)]
    pull = [rand_e(rng) for _ in range(1 << mu)]
    cnt = [rand_e(rng) for _ in range(1 << mu)]
    lie = rand_e(rng)
    stream, roots = prove([push, pull, cnt], mu, seed, skip_layer=skipped, lie_root=lie)
    assert roots[0] != roots[1]
    # the full verifier rejects
    try:
        pv.verify_gkr_grand_products(mu, FakeTranscript(stream, seed))
        full = "ACCEPTED"
    except pv.VerificationError as e:
        full = f"rejected ({e})"
    # the verifier without the check of layer `skipped` accepts, with TRUE leaf claims
    t = FakeTranscript(stream, seed)
    _, point, values = verify_without_layer_check(mu, t, skipped)
    true_leaf = all(v == pv.multilinear_eval(lv, point) for lv, v in zip([push, pull, cnt], values))
    return full, true_leaf


if __name__ == "__main__":
    print("mu  scalars(read) formula  challenges formula  zeta_k = draw number (0-based, draws of the GKR only)")
    for mu in range(0, 13):
        s, c, where = count(mu)
        assert s == scalars_formula(mu), (mu, s, scalars_formula(mu))
        assert c == challenges_formula(mu), (mu, c, challenges_formula(mu))
        print(f"{mu:2d}  {s:6d} {scalars_formula(mu):8d}  {c:6d} {challenges_formula(mu):8d}   {where}   total draws {c}")
    for mu in range(1, 6):
        for seed in range(2):
            honest_run(mu, seed)
    print("honest prover: accepted by the pinned verifier for mu = 1..5; leaf values = extensions at zeta")
    for mu, skipped in [(4, 4), (4, 2), (5, 5), (5, 4), (5, 2)]:
        full, true_leaf = attack(mu, skipped, seed=7)
        print(f"unbalanced bus, mu={mu}, check of layer {skipped} removed: full verifier {full}; "
              f"weakened verifier accepts, leaf claims true: {true_leaf}")
