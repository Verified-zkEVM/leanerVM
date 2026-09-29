"""Probe for the dossier gt-flock-ring (scratch).

One zerocheck round of Flock, with the formulas of the pinned Rust prover
(crates/flock/src/zerocheck.rs:116-123, `send_round`) and of the pinned verifiers
(crates/fiat_shamir/src/transcript.rs:289-309; python-verifier/verifier.py:406-413), over the
field arithmetic of the pinned Python verifier. `inv0` is the Rust's inverse, which sends 0 to 0
(crates/primitives/src/field/gf2_64x3.rs:137, "`ZERO.inv() == ZERO`").

For a round polynomial G(X) = c0 + c1 X + c2 X^2 and an eq coordinate r, the incoming claim is
(1 + r) G(0) + r G(1). The Rust prover knows G(1) and G(inf) = c2 and derives G(0) from the claim.
"""
import importlib.util, random, sys

sys.dont_write_bytecode = True   # the pinned checkout must stay untouched

spec = importlib.util.spec_from_file_location(
    "verifier", "/home/scaraven/Documents/leanEthereum/leanVM/python-verifier/verifier.py")
v = importlib.util.module_from_spec(spec); sys.modules["verifier"] = v; spec.loader.exec_module(v)
E, ONE, ZERO = v.E, v.ONE, v.ZERO

def inv0(x):            # Rust: F192::inv, ZERO.inv() == ZERO
    return x ** (2**192 - 2)

def rnd(rng):
    return E(rng.getrandbits(64), rng.getrandbits(64), rng.getrandbits(64))

def run(r, rng):
    c0, c1, c2 = rnd(rng), rnd(rng), rnd(rng)           # the true cofactor G
    G = lambda x: c0 + c1 * x + c2 * x * x
    g1, ginf = G(ONE), c2
    claim = (ONE + r) * G(ZERO) + r * g1                  # the true incoming claim
    # Rust prover, send_round:
    g0 = (claim + r * g1) * inv0(ONE + r)
    wire = (g0 + g1 + ginf, ginf)                         # c1, c2 as transmitted (c0 is not sent)
    chi = rnd(rng)
    prover_next = g0 + chi * (g0 + g1 + (ONE + chi) * ginf)
    # verifiers, next_round_poly with eq = Some(r): c0 := claim + r (c1 + c2)
    d0 = claim + r * (wire[0] + wire[1])
    verifier_next = v.poly_eval([d0, wire[0], wire[1]], chi)
    # a prover that sends the true coefficients c1, c2 (no inverse):
    e0 = claim + r * (c1 + c2)
    verifier_next_true = v.poly_eval([e0, c1, c2], chi)
    return (prover_next == verifier_next, verifier_next == G(chi), verifier_next_true == G(chi), c0 != ZERO)

rng = random.Random(20260929)
for name, r in (("r_eq random", rnd(rng)), ("r_eq = 1", ONE)):
    out = [run(r, rng) for _ in range(200)]
    print(name,
          "| Rust prover and verifier agree:", all(o[0] for o in out),
          "| their next claim is the true G(chi):", sum(o[1] for o in out), "/ 200",
          "| with the true coefficients sent, the verifier's next claim is G(chi):", sum(o[2] for o in out), "/ 200")
