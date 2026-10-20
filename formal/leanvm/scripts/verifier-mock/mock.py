"""A mock interactive run of verify_execution: scripted challenges (not Fiat--Shamir), committed
words given by a formula, and prover messages fixed up so that every check passes."""
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import *

ORIG_EQ = E.__eq__
LAST = {"diff": None, "read": None}

def patched_eq(self, other):
    if isinstance(other, E):
        LAST["diff"] = self + other
    return ORIG_EQ(self, other)

E.__eq__ = patched_eq
E.__hash__ = lambda self: hash(int(self))

class Stop(Exception):
    pass

def sample_value(j):
    return fe(j + 2**20)

def row_word(i, p, j):
    return K(fw(i * 2**40 + p * 2**12 + j + 2**30, 3))

def read_value(k, overrides):
    return overrides.get(k, fe(k))

class Mock:
    def __init__(self, overrides):
        self.overrides = overrides
        self.reads = 0
        self.samples_n = 0
        self.events = []
        self.read_values = []

    def next_scalar(self):
        k = self.reads
        self.reads += 1
        v = read_value(k, self.overrides)
        LAST["read"] = k
        self.events.append(("r", k))
        self.read_values.append(v)
        return v

    next_scalars = V.Transcript.next_scalars
    sumcheck_round_poly = V.Transcript.sumcheck_round_poly
    samples = V.Transcript.samples

    def sample(self):
        j = self.samples_n
        self.samples_n += 1
        self.events.append(("s", j))
        return sample_value(j)

    def grind_check(self, bits):
        self.events.append(("g", bits))

    def merkle(self, root, block_length, queries, leaf_words):
        i = ROOTS[root.value]
        h = V.log2_strict(block_length)
        self.events.append(("q", i, h, leaf_words, list(queries)))
        return [tuple(row_word(i, q, j) for j in range(leaf_words)) for q in queries]

    def finish(self):
        pass

ROOTS = {}
MOCK = {}

def from_halves(cls, low, high):
    i = len(ROOTS)
    value = i.to_bytes(32, "little")
    ROOTS[value] = i
    MOCK["m"].events.append(("c", i, MOCK["m"].reads - 2, MOCK["m"].reads - 1))
    return cls(value)

V.Digest.from_halves = classmethod(from_halves)

STATE = {"count": 0, "stop_at": None, "failure": None}

def require(condition, message):
    idx = STATE["count"]
    STATE["count"] += 1
    if STATE["stop_at"] is not None and idx == STATE["stop_at"]:
        STATE["failure"] = (idx, LAST["read"], LAST["diff"], message)
        raise Stop()
    if not condition:
        STATE["failure"] = (idx, LAST["read"], LAST["diff"], message)
        raise Stop()

V.require = require

def run(bytecode, public_input, overrides, stop_at=None):
    ROOTS.clear()
    STATE.update(count=0, stop_at=stop_at, failure=None)
    m = Mock(overrides)
    MOCK["m"] = m
    V.Transcript = lambda proof, iv, pi: m
    try:
        V.verify_execution(bytecode, public_input, V.Proof((), b""))
        return m, None
    except Stop:
        return m, STATE["failure"]

def solve(bytecode, public_input, overrides):
    while True:
        t = time.time()
        m, failure = run(bytecode, public_input, overrides)
        print("run", time.time() - t, failure and failure[0], failure and failure[3], file=sys.stderr)
        if failure is None:
            return m
        idx, k, d0, message = failure
        assert d0 is not None, message
        v0 = read_value(k, overrides)
        trial = dict(overrides)
        trial[k] = v0 + V.ONE
        _, f1 = run(bytecode, public_input, trial, stop_at=idx)
        d1 = f1[2]
        b = d0 + d1
        assert b != V.ZERO, message
        overrides[k] = v0 + d0 / b
