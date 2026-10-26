#!/usr/bin/env python3
"""Differential fuzzing of leanerVM's executable verifier against the pinned Rust leanVM verifier.

Mutates proofs in the text format of scripts/dump-proof-rust.sh and hands each mutant to two
oracles, `leanervm-check serve` (bench/LeanerVMCheck.lean) and `proof-check serve`
(tests/rust/proof_check.rs), which answer one line per path: <file>\t<VERDICT>\t<detail>\t<micros>.
Standard library only; run with `python3 -I`.

Subcommands: selftest, list, mutate, replay, enumerate, run.  See README.md next to this file.
"""

import argparse
import gzip
import json
import os
import queue
import random
import re
import shutil
import subprocess
import sys
import threading
import time
from collections import Counter, defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
LEAN_BIN = os.path.join(ROOT, ".lake/build/bin/leanervm-check")
OUT_DIR = os.path.join(ROOT, ".lake/differential")
VECTOR = os.path.join(ROOT, "tests/vectors/fill.proof.gz")
FIXTURE = os.path.join(ROOT, "tests/LeanerVMTests/Protocol/RustProofData.lean")
SCOPE = []  # the systemd-run prefix of every oracle process; set by main (--memory)
M64 = (1 << 64) - 1
ORD_G = (1 << 64) - 1  # order of the generator g whose powers the operands name

# ---------------------------------------------------------------------------------------------
# The proof structure, parser and serialiser
# ---------------------------------------------------------------------------------------------


class Phase:
    __slots__ = ("rows", "sibs")

    def __init__(self, rows, sibs):
        self.rows = rows  # list of tuples of 64-bit ints
        self.sibs = sibs  # list of 64-hex-digit strings

    def clone(self):
        return Phase(list(self.rows), list(self.sibs))


class Proof:
    __slots__ = ("tag", "rate", "prog", "phash", "pub", "stream", "merkle")

    def __init__(self, tag, rate, prog, phash, pub, stream, merkle):
        self.tag = tag        # str
        self.rate = rate      # str (decimal as written)
        self.prog = prog      # list of tuples of tokens (str)
        self.phash = phash    # str, 64 hex digits (stale after program mutations, on purpose)
        self.pub = pub        # list of 6 ints: e0.c0 e0.c1 e0.c2 e1.c0 e1.c1 e1.c2
        self.stream = stream  # list of (c0, c1, c2) int tuples
        self.merkle = merkle  # list of Phase

    def clone(self):
        """Copy-on-write clone: every list is copied, the immutable tuples inside are shared."""
        return Proof(self.tag, self.rate, list(self.prog), self.phash, list(self.pub),
                     list(self.stream), [ph.clone() for ph in self.merkle])


class ParseError(Exception):
    pass


def parse(text):
    """Strict parser of the canonical format the dump script prints."""
    lines = text.split("\n")
    if lines and lines[-1] == "":
        lines.pop()
    pos = 0

    def nxt(expect=None):
        nonlocal pos
        if pos >= len(lines):
            raise ParseError("unexpected end of file")
        l = lines[pos]
        pos += 1
        toks = l.split(" ")
        if expect is not None and toks[0] != expect:
            raise ParseError(f"line {pos}: expected {expect}, got {l[:60]!r}")
        return toks

    t = nxt("leanvm-proof")
    tag = " ".join(t[1:])
    rate = nxt("rate")[1]
    n = int(nxt("program")[1])
    prog = [tuple(nxt()) for _ in range(n)]
    phash = nxt("program_hash")[1]
    pub = [int(x, 16) for x in nxt("public")[1:]]
    if len(pub) != 6:
        raise ParseError("public needs 6 limbs")
    n = int(nxt("stream")[1])
    stream = []
    for _ in range(n):
        a, b, c = nxt()
        stream.append((int(a, 16), int(b, 16), int(c, 16)))
    p = int(nxt("merkle")[1])
    merkle = []
    for _ in range(p):
        _, r, s = nxt("phase")
        rows = []
        for _ in range(int(r)):
            t = nxt("row")
            words = tuple(int(w, 16) for w in t[2:] if w != "")
            if len(words) != int(t[1]):
                raise ParseError("row width mismatch")
            rows.append(words)
        sibs = [nxt("sibling")[1] for _ in range(int(s))]
        merkle.append(Phase(rows, sibs))
    nxt("end")
    if pos != len(lines):
        raise ParseError("trailing lines after end")
    return Proof(tag, rate, prog, phash, pub, stream, merkle)


def h16(x):
    return "%016x" % x


def dump(p):
    """The dump script's printer; counts are always written from the structure."""
    out = [f"leanvm-proof {p.tag}", f"rate {p.rate}", f"program {len(p.prog)}"]
    out.extend(" ".join(op) for op in p.prog)
    out.append(f"program_hash {p.phash}")
    out.append("public " + " ".join(map(h16, p.pub)))
    out.append(f"stream {len(p.stream)}")
    out.extend("%016x %016x %016x" % s for s in p.stream)
    out.append(f"merkle {len(p.merkle)}")
    for ph in p.merkle:
        out.append(f"phase {len(ph.rows)} {len(ph.sibs)}")
        for r in ph.rows:
            out.append(f"row {len(r)} " + " ".join(map(h16, r)))
        out.extend("sibling " + s for s in ph.sibs)
    out.append("end")
    return "\n".join(out) + "\n"


def load_seed(path):
    with (gzip.open(path, "rt") if path.endswith(".gz") else open(path)) as f:
        text = f.read()
    return text, parse(text)


def stem(path):
    b = os.path.basename(path)
    for ext in (".gz", ".proof"):
        b = b[:-len(ext)] if b.endswith(ext) else b
    return b


def fixture_text(path=FIXTURE):
    """The pinned Rust prover's proof that the Lean fixture embeds as `rustProofText`."""
    with open(path) as f:
        src = f.read()
    m = re.search(r'def rustProofText : String := "\n(.*?)"\n', src, re.S)
    if m is None or "\\" in m.group(1):
        raise SystemExit(f"{path}: no escape-free `rustProofText` literal")
    return m.group(1)


def seed_files(paths, outdir):
    """Plain copies of the seeds under <outdir>/seeds, the files both oracles read.

    Default: the Lean prover's test vector `fill` and the Rust fixture `field_div`. A seed path
    may be gzip-compressed."""
    d = os.path.join(outdir, "seeds")
    os.makedirs(d, exist_ok=True)
    texts = {}
    if not paths:
        with gzip.open(VECTOR, "rt") as f:
            texts["fill"] = f.read()
        texts["field_div"] = fixture_text()
    for p in paths or []:
        s = stem(p)
        if s in texts:
            raise SystemExit(f"two seeds named {s}")
        texts[s] = load_seed(p)[0]
    out = []
    for s, text in sorted(texts.items()):
        path = os.path.join(d, s + ".proof")
        with open(path, "w") as f:
            f.write(text)
        out.append(path)
    return out


# ---------------------------------------------------------------------------------------------
# Mutation catalog.  A mutation is fn(proof, rng, ctx) -> bool, mutating a clone in place;
# False means "not applicable to this seed".  Deterministic in (seed, rng).
# ---------------------------------------------------------------------------------------------

CATALOG = {}   # name -> (family, fn, description)
DESCR = {}     # family-level descriptions for the README table


def mut(name, descr=""):
    def deco(fn):
        CATALOG[name] = (name.split(".")[0], fn, descr)
        return fn
    return deco


def limb_value(kind, old, rng):
    if kind == "zero":
        return 0
    if kind == "one":
        return 1
    if kind == "small":
        return rng.randint(2, 255)
    if kind == "ones":
        return M64
    if kind == "rand":
        return rng.getrandbits(64)
    if kind == "flip":
        return old ^ (1 << rng.randrange(64))
    if kind == "inc":
        return (old + 1) & M64
    if kind == "dec":
        return (old - 1) & M64
    raise ValueError(kind)


def rand_digest(rng):
    return "%064x" % rng.getrandbits(256)


ZERO_DIGEST = "0" * 64

# --- statement: public input -----------------------------------------------------------------

for _e in (0, 1):
    for _c in (0, 1, 2):
        for _k in ("zero", "one", "small", "ones", "rand", "flip"):
            def _f(p, rng, ctx, e=_e, c=_c, k=_k):
                i = 3 * e + c
                new = limb_value(k, p.pub[i], rng)
                if new == p.pub[i]:
                    return False
                p.pub[i] = new
                return True
            mut(f"pub.e{_e}.c{_c}.{_k}", f"public element {_e}, limb c{_c} := {_k}")(_f)


@mut("pub.swap", "swap the two public-input elements")
def _(p, rng, ctx):
    p.pub = p.pub[3:] + p.pub[:3]
    return True


@mut("pub.copy01", "public element 1 := element 0")
def _(p, rng, ctx):
    p.pub[3:] = p.pub[:3]
    return True


@mut("pub.copy10", "public element 0 := element 1")
def _(p, rng, ctx):
    p.pub[:3] = p.pub[3:]
    return True


# --- statement: program ----------------------------------------------------------------------

def operand_slots(op):
    k = op[0]
    if k in ("xor", "mul", "jump", "deref"):
        return [1, 2, 3]
    if k == "set":
        return [1]
    if k == "blake2s":
        return [1, 2, 3, 4, 5, 6, 7]
    return []


def pick_op(p, rng, pred=lambda op: True):
    idx = [i for i, op in enumerate(p.prog) if pred(op)]
    return rng.choice(idx) if idx else None


def edit_operand(p, rng, f):
    i = pick_op(p, rng, lambda op: operand_slots(op))
    if i is None:
        return False
    op = list(p.prog[i])
    j = rng.choice(operand_slots(op))
    new = f(op[j], rng)
    if new is None:
        return False
    op[j] = new
    p.prog[i] = tuple(op)
    return True


@mut("prog.operand.inc", "a random operand exponent + 1")
def _(p, rng, ctx):
    return edit_operand(p, rng, lambda s, r: str(int(s.replace("_", "")) + 1))


@mut("prog.operand.dec", "a random operand exponent - 1")
def _(p, rng, ctx):
    return edit_operand(p, rng, lambda s, r: str(int(s.replace("_", "")) - 1)
                        if int(s.replace("_", "")) > 0 else None)


@mut("prog.operand.rand", "a random operand := random small exponent")
def _(p, rng, ctx):
    return edit_operand(p, rng, lambda s, r: str(r.randrange(64)))


@mut("prog.operand.big", "a random operand := exponent >= 2^32 (not a u32 on the Rust side)")
def _(p, rng, ctx):
    return edit_operand(p, rng, lambda s, r: str((1 << 32) + r.randrange(1 << 20)))


@mut("text.operand.alias", "operand j written as j + (2^64-1): the same g^j (text alias)")
def _(p, rng, ctx):
    return edit_operand(p, rng, lambda s, r: str(int(s.replace("_", "")) + ORD_G))


@mut("text.operand.leadzero", "operand written with a leading 0 (text alias)")
def _(p, rng, ctx):
    return edit_operand(p, rng, lambda s, r: "0" + s)


@mut("text.operand.underscore", "operand with a `_` digit separator (Lean toNat? alias)")
def _(p, rng, ctx):
    return edit_operand(p, rng, lambda s, r: s[0] + "_" + s[1:] if len(s) >= 2 else None)


@mut("text.limb.17digits", "a public limb written with 17 hex digits (high digit dropped mod 2^64)")
def _(p, rng, ctx):
    # The structure keeps ints < 2^64, so this one is applied to the text (apply_mutation).
    ctx.setdefault("textpatch", []).append("limb17")
    return True


@mut("prog.opcode.xormul", "swap xor <-> mul on one op")
def _(p, rng, ctx):
    i = pick_op(p, rng, lambda op: op[0] in ("xor", "mul"))
    if i is None:
        return False
    op = p.prog[i]
    p.prog[i] = ("mul" if op[0] == "xor" else "xor",) + op[1:]
    return True


@mut("prog.deref.mode", "change the mode of one deref")
def _(p, rng, ctx):
    i = pick_op(p, rng, lambda op: op[0] == "deref")
    if i is None:
        return False
    op = p.prog[i]
    p.prog[i] = op[:4] + (rng.choice([m for m in ("cell", "pc", "fp") if m != op[4]]),)
    return True


for _c in (0, 1, 2):
    def _f(p, rng, ctx, c=_c):
        i = pick_op(p, rng, lambda op: op[0] == "set")
        if i is None:
            return False
        op = list(p.prog[i])
        op[2 + c] = h16(rng.getrandbits(64))
        p.prog[i] = tuple(op)
        return True
    mut(f"prog.set.c{_c}", f"one set immediate: limb c{_c} := random")(_f)


@mut("prog.op.swap", "swap two ops")
def _(p, rng, ctx):
    if len(p.prog) < 2:
        return False
    i, j = rng.sample(range(len(p.prog)), 2)
    if p.prog[i] == p.prog[j]:
        return False
    p.prog[i], p.prog[j] = p.prog[j], p.prog[i]
    return True


@mut("prog.op.nop", "replace one op by xor 0 0 0")
def _(p, rng, ctx):
    i = pick_op(p, rng, lambda op: op != ("xor", "0", "0", "0"))
    if i is None:
        return False
    p.prog[i] = ("xor", "0", "0", "0")
    return True


@mut("prog.append1", "append one xor 0 0 0 (length 2^k + 1)")
def _(p, rng, ctx):
    p.prog.append(("xor", "0", "0", "0"))
    return True


@mut("prog.drop_last", "remove the last op (length 2^k - 1)")
def _(p, rng, ctx):
    p.prog.pop()
    return True


@mut("prog.double_nop", "pad the program to twice its length with xor 0 0 0")
def _(p, rng, ctx):
    p.prog.extend([("xor", "0", "0", "0")] * len(p.prog))
    return True


@mut("prog.double_copy", "the program twice")
def _(p, rng, ctx):
    p.prog.extend(list(p.prog))
    return True


@mut("prog.double_tail", "pad to twice the length with copies of the last op")
def _(p, rng, ctx):
    p.prog.extend([p.prog[-1]] * len(p.prog))
    return True


@mut("prog.halve", "keep the first half of the program")
def _(p, rng, ctx):
    if len(p.prog) < 2:
        return False
    del p.prog[len(p.prog) // 2:]
    return True


@mut("rate.inc", "header rate + 1 (the stream head carries the rate too)")
def _(p, rng, ctx):
    p.rate = str(int(p.rate.replace("_", "")) + 1)
    return True


@mut("rate.zero", "header rate := 0")
def _(p, rng, ctx):
    if p.rate == "0":
        return False
    p.rate = "0"
    return True


@mut("rate.huge", "header rate := 2^64 (not a u64)")
def _(p, rng, ctx):
    p.rate = str(1 << 64)
    return True


@mut("text.tag", "header tag := other")
def _(p, rng, ctx):
    p.tag = "fuzzed"
    return True


# --- stream ----------------------------------------------------------------------------------

def rand_scalar(rng):
    return (rng.getrandbits(64), rng.getrandbits(64), rng.getrandbits(64))


for _n in (1, 2, 3):
    def _fz(p, rng, ctx, n=_n):
        p.stream.extend([(0, 0, 0)] * n)
        return True

    def _fr(p, rng, ctx, n=_n):
        p.stream.extend(rand_scalar(rng) for _ in range(n))
        return True
    mut(f"stream.append.zero.{_n}", f"append {_n} zero scalars")(_fz)
    mut(f"stream.append.rand.{_n}", f"append {_n} random scalars")(_fr)


@mut("stream.append.copylast", "append a copy of the last scalar")
def _(p, rng, ctx):
    p.stream.append(p.stream[-1])
    return True


@mut("stream.drop_last", "drop the last scalar")
def _(p, rng, ctx):
    p.stream.pop()
    return True


@mut("stream.drop_last2", "drop the last two scalars")
def _(p, rng, ctx):
    del p.stream[-2:]
    return True


@mut("stream.head.insert.zero", "insert a zero scalar at the head")
def _(p, rng, ctx):
    p.stream.insert(0, (0, 0, 0))
    return True


@mut("stream.head.insert.rand", "insert a random base-field scalar (c1 = c2 = 0) at the head")
def _(p, rng, ctx):
    p.stream.insert(0, (rng.randrange(64), 0, 0))
    return True


@mut("stream.head.delete", "delete the first scalar")
def _(p, rng, ctx):
    del p.stream[0]
    return True


HEAD = 10  # 8 announced sizes/rate, then the setup digest as two scalars
for _i in range(HEAD):
    for _c, _k in ((0, "inc"), (0, "dec"), (0, "flip"), (1, "one"), (2, "one"), (1, "ones"),
                   (2, "ones")):
        def _f(p, rng, ctx, i=_i, c=_c, k=_k):
            if i >= len(p.stream):
                return False
            s = list(p.stream[i])
            new = limb_value(k, s[c], rng)
            if new == s[c]:
                return False
            s[c] = new
            p.stream[i] = tuple(s)
            return True
        mut(f"stream.h{_i}.c{_c}.{_k}", f"stream head scalar {_i}: limb c{_c} := {_k}")(_f)


def _region(p, rng, where):
    n = len(p.stream)
    if where == "tail":
        return rng.randrange(max(0, n - 5), n)
    return rng.randrange(n)


for _w in ("tail", "rand"):
    for _c in (0, 1, 2):
        def _f(p, rng, ctx, w=_w, c=_c):
            i = _region(p, rng, w)
            s = list(p.stream[i])
            s[c] ^= 1 << rng.randrange(64)
            p.stream[i] = tuple(s)
            return True
        mut(f"stream.{_w}.c{_c}.flip", f"flip one bit of limb c{_c} of a {_w} scalar")(_f)


for _c in (1, 2):
    for _k in ("one", "rand"):
        def _f(p, rng, ctx, c=_c, k=_k):
            idx = [i for i, s in enumerate(p.stream) if s[1] == 0 and s[2] == 0]
            if not idx:
                return False
            i = rng.choice(idx)
            s = list(p.stream[i])
            s[c] = 1 if k == "one" else (rng.getrandbits(64) | 1)
            p.stream[i] = tuple(s)
            return True
        mut(f"stream.base.c{_c}.{_k}",
            f"a scalar with c1 = c2 = 0 (a base-field value): limb c{_c} := {_k}")(_f)


@mut("stream.ext.c2.zero", "a scalar with c2 != 0: c2 := 0")
def _(p, rng, ctx):
    idx = [i for i, s in enumerate(p.stream) if s[2] != 0]
    if not idx:
        return False
    i = rng.choice(idx)
    p.stream[i] = p.stream[i][:2] + (0,)
    return True


@mut("stream.swap.adj", "swap two adjacent scalars")
def _(p, rng, ctx):
    i = rng.randrange(len(p.stream) - 1)
    if p.stream[i] == p.stream[i + 1]:
        return False
    p.stream[i], p.stream[i + 1] = p.stream[i + 1], p.stream[i]
    return True


# --- Merkle hints: phases --------------------------------------------------------------------

def junk_phase(p, rng):
    src = rng.choice(p.merkle) if p.merkle else Phase([(0,)], [])
    w = len(src.rows[0]) if src.rows else 1
    rows = [tuple(rng.getrandbits(64) for _ in range(w)) for _ in range(rng.randint(1, 4))]
    return Phase(rows, [rand_digest(rng) for _ in range(rng.randint(1, 8))])


@mut("merkle.phase.append_empty", "append a phase with no rows and no siblings")
def _(p, rng, ctx):
    p.merkle.append(Phase([], []))
    return True


@mut("merkle.phase.prepend_empty", "prepend a phase with no rows and no siblings")
def _(p, rng, ctx):
    p.merkle.insert(0, Phase([], []))
    return True


@mut("merkle.phase.append_junk", "append a phase of random rows and siblings")
def _(p, rng, ctx):
    p.merkle.append(junk_phase(p, rng))
    return True


@mut("merkle.phase.append_copy", "append a copy of the last phase")
def _(p, rng, ctx):
    if not p.merkle:
        return False
    p.merkle.append(p.merkle[-1].clone())
    return True


@mut("merkle.phase.drop_last", "drop the last phase")
def _(p, rng, ctx):
    if not p.merkle:
        return False
    p.merkle.pop()
    return True


@mut("merkle.phase.drop_first", "drop the first phase")
def _(p, rng, ctx):
    if not p.merkle:
        return False
    p.merkle.pop(0)
    return True


@mut("merkle.phase.swap", "swap two adjacent phases")
def _(p, rng, ctx):
    if len(p.merkle) < 2:
        return False
    i = rng.randrange(len(p.merkle) - 1)
    p.merkle[i], p.merkle[i + 1] = p.merkle[i + 1], p.merkle[i]
    return True


@mut("merkle.phase.reverse", "reverse the order of the phases")
def _(p, rng, ctx):
    if len(p.merkle) < 2:
        return False
    p.merkle.reverse()
    return True


@mut("merkle.phase.split", "split one phase into two (rows and siblings cut at their middles)")
def _(p, rng, ctx):
    idx = [i for i, ph in enumerate(p.merkle) if len(ph.rows) >= 2]
    if not idx:
        return False
    i = rng.choice(idx)
    ph = p.merkle[i]
    r, s = len(ph.rows) // 2, len(ph.sibs) // 2
    p.merkle[i:i + 1] = [Phase(ph.rows[:r], ph.sibs[:s]), Phase(ph.rows[r:], ph.sibs[s:])]
    return True


@mut("merkle.phase.merge", "merge two adjacent phases into one")
def _(p, rng, ctx):
    if len(p.merkle) < 2:
        return False
    i = rng.randrange(len(p.merkle) - 1)
    a, b = p.merkle[i], p.merkle[i + 1]
    p.merkle[i:i + 2] = [Phase(a.rows + b.rows, a.sibs + b.sibs)]
    return True


# --- Merkle hints: rows and siblings within a phase -------------------------------------------

def pick_phase(p, rng, pred=lambda ph: True):
    idx = [i for i, ph in enumerate(p.merkle) if pred(ph)]
    return p.merkle[rng.choice(idx)] if idx else None


def phase_op(pred):
    def deco(fn):
        def g(p, rng, ctx):
            ph = pick_phase(p, rng, pred)
            if ph is None:
                return False
            return fn(ph, rng, p)
        return g
    return deco


def has_rows(n):
    return lambda ph: len(ph.rows) >= n


def has_sibs(n):
    return lambda ph: len(ph.sibs) >= n


def reg_phase(name, descr, pred):
    def deco(fn):
        mut(name, descr)(phase_op(pred)(fn))
        return fn
    return deco


@reg_phase("merkle.rows.dup", "duplicate one row in place", has_rows(1))
def _(ph, rng, p):
    i = rng.randrange(len(ph.rows))
    ph.rows.insert(i, ph.rows[i])
    return True


@reg_phase("merkle.rows.dup_last", "append a copy of the last row", has_rows(1))
def _(ph, rng, p):
    ph.rows.append(ph.rows[-1])
    return True


@reg_phase("merkle.rows.drop", "drop one row", has_rows(1))
def _(ph, rng, p):
    del ph.rows[rng.randrange(len(ph.rows))]
    return True


@reg_phase("merkle.rows.drop_last", "drop the last row", has_rows(1))
def _(ph, rng, p):
    ph.rows.pop()
    return True


@reg_phase("merkle.rows.swap", "swap two rows", has_rows(2))
def _(ph, rng, p):
    i, j = rng.sample(range(len(ph.rows)), 2)
    if ph.rows[i] == ph.rows[j]:
        return False
    ph.rows[i], ph.rows[j] = ph.rows[j], ph.rows[i]
    return True


@reg_phase("merkle.rows.swap_adj", "swap two adjacent rows", has_rows(2))
def _(ph, rng, p):
    i = rng.randrange(len(ph.rows) - 1)
    if ph.rows[i] == ph.rows[i + 1]:
        return False
    ph.rows[i], ph.rows[i + 1] = ph.rows[i + 1], ph.rows[i]
    return True


@reg_phase("merkle.rows.reverse", "reverse the rows of a phase", has_rows(2))
def _(ph, rng, p):
    ph.rows.reverse()
    return True


@reg_phase("merkle.rows.shuffle", "shuffle the rows of a phase", has_rows(2))
def _(ph, rng, p):
    rng.shuffle(ph.rows)
    return True


@reg_phase("merkle.rows.empty", "remove every row of a phase", has_rows(1))
def _(ph, rng, p):
    ph.rows.clear()
    return True


@reg_phase("merkle.rows.append_zero", "append an all-zero row of the phase's width", has_rows(1))
def _(ph, rng, p):
    ph.rows.append((0,) * len(ph.rows[-1]))
    return True


@reg_phase("merkle.rows.append_rand", "append a random row of the phase's width", has_rows(1))
def _(ph, rng, p):
    ph.rows.append(tuple(rng.getrandbits(64) for _ in ph.rows[-1]))
    return True


@mut("merkle.rows.move_next", "move the last row of a phase to the head of the next phase")
def _(p, rng, ctx):
    idx = [i for i in range(len(p.merkle) - 1) if p.merkle[i].rows]
    if not idx:
        return False
    i = rng.choice(idx)
    p.merkle[i + 1].rows.insert(0, p.merkle[i].rows.pop())
    return True


@reg_phase("merkle.sibs.dup", "duplicate one sibling in place", has_sibs(1))
def _(ph, rng, p):
    i = rng.randrange(len(ph.sibs))
    ph.sibs.insert(i, ph.sibs[i])
    return True


@reg_phase("merkle.sibs.drop", "drop one sibling", has_sibs(1))
def _(ph, rng, p):
    del ph.sibs[rng.randrange(len(ph.sibs))]
    return True


@reg_phase("merkle.sibs.drop_last", "drop the last sibling", has_sibs(1))
def _(ph, rng, p):
    ph.sibs.pop()
    return True


@reg_phase("merkle.sibs.append_zero", "append an all-zero sibling", lambda ph: True)
def _(ph, rng, p):
    ph.sibs.append(ZERO_DIGEST)
    return True


@reg_phase("merkle.sibs.append_rand", "append a random sibling", lambda ph: True)
def _(ph, rng, p):
    ph.sibs.append(rand_digest(rng))
    return True


@reg_phase("merkle.sibs.append_copy", "append a copy of the last sibling", has_sibs(1))
def _(ph, rng, p):
    ph.sibs.append(ph.sibs[-1])
    return True


@reg_phase("merkle.sibs.prepend_zero", "prepend an all-zero sibling", lambda ph: True)
def _(ph, rng, p):
    ph.sibs.insert(0, ZERO_DIGEST)
    return True


@reg_phase("merkle.sibs.swap", "swap two siblings", has_sibs(2))
def _(ph, rng, p):
    i, j = rng.sample(range(len(ph.sibs)), 2)
    if ph.sibs[i] == ph.sibs[j]:
        return False
    ph.sibs[i], ph.sibs[j] = ph.sibs[j], ph.sibs[i]
    return True


@reg_phase("merkle.sibs.swap_adj", "swap two adjacent siblings", has_sibs(2))
def _(ph, rng, p):
    i = rng.randrange(len(ph.sibs) - 1)
    if ph.sibs[i] == ph.sibs[i + 1]:
        return False
    ph.sibs[i], ph.sibs[i + 1] = ph.sibs[i + 1], ph.sibs[i]
    return True


@reg_phase("merkle.sibs.empty", "remove every sibling of a phase", has_sibs(1))
def _(ph, rng, p):
    ph.sibs.clear()
    return True


@reg_phase("merkle.sibs.flip", "flip one bit of one sibling", has_sibs(1))
def _(ph, rng, p):
    i = rng.randrange(len(ph.sibs))
    v = int(ph.sibs[i], 16) ^ (1 << rng.randrange(256))
    ph.sibs[i] = "%064x" % v
    return True


@mut("merkle.sibs.move_next", "move the last sibling of a phase to the head of the next phase")
def _(p, rng, ctx):
    idx = [i for i in range(len(p.merkle) - 1) if p.merkle[i].sibs]
    if not idx:
        return False
    i = rng.choice(idx)
    p.merkle[i + 1].sibs.insert(0, p.merkle[i].sibs.pop())
    return True


# --- Merkle hints: the width of a row (one row, or every row of a phase) ----------------------

def w_prepend_zero(r, rng):
    return (0,) + r


def w_append_zero(r, rng):
    return r + (0,)


def w_prepend_rand(r, rng):
    return (rng.getrandbits(64) | 1,) + r


def w_append_rand(r, rng):
    return r + (rng.getrandbits(64) | 1,)


def w_strip_leading_zero(r, rng):
    k = 0
    while k < len(r) and r[k] == 0:
        k += 1
    return r[k:] if k else None


def w_strip_trailing_zero(r, rng):
    k = len(r)
    while k > 0 and r[k - 1] == 0:
        k -= 1
    return r[:k] if k < len(r) else None


def w_strip_trailing(r, rng):
    return r[:-1] if r else None


def w_strip_leading(r, rng):
    return r[1:] if r else None


def w_empty(r, rng):
    return () if r else None


def w_flip(r, rng):
    if not r:
        return None
    i = rng.randrange(len(r))
    return r[:i] + (r[i] ^ (1 << rng.randrange(64)),) + r[i + 1:]


def w_top_ones(r, rng):
    if not r:
        return None
    i = rng.randrange(len(r))
    return r[:i] + (r[i] | (1 << 63),) + r[i + 1:]


WIDTH = {
    "prepend_zero": (w_prepend_zero, "prepend a zero word"),
    "append_zero": (w_append_zero, "append a zero word"),
    "prepend_rand": (w_prepend_rand, "prepend a nonzero word"),
    "append_rand": (w_append_rand, "append a nonzero word"),
    "strip_leading_zero": (w_strip_leading_zero, "strip the leading zero words"),
    "strip_trailing_zero": (w_strip_trailing_zero, "strip the trailing zero words"),
    "strip_leading": (w_strip_leading, "strip the first word"),
    "strip_trailing": (w_strip_trailing, "strip the last word"),
    "empty": (w_empty, "make the row empty"),
    "flip": (w_flip, "flip a bit of one word"),
    "topbit": (w_top_ones, "set the top bit of one word"),
}

for _k, (_fn, _d) in WIDTH.items():
    def _one(p, rng, ctx, fn=_fn):
        cand = [(i, j) for i, ph in enumerate(p.merkle) for j in range(len(ph.rows))]
        if not cand:
            return False
        # Prefer a row the edit applies to.
        rng.shuffle(cand)
        for i, j in cand[:64]:
            new = fn(p.merkle[i].rows[j], rng)
            if new is not None:
                p.merkle[i].rows[j] = new
                return True
        return False

    def _all(p, rng, ctx, fn=_fn):
        ph = pick_phase(p, rng, has_rows(1))
        if ph is None:
            return False
        new = [fn(r, rng) for r in ph.rows]
        if any(r is None for r in new):
            return False
        ph.rows[:] = new
        return True
    mut(f"merkle.row.{_k}", f"one row: {_d}")(_one)
    if _k not in ("flip", "topbit"):
        mut(f"merkle.rowsall.{_k}", f"every row of one phase: {_d}")(_all)


# --- havoc -----------------------------------------------------------------------------------

@mut("havoc", "2-4 random catalog mutations composed (no text.*, rate.*, or self cross)")
def _(p, rng, ctx):
    # text.* and rate.* change only what both loaders ignore or read alike; a self cross undoes
    # an earlier cross: either would turn a no-op chain into a spurious MALLEABLE.
    names = sorted(n for n in CATALOG
                   if n != "havoc" and not n.startswith(("text.", "rate.")))
    names += sorted(n for n in ctx.get("cross", {}) if not n.endswith("@" + ctx.get("self", "")))
    k = rng.randint(2, 4)
    done = 0
    chain = ctx.setdefault("chain", [])
    for _ in range(20):
        if done == k:
            break
        n = rng.choice(names)
        fn = CATALOG[n][1] if n in CATALOG else ctx["cross"][n]
        if fn(p, rng, ctx):
            chain.append(n)
            done += 1
    return done > 0


# --- cross-statement (built per seed set) ----------------------------------------------------

def cross_mutations(seeds):
    """name -> fn for every ordered pair: cross.<what>@<other seed stem>."""
    out = {}
    for path, (_, other) in seeds.items():
        s = stem(path)

        def prog(p, rng, ctx, o=other):
            if p.prog == o.prog:
                return False
            p.prog = list(o.prog)
            return True

        def pub(p, rng, ctx, o=other):
            if p.pub == o.pub:
                return False
            p.pub = list(o.pub)
            return True

        def both(p, rng, ctx, o=other):
            a, b = prog(p, rng, ctx, o), pub(p, rng, ctx, o)
            return a or b
        out[f"cross.program@{s}"] = prog
        out[f"cross.public@{s}"] = pub
        out[f"cross.both@{s}"] = both
    return out


def apply_mutation(seed_proof, name, rseed, cross, self_stem=""):
    """(text or None, chain).  Deterministic in (seed, name, rseed)."""
    rng = random.Random(rseed)
    p = seed_proof.clone()
    ctx = {"cross": cross, "self": self_stem}
    fn = CATALOG[name][1] if name in CATALOG else cross.get(name)
    if fn is None:
        raise KeyError(f"unknown mutation {name}")
    if not fn(p, rng, ctx):
        return None, ctx.get("chain", [])
    text = dump(p)
    if "limb17" in ctx.get("textpatch", []):
        # "public 0000..." -> first limb gets a leading extra hex digit 1 (mod 2^64: same value).
        text = text.replace("\npublic ", "\npublic 1", 1)
    return text, ctx.get("chain", [])


def family(name):
    if name.startswith("merkle."):
        return "merkle." + name.split(".")[1]
    return name.split(".")[0]


# ---------------------------------------------------------------------------------------------
# Oracles
# ---------------------------------------------------------------------------------------------


class Worker:
    def __init__(self, name, argv, logdir):
        self.name = name
        self.argv = argv
        self.logdir = logdir
        self.gen = 0
        self.restarts = 0
        self.start()

    def start(self):
        self.gen += 1
        self.err = open(os.path.join(self.logdir, f"{self.name}.stderr"), "a")
        self.p = subprocess.Popen(SCOPE + self.argv, stdin=subprocess.PIPE,
                                  stdout=subprocess.PIPE, stderr=self.err, text=True, bufsize=1)
        self.q = queue.Queue()
        threading.Thread(target=self._reader, args=(self.p, self.q), daemon=True).start()

    @staticmethod
    def _reader(p, q):
        for line in p.stdout:
            q.put(line.rstrip("\n"))
        q.put(None)

    def stop(self):
        try:
            self.p.stdin.close()
        except Exception:
            pass
        try:
            self.p.wait(timeout=5)
        except Exception:
            self.p.kill()
        self.err.close()

    def restart(self):
        try:
            self.p.kill()
            self.p.wait(timeout=10)
        except Exception:
            pass
        self.err.close()
        self.restarts += 1
        self.start()

    def send(self, path):
        try:
            self.p.stdin.write(path + "\n")
            self.p.stdin.flush()
            return True
        except Exception:
            return False

    def recv(self, path, deadline):
        """('OK', fields) | ('CRASH', why) | ('HANG', None)."""
        while True:
            left = deadline - time.monotonic()
            if left <= 0:
                return "HANG", None
            try:
                line = self.q.get(timeout=left)
            except queue.Empty:
                return "HANG", None
            if line is None:
                rc = self.p.wait()
                return "CRASH", f"exit {rc}"
            f = line.split("\t")
            if len(f) >= 3 and f[0] == path:
                return "OK", f
            # stray output (e.g. a log line on stdout): skip it


def scope_argv(binary):
    return [binary, "serve"]


def check_once(path, lean_bin, rust_bin, timeout):
    out = {}
    for name, b in (("lean", lean_bin), ("rust", rust_bin)):
        if not b:
            continue
        try:
            r = subprocess.run(SCOPE + [b, "serve"], input=path + "\n", capture_output=True,
                               text=True, timeout=timeout)
            out[name] = (r.stdout.strip() or f"<no output, exit {r.returncode}>",
                         r.stderr.strip()[-2000:])
        except subprocess.TimeoutExpired:
            out[name] = ("<HANG>", "")
    return out


# ---------------------------------------------------------------------------------------------
# Classification and bookkeeping
# ---------------------------------------------------------------------------------------------

CLASSES = ["DIVERGENCE", "PANIC", "CRASH", "HANG", "INCONSISTENT", "MALLEABLE",
           "PARSEFAIL-ASYM", "REJECT", "NOOP", "N/A"]


def classify(lv, rv):
    if "CRASH" in (lv, rv):
        return "CRASH"
    if "HANG" in (lv, rv):
        return "HANG"
    if rv == "PANIC":
        return "PANIC"
    if lv == "INCONSISTENT":
        return "INCONSISTENT"
    if rv is None:  # Lean-only mode
        return "MALLEABLE" if lv == "ACCEPT" else ("REJECT" if lv in ("REJECT", "PARSEFAIL")
                                                   else "DIVERGENCE")
    if (lv == "ACCEPT") != (rv == "ACCEPT"):
        other = rv if lv == "ACCEPT" else lv
        return "PARSEFAIL-ASYM" if other == "PARSEFAIL" else "DIVERGENCE"
    if lv == "ACCEPT":
        return "MALLEABLE"
    if (lv == "PARSEFAIL") != (rv == "PARSEFAIL"):
        return "PARSEFAIL-ASYM"
    return "REJECT"


# Mutations that only re-spell the proof (README.md, Findings): the two loaders may read such a
# text differently, or both read it as the seed's proof.
SPELLING = ("text.", "rate.")


def needs_look(cls, name, lv, rv):
    """Whether a mutant's class is one the loaders do not explain."""
    if cls in ("DIVERGENCE", "PANIC", "CRASH", "HANG", "INCONSISTENT"):
        return True
    return (cls in ("MALLEABLE", "PARSEFAIL-ASYM") and "ACCEPT" in (lv, rv)
            and not name.startswith(SPELLING))


KEEP_FILES = {"DIVERGENCE": 20, "PANIC": 20, "CRASH": 20, "HANG": 20, "INCONSISTENT": 20,
              "MALLEABLE": 1, "PARSEFAIL-ASYM": 1}
LOG_LINES = 50


def norm_detail(s):
    s = re.sub(r"`[^`]*`", "`_`", s or "")
    s = re.sub(r"0x[0-9a-fA-F]+|\b[0-9a-f]{8,}\b|\d+", "#", s)
    return s[:100]


class Book:
    def __init__(self, outdir, seeds):
        self.outdir = outdir
        self.seeds = seeds                        # every seed path, for a cross mutation's regen
        self.lock = threading.Lock()
        self.look = Counter()                     # class -> mutants needing a look
        self.per_mut = defaultdict(Counter)       # name -> class -> n
        self.pairs = defaultdict(Counter)         # name -> "lv/rv" -> n
        self.stages = Counter()                   # (lean stage, rust detail) -> n
        self.kept = Counter()                     # (class, name) -> files kept
        self.logged = Counter()                   # (class, name) -> lines logged
        self.total = 0
        self.t0 = time.monotonic()
        self.fjson = open(os.path.join(outdir, "findings.jsonl"), "a")
        os.makedirs(os.path.join(outdir, "findings"), exist_ok=True)

    def record(self, job, path, lres, rres):
        lv = lres[1][1] if lres[0] == "OK" else lres[0]
        rv = None if rres is None else (rres[1][1] if rres[0] == "OK" else rres[0])
        cls = classify(lv, rv)
        ls = lres[1][2] if lres[0] == "OK" else lres[0]
        rs = None if rres is None else (rres[1][2] if rres[0] == "OK" else rres[0])
        name = job["mutation"]
        with self.lock:
            self.total += 1
            self.per_mut[name][cls] += 1
            if needs_look(cls, name, lv, rv):
                self.look[cls] += 1
            self.pairs[name][f"{lv}/{rv}"] += 1
            self.stages[(ls.split(";")[0], norm_detail(rs))] += 1
            keep = None
            if cls in KEEP_FILES and self.kept[(cls, name)] < KEEP_FILES[cls]:
                self.kept[(cls, name)] += 1
                keep = os.path.join(self.outdir, "findings", f"{cls}-{os.path.basename(path)}")
            log = cls not in ("REJECT", "NOOP") and self.logged[(cls, name)] < LOG_LINES
            if log:
                self.logged[(cls, name)] += 1
        if keep:
            shutil.move(path, keep)
        else:
            try:
                os.remove(path)
            except FileNotFoundError:
                pass
        if log:
            cross = any(n.startswith("cross.") for n in [name] + job.get("chain", []))
            regen = (f"python3 -I {HERE}/fuzz.py mutate --seed {job['seed']} --mutation {name} "
                     f"--rng {job['rng']}" + (" --seeds " + " ".join(self.seeds) if cross else ""))
            rec = dict(time=time.strftime("%Y-%m-%dT%H:%M:%S"), cls=cls, seed=job["seed"],
                       mutation=name, rng=job["rng"], chain=job.get("chain", []),
                       lean="\t".join(lres[1]) if lres[0] == "OK" else f"{lres[0]} {lres[1]}",
                       rust=(None if rres is None else
                             "\t".join(rres[1]) if rres[0] == "OK" else f"{rres[0]} {rres[1]}"),
                       file=keep, regen=regen)
            with self.lock:
                self.fjson.write(json.dumps(rec) + "\n")
                self.fjson.flush()
        return cls

    def skip(self, name, cls):
        with self.lock:
            self.per_mut[name][cls] += 1

    def table(self, by_family=True):
        rows = defaultdict(Counter)
        with self.lock:
            for n, c in self.per_mut.items():
                rows[family(n) if by_family else n].update(c)
        cols = [c for c in CLASSES if any(r[c] for r in rows.values())]
        w = max([len(k) for k in rows] + [8])
        out = [f"{'family':<{w}} " + " ".join(f"{c:>9}" for c in cols)]
        for k in sorted(rows):
            out.append(f"{k:<{w}} " + " ".join(f"{rows[k][c]:>9}" for c in cols))
        tot = Counter()
        for r in rows.values():
            tot.update(r)
        out.append(f"{'TOTAL':<{w}} " + " ".join(f"{tot[c]:>9}" for c in cols))
        el = time.monotonic() - self.t0
        out.append(f"{self.total} mutants checked in {el:.0f} s: {self.total / max(el, 1e-9):.1f}/s")
        look = ", ".join(f"{c} {n}" for c, n in sorted(self.look.items())) or "none"
        out.append(f"needing a look: {look}")
        return "\n".join(out)

    def save_summary(self, extra):
        extra = dict(extra)
        for k in ("lean", "rust"):
            b = extra.get(k + "_bin")
            if b and os.path.exists(b):
                st = os.stat(b)
                extra[k + "_bin_mtime"] = time.strftime("%Y-%m-%dT%H:%M:%S", time.gmtime(st.st_mtime))
        with self.lock:
            data = dict(extra, total=self.total, seconds=time.monotonic() - self.t0,
                        needing_a_look=dict(self.look),
                        per_mutation={n: dict(c) for n, c in sorted(self.per_mut.items())},
                        verdict_pairs={n: dict(c) for n, c in sorted(self.pairs.items())},
                        stage_pairs=[dict(lean=a, rust=b, n=k)
                                     for (a, b), k in self.stages.most_common()])
        base = os.path.join(self.outdir, f"summary-{extra.get('mode', 'run')}")
        with open(base + ".json", "w") as f:
            json.dump(data, f, indent=1)
        with open(base + ".txt", "w") as f:
            f.write(self.table() + "\n\nPer mutation:\n" + self.table(by_family=False) + "\n")
            f.write("\nRejection-stage pairs (count, Lean stage || Rust detail):\n")
            for x in data["stage_pairs"]:
                f.write(f"{x['n']:>8} {x['lean']} || {x['rust']}\n")


# ---------------------------------------------------------------------------------------------
# Runner
# ---------------------------------------------------------------------------------------------


def load_seeds(paths):
    seeds = {}
    for p in sorted(set(os.path.abspath(x) for x in paths)):
        seeds[p] = load_seed(p)
    return seeds


class Runner:
    def __init__(self, args, jobs):
        self.args = args
        self.jobs = jobs  # iterator of job dicts (thread-safe through self.jlock)
        self.jlock = threading.Lock()
        self.stop = threading.Event()
        self.outdir = args.out
        self.work = os.path.join(self.outdir, "work")
        self.logdir = os.path.join(self.outdir, "logs")
        os.makedirs(self.work, exist_ok=True)
        os.makedirs(self.logdir, exist_ok=True)
        self.lean_only = args.lean_only
        self.seeds = load_seeds(args.seed_paths)
        self.book = Book(self.outdir, sorted(self.seeds))
        self.cross = cross_mutations(self.seeds)
        self.counter = 0

    def next_job(self):
        with self.jlock:
            try:
                j = next(self.jobs)
            except StopIteration:
                return None
            self.counter += 1
            j["n"] = self.counter
            return j

    def lane(self, k):
        lean = Worker(f"lean{k}", scope_argv(self.args.lean), self.logdir)
        rust = None if self.lean_only else Worker(f"rust{k}", scope_argv(self.args.rust),
                                                  self.logdir)
        try:
            while not self.stop.is_set():
                job = self.next_job()
                if job is None:
                    break
                seed_text, seed_proof = self.seeds[job["seed"]]
                text, chain = apply_mutation(seed_proof, job["mutation"], job["rng"], self.cross,
                                             stem(job["seed"]))
                job["chain"] = chain
                if text is None:
                    self.book.skip(job["mutation"], "N/A")
                    continue
                if text == seed_text:
                    self.book.skip(job["mutation"], "NOOP")
                    continue
                path = os.path.join(self.work, f"{stem(job['seed'])}--{job['mutation']}--"
                                               f"{job['rng']}.proof")
                with open(path, "w") as f:
                    f.write(text)
                deadline = time.monotonic() + self.args.timeout
                okl = lean.send(path)
                okr = True if rust is None else rust.send(path)
                lres = lean.recv(path, deadline) if okl else ("CRASH", "stdin closed")
                rres = None
                if rust is not None:
                    rres = rust.recv(path, deadline) if okr else ("CRASH", "stdin closed")
                self.book.record(job, path, lres, rres)
                if lres[0] != "OK":
                    lean.restart()
                if rres is not None and rres[0] != "OK":
                    rust.restart()
        finally:
            lean.stop()
            if rust:
                rust.stop()

    def run(self, minutes, extra):
        lanes = [threading.Thread(target=self.lane, args=(k,), daemon=True)
                 for k in range(self.args.workers)]
        for t in lanes:
            t.start()
        t_end = None if minutes is None else time.monotonic() + 60 * minutes
        last = time.monotonic()
        try:
            while any(t.is_alive() for t in lanes):
                time.sleep(1)
                now = time.monotonic()
                if t_end is not None and now >= t_end:
                    self.stop.set()
                if now - last >= self.args.report * 60:
                    last = now
                    print(time.strftime("%H:%M:%S"), "\n" + self.book.table(), flush=True)
                    self.book.save_summary(extra)
        except KeyboardInterrupt:
            self.stop.set()
            for t in lanes:
                t.join(timeout=60)
        print("\nFINAL\n" + self.book.table(), flush=True)
        self.book.save_summary(extra)
        print(f"summary: {self.outdir}/summary-{extra.get('mode', 'run')}.txt, "
              f"findings: {self.outdir}/findings.jsonl")
        return 1 if self.book.look else 0


def enumerate_jobs(seeds, cross, reps, rng, cross_limit):
    names = sorted(n for n in CATALOG if n != "havoc")
    order = sorted(seeds)
    for k, s in enumerate(order):
        # cross-statement partners: the next `cross_limit` seeds in sorted order
        partners = {stem(order[(k + d) % len(order)]) for d in range(1, len(order))
                    if d <= cross_limit}
        xs = sorted(n for n in cross if n.split("@", 1)[1] in partners)
        for name in names + xs:
            for r in range(reps):
                yield dict(seed=s, mutation=name, rng=rng * 1000 + r)


def random_jobs(seeds, cross, rng_seed, havoc_share):
    master = random.Random(rng_seed)
    fams = defaultdict(list)
    for n in CATALOG:
        if n != "havoc":
            fams[family(n)].append(n)
    for n in cross:
        fams["cross"].append(n)
    fam_names = sorted(fams)
    for f in fam_names:
        fams[f].sort()
    seed_list = sorted(seeds)
    while True:
        s = master.choice(seed_list)
        if master.random() < havoc_share:
            name = "havoc"
        else:
            name = master.choice(fams[master.choice(fam_names)])
            if name.startswith("cross.") and name.endswith("@" + stem(s)):
                continue
        yield dict(seed=s, mutation=name, rng=master.getrandbits(48))


def sanity(seeds, args):
    """Both oracles on the unmutated seeds, one serve process each."""
    print("seed sanity (both oracles on the unmutated seeds):")
    ok = True
    paths = "".join(s + "\n" for s in sorted(seeds))
    for name, b in (("lean", args.lean), ("rust", None if args.lean_only else args.rust)):
        if not b:
            continue
        r = subprocess.run(SCOPE + [b, "serve"], input=paths, capture_output=True, text=True,
                           timeout=args.timeout * len(seeds))
        lines = r.stdout.splitlines()
        acc = sum("\tACCEPT\t" in l for l in lines)
        print(f"  {name}: {acc}/{len(seeds)} seeds ACCEPT")
        for l in lines:
            if "\tACCEPT\t" not in l:
                print("   ", l)
        ok &= acc == len(seeds)
    return ok


# ---------------------------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------------------------


def classify_selftest():
    """The classes of the verdict pairs that decide what a campaign reports."""
    cases = [(("ACCEPT", "ACCEPT", "stream.drop_last"), "MALLEABLE", True),
             (("ACCEPT", "ACCEPT", "text.tag"), "MALLEABLE", False),
             (("ACCEPT", "REJECT", "pub.swap"), "DIVERGENCE", True),
             (("REJECT", "ACCEPT", "havoc"), "DIVERGENCE", True),
             (("INCONSISTENT", "REJECT", "havoc"), "INCONSISTENT", True),
             (("REJECT", "PANIC", "havoc"), "PANIC", True),
             (("ACCEPT", "PARSEFAIL", "text.operand.alias"), "PARSEFAIL-ASYM", False),
             (("ACCEPT", "PARSEFAIL", "prog.operand.big"), "PARSEFAIL-ASYM", True),
             (("PARSEFAIL", "REJECT", "pub.e0.c2.one"), "PARSEFAIL-ASYM", False),
             (("PARSEFAIL", "PARSEFAIL", "havoc"), "REJECT", False),
             (("REJECT", "REJECT", "havoc"), "REJECT", False)]
    bad = 0
    for (lv, rv, name), cls, look in cases:
        got = classify(lv, rv)
        if (got, needs_look(got, name, lv, rv)) != (cls, look):
            bad += 1
            print(f"  classify {lv}/{rv} on {name}: {got}, expected {cls}")
    return bad


def cmd_selftest(args):
    seeds = load_seeds(args.seed_paths)
    cross = cross_mutations(seeds)
    bad = classify_selftest()
    for path, (text, p) in seeds.items():
        rt = dump(p)
        same = rt == text
        bad += not same
        print(f"round-trip {'OK ' if same else 'FAIL'} {path} ({len(text)} bytes)")
        # Clone independence and determinism of every mutation.
        for name in sorted(CATALOG) + sorted(cross):
            a = apply_mutation(p, name, 12345, cross, stem(path))
            b = apply_mutation(p, name, 12345, cross, stem(path))
            if a != b:
                bad += 1
                print(f"  NONDETERMINISTIC {name}")
            if a[0] is not None:
                try:
                    q = parse(a[0])
                    if name != "text.limb.17digits" and dump(q) != a[0]:
                        bad += 1
                        print(f"  mutant does not round-trip: {name}")
                except (ParseError, ValueError) as e:
                    if not name.startswith("text."):
                        bad += 1
                        print(f"  mutant does not parse: {name}: {e}")
        if dump(p) != text:
            bad += 1
            print("  a mutation modified the seed structure in place!")
    print(f"{len(CATALOG)} catalog mutations, {len(cross)} cross-statement ones")
    print("selftest", "PASSED" if not bad else f"FAILED ({bad})")
    return 1 if bad else 0


def cmd_list(args):
    seeds = load_seeds(args.seed_paths)
    for n in sorted(CATALOG):
        fam, _, d = CATALOG[n]
        print(f"{n:34} {d}")
    for n in sorted(cross_mutations(seeds)):
        print(f"{n:34} cross-statement")


def cmd_mutate(args):
    seed = os.path.abspath(args.seed)
    seeds = load_seeds([seed] + (args.seeds or []))
    cross = cross_mutations(seeds)
    text, chain = apply_mutation(seeds[seed][1], args.mutation, args.rng, cross, stem(seed))
    if text is None:
        print("mutation not applicable", file=sys.stderr)
        return 1
    if chain:
        print("chain:", " ".join(chain), file=sys.stderr)
    if args.output:
        with open(args.output, "w") as f:
            f.write(text)
        if args.check:
            for k, (line, err) in check_once(os.path.abspath(args.output), args.lean, args.rust,
                                             args.timeout).items():
                print(f"{k}: {line}")
    else:
        sys.stdout.write(text)
    return 0


def cmd_replay(args):
    path = os.path.abspath(args.file)
    for k, (line, err) in check_once(path, args.lean, args.rust, args.timeout).items():
        print(f"{k}: {line}")
        if err and args.verbose:
            print(f"{k} stderr: {err}")
    return 0


def resolve_bins(args, need_rust):
    """The two oracles' paths: --lean, and --rust or the binary --leanvm builds."""
    if not os.path.exists(args.lean):
        sys.exit(f"Lean oracle {args.lean} not found: `lake build leanervm-check`, or --lean")
    if not need_rust:
        return
    if args.rust is None and args.leanvm is not None:
        r = subprocess.run([sys.executable, "-I", os.path.join(ROOT, "scripts/check-proofs-rust.py"),
                            args.leanvm, "--build-only"], stdout=subprocess.PIPE, text=True)
        if r.returncode != 0:
            sys.exit("scripts/check-proofs-rust.py --build-only failed")
        args.rust = r.stdout.strip().splitlines()[-1]
    if args.rust is None or not os.path.exists(args.rust):
        sys.exit(f"Rust oracle {args.rust} not found: pass --leanvm <leanVM checkout> to build "
                 "it, --rust <proof-check binary>, or --lean-only")


def cmd_enumerate(args):
    resolve_bins(args, not args.lean_only)
    r = Runner(args, iter(()))
    if not sanity(r.seeds, args):
        print("WARNING: a seed is not accepted by both oracles")
    r.jobs = enumerate_jobs(r.seeds, r.cross, args.reps, args.rng, args.cross_limit)
    return r.run(None, dict(mode="enumerate", lean_bin=args.lean, rust_bin=args.rust,
                            seeds=sorted(r.seeds), reps=args.reps, rng=args.rng))


def cmd_run(args):
    resolve_bins(args, not args.lean_only)
    r = Runner(args, iter(()))
    if not sanity(r.seeds, args):
        print("WARNING: a seed is not accepted by both oracles")
    r.jobs = random_jobs(r.seeds, r.cross, args.rng, args.havoc)
    return r.run(args.minutes, dict(mode="run", lean_bin=args.lean, rust_bin=args.rust,
                                    seeds=sorted(r.seeds), rng=args.rng))


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)

    def out(p):
        p.add_argument("--out", default=OUT_DIR,
                       help="work directory: seeds/, work/, findings/, logs/, summaries "
                            "(default: .lake/differential)")

    def seeds(p):
        out(p)
        p.add_argument("--seeds", nargs="+",
                       help="seed proofs, plain or gzip (default: tests/vectors/fill.proof.gz "
                            "and the Rust fixture in tests/LeanerVMTests/Protocol/RustProofData.lean)")

    def oracles(p):
        p.add_argument("--lean", default=LEAN_BIN, help="leanervm-check (default: .lake/build/bin)")
        p.add_argument("--rust", help="the proof-check binary (scripts/check-proofs-rust.py "
                                      "--build-only prints its path)")
        p.add_argument("--leanvm", help="a leanVM checkout at the pin, to build proof-check from")
        p.add_argument("--timeout", type=float, default=30.0, help="per-proof seconds")
        p.add_argument("--memory", default="4G",
                       help="MemoryMax of each oracle process under systemd-run (0: no scope)")

    def runner(p):
        oracles(p)
        seeds(p)
        p.add_argument("--workers", type=int, default=4, help="Lean and Rust workers each")
        p.add_argument("--rng", type=int, default=1)
        p.add_argument("--report", type=float, default=3.0, help="minutes between tables")
        p.add_argument("--lean-only", action="store_true", help="development without Rust")

    p = sub.add_parser("selftest", help="round-trip, determinism and classification checks")
    seeds(p)
    p.set_defaults(fn=cmd_selftest)
    p = sub.add_parser("list", help="print the mutation catalog")
    seeds(p)
    p.set_defaults(fn=cmd_list)
    p = sub.add_parser("mutate", help="regenerate a mutant from (seed, mutation, rng)")
    oracles(p)
    p.add_argument("--seed", required=True)
    p.add_argument("--mutation", required=True)
    p.add_argument("--rng", type=int, required=True)
    p.add_argument("--seeds", nargs="*", help="the other seeds a cross.* mutation names")
    p.add_argument("-o", "--output")
    p.add_argument("--check", action="store_true", help="run both oracles on --output")
    p.set_defaults(fn=cmd_mutate)
    p = sub.add_parser("replay", help="run both oracles once on a proof file")
    oracles(p)
    p.add_argument("file")
    p.add_argument("-v", "--verbose", action="store_true")
    p.set_defaults(fn=cmd_replay)
    p = sub.add_parser("enumerate", help="every deterministic single mutation once per seed")
    runner(p)
    p.add_argument("--reps", type=int, default=1, help="rng seeds per (seed, mutation)")
    p.add_argument("--cross-limit", type=int, default=3, help="cross partners per seed")
    p.set_defaults(fn=cmd_enumerate)
    p = sub.add_parser("run", help="random mutation and havoc for M minutes")
    runner(p)
    p.add_argument("--minutes", type=float, default=20.0)
    p.add_argument("--havoc", type=float, default=0.3, help="share of havoc mutants")
    p.set_defaults(fn=cmd_run)
    args = ap.parse_args()
    if getattr(args, "memory", "0") != "0" and shutil.which("systemd-run"):
        SCOPE[:] = ["systemd-run", "--user", "--scope", "-q", "-p", f"MemoryMax={args.memory}",
                    "-p", "MemorySwapMax=0"]
    if args.cmd in ("selftest", "list", "enumerate", "run"):
        args.out = os.path.abspath(args.out)
        args.seed_paths = seed_files(args.seeds, args.out)
    if args.cmd == "replay" or (args.cmd == "mutate" and args.check):
        # Rust is optional here: without --rust or --leanvm only Lean answers.
        resolve_bins(args, args.rust is not None or args.leanvm is not None)
    sys.exit(args.fn(args) or 0)


if __name__ == "__main__":
    main()
