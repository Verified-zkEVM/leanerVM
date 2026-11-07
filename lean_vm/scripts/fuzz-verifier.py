"""Differential fuzzing of the Lean verifier against the deployed Rust verifier on real proofs.

The fixtures under tests/fixtures/verifier/ are proofs of the leanVM Rust prover
(scripts/export-verifier-fixtures-rust.sh), each in three forms: the scalar stream with the
Merkle openings phase by phase (`stream.bin`, `merkle_phases.bin`: the `verifier` crate's
`Proof { stream, merkle_openings: Vec<Vec<MerklePath>> }`), the Python verifier's flat openings
(`merkle_openings.bin`), and the wire encoding (`proof.wire`, `Proof::to_bytes`). This driver
mutates every fixture and runs, on the honest proof and on every mutation,

  * the Lean verifier, `lake exe leanvm-verify` (cli/LeanvmVerify.lean): the statement's verifier
    compiled, on the structured files, or `Proof.fromBytes` then that verifier on a wire proof;
  * the Rust verifier, scripts/rust-verifier-cli (`verifier::verify_execution` of leanVM's
    `crates/verifier`, the deployed one, after `Proof::from_bytes` on a wire proof), in one
    `--batch` process;
  * with `--python`, also the Python verifier itself, as a tie-breaker, on the flat openings of
    the (mutated) phases.

It fails if the Lean and the Rust verdicts ever differ, and prints a table of verdicts by
mutation class. A Rust panic or a Lean crash counts as a rejection but is reported.

The stream's mutation positions come from an instrumented run of the Python verifier on the
honest proof: the stream offset where every phase of `verify_execution` starts, every
commitment root's two halves and every proof-of-work nonce; the openings' from the phases file
itself. Each structured case changes one thing:

  phase       one bit of the first, middle or last scalar of a phase (low bit of limb 0, top bit
              of limb 2), of a repeated phase (the Keccak layers) its first and last instances;
  root        the low bit, or a bit of the (must-be-zero) top limb, of a root half;
  nonce       the low bit, the top bit, or a bit of limb 1, of a proof-of-work nonce;
  opening     one bit of a phase's first or last leaf word, its first sibling, its top sibling,
              and of a random path of the phase;
  position    a path's `leaf_index`: its low bit, its top bit, the next path's position, the
              position plus 2^height (the same path, out of range), two paths swapped;
  shape       a leaf one word longer or shorter, a path one sibling longer or shorter, a phase
              one path shorter or longer, the last phase dropped or repeated, a count set to
              2^32 - 1 (the shape check, `Transcript::merkle`, and the reader's bounds);
  public      one bit of a public input byte (0, 15, 16, 31);
  rows        a table's announced row count one fewer, one more, zero, its full height and above
              the cap, which moves its padding rows (or its height);
  bytecode    one bit of the first, the first nonzero, a middle and the last bytecode byte;
  length      truncations and appends of every file (whole and partial elements, words, digests);
  wire        the wire proof, decoded by each verifier (`Proof::from_bytes`, `Proof.fromBytes`):
              honest; a scalar's bit; truncated and extended; the phase count, a query count, the
              height, the leaf width and the row width changed; a position flipped, set out of
              range, set to another query's; the row width made non-minimal (a zero word kept in
              every leaf); a surplus sibling; a carried sibling's bit.

The random cases, from `--seed`, are single random bit flips anywhere (weighted by file size),
random multi-byte corruptions (several bytes of one file, or one random run of bytes), a random
scalar replaced by a random element or by zero, two scalars of one phase swapped, a random
path's leaf word or sibling replaced, a random path's position bit flipped below the height,
and random bit flips of the wire proof; a random edit that leaves the proof unchanged is drawn
again.

Usage (from lean_vm; the two verifiers built first, see below):
  python3 -I scripts/fuzz-verifier.py tests/fixtures/verifier \\
      [--mutations 250] [--seed 1] [--jobs 8] [--python] [--keep <dir>] [fixture ...]

  ( ulimit -v 40000000; lake build leanvm-verify )
  cargo build --release --manifest-path scripts/rust-verifier-cli/Cargo.toml

The Rust and Python verifiers are those of the leanVM commit in `../leanvm-rev`, in the tree
`../leanvm-tree.sh` checks out.

`--mutations` is the number of cases per fixture, structured ones first, then random ones up to
it. Every child process runs under an address-space limit (`--memory-gb`, default 40). The
mutated files of every case on which the verifiers disagree are kept under `--keep` (default: a
new directory under the system temporary directory), with a `case.txt` saying what was changed;
`--log` writes one line per case.
"""

import argparse
import contextlib
import hashlib
import importlib.util
import os
import random
import resource
import shutil
import subprocess
import sys
import tempfile
import time
import zlib
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

PIN = "d1c4c8f70dd3245bc610a187702158989bc8275a"
VERIFIER_SHA256 = "67a58e965ee5932da225670ab47dc5cb15e0c68fda6b7b7ffff37659c58eb1d4"
FLAT = ("bytecode.bin", "public_input.bin", "stream.bin", "merkle_openings.bin")  # the Python verifier's
ROOT = Path(__file__).resolve().parent.parent
TREE = ROOT.parent / ".leanvm"
LEAN_EXE = ROOT / ".lake" / "build" / "bin" / "leanvm-verify"
RUST_EXE = ROOT / "scripts" / "rust-verifier-cli" / "target" / "release" / "leanvm-rust-verify"


# The Python verifier, instrumented -------------------------------------------------------------


def load_verifier(tree: Path):
    """A fresh copy of the verifier module, so that instrumenting it touches no other."""
    path = tree / "python-verifier" / "verifier.py"
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    if digest != VERIFIER_SHA256:
        sys.exit(f"{path} is not the verifier at {PIN} (sha256 {digest})")
    spec = importlib.util.spec_from_file_location("instrumented_verifier", path)
    module = importlib.util.module_from_spec(spec)
    sys.modules["instrumented_verifier"] = module
    spec.loader.exec_module(module)
    return module


def instrument(tree: Path, directory: Path) -> dict:
    """Run the Python on the honest proof (its flat openings), recording where each phase, root and nonce is."""
    V = load_verifier(tree)
    events = {"phase": [("sizes", 0)], "nonce": [], "root": [], "merkle": []}
    state = {}
    original_init = V.Transcript.__init__

    def init(self, *args, **kwargs):
        original_init(self, *args, **kwargs)
        state["transcript"] = self

    def offset() -> int:
        return state["transcript"].stream_offset

    def phase(name, function):
        def wrapped(*args, **kwargs):
            events["phase"].append((name, offset()))
            return function(*args, **kwargs)

        return wrapped

    original_grind = V.Transcript.grind_check

    def grind(self, bits):
        events["nonce"].append((self.stream_offset, bits))
        return original_grind(self, bits)

    original_merkle = V.Transcript.merkle

    def merkle(self, root, block_length, queries, leaf_words):
        start = self.opening_offset
        result = original_merkle(self, root, block_length, queries, leaf_words)
        events["merkle"].append((start, len(queries), V.log2_strict(block_length), leaf_words))
        return result

    original_from_halves = V.Digest.from_halves.__func__

    def from_halves(cls, low, high):
        events["root"].append(offset() - 2)
        return original_from_halves(cls, low, high)

    V.Transcript.__init__ = init
    V.Transcript.grind_check = grind
    V.Transcript.merkle = merkle
    V.Digest.from_halves = classmethod(from_halves)
    for name, attribute in (("bus", "verify_bus_balance"), ("keccak", "verify_keccak"),
                            ("keccak-layer", "verify_keccak_layer"), ("keccak-open", "_keccak_open"),
                            ("ring", "ring_switch"), ("whir", "verify_stacked_opening")):
        setattr(V, attribute, phase(name, getattr(V, attribute)))
    original_table = V.table_sumcheck

    def table(*args, **kwargs):  # the public input phase starts where the table sumcheck ends
        result = original_table(*args, **kwargs)
        events["phase"].append(("public", offset()))
        return result

    V.table_sumcheck = phase("tables", table)
    with contextlib.redirect_stdout(sys.stderr):
        code = V.main([str(directory / name) for name in FLAT])
    assert code == 0, f"{directory}: the honest proof is rejected by the Python"
    transcript = state["transcript"]
    events["stream_length"] = len(transcript.proof.stream)
    events["openings_length"] = len(transcript.proof.merkle_openings)
    # The root is read between the sizes and the bus; give it a phase of its own.
    events["phase"].insert(1, ("root", events["root"][0]))
    return events


# The proof's files ------------------------------------------------------------------------------


def u32(n: int) -> bytes:
    return n.to_bytes(4, "little")


def parse_phases(data: bytes) -> list:
    """The phases file's layout: per phase its count's offset and per path the offsets of its
    position, leaf length, leaf, sibling count and siblings, with the lengths."""
    at = 4
    phases = []
    for _ in range(int.from_bytes(data[:4], "little")):
        count_at = at
        count = int.from_bytes(data[at:at + 4], "little")
        at += 4
        paths = []
        for _ in range(count):
            path = {"index": at, "position": int.from_bytes(data[at:at + 8], "little")}
            at += 8
            path["leaf_length"] = at
            path["words"] = int.from_bytes(data[at:at + 4], "little")
            at += 4
            path["leaf"] = at
            at += 8 * path["words"]
            path["sibling_count"] = at
            path["height"] = int.from_bytes(data[at:at + 4], "little")
            at += 4
            path["siblings"] = at
            at += 32 * path["height"]
            path["end"] = at
            paths.append(path)
        phases.append({"count": count_at, "paths": paths, "start": count_at, "end": at})
    assert at == len(data), "the honest phases file is read whole"
    return phases


def flat_openings(phases_data: bytes):
    """The Python verifier's flat openings of a (mutated) phases file, or None if it does not parse."""
    try:
        out, at = bytearray(), 4
        for _ in range(int.from_bytes(phases_data[:4], "little")):
            count = int.from_bytes(phases_data[at:at + 4], "little")
            at += 4
            for _ in range(count):
                words = int.from_bytes(phases_data[at + 8:at + 12], "little")
                out += phases_data[at:at + 8] + phases_data[at + 12:at + 12 + 8 * words]
                at += 12 + 8 * words
                height = int.from_bytes(phases_data[at:at + 4], "little")
                out += phases_data[at + 4:at + 4 + 32 * height]
                at += 4 + 32 * height
                if at > len(phases_data):
                    return None
        return bytes(out) if at == len(phases_data) else None
    except IndexError:
        return None


def parse_wire(data: bytes) -> dict:
    """The wire proof's layout (wire.rs, `to_bytes`): the stream, then per phase the offsets of its
    query count, positions, height, leaf width, row width, distinct leaves and carried siblings."""
    length = int.from_bytes(data[:4], "little")
    at = 4 + 24 * length
    wire = {"stream": 4, "phase_count": at, "phases": []}
    at += 4
    for _ in range(int.from_bytes(data[wire["phase_count"]:wire["phase_count"] + 4], "little")):
        phase = {"count": at}
        count = int.from_bytes(data[at:at + 4], "little")
        at += 4
        phase["positions"] = at
        positions = [int.from_bytes(data[at + 4 * i:at + 4 * i + 4], "little") for i in range(count)]
        at += 4 * count
        phase["height"], phase["leaf_words"], phase["row_words"] = at, at + 4, at + 8
        height, leaf_words, row_words = (int.from_bytes(data[at + 4 * i:at + 4 * i + 4], "little") for i in range(3))
        at += 12
        distinct = sorted(set(positions))
        phase["leaves"] = at
        at += 8 * row_words * len(distinct)
        carried, level = 0, set(distinct)
        for _ in range(height):
            carried += len({node ^ 1 for node in level} - level)
            level = {node >> 1 for node in level}
        phase["siblings"] = at
        at += 32 * carried
        phase.update(end=at, positions_list=positions, height_value=height, leaf_words_value=leaf_words,
                     row_words_value=row_words, distinct=len(distinct), carried=carried)
        wire["phases"].append(phase)
    assert at == len(data), "the honest wire proof is read whole"
    return wire


# Mutations --------------------------------------------------------------------------------------
#
# A case is (category, label, edits); an edit is one of
#   ("flip", file, offset, mask)               XOR a mask into a byte;
#   ("set", file, offset, bytes)               overwrite bytes;
#   ("splice", file, offset, delete, bytes)    delete bytes there and insert others;
#   ("truncate", file, n)                      drop the last n bytes;
#   ("append", file, bytes)                    append bytes.
# Splices of one case are applied from the last offset to the first. A case whose edits touch
# `proof.wire` is a wire case: the verifiers read the bytecode, the public input and the wire
# proof; any other reads the bytecode, the public input, the stream and the phases.

S, M, W = "stream.bin", "merkle_phases.bin", "proof.wire"
STRUCTURED = ("bytecode.bin", "public_input.bin", S, M)
WIRE = ("bytecode.bin", "public_input.bin", W)
FILES = STRUCTURED + (W,)


def flip(file, offset, bit=0):
    return ("flip", file, offset, 1 << bit)


def phase_cases(phases: list, data: dict, rng: random.Random) -> list:
    """The openings', the positions' and the shapes' cases, on the first and the last phase (all
    of them with `rng`-chosen paths in between) and the phase list."""
    cases = []
    chosen = sorted({0, len(phases) - 1})
    for p in chosen:
        paths = phases[p]["paths"]
        first, last, middle = paths[0], paths[-1], paths[rng.randrange(len(paths))]
        height = first["height"]
        cases += [
            ("opening", f"phase {p} first leaf, word 0", [flip(M, first["leaf"])]),
            ("opening", f"phase {p} last leaf, last word, top bit", [flip(M, last["sibling_count"] - 1, 7)]),
            ("opening", f"phase {p} first sibling", [flip(M, first["siblings"])]),
            ("opening", f"phase {p} last path, top sibling", [flip(M, last["end"] - 1, 7)]),
            ("opening", f"phase {p} random byte of a random path",
             [flip(M, rng.randrange(middle["leaf"], middle["end"]), rng.randrange(8))]),
            ("position", f"phase {p} first position low bit", [flip(M, first["index"])]),
            ("position", f"phase {p} first position top bit", [flip(M, first["index"] + 7, 7)]),
            ("position", f"phase {p} first position + 2^{height} (out of range)",
             [("set", M, first["index"], (first["position"] + (1 << height)).to_bytes(8, "little"))]),
        ]
        if len(paths) >= 2:
            a, b = paths[0], paths[1]
            cases.append(("position", f"phase {p} first position set to the second's",
                          [("set", M, a["index"], data[M][b["index"]:b["index"] + 8])]))
            if a["position"] != b["position"]:
                cases.append(("position", f"phase {p} first two paths swapped",
                              [("set", M, a["index"], data[M][b["index"]:b["end"]] + data[M][a["index"]:a["end"]])]))
        cases += [
            ("shape", f"phase {p} first leaf one word longer",
             [("splice", M, first["leaf_length"], 4, u32(first["words"] + 1)), ("splice", M, first["leaf"], 0, bytes(8))]),
            ("shape", f"phase {p} first leaf one word shorter (its first word dropped)",
             [("splice", M, first["leaf_length"], 4, u32(first["words"] - 1)), ("splice", M, first["leaf"], 8, b"")]),
            ("shape", f"phase {p} last path one sibling longer",
             [("splice", M, last["sibling_count"], 4, u32(height + 1)), ("splice", M, last["end"], 0, bytes(32))]),
            ("shape", f"phase {p} last path one sibling shorter",
             [("splice", M, last["sibling_count"], 4, u32(height - 1)), ("splice", M, last["end"] - 32, 32, b"")]),
            ("shape", f"phase {p} last path dropped",
             [("splice", M, phases[p]["count"], 4, u32(len(paths) - 1)), ("splice", M, last["index"], last["end"] - last["index"], b"")]),
            ("shape", f"phase {p} last path repeated",
             [("splice", M, phases[p]["count"], 4, u32(len(paths) + 1)), ("splice", M, last["end"], 0, data[M][last["index"]:last["end"]])]),
            ("shape", f"phase {p} path count 2^32 - 1", [("set", M, phases[p]["count"], u32(2**32 - 1))]),
            ("shape", f"phase {p} first leaf length 2^32 - 1", [("set", M, first["leaf_length"], u32(2**32 - 1))]),
        ]
    last = phases[-1]
    cases += [
        ("shape", "last phase dropped", [("splice", M, 0, 4, u32(len(phases) - 1)), ("truncate", M, last["end"] - last["start"])]),
        ("shape", "last phase repeated", [("splice", M, 0, 4, u32(len(phases) + 1)), ("append", M, data[M][last["start"]:last["end"]])]),
        ("shape", "an empty phase appended", [("splice", M, 0, 4, u32(len(phases) + 1)), ("append", M, u32(0))]),
        ("shape", "phase count 2^32 - 1", [("set", M, 0, u32(2**32 - 1))]),
    ]
    return cases


def wire_cases(wire: dict, events: dict, data: dict, rng: random.Random) -> list:
    cases = [("honest", "the honest wire proof", [("set", W, 0, data[W][:4])])]
    for name, first in events["phase"][2::3]:
        cases.append(("wire", f"wire: {name} scalar {first} limb 0 bit 0", [flip(W, 4 + 24 * first)]))
    cases += [
        ("wire", "wire: stream length + 1", [("set", W, 0, u32(events["stream_length"] + 1))]),
        ("wire", "wire: last byte dropped", [("truncate", W, 1)]),
        ("wire", "wire: last sibling dropped", [("truncate", W, 32)]),
        ("wire", "wire: a byte appended", [("append", W, bytes(1))]),
        ("wire", "wire: a zero u32 appended", [("append", W, u32(0))]),
        ("wire", "wire: phase count + 1",
         [("set", W, wire["phase_count"], u32(len(wire["phases"]) + 1))]),
        ("wire", "wire: phase count 9 (above MAX_PHASES)", [("set", W, wire["phase_count"], u32(9))]),
    ]
    for p in sorted({0, len(wire["phases"]) - 1}):
        ph = wire["phases"][p]
        positions, height = ph["positions_list"], ph["height_value"]
        words, row = ph["leaf_words_value"], ph["row_words_value"]
        cases += [
            ("wire", f"wire: phase {p} query count + 1", [("set", W, ph["count"], u32(len(positions) + 1))]),
            ("wire", f"wire: phase {p} query count 257 (above MAX_QUERIES)", [("set", W, ph["count"], u32(257))]),
            ("wire", f"wire: phase {p} first position low bit", [flip(W, ph["positions"])]),
            ("wire", f"wire: phase {p} first position 2^{height} (out of range)",
             [("set", W, ph["positions"], u32(1 << height))]),
            ("wire", f"wire: phase {p} height + 1", [("set", W, ph["height"], u32(height + 1))]),
            ("wire", f"wire: phase {p} height 33 (above MAX_HEIGHT)", [("set", W, ph["height"], u32(33))]),
            ("wire", f"wire: phase {p} leaf width + 1", [("set", W, ph["leaf_words"], u32(words + 1))]),
            ("wire", f"wire: phase {p} row width - 1", [("set", W, ph["row_words"], u32(row - 1))]),
            ("wire", f"wire: phase {p} row width above the leaf width", [("set", W, ph["row_words"], u32(words + 1))]),
            ("wire", f"wire: phase {p} first leaf, last word, low bit", [flip(W, ph["leaves"] + 8 * row - 8)]),
            ("wire", f"wire: phase {p} surplus sibling", [("splice", W, ph["end"], 0, bytes(32))]),
        ]
        if len(set(positions)) >= 2:
            other = next(q for q in positions if q != positions[0])
            cases.append(("wire", f"wire: phase {p} first position set to another query's",
                          [("set", W, ph["positions"], u32(other))]))
        if row < words:  # one zero word kept in front of every distinct leaf: not the least row width
            edits = [("set", W, ph["row_words"], u32(row + 1))]
            edits += [("splice", W, ph["leaves"] + 8 * row * i, 0, bytes(8)) for i in range(ph["distinct"])]
            cases.append(("wire", f"wire: phase {p} row width {row + 1}, not minimal", edits))
        if ph["carried"]:
            cases.append(("wire", f"wire: phase {p} first carried sibling, bit 0", [flip(W, ph["siblings"])]))
    return cases


def structured_cases(events: dict, sizes: dict, data: dict, rng: random.Random) -> list:
    wire = wire_cases(events["wire"], events, data, rng)
    cases = [("honest", "the honest proof", []), wire[0]]  # the honest proof, then its wire form
    cases += phase_cases(events["phases"], data, rng)
    cases += wire[1:]
    bounds = events["phase"] + [("end", events["stream_length"])]
    names = [name for name, _ in events["phase"]]
    for index, ((phase, first), (_, end)) in enumerate(zip(bounds, bounds[1:])):
        if first == end:  # the public phase and the ring switch may read no scalar
            continue
        if names.index(phase) < index < len(names) - 1 - names[::-1].index(phase):
            continue  # of a repeated phase (the Keccak layers), its first and last instances only
        for position in sorted({first, (first + end) // 2, end - 1}):
            cases.append(("phase", f"{phase} scalar {position} limb 0 bit 0", [flip(S, 24 * position)]))
            cases.append(("phase", f"{phase} scalar {position} limb 2 bit 63", [flip(S, 24 * position + 23, 7)]))
    for index, position in enumerate(events["root"]):
        for half in (0, 1):
            at = 24 * (position + half)
            cases.append(("root", f"root {index} half {half} low bit", [flip(S, at)]))
            cases.append(("root", f"root {index} half {half} limb 2 bit 0", [flip(S, at + 16)]))
    for position, bits in events["nonce"]:
        at = 24 * position
        cases.append(("nonce", f"nonce at scalar {position} ({bits} bits) low bit", [flip(S, at)]))
        cases.append(("nonce", f"nonce at scalar {position} ({bits} bits) bit 63", [flip(S, at + 7, 7)]))
        cases.append(("nonce", f"nonce at scalar {position} ({bits} bits) limb 1 bit 0", [flip(S, at + 8)]))
    for at in (0, 15, 16, 31):
        cases.append(("public", f"public input byte {at}", [flip("public_input.bin", at)]))
    stream = data[S]
    for table in range(6):  # the announced row counts, scalars 1..6: the padding rows move
        at = 24 * (1 + table)
        rows = int.from_bytes(stream[at : at + 8], "little")
        full = 1 << max(rows - 1, 0).bit_length()
        changes = (("one fewer", rows - 1), ("one more", rows + 1), ("none", 0), ("a full table", full), ("above the cap", 2**32 + 1))
        for label, value in changes:
            if 0 <= value != rows:
                cases.append(("rows", f"table {table} rows {rows} -> {value} ({label})", [("set", S, at, value.to_bytes(8, "little"))]))
    bytecode = data["bytecode.bin"]
    nonzero = next(i for i, b in enumerate(bytecode) if b)
    for label, at in (("byte 0", 0), (f"first nonzero byte {nonzero}", nonzero),
                      ("middle byte", len(bytecode) // 2), ("last byte", len(bytecode) - 1)):
        cases.append(("bytecode", f"bytecode {label}", [flip("bytecode.bin", at)]))
    length = [
        (S, "truncate", 24, "last scalar dropped"),
        (S, "truncate", 1, "stream cut mid-scalar"),
        (S, "truncate", sizes[S], "empty stream"),
        (S, "append", bytes(24), "zero scalar appended"),
        (S, "append", bytes(rng.randrange(256) for _ in range(24)), "random scalar appended"),
        (S, "append", bytes(5), "partial scalar appended"),
        (M, "truncate", 32, "last sibling dropped"),
        (M, "truncate", 1, "phases cut by one byte"),
        (M, "truncate", sizes[M], "empty phases file"),
        (M, "append", bytes(1), "byte appended to the phases"),
        (M, "append", bytes(32), "digest appended to the phases"),
        ("public_input.bin", "truncate", 1, "public input cut by one byte"),
        ("public_input.bin", "append", bytes(1), "byte appended to the public input"),
        ("bytecode.bin", "truncate", 8, "last bytecode word dropped"),
        ("bytecode.bin", "truncate", 3, "bytecode cut mid-word"),
        ("bytecode.bin", "append", bytes(8), "zero bytecode word appended"),
        ("bytecode.bin", "append", bytes(sizes["bytecode.bin"]), "bytecode doubled with zero words"),
        ("bytecode.bin", "truncate", sizes["bytecode.bin"] // 2, "bytecode halved"),
    ]
    for file, operation, argument, label in length:
        cases.append(("length", label, [(operation, file, argument)]))
    return cases


def random_case(events: dict, sizes: dict, data: dict, rng: random.Random):
    kind = rng.choices(["flip", "bytes", "run", "scalar", "zero", "swap", "leaf", "sibling", "position", "wire"],
                       [25, 12, 8, 12, 8, 8, 8, 6, 6, 7])[0]
    if kind == "flip":
        file = rng.choices(STRUCTURED, [sizes[f] for f in STRUCTURED])[0]
        at, bit = rng.randrange(sizes[file]), rng.randrange(8)
        return ("random-flip", f"{file} byte {at} bit {bit}", [flip(file, at, bit)])
    if kind == "bytes":
        file = rng.choices(STRUCTURED[1:], [1, 3, 3])[0]
        count = rng.randrange(2, 9)
        edits = [("set", file, rng.randrange(sizes[file]), bytes([rng.randrange(256)])) for _ in range(count)]
        return ("random-bytes", f"{file} {count} random bytes at {sorted(e[2] for e in edits)}", edits)
    if kind == "run":
        file = rng.choice((S, M))
        length = rng.randrange(2, 65)
        at = rng.randrange(sizes[file] - length)
        return ("random-run", f"{file} bytes {at}..{at + length} random", [("set", file, at, rng.randbytes(length))])
    if kind == "wire":
        at, bit = rng.randrange(sizes[W]), rng.randrange(8)
        return ("random-wire", f"{W} byte {at} bit {bit}", [flip(W, at, bit)])
    scalars = events["stream_length"]
    if kind == "scalar":
        position = rng.randrange(scalars)
        return ("random-scalar", f"scalar {position} replaced by a random element", [("set", S, 24 * position, rng.randbytes(24))])
    if kind == "zero":
        position = rng.randrange(scalars)
        return ("random-scalar", f"scalar {position} replaced by zero", [("set", S, 24 * position, bytes(24))])
    if kind == "swap":
        bounds = [p for p in events["phase"]] + [("end", scalars)]
        spans = [(name, first, end) for (name, first), (_, end) in zip(bounds, bounds[1:]) if end - first >= 2]
        name, first, end = rng.choice(spans)
        i, j = rng.sample(range(first, end), 2)
        stream = data[S]
        return ("random-swap", f"{name} scalars {i} and {j} swapped",
                [("set", S, 24 * i, stream[24 * j:24 * j + 24]), ("set", S, 24 * j, stream[24 * i:24 * i + 24])])
    p = rng.randrange(len(events["phases"]))
    n = rng.randrange(len(events["phases"][p]["paths"]))
    path = events["phases"][p]["paths"][n]
    if kind == "leaf":
        word = rng.randrange(path["words"])
        return ("random-leaf", f"phase {p} path {n} leaf word {word} replaced",
                [("set", M, path["leaf"] + 8 * word, rng.randbytes(8))])
    if kind == "sibling":
        level = rng.randrange(path["height"])
        return ("random-sibling", f"phase {p} path {n} sibling {level} replaced",
                [("set", M, path["siblings"] + 32 * level, rng.randbytes(32))])
    bit = rng.randrange(max(path["height"], 1))
    return ("random-position", f"phase {p} path {n} position bit {bit}", [flip(M, path["index"] + bit // 8, bit % 8)])


def apply(data: dict, edits: list) -> dict:
    """The mutated files, only those an edit touches."""
    out = {}
    splices = sorted((e for e in edits if e[0] == "splice"), key=lambda e: -e[2])
    for edit in [e for e in edits if e[0] != "splice"] + splices:
        file = edit[1]
        buffer = out.setdefault(file, bytearray(data[file]))
        if edit[0] == "flip":
            buffer[edit[2]] ^= edit[3]
        elif edit[0] == "set":
            buffer[edit[2]:edit[2] + len(edit[3])] = edit[3]
        elif edit[0] == "splice":
            buffer[edit[2]:edit[2] + edit[3]] = edit[4]
        elif edit[0] == "truncate":
            del buffer[len(buffer) - edit[2]:]
        elif edit[0] == "append":
            buffer.extend(edit[2])
    return {file: bytes(buffer) for file, buffer in out.items()}


def describe(edit) -> str:
    if edit[0] == "flip":
        return f"flip {edit[1]} {edit[2]} 0x{edit[3]:02x}"
    if edit[0] == "set":
        return f"set {edit[1]} {edit[2]} {edit[3].hex() if len(edit[3]) <= 64 else f'({len(edit[3])} bytes)'}"
    if edit[0] == "splice":
        return f"splice {edit[1]} {edit[2]} -{edit[3]} +{edit[4].hex() if len(edit[4]) <= 64 else f'({len(edit[4])} bytes)'}"
    if edit[0] == "truncate":
        return f"truncate {edit[1]} {edit[2]}"
    return f"append {edit[1]} {edit[2].hex() if len(edit[2]) <= 64 else f'({len(edit[2])} bytes)'}"


# Running the verifiers --------------------------------------------------------------------------


def limit(gigabytes: int):
    def set_limit():
        cap = gigabytes << 30
        resource.setrlimit(resource.RLIMIT_AS, (cap, cap))

    return set_limit


def run_lean(exe: Path, paths: list, memory: int, timeout: int) -> tuple:
    start = time.monotonic()
    try:
        run = subprocess.run([str(exe), *map(str, paths)], capture_output=True, text=True, timeout=timeout,
                             preexec_fn=limit(memory))
    except subprocess.TimeoutExpired:
        return "timeout", f"no verdict after {timeout} s", time.monotonic() - start
    elapsed = time.monotonic() - start
    message = (run.stdout.strip().splitlines() or [""])[-1]
    if run.returncode == 0 and message == "verification succeeded":
        verdict = "accept"
    elif run.returncode == 1 and message == "verification failed":
        verdict = "reject"
    else:
        verdict = "crash"
        message = f"exit {run.returncode}: {(run.stdout + run.stderr).strip()[-300:]}"
    if "PANIC" in run.stderr:
        message += f" [Lean panic: {run.stderr.strip()[-300:]}]"
    return verdict, message, elapsed


def run_python(tree: Path, paths: list, memory: int, timeout: int) -> tuple:
    start = time.monotonic()
    try:
        run = subprocess.run([sys.executable, "-I", str(tree / "python-verifier" / "verifier.py"), *map(str, paths)],
                             capture_output=True, text=True, timeout=timeout, preexec_fn=limit(memory))
    except subprocess.TimeoutExpired:
        return "timeout", f"no verdict after {timeout} s", time.monotonic() - start
    message = ((run.stdout + run.stderr).strip().splitlines() or [""])[-1]
    verdict = "accept" if run.returncode == 0 and message == "verification succeeded" else "reject"
    if run.returncode not in (0, 1):
        verdict, message = "crash", f"exit {run.returncode}: {(run.stdout + run.stderr).strip()[-300:]}"
    return verdict, message, time.monotonic() - start


def run_rust(exe: Path, cases: list, memory: int) -> list:
    """Every case in one `--batch` process: one verdict line per line of four (or three) paths."""
    lines = "".join("\t".join(map(str, c["paths"])) + "\n" for c in cases)
    run = subprocess.run([str(exe), "--batch"], input=lines, capture_output=True, text=True,
                         preexec_fn=limit(memory), check=True)
    verdicts = []
    for line in run.stdout.splitlines():
        head, _, reason = line.partition(" ")
        verdicts.append((head, reason))
    assert len(verdicts) == len(cases), run.stderr
    return verdicts


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("fixtures", type=Path, help="directory of fixtures (tests/fixtures/verifier)")
    parser.add_argument("only", nargs="*", help="fixtures to fuzz (default: every one)")
    parser.add_argument("--mutations", type=int, default=250, help="cases per fixture, the honest one included")
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--jobs", type=int, default=8, help="Lean (and Python) verifiers run at once")
    parser.add_argument("--python", action="store_true", help="also run the Python verifier on every case")
    parser.add_argument("--lean-exe", type=Path, default=LEAN_EXE)
    parser.add_argument("--rust-exe", type=Path, default=RUST_EXE)
    parser.add_argument("--memory-gb", type=int, default=40, help="address-space limit of every child process")
    parser.add_argument("--timeout", type=int, default=900, help="seconds per Lean or Python run")
    parser.add_argument("--keep", type=Path, help="where to keep the files of disagreeing cases")
    parser.add_argument("--log", type=Path, help="write one line per case here")
    arguments = parser.parse_args()
    tree, fixtures = TREE, arguments.fixtures.resolve()
    for exe in (arguments.lean_exe, arguments.rust_exe):
        if not exe.exists():
            sys.exit(f"{exe} is not built; see the usage in {Path(__file__).name}")
    names = arguments.only or sorted(p.name for p in fixtures.iterdir() if p.is_dir())
    scratch = Path(tempfile.mkdtemp(prefix="fuzz-verifier-"))
    keep = arguments.keep or Path(tempfile.mkdtemp(prefix="fuzz-verifier-divergent-"))
    cases = []
    data_of = {}  # each fixture's honest phases file
    try:
        for name in names:
            directory = fixtures / name
            data = {file: (directory / file).read_bytes() for file in FILES}
            sizes = {file: len(content) for file, content in data.items()}
            data_of[name] = data[M]
            if flat_openings(data[M]) != (directory / "merkle_openings.bin").read_bytes():
                sys.exit(f"{directory}: merkle_phases.bin and merkle_openings.bin are not the same openings")
            events = instrument(tree, directory)
            events["phases"] = parse_phases(data[M])
            events["wire"] = parse_wire(data[W])
            print(f"{name}: {events['stream_length']} scalars, phases {events['phase']}, "
                  f"{len(events['root'])} roots, {len(events['nonce'])} nonces, "
                  f"{len(events['phases'])} opening phases of "
                  f"{[len(phase['paths']) for phase in events['phases']]} paths, "
                  f"{sizes[W]} wire bytes", file=sys.stderr)
            rng = random.Random(arguments.seed * 1_000_003 + zlib.crc32(name.encode()))
            generated = structured_cases(events, sizes, data, rng)[:arguments.mutations]
            while len(generated) < arguments.mutations:
                case = random_case(events, sizes, data, rng)
                # A random edit can leave the proof as it was (a zero scalar zeroed, equal scalars
                # swapped); draw again, so that every random case is a different proof.
                if any(content != data[file] for file, content in apply(data, case[2]).items()):
                    generated.append(case)
            for index, (category, label, edits) in enumerate(generated):
                mutated = apply(data, edits)
                case_dir = scratch / name / str(index)
                case_dir.mkdir(parents=True)
                paths = []
                for file in (WIRE if any(edit[1] == W for edit in edits) else STRUCTURED):
                    if file in mutated:
                        (case_dir / file).write_bytes(mutated[file])
                        paths.append(case_dir / file)
                    else:
                        paths.append(directory / file)
                cases.append({"fixture": name, "index": index, "category": category, "label": label,
                              "edits": edits, "paths": paths, "dir": case_dir})
        print(f"{len(cases)} cases; Rust verifier ...", file=sys.stderr)
        start = time.monotonic()
        for case, (verdict, reason) in zip(cases, run_rust(arguments.rust_exe, cases, arguments.memory_gb)):
            case["rust"] = verdict
            case["rust_reason"] = reason
        rust_time = time.monotonic() - start
        print(f"Rust: {rust_time:.1f} s for {len(cases)} cases; Lean verifier ({arguments.jobs} at once) ...",
              file=sys.stderr)

        done = Counter()

        def lean_job(case):
            case["lean"], case["lean_message"], case["lean_time"] = run_lean(
                arguments.lean_exe, case["paths"], arguments.memory_gb, arguments.timeout)
            done["lean"] += 1
            agree = "ok" if case["lean"] == case["rust"] or {case["lean"], case["rust"]} <= {"reject", "panic", "crash"} else "DIFFER"
            print(f"[{done['lean']}/{len(cases)}] {case['fixture']} #{case['index']} {case['category']}: "
                  f"{case['label']}: Lean {case['lean']} ({case['lean_time']:.1f} s), Rust {case['rust']} "
                  f"{case['rust_reason']} [{agree}]", file=sys.stderr, flush=True)

        def python_job(case):
            # The Python reads the flat openings: those of the (mutated) phases, if they parse.
            if len(case["paths"]) == 3:
                case["python"], case["python_message"], case["python_time"] = "skip", "a wire case", 0.0
                return
            phases = Path(case["paths"][3]).read_bytes()
            flat = flat_openings(phases)
            if flat is None:
                case["python"], case["python_message"], case["python_time"] = "skip", "the phases do not parse", 0.0
                return
            if phases != data_of[case["fixture"]] and flat == flat_openings(data_of[case["fixture"]]):
                # the phases changed and their flat form did not (an empty phase, a moved boundary)
                case["python"], case["python_message"], case["python_time"] = "skip", "the flat form is the honest one", 0.0
                return
            target = case["dir"] / "merkle_openings.bin"
            target.write_bytes(flat)
            case["python"], case["python_message"], case["python_time"] = run_python(
                tree, case["paths"][:3] + [target], arguments.memory_gb, arguments.timeout)

        start = time.monotonic()
        with ThreadPoolExecutor(arguments.jobs) as pool:
            # Slowest first: the Lean runs, then the Python ones fill the tail.
            futures = [pool.submit(lean_job, case) for case in cases]
            if arguments.python:
                futures += [pool.submit(python_job, case) for case in cases]
            for future in futures:
                future.result()
        lean_time = time.monotonic() - start

        # Verdicts: a Rust panic or a Lean crash is a rejection, but counted on its own.
        def accepted(verdict):
            return verdict == "accept"

        differ = [c for c in cases if accepted(c["lean"]) != accepted(c["rust"])]
        python_differ = [c for c in cases if arguments.python and c["python"] != "skip"
                         and accepted(c["python"]) != accepted(c["rust"])]
        table = defaultdict(Counter)
        for case in cases:
            row = table[(case["fixture"], case["category"])]
            row["cases"] += 1
            row["both accept"] += accepted(case["lean"]) and accepted(case["rust"])
            row["both reject"] += not accepted(case["lean"]) and not accepted(case["rust"])
            row["Lean only accepts"] += accepted(case["lean"]) and not accepted(case["rust"])
            row["Rust only accepts"] += accepted(case["rust"]) and not accepted(case["lean"])
            row["Rust panic"] += case["rust"] == "panic"
            row["Lean crash/timeout"] += case["lean"] in ("crash", "timeout")
            if arguments.python:
                row["Python differs"] += case["python"] != "skip" and accepted(case["python"]) != accepted(case["rust"])
            row["Lean seconds"] += case["lean_time"]
        columns = ["cases", "both accept", "both reject", "Lean only accepts", "Rust only accepts", "Rust panic",
                   "Lean crash/timeout"] + (["Python differs"] if arguments.python else []) + ["Lean seconds"]
        header = ["fixture", "class", *columns]
        rows = [[fixture, category, *(f"{table[(fixture, category)][c]:.0f}" for c in columns)]
                for fixture, category in sorted(table)]
        totals = Counter()
        for row in table.values():
            totals.update(row)
        rows.append(["all", "all", *(f"{totals[c]:.0f}" for c in columns)])
        widths = [max(len(r[i]) for r in [header, *rows]) for i in range(len(header))]
        print()
        for row in [header, ["-" * w for w in widths], *rows]:
            print("  ".join(cell.ljust(w) if i < 2 else cell.rjust(w) for i, (cell, w) in enumerate(zip(row, widths))))
        reasons = Counter(c["rust_reason"] or "accepted" for c in cases)
        print("\nRust verdicts by reason:")
        for reason, count in reasons.most_common():
            print(f"  {count:5}  {reason}")
        accepted_mutations = [c for c in cases if c["category"] != "honest" and accepted(c["lean"]) and accepted(c["rust"])]
        if accepted_mutations:
            print("\nMutations BOTH verifiers accept:")
            for case in accepted_mutations:
                print(f"  {case['fixture']} #{case['index']}: {case['label']}: {'; '.join(map(describe, case['edits']))}")
        print(f"\nRust {rust_time:.1f} s (one process); Lean {totals['Lean seconds']:.0f} s of runs, "
              f"{lean_time:.0f} s wall at {arguments.jobs} jobs")
        if arguments.log:
            with arguments.log.open("w") as log:
                for c in cases:
                    log.write("\t".join([c["fixture"], str(c["index"]), c["category"], c["label"], c["lean"],
                                         f"{c['lean_time']:.1f}", c["rust"], c["rust_reason"],
                                         c.get("python", "-"), c.get("python_message", "-"),
                                         "; ".join(map(describe, c["edits"]))]) + "\n")
        failures = differ + [c for c in python_differ if c not in differ]
        for case in failures:
            target = keep / case["fixture"] / str(case["index"])
            target.mkdir(parents=True, exist_ok=True)
            for path in case["paths"]:
                shutil.copy(path, target / Path(path).name)
            (target / "case.txt").write_text(
                f"fixture {case['fixture']} case {case['index']} ({case['category']}): {case['label']}\n"
                + "".join(describe(e) + "\n" for e in case["edits"])
                + f"Lean {case['lean']}: {case['lean_message']}\nRust {case['rust']}: {case['rust_reason']}\n"
                + (f"Python {case['python']}: {case['python_message']}\n" if arguments.python else ""))
        for case in differ:
            print(f"DIFFER {case['fixture']} #{case['index']} {case['label']}: Lean {case['lean']}, "
                  f"Rust {case['rust']} {case['rust_reason']} (kept in {keep / case['fixture'] / str(case['index'])})")
        for case in python_differ:
            print(f"PYTHON DIFFERS FROM RUST {case['fixture']} #{case['index']} {case['label']}: "
                  f"Python {case['python']} {case['python_message']}, Rust {case['rust']} {case['rust_reason']}")
        print(f"\n{len(differ)} Lean/Rust verdict difference(s) in {len(cases)} cases"
              + (f"; {len(python_differ)} Python/Rust" if arguments.python else ""))
        sys.exit(1 if differ else 0)
    finally:
        shutil.rmtree(scratch, ignore_errors=True)
        if keep != arguments.keep and not any(keep.iterdir()):
            keep.rmdir()


if __name__ == "__main__":
    main()
