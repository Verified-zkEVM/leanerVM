#!/usr/bin/env python3
"""Transcript-consistent tampering, checked by both verifiers.

For each stream offset and delta, `leanervm-prove tamper-at` writes the proof of the test vector's
witness with the delta added to the scalar sent at that offset, the prover running on: the proof
is consistent with the Fiat-Shamir chain and wrong at one message. `leanervm-check` and the pinned
Rust verifier (`proof-check serve`, tests/rust/proof_check.rs) each give a verdict.

Writes <out>/results.tsv, one line per (offset, delta):
  offset  delta  class  lean-verdict  lean-stage  rust-verdict  rust-detail
The class is NOOP (the proof is byte-identical to the untampered one: the prover does not send
that scalar through the tampered `send`), PROVEFAIL (the prover returned no proof), REJECT (both
reject), DIVERGENCE (one accepts) or ACCEPT (both accept a changed proof). A proof is kept under
<out>/proofs/ only when a verifier accepts it. A rerun skips the pairs results.tsv already holds.
Exits nonzero on a DIVERGENCE, an ACCEPT or a PROVEFAIL. Standard library only.
"""

import argparse
import os
import shutil
import subprocess
import sys
import threading
from collections import Counter
from concurrent.futures import ThreadPoolExecutor

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
BIN = os.path.join(ROOT, ".lake/build/bin")
NEVER = str(10 ** 12)  # an offset past every stream: `tamper-at` there writes the honest proof


def offsets(spec, n):
    """`0-9,20,30-39` as a sorted list; `all` is every offset below n."""
    if spec == "all":
        return list(range(n))
    out = set()
    for part in spec.split(","):
        a, _, b = part.partition("-")
        out.update(range(int(a), int(b or a) + 1))
    return sorted(out)


class Sweep:
    def __init__(self, args):
        self.args = args
        self.scope = (["systemd-run", "--user", "--scope", "-q", "-p", f"MemoryMax={args.memory}",
                       "-p", "MemorySwapMax=0"]
                      if args.memory != "0" and shutil.which("systemd-run") else [])
        self.lock = threading.Lock()
        self.counts = Counter()

    def run(self, argv, timeout, stdin=None):
        """The command's standard output, or None when it fails or times out."""
        try:
            r = subprocess.run(self.scope + ["timeout", str(timeout)] + argv, input=stdin,
                               capture_output=True, text=True)
        except OSError:
            return None
        return r.stdout if r.returncode == 0 else None

    def prove(self, path, off, delta):
        a = self.args
        return self.run([a.prove, "tamper-at", path, str(off), delta, str(a.rate)],
                        a.prove_timeout) is not None

    def verdicts(self, path):
        """(lean verdict, lean stage, rust verdict, rust detail)."""
        t = self.args.check_timeout
        lean = self.run([self.args.check, path], t)
        rust = self.run([self.args.rust, "serve"], t, stdin=path + "\n")
        fields = []
        for line in (lean, rust):
            f = (line or "").rstrip("\n").split("\t")
            fields += f[1:3] if len(f) >= 3 else ["NOANSWER", "-"]
        return fields

    def one(self, reference, off, delta, results):
        a = self.args
        path = os.path.join(a.out, "proofs", f"t{off}_{delta}.proof")
        if not self.prove(path, off, delta):
            row = ["PROVEFAIL", "-", "-", "-", "-"]
        else:
            with open(path) as f:
                same = f.read() == reference
            if same:
                row = ["NOOP", "-", "-", "-", "-"]
            else:
                lv, ls, rv, rd = self.verdicts(path)
                acc = (lv == "ACCEPT", rv == "ACCEPT")
                cls = "ACCEPT" if all(acc) else "DIVERGENCE" if any(acc) else "REJECT"
                row = [cls, lv, ls, rv, rd]
            if row[0] in ("NOOP", "REJECT"):
                os.remove(path)
        line = "\t".join([str(off), delta] + row)
        with self.lock:
            self.counts[row[0]] += 1
            with open(results, "a") as f:
                f.write(line + "\n")
            print(line, flush=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("out", help="output directory (results.tsv, proofs/)")
    ap.add_argument("--offsets", default="all", help="e.g. 0-99,500 (default: every offset)")
    ap.add_argument("--deltas", default="1,y,y2",
                    help="comma-separated: 1, y, y2 add one to the first, second, third limb")
    ap.add_argument("--rate", type=int, default=1)
    ap.add_argument("--jobs", type=int, default=4, help="proofs in parallel (about 1 GiB each)")
    ap.add_argument("--prove", default=os.path.join(BIN, "leanervm-prove"))
    ap.add_argument("--check", default=os.path.join(BIN, "leanervm-check"))
    ap.add_argument("--rust", help="the proof-check binary")
    ap.add_argument("--leanvm", help="a leanVM checkout at the pin, to build proof-check from")
    ap.add_argument("--memory", default="3G",
                    help="MemoryMax of each process under systemd-run (0: no scope)")
    ap.add_argument("--prove-timeout", type=int, default=900, help="seconds per proof")
    ap.add_argument("--check-timeout", type=int, default=300, help="seconds per verdict")
    args = ap.parse_args()
    args.out = os.path.abspath(args.out)
    deltas = args.deltas.split(",")
    if not set(deltas) <= {"1", "y", "y2"}:
        ap.error("a delta is 1, y or y2")
    if args.rust is None and args.leanvm is not None:
        r = subprocess.run([sys.executable, "-I", os.path.join(ROOT, "scripts/check-proofs-rust.py"),
                            args.leanvm, "--build-only"], stdout=subprocess.PIPE, text=True)
        args.rust = r.stdout.strip().splitlines()[-1] if r.returncode == 0 else None
    for name in ("prove", "check", "rust"):
        if not getattr(args, name) or not os.path.exists(getattr(args, name)):
            sys.exit(f"--{name}: {getattr(args, name)} not found (`lake build leanervm-prove "
                     "leanervm-check`; --rust or --leanvm for the Rust verifier)")
    os.makedirs(os.path.join(args.out, "proofs"), exist_ok=True)
    sweep = Sweep(args)
    ref_path = os.path.join(args.out, f"reference-rate{args.rate}.proof")
    if not os.path.exists(ref_path) and not sweep.prove(ref_path, NEVER, "1"):
        sys.exit("the prover failed on the untampered proof")
    with open(ref_path) as f:
        reference = f.read()
    n = next(int(l.split()[1]) for l in reference.splitlines() if l.startswith("stream "))
    results = os.path.join(args.out, "results.tsv")
    done = set()
    if os.path.exists(results):
        with open(results) as f:
            done = {tuple(l.split("\t")[:2]) for l in f if l.strip()}
    todo = [(o, d) for d in deltas for o in offsets(args.offsets, n) if (str(o), d) not in done]
    print(f"{len(todo)} proofs to write ({len(done)} done), stream of {n} scalars", flush=True)
    with ThreadPoolExecutor(args.jobs) as pool:
        for job in [pool.submit(sweep.one, reference, o, d, results) for o, d in todo]:
            job.result()
    print("this run:", ", ".join(f"{c} {k}" for c, k in sorted(sweep.counts.items())) or "nothing")
    bad = sum(sweep.counts[c] for c in ("DIVERGENCE", "ACCEPT", "PROVEFAIL"))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
