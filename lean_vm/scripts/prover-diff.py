"""Differential test of the statement's honest prover against the Lean and the Rust verifier.

For every case directory (scripts/export-prover-traces-rust.sh writes them: a program's bytecode,
its public input, an execution's memory and `trace.txt`, and the Rust prover's proof of it), this

  1. runs `lake exe leanvm-prove` (cli/LeanvmProve.lean: `LeanVM.Prover.prove` with Keccak-256
     and Keccak-f[1600], the statement's prover compiled) on the case, timing it, and sets the
     time beside the Rust prover's (`rust.txt`);
  2. checks that the Lean-made proof is byte-identical to the Rust prover's (reported, not
     required: the Rust prover may change its encoding without changing the statement);
  3. writes the Lean-made proof as a verifier fixture (bytecode, public input, stream, openings)
     and runs scripts/fuzz-verifier.py on the fixtures: the Lean verifier (`leanvm-verify`) and
     the Rust verifier (`scripts/rust-verifier-cli`) on the honest Lean-made proof and on
     `--mutations` mutations of it, structured and random.

It fails unless every Lean-made proof is accepted by both verifiers and every mutation is
rejected by both (and the two verifiers agree everywhere).

Usage (the three executables built first, see lean_vm/README.md):
  python3 -I scripts/prover-diff.py <cases dir> [--mutations 60] [--fuel N] [--jobs 4] [case ...]
"""

import argparse
import resource
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PROVE_EXE = ROOT / ".lake" / "build" / "bin" / "leanvm-prove"
FILES = ("bytecode.bin", "public_input.bin", "stream.bin", "merkle_openings.bin")


def limit(gigabytes: int):
    def apply():
        size = gigabytes << 30
        resource.setrlimit(resource.RLIMIT_AS, (size, size))
        resource.setrlimit(resource.RLIMIT_STACK, (resource.RLIM_INFINITY, resource.RLIM_INFINITY))
    return apply


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("cases", type=Path)
    parser.add_argument("only", nargs="*")
    parser.add_argument("--mutations", type=int, default=60, help="fuzz cases per proof, the honest one included")
    parser.add_argument("--fuel", type=int, help="nonces per proof of work (default: the prover's 2^25)")
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--memory-gb", type=int, default=16)
    parser.add_argument("--prove-exe", type=Path, default=PROVE_EXE)
    arguments = parser.parse_args()
    if not arguments.prove_exe.exists():
        sys.exit(f"{arguments.prove_exe} is not built (lake build leanvm-prove)")
    cases = arguments.cases.resolve()
    names = arguments.only or sorted(p.name for p in cases.iterdir() if (p / "trace.txt").exists())
    fixtures = Path(tempfile.mkdtemp(prefix="prover-diff-"))
    rows = []
    failed = False
    try:
        for name in names:
            directory = cases / name
            command = [str(arguments.prove_exe), str(directory)]
            if arguments.fuel is not None:
                command.append(str(arguments.fuel))
            start = time.monotonic()
            run = subprocess.run(command, capture_output=True, text=True,
                                 preexec_fn=limit(arguments.memory_gb))
            seconds = time.monotonic() - start
            if run.returncode != 0:
                print(f"{name}: leanvm-prove failed ({run.returncode}): {run.stdout}{run.stderr}")
                failed = True
                continue
            rust = (directory / "rust.txt").read_text().strip() if (directory / "rust.txt").exists() else "-"
            identical = all(
                (directory / f"lean_{f}").read_bytes() == (directory / f).read_bytes()
                for f in ("stream.bin", "merkle_openings.bin") if (directory / f).exists())
            target = fixtures / name
            target.mkdir()
            for f in ("bytecode.bin", "public_input.bin"):
                shutil.copy(directory / f, target / f)
            for f in ("stream.bin", "merkle_openings.bin"):
                shutil.copy(directory / f"lean_{f}", target / f)
            rows.append((name, f"{seconds:.1f}", rust, "yes" if identical else "no"))
            print(f"{name}: Lean prover {seconds:.1f} s, Rust prover {rust} s, "
                  f"identical to the Rust proof: {'yes' if identical else 'no'}", flush=True)
        if not rows:
            sys.exit("no proof to test")
        log = fixtures / "fuzz.log"
        fuzz = subprocess.run([sys.executable, "-I", str(ROOT / "scripts" / "fuzz-verifier.py"), str(fixtures),
                               "--mutations", str(arguments.mutations), "--jobs", str(arguments.jobs),
                               "--memory-gb", str(arguments.memory_gb), "--log", str(log)])
        if fuzz.returncode != 0:
            failed = True
        accepted = rejected = 0
        bad = []
        for line in log.read_text().splitlines():
            fields = line.split("\t")
            fixture, index, category, label, lean, _, rust = fields[:7]
            both_accept = lean == "accept" and rust == "accept"
            both_reject = lean != "accept" and rust != "accept"
            if category == "honest":
                accepted += both_accept
                if not both_accept:
                    bad.append(f"honest proof of {fixture} not accepted: Lean {lean}, Rust {rust}")
            else:
                rejected += both_reject
                if not both_reject:
                    bad.append(f"{fixture} #{index} {label}: Lean {lean}, Rust {rust}")
        print(f"\nLean-made proofs accepted by both verifiers: {accepted} of {len(rows)}; "
              f"mutations rejected by both: {rejected}")
        print("\ncase                 Lean prover s  Rust prover s  identical")
        for row in rows:
            print(f"{row[0]:20} {row[1]:>13}  {row[2]:>13}  {row[3]:>9}")
        for b in bad:
            print("FAIL", b)
        sys.exit(1 if failed or bad or accepted != len(rows) else 0)
    finally:
        shutil.rmtree(fixtures, ignore_errors=True)


if __name__ == "__main__":
    main()
