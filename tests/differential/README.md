# Differential tests of the two verifiers

Two tools hand the same proofs to leanerVM's executable verifier and to the pinned Rust leanVM
verifier (`lean_vm::cpu::verify`, `crates/lean_vm/src/cpu/mod.rs:711` at
`a386121f84292f6fa663aaa3e570c15bc0240ea2`) and compare their verdicts:
[`fuzz.py`](fuzz.py) mutates whole proof files, [`tamper-sweep.py`](tamper-sweep.py) changes one
prover message at a time. Both are standard-library Python, run with `python3 -I`, and run every
oracle process under `systemd-run --user --scope` with a memory cap when `systemd-run` exists
(`--memory`, `0` for none). Agreement they observe is implementation evidence about the Rust
verifier, not a proof about its source.

A proof is a statement (program, public input) with its scalar stream and Merkle openings, in the
text format of [`scripts/dump-proof-rust.sh`](../../scripts/dump-proof-rust.sh). The two oracles
answer one line per file, `<file>\t<verdict>\t<detail>\t<microseconds>`:

- Lean: `leanervm-check serve` ([`bench/LeanerVMCheck.lean`](../../bench/LeanerVMCheck.lean)):
  `ACCEPT`, `REJECT` or `PARSEFAIL`, or `INCONSISTENT` when `verify` and `outcomeAt` disagree; the
  detail is the stage `outcomeAt` names.
- Rust: `proof-check serve` ([`tests/rust/proof_check.rs`](../rust/proof_check.rs)): `ACCEPT`,
  `REJECT` (the detail is the verifier's error), `PARSEFAIL` or `PANIC` (caught; the detail is
  its message). A program with an operand exponent above `2^24` is `PARSEFAIL` without being
  assembled: `bytecode_columns` (`crates/lean_vm/src/cpu/layout.rs:229-241`) allocates a power of
  `g` per exponent up to the largest, 32 GiB at `2^32 - 1` (`PROOF_CHECK_MAX_OPERAND` moves the
  cap).

Neither verifier reads the file's program hash; both append `;hashmismatch` to the detail when it
is not the program's, and the mutations never recompute it.

A divergence is one verifier accepting a proof the other rejects. A panic, a crash, a hang, or a
Lean `INCONSISTENT` is a finding on its own; so is a changed proof both accept, unless the change
only respells it (below).

## Building the oracles

```sh
lake build leanervm-check leanervm-prove
python3 scripts/check-proofs-rust.py <leanVM checkout> --build-only   # prints proof-check's path
```

`fuzz.py` and `tamper-sweep.py` take the Rust binary as `--rust <path>`, or build it themselves
from `--leanvm <leanVM checkout>` through that script; the Lean binaries default to
`.lake/build/bin/`.

## `fuzz.py`

```sh
F="python3 -I tests/differential/fuzz.py"
$F selftest                                   # round trips, determinism, classification
$F list                                       # the mutation catalog
$F enumerate --leanvm <checkout> --workers 4 --reps 2
$F run --leanvm <checkout> --minutes 20 --workers 4 --rng 7
$F replay --rust <proof-check> .lake/differential/findings/<file>.proof
$F mutate --seed .lake/differential/seeds/fill.proof --mutation pub.swap --rng 0 -o m.proof --check
```

- Seeds: by default the Lean prover's vector [`tests/vectors/fill.proof.gz`](../vectors/README.md)
  (`fill`) and the pinned Rust prover's proof embedded in
  `tests/LeanerVMTests/Protocol/RustProofData.lean` (`field_div`); `--seeds` takes others, plain
  or gzip. They are copied, plain, to `<out>/seeds/`. Both oracles must accept every seed; the
  runner checks that first.
- `enumerate` runs every catalog mutation on every seed, `--reps` times with rng seeds
  `rng * 1000 + r`, and the cross-statement mutations against the next `--cross-limit` seeds.
- `run` draws a seed, a mutation (havoc with probability `--havoc`, else a family uniformly and a
  mutation in it uniformly) and a 48-bit rng seed per mutant, for `--minutes`.
- A mutant is a function of (seed, mutation, rng seed); each logged finding carries the `mutate`
  command that regenerates it.
- `--workers N` runs N lanes, each one Lean and one Rust `serve` process. A process that dies is
  restarted and the input is a `CRASH`; no answer within `--timeout` seconds is a `HANG`.

The work directory `--out` (default `.lake/differential/`, ignored by Git) holds `seeds/`,
`work/` (mutants in flight), `findings/` (kept mutants), `findings.jsonl` (one record per notable
mutant, appended across runs, at most 50 per class and mutation), `logs/` (worker stderr) and
`summary-<mode>.{txt,json}` (per family and per mutation class counts, verdict pairs, and the
pairs of rejecting stages, Lean's against Rust's error, as a coverage proxy).

### Mutations

| Family | Mutations | What it probes |
| --- | --- | --- |
| `pub` | each limb of each public element set to zero, one, small, all ones, random, or one bit flipped; `pub.swap`, `pub.copy01`, `pub.copy10` | the public input, its third limbs included |
| `prog` | an operand plus or minus one, random, or `>= 2^32`; `xor`/`mul` swapped; a deref mode; a `set` limb; two ops swapped; an op made `xor 0 0 0`; the length changed off and on a power of two | the program as a verifier input |
| `stream` | scalars appended, dropped, inserted or deleted at the head; each limb of the first ten scalars (the eight announced sizes and rate, then the setup digest); a bit of a tail or random scalar; extension limbs on base-field scalars; adjacent scalars swapped | the scalar stream |
| `merkle.phase` | an empty, junk or copied phase added; one dropped; phases swapped, reversed, split, merged | the list of openings |
| `merkle.rows`, `merkle.sibs` | rows or siblings duplicated, dropped, swapped, shuffled, emptied, appended, moved to the next phase | each opening's rows and siblings |
| `merkle.row`, `merkle.rowsall` | words prepended, appended or stripped, a row emptied, a bit flipped, a top bit set, in one row or every row of a phase | the width of the opened rows |
| `cross` | `cross.{program,public,both}@<seed>` | one seed's proof under another seed's statement |
| `havoc` | two to four of the above composed, the chain logged | combinations |
| `text`, `rate` | an operand respelled (plus the order of `g`, a leading zero, a `_` separator), a public limb in 17 digits, the header tag, the header rate line | the loaders only |

The printer writes every count from the lists, so a count changes only with the list it counts.
Havoc draws no `text`, `rate` or self-cross mutation: each can leave the proof unchanged.

### Classes

| Class | Verdicts | Kept |
| --- | --- | --- |
| `DIVERGENCE` | one `ACCEPT`, the other `REJECT` or `INCONSISTENT` | 20 per mutation |
| `PANIC`, `CRASH`, `HANG`, `INCONSISTENT` | as above | 20 per mutation |
| `MALLEABLE` | both accept a mutant that differs from the seed | 1 per mutation |
| `PARSEFAIL-ASYM` | one loader refuses the file, the other verifier answers | 1 per mutation |
| `REJECT` | both reject or both refuse | none |
| `NOOP`, `N/A` | the mutant is the seed's text / the mutation does not apply; not run | none |

The two loaders read different languages, so some classes are expected. Lean's
(`LeanerVMTests.Protocol.RustProof.load`) reads hexadecimal words of any length modulo `2^64`,
lower case only, decimals with `_` separators, and an operand as any natural `j` naming `g^j`;
`proof-check`'s reads one to sixteen digits of either case and `u32` operands. So `text`
mutations end `MALLEABLE` or `PARSEFAIL-ASYM`, and `rate` mutations `MALLEABLE` (both verifiers
read the rate from the stream). Lean refuses a nonzero third public limb, which the Rust verifier
rejects (`crates/lean_vm/src/cpu/mod.rs:141`), and `proof-check` refuses an operand above its cap:
`PARSEFAIL-ASYM` with no acceptance. Each table ends with the count needing a look: every
`DIVERGENCE`, `PANIC`, `CRASH`, `HANG` and `INCONSISTENT`, and every `MALLEABLE` or
`PARSEFAIL-ASYM` with an `ACCEPT` outside the `text` and `rate` families; `enumerate` and `run`
exit nonzero when it is not zero.

### The 2026-10-26 campaign

What was compared: 30 honest proofs. These are the Lean vector (bytecode 32, memory `2^16`) and
29 proofs from the pinned Rust prover: its 15 test programs, `filler.rs` loops, BLAKE2s tables up
to `2^8`, memory `2^17` and `2^20`, bytecode 2048, and `field_div` at rates 1 to 4 (the others at
rate 1). Each verifier accepts every one of them.

- **Mutants.** About 35 000 structural, statement and havoc mutants gave no divergence, panic,
  crash, hang or inconsistency. Every difference was in the loaders: the Lean loader then dropped
  a nonzero third public limb (it now refuses it), the respellings above, and two havoc chains
  through `rate.zero`, which havoc no longer draws. That campaign drove an out-of-tree Rust
  harness whose loader read Lean's language; `proof-check` reads the stricter one above.
- **Lean tamper sweep.** All 747 offsets × 3 deltas on the vector: every changed proof is
  rejected by both. The 17 no-op offsets are the announced sizes, the roots and the grinding
  nonces, which the Lean prover does not write through `send`.
- **Rust tamper sweep.** A hooked copy of the pinned Rust prover covered those paths too. It
  wrote 9 342 single-message tampers, every offset × 3 on four programs (`field_div` at rates 1
  and 3, a `2^8` BLAKE2s table, `match_arms`), plus 36 on a five-level WHIR ladder. It also wrote
  pair tampers that keep the public-input combination check true, which both verifiers reject at
  the opening. Every one was rejected by both.
- **Sentinel slot.** The pinned Rust prover proved programs whose never-executed last slot
  carries operands up to `2^28`, or a `JUMP`. Both verifiers accept these proofs. A `JUMP` there
  is outside the `SentinelSafe` premise of the execution-level headline.

What it did not test:
- wrong-witness proofs (a committed value changed and the prover honest after);
- shapes outside those listed;
- byte-level (serde) proof encodings.

The agreement is implementation evidence at one pin, not a proof.

## `tamper-sweep.py`

```sh
python3 -I tests/differential/tamper-sweep.py <out> --leanvm <checkout> --jobs 8
python3 -I tests/differential/tamper-sweep.py <out> --rust <proof-check> --offsets 0-99 --deltas y2
```

For each stream offset (`--offsets`, default all) and delta (`--deltas`, `1`, `y`, `y2`: one
added to the first, second or third limb), `leanervm-prove tamper-at` writes the vector's proof
with the delta added to the scalar sent at that offset, the prover running on, so the proof is
consistent with the Fiat–Shamir chain and wrong at one message; then both verifiers judge it.
`<out>/results.tsv` gets one line per pair: offset, delta, class, Lean's verdict and stage,
Rust's verdict and detail. The class is `NOOP` when the proof is byte-identical to the untampered
one (offsets the prover does not write through the tampered `send`, such as the announced sizes at
offsets 0 to 9), `PROVEFAIL`, `REJECT`, `DIVERGENCE`, or `ACCEPT` (both accept a changed proof).
Proofs are kept under `<out>/proofs/` only when a verifier accepts them; a rerun skips the pairs
already in `results.tsv`. Each prover run takes about a minute and 1 GiB. The script exits
nonzero on a `DIVERGENCE`, an `ACCEPT` or a `PROVEFAIL`.
