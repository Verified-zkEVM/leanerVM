# Test vectors

Proofs written by leanerVM's honest prover (`LeanerVM.Protocol.Prove`), each with its program and
public input, in the text format of [`scripts/dump-proof-rust.sh`](../../scripts/dump-proof-rust.sh),
which the Rust fixture's loader reads (`LeanerVMTests.Protocol.RustProof.load`). Stored compressed
(`gzip -9 -n`); the plain file is 363 KB.

| File | Witness | Sizes | Proof |
| --- | --- | --- | --- |
| `fill.proof.gz` (141 KB) | the constraint statement tests' `fillW 1 g memCnt`: `mul_192bit_word` with its fill blocks, program `fillProg` (32 instructions), public input `mulInput` | memory `2^16`, tables `2^0, 2^0, 2^1, 2^0, 2^2, 2^3`, a stack of `2^19` cells, WHIR rate `1/2` | 747 scalars; three openings of 223, 56 and 32 rows with 1168, 353 and 197 siblings |

The witness is hand-built and proved to satisfy the constraint statement
(`fill_satisfiedBy`, `tests/LeanerVMTests/Arithmetization/Statement.lean`); its sizes are the
smallest the setup admits.

## Generating and checking

```sh
lake build leanervm-prove leanervm-verify
.lake/build/bin/leanervm-prove tests/vectors/fill.proof 1   # prove, write, read back, verify, mutate
gzip -9 -n -f tests/vectors/fill.proof
gunzip -k tests/vectors/fill.proof.gz
.lake/build/bin/leanervm-verify 1 tests/vectors/fill.proof  # verify and the mutations, on the file
```

`leanervm-prove` checks that `verify` accepts the proof it writes, rejects each mutation of
`LeanerVMTests.Protocol.Verify.mutationsOf` at the stage it names, and rejects the honest wire
with one message changed in each front phase and in WHIR at that phase (`frontChecksOf`,
`whirChecksOf`); `leanervm-verify` makes the same checks on the file; `leanervm-prove tamper` runs
the prover with one front phase's message changed and checks that each proof is read to its end
and rejected by that phase (recorded in `bench/README.md`); with a fourth argument `pure` it
also runs `prove` itself, in `Id`, and checks it returns the same proof. The prover is
deterministic: two runs write the same plain file. On every pull request to `main` the
`Executables` workflow (`.github/workflows/executables.yml`) runs `leanervm-verify` on the Rust
proof and on the committed file, and `leanervm-prove` without `pure`, comparing its proof with the
committed one; it also runs `leanervm-prove log`, `tamper`, `m3` and `sentinel`. The compressed
file also depends on the `gzip` version; compare the decompressed files.

## Differences from the Rust prover's dumps

- The first line is `leanvm-proof leanerVM`, where the Rust dump names its pin; the loader reads
  any tag.
- The program is printed with each operand as its exponent `j` of `g^j`, searched below `2^12`;
  the Rust prints the compiler's operands the same way.
- The witness is not the Rust's: the Rust builds its witness from an execution of the program,
  here it is given. The stream is the same function of the oracle protocol's honest messages and
  the chain; the two provers agree on a proof only where their witnesses and honest messages
  agree.
- The grinding nonce is the smallest that clears the bits, as the Rust's parallel search returns,
  but searched within a fuel of candidates (default `2^24`). A grind of 17 bits tries `2^17`
  candidates on average; for a random function the search fails with probability
  `(1 − 2^-17)^(2^24) ≈ e^-128` per level. At BLAKE2s a failing input cannot be excluded, and
  `prove` then returns no proof. The Rust's search is unbounded over `u64`.
- The openings are written after the stream in level order, from the commitments kept; the Rust
  hands each level's opening to the proof as it opens it. The proof's opening list is the same.

## Executions of compiled programs

`executions/*.exec.gz` are runs of compiled leanVM programs by the Rust executor at leanVM
`a386121f84292f6fa663aaa3e570c15bc0240ea2` (`Program::execute_to_floor`, the run `prove` makes),
written by [`scripts/dump-execution-rust.sh`](../../scripts/dump-execution-rust.sh), whose header
gives the format: the program, the public input, the final memory image, the main-run and total
row counts, the Rust prover's committed-size floor, and every table row `(pc, fp)`. `leanervm-witgen` (`bench/LeanerVMWitgen.lean`) reads
them into `Program`, `PublicInput` and `Trace prog` and checks them against the reference
semantics; they are the inputs of the witness generator's end-to-end runs.

| File | Program | Bytecode | Memory | Main steps | Rows after the fill (XOR, MUL, SET, DEREF, JUMP, BLAKE2S) |
| --- | --- | --- | --- | --- | --- |
| `field_div` | the division test (`lean_compiler/tests/suite/field_div.rs`), the program of `scripts/dump-proof-rust.sh` | `2^11` | `2^17` | 13 | 1, 8, 8, 2, 16, 8 |
| `hash_chain_8` | eight chained compressions (`rec_aggregation/src/hash_chain.rs`) | `2^11` | `2^17` | 66 | 2, 8, 32, 32, 16, 8 |
| `py_*` | the fifteen programs of `lean_compiler/tests/programs`, with their annotated inputs | `2^11` | `2^17` | 10 to 198 | at most 16, 32, 64, 128, 64, 8 |
| `fibonacci_1000` | Fibonacci in the exponent (`rec_aggregation/src/fibonacci.rs`), `n = 1000` | `2^12` | `2^17` | 1031 | 1, 1024, 8, 16, 16, 8 |
| `fibonacci_20000` | the same, `n = 20000` | `2^12` | `2^17` | 20336 | 32, 32768, 128, 256, 256, 8 |

Every program has its 48 fill blocks, every run reads no unwritten cell, and memory is `2^17`
because the fill frames start at `2^16`. The recursion guest on one XMSS signature
(`scripts/dump-execution-rust.sh -g`: bytecode `2^19`, memory `2^17`, 5725 main steps, SET filled
to `2^17` rows by the `2^22` committed floor) is 1.7 MB compressed and is regenerated, not
checked in.

```sh
scripts/dump-execution-rust.sh -f 1000 -f 20000 <leanVM checkout> tests/vectors/executions
lake build leanervm-witgen
.lake/build/bin/leanervm-witgen tests/vectors/executions/*.exec.gz
```

The Rust writes the files deterministically; compare decompressed files.
