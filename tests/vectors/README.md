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

`leanervm-prove` checks that `verify` accepts the proof it writes and rejects each mutation of
`LeanerVMTests.Protocol.Verify.mutationsOf` at the stage it names; with a fourth argument `pure` it
also runs `prove` itself, in `Id`, and checks it returns the same proof. The prover is
deterministic: two runs write the same file.

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
  but searched within a fuel of candidates (default `2^24`).
- The openings are written after the stream in level order, from the commitments kept; the Rust
  hands each level's opening to the proof as it opens it. The proof's opening list is the same.
