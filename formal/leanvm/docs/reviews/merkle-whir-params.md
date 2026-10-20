# Review: Merkle trees, the byte hasher and the WHIR parameters (PR #67)

Adversarial review of branch `feat/protocol-merkle-whir-params` at `main` + 1 commit, run on
2026-10-01 with the three passes of the `adversarial-review` skill: fidelity against the pinned
leanVM `a386121f84292f6fa663aaa3e570c15bc0240ea2` first, then the specifications, then hygiene.
Every suspicion below was executed before it was written down.

## Findings, most severe first

### 1. `merkleVerify` fixes neither the depth nor the leaf width (defect)

`LeanerVM/Protocol/ToArkLib/Merkle.lean:87` (`MerkleTree.verify`) and
`LeanerVM/Protocol/Merkle.lean:53` (`merkleVerify`). The check climbs whatever path it is given
from whatever index it is given. Two accepted inputs on the four-leaf tree of the test file,
with `root`, `path2 = [leaf3, node01]` and `node01` as there:

- `merkleVerify root 6 [w 5, w 6] path2 = true`, and index `10` likewise: the index is read
  modulo `2^depth` through `i / 2`. The pinned opener rejects `p >= num_leaves`
  (`crates/fiat_shamir/src/merkle.rs:184-186`).
- `merkleVerify root 1 fake [node01] = true`, where `fake` is the eight-word row whose bytes are
  `digest(leaf 2) ‖ digest(leaf 3)`: `hash_words` on 64 bytes and `hash_pair` are the same
  function, so the row hashes to the internal node and a one-element path reaches the root.
  The pinned opener fixes the path length by `height = num_leaves.trailing_zeros()` and the
  row width by `row.len() == row_words` and `row_words <= leaf_words`
  (`merkle.rs:147, 176-182`), so neither shortcut exists for a Rust prover.

A compiled verifier built on `merkleVerify` as it stands would have to add both checks itself,
and nothing in the module says so. The master theorems would catch the omission only through
the hypothesis `hl : p.length = p'.length` of `collision_of_verify`, which is exactly the
missing check. Fix: `MerkleTree.verify (k : ℕ) root i leaf path` deciding
`path.length = k ∧ i < 2 ^ k ∧ rootOfPath … = root`; `merkleVerify (depth leafWords : ℕ) …`
adding `leaf.length = leafWords`; `verify_path` unchanged in content; `collision_of_verify`
drops `hl`; both accepted inputs above become rejected mutations in
`tests/LeanerVMTests/Protocol/Merkle.lean`.

### 2. `leafImage` is total where the Rust is partial (defect, low)

`LeanerVM/Protocol/Merkle.lean:40`. `leafImage 2 [w 1, w 2, w 3] = [w 1, w 2, w 3]`: a row longer
than the leaf width comes back unchanged and longer. `leaf_image` (`merkle.rs:54-58`) would
underflow, and the opener rejects the width first. Subsumed by the width check of finding 1,
which should come with a test that the over-long row is rejected.

### 3. The out-of-domain count is pinned by the Rust test for sizes 22 to 28 only (observation)

`LeanerVM/Parameters/Whir.lean:88-91`, the docstring of `oodSamples`, cites
`whir_config.rs:1021, 1033`. That test loops `m` from `22 + LOG_PACKING` to `28 + LOG_PACKING`,
so it fixes one sample per later level for stack sizes 22 to 28 only. For 15 to 21 the evidence
is the Python verifier, which takes exactly one sample per non-final level
(`verifier.py:1033-1037`) and must agree with the prover for its query table to be usable. The
docstring should say which source covers which sizes.

### 4. Two Rust parameters are implicit (observation)

`LeanerVM/Parameters/Whir.lean`. The Rust API takes `m = μ + LOG_PACKING` with `LOG_PACKING = 6`
(`crates/pcs/src/pack.rs:7`), while `ladder` takes `μ` as the Python `derive_config` does; a
reader comparing with `derive_config_with_log_inv_rate` needs that sentence. `LOG_INV_RATE_0 = 1`
(`whir_config.rs:41`), the rate the Rust test suite proves at, is not transcribed; it is not a
verifier parameter, since the rate is read from the statement, and the docstring could say so.

### 5. Binding is stated for the abstract hashes (observation)

`LeanerVM/Protocol/ToArkLib/Merkle.lean:131-134`, `collision_of_verify`, and its instance
`collision_of_merkleVerify`. The conclusion is a collision of `hashWords` or `hashPair`, not of
`blake2sBytes`; the step is the injectivity of the two byte encodings on equal-length inputs,
which the PR body leaves to the compiler layer. Once finding 1 fixes the leaf width, a
`LeafCollision hashWords` on two rows of the same width is a `blake2sBytes` collision on two
distinct byte strings of equal length, the form a collision-resistance assumption consumes.

### 6. Hygiene

- `LeanerVM/Parameters/Whir.lean:130`: 101 characters.
- `LeanerVM.Parameters.Whir.Admissible` will sit beside the adaptor's `Sizes.Admissible`
  (Layer 3 of the blueprint); different namespaces, but the adaptor should consume
  `minLogStack` and `maxLogStack` rather than restate 15 and 28.
- The blueprint's Layer 11 sketch names `LeanerVM/Parameters/Blake2sHash.lean`; the module landed
  in `LeanerVM/Protocol/` because it is built over `compress` from `LeanerVM/Semantics/` and the
  layer DAG forbids the import. The PR body records it; a `docs(protocol)` follow-up should
  move the name in the blueprint.

Otherwise clean: no forbidden token (`./scripts/audit-lean.sh`), no comment naming a layer,
hole, ledger or finding, declaration docstrings of one to three lines, module docstrings
carrying the pin and line ranges, no dead code, all theorems closing on `propext`,
`Classical.choice`, `Quot.sound`.

## Pass B: fidelity against the pin

Read before the Lean, in this order: `crates/primitives/src/hash.rs`,
`crates/fiat_shamir/src/merkle.rs`, `crates/pcs/src/merkle.rs`, `crates/pcs/src/whir_config.rs`,
`crates/lean_vm/src/pcs.rs`, `python-verifier/verifier.py:897-1075`.

**Byte hasher** (`hash.rs:66-224`), seven behaviours, seven matched: parameter block
`0x01010020` into word 0; counter low and high words into `v[12]`, `v[13]` (in `compress`,
reviewed with leanISA Layer 1); last-block flag as `!v[14]`, which is XOR with `0xFFFFFFFF`;
last-node flag never set; `block_words` and `state_bytes` little-endian; streaming with every
non-final block at the byte count including it and the final block at the total length; the
empty message as one zero block at counter 0. The whole-blocks fast path (`hash.rs:212-220`) is
checked equal to the streaming path at 64 bytes. Vectors are CPython's `hashlib.blake2s`, which
is standard BLAKE2s-256, as `init_state(0)` is, at 0, 3, 64, 65 and 128 bytes.

**Digest encoding** (`merkle.rs:14-36`), three of three: halves at bytes 0 and 16, each the two
little-endian 64-bit words as limbs 0 and 1 with limb 2 zero; the decoder rejects a nonzero
limb 2 and nothing else.

**Merkle** (`merkle.rs:40-67, 254-263`; `pcs/merkle.rs:119-142`): leaf hash is BLAKE2s of the
words as little-endian bytes; node hash is BLAKE2s of the 64 bytes left then right; the zero
prefix of `leaf_image`; `RawMerklePath::root` with the running node on the left at an even
index; the tree pairs adjacent nodes left first. Of the opener's seven checks (`open`,
`merkle.rs:160-230`: power-of-two leaf count, nonempty queries, row count, row width, index
range, exact sibling count, root match) the single-path `merkleVerify` carries the root match
and, through the path it is handed, the sibling count; the index range, the depth and the row
width are finding 1. The pruned octopus is deferred to the proof object, as the PR says.

**WHIR parameters** (`whir_config.rs:38-92, 260-311`; `pcs.rs:49-51`; `verifier.py:900-935`):
eleven Rust constants, ten transcribed plus `oodSamples`; `LOG_INV_RATE_0` and
`JOHNSON_ETA_SEARCH_MAX_M` are not (finding 4; the second is search-only). The ladder geometry
is `derive_ladder` with `derive_ladder_shape`'s rate rule and the Python `derive_config`,
checked over all 56 admissible pairs by a script; the 56-entry query table equals the
`WHIR_QUERIES` line by a programmatic diff; `blockLogs` is `message_log + level_rate`
(`verifier.py:1040`). The query counts remain the Rust's floating-point output, not re-derived.

## Pass A: specifications

Every theorem was instantiated: the Merkle theorems on the four-leaf tree, the ladder facts at
`(15, 1)`, `(16, 1)`, `(28, 4)`, the encoding round trips on the `"abc"` digest. None is
vacuous. `collision_of_verify` is substantive, since dropping `hl` makes it false
(finding 1 is the witness). `ladder_isSome` fails on a table row one entry short and
`ladder_blocks` on a count above a block length, so the decided facts pin the table rather
than restate it. `blake2sBytes` and the tree are pinned against an object defined outside the
Lean (hashlib), not against their own definitions.

Target classification: the PR names Category B per module, ledger A7 and the T4 obligation
through Layer 12's `verify`; no T1 to T8 theorem is claimed and none is implied. Not overstated.

## Pass C: hygiene

Finding 6 only. Imports are narrow and `public` where a signature needs them; exported
declarations sit in `@[expose] public section` as in the sibling `To*` modules; the test files
are plain so the kernel can decide hash equalities.

## What the review could not do

The Rust was not executed, so the query counts and the out-of-domain count at sizes 15 to 21
rest on the Python verifier's transcription of the Rust's output (finding 3).

## Applied

All six findings were applied on the branch the same day: `MerkleTree.verify` takes the depth
and `merkleVerify` the depth and the leaf width, `collision_of_verify` and
`collision_of_merkleVerify` lost the path-length hypothesis, `merkleVerify_merklePath` takes
the leaf's width; the two accepted inputs of finding 1, the over-wide row of finding 2, a wrong
depth and the hash-level fact behind the node-as-leaf opening are tests in
`tests/LeanerVMTests/Protocol/Merkle.lean`; the docstrings of findings 3, 4 and 6 were revised.
