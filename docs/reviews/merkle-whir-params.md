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

## Second review (2026-10-19)

Adversarial review of branch `review/whir-67` (the head of pull request #67 with `origin/main`
`9595721` merged in, merge commit `d9a457f`), run on 2026-10-19 with the three passes of the
`adversarial-review` skill, against the pinned leanVM `a386121f84292f6fa663aaa3e570c15bc0240ea2`
read first. The first review's defect (the depth and the leaf width) was checked complete: both
accepted inputs it named are rejected tests, `collision_of_verify` has no path-length hypothesis,
and nothing was found that reopens it. Every claim below was executed before it was written down;
the probe files are named at the end.

**Disposition**:

| Finding | Disposition | Commit |
| --- | --- | --- |
| 1. the collision conclusions are closed propositions | met: `Collision`, `findCollision`, `collision_of_verify` returning the computed collision; `merkleCollision`, `collision_of_merkleVerify`; toy-hash tests | `3b150d2` |
| 2. the row width is the image's, not the row's | met: `merkleVerify` says the image has the leaf width; the module docstring leaves the row checks to the proof decoder and notes the reversed level-0 lanes | `3b150d2` |
| 3. the Johnson slack is not transcribed | met by option (b): `Level` says the slack is not a field and the opening's soundness takes it as a parameter; the blueprint's option (a) is put to the maintainer in the pull request body | `3b150d2` |
| 4. the block bound stops at 64 where the encoders stop at 63 | met: `ladder_blocks` states 63; a test pins the window's largest code, 26 | `3b150d2` |
| 5. the blueprint's Merkle candidate is not named | met in the pull request body (why the tree is local, and where a later fit to VCVio's trees would reuse `findCollision`) | — |
| 6. documentation | met: this review listed in `docs/README.md`; the status page names the modules on merge; the body's classification names the binding statement | this commit |
| 7. hygiene | met: `sibling_lt` private and `div_two_lt` deleted (golf `eba7090`); `absorb` documents its block-count precondition instead of turning private, since the exposed `blake2sBytes` cannot name a private definition; the module docstring names the extractor | `eba7090`, `3b150d2` |

## Findings, most severe first

### 1. The collision conclusions are closed propositions once instantiated (defect in the statement)

`LeanerVM/Protocol/ToArkLib/Merkle.lean:149-152, 171-189` (`PairCollision`, `LeafCollision`,
`collision_of_rootOfPath_eq`, `collision_of_verify`) and `LeanerVM/Protocol/Merkle.lean:71-80`
(`collision_of_merkleVerify`). The conclusion of the binding half,
`LeafCollision hashWords ∨ PairCollision hashPair`, is
`(∃ a b, a ≠ b ∧ hashWords a = hashWords b) ∨ …`, a proposition about the two fixed functions and
nothing else. `hashWords : List K → Digest` has an infinite domain and a finite codomain, so the
left disjunct is a theorem with no hypothesis, by the pigeonhole principle; `hashPair` on
`Digest × Digest` likewise (`2^512` inputs, `2^256` outputs). Executed: the probe proves

```lean
theorem collision_of_merkleVerify_conclusion_trivial :
    MerkleTree.LeafCollision hashWords ∨ MerkleTree.PairCollision hashPair :=
  Or.inl (by obtain ⟨a, b, hne, h⟩ := Finite.exists_ne_map_eq_of_infinite hashWords; exact ⟨a, b, hne, h⟩)
```

with `Finite Digest` from the eight words (`Finite.of_injective` into `Fin 8 → Fin (2^32)`) and
Mathlib's `Infinite (List K)`; it closes on `propext, Classical.choice, Quot.sound`. So
`collision_of_merkleVerify` is true with its two `merkleVerify` hypotheses deleted, and pins
nothing about the verifier: a `merkleVerify` that ignored its path would satisfy it. The generic
`collision_of_verify` escapes only because `L` and `D` are abstract; every instance the protocol
will build (BLAKE2s leaves of `List K`, digests of 256 bits) is of this kind, and a collision
resistance assumption, or Layer 12's random-oracle extractor (`BcsSecurity`, "the extractor reads
leaves off the query log"), needs the colliding pair *as data computed from the two openings*,
not its existence.

Where a weakening would hide: a later `merkle_binding` theorem consuming
`collision_of_merkleVerify` would be provable for any `merkleVerify`, so a missing or wrong
check in the climb would leave the binding theorem provable. The repository's requirement (a missing check
must leave soundness unprovable) is not met by this statement shape.

Fix, in `ToArkLib/Merkle.lean`, keeping the theorems' content but making the collision explicit
and local to the two paths:

```lean
/-- The colliding inputs two accepted openings exhibit: two distinct leaves with one digest, or two
distinct child pairs with one parent. -/
def Collision (L D : Type) := (L × L) ⊕ ((D × D) × (D × D))

/-- Climb both paths in step and return the first level at which the running nodes become equal. -/
def findCollision [DecidableEq D] (hashLeaf) (hashPair) (leaf leaf' : L) (i : ℕ) (p p' : List D) :
    Option (Collision L D)

theorem findCollision_spec [DecidableEq D] {k root i leaf leaf' p p'} (hne : leaf ≠ leaf')
    (h : verify … k root i leaf p = true) (h' : verify … k root i leaf' p' = true) :
    ∃ c, findCollision … leaf leaf' i p p' = some c ∧ IsCollision hashLeaf hashPair c
```

where `IsCollision` says `a ≠ b ∧ hashLeaf a = hashLeaf b` for `.inl (a, b)` and
`(a, b) ≠ (a', b') ∧ hashPair a b = hashPair a' b'` for `.inr ((a, b), (a', b'))`. `pairCollision_of_climb_eq`
already does this search in its proof; it becomes the specification of the function. Instantiate
in `LeanerVM/Protocol/Merkle.lean` as `merkleCollision` with its spec, and add to
`tests/LeanerVMTests/Protocol/Merkle.lean` a `#guard` that on the node-as-leaf opening of the
existing test (`merkleVerify 1 8 root 1 nodeAsLeaf [node01]` against the honest `merkleVerify 1 8
root 1 …` of a different eight-word row, or two openings built from a deliberately colliding toy
`hashPair`) the function returns the expected pair. Delete `LeafCollision` and `PairCollision` or
keep them as the projections of `IsCollision`; their docstrings should say they are existential and
not what a consumer should use.

### 2. The width check is on the image, not on the row (observation)

`LeanerVM/Protocol/Merkle.lean:54-60`. The docstring of `merkleVerify` says "the row has the
announced width", but `leaf` is the leaf image and the check is `leaf.length = leafWords`. The
pinned opener checks two things the Lean collapses into one: `row.len() == row_words` and
`row_words <= leaf_words` (`fiat_shamir/src/merkle.rs:141, 147`), then hashes
`leaf_image(row, leaf_words)`. A caller doing `merkleVerify depth leafWords root i (leafImage
leafWords row) path` passes the width check for every `row.length ≤ leafWords`, whatever
`row_words` was announced. Executed: `merkleVerify 0 4 (hashWords [0, 0, w 1, w 2]) 0 (leafImage 4
[w 1, w 2]) [] = true` and the same with the three-word row `[0, w 1, w 2]`. This is not a
soundness gap: the opener returns the full image (`merkle.rs:230`) and the verifier reads lanes
from the image, so a shorter row with the same image is the same opening; it is a proof-format
check that Layer 12's `RoundPoly.decode` has to make on the pruned object (`row.length =
rowWords`, `rowWords ≤ leafWords`). Fix: say so in the docstring ("the image has the leaf width;
the row's announced width is checked by the proof decoder"), and in the module docstring note that
the level-0 image is hashed with the lanes in reverse order (`verifier.py:1050`, Annex B
§pcs-opt), since Layer 12 will read `leafImage` through that reversal.

### 3. The Johnson slack is not transcribed (observation)

`LeanerVM/Parameters/Whir.lean:111-118`. The blueprint's Layer 11 sketch has `Level` carry
`(η : ℚ)`, "the deployed η per (μ, ρ) transcribed", and `whirOpen_rbrSoundness`'s error "a
function of η". The PR body says the floating-point search is not restated, which is right, but
not that its *output* `η_i` is dropped: `Level` has `fold`, `logInvRate`, `queries` only. The
verifier never uses `η` (the Python has none), so nothing here is unfaithful; but
`whirOpen_rbrSoundness` at deployed parameters needs a radius `γ_i = 1 - √ρ_i - η_i` per level for
`(1 - γ_i)^{t_i}` and the list size `L_i`, and the only pinned source of it is the Rust. The Rust's
`η` is determined by an integer: `johnson_eta_for_m` (`whir_config.rs:624-631`) takes `η = √ρ / m`
(nudged up by ulps) for the integer `m ≥ 3` the search settles on, so the transcribable datum is
`m` per level, not a float. Fix options: (a) add `johnsonM : ℕ` to `Level` and a table dumped by a
Rust test print (the PR body would then name the dump); (b) leave `η` to the soundness theorem,
which takes any `η_i` meeting the budget and lets the deployed instance be a witness. Either way
the module docstring should say which, since the blueprint says (a).

### 4. The block bound stops at 64 where both encoders stop at 63 (observation)

`LeanerVM/Parameters/Whir.lean:224-236`, `ladder_blocks`, states `κ_i + R_i ≤ 64`, the Annex's
bound. The deployed maximum is 26 (level 5 of `(28, 4)`: `κ = 6`, `R = 19`; checked over all 56
ladders). The Rust encoder asserts `dim ≤ 63` (`crates/pcs/src/ntt/additive_ntt_f64.rs:66`) and
CompPoly's NTT, which #103's test instantiates, needs `ℓ + R < 64`; #103's `encode_injective`
needs only `κ ≤ 64`. So the theorem as stated does not certify that the Rust can encode every
level, though every level satisfies the sharper bound. Fix: state `p.1 ≤ 63` (still decided by
`decide +kernel`), with the docstring naming both the Annex's 64 and the Rust's 63; the fit with
#103 is then exact (`κ_i + R_i ≤ 63 → κ_i ≤ 64`, and the positions `domainPt v`, `v < 2^(κ+R)`,
are distinct, which the opening's distance argument needs).

### 5. The blueprint's Merkle candidate is not named (observation)

`LeanerVM/Protocol/ToArkLib/Merkle.lean`. The blueprint (hole table row, "Merkle trees, the byte
hasher and the WHIR parameters", *Needs* "VCVio's Merkle trees"; the interface line `merkle_fits`;
the status page's watch row "VCVio #571 | the Merkle trees | leanVM's trees on VCVio's library |
the fit lemma holds") plans to consume VCVio's `CryptoFoundations/MerkleTree/` (`Hashing/Defs.lean`
`build`, `verify`, `verifyWithHash`; `Extractability.lean` `extractability_rom_bound`), present at
the pin, with Layer 12's `BcsSecurity` resting on its random-oracle extractability. The PR builds
its own tree and lists it as an ArkLib candidate; the "Readings and deviations" section does not
mention VCVio, `merkle_fits`, or why the fit was not attempted. Not a defect: the tree is small,
correct and pinned by vectors. But the decision belongs in the PR body and the status page's watch
row, and finding 1's extractor is exactly where VCVio's `ExtractionKernel.verifyOpening` shape
would be reused if the fit is taken later.

### 6. Documentation (observation)

- `docs/README.md` does not list `docs/reviews/merkle-whir-params.md`; every other review is
  listed there (`docs/README.md:30-61`).
- `docs/roadmap/protocol-status.md` is untouched; the PR body deferred it to avoid conflicts with
  #62 and #66, both merged since. The hole's coverage row and the open-pull-request row the PR
  body drafts can land now.
- The PR body's classification names Category B, ledger A7 and the T4 obligation; it does not say
  that `collision_of_merkleVerify` is the only security-shaped statement and that it is not yet
  in a consumable form (finding 1).

### 7. Hygiene

- `LeanerVM/Protocol/Blake2sHash.lean:81-85`: `absorb` is public with a free block count; a wrong
  count silently truncates the final block through `blockWords`' `getD` (executed: `absorb paramIv
  0 0 (ramp 100)` is a digest of neither 64 nor 100 bytes). Make it `private` (with `by exact` at
  its use if the exposed `blake2sBytes` needs it), or document the precondition.
- `LeanerVM/Protocol/ToArkLib/Merkle.lean:59-63`: `sibling_lt` and `div_two_lt` are public
  arithmetic helpers with no docstring; `private`.
- `LeanerVM/Protocol/ToArkLib/Merkle.lean:26-27`: the module docstring names
  `collision_of_rootOfPath_eq`; after finding 1 it should name the extractor.

Otherwise clean: no roadmap codes in Lean comments ("Category B" is the repository's source
convention, used in 22 modules on `main`), declaration docstrings of one to three lines, every
line at most 100 characters, module shape and `@[expose] public section` as in the sibling `To*`
modules, imports narrow, the four scripts green (`audit-lean.sh`, `check-imports.sh`,
`check-layers.sh`, `check-docs.py`), and every public theorem closing on at most `propext,
Classical.choice, Quot.sound` (`residualLog_le` on none).

## Pass B: fidelity against the pin

Read before the Lean: `crates/primitives/src/hash.rs:60-230`, `crates/fiat_shamir/src/merkle.rs`
(whole), `crates/pcs/src/merkle.rs:1-195`, `crates/pcs/src/whir_config.rs:1-330, 639-707,
919-960`, `crates/pcs/src/whir.rs:274-276`, `crates/pcs/src/pack.rs:7`,
`crates/lean_vm/src/pcs.rs:1-80`, `crates/lean_vm/src/cpu/mod.rs:174`,
`python-verifier/verifier.py:196-225, 392-404, 897-1087`, Annex B.

**Byte hasher** (`hash.rs:66-224`): seven behaviours as in the first review, all matched again;
in addition `blake2sBytes` was checked against CPython's `hashlib.blake2s` at 1, 63, 127, 129, 191,
192, 193, 256 and 320 bytes (both sides of every block boundary up to five blocks, and three
whole-block cases of the fast path `hash.rs:212-220`): nine of nine equal.

**Digest encoding** (`merkle.rs:14-36`; `verifier.py:212-224` `Digest.words`, `halves`,
`from_halves`): the two 128-bit halves as the two low limbs, little-endian 64-bit words, top limb
zero, decoder rejecting a nonzero top limb: three of three, both verifiers.

**Merkle** (`merkle.rs:40-67, 139-150, 163-235, 254-263`; `pcs/merkle.rs:100-142, 161-192`;
`verifier.py:392-404`): leaf hash of the words' little-endian bytes, node hash of the 64 bytes left
then right, adjacent pairing left first, running node left at an even index, index halved per
level, one sibling per level, index below the leaf count, root compared: all matched. An eight-leaf
tree of three-word leaves built with `hashlib` agrees with `merkleRoot`, `merklePath` of leaf 5 and
`merkleVerify` at depth 3 and width 3; the zero-prefix image of a two-word row in a five-word leaf
hashes as `hashlib` hashes the 40 bytes. The rejections of the Rust test
`malformed_phases_are_rejected` (`merkle.rs:306-351`) that apply to one path (trailing sibling,
missing sibling, tampered sibling, tampered row, wrong row width, wrong announced width,
out-of-range query) are all tests of the Lean; the three that are the octopus's (wrong query
count, non-power-of-two tree, shared siblings) belong to Layer 12, as the module docstring says.
The row-width check differs in shape (finding 2). Of the opener's seven checks the Lean carries
five; the two it leaves to the proof decoder are the row width and the power-of-two leaf count
(the Lean takes the depth, so the leaf count is `2^depth` by type).

**WHIR parameters** (`whir_config.rs:38-92, 260-311, 919-960`; `pcs.rs:40-51`; `pack.rs:7`;
`verifier.py:900-935`): ten constants transcribed, `oodSamples` per `whir_config.rs:677-684` (0 at
level 0, the least `s ≥ 1` meeting the OOD budget after; 1 for every deployed level by the Rust
test at 22 to 28 and the Python at every size); the window `15..28 × 1..4` is the Rust verifier's
(`cpu/mod.rs:174`, `validate_log_inv_rate`) and the Python's (`verifier.py:923`). The ladder
geometry: `derive_ladder` with `derive_ladder_shape`'s rate rule, and `derive_config`; all 56
ladders were recomputed from the Python's rule in a script and compared with `ladder`'s output
(`#eval` over the window): 56 of 56 equal, residuals included. The query table was diffed
programmatically against the `WHIR_QUERIES` line: equal. The block logs are `message_log +
level_rate` (`verifier.py:1040`); maximum 26. Not transcribed: `η` (finding 3), `LOG_INV_RATE_0`
and `JOHNSON_ETA_SEARCH_MAX_M` (as in the first review; neither is a verifier parameter).
`ladder_blocks`' second conjunct is `whir_config.rs:673`, `queries > block_len → continue`.

Nothing in the Lean is from the historical implementation; no Poseidon, no KoalaBear.

## Pass A: specifications

Instantiated: the ladder facts at the three tested pairs and at all 56 (the `#eval` above); the
Merkle theorems on the four- and eight-leaf trees; the encoding round trips on the `"abc"` digest;
`merkleVerify` at depth 0 (accepts index 0 with the empty path, rejects index 1). No hypothesis is
unsatisfiable. `verify_path` and `merkleVerify_merklePath` are substantive (the honest path is the
only object of their kind). `ladder_isSome`, `ladder_length`, `residualLog_le`, `ladder_blocks`
pin the table rather than restate it (the first review's mutations still apply). The binding half
is finding 1: its conclusion is provable with no hypothesis, so it is not a specification of the
verifier. `blake2sBytes` and the tree are pinned against `hashlib`, an object defined outside the
Lean.

Target classification: Category B per module, ledger A7, T4 through Layer 12's `verify`; no T1 to
T8 theorem claimed. Correct, with the caveat of finding 6.

## Pass C: hygiene

Finding 7 and the documentation items of finding 6; otherwise clean, as listed under finding 7.

## What the review could not do

The Rust was not executed; the query counts and `oodSamples` at sizes 15 to 21 rest on the Python
verifier's transcription of the Rust's output, as before. VCVio's `merkle_fits` was not attempted
(finding 5 asks the author to say whether it was). The probes (hashlib vectors, the eight-leaf
tree, the 56 ladders, the axioms, the depth-0 and image-width cases, and the pigeonhole proof
quoted under finding 1) were scratch files of the review session and are not kept.
