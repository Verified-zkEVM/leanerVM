# Tests

Lean tests live here and are run by `lake test`, which builds the `LeanerVMTests` library: every
test is a `#guard` (compiled evaluation) or an `example` (kernel check) that fails the build.
`Main.lean` imports the `LeanerVMTests.lean` aggregate, which imports every test module and
checks the production public module graph; `scripts/validate.sh` elaborates it with warnings as
errors. There is no test executable: at the former CompPoly pin a binary linking the `BF64`
module was killed at startup evaluating its eager `Fintype BF64` instance (finding P3 in
[`docs/roadmap/leanisa-status.md`](../docs/roadmap/leanisa-status.md)). At `572f9973` that
instance is proof-only; whether the tests can again be an executable is unchecked.
`scripts/check-imports.sh` rejects missing, stale, or duplicate test imports. The aggregate and
`Main.lean` are plain files because `LeanerVM.lean` is one (see `CONTRIBUTING.md`); a test
module may be a `module` or plain, and a plain one can decide `E` arithmetic in the kernel,
which a `module` cannot.

As executable definitions arrive, add focused unit, differential, and mutation tests here.
Put their modules under `tests/LeanerVMTests/` and import each one from `LeanerVMTests.lean`.
Tests must not be imported by the production `LeanerVM/` library.

In a `module` test file, a `#guard` needs a `meta import` of the module it evaluates, and
core's `DecidableEq` instances for `Vector` and `Array` are not exposed, so neither `decide` nor
the kernel can reduce an equality of vectors there (finding L1): state such checks on the word
lists through `Vector.toList_inj`, and give production predicates over vectors a `Decidable`
instance that compares lists, as `CompressCells` does in `LeanerVM/Semantics/Blake2s.lean`.

A kernel check of an equality on a structure over `K` or `E` goes through that structure's
`DecidableEq` instance, and a *derived* instance decides its later fields under `h ▸` for the
earlier ones, which makes the kernel compare two field values symbolically instead of
evaluating them (finding E5): `decide +kernel` on `⟨g * 1, 1⟩ = ⟨g ^ 1, 1⟩` never returns
under a derived instance. Production structures that kernel proofs compare carry a
hand-written `decidable_of_iff` instance (`Regs`), and an `E` equality is decided only against
a word in `E.ofLimbs` form, as `tests/LeanerVMTests/Semantics/Execution.lean` does.

Pitfalls met while building the proof system (`LeanerVM/Protocol/`):

- A structure that holds a real number (an error bound) makes every definition built from it
  `noncomputable`; keep the reduction, the verifier and the extractor in computable definitions
  and the error elsewhere, and check an extractor by a `def` without `noncomputable`.
- `simp` does not rewrite inside instance arguments carried by a structure's type: state a
  phase's lemmas on its literal prover and verifier, not on the bundle's projections.
- A `Decidable` instance written `by unfold …; infer_instance` can elaborate and never return
  when a `#guard` evaluates it; write it `inferInstanceAs (Decidable …)`. Read a compile's exit
  status: a kill hidden behind a pipe into `head` looks like success.
- A binder whose type is a membership in `Finset.univ : Finset E` makes a linter enumerate the
  field ("maximum recursion depth"); state counting bounds over an abstract `[Fintype α]`.
- Under a section's `[CommRing R]`, a `def` taking `[Zero R]` is rejected by Mathlib's
  overlapping-instances linter, which `warningAsError` makes an error; use the ring's zero.
- `#guard v = w` finds no `Decidable` instance when the vectors' length is a computed size;
  compare `.toList`. A `#guard` whose proposition has a numeral of `E` next to an operation
  (`y ^ 2 + 1`) finds none either; name such values as definitions.
- Since CompPoly `572f9973` a numeral in `K` has its characteristic-two value (`(2 : K) = 0`):
  write an encoded word as `K.ofBits n`.

Implementation-validation tests should run identical versioned workloads through the Lean
reference and a pinned Rust leanVM revision, comparing decoding, state transitions, outputs,
traces, encodings, and rejection behavior as each surface becomes available. Optimized native,
Rust FFI, CUDA, and future compiled paths use the same fixtures. These tests establish observed
agreement, not a formal theorem about the foreign implementation.

The initial target suite should cover all six opcodes, write-once conflicts, invalid generator-
power addresses, branch state, BLAKE2s counter/finalization metadata, public-input encoding, and
prover-supplied cells. Guest-level fixtures should separately cover XMSS epoch groups, SPHINCS
`(key, message)` claims, overlaps, conflicting messages, omitted coverage, child mappings, and
deferred-claim rejection. Bind vectors to the revision in
[`docs/leanvm-target.md`](../docs/leanvm-target.md).

The executable ISA checker and its proved contracts are documented in
[`docs/leanisa-checker.md`](../docs/leanisa-checker.md). The optional
`python3 scripts/test-rust-contracts.py /path/to/leanVM` lane runs the maintained Rust fixtures
in `tests/rust/` and validates their actual exports in Lean. It requires the pinned source
commit and an offline Cargo cache; the ordinary Lean gate does not depend on a Rust checkout.
