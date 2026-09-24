/-
Copyright (c) 2026 leanerVM Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin, Stefano Rocca, Aristotle (Harmonic)

Derived-source notice:
Copyright (c) 2026 Leanth Contributors. All rights reserved.
-/

/-
  LeanerVM.Protocol.Generic.Claims

  Block evaluation claims as weighted claims on an arbitrary committed table.
-/

module

public import LeanerVM.Protocol.Stacking

/-!
# Claims on aligned blocks

A claim names a block, an evaluation point and a value. Its equality-kernel weight is
supported on the declared block window. The pairing theorem applies to every ambient table,
including tables with noncanonical padding; it therefore serves both completeness and
reconstruction from a prover's committed column.

Category A: the weighted-claim identity in leanVM specification §4.1
(`doc/leanvm/body/04-committing-the-witness.tex:4-18`) at
`a386121f84292f6fa663aaa3e570c15bc0240ea2`, generalized to arbitrary commutative rings.
The pinned `crates/pcs/src/stack_open.rs:8-12` point-claim interface and
`python-verifier/verifier.py:514-522` use the same selector-weight construction.

Derived from Verified-zkEVM/leanth at 23929f8c922cd4461ab22dbfaa6520f3ad23a3b2,
`Leanth/ProofSystem/Stacking.lean:705-777` (`claim_iff_innerProduct`, `unstack_stack`,
`sum_weight_stack_unstack`, `isValid_unstack_iff`) and
`Leanth/LeanVM/Protocol.lean:8550-8602` (`assignmentStackedVector_innerProduct`,
`assignmentStackedVector_pairing_iff`), by Aristotle (Harmonic), Stefano Rocca and Elias Judin.
The statements use the current little-endian selection API and arbitrary coefficient maps;
only unshifted claims are represented because the leanISA protocol has no shifted columns.
This generic staging module is consumed by the opening phase and is intended for ArkLib.

Upstream ownership: [ArkLib #900](https://github.com/Verified-zkEVM/ArkLib/issues/900).
-/

namespace LeanerVM.Protocol

open CompPoly CMlPolynomialEval

@[expose] public section

variable {R S : Type*} [CommRing R] [CommRing S]

/-- An evaluation claim about one declared block. -/
structure BlockClaim (B : Blocks R) (S : Type*) where
  /-- The block whose values are read from the ambient table. -/
  block : Fin B.n
  /-- A point in the coefficient extension ring. -/
  point : Vector S (B.size block)
  /-- The claimed multilinear evaluation. -/
  value : S

namespace BlockClaim

variable {B : Blocks R} (c : BlockClaim B S)

/-- Embed the claim point using the block selector in the high coordinates. -/
def ambientPoint {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) : Vector S μ :=
  Vector.cast (Nat.add_sub_cancel' (B.size_le hμ c.block))
    (c.point ++ (boolVec (B.selector hμ c.block) : Vector S (μ - B.size c.block)))

/-- The equality-kernel weight corresponding to the block evaluation. -/
def weight {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) : CMlPolynomialEval S μ :=
  eqTable (c.ambientPoint hμ)

/-- The claim holds when reading its block from the actual committed table. -/
def IsValid (φ : R →+* S) {μ : ℕ} (hμ : B.total ≤ 2 ^ μ)
    (q : CMlPolynomialEval R μ) : Prop :=
  eval₂Mle (B.unstack hμ q c.block) φ c.point = c.value

/-- Pairing the claim weight with the mapped committed table evaluates the selected block. -/
theorem pairing_eq (φ : R →+* S) {μ : ℕ} (hμ : B.total ≤ 2 ^ μ)
    (q : CMlPolynomialEval R μ) :
    sumCube (hadamard (c.weight hμ) (CMlPolynomialEval.map φ q)) =
      eval₂Mle (B.unstack hμ q c.block) φ c.point := by
  rw [weight, ← eval_eq_sum_eqTable]
  exact B.unstack_eval₂ φ hμ q c.block c.point

/-- A block claim is precisely the associated weighted inner-product claim. -/
theorem isValid_iff_pairing (φ : R →+* S) {μ : ℕ} (hμ : B.total ≤ 2 ^ μ)
    (q : CMlPolynomialEval R μ) :
    c.IsValid φ hμ q ↔
      sumCube (hadamard (c.weight hμ) (CMlPolynomialEval.map φ q)) = c.value := by
  rw [c.pairing_eq]
  rfl

/-- Agreement of mapped coefficients on the selected window preserves its block claim. -/
theorem isValid_iff_of_map_window_eq (φ : R →+* S) {μ : ℕ} (hμ : B.total ≤ 2 ^ μ)
    (q r : CMlPolynomialEval R μ)
    (h : ∀ x : Fin (2 ^ μ), B.InWindow c.block x.val → φ q[x] = φ r[x]) :
    c.IsValid φ hμ q ↔ c.IsValid φ hμ r := by
  unfold IsValid eval₂Mle
  rw [← B.unstack_map φ hμ q c.block, ← B.unstack_map φ hμ r c.block]
  rw [(B.map φ).unstack_eq_of_window_eq hμ (CMlPolynomialEval.map φ q)
    (CMlPolynomialEval.map φ r) c.block]
  intro x hx
  simpa only [CMlPolynomialEval.map, Fin.getElem_fin, Vector.getElem_map] using h x hx

/-- Changes outside the selected window preserve its block evaluation claim. -/
theorem isValid_iff_of_window_eq (φ : R →+* S) {μ : ℕ} (hμ : B.total ≤ 2 ^ μ)
    (q r : CMlPolynomialEval R μ)
    (h : ∀ x : Fin (2 ^ μ), B.InWindow c.block x.val → q[x] = r[x]) :
    c.IsValid φ hμ q ↔ c.IsValid φ hμ r := by
  exact c.isValid_iff_of_map_window_eq φ hμ q r (fun x hx ↦ congrArg φ (h x hx))

end BlockClaim

end
end LeanerVM.Protocol
