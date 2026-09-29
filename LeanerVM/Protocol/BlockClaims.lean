/-
Copyright (c) 2026 leanerVM Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin, Stefano Rocca, Aristotle (Harmonic)

Derived-source notice:
Copyright (c) 2026 Leanth Contributors. All rights reserved.
-/

/-
  LeanerVM.Protocol.BlockClaims

  Evaluation claims on the blocks of an aligned layout, as weighted claims on the committed
  table.
-/

module

public import LeanerVM.Protocol.ToCompPoly.Stacking

/-!
# Claims on aligned blocks

A claim names a block, an evaluation point and a value. It holds of a committed table when the
block read off the table evaluates to the value at the point, and that is the same as a
weighted sum over the whole table, the weight being the equality kernel at the point lifted by
the block's selector (specification §4.1, `doc/leanvm/body/04-committing-the-witness.tex:4-18`
at `a386121f84292f6fa663aaa3e570c15bc0240ea2`). The statements are for every table, a stack or
not, so they serve completeness and the reconstruction of a witness from what a prover
committed. Category A: written from the specification; the identity itself is
`Blocks.unstack_eval₂_eq_sumCube`, and this module only names its arguments.

This is the aligned case. leanVM also reads the eighteen BLAKE2S limb columns off the same
stack by strided claims, whose weights put the slot bits in the low coordinates, and pools
ring-switched claims whose weights are no equality kernel (`crates/pcs/src/stack_open.rs:73-98`,
`crates/lean_vm/src/cpu/mod.rs:790-814`); neither is a `BlockClaim`.

Derived from Verified-zkEVM/leanth at 23929f8c922cd4461ab22dbfaa6520f3ad23a3b2,
`Leanth/ProofSystem/Stacking.lean:705-777` (`claim_iff_innerProduct`, `unstack_stack`,
`sum_weight_stack_unstack`, `isValid_unstack_iff`) and
`Leanth/LeanVM/Protocol.lean:8550-8602` (`assignmentStackedVector_innerProduct`,
`assignmentStackedVector_pairing_iff`), by Aristotle (Harmonic), Stefano Rocca and Elias Judin.
-/

namespace LeanerVM.Protocol

open CompPoly CMlPolynomialEval

@[expose] public section

variable {R S : Type*} [CommRing R] [CommRing S]

/-- An evaluation claim about one block of an aligned layout. -/
structure BlockClaim (B : Blocks) (S : Type*) where
  /-- The block whose values are read from the committed table. -/
  block : Fin B.n
  /-- A point in the ring of the challenges. -/
  point : Vector S (B.size block)
  /-- The claimed multilinear evaluation. -/
  value : S

namespace BlockClaim

variable {B : Blocks} (c : BlockClaim B S)

/-! ## The claim and its weight -/

/-- The claim's point lifted to the stack: the block's selector bits in the high coordinates. -/
def ambientPoint {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) : Vector S μ :=
  B.extendPoint hμ c.block c.point

/-- The weight of the claim on the stack: the equality kernel at the lifted point. -/
def weight {μ : ℕ} (hμ : B.total ≤ 2 ^ μ) : CMlPolynomialEval S μ :=
  lagrangeBasis (c.ambientPoint hμ)

/-- The claim holds of a committed table: its block, read off the table, evaluates to the value
at the point. -/
def IsValid (φ : R →+* S) {μ : ℕ} (hμ : B.total ≤ 2 ^ μ)
    (q : CMlPolynomialEval R μ) : Prop :=
  eval₂Mle (B.unstack hμ q c.block) φ c.point = c.value

/-- Pairing the claim's weight with the committed table evaluates the claimed block. -/
theorem pairing_eq (φ : R →+* S) {μ : ℕ} (hμ : B.total ≤ 2 ^ μ)
    (q : CMlPolynomialEval R μ) :
    sumCube (hadamard (c.weight hμ) (CMlPolynomialEval.map φ q)) =
      eval₂Mle (B.unstack hμ q c.block) φ c.point :=
  (B.unstack_eval₂_eq_sumCube φ hμ q c.block c.point).symm

/-- A block claim is the weighted claim on the stack with the claim's weight. -/
theorem isValid_iff_pairing (φ : R →+* S) {μ : ℕ} (hμ : B.total ≤ 2 ^ μ)
    (q : CMlPolynomialEval R μ) :
    c.IsValid φ hμ q ↔
      sumCube (hadamard (c.weight hμ) (CMlPolynomialEval.map φ q)) = c.value := by
  rw [c.pairing_eq]
  rfl

/-! ## Locality -/

/-- Two committed tables whose mapped entries agree on the block's window satisfy the same
claim. -/
theorem isValid_iff_of_map_window_eq (φ : R →+* S) {μ : ℕ} (hμ : B.total ≤ 2 ^ μ)
    (q r : CMlPolynomialEval R μ)
    (h : ∀ x : Fin (2 ^ μ), B.InWindow c.block x.val → φ q[x] = φ r[x]) :
    c.IsValid φ hμ q ↔ c.IsValid φ hμ r := by
  unfold IsValid eval₂Mle
  rw [← B.unstack_map φ hμ q c.block, ← B.unstack_map φ hμ r c.block]
  rw [B.unstack_eq_of_window_eq hμ (CMlPolynomialEval.map φ q)
    (CMlPolynomialEval.map φ r) c.block]
  intro x hx
  simpa only [CMlPolynomialEval.map, Fin.getElem_fin, Vector.getElem_map] using h x hx

/-- Changing the committed table outside the block's window does not change the claim. -/
theorem isValid_iff_of_window_eq (φ : R →+* S) {μ : ℕ} (hμ : B.total ≤ 2 ^ μ)
    (q r : CMlPolynomialEval R μ)
    (h : ∀ x : Fin (2 ^ μ), B.InWindow c.block x.val → q[x] = r[x]) :
    c.IsValid φ hμ q ↔ c.IsValid φ hμ r :=
  c.isValid_iff_of_map_window_eq φ hμ q r (fun x hx ↦ congrArg φ (h x hx))

end BlockClaim

end
end LeanerVM.Protocol
