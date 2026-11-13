/-
Copyright (c) 2026 leanerVM Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Derived-source notice:
Copyright (c) 2026 Leanth Contributors. All rights reserved.
-/

/-
  LeanerVM.Protocol.ToCompPoly.PowerBatching

  Power batching of weighted claims, with exponents starting at zero.
-/

module

public import LeanerVM.Protocol.ToCompPoly.Multilinear
public import LeanerVM.Protocol.ToCompPoly.FinLoop
public import Mathlib.Algebra.Polynomial.Roots
import CompPoly.ToMathlib.Polynomial.Roots
import Mathlib.Algebra.Polynomial.OfFn

/-!
# Power batching

A family of `J` values or tables is combined with powers `ρ^j`, starting at zero.
The polynomial whose coefficients are the differences of two families has degree at most
`J - 1`, so a false family survives at most `J - 1` challenges. A false singleton remains false
at every challenge, including zero. The empty family is handled separately.

Candidate for CompPoly: finite power combinations, their multilinear table pairing and
extension, and the finite-field root count. The values are fixed before the challenge is
chosen.

Derived from the zero-based scalar-batching results in Verified-zkEVM/leanth at
23929f8c922cd4461ab22dbfaa6520f3ad23a3b2, by Aristotle (Harmonic), Stefano Rocca and
Elias Judin: `Leanth/ProofSystem/ZeroCheck.lean:670-697`, `scalarBatch_rejection` and
`scalarBatch_eq_zero`. The current API takes separate actual and claimed values, exposes the
difference polynomial, and includes the empty case. `Leanth/ProofSystem/Stacking.lean:779-804`
uses positive powers in `BatchedAccepts` and `batchPoly`; that distinct convention has an
additional automatic root at zero and a `J` bound.

Compiled code computes a combination by Horner's rule and a combination of tables with each table
built once (`powerBatch_eq_powerBatchFast`, `batchWeight_eq_batchWeightFast`, `@[csimp]`
theorems): `batchWeight` reads every table at every entry, and a table given as a function, such as
a weight's values, is rebuilt at each read.
-/

namespace LeanerVM.Protocol

open CompPoly CMlPolynomialEval

@[expose] public section

variable {R : Type*} [CommRing R] {J μ : ℕ}

/-- A finite power combination, with coefficient zero weighted by one. -/
def powerBatch (a : Fin J → R) (ρ : R) : R := ∑ j : Fin J, a j * ρ ^ j.val

/-- Batch weight tables pointwise with the same powers as their targets. -/
def batchWeight (w : Fin J → CMlPolynomialEval R μ) (ρ : R) : CMlPolynomialEval R μ :=
  Vector.ofFn fun x ↦ powerBatch (fun j ↦ (w j)[x]) ρ

/-- Pairing is linear in a family of weights on the same arbitrary committed column. -/
theorem pairing_batchWeight (w : Fin J → CMlPolynomialEval R μ)
    (q : CMlPolynomialEval R μ) (ρ : R) :
    sumCube (hadamard (batchWeight w ρ) q) =
      powerBatch (fun j ↦ sumCube (hadamard (w j) q)) ρ := by
  simp only [sumCube, hadamard, batchWeight, Fin.getElem_fin, Vector.getElem_ofFn, powerBatch]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_right_comm _ (ρ ^ _) _]

/-- Multilinear extension commutes with power batching, at every point, including off the cube. -/
theorem evalMle_batchWeight (w : Fin J → CMlPolynomialEval R μ) (ρ : R) (r : Vector R μ) :
    evalMle (batchWeight w ρ) r = powerBatch (fun j ↦ evalMle (w j) r) ρ := by
  simp only [evalMle_eq_sum, batchWeight, Fin.getElem_fin, Vector.getElem_ofFn, powerBatch]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_right_comm _ (ρ ^ _) _]

/-- Batching commutes with differences. -/
theorem powerBatch_sub (a b : Fin J → R) (ρ : R) :
    powerBatch a ρ - powerBatch b ρ = powerBatch (fun i ↦ a i - b i) ρ := by
  simp only [powerBatch, ← Finset.sum_sub_distrib, sub_mul]

/-- A false singleton has no successful challenge; a zero challenge cannot erase its error. -/
theorem singleton_batch_ne (a v : Fin 1 → R) (h : a 0 ≠ v 0) (ρ : R) :
    powerBatch a ρ ≠ powerBatch v ρ := by
  simpa [powerBatch] using h

/-- The empty batch is the trivial zero target. -/
@[simp] theorem empty_powerBatch (a : Fin 0 → R) (ρ : R) : powerBatch a ρ = 0 := by
  simp [powerBatch]

/-- A batch with an entry in front: the entry, then the rest batched one power up. -/
theorem powerBatch_cons (x : R) (a : Fin J → R) (ρ : R) :
    powerBatch (Fin.cons x a : Fin (J + 1) → R) ρ = x + ρ * powerBatch a ρ := by
  rw [powerBatch, powerBatch, Fin.sum_univ_succ, Finset.mul_sum]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
  exact congrArg (x + ·) (Finset.sum_congr rfl fun _ _ ↦ by ring)

/-! ## Compiled forms -/

/-- A power combination by Horner's rule. -/
def powerBatchFast (a : Fin J → R) (ρ : R) : R := hornerFin a ρ

/-- Horner's rule is the power combination. -/
@[csimp] theorem powerBatch_eq_powerBatchFast : @powerBatch = @powerBatchFast := by
  funext R _ J a ρ
  rw [powerBatchFast, hornerFin_eq_sum, powerBatch]
  exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _

/-- Tables combined by the powers of `ρ`, each table built once, each entry by Horner's rule. -/
def batchWeightFast (w : Fin J → CMlPolynomialEval R μ) (ρ : R) : CMlPolynomialEval R μ :=
  let ts := Vector.ofFn w
  Vector.ofFn fun x ↦ hornerFin (fun j : Fin J ↦ ts[j][x]) ρ

/-- The tables built once give the combination. -/
@[csimp] theorem batchWeight_eq_batchWeightFast : @batchWeight = @batchWeightFast := by
  funext R _ J μ w ρ
  refine Vector.ext fun x hx ↦ ?_
  simp only [batchWeight, batchWeightFast, Vector.getElem_ofFn, hornerFin_eq_sum, powerBatch,
    Fin.getElem_fin]
  exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _

section FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- At most `J - 1` challenges make a false family appear true after power batching: they are
roots of the nonzero polynomial whose coefficients are the differences of the claims. -/
theorem card_false_batch_le (a v : Fin J → F) (h : ∃ j, a j ≠ v j) :
    (Finset.univ.filter fun ρ ↦ powerBatch a ρ = powerBatch v ρ).card ≤ J - 1 := by
  obtain ⟨j, hj⟩ := h
  have hp : Polynomial.ofFn J (a - v) ≠ 0 := fun hp ↦ hj <| sub_eq_zero.mp <| by
    simpa [hp] using (Polynomial.ofFn_coeff_eq_val_of_lt (a - v) j.isLt).symm
  calc _ = (Finset.univ.filter fun ρ ↦ (Polynomial.ofFn J (a - v)).eval (id ρ) = 0).card := by
        refine congrArg Finset.card (Finset.filter_congr fun ρ _ ↦ ?_)
        rw [← sub_eq_zero, powerBatch_sub, id, Polynomial.ofFn_eq_sum_monomial,
          Polynomial.eval_finsetSum]
        simp only [powerBatch, Polynomial.eval_monomial, Pi.sub_apply, mul_comm]
    _ ≤ _ := Polynomial.card_eval_zero_le_natDegree _ id (Set.injOn_id _) _ hp
    _ ≤ J - 1 := Nat.le_sub_one_of_lt (Polynomial.ofFn_natDegree_lt j.pos _)

end FiniteField

end
end LeanerVM.Protocol
