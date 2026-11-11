/-
  LeanerVM.Protocol.ToCompPoly.LinearSolve

  A square linear system over a field solved by Gaussian elimination, computably, with its two
  facts: a returned vector solves the system, and the solver fails only on a singular matrix.
  Candidate for CompPoly.
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Data.List.FinRange
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# Gaussian elimination

`gaussSolve n M y` solves `Σ_j M i j • x j = y i` for `x : Fin n → V`, with the matrix over a
field `F` and the right-hand side in an `F`-module `V`: it picks the first row whose entry in
column `0` is nonzero as the pivot, eliminates column `0` from the other rows, solves the
remaining `n - 1` unknowns recursively and recovers `x 0` from the pivot row. The reduced system is
built as a table at each step, and the pivot is inverted once per step, so the cost is `O(n³)`
operations and `n` inversions in `F`. A right-hand side in a module solves several systems with one
matrix at once (`V = Fin k → F`), and a matrix over a subfield solves systems over the extension
with inversions in the subfield.

* `gaussSolve_sound`: a returned vector solves the system.
* `exists_kernel_of_gaussSolve_eq_none`: the solver fails only when the matrix sends a nonzero
  vector of `F` to zero, so it returns a solution of every system whose matrix is injective
  (`gaussSolve_of_injective`).

Over an arbitrary field with decidable equality. Nothing here transcribes a source.
-/

namespace LeanerVM.Protocol

@[expose] public section

variable {F V : Type*} [Field F] [DecidableEq F] [AddCommGroup V] [Module F V]

/-- Gaussian elimination: a solution of `Σ_j M i j • x j = y i`, or `none` when no pivot is
found at some step. -/
def gaussSolve : (n : ℕ) → (Fin n → Fin n → F) → (Fin n → V) → Option (Vector V n)
  | 0, _, _ => some #v[]
  | n + 1, M, y =>
    match (List.finRange (n + 1)).find? (fun i ↦ M i 0 ≠ 0) with
    | none => none
    | some p =>
      let inv := (M p 0)⁻¹
      let c := Vector.ofFn fun i : Fin n ↦ M (p.succAbove i) 0 * inv
      let A := Vector.ofFn fun i : Fin n ↦ Vector.ofFn fun j : Fin n ↦
        M (p.succAbove i) j.succ - c[i] * M p j.succ
      let b := Vector.ofFn fun i : Fin n ↦ y (p.succAbove i) - c[i] • y p
      (gaussSolve n (fun i j ↦ A[i][j]) (fun i ↦ b[i])).map fun x ↦
        let x0 := inv • (y p - ∑ j : Fin n, M p j.succ • x[j])
        Vector.ofFn (Fin.cons x0 fun j ↦ x[j])

omit [AddCommGroup V] [Module F V] in
/-- The pivot the solver picks has a nonzero entry in column `0`. -/
private theorem pivot_ne_zero {n : ℕ} {M : Fin (n + 1) → Fin (n + 1) → F} {p : Fin (n + 1)}
    (h : (List.finRange (n + 1)).find? (fun i ↦ M i 0 ≠ 0) = some p) : M p 0 ≠ 0 := by
  simpa using List.find?_some h

omit [DecidableEq F] in
/-- The pivot row is solved by the vector with the pivot's unknown in front. -/
private theorem pivot_row {n : ℕ} (M : Fin (n + 1) → Fin (n + 1) → F) (y : Fin (n + 1) → V)
    (p : Fin (n + 1)) (hp : M p 0 ≠ 0) (x : Fin n → V) :
    ∑ j, M p j • (Fin.cons ((M p 0)⁻¹ • (y p - ∑ j, M p j.succ • x j)) x :
      Fin (n + 1) → V) j = y p := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, smul_smul, mul_inv_cancel₀ hp, one_smul,
    sub_add_cancel]

omit [DecidableEq F] in
/-- The one step of elimination, on one row other than the pivot: if the reduced row is solved
by `x`, the row is solved by `x` with the pivot's unknown in front. -/
private theorem row_step {n : ℕ} (M : Fin (n + 1) → Fin (n + 1) → F) (y : Fin (n + 1) → V)
    (p i : Fin (n + 1)) (x : Fin n → V)
    (h : ∑ j, (M i j.succ - M i 0 * (M p 0)⁻¹ * M p j.succ) • x j =
      y i - (M i 0 * (M p 0)⁻¹) • y p) :
    ∑ j, M i j • (Fin.cons ((M p 0)⁻¹ • (y p - ∑ j, M p j.succ • x j)) x :
      Fin (n + 1) → V) j = y i := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  simp only [sub_smul, Finset.sum_sub_distrib] at h
  rw [show ∑ j, (M i 0 * (M p 0)⁻¹ * M p j.succ) • x j =
      (M i 0 * (M p 0)⁻¹) • ∑ j, M p j.succ • x j by
    rw [Finset.smul_sum]; simp only [mul_smul]] at h
  linear_combination (norm := module) h

/-- **A returned vector solves the system.** -/
theorem gaussSolve_sound : ∀ (n : ℕ) (M : Fin n → Fin n → F) (y : Fin n → V) (x : Vector V n),
    gaussSolve n M y = some x → ∀ i, ∑ j, M i j • x[j] = y i
  | 0, _, _, _, _, i => i.elim0
  | n + 1, M, y, x, h, i => by
    unfold gaussSolve at h
    split at h
    · exact absurd h (by simp)
    · rename_i p hfind
      have hp := pivot_ne_zero hfind
      obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp h
      have ih := gaussSolve_sound n _ _ x' hx'
      simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]
      rcases Fin.eq_self_or_eq_succAbove p i with rfl | ⟨i', rfl⟩
      · exact pivot_row M y _ hp fun j ↦ x'[j]
      · refine row_step M y p _ (fun j ↦ x'[j]) ?_
        have := ih i'
        simpa only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta] using this

/-- **The solver fails only on a singular matrix**: when it returns `none`, some nonzero vector
of `F` is sent to zero. -/
theorem exists_kernel_of_gaussSolve_eq_none : ∀ (n : ℕ) (M : Fin n → Fin n → F) (y : Fin n → V),
    gaussSolve n M y = none → ∃ x : Fin n → F, x ≠ 0 ∧ ∀ i, ∑ j, M i j * x j = 0
  | 0, _, _, h => absurd h (by simp [gaussSolve])
  | n + 1, M, y, h => by
    unfold gaussSolve at h
    split at h
    · rename_i hfind
      have hcol : ∀ i, M i 0 = 0 := fun i ↦ by
        simpa using List.find?_eq_none.mp hfind i (List.mem_finRange i)
      refine ⟨Fin.cons 1 0, fun h0 ↦ ?_, fun i ↦ ?_⟩
      · simpa using congrFun h0 0
      · rw [Fin.sum_univ_succ]
        simp [hcol i]
    · rename_i p hfind
      have hp := pivot_ne_zero hfind
      obtain ⟨x', hx'0, hx'⟩ := exists_kernel_of_gaussSolve_eq_none n _ _
        (Option.map_eq_none_iff.mp h)
      refine ⟨Fin.cons ((M p 0)⁻¹ • ((0 : Fin (n + 1) → F) p - ∑ j, M p j.succ • x' j)) x',
        fun h0 ↦ hx'0 ?_, fun i ↦ ?_⟩
      · funext j
        simpa using congrFun h0 j.succ
      · rcases Fin.eq_self_or_eq_succAbove p i with rfl | ⟨i', rfl⟩
        · exact pivot_row (V := F) M 0 _ hp x'
        · refine row_step (V := F) M 0 p _ x' ?_
          have := hx' i'
          simpa only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, smul_eq_mul, Pi.zero_apply,
            mul_zero, sub_zero] using this

/-- **On an injective matrix the solver returns a solution.** -/
theorem gaussSolve_of_injective {n : ℕ} (M : Fin n → Fin n → F) (y : Fin n → V)
    (hM : ∀ x : Fin n → F, (∀ i, ∑ j, M i j * x j = 0) → x = 0) :
    ∃ x, gaussSolve n M y = some x ∧ ∀ i, ∑ j, M i j • x[j] = y i := by
  cases h : gaussSolve n M y with
  | none =>
    obtain ⟨x, hx0, hx⟩ := exists_kernel_of_gaussSolve_eq_none n M y h
    exact absurd (hM x hx) hx0
  | some x => exact ⟨x, rfl, gaussSolve_sound n M y x h⟩

end
end LeanerVM.Protocol
