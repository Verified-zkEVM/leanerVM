/-
  LeanVM.Guest.B1.Comp.Digest.Common

  Loops, backward, under any semantics.
-/

module

public import LeanVM.Guest.B1.Comp.Basic
public import LeanVM.Guest.B1.Digest.CommonM

/-!
# `mul_range` loops, backward, under any semantics

`loopB_bwd`: the backward half of `loop_iff` under any semantics `S` (`loopB_fwd` is the forward
half): a loop helper whose body, at `x`, holds when its iteration `B x` does and the conditional
call to `x·g` holds, holds from `g^k` to `N = g^m` when every iteration does.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- **A `mul_range` loop helper, backward, under any semantics** (`loop_iff`'s backward half). -/
theorem loopB_bwd {S : BlakeSem} {rd : Reader} {f : String} {ps : List E} {N : E}
    {B : E → Prop}
    (hstep : ∀ x, B x → IsInK (x * gen + N) →
      (x * gen + N ≠ 0 → coreProgram.RelB S rd f (x * gen :: ps) []) →
      ∃ fn, coreProgram.find? f = some fn ∧ fn.SemB S (coreProgram.RelB S rd) rd (x :: ps) [])
    {k m : ℕ} (hkm : k < m) (hN : N = gen ^ m) (hall : ∀ j, k ≤ j → j < m → B (gen ^ j)) :
    coreProgram.RelB S rd f (gen ^ k :: ps) [] := by
  have hadd : ∀ j, gen ^ j * gen + N = 0 ↔ N = gen ^ (j + 1) := fun j => by
    rw [e_add_eq_zero_iff, pow_succ, eq_comm]
  obtain ⟨t, rfl⟩ : ∃ t, m = k + 1 + t := ⟨m - k - 1, by omega⟩
  have hK : ∀ j, IsInK (gen ^ j * gen + N) := fun j => by
    rw [hN, ← pow_succ, gen_pow_eq_ofK, gen_pow_eq_ofK, ← ofK_add]; exact ofK_isInK _
  induction t generalizing k with
  | zero =>
    rw [relB_iff]
    exact hstep _ (hall k le_rfl (by omega)) (hK k) fun h => absurd ((hadd k).mpr hN) h
  | succ t ih =>
    rw [relB_iff]
    refine hstep _ (hall k le_rfl (by omega)) (hK k) fun _ => ?_
    rw [← pow_succ]
    exact ih (k := k + 1) (by omega) (by rw [hN]; congr 1; omega)
      (fun j h1 h2 => hall j (by omega) (by omega))

/-- **A loop behind its guard, backward, under any semantics** (`guarded_loop_iff`'s backward
half): `for x in mul_range(1, N)`, `N = g^m`, every iteration holding. -/
theorem guarded_loopB_bwd {S : BlakeSem} {rd : Reader} {f : String} {ps : List E} {N : E}
    {B : E → Prop}
    (hstep : ∀ x, B x → IsInK (x * gen + N) →
      (x * gen + N ≠ 0 → coreProgram.RelB S rd f (x * gen :: ps) []) →
      ∃ fn, coreProgram.find? f = some fn ∧ fn.SemB S (coreProgram.RelB S rd) rd (x :: ps) [])
    {m : ℕ} (hN : N = gen ^ m) (hall : ∀ j < m, B (gen ^ j)) :
    IsInK (1 + N) ∧ (1 + N ≠ 0 → coreProgram.RelB S rd f (1 :: ps) []) := by
  refine ⟨?_, fun h1 => ?_⟩
  · rw [hN]
    exact isInK_add (by rw [← pow_zero gen]; exact gen_pow_isInK 0) (gen_pow_isInK m)
  · have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · exact absurd (show 1 + N = 0 by rw [hN, h, pow_zero]; exact e_add_self 1) h1
      · exact h
    have := loopB_bwd (k := 0) hstep hm0 hN (fun j _ hj => hall j hj)
    rwa [pow_zero] at this

end
end LeanVM.Guest.B1.Digest
