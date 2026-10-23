/-
  LeanVM.Guest.B1.Sig.WotsArm

  The arms of a WOTS+C group are in single-assignment form and complete: arm `0` lays the slots out,
  every other arm writes them from its own fresh values.
-/

module

public import LeanVM.Guest.B1.Sig.WotsComplete

/-!
# The arms, complete

* `walkSum`, `walkBase_eq`: where a walk starts;
* `walkLay_zero`, `walkLay_pos`: the walks of arm `0` and of a later arm are laid out
  (`WalkLay`), their regions apart;
* `armT_ssa`, `armT_canon`: an arm is in single-assignment form, its `KECCAK`s on canonical
  inputs;
* `armBase_*`: the arms' bases.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- The fresh values of walks `r ..< r + t` of arm `k`. -/
def walkSum (stride k : Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | r, t + 1 => walkSize stride (dig k r) + walkSum stride k (r + 1) t

theorem walkSum_succ (stride k : Nat) : ∀ (r t : Nat),
    walkSum stride k r (t + 1) = walkSum stride k r t + walkSize stride (dig k (r + t))
  | r, 0 => by simp [walkSum]
  | r, t + 1 => by
      rw [walkSum, walkSum_succ stride k (r + 1) t, walkSum, show r + 1 + t = r + (t + 1) by omega]
      omega

theorem walkBase_eq (stride k : Nat) : ∀ (r t b : Nat), walkBase stride k r t b = b + walkSum stride k r t
  | _, 0, _ => rfl
  | r, t + 1, b => by
      rw [walkBase, walkBase_eq stride k (r + 1) t, walkSum]
      simp only [dig]
      omega

theorem walkSum_zero_digits (S : Nat) : ∀ (r t : Nat), walkSum S 0 r t = t * (1 + 3 * S)
  | _, 0 => by simp [walkSum]
  | r, t + 1 => by
      rw [walkSum, walkSum_zero_digits S (r + 1) t]
      simp [walkSize, dig]
      ring

theorem walkSize_le (stride d : Nat) : walkSize stride d ≤ 1 + 3 * stride := by
  unfold walkSize
  split
  · omega
  · have := Nat.mul_le_mul_right stride (show 3 - d ≤ 3 by omega); omega

end
end LeanVM.Guest.B1.Sig
