/-
  LeanVM.Guest.B1.Sig.WotsGroup

  The layout of a WOTS+C group's arms: arm `0` lays the slots out after the group's base, every
  later arm starts above the product and the encoding.
-/

module

public import LeanVM.Guest.B1.Sig.WotsArm

/-!
# A group's layout

* `walksT_snd`, `armT_snd`, `armBase_succ`, `armsT_snd`: the bases;
* `slot_lt`, `slot_ge`: a group's slots lie between its first walk and its product;
* `armZeroLay`, `armPosLay`: the hypotheses of `armT_ssa`/`armT_canon` for arm `0` and for a later
  arm.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

theorem walksT_snd (W : WotsT) (slots : Nat → Nat → Nat) (first k stride : Nat) :
    ∀ (m r b : Nat), (walksT W slots first k stride m r b).2 = walkBase stride k r m b
  | 0, _, _ => rfl
  | m + 1, r, _ => walksT_snd W slots first k stride m (r + 1) _

theorem armT_snd (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) (k b : Nat) :
    (armT W slots first n fold prodIn encIn prodOut encOut k b).2 =
      if k = 0 then walkBase (W.size + 13) k 0 n (if fold then b + 1 else b)
      else walkBase W.size k 0 n (if fold then b + 1 else b) + 1 := by
  unfold armT
  split <;> simp_all [walksT_snd]

/-- The base after arm `k` from `a`. -/
def armNext (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) (k a : Nat) : Nat :=
  if k = 0 then (armT W slots first n fold prodIn encIn prodOut encOut k a).2 + 2
  else (armT W slots first n fold prodIn encIn prodOut encOut k a).2

theorem armBase_succ (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) : ∀ (k0 j b : Nat),
    armBase W slots first n fold prodIn encIn prodOut encOut k0 (j + 1) b =
      armNext W slots first n fold prodIn encIn prodOut encOut (k0 + j)
        (armBase W slots first n fold prodIn encIn prodOut encOut k0 j b)
  | k0, 0, b => by simp [armBase, armNext]
  | k0, j + 1, b => by
      rw [armBase, armBase_succ W slots first n fold prodIn encIn prodOut encOut (k0 + 1) j,
        show k0 + 1 + j = k0 + (j + 1) by omega]
      rfl

theorem armsT_snd (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) : ∀ (m k b : Nat),
    (armsT W slots first n fold prodIn encIn prodOut encOut m k b).2 =
      armBase W slots first n fold prodIn encIn prodOut encOut k m b
  | 0, _, _ => rfl
  | m + 1, k, _ => armsT_snd W slots first n fold prodIn encIn prodOut encOut m (k + 1) _

/-- The group's start, as a number. -/
theorem groupStart_eq (fold : Bool) (b : Nat) : groupStart fold b = b + 5 + (if fold then 1 else 0) := rfl

theorem chainStride_eq (W : WotsT) : chainStride W = 1 + 3 * (W.size + 13) := rfl

theorem slot_bounds (W : WotsT) (fold : Bool) (b t s : Nat) (hs : s < 3) :
    groupStart fold b + chainStride W * t + 1 ≤ slotsT W fold b t s ∧
      slotsT W fold b t s + 13 ≤ groupStart fold b + chainStride W * (t + 1) := by
  unfold slotsT
  rw [mul_add, mul_one, chainStride_eq]
  interval_cases s <;> omega

theorem slot_mono (W : WotsT) (fold : Bool) (b t : Nat) {s s' : Nat} (h : s < s') (hs : s' < 3) :
    slotsT W fold b t s + 13 ≤ slotsT W fold b t s' := by
  unfold slotsT
  have : s < 3 := by omega
  interval_cases s <;> interval_cases s' <;> omega

theorem chain_le (W : WotsT) (fold : Bool) (b : Nat) {t t' : Nat} (h : t < t') :
    groupStart fold b + chainStride W * (t + 1) ≤ groupStart fold b + chainStride W * t' :=
  Nat.add_le_add_left (Nat.mul_le_mul_left _ h) _

end
end LeanVM.Guest.B1.Sig
