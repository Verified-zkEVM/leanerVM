/-
  LeanVM.Guest.B1.Sig.SpWotsArms

  An arm of `sp_wots`'s digit dispatch, sound: its walks reach their tips from the hinted starts,
  its product and encoding are folded.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsLayout
public import LeanVM.Guest.B1.Sig.SphincsKec
public import LeanVM.Guest.B1.Sig.SphincsHash

/-!
# `sp_wots`'s arms, sound

An arm of the template is the shared arm `armT spW …`, every chain step reading the padding run the
first group sets at `spPad`. So once that run holds `[0x01, 0, 0, 0, 0]` (`padRun_ok`), the chain
step is sound with the step function `spStepF` (`spW_step_sound`) and the shared arm's soundness
(`armT_sound`) applies.

* `SpArmOK`, `spArmK_sound`: what arm `k` establishes, its chain `r` started at `spStartOf … r`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

theorem padRun_ok {P : Nat} (h : AtomsHold rd σ (padRun P)) : PadOK σ P := by
  have e : ∀ k < 5, σ (.n (P + k)) = word (if k = 0 then 1 else 0) 0 0 := fun k hk =>
    h.atom (a := .const (.n (P + k)) _) (by
      simp only [padRun, cst, List.mem_map, List.mem_range]
      exact ⟨k, hk, rfl⟩)
  refine ⟨by simpa using e 0 (by norm_num), ?_, ?_, ?_, ?_⟩ <;>
    [have := e 1 (by norm_num); have := e 2 (by norm_num); have := e 3 (by norm_num);
      have := e 4 (by norm_num)] <;> simpa [word_zero] using this

/-! ## The chain step -/

/-- **`sp_wots`'s step, sound**, its run holding the padding: the output's first cell is the step's
hash of cells. -/
theorem spW_step_sound (hp : PadOK σ spPad) : StepSound rd σ spW (spStepF (σ (.n 0)) (σ (.n 1))) := by
  intro i s v c o h
  have h1 : σ (.n c) = word (tw 1 + i * hiMul + s * stepMul) 0 0 :=
    h.atom (a := .const (.n c) _) (by simp [spW, spWp, cst])
  have h2 : σ (.n (c + 1)) = σ (.n 1) + σ (.n c) :=
    h.atom (a := .add (.n (c + 1)) (.n 1) (.n c)) (by simp [spW, spWp, addS])
  have hk := k48At_sound hp (pp := .n 0) (a := .n (c + 1)) (v := v) (c := c + 2) (o := o)
    (h.sub fun x hx => by simp only [spW, spWp, List.mem_cons]; tauto)
  rw [spStepF, ← h1, ← h2]
  exact congrArg Prod.fst hk

/-! ## An arm -/

/-- **Chain `r`'s start in arm `k`**: its hint, or its tip at digit `3`, as the arm holds it. -/
def spStartOf (_first _n : Nat) (fold : Bool) (B : Nat) (_prodIn _encIn : V) (k b r : Nat) : V :=
  armStart spW (spSlot fold B) fold k b r

/-- **What arm `k` of a group establishes**, chain `r` starting at `start r`: each walk reaches the
slot of its last step from its start, the product and the encoding are folded into the group's
outputs. -/
structure SpArmOK (σ : Val) (first n : Nat) (fold : Bool) (B : Nat) (prodIn encIn : V) (k : Nat)
    (start : Nat → V) : Prop where
  tip : ∀ r < n, σ (.n (spSlot fold B r 2)) =
    chainT (spStepF (σ (.n 0)) (σ (.n 1))) (first + r) (3 - k / 4 ^ r % 4) (k / 4 ^ r % 4)
      (σ (start r))
  prod : σ (.n (spProd fold n B)) = (if fold then 1 else σ prodIn) * σ (.n (3 + digitSum k n))
  enc : σ (.n (spEnc fold n B)) = (if fold then 0 else σ encIn) + lit (k * 4 ^ first)

theorem digitSum_le_three (k : Nat) : ∀ n, digitSum k n ≤ 3 * n
  | 0 => le_refl _
  | n + 1 => by
      have := digitSum_le_three k n
      have := Nat.mod_lt (k / 4 ^ n) (show 4 > 0 by norm_num)
      simp only [digitSum]
      omega

theorem digitSum_le_nine (k n : Nat) (hn : n ≤ 3) : digitSum k n ≤ 9 :=
  le_trans (digitSum_le_three k n) (by omega)

/-- **Arm `k`, sound**: when the padding run holds and its atoms hold, it establishes `SpArmOK`
with its chains started at `spStartOf`. -/
theorem spArmK_sound {first n : Nat} {fold : Bool} {B : Nat} {prodIn encIn : V} {k b : Nat}
    (hp : PadOK σ spPad) (h : AtomsHold rd σ (spArmK first n fold B prodIn encIn k b).1) :
    SpArmOK σ first n fold B prodIn encIn k (spStartOf first n fold B prodIn encIn k b) :=
  let ha := armT_sound (spW_step_sound (rd := rd) hp) h
  ⟨ha.tip, ha.prod, ha.enc⟩

end
end LeanVM.Guest.B1.Sig
