/-
  LeanVM.Guest.B1.Sig.SphincsSoundPath

  `sp_path` (`lean_ethereum.py:3634-3651` at leanVM `542b0353`) is sound: whatever children are
  hinted, the node a path reaches is the tree's fold of the hinted siblings.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsPathComplete
public import LeanVM.Guest.B1.Sig.SphincsKec
public import LeanVM.Guest.B1.Sig.Merkle

/-!
# `sp_path`, sound

* `isChild_sound`: `is_child` makes the node the hinted child its bit names, the two children
  being the node and its sibling `siblingOf` in the bit's order (`mPair`);
* `sPath_sound`: `sp_path` of `h` levels from bit `off`, its bits those of `e` and its shifted
  values `e`'s, reaches `pFold` of `tNode` at the lane, the siblings hinted at `x + 21 l`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (eOfNat)

@[expose] public section

variable {rd : Reader} {σ : Val}

/-- **The sibling of a node** whose two children are hinted at `x`, `x + 1`, the node climbed the
one the bit names: the left child when the bit is `1`. -/
def siblingOf (σ : Val) (bit : V) (x : Nat) : E :=
  if σ bit = 1 then σ (.n x) else σ (.n (x + 1))

/-- **`is_child`, sound**: the children are the node and its sibling, in the order of the bit. -/
theorem isChild_sound {cur bit : V} {x b : Nat} (hbit : IsBit (σ bit))
    (e1 : σ (.n b) = σ cur + σ (.n x)) (e2 : σ (.n (b + 1)) = σ (.n x) + σ (.n (x + 1)))
    (e3 : σ (.n b) = σ bit * σ (.n (b + 1))) :
    (σ (.n x), σ (.n (x + 1))) = mPair (decide (σ bit = 1)) (σ cur) (siblingOf σ bit x) := by
  rcases isBit_cases hbit with h0 | h1
  · rw [h0, zero_mul, e1] at e3
    have : σ cur = σ (.n x) := e_add_eq_zero_iff.mp e3
    simp [h0, this, mPair, siblingOf]
  · rw [h1, one_mul, e1, e2] at e3
    have : σ cur = σ (.n (x + 1)) :=
      add_left_cancel (a := σ (.n x)) (by rw [add_comm (σ (.n x))]; exact e3)
    simp [h1, this, mPair, siblingOf]

/-- The address of a path level: the lane, its constant and the shifted index. -/
theorem tAdr_zero (L : E) (l : Nat) : tAdr L l 0 = L + word (tw 3 + (l + 1) * hiMul) 0 0 := by
  simp [tAdr, Value.eOfNat_zero]

/-- **One level of a path**, its node address `adr`. -/
theorem pathLevel_sound (hp : PadOK σ sPad) {cur bit adr : V} {x : Nat} (hbit : IsBit (σ bit))
    (hc : AtomsHold rd σ [addS (.n (x + 2)) cur (.n x), addS (.n (x + 3)) (.n x) (.n (x + 1)),
      mulS (.n (x + 2)) bit (.n (x + 3))])
    {c : Nat} (hk : AtomsHold rd σ (k64 sPad sPP adr (.n x) (.n (x + 1)) c (c + 1))) :
    σ (.n (c + 1)) = (hcell [σ sPP, σ adr, (mPair (decide (σ bit = 1)) (σ cur) (siblingOf σ bit x)).1,
      (mPair (decide (σ bit = 1)) (σ cur) (siblingOf σ bit x)).2]).1 := by
  have e1 : σ (.n (x + 2)) = σ cur + σ (.n x) := hc.atom (a := .add _ _ _) (by simp [addS])
  have e2 : σ (.n (x + 3)) = σ (.n x) + σ (.n (x + 1)) := hc.atom (a := .add _ _ _) (by simp [addS])
  have e3 : σ (.n (x + 2)) = σ bit * σ (.n (x + 3)) := hc.atom (a := .mul _ _ _) (by simp [mulS])
  rw [← isChild_sound hbit e1 e2 e3]
  exact congrArg Prod.fst (k64_sound hp hk)

/-- The node of a path at level `l` whose leaf is `e`, its siblings hinted at `x + 21 l`. -/
def pathNode (σ : Val) (lane : V) (off e x : Nat) : Nat → E → E :=
  tNode (σ sPP) (σ lane) e fun j => siblingOf σ (sBit (off + j)) (x + 21 * j)

/-- **`sp_path`, sound**: from level `l` (base `x + 21 l`), `m` levels to height `h`, the bits
those of `e < 2^h` and the shifted values `e`'s, the node reached is `nIter` of the levels. -/
theorem sPath_sound (hp : PadOK σ sPad) {lane : V} {off e h x : Nat} (he : e < 2 ^ h)
    (hbit : ∀ l < h, σ (sBit (off + l)) = if e.testBit l then 1 else 0)
    (hval : ∀ l, l + 1 < h → σ (sVal (off + l + 1)) = eOfNat (e >>> (l + 1))) :
    ∀ (m l : Nat) (cur : V), l + m = h →
      AtomsHold rd σ (sPath lane off m l cur (x + 21 * l)).1 →
      σ (sPath lane off m l cur (x + 21 * l)).2.2 = nIter (pathNode σ lane off e x) l m (σ cur)
  | 0, _, _, _, _ => rfl
  | m + 1, l, cur, hm, hA => by
      have hb := hbit l (by omega)
      have hib : IsBit (σ (sBit (off + l))) := by rw [hb]; split <;> simp [IsBit]
      have hd : decide (σ (sBit (off + l)) = 1) = e.testBit l := by
        rw [hb]; cases e.testBit l <;> simp [one_ne_zero_E.symm]
      set X := x + 21 * l with hX
      rcases m with _ | m
      · rw [sPath_eq_last] at hA ⊢
        have hc := hA.left.left.sub (ss' := [addS (.n (X + 2)) cur (.n X),
          addS (.n (X + 3)) (.n X) (.n (X + 1)), mulS (.n (X + 2)) (sBit (off + l)) (.n (X + 3))])
          (fun s hs => by simp only [List.mem_cons, List.not_mem_nil] at hs ⊢; tauto)
        have hk := hA.right
        rw [show X + 6 - 1 = X + 5 by omega] at hk
        have ha5 : σ (.n (X + 5)) = σ lane + σ (.n (X + 4)) :=
          hA.atom (a := .add _ _ _) (by simp [addS])
        have ha4 : σ (.n (X + 4)) = word (tw 3 + (l + 1) * hiMul) 0 0 :=
          hA.atom (a := .const _ _) (by simp [cst])
        have hq : e >>> (l + 1) = 0 := by
          rw [Nat.shiftRight_eq_div_pow]
          exact Nat.div_eq_of_lt (lt_of_lt_of_le he (Nat.pow_le_pow_right (by norm_num) (by omega)))
        simp only [nIter]
        rw [show X + 6 + 1 = (X + 6) + 1 from rfl, pathLevel_sound hp hib hc hk, hd, ha5, ha4,
          pathNode, tNode, hq, tAdr_zero, hX]
      · rw [sPath_eq_step] at hA ⊢
        have hc := hA.left.left.left.sub (ss' := [addS (.n (X + 2)) cur (.n X),
          addS (.n (X + 3)) (.n X) (.n (X + 1)), mulS (.n (X + 2)) (sBit (off + l)) (.n (X + 3))])
          (fun s hs => by simp only [List.mem_cons, List.not_mem_nil] at hs ⊢; tauto)
        have hk := hA.left.right
        rw [show X + 7 - 1 = X + 6 by omega] at hk
        have ha6 : σ (.n (X + 6)) = σ (.n (X + 5)) + σ (sVal (off + l + 1)) :=
          hA.left.atom (a := .add (.n (X + 6)) _ _) (by simp [addS])
        have ha5 : σ (.n (X + 5)) = σ lane + σ (.n (X + 4)) :=
          hA.left.atom (a := .add (.n (X + 5)) _ _) (by simp [addS])
        have ha4 : σ (.n (X + 4)) = word (tw 3 + (l + 1) * hiMul) 0 0 :=
          hA.left.atom (a := .const _ _) (by simp [cst])
        have hrest := sPath_sound hp he hbit hval (m + 1) (l + 1) (.n (X + 8)) (by omega)
          (by rw [show x + 21 * (l + 1) = X + 21 by omega]; exact hA.right)
        rw [show x + 21 * (l + 1) = X + 21 by omega] at hrest
        rw [hrest, nIter, show X + 8 = (X + 7) + 1 from rfl, pathLevel_sound hp hib hc hk, hd, ha6, ha5,
          ha4, hval l (by omega)]
        rfl

/-- **A whole path**: `h ≥ 1` levels from level `0` at base `x` reach `pFold` of the levels. -/
theorem sPath_sound_all (hp : PadOK σ sPad) {lane : V} {off e h x : Nat} (he : e < 2 ^ h)
    (hbit : ∀ l < h, σ (sBit (off + l)) = if e.testBit l then 1 else 0)
    (hval : ∀ l, l + 1 < h → σ (sVal (off + l + 1)) = eOfNat (e >>> (l + 1))) {cur : V}
    (hA : AtomsHold rd σ (sPath lane off h 0 cur x).1) :
    σ (sPath lane off h 0 cur x).2.2 = pFold (pathNode σ lane off e x) h (σ cur) := by
  rw [← nIter_zero]
  exact sPath_sound hp he hbit hval h 0 cur (by omega) hA

end
end LeanVM.Guest.B1.Sig
