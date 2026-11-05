/-
  LeanVM.Guest.B1.Sig.SphincsSoundFors

  The FORS trees of `verify_sig_lean_sphincs` (`sp_fors_tree`, `lean_ethereum.py:3756-3775` at
  leanVM `1a379148`) are sound: whatever secrets and children are hinted, each tree's two top
  nodes are `fTops` of the hinted secret and siblings.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsSoundPath

/-!
# FORS, sound

Tree `c` from base `b` hints its secret at `b` and the children of level `l` at `b + 22 + 23 l`
(the top ones at `b + 229`); `forsSib σ c b l` is the sibling of level `l` (`siblingOf`).

* `sForsLevels_sound`: the nine levels climb `nIter` of `fNode`;
* `sForsTree_sound`: the two top nodes are `fTops` at the index's cell and the field's leaf;
* `sForsTrees_tops`, `sForsTrees_sound`: the 24 trees from `1225`, tree `c`'s at
  `1225 + 233 c`, their top nodes in order.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (eOfNat)

@[expose] public section

variable {rd : Reader} {σ : Val}

/-- The sibling of level `l` of FORS tree `c` from base `b`. -/
def forsSib (σ : Val) (c b l : Nat) : E := siblingOf σ (sBit (fOff c + l)) (b + 22 + 23 * l)

theorem word_two_pow_mul_eOfNat {k v : Nat} (h : 2 ^ k * v < 2 ^ 64) :
    eOfNat v * word (2 ^ k) 0 0 = eOfNat (2 ^ k * v) := by
  rw [word_eq_eOfNat, mul_comm, eOfNat_two_pow_mul h]

/-- **A FORS tree's levels, sound**: from level `l` (base `x + 23 l`), `m` levels up to `9`, at
the node base holding `I + (TW_FNODE + c·2^32)`, the node reached is `nIter` of `fNode`. -/
theorem sForsLevels_sound (hp : PadOK σ sPad) {c s : Nat} (hs : s < 2 ^ 10) {base : V} {I : E} {x : Nat}
    (hbase : σ base = I + word (tw 17 + c * hiMul) 0 0)
    (hbit : ∀ j < 10, σ (sBit (fOff c + j)) = if s.testBit j then 1 else 0)
    (hval : ∀ j < 10, σ (sVal (fOff c + j)) = eOfNat (s >>> j)) :
    ∀ (m l : Nat) (cur : V), l + m ≤ 9 →
      AtomsHold rd σ (sForsLevels c base m l cur (x + 23 * l)).1 →
      σ (sForsLevels c base m l cur (x + 23 * l)).2.2 =
        nIter (fNode (σ sPP) I c s fun j => siblingOf σ (sBit (fOff c + j)) (x + 23 * j)) l m (σ cur)
  | 0, _, _, _, _ => rfl
  | m + 1, l, cur, hm, hA => by
      rw [sForsLevels_succ] at hA ⊢
      set X := x + 23 * l with hX
      have hb := hbit l (by omega)
      have hib : IsBit (σ (sBit (fOff c + l))) := by rw [hb]; split <;> simp [IsBit]
      have hd : decide (σ (sBit (fOff c + l)) = 1) = s.testBit l := by
        rw [hb]; cases s.testBit l <;> simp [one_ne_zero_E.symm]
      have hL := hA.left
      rw [sForsLevel_eq] at hL
      have hc := hL.left.left.sub (ss' := [addS (.n (X + 2)) cur (.n X),
        addS (.n (X + 3)) (.n X) (.n (X + 1)), mulS (.n (X + 2)) (sBit (fOff c + l)) (.n (X + 3))])
        (fun s hs => by simp only [List.mem_cons, List.not_mem_nil] at hs ⊢; tauto)
      have hk := hL.right
      rw [show X + 9 - 1 = X + 8 by omega] at hk
      have hN := hL.left.right
      have a4 : σ (.n (X + 4)) = word (64 * (l + 1) * hiMul) 0 0 :=
        hL.left.left.atom (a := .const _ _) (by simp [cst])
      have a5 : σ (.n (X + 5)) = σ base + σ (.n (X + 4)) := hN.atom (a := .add _ _ _) (by simp [fNodeL, addS])
      have a6 : σ (.n (X + 6)) = word (2 ^ 42) 0 0 := hN.atom (a := .const _ _) (by simp [fNodeL, cst])
      have a7 : σ (.n (X + 7)) = σ (sVal (fOff c + l + 1)) * σ (.n (X + 6)) :=
        hN.atom (a := .mul _ _ _) (by simp [fNodeL, mulS])
      have a8 : σ (.n (X + 8)) = σ (.n (X + 5)) + σ (.n (X + 7)) :=
        hN.atom (a := .add (.n (X + 8)) _ _) (by simp [fNodeL, addS])
      have hq : s >>> (l + 1) < 2 ^ 10 := lt_of_le_of_lt (Nat.shiftRight_le _ _) hs
      have hrest := sForsLevels_sound hp hs hbase hbit hval m (l + 1) (.n (X + 10)) (by omega)
        (by rw [show x + 23 * (l + 1) = X + 23 by omega]; exact hA.right)
      rw [show x + 23 * (l + 1) = X + 23 by omega] at hrest
      rw [hrest, nIter, show X + 10 = (X + 9) + 1 from rfl, pathLevel_sound hp hib hc hk, hd, a8, a5, a7,
        a6, a4, hbase, show σ (sVal (fOff c + l + 1)) = eOfNat (s >>> (l + 1)) from hval (l + 1) (by omega),
        word_two_pow_mul_eOfNat (by omega)]
      rfl

/-- **FORS tree `c` from base `b`, sound**: at the index `σ sIdx = I`, the leaf `s` its field
gives, the two top nodes are `fTops` of the hinted secret and the siblings. -/
theorem sForsTree_sound (hp : PadOK σ sPad) {c s b : Nat} (hs : s < 2 ^ 10) {I : E} (hI : σ sIdx = I)
    (hbit : ∀ j < 10, σ (sBit (fOff c + j)) = if s.testBit j then 1 else 0)
    (hval : ∀ j < 10, σ (sVal (fOff c + j)) = eOfNat (s >>> j))
    (hA : AtomsHold rd σ (sForsTree c b).1) :
    (σ (.n (b + 229)), σ (.n (b + 230))) = fTops (σ sPP) I c s (σ (.n b)) (forsSib σ c b) := by
  rw [sForsTree_eq] at hA
  dsimp only at hA
  have hP : AtomsHold rd σ (fLeafPre c b ++ _) := hA.sub fun x hx => List.mem_cons_of_mem _ hx
  have hLP := hP.left
  have hR := hP.right
  have hK := hR.left
  have hR2 := hR.right
  have hB := hR2.left
  have hR3 := hR2.right
  have hLv := hR3.left
  have hT := hR3.right
  -- the leaf
  have l1 : σ (.n (b + 1)) = word (tw 15 + c * hiMul) 0 0 := hLP.atom (a := .const _ _) (by simp [fLeafPre, cst])
  have l2 : σ (.n (b + 2)) = σ sIdx + σ (.n (b + 1)) := hLP.atom (a := .add (.n (b + 2)) _ _) (by simp [fLeafPre, addS])
  have l3 : σ (.n (b + 3)) = word (2 ^ 38) 0 0 := hLP.atom (a := .const (.n (b + 3)) _) (by simp [fLeafPre, cst])
  have l4 : σ (.n (b + 4)) = σ (sVal (fOff c)) * σ (.n (b + 3)) :=
    hLP.atom (a := .mul _ _ _) (by simp [fLeafPre, mulS])
  have l5 : σ (.n (b + 5)) = σ (.n (b + 2)) + σ (.n (b + 4)) :=
    hLP.atom (a := .add (.n (b + 5)) _ _) (by simp [fLeafPre, addS])
  have hleaf : σ (.n (b + 7)) = fLeaf (σ sPP) I c s (σ (.n b)) := by
    have := congrArg Prod.fst (k48_sound hp hK)
    simp only at this
    rw [this, l5, l2, l1, l4, l3, hI, show σ (sVal (fOff c)) = eOfNat s by
      rw [show fOff c = fOff c + 0 from rfl, hval 0 (by norm_num)]; rfl,
      word_two_pow_mul_eOfNat (by omega)]
    rfl
  -- the node base
  have b20 : σ (.n (b + 20)) = word (tw 17 + c * hiMul) 0 0 := hB.atom (a := .const _ _) (by simp [fBasePre, cst])
  have b21 : σ (.n (b + 21)) = σ sIdx + σ (.n (b + 20)) := hB.atom (a := .add _ _ _) (by simp [fBasePre, addS])
  have hbase : σ (.n (b + 21)) = I + word (tw 17 + c * hiMul) 0 0 := by rw [b21, b20, hI]
  -- the levels
  have hlv := sForsLevels_sound (x := b + 22) hp hs hbase hbit hval 9 0 (.n (b + 7)) (by norm_num)
    (by simpa using hLv)
  obtain ⟨-, h2⟩ := sForsLevels_shape c (.n (b + 21)) 9 0 (.n (b + 7)) (b + 22)
  simp only [Nat.mul_zero, Nat.add_zero, h2, show (9 : Nat) ≠ 0 by decide, ↓reduceIte,
    show b + 22 + 23 * 9 - 13 = b + 216 by omega] at hlv
  rw [nIter_zero, hleaf] at hlv
  -- the top
  have t1 : σ (.n (b + 231)) = σ (.n (b + 216)) + σ (.n (b + 229)) :=
    hT.atom (a := .add (.n (b + 231)) _ _) (by simp [fTopChk, addS])
  have t2 : σ (.n (b + 232)) = σ (.n (b + 229)) + σ (.n (b + 230)) :=
    hT.atom (a := .add (.n (b + 232)) _ _) (by simp [fTopChk, addS])
  have t3 : σ (.n (b + 231)) = σ (sBit (fOff c + 9)) * σ (.n (b + 232)) :=
    hT.atom (a := .mul _ _ _) (by simp [mulS])
  have hb9 := hbit 9 (by norm_num)
  have hib : IsBit (σ (sBit (fOff c + 9))) := by rw [hb9]; split <;> simp [IsBit]
  have hd : decide (σ (sBit (fOff c + 9)) = 1) = s.testBit 9 := by
    rw [hb9]; cases s.testBit 9 <;> simp [one_ne_zero_E.symm]
  rw [isChild_sound (x := b + 229) hib t1 t2 t3, hd, hlv, fTops]
  rfl

/-- FORS tree `c`'s base in `verify_sig_lean_sphincs`. -/
theorem sForsTrees_base : ∀ (m c b : Nat), (sForsTrees m c b).2.2 =
    (List.range m).flatMap fun k => [V.n (b + 233 * k + 229), .n (b + 233 * k + 230)]
  | 0, _, _ => rfl
  | m + 1, c, b => by
      have e : (sForsTrees (m + 1) c b).2.2 = (sForsTree c b).2.2.1 :: (sForsTree c b).2.2.2 ::
        (sForsTrees m (c + 1) (sForsTree c b).2.1).2.2 := rfl
      rw [e, sForsTree_eq]
      dsimp only
      rw [sForsTrees_base m (c + 1) (b + 233), List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
      simp only [Nat.mul_zero, Nat.add_zero, List.cons_append, List.nil_append, Nat.succ_eq_add_one,
        show ∀ k, b + 233 + 233 * k = b + 233 * (k + 1) from fun k => by ring]

/-- **The FORS trees, sound**: `m` trees from tree `c` at base `b`, tree `c + k`'s top nodes at
`b + 233 k + 229`, `+ 230` are `fTops` of its hinted secret at `b + 233 k`. -/
theorem sForsTrees_sound (hp : PadOK σ sPad) {I : E} (hI : σ sIdx = I) {s : Nat → Nat}
    (hs : ∀ c < 24, s c < 2 ^ 10)
    (hbit : ∀ c < 24, ∀ j < 10, σ (sBit (fOff c + j)) = if (s c).testBit j then 1 else 0)
    (hval : ∀ c < 24, ∀ j < 10, σ (sVal (fOff c + j)) = eOfNat (s c >>> j)) :
    ∀ (m c b : Nat), c + m ≤ 24 → AtomsHold rd σ (sForsTrees m c b).1 → ∀ k < m,
      (σ (.n (b + 233 * k + 229)), σ (.n (b + 233 * k + 230))) =
        fTops (σ sPP) I (c + k) (s (c + k)) (σ (.n (b + 233 * k))) (forsSib σ (c + k) (b + 233 * k))
  | 0, _, _, _, _, k, hk => absurd hk (by omega)
  | m + 1, c, b, hcm, hA, k, hk => by
      rw [(sForsTrees_succ m c b).1] at hA
      rcases k with _ | k
      · simpa using sForsTree_sound hp (hs c (by omega)) hI (hbit c (by omega)) (hval c (by omega)) hA.left
      · have := sForsTrees_sound hp hI hs hbit hval m (c + 1) (b + 233) (by omega) hA.right k (by omega)
        rw [show c + (k + 1) = c + 1 + k by omega, show b + 233 * (k + 1) = b + 233 + 233 * k by ring]
        exact this

end
end LeanVM.Guest.B1.Sig
