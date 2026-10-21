/-
  LeanVM.Guest.B1.Comp.Sig.Group

  A digit group of a WOTS+C codeword, complete over a completeness model (`cGroup_complete`).
-/

module

public import LeanVM.Guest.B1.Comp.Sig.Arm

/-!
# A digit group over a completeness model

`Group.lean`'s completeness over a `CompModel`: the presets of the tips the model's chain ends
(`groupPresetC`), the arm `cArm_comp`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.E2E.Complete

@[expose] public section

variable {CM : CompModel} {C : CallRel} {rd : Reader}

theorem holdsListB_match_singleS {S : BlakeSem} (x : V) (arms : List (List Stmt)) (next : Prop)
    (kret : List E → Prop) (σ : Val) :
    Stmt.HoldsListB S C rd σ [.match_ x arms] next kret ↔
      ∃ (j : Nat) (h : j < arms.length), σ x = ofK (gpow j) ∧ Stmt.HoldsListB S C rd σ arms[j] next kret := by
  simp only [Stmt.HoldsListB]
  exact holdsB_match_iff x arms next kret

/-- A group's presets over the model (`groupPreset`): the digit, its bound and the range check's values, then the tips, then the
product and the encoding. -/
def groupPresetC (CM : CompModel) (w : Wots) (σ : Val) (power : Nat → V) (prodIn encIn : V) (first n : Nat) (fold : Bool)
    (b k : Nat) (y t1 t2 : E) (xs : Nat → E) : Val :=
  let s0 := groupStart fold b
  let st := chainStride w.lx
  let tp := fun r => tipPairC CM w.lx (w.pp' σ) (w.adr' σ) (w.idx' σ) (first + r) (armDigit k r) (xs r)
  let σa := patch σ b (b + 5) fun j =>
    if j = b then ofK (gpow k) else if j = b + 1 then word (2 ^ (4 ^ n - 1)) 0 0
    else if j = b + 2 then y else if j = b + 3 then t1 else t2
  let σb := patch σa s0 (s0 + st * n) (tipsPre w.lx s0 tp σa)
  patch σb (s0 + st * n) (s0 + st * n + 2) fun j =>
    if j = s0 + st * n then (if fold then 1 else σ prodIn) * σ (power (digitSum k n))
    else (if fold then 0 else σ encIn) + lit (k * 4 ^ first)

section Pre

variable (CM) (w : Wots) (σ : Val) (power : Nat → V) (prodIn encIn : V) (first n : Nat) (fold : Bool)
  (b k : Nat) (y t1 t2 : E) (xs : Nat → E)

theorem groupPresetC_ext :
    Ext b (groupStart fold b + chainStride w.lx * n + 2) σ
      (groupPresetC CM w σ power prodIn encIn first n fold b k y t1 t2 xs) := by
  have h5 := groupStart_ge fold b
  unfold groupPresetC
  exact ((patch_ext _ _ _ _).mono le_rfl (by omega)).comp
    (((patch_ext _ _ _ _).mono (by omega) (by omega)).comp ((patch_ext _ _ _ _).mono (by omega) le_rfl))

theorem groupPresetC_low {j : Nat} (h1 : b ≤ j) (h2 : j < b + 5) :
    groupPresetC CM w σ power prodIn encIn first n fold b k y t1 t2 xs (.n j) =
      if j = b then ofK (gpow k) else if j = b + 1 then word (2 ^ (4 ^ n - 1)) 0 0
      else if j = b + 2 then y else if j = b + 3 then t1 else t2 := by
  have h5 := groupStart_ge fold b
  unfold groupPresetC
  rw [patch_out _ _ (by omega), patch_out _ _ (by omega), patch_at _ _ h1 h2]

theorem groupPresetC_tip {r : Nat} (hr : r < n) :
    groupPresetC CM w σ power prodIn encIn first n fold b k y t1 t2 xs
        (.n (groupStart fold b + chainStride w.lx * r + walkSize w.lx 0)) =
      (tipPairC CM w.lx (w.pp' σ) (w.adr' σ) (w.idx' σ) (first + r) (armDigit k r) (xs r)).1 ∧
    groupPresetC CM w σ power prodIn encIn first n fold b k y t1 t2 xs
        (.n (groupStart fold b + chainStride w.lx * r + walkSize w.lx 0 + 1)) =
      (tipPairC CM w.lx (w.pp' σ) (w.adr' σ) (w.idx' σ) (first + r) (armDigit k r) (xs r)).2 := by
  have hst := ws_lt_stride w.lx
  have hm : chainStride w.lx * r + chainStride w.lx ≤ chainStride w.lx * n := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hr
  have ht := tipsPre_tip w.lx (groupStart fold b) (fun r => tipPairC CM w.lx (w.pp' σ) (w.adr' σ) (w.idx' σ)
    (first + r) (armDigit k r) (xs r)) (patch σ b (b + 5) fun j =>
    if j = b then ofK (gpow k) else if j = b + 1 then word (2 ^ (4 ^ n - 1)) 0 0
    else if j = b + 2 then y else if j = b + 3 then t1 else t2) r
  unfold groupPresetC
  constructor
  · rw [patch_out _ _ (by omega), patch_at _ _ (by omega) (by omega)]; exact ht.1
  · rw [patch_out _ _ (by omega), patch_at _ _ (by omega) (by omega)]; exact ht.2

theorem groupPresetC_out :
    groupPresetC CM w σ power prodIn encIn first n fold b k y t1 t2 xs (.n (groupStart fold b + chainStride w.lx * n)) =
      (if fold then 1 else σ prodIn) * σ (power (digitSum k n)) ∧
    groupPresetC CM w σ power prodIn encIn first n fold b k y t1 t2 xs
        (.n (groupStart fold b + chainStride w.lx * n + 1)) =
      (if fold then 0 else σ encIn) + lit (k * 4 ^ first) := by
  unfold groupPresetC
  constructor
  · rw [patch_at _ _ le_rfl (by omega)]; simp
  · rw [patch_at _ _ (by omega) (by omega)]; simp

end Pre

/-- **A group is complete over the model** (`cGroup_complete`): for a digit value `k` in range and
the chains' values `xs`, their steps answered, a valuation under which the group holds, its chains'
tips, product and encoding those of arm `k`. -/
theorem cGroup_comp {w : Wots} {power : Nat → V} {prodIn encIn : V} {first n : Nat} {fold : Bool}
    {b : Nat} {σ : Val} (hrd : MemOK rd (4 ^ n)) (hn : n ≤ 3) (hw : w.Below b)
    (hin : NB b prodIn ∧ NB b encIn ∧ ∀ s < 10, NB b (power s)) (hmd : σ w.md = mdw (stepCount w.lx) true)
    (hc : w.Canon σ) {k : Nat} (hk : k < 4 ^ n) {xs : Nat → E} (hx : ∀ r < n, IsCanonical128 (xs r))
    (ha : ∀ r < n, TipAnsC CM w σ (first + r) (armDigit k r) (xs r)) :
    CompletesB CM.sem C rd b (cGroup w power prodIn encIn first n fold b).2 (cGroup w power prodIn encIn first n fold b).1 σ
      (fun σ' => σ' (.n b) = ofK (gpow k) ∧
        (∀ r < n, TipSetC CM w σ' (first + r) (armDigit k r) (xs r) (groupTips w.lx fold b r)) ∧
        ArmFold σ' power prodIn encIn (groupProd w.lx fold n b) (groupEnc w.lx fold n b) first n k fold) := by
  have h4 : 1 ≤ 4 ^ n := Nat.one_le_pow _ _ (by norm_num)
  have h64 : 4 ^ n ≤ 64 := le_trans (Nat.pow_le_pow_right (by norm_num) hn) (by norm_num)
  obtain ⟨y, t1, t2, hl1, hl2, hl3⟩ := rangeCheck_witness hrd h4 hk
  have h5 := groupStart_ge fold b
  have hst := ws_lt_stride w.lx
  set tips := groupTips w.lx fold b with htips_def
  set A := cArms w tips power prodIn encIn (groupProd w.lx fold n b) (groupEnc w.lx fold n b) first n fold
    (4 ^ n) 0 (b + 5) with hA
  have ha0 : (cArm w tips power prodIn encIn (groupProd w.lx fold n b) (groupEnc w.lx fold n b) first n 0 fold
      true (b + 5)).2 = groupStart fold b + chainStride w.lx * n + 2 := by
    rw [cArm_snd, armWalksEnd, cWalks_snd_fresh, groupStart_eq]; simp
  obtain ⟨b0, -, -, h0le, -, hb0⟩ := cArms_get w tips power prodIn encIn (groupProd w.lx fold n b)
    (groupEnc w.lx fold n b) first n fold (4 ^ n) 0 (b + 5) 0 (by omega)
  rw [hb0 rfl, Nat.zero_add] at h0le
  simp only [beq_self_eq_true] at h0le
  rw [ha0] at h0le
  obtain ⟨bk, hgk, hbk, hkle, h0k, hk0⟩ := cArms_get w tips power prodIn encIn (groupProd w.lx fold n b)
    (groupEnc w.lx fold n b) first n fold (4 ^ n) 0 (b + 5) k hk
  simp only [Nat.zero_add] at hgk hkle h0k
  simp only [beq_self_eq_true] at h0k
  rw [ha0] at h0k
  set σ1 := groupPresetC CM w σ power prodIn encIn first n fold b k y t1 t2 xs with hσ1
  have he1 := groupPresetC_ext CM w σ power prodIn encIn first n fold b k y t1 t2 xs
  rw [← hσ1] at he1
  have hk1 := hw.keep he1
  have hlow := fun {j : Nat} (h1 : b ≤ j) (h2 : j < b + 5) =>
    groupPresetC_low CM w σ power prodIn encIn first n fold b k y t1 t2 xs h1 h2
  have htip := fun {r : Nat} (hr : r < n) => groupPresetC_tip CM w σ power prodIn encIn first n fold b k y t1 t2 xs hr
  have hout := groupPresetC_out CM w σ power prodIn encIn first n fold b k y t1 t2 xs
  rw [← hσ1] at hlow htip hout
  have hmid : ∀ r < n, chainStride w.lx * r + walkSize w.lx 0 + 2 ≤ chainStride w.lx * n := fun r hr => by
    have : chainStride w.lx * r + chainStride w.lx ≤ chainStride w.lx * n := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hr
    unfold chainStride at this ⊢; omega
  have hcomp := cArm_comp (CM := CM) (C := C) (rd := rd) (σ := σ1) (b := bk) (xs := xs)
    (tips := tips) (power := power) (prodIn := prodIn) (encIn := encIn) (prodOut := groupProd w.lx fold n b)
    (encOut := groupEnc w.lx fold n b) (first := first) (n := n) (k := k) (fold := fold) (fresh := k == 0)
    (hw.mono (by omega)) ?_ ?_ ?_ (by rw [hk1.2.2.2, hmd]) (hc.congr hk1) ?_ ?_
  rotate_left
  · -- the tips' positions
    by_cases hk' : k = 0
    · subst hk'
      simp only [beq_self_eq_true, ↓reduceIte, TipsPos]
      refine ⟨trivial, fun r' _ _ => ?_⟩
      rw [hk0 rfl, htips_def, groupTips, groupStart_eq, Nat.sub_zero]
    · simp only [hk', beq_iff_eq, ↓reduceIte, TipsPos]
      intro r' _ hr'
      have := h0k (by omega)
      have := hmid r' (by omega)
      exact ⟨⟨_, by omega, rfl⟩, ⟨_, by omega, rfl⟩⟩
  · -- the outputs' positions
    by_cases hk' : k = 0
    · subst hk'
      simp only [beq_self_eq_true, ↓reduceIte]
      rw [hk0 rfl, armWalksEnd, cWalks_snd_fresh, ← groupStart_eq]
      exact ⟨rfl, rfl⟩
    · simp only [hk', beq_iff_eq, ↓reduceIte]
      have := h0k (by omega)
      exact ⟨⟨_, by omega, rfl⟩, ⟨_, by omega, rfl⟩⟩
  · exact ⟨hin.1.mono (by omega), hin.2.1.mono (by omega), (hin.2.2 _ (digitSum_lt_ten _ hn)).mono (by omega)⟩
  · intro r hr
    refine ⟨hx r hr, (ha r hr).congr hk1, ?_⟩
    rw [TipSetC, hk1.1, hk1.2.1, hk1.2.2.1]
    exact ⟨(htip hr).1, fun _ => (htip hr).2⟩
  · rw [ArmFold, groupProd, groupEnc, hout.1, hout.2, he1.below hin.1, he1.below hin.2.1, he1.below (hin.2.2 _ (digitSum_lt_ten _ hn))]
    exact ⟨rfl, rfl⟩
  obtain ⟨σ', he', hpost, hh⟩ := hcomp
  have heT : Ext b A.2 σ σ' := (he1.mono le_rfl (by omega)).comp (he'.mono (by omega) hkle)
  have hk2 := hw.keep heT
  have hb : ∀ j, b ≤ j → j < b + 5 → σ' (.n j) = σ1 (.n j) := fun j _ h2 => he'.apply (Or.inl (by omega))
  refine ⟨σ', heT, ⟨?_, fun r hr => ?_, ?_⟩, fun next kret hn => ?_⟩
  · rw [hb b le_rfl (by omega), hlow le_rfl (by omega)]; simp
  · rw [TipSetC, hk2.1, hk2.2.1, hk2.2.2.1, (hpost.1 r hr).1, (hpost.1 r hr).2]
    exact ⟨(htip hr).1, fun _ => (htip hr).2⟩
  · rw [ArmFold, hpost.2.1, hpost.2.2, groupProd, groupEnc, hout.1, hout.2, heT.below hin.1,
      heT.below hin.2.1, heT.below (hin.2.2 _ (digitSum_lt_ten _ hn))]
    exact ⟨rfl, rfl⟩
  · simp only [cGroup, hintW, rangeS, cst, List.cons_append, List.nil_append, holdsListB_cons_atom,
      Atom.HoldsB, true_and]
    rw [hb (b + 1) (by omega) (by omega), hb b le_rfl (by omega), hb (b + 2) (by omega) (by omega),
      hb (b + 3) (by omega) (by omega), hb (b + 4) (by omega) (by omega), hlow le_rfl (by omega),
      hlow (by omega) (by omega), hlow (by omega) (by omega), hlow (by omega) (by omega),
      hlow (by omega) (by omega)]
    simp only [show b + 1 ≠ b by omega, show b + 2 ≠ b by omega, show b + 2 ≠ b + 1 by omega,
      show b + 3 ≠ b by omega, show b + 3 ≠ b + 1 by omega, show b + 3 ≠ b + 2 by omega,
      show b + 4 ≠ b by omega, show b + 4 ≠ b + 1 by omega, show b + 4 ≠ b + 2 by omega,
      show b + 4 ≠ b + 3 by omega, ↓reduceIte]
    refine ⟨trivial, ⟨hl1, by rw [word_two_pow (by omega)]; exact hl2, hl3⟩,
      (holdsListB_match_singleS _ _ _ _ _).mpr ⟨k, by rw [cArms_length]; exact hk, ?_, ?_⟩⟩
    · rw [hb b le_rfl (by omega), hlow le_rfl (by omega)]; simp
    · rw [List.getElem?_eq_getElem (by rw [cArms_length]; exact hk), Option.some.injEq] at hgk
      rw [hgk]
      exact hh next kret hn


end
end LeanVM.Guest.B1.Sig
