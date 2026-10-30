/-
  LeanVM.Guest.B1.Sig.SphincsFk

  The forest keys of `verify_sig_lean_sphincs` (`sp_forest_top`, `sp_forest_key`,
  `lean_ethereum.py:3546-3587`) are sound: arm `t` of a sub-tree's dispatch writes the child leaf
  of the codeword `t`'s chains and the weight of `t`.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsKec
public import LeanVM.Guest.B1.Sig.SphincsScheme

/-!
# The forest keys, sound

* `holdsList_match`: a `match` whose arms are atoms holds when one arm `j` does at `x = g^j`;
* `TwsOK`: the prologue's forest address constants;
* `fkSteps_sound`, `fkChain_sound`, `fkChains_sound`: chain `i` of key `t` walks `fChain` its
  deficit `spCode t i` from its hinted value;
* `fkArm_sound`: the key's child leaf (`hcell` of `P`, the leaf address and the six chain ends) and
  its weight;
* `fkArmsRest_getElem`, `fkArms_getElem`, `fkArms_sound`: arm `t` of the 256 is `fkArm t`, from the
  base `fkAB`, writing into the dispatch's two cells.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat)

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-! ## A `match` of atoms -/

theorem holdsArms_some {x : V} : ∀ (arms : List (List Stmt)) (j0 : Nat) {N : Prop},
    Stmt.HoldsArms C rd σ x j0 arms N kret →
      ∃ (k : Nat) (hk : k < arms.length), σ x = ofK (gpow (j0 + k)) ∧
        Stmt.HoldsList C rd σ arms[k] N kret
  | [], _, _, h => h.elim
  | a :: as, j0, N, h => by
      rcases h with ⟨hx, ha⟩ | h
      · exact ⟨0, by simp, by simpa using hx, ha⟩
      · obtain ⟨k, hk, hx, ha⟩ := holdsArms_some as (j0 + 1) h
        exact ⟨k + 1, by simp; omega, by rw [hx]; congr 2; omega, ha⟩

/-- **A `match` of atoms**: arm `j` at `x = g^j` holds, then the rest. -/
theorem holdsList_match {x : V} {arms : List (List Stmt)} {rest : List Stmt} {next : Prop}
    (hA : ∀ a ∈ arms, atomsOnly a = true)
    (h : Stmt.HoldsList C rd σ (.match_ x arms :: rest) next kret) :
    ∃ (j : Nat) (hj : j < arms.length), σ x = ofK (gpow j) ∧ AtomsHold rd σ arms[j] ∧
      Stmt.HoldsList C rd σ rest next kret := by
  obtain ⟨j, hj, hx, ha⟩ := holdsArms_some arms 0 h
  have hat := hA _ (List.getElem_mem hj)
  have hs := holdsList_split_atoms (ys := []) hat (by simpa using ha)
  exact ⟨j, hj, by simpa using hx, atomsHold_of_holdsList hat hs.1, hs.2⟩

/-! ## The chains -/

/-- The prologue's forest address constants: `tws[4 i + s]` and `tws[24]`. -/
def TwsOK (σ : Val) : Prop :=
  (∀ i < 6, ∀ s < 4, σ (sTws (4 * i + s)) = word (tw 15 + i * 2 ^ 43 + s * stepMul) 0 0) ∧
    σ (sTws 24) = word (tw 16) 0 0

theorem spCode_lt (t i : Nat) : spCode t i < 5 := Nat.mod_lt _ (by norm_num)

/-- **A chain's steps**: step `j` of a walk of `d` steps from `v` writes `fChain` after `j + 1`. -/
theorem fkSteps_sound (hp : PadOK σ sPad) (htws : TwsOK σ) {i d : Nat} (hi : i < 6) (hd : d ≤ 4)
    {keyAt : V} {b : Nat}
    (h : AtomsHold rd σ ((List.range d).flatMap fun j =>
      addS (.n (b + 1 + 15 * j)) keyAt (sTws (4 * i + 4 - d + j)) ::
        k48 (.n (b + 1 + 15 * j)) (if j = 0 then .n b else .n (b + 1 + 15 * j - 13))
          (b + 1 + 15 * j + 1) (b + 1 + 15 * j + 2))) :
    ∀ j < d, σ (.n (b + 1 + 15 * j + 2)) =
      fChain (σ sPP) (σ keyAt) i (4 - d) (σ (.n b)) (j + 1) := by
  intro j hj
  induction j with
  | zero =>
      have hk := k48_sound hp (h.sub fun x hx => List.mem_flatMap.mpr
        ⟨0, List.mem_range.mpr hj, List.mem_cons_of_mem _ hx⟩)
      have ha : σ (.n (b + 1 + 15 * 0)) = σ keyAt + σ (sTws (4 * i + 4 - d + 0)) :=
        h.atom (a := .add (.n (b + 1 + 15 * 0)) keyAt (sTws (4 * i + 4 - d + 0)))
          (List.mem_flatMap.mpr ⟨0, List.mem_range.mpr hj, List.mem_cons_self⟩)
      rw [show sTws (4 * i + 4 - d + 0) = sTws (4 * i + (4 - d)) by congr 1; omega,
        htws.1 i hi (4 - d) (by omega), word_eq_eOfNat] at ha
      simp only [↓reduceIte] at hk
      have hk1 := congrArg Prod.fst hk
      simp only at hk1
      rw [fChain, fChain, hk1, ha]
      simp only [Nat.add_zero]
  | succ j ih =>
      have hk := k48_sound hp (h.sub fun x hx => List.mem_flatMap.mpr
        ⟨j + 1, List.mem_range.mpr hj, List.mem_cons_of_mem _ hx⟩)
      have ha : σ (.n (b + 1 + 15 * (j + 1))) = σ keyAt + σ (sTws (4 * i + 4 - d + (j + 1))) :=
        h.atom (a := .add (.n (b + 1 + 15 * (j + 1))) keyAt (sTws (4 * i + 4 - d + (j + 1))))
          (List.mem_flatMap.mpr ⟨j + 1, List.mem_range.mpr hj, List.mem_cons_self⟩)
      rw [show sTws (4 * i + 4 - d + (j + 1)) = sTws (4 * i + (4 - d + (j + 1))) by
        congr 1; omega, htws.1 i hi (4 - d + (j + 1)) (by omega), word_eq_eOfNat] at ha
      simp only [Nat.add_one_ne_zero, ↓reduceIte,
        show b + 1 + 15 * (j + 1) - 13 = b + 1 + 15 * j + 2 by omega] at hk
      rw [fChain, ← ih (by omega), ← ha, ← congrArg Prod.fst hk]

/-- **Chain `i` of key `t`**: its top is `fChain` of its hinted value, its deficit's steps from
position `4 - d`. -/
theorem fkChain_sound (hp : PadOK σ sPad) (htws : TwsOK σ) {t i : Nat} (hi : i < 6) {keyAt : V}
    {b : Nat} (h : AtomsHold rd σ (fkChain t i keyAt b).1) :
    σ (fkChain t i keyAt b).2.2 =
      fChain (σ sPP) (σ keyAt) i (4 - spCode t i) (σ (.n b)) (spCode t i) := by
  have hd5 := spCode_lt t i
  unfold fkChain at h ⊢
  simp only at h ⊢
  by_cases h0 : spCode t i = 0
  · simp only [h0, ↓reduceIte] at h ⊢
    rfl
  · simp only [h0, ↓reduceIte] at h ⊢
    have key := fun (hS : AtomsHold rd σ ((List.range (spCode t i)).flatMap fun j =>
        addS (.n (b + 1 + 15 * j)) keyAt (sTws (4 * i + 4 - spCode t i + j)) ::
          k48 (.n (b + 1 + 15 * j)) (if j = 0 then .n b else .n (b + 1 + 15 * j - 13))
            (b + 1 + 15 * j + 1) (b + 1 + 15 * j + 2))) =>
      fkSteps_sound hp htws hi (by omega) hS (spCode t i - 1) (by omega)
    have e : b + 1 + 15 * (spCode t i - 1) + 2 = b + 15 * spCode t i - 12 := by omega
    have e1 : spCode t i - 1 + 1 = spCode t i := by omega
    by_cases hi2 : i < 2
    · simp only [hi2, ↓reduceIte] at h ⊢
      rw [← e, key (h.sub fun x hx => List.mem_cons_of_mem _ hx), e1]
    · simp only [hi2, ↓reduceIte] at h ⊢
      have hc : σ (.n (b + 1 + 15 * spCode t i)) = σ (.n (b + 15 * spCode t i - 12)) :=
        h.atom (a := .copy (.n (b + 1 + 15 * spCode t i)) (.n (b + 15 * spCode t i - 12)))
          (by simp [copyS])
      rw [hc, ← e, key (h.sub fun x hx => List.mem_cons_of_mem _ (List.mem_append_left _ hx)), e1]

/-- The base of chain `i + k` of key `t`, after `k` chains from chain `i` at `b`. -/
def fkCB (t : Nat) (keyAt : V) (i b k : Nat) : Nat := (fkChains t keyAt k i b).2.1

/-- **Chains `i ..< i + m` of key `t`.** -/
theorem fkChains_sound (hp : PadOK σ sPad) (htws : TwsOK σ) {t : Nat} {keyAt : V} :
    ∀ (m i b : Nat), i + m ≤ 6 → AtomsHold rd σ (fkChains t keyAt m i b).1 → ∀ k < m,
      σ ((fkChains t keyAt m i b).2.2.getD k (.n 0)) =
        fChain (σ sPP) (σ keyAt) (i + k) (4 - spCode t (i + k)) (σ (.n (fkCB t keyAt i b k)))
          (spCode t (i + k))
  | 0, _, _, _, _, k, hk => absurd hk (by omega)
  | m + 1, i, b, hm, h, k, hk => by
      have h' : AtomsHold rd σ ((fkChain t i keyAt b).1 ++
          (fkChains t keyAt m (i + 1) (fkChain t i keyAt b).2.1).1) := h
      rcases k with _ | k
      · exact fkChain_sound hp htws (by omega) h'.left
      · have := fkChains_sound hp htws m (i + 1) (fkChain t i keyAt b).2.1 (by omega) h'.right k
          (by omega)
        rw [show i + 1 + k = i + (k + 1) by omega] at this
        exact this

/-- **Key `t`'s arm**: the child leaf, `hcell` of `P`, the leaf address `keyAt + tws[24]` and the
six chain ends, into its leaf cell; the weight of `t` at byte `w` into its weight cell. -/
theorem fkArm_sound (hp : PadOK σ sPad) (htws : TwsOK σ) {t w : Nat} {keyAt retN retW : V}
    {fresh : Bool} {b : Nat} (h : AtomsHold rd σ (fkArm t w keyAt retN retW fresh b).1) :
    σ (if fresh then .n ((fkChains t keyAt 6 0 b).2.1 + 15) else retN) =
        (hcell (σ sPP :: (σ keyAt + word (tw 16) 0 0) :: (List.range 6).map fun i =>
          fChain (σ sPP) (σ keyAt) i (4 - spCode t i) (σ (.n (fkCB t keyAt 0 b i)))
            (spCode t i))).1 ∧
      σ (if fresh then .n ((fkChains t keyAt 6 0 b).2.1 + 16) else retW) = fkWeight t w := by
  unfold fkArm at h
  simp only at h
  set ch := fkChains t keyAt 6 0 b with hch
  set B := ch.2.1 with hB
  have hc := fkChains_sound hp htws 6 0 b (le_refl _) h.left
  have ha : σ (.n B) = σ keyAt + σ (sTws 24) := h.right.atom (a := .add (.n B) keyAt (sTws 24))
    (by simp [addS])
  have h1 : σ (.n (B + 1)) = word (2 ^ 63 + 1) 0 0 :=
    h.right.atom (a := .const (.n (B + 1)) _) (by simp [cst])
  have hk := kec128_sound (o := B + 2) (m0 := sPP) (m1 := .n B) (m2 := ch.2.2.getD 0 (.n 0))
    (m3 := ch.2.2.getD 1 (.n 0)) (m4 := ch.2.2.getD 2 (.n 0)) (m5 := ch.2.2.getD 3 (.n 0))
    (m6 := ch.2.2.getD 4 (.n 0)) (m7 := ch.2.2.getD 5 (.n 0)) hp (h.right.sub fun x hx => by
    simp only [List.mem_singleton] at hx
    subst hx
    simp) h1
  have hcp : σ (if fresh then .n (B + 15) else retN) = σ (.n (B + 2)) :=
    h.right.atom (a := .copy (if fresh then .n (B + 15) else retN) (.n (B + 2))) (by simp [copyS])
  have hw : σ (if fresh then .n (B + 16) else retW) = fkWeight t w :=
    h.right.atom (a := .const (if fresh then .n (B + 16) else retW) (fkWeight t w)) (by simp)
  refine ⟨?_, hw⟩
  have hk1 := congrArg Prod.fst hk
  simp only at hk1
  rw [hcp, hk1, ha, htws.2]
  rw [hch]
  rw [hc 0 (by norm_num), hc 1 (by norm_num), hc 2 (by norm_num), hc 3 (by norm_num),
    hc 4 (by norm_num), hc 5 (by norm_num)]
  rfl

/-! ## The 256 arms -/

theorem fkArmsRest_length (w : Nat) (keyAt retN retW : V) :
    ∀ (m t b : Nat), (fkArmsRest w keyAt retN retW m t b).1.length = m
  | 0, _, _ => rfl
  | m + 1, t, b => by
      simp only [fkArmsRest, List.length_cons, fkArmsRest_length w keyAt retN retW m]

theorem fkArmsRest_getElem (w : Nat) (keyAt retN retW : V) :
    ∀ (m t b k : Nat) (hk : k < (fkArmsRest w keyAt retN retW m t b).1.length),
      (fkArmsRest w keyAt retN retW m t b).1[k] =
        (fkArm (t + k) w keyAt retN retW false (fkArmsRest w keyAt retN retW k t b).2).1
  | 0, _, _, k, hk => absurd hk (by simp [fkArmsRest])
  | m + 1, t, b, k, hk => by
      rcases k with _ | k
      · rfl
      · have := fkArmsRest_getElem w keyAt retN retW m (t + 1)
          (fkArm t w keyAt retN retW false b).2 k
          (by simp only [fkArmsRest, List.length_cons, fkArmsRest_length] at hk ⊢; omega)
        rw [show t + 1 + k = t + (k + 1) by omega] at this
        exact this

theorem fkArms_length (w : Nat) (keyAt : V) (b : Nat) : (fkArms w keyAt b).1.length = 256 := by
  simp only [fkArms, List.length_cons, fkArmsRest_length]

/-- The base of arm `t` of the 256. -/
def fkAB (w : Nat) (keyAt : V) (b t : Nat) : Nat :=
  if t = 0 then b else
    (fkArmsRest w keyAt (fkArms w keyAt b).2.2.1 (fkArms w keyAt b).2.2.2 (t - 1) 1
      (fkArm 0 w keyAt (.n 0) (.n 0) true b).2).2

theorem fkArm_atoms (t w : Nat) (keyAt retN retW : V) (fresh : Bool) (b : Nat) :
    atomsOnly (fkArm t w keyAt retN retW fresh b).1 = true := by
  have hch : ∀ m i b, atomsOnly (fkChains t keyAt m i b).1 = true := by
    intro m
    induction m with
    | zero => intro _ _; rfl
    | succ m ih =>
        intro i b
        simp only [fkChains, atomsOnly_append, ih, Bool.and_true]
        unfold fkChain
        simp only
        split
        · rfl
        · split
          · exact atomsOnly_flatMap _ (fun j => rfl) _
          · rw [List.cons_append]
            show atomsOnly (_ ++ _) = true
            rw [atomsOnly_append, atomsOnly_flatMap _ (fun j => rfl) _]
            rfl
  simp only [fkArm, atomsOnly_append, hch]
  rfl

theorem fkArms_atoms (w : Nat) (keyAt : V) (b : Nat) : ∀ a ∈ (fkArms w keyAt b).1, atomsOnly a = true := by
  have hr : ∀ m t b' (rN rW : V), ∀ a ∈ (fkArmsRest w keyAt rN rW m t b').1, atomsOnly a = true := by
    intro m
    induction m with
    | zero => intro _ _ _ _ a ha; simp [fkArmsRest] at ha
    | succ m ih =>
        intro t b' rN rW a ha
        simp only [fkArmsRest, List.mem_cons] at ha
        rcases ha with rfl | ha
        · exact fkArm_atoms _ _ _ _ _ _ _
        · exact ih _ _ _ _ a ha
  intro a ha
  simp only [fkArms, List.mem_cons] at ha
  rcases ha with rfl | ha
  · exact fkArm_atoms _ _ _ _ _ _ _
  · exact hr _ _ _ _ _ a ha

/-- **Arm `t` of the 256, sound**: the child leaf of key `t` into the dispatch's leaf cell, its
weight into the weight cell. -/
theorem fkArms_sound (hp : PadOK σ sPad) (htws : TwsOK σ) {w : Nat} {keyAt : V} {b t : Nat}
    (ht : t < (fkArms w keyAt b).1.length) (h : AtomsHold rd σ (fkArms w keyAt b).1[t]) :
    σ (fkArms w keyAt b).2.2.1 =
        (hcell (σ sPP :: (σ keyAt + word (tw 16) 0 0) :: (List.range 6).map fun i =>
          fChain (σ sPP) (σ keyAt) i (4 - spCode t i) (σ (.n (fkCB t keyAt 0 (fkAB w keyAt b t) i)))
            (spCode t i))).1 ∧
      σ (fkArms w keyAt b).2.2.2 = fkWeight t w := by
  rcases t with _ | t
  · have e : (fkArms w keyAt b).1[0] = (fkArm 0 w keyAt (.n 0) (.n 0) true b).1 := rfl
    rw [e] at h
    have := fkArm_sound hp htws h
    simp only [↓reduceIte] at this
    have e1 : (fkArms w keyAt b).2.2.1 = .n ((fkChains 0 keyAt 6 0 b).2.1 + 15) := by
      simp only [fkArms, fkArm, ↓reduceIte]
      congr 1
    have e2 : (fkArms w keyAt b).2.2.2 = .n ((fkChains 0 keyAt 6 0 b).2.1 + 16) := by
      simp only [fkArms, fkArm, ↓reduceIte]
      congr 1
    rw [e1, e2]
    exact this
  · have e : (fkArms w keyAt b).1[t + 1] =
        (fkArm (t + 1) w keyAt (fkArms w keyAt b).2.2.1 (fkArms w keyAt b).2.2.2 false
          (fkAB w keyAt b (t + 1))).1 := by
      have := fkArmsRest_getElem w keyAt (fkArms w keyAt b).2.2.1 (fkArms w keyAt b).2.2.2 255 1
        (fkArm 0 w keyAt (.n 0) (.n 0) true b).2 t
        (by rw [fkArmsRest_length]; rw [fkArms_length] at ht; omega)
      rw [show 1 + t = t + 1 by omega] at this
      exact this
    rw [e] at h
    exact fkArm_sound hp htws h

end
end LeanVM.Guest.B1.Sig
