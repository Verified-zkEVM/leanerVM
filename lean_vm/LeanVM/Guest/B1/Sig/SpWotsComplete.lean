/-
  LeanVM.Guest.B1.Sig.SpWotsComplete

  `sp_wots` is complete (`sp_wots_complete`): for a digest of digit sum `128` and any chain values,
  its body holds of a valuation whose arguments are the parameter's cell, the key's address cell
  and the digest's cell, returning the cell of the leaf the values recover.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsGroupComplete
public import LeanVM.Guest.B1.Sig.SpWotsPostCheck
public import LeanVM.Guest.B1.Sig.SpWotsLeafCheck
public import LeanVM.Guest.B1.Sig.SpWotsSound
public import LeanVM.Guest.B1.Sig.SpWotsData

/-!
# `sp_wots`, complete

The valuation: the arguments; the powers; each digit group with the digest's digits (`spK`) and
the chain values' cells loaded at its arm's starts (`spGroupsC`); the checks, which hold since the
digits are the digest's (`spCheck_complete`); the leaf's message, evaluated with its padding run at
the last group's digit cells and moved (`spLeaf_complete`); the copy. The returned leaf is then read
off by soundness (`sp_wots_sound`): its chain values are the loaded ones (`spValues_eq`).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (gen)
open HashSig

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-! ## The digits and the values -/

/-- Group `p`'s digit word for the digest: its `spN p` base-4 digits from digit `3p`. -/
def spK (digest : Digest) (p : Nat) : Nat := digest.toNat / 4 ^ (3 * p) % 4 ^ spN p

/-- Chain `i`'s value as a cell. -/
def spCv (values : Sphincs.ChainIndex → Digest) (i : Nat) : E :=
  if h : i < 64 then cellOf128 (values ⟨i, h⟩) else 0

theorem spCv_canon (values : Sphincs.ChainIndex → Digest) (i : Nat) : IsCanonical128 (spCv values i) := by
  unfold spCv; split
  · exact isCanonical128_cellOf128 _
  · exact canon_zero

theorem spK_lt (digest : Digest) (p : Nat) : spK digest p < 4 ^ spN p := Nat.mod_lt _ (by positivity)

theorem spK_digit (digest : Digest) {p t : Nat} (ht : t < spN p) :
    spK digest p / 4 ^ t % 4 = digest.toNat / 4 ^ (3 * p + t) % 4 := by
  unfold spK
  obtain ⟨m, hm⟩ : ∃ m, spN p = t + (m + 1) := ⟨spN p - t - 1, by omega⟩
  rw [hm, pow_add, Nat.mod_mul_right_div_self, Nat.div_div_eq_div_mul, ← pow_add, pow_succ,
    Nat.mod_mul_left_mod]

theorem sum_base4 (x : Nat) : ∀ m, ∑ i ∈ Finset.range m, x / 4 ^ i % 4 * 4 ^ i = x % 4 ^ m
  | 0 => by simp [Nat.mod_one]
  | m + 1 => by
      rw [Finset.sum_range_succ, sum_base4 x m, Nat.mod_pow_succ]
      ring

theorem digestDigits_val (digest : Digest) (i : Sphincs.ChainIndex) :
    (digestDigits digest i).val = digest.toNat / 4 ^ i.val % 4 := by
  show (BitVec.extractLsb' (2 * i.val) 2 digest).toNat = _
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, pow_mul]
  norm_num

theorem lit_bv (v : BitVec 128) : lit v.toNat = cellOf128 v := by
  rw [lit_eq _ v.isLt, ← cellOf128_eq_eOfNat192 v.isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem cellVal_cellOf128_digest (digest : Digest) : cellVal (cellOf128 digest) = digest :=
  cellVal_cellOf128 digest

theorem lit_digest (digest : Digest) : lit digest.toNat = cellOf128 digest := lit_bv digest

/-! ## A group's post, kept -/

/-- The end of group `p`. -/
def spEnd (p : Nat) : Nat :=
  (spGroupT (3 * p) (spN p) (p == 0) (spState p).1 (spState p).2.1 (spState p).2.2).2

theorem spEnd_eq (p : Nat) :
    spEnd p = spArmB (3 * p) (spN p) (p == 0) (spState p).2.2 (spState p).1 (spState p).2.1 (4 ^ spN p) :=
  spGroupT_end ..

theorem spState_succ_end {p : Nat} (hp : p < 21) : (spState (p + 1)).2.2 = spEnd p := by
  rw [spState_succ, spEnd, spN_of_lt hp]

theorem spState_le_end (p : Nat) : (spState p).2.2 + 5 ≤ spEnd p := by
  rw [spEnd_eq]; exact spArmB_ge ..

theorem spState_mono : ∀ {p q : Nat}, p ≤ q → q ≤ 21 → (spState p).2.2 ≤ (spState q).2.2
  | p, q, h, hq => by
      induction q with
      | zero => have : p = 0 := by omega
                subst this; exact le_rfl
      | succ q ih =>
          rcases Nat.lt_or_ge p (q + 1) with h' | h'
          · have := ih (by omega) (by omega)
            rw [spState_succ_end (by omega)]
            have := spState_le_end q
            omega
          · have : p = q + 1 := by omega
            subst this; exact le_rfl

/-- What group `q` establishes: its digit word, its arm's tips canonical and starts loaded. -/
def SpGP (digest : Digest) (values : Sphincs.ChainIndex → Digest) (q : Nat) (σ : Val) : Prop :=
  σ (.n (spState q).2.2) = ofK (addressOfIndex (spK digest q)) ∧
    SpArmPost (3 * q) (spN q) (q == 0) (spState q).2.2 (spState q).1 (spState q).2.1 (spK digest q)
      (fun t => spCv values (3 * q + t)) σ

theorem SpGP.keep {digest : Digest} {values : Sphincs.ChainIndex → Digest} {q : Nat} (hq : q < 22)
    {σ σ' : Val} (h : SpGP digest values q σ) {lo hi : Nat} (he : Ext lo hi σ σ') (hlo : spEnd q ≤ lo) :
    SpGP digest values q σ' := by
  obtain ⟨hs, hst⟩ := spPost_all hq
  have hB := spState_le_end q
  rw [spEnd_eq] at hlo hB
  refine ⟨by rw [he.apply (Or.inl (by omega))]; exact h.1, fun t ht => ?_, fun t ht => ?_⟩
  · rw [he.apply (Or.inl (by have := (hs t ht).2; omega))]; exact h.2.1 t ht
  · obtain ⟨j, e, -, hj⟩ := hst _ (spK_lt digest q) t ht
    rw [e, he.apply (Or.inl (by omega)), ← e]
    exact h.2.2 t ht

/-! ## The groups -/

/-- Groups `p ..< p + m`. -/
def spGL : Nat → Nat → List Stmt
  | _, 0 => []
  | p, m + 1 => (spGroupT (3 * p) (spN p) (p == 0) (spState p).1 (spState p).2.1 (spState p).2.2).1 ++
      spGL (p + 1) m

theorem spGL_eq : ∀ m p, p + m ≤ 21 →
    (spGroupsT m p (spState p).1 (spState p).2.1 (spState p).2.2).1 = spGL p m
  | 0, _, _ => by simp [spGroupsT, spGL]
  | m + 1, p, h => by
      rw [spGroupsT_fst, spGL, spN_of_lt (by omega), spGL_eq m (p + 1) (by omega)]

theorem spGL_snoc : ∀ m p, spGL p (m + 1) = spGL p m ++
    (spGroupT (3 * (p + m)) (spN (p + m)) (p + m == 0) (spState (p + m)).1 (spState (p + m)).2.1
      (spState (p + m)).2.2).1
  | 0, p => by simp [spGL]
  | m + 1, p => by
      rw [spGL, spGL_snoc m (p + 1), spGL, List.append_assoc, show p + 1 + m = p + (m + 1) by omega]

/-- The end of groups `p ..< p + m`. -/
def spGLEnd (p m : Nat) : Nat := if m = 0 then (spState p).2.2 else spEnd (p + m - 1)

/-- **Groups `p ..< p + m` complete**, each with the digest's digits and the values loaded. -/
theorem spGroupsC (digest : Digest) (values : Sphincs.ChainIndex → Digest) (hm : MemOK rd 64) :
    ∀ m p, p + m ≤ 22 → ∀ σ, IsCanonical128 (σ (.n 0)) → IsCanonical128 (σ (.n 1)) →
      Completes C rd (spState p).2.2 (spGLEnd p m) (spGL p m) σ
        (fun σ' => ∀ q, p ≤ q → q < p + m → SpGP digest values q σ') ∧
      NumBelow (spGLEnd p m) (Stmt.valsList (spGL p m))
  | 0, p, _, σ, _, _ => ⟨⟨σ, Ext.refl _ _ _, fun q h1 h2 => by omega, fun _ _ hn => hn⟩,
      NumBelow.nil _⟩
  | m + 1, p, hpm, σ, h0, h1 => by
      have hp : p < 22 := by omega
      have hg := spGroupP_complete (C := C) hp (spK_lt digest p) hm σ h0 h1
        (fun t => spCv values (3 * p + t)) (fun t _ => spCv_canon _ _)
      have hnb := spGroupP_nb hp
      have hB := spState_le_end p
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · simp only [spGL, List.append_nil]
        have e : spGLEnd p 1 = spEnd p := by simp [spGLEnd]
        rw [e]
        exact ⟨hg.mono le_rfl le_rfl (fun σ' hσ' q h1 h2 => by
          have : q = p := by omega
          subst this; exact hσ'), hnb⟩
      · have hp21 : p < 21 := by omega
        have hst := spState_succ_end hp21
        have e : spGLEnd (p + 1) m = spGLEnd p (m + 1) := by
          unfold spGLEnd; simp only [show m ≠ 0 by omega, ↓reduceIte, Nat.add_eq_zero_iff]
          congr 1; omega
        have hle : spEnd p ≤ spGLEnd (p + 1) m := by
          unfold spGLEnd; simp only [show m ≠ 0 by omega, ↓reduceIte]
          have := spState_le_end (p + 1 + m - 1)
          have := spState_mono (p := p + 1) (q := p + 1 + m - 1) (by omega) (by omega)
          omega
        obtain ⟨-, hnbR⟩ := spGroupsC digest values hm m (p + 1) (by omega) σ h0 h1
        refine ⟨?_, ?_⟩
        · simp only [spGL]
          refine Completes.append (m := spEnd p) (by omega) (by rw [← e]; exact hle) hnb hg
            (fun σ1 he1 hp1 => ?_)
          have hag : AgreeBelow (spState p).2.2 σ σ1 := he1.agree
          have hB13 : 13 ≤ (spState p).2.2 := by
            have := spGroupPad_all hp
            simp only [spGroupPadOK, Bool.and_eq_true, decide_eq_true_eq] at this
            exact this.1.2
          obtain ⟨ih, -⟩ := spGroupsC digest values hm m (p + 1) (by omega) σ1
            (by rw [← hag 0 (by omega)]; exact h0) (by rw [← hag 1 (by omega)]; exact h1)
          rw [hst, e] at ih
          refine (ih.keep (Q := SpGP digest values p) (Q' := SpGP digest values p) hp1
            (fun σ' he' hq => hq.keep hp he' le_rfl)).mono le_rfl le_rfl
            (fun σ' ⟨hr, hq⟩ q h1 h2 => ?_)
          rcases Nat.lt_or_ge q (p + 1) with h | h
          · have : q = p := by omega
            subst this; exact hq
          · exact hr q h (by omega)
        · simp only [spGL, valsList_append]
          rw [← e]
          exact (hnb.mono hle).append hnbR

theorem spGL_full : spGL 0 22 = spGs.1 ++ spLast.1 := by
  rw [spGL_snoc 21 0, ← spGL_eq 21 0 (by norm_num), ← spGs_fst, spLast_eq]
  rfl

theorem spGLEnd_full : spGLEnd 0 22 = spC := by
  unfold spGLEnd
  simp only [show (22 : Nat) ≠ 0 by norm_num, ↓reduceIte]
  rw [spC, spLast_eq]
  rfl

theorem spC_ge : 13 ≤ spC := by
  rw [← spGLEnd_full]
  unfold spGLEnd
  simp only [show (22 : Nat) ≠ 0 by norm_num, ↓reduceIte, show 0 + 22 - 1 = 21 by norm_num]
  have := spState_le_end 21
  have := spState_mono (p := 0) (q := 21) (by norm_num) le_rfl
  rw [spState_zero] at this
  simp only at this
  omega

/-- **The powers and the groups complete**, the digits the digest's and the values loaded. -/
theorem spCode_complete (digest : Digest) (values : Sphincs.ChainIndex → Digest) (hm : MemOK rd 64)
    (σ : Val) (h0 : IsCanonical128 (σ (.n 0))) (h1 : IsCanonical128 (σ (.n 1))) :
    Completes C rd 3 spC (spPowers ++ (spGs.1 ++ spLast.1)) σ
      (fun σ' => (∀ s < 10, σ' (.n (3 + s)) = gen ^ s) ∧ ∀ q < 22, SpGP digest values q σ') ∧
    NumBelow spC (Stmt.valsList (spPowers ++ (spGs.1 ++ spLast.1))) := by
  have hseq : SeqOK 3 spPowers 13 := seqB_ok (by decide +kernel)
  rw [← spGL_full, ← spGLEnd_full]
  have hst0 : (spState 0).2.2 = 13 := by rw [spState_zero]
  have hC := spC_ge
  rw [← spGLEnd_full] at hC
  refine ⟨Completes.append (m := 13) (by norm_num) hC hseq.numBelow (seq_completes hseq σ)
    (fun σ1 he1 hp1 => ?_), ?_⟩
  · have hpow : ∀ s < 10, σ1 (.n (3 + s)) = gen ^ s := by
      intro s hs
      have e : σ1 (.n (3 + s)) = word (2 ^ s) 0 0 := hp1.atom (a := .const (.n (3 + s)) _) (by
        simp only [spPowers, cst, List.mem_map, List.mem_range]
        exact ⟨s, hs, rfl⟩)
      rw [e, word_eq_eOfNat, Value.gen_pow_eq_eOfNat (by omega)]
    have hag : AgreeBelow 3 σ σ1 := he1.agree
    obtain ⟨hg, -⟩ := spGroupsC (C := C) digest values hm 22 0 (by norm_num) σ1
      (by rw [← hag 0 (by norm_num)]; exact h0) (by rw [← hag 1 (by norm_num)]; exact h1)
    rw [hst0] at hg
    refine (hg.keep (Q := fun σ => ∀ s < 10, σ (.n (3 + s)) = gen ^ s)
      (Q' := fun σ => ∀ s < 10, σ (.n (3 + s)) = gen ^ s) hpow
      (fun σ' he' hq s hs => by rw [he'.apply (Or.inl (by omega))]; exact hq s hs)).mono le_rfl le_rfl
      (fun σ' ⟨hr, hq⟩ => ⟨hq, fun q hq' => hr q (Nat.zero_le _) (by omega)⟩)
  · rw [valsList_append]
    obtain ⟨-, hnb⟩ := spGroupsC (C := C) digest values hm 22 0 (by norm_num) σ h0 h1
    exact (hseq.numBelow.mono hC).append hnb

theorem spN_mod (i : Nat) (hi : i < 64) : i % 3 < spN (i / 3) := by
  unfold spN; split <;> omega

/-- **The codeword's product and encoding**, the groups' digits the digest's. -/
theorem spVals {digest : Digest} {values : Sphincs.ChainIndex → Digest} {σ : Val} {rest : List Stmt}
    {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (spGs.1 ++ (spLast.1 ++ rest)) next kret)
    (hpow : ∀ s < 10, σ (.n (3 + s)) = gen ^ s) (hgp : ∀ q < 22, SpGP digest values q σ)
    (hT : Sphincs.TargetSum.Valid (digestDigits digest)) :
    σ (.n (spEnc false 1 (spState 21).2.2)) = cellOf128 digest ∧
      σ (.n (spProd false 1 (spState 21).2.2)) = spTarget := by
  rw [spGs_fst] at h
  obtain ⟨s2, hg⟩ := spGroupsT_sound (C := C) (rd := rd) (σ := σ) 21 0 (by norm_num) h
  rw [spLast_eq] at s2
  obtain ⟨-, kL, hkL, hxL, haL⟩ := spGroupT_sound s2
  have hgrp : ∀ p < 22, SpGroupOK rd σ p := by
    intro p hp
    by_cases hp21 : p < 21
    · simpa using hg p hp21
    · have : p = 21 := by omega
      subst this
      exact ⟨kL, by simpa [spN] using hkL, hxL, by simpa [spN] using haL⟩
  obtain ⟨-, hprod, henc⟩ := spCodeword_sound hpow hgrp
  have hdig : ∀ i < 64, spDigit σ i = digest.toNat / 4 ^ i % 4 := by
    intro i hi
    unfold spDigit
    rw [spDigitWord_eq (spK_lt digest (i / 3)) (hgp (i / 3) (by omega)).1,
      spK_digit digest (spN_mod i hi), show 3 * (i / 3) + i % 3 = i by omega]
  have hsum : ∑ i ∈ Finset.range 64, spDigit σ i = 128 := by
    rw [Finset.sum_congr rfl fun i hi => hdig i (Finset.mem_range.mp hi)]
    have := hT
    unfold Sphincs.TargetSum.Valid Sphincs.TargetSum.sum at this
    simp only [digestDigits_val] at this
    rw [Fin.sum_univ_eq_sum_range (fun i => digest.toNat / 4 ^ i % 4)] at this
    exact this
  have hlt : digest.toNat < 4 ^ 64 :=
    lt_of_lt_of_le (show (digest : BitVec 128).toNat < 2 ^ 128 from BitVec.isLt _) (by norm_num)
  have henc' : ∑ i ∈ Finset.range 64, spDigit σ i * 4 ^ i = digest.toNat := by
    rw [Finset.sum_congr rfl fun i hi => by rw [hdig i (Finset.mem_range.mp hi)], sum_base4,
      Nat.mod_eq_of_lt hlt]
  refine ⟨by rw [henc, henc', lit_digest], by rw [hprod, hsum, spTarget_eq]⟩

/-! ## The checks and the leaf -/

theorem upds3 (σ : Val) (e0 e1 e2 : E) (k : Nat) :
    upds σ [(k, e0), (k + 1, e1), (k + 2, e2)] (.n k) = e0 ∧
      upds σ [(k, e0), (k + 1, e1), (k + 2, e2)] (.n (k + 1)) = e1 ∧
      upds σ [(k, e0), (k + 1, e1), (k + 2, e2)] (.n (k + 2)) = e2 := by
  refine ⟨upds_cons_self _ _ _ _, ?_, ?_⟩
  · rw [upds_cons_ne _ _ _ (by omega), upds_cons_self]
  · rw [upds_cons_ne _ _ _ (by omega), upds_cons_ne _ _ _ (by omega), upds_cons_self]

/-- **The checks complete**, the encoding the argument's and the product the target. -/
theorem spCheck_complete (σ : Val)
    (henc : σ (.n (spEnc false 1 (spState 21).2.2)) = σ (.n 2))
    (hprod : σ (.n (spProd false 1 (spState 21).2.2)) = spTarget) :
    Completes C rd spC (spC + 3) spChecks σ
      (fun σ' => σ' (.n (spC + 2)) = σ (.n 1) + word (tw 2) 0 0) := by
  obtain ⟨-, -, -, -, -, -, -, hE, hP⟩ := spLeaf_check
  rw [spLeafB] at hE hP
  have hC := spC_ge
  obtain ⟨e0, e1, e2⟩ := upds3 σ spTarget (word (tw 2) 0 0) (σ (.n 1) + word (tw 2) 0 0) spC
  have hext : Ext spC (spC + 3) σ
      (upds σ [(spC, spTarget), (spC + 1, word (tw 2) 0 0), (spC + 2, σ (.n 1) + word (tw 2) 0 0)]) :=
    upds_ext σ _ (by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> simp)
  set σ3 := upds σ [(spC, spTarget), (spC + 1, word (tw 2) 0 0), (spC + 2, σ (.n 1) + word (tw 2) 0 0)]
    with hσ3
  have below : ∀ j < spC, σ3 (.n j) = σ (.n j) := fun j hj => hext.apply (Or.inl hj)
  refine completes_atoms rfl hext (by rw [e2]) (fun a ha => ?_)
  simp only [spChecks, cst, addS, List.mem_cons, Stmt.atom.injEq, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · show σ3 _ + σ3 _ = 0
    rw [below _ hE, below 2 (by omega), henc, e_add_self]
  · exact e0
  · show σ3 _ + σ3 _ = 0
    rw [below _ hP, e0, hprod, e_add_self]
  · exact e1
  · show σ3 _ = σ3 _ + σ3 _
    rw [e2, below 1 (by omega), e1]

theorem spChecks_nb : NumBelow (spC + 3) (Stmt.valsList spChecks) := by
  obtain ⟨-, -, -, -, -, -, -, hE, hP⟩ := spLeaf_check
  rw [spLeafB] at hE hP
  have hC := spC_ge
  intro v hv
  simp only [spChecks, cst, addS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with (rfl | rfl) | rfl | (rfl | rfl) | rfl | (rfl | rfl | rfl)
  all_goals exact ⟨_, by omega, rfl⟩

theorem padPull_lt (σ : Val) {B P j : Nat} (hj : j < B ∨ B + 5 ≤ j) (hP : j < P) :
    padPull σ B P (.n j) = σ (.n j) := by
  have e : ¬ (B ≤ j ∧ j < B + 5) := by omega
  simp only [padPull, V.n, true_and, e, ↓reduceIte, padRen_n, show ¬ P ≤ j by omega]

theorem padPull_canon (σ : Val) {B P : Nat} {j : Nat} (hP : j < P) (h : IsCanonical128 (σ (.n j))) :
    IsCanonical128 (padPull σ B P (.n j)) := by
  by_cases hj : B ≤ j ∧ j < B + 5
  · have e : padPull σ B P (.n j) = padC (j - B) := by
      simp only [padPull, hj, and_self, ↓reduceIte]
    rw [e]; exact canon_word _ _
  · rw [padPull_lt σ (by omega) hP]; exact h

theorem spEnd_le_C {q : Nat} (hq : q < 22) : spEnd q ≤ spC := by
  rw [← spGLEnd_full]
  unfold spGLEnd
  simp only [show (22 : Nat) ≠ 0 by norm_num, ↓reduceIte, show 0 + 22 - 1 = 21 by norm_num]
  rcases Nat.lt_or_ge q 21 with h | h
  · rw [← spState_succ_end h]
    have := spState_mono (p := q + 1) (q := 21) (by omega) le_rfl
    have := spState_le_end 21
    omega
  · have : q = 21 := by omega
    subst this; exact le_rfl

theorem spLeafCells_lt : ∀ v ∈ spLeafCells, ∃ j, v = .n j ∧ j < spC + 3 := by
  intro v hv
  rw [spLeafCells_eq] at hv
  simp only [List.mem_cons, List.mem_map, List.mem_range] at hv
  rcases hv with rfl | rfl | ⟨i, hi, rfl⟩
  · exact ⟨0, rfl, by omega⟩
  · exact ⟨_, rfl, by omega⟩
  · have hp : i / 3 < 22 := by omega
    have h := ((spPost_all hp).1 (i % 3) (spN_mod i hi)).2
    rw [← spEnd_eq] at h
    have := spEnd_le_C hp
    exact ⟨_, rfl, by omega⟩

/-- **The leaf's message completes** on canonical cells, its padding run moved. -/
theorem spLeaf_complete (σ : Val) (hc : ∀ v ∈ spLeafCells, IsCanonical128 (σ v)) :
    Completes C rd (spC + 3) spLeafK.2.1 spLeafK.1 σ (fun _ => True) ∧
      NumBelow spLeafK.2.1 (Stmt.valsList spLeafK.1) := by
  obtain ⟨hpar, hE, -, hB5, hP3, hPE, -, -, -⟩ := spLeaf_check
  obtain ⟨hsome, hcells, -, -⟩ := spLeafPad
  obtain ⟨i, hf⟩ := Option.isSome_iff_exists.mp hsome
  have hP : firstDef (spLeafM.1.getD i default) = spLeafP := by rw [spLeafP, padBase_eq hf]
  have hK : spLeafK.1 = (Stmt.renameList (padRen spLeafB spLeafP) spLeafMb.1).take i ++ padRun spLeafP ++
      (Stmt.renameList (padRen spLeafB spLeafP) spLeafMb.1).drop i := by
    show (withPad spVPad isKeccak spLeafM.1).1 = _
    rw [withPad_some hf, hP, hpar]
  have hK2 : spLeafK.2.1 = spLeafM.2.1 + 5 := by
    show spLeafM.2.1 + (withPad spVPad isKeccak spLeafM.1).2 = _
    rw [withPad_some hf]
  set σ0 := padPull σ spLeafB spLeafP with hσ0
  obtain ⟨hcomp, hnb, -⟩ := kMsg_complete (C := C) (rd := rd) (pad := spLeafB)
    (cells := spLeafCells.map KC.cell) (len := 1056) (tailRun := false) (b := spC + 3) σ0
    (padOK_padPull σ _ _) hB5 (fun c hcm => by
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hcm
      obtain ⟨e, hlt⟩ := hcells v hv
      obtain ⟨j, ej, hj⟩ := spLeafCells_lt v hv
      refine ⟨⟨j, hj, ej⟩, ?_⟩
      show IsCanonical128 (σ0 v)
      rw [e]
      exact padPull_canon σ hlt (by rw [← e]; exact hc v hv)) (fun h => by simp at h)
  change Completes C rd (spC + 3) spLeafMb.2.1 spLeafMb.1 σ0 _ at hcomp
  change NumBelow spLeafMb.2.1 (Stmt.valsList spLeafMb.1) at hnb
  rw [hE] at hcomp hnb
  obtain ⟨σ1, he1, -, hh1⟩ := hcomp
  have hat : atomsOnly spLeafMb.1 = true := kMsg_atoms ..
  have hA : AtomsHold rd σ1 spLeafMb.1 := atomsHold_of_holdsList (C := C) (kret := fun _ => True) hat
    (hh1 True (fun _ => True) trivial)
  have hv : ∀ v ∈ Stmt.valsList spLeafMb.1, ∃ j, v = .n j ∧ j < spLeafM.2.1 := fun v hv =>
    let ⟨j, hj, e⟩ := hnb v hv; ⟨j, e, hj⟩
  have hpadv : ∀ j < 5, σ1 (.n (spLeafB + j)) = padC j := fun j hj => by
    rw [he1.apply (Or.inl (by omega)), hσ0, padPull_run σ hj]
  have hag : ∀ j < spC + 3, (j < spLeafB ∨ spLeafB + 5 ≤ j) → σ1 (.n j) = σ (.n j) := fun j hj h => by
    rw [he1.apply (Or.inl hj), hσ0, padPull_lt σ h (by omega)]
  rw [hK, hK2]
  exact ⟨(padMove_completes (C := C) (rd := rd) hat hP3 hPE le_rfl hv hpadv hag hA i).mono le_rfl le_rfl
    (fun _ _ => trivial), padMove_numBelow hat hPE hv i⟩

/-! ## `sp_wots`, complete -/

/-- **The chain values read off the frame are the loaded ones.** -/
theorem spValues_eq {digest : Digest} {values : Sphincs.ChainIndex → Digest} {σ : Val}
    (hgp : ∀ q < 22, SpGP digest values q σ) : spValues σ = values := by
  funext i
  have hi := i.isLt
  have hp : i.val / 3 < 22 := by simp only [Sphincs.chainCount] at hi; omega
  have hs : spStart σ i.val = spStartAt (spK digest) i.val := by
    unfold spStart spStartAt
    dsimp only
    rw [spDigitWord_eq (spK_lt digest (i.val / 3)) (hgp (i.val / 3) hp).1]
  have h := (hgp (i.val / 3) hp).2.2 (i.val % 3) (spN_mod i.val (by simpa [Sphincs.chainCount] using hi))
  unfold spValues
  rw [hs]
  change σ (spStartAt (spK digest) i.val) = spCv values (3 * (i.val / 3) + i.val % 3) at h
  have hi64 : i.val < 64 := by simpa [Sphincs.chainCount] using hi
  rw [h, show 3 * (i.val / 3) + i.val % 3 = i.val by omega, spCv]
  simp only [hi64, ↓reduceDIte]
  exact cellVal_cellOf128 _

/-- **`sp_wots` is complete.** -/
theorem sp_wots_complete : sp_wots_complete_Spec := by
  intro C rd parameter layer tree leaf digest values hm hT
  set σI : Val := Function.update (Function.update (Function.update (fun _ => 0) (.n 0)
    (cellOf128 parameter)) (.n 1) (keyAddressCell layer tree leaf)) (.n 2) (cellOf128 digest) with hσI
  have i0 : σI (.n 0) = cellOf128 parameter := by simp [hσI]
  have i1 : σI (.n 1) = keyAddressCell layer tree leaf := by simp [hσI]
  have i2 : σI (.n 2) = cellOf128 digest := by simp [hσI]
  have hC := spC_ge
  have c0 : IsCanonical128 (σI (.n 0)) := by rw [i0]; exact isCanonical128_cellOf128 _
  have c1 : IsCanonical128 (σI (.n 1)) := by rw [i1]; exact isCanonical128_cellOf128 _
  obtain ⟨hA, hnbA⟩ := spCode_complete (C := C) (rd := rd) digest values hm σI c0 c1
  -- the checks
  have hB : Completes C rd 3 (spC + 3) ((spPowers ++ (spGs.1 ++ spLast.1)) ++ spChecks) σI
      (fun σ' => (∀ q < 22, SpGP digest values q σ') ∧
        σ' (.n (spC + 2)) = σI (.n 1) + word (tw 2) 0 0) := by
    refine Completes.append (m := spC) (by omega) (by omega) hnbA hA.withHolds
      (fun σ2 he2 ⟨⟨hpow, hgp⟩, hh2⟩ => ?_)
    have hag2 : AgreeBelow 3 σI σ2 := he2.agree
    have h22 : σ2 (.n 2) = cellOf128 digest := by rw [← hag2 2 (by norm_num)]; exact i2
    have h21 : σ2 (.n 1) = σI (.n 1) := (hag2 1 (by norm_num)).symm
    have hs := (holdsList_split_atoms (xs := spPowers) rfl hh2).2
    rw [show spGs.1 ++ spLast.1 = spGs.1 ++ (spLast.1 ++ []) by simp] at hs
    obtain ⟨henc, hprod⟩ := spVals hs hpow hgp hT
    refine ((spCheck_complete (C := C) (rd := rd) σ2 (by rw [henc, h22]) hprod).keep
      (Q := fun σ => ∀ q < 22, SpGP digest values q σ) (Q' := fun σ => ∀ q < 22, SpGP digest values q σ) hgp
      (fun σ' he' hq q hq' => (hq q hq').keep hq' he' (spEnd_le_C hq'))).mono le_rfl le_rfl
      (fun σ' ⟨h1, h2⟩ => ⟨h2, by rw [h1, h21]⟩)
  -- the leaf
  have hLe : spC + 3 ≤ spLeafK.2.1 := by
    obtain ⟨-, -, -, -, hP3, hPE, -, -, -⟩ := spLeaf_check
    show spC + 3 ≤ spLeafM.2.1 + (withPad spVPad isKeccak spLeafM.1).2
    omega
  have hnbB : NumBelow (spC + 3) (Stmt.valsList ((spPowers ++ (spGs.1 ++ spLast.1)) ++ spChecks)) := by
    rw [valsList_append]; exact (hnbA.mono (by omega)).append spChecks_nb
  have hL : Completes C rd 3 spLeafK.2.1 (((spPowers ++ (spGs.1 ++ spLast.1)) ++ spChecks) ++ spLeafK.1) σI
      (fun σ' => ∀ q < 22, SpGP digest values q σ') := by
    refine Completes.append (m := spC + 3) (by omega) hLe hnbB hB (fun σ3 he3 ⟨hgp3, h32⟩ => ?_)
    have hag3 : AgreeBelow 3 σI σ3 := he3.agree
    have hcells : ∀ v ∈ spLeafCells, IsCanonical128 (σ3 v) := by
      intro v hv
      rw [spLeafCells_eq] at hv
      simp only [List.mem_cons, List.mem_map, List.mem_range] at hv
      rcases hv with rfl | rfl | ⟨i, hi, rfl⟩
      · rw [← hag3 0 (by norm_num)]; exact c0
      · rw [h32]; exact canon_add c1 (canon_word _ _)
      · have hp : i / 3 < 22 := by omega
        exact (hgp3 (i / 3) hp).2.1 (i % 3) (spN_mod i hi)
    refine ((spLeaf_complete (C := C) (rd := rd) σ3 hcells).1.keep
      (Q := fun σ => ∀ q < 22, SpGP digest values q σ) (Q' := fun σ => ∀ q < 22, SpGP digest values q σ) hgp3
      (fun σ' he' hq q hq' => (hq q hq').keep hq' he' (by have := spEnd_le_C hq'; omega))).mono le_rfl le_rfl
      (fun σ' h => h.2)
  -- the copy
  have hlt : spLeafK.2.2 < spLeafK.2.1 := by
    obtain ⟨-, -, -, -, -, -, h, -, -⟩ := spLeaf_check
    show spLeafM.2.2 + (withPad spVPad isKeccak spLeafM.1).2 < spLeafM.2.1 + (withPad spVPad isKeccak spLeafM.1).2
    omega
  have hnbL : NumBelow spLeafK.2.1
      (Stmt.valsList (((spPowers ++ (spGs.1 ++ spLast.1)) ++ spChecks) ++ spLeafK.1)) := by
    rw [valsList_append]; exact (hnbB.mono hLe).append (spLeaf_complete (C := C) (rd := rd) (fun _ => 0) (fun _ _ => canon_zero)).2
  have hD : Completes C rd 3 (spLeafK.2.1 + 1)
      ((((spPowers ++ (spGs.1 ++ spLast.1)) ++ spChecks) ++ spLeafK.1) ++ [copyS (.n spLeafK.2.1) (.n spLeafK.2.2)])
      σI (fun σ' => ∀ q < 22, SpGP digest values q σ') := by
    refine Completes.append (m := spLeafK.2.1) (by omega) (by omega) hnbL hL (fun σ4 he4 hgp4 => ?_)
    have hext : Ext spLeafK.2.1 (spLeafK.2.1 + 1) σ4 (upds σ4 [(spLeafK.2.1, σ4 (.n spLeafK.2.2))]) :=
      upds_ext σ4 _ (by simp)
    refine completes_atoms rfl hext (fun q hq => (hgp4 q hq).keep hq hext
      (by have := spEnd_le_C hq; omega)) (fun a ha => ?_)
    simp only [copyS, List.mem_singleton, Stmt.atom.injEq] at ha
    subst ha
    show upds σ4 _ _ = upds σ4 _ _
    rw [upds_cons_self, hext.apply (Or.inl hlt)]
  obtain ⟨σf, hef, hgpf, hhf⟩ := hD
  have f0 : σf (.n 0) = cellOf128 parameter := by rw [hef.apply (Or.inl (by norm_num))]; exact i0
  have f1 : σf (.n 1) = keyAddressCell layer tree leaf := by rw [hef.apply (Or.inl (by norm_num))]; exact i1
  have f2 : σf (.n 2) = cellOf128 digest := by rw [hef.apply (Or.inl (by norm_num))]; exact i2
  have hbody : Data.core20.body = ((((spPowers ++ (spGs.1 ++ spLast.1)) ++ spChecks) ++ spLeafK.1) ++
      [copyS (.n spLeafK.2.1) (.n spLeafK.2.2)]) ++ [.ret [.n spLeafK.2.1]] := by
    rw [spBody_eq, spBody_split]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hH : Stmt.HoldsList C rd σf Data.core20.body False (fun rs => rs = [σf (.n spLeafK.2.1)]) := by
    rw [hbody, holdsList_append]
    exact hhf _ _ rfl
  obtain ⟨lf, hrets, hcan, hsound⟩ := sp_wots_sound hH
  obtain ⟨-, hval⟩ := hsound layer tree leaf f1
  rw [f0, f2, cellVal_cellOf128, cellVal_cellOf128_digest, spValues_eq hgpf] at hval
  have hlf : lf = cellOf128 (wotsLeafOf parameter layer tree leaf digest values) :=
    cellVal_inj hcan (isCanonical128_cellOf128 _) (by rw [hval, cellVal_cellOf128_digest])
  have e : σf (.n spLeafK.2.1) = cellOf128 (wotsLeafOf parameter layer tree leaf digest values) := by
    rw [← hlf]; exact List.singleton_inj.mp hrets
  refine ⟨σf, f0, f1, f2, ?_⟩
  rw [← e]
  exact hH

end
end LeanVM.Guest.B1.Sig
