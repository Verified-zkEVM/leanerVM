/-
  LeanVM.Guest.B1.Sig.SpWotsComplete

  `sp_wots` is complete (`sp_wots_complete`): for a digest of digit sum `128` and any chain values,
  its body holds of a valuation whose arguments are the parameter's cell, the key's address cell
  and the digest's cell, returning the cell of the leaf the values recover.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsGroupComplete
public import LeanVM.Guest.B1.Sig.SpWotsSound
public import LeanVM.Guest.B1.Sig.SpWotsData
public import LeanVM.Guest.B1.Sig.CompleteKit

/-!
# `sp_wots`, complete

The valuation: the arguments; the powers; each digit group with the digest's digits (`spK`) and
the chain values' cells loaded at its arm's starts (`spGroupsC`), the first setting the padding
run; the checks, which hold since the digits are the digest's (`spCheck_complete`); the leaf's
message over that run (`spLeaf_complete`); the copy. The returned leaf is then read
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

theorem spState_le_end (p : Nat) : (spState p).2.2 + 6 ≤ spEnd p := by
  rw [spEnd_eq]
  have := spArmB_ge (3 * p) (spN p) (p == 0) (spState p).2.2 (spState p).1 (spState p).2.1 (4 ^ spN p)
  have := spL_ge (p == 0) (spState p).2.2
  omega

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

/-- Every group's arms lie above the padding run. -/
theorem spL_state : ∀ q, q ≤ 21 → 18 ≤ spL (q == 0) (spState q).2.2
  | 0, _ => by rw [spState_zero]; decide
  | q + 1, hq => by
      have ih := spL_state q (by omega)
      have h1 : spL (q + 1 == 0) (spState (q + 1)).2.2 = (spState (q + 1)).2.2 := by simp [spL]
      rw [h1, spState_succ_end (by omega), spEnd_eq]
      have := spArmB_ge (3 * q) (spN q) (q == 0) (spState q).2.2 (spState q).1 (spState q).2.1 (4 ^ spN q)
      omega

/-- A later group's running product and encoding lie below its base, and its base above `23`. -/
theorem spState_in {p : Nat} (hp0 : 0 < p) (hp : p ≤ 21) :
    NBv (spState p).2.2 (spState p).1 ∧ NBv (spState p).2.2 (spState p).2.1 ∧ 24 ≤ (spState p).2.2 := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hl := spL_state q (by omega)
  have he := spEnc_lt_end (3 * q) 3 (q == 0) (spState q).2.2 (spState q).1 (spState q).2.1
  have hg := spArmB_ge (3 * q) 3 (q == 0) (spState q).2.2 (spState q).1 (spState q).2.1 (4 ^ 3)
  have hend : (spState (q + 1)).2.2 = spArmB (3 * q) 3 (q == 0) (spState q).2.2 (spState q).1
      (spState q).2.1 (4 ^ 3) := by
    rw [spState_succ_end (by omega), spEnd_eq, spN_of_lt (by omega)]
  rw [hend]
  rw [spState_succ]
  unfold spEnc at he
  exact ⟨⟨_, by omega, rfl⟩, ⟨_, by unfold spEnc; omega, rfl⟩, by omega⟩

/-- What group `q` establishes: its digit word, its arm's tips canonical and starts loaded. -/
def SpGP (digest : Digest) (values : Sphincs.ChainIndex → Digest) (q : Nat) (σ : Val) : Prop :=
  σ (.n (spState q).2.2) = ofK (addressOfIndex (spK digest q)) ∧
    SpArmPost (3 * q) (spN q) (q == 0) (spState q).2.2 (spState q).1 (spState q).2.1 (spK digest q)
      (fun t => spCv values (3 * q + t)) σ

theorem spPost_q {q t : Nat} (k : Nat) (hk : k < 4 ^ spN q) (ht : t < spN q) :
    ((spState q).2.2 ≤ spSlot (q == 0) (spState q).2.2 t 2 ∧ spSlot (q == 0) (spState q).2.2 t 2 < spEnd q) ∧
      ∃ j, spStartOf (3 * q) (spN q) (q == 0) (spState q).2.2 (spState q).1 (spState q).2.1 k
        (spArmB (3 * q) (spN q) (q == 0) (spState q).2.2 (spState q).1 (spState q).2.1 k) t = .n j ∧
        (spState q).2.2 ≤ j ∧ j < spEnd q := by
  obtain ⟨⟨h1, h2⟩, j, ej, h3, h4⟩ := spPost_bounds (3 * q) (spN q) (q == 0) (spState q).2.2
    (spState q).1 (spState q).2.1 hk ht
  have := spL_ge (q == 0) (spState q).2.2
  rw [← spEnd_eq] at h2 h4
  exact ⟨⟨by omega, h2⟩, j, ej, by omega, h4⟩

theorem SpGP.keep {digest : Digest} {values : Sphincs.ChainIndex → Digest} {q : Nat}
    {σ σ' : Val} (h : SpGP digest values q σ) {lo hi : Nat} (he : Ext lo hi σ σ') (hlo : spEnd q ≤ lo) :
    SpGP digest values q σ' := by
  have hB := spState_le_end q
  refine ⟨by rw [he.apply (Or.inl (by omega))]; exact h.1, fun t ht => ?_, fun t ht => ?_⟩
  · rw [he.apply (Or.inl (by have := (spPost_q (spK digest q) (spK_lt digest q) ht).1.2; omega))]
    exact h.2.1 t ht
  · obtain ⟨j, e, -, hj⟩ := (spPost_q (spK digest q) (spK_lt digest q) ht).2
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

/-- What a valuation needs before group `p`: before the first, `pp` and the key's address canonical;
before a later one, those and the padding run (`SpGood`). -/
def SpBefore (p : Nat) (σ : Val) : Prop :=
  if p = 0 then IsCanonical128 (σ (.n 0)) ∧ IsCanonical128 (σ (.n 1)) else SpGood spPad σ

/-- **Group `p` of the body completes**, its digit word `g^k` loaded. -/
theorem spGroupP_complete {p k : Nat} (hp : p < 22) (hk : k < 4 ^ spN p) (hm : MemOK rd 64)
    (σ : Val) (hσ : SpBefore p σ) (vals : Nat → E) (hv : ∀ t < spN p, IsCanonical128 (vals t)) :
    Completes C rd (spState p).2.2
      (spGroupT (3 * p) (spN p) (p == 0) (spState p).1 (spState p).2.1 (spState p).2.2).2
      (spGroupT (3 * p) (spN p) (p == 0) (spState p).1 (spState p).2.1 (spState p).2.2).1 σ
      (fun σ' => σ' (.n (spState p).2.2) = ofK (addressOfIndex k) ∧
        SpArmPost (3 * p) (spN p) (p == 0) (spState p).2.2 (spState p).1 (spState p).2.1 k vals σ' ∧
        SpGood spPad σ') := by
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · simp only [SpBefore, ↓reduceIte] at hσ
    rw [spState_zero]
    exact spGroupT_complete (Bs := 23) (spN_le 0) hk hm le_rfl (by decide) ⟨0, by norm_num, rfl⟩
      ⟨0, by norm_num, rfl⟩ vals hv σ (fun σ' hag hpre =>
        ⟨by rw [← hag 0 (by norm_num)]; exact hσ.1, by rw [← hag 1 (by norm_num)]; exact hσ.2,
          padRun_ok (P := 13 + 5) hpre⟩)
  · have hσ' : SpGood spPad σ := by simpa [SpBefore, show p ≠ 0 by omega] using hσ
    obtain ⟨hpi, hei, h24⟩ := spState_in hp0 (by omega)
    have hl : spL (p == 0) (spState p).2.2 = (spState p).2.2 := by
      simp [spL, show p ≠ 0 by omega]
    exact spGroupT_complete (Bs := (spState p).2.2) (spN_le p) hk hm (by omega) (by rw [hl]; omega)
      hpi hei vals hv σ (fun σ' hag _ =>
        spGood_congr (B := (spState p).2.2) (by simp [spPad]; omega) (by omega) hag hσ')

/-- **Group `p`'s values are numbered below its end.** -/
theorem spGroupP_nb {p : Nat} (hp : p < 22) :
    NumBelow (spGroupT (3 * p) (spN p) (p == 0) (spState p).1 (spState p).2.1 (spState p).2.2).2
      (Stmt.valsList (spGroupT (3 * p) (spN p) (p == 0) (spState p).1 (spState p).2.1 (spState p).2.2).1) := by
  have hl := spL_state p (by omega)
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · rw [spState_zero] at hl ⊢
    exact spGroupT_nb (spN_le 0) (by omega) ⟨0, by norm_num, rfl⟩ ⟨0, by norm_num, rfl⟩
  · obtain ⟨hpi, hei, -⟩ := spState_in hp0 (by omega)
    have hl' : spL (p == 0) (spState p).2.2 = (spState p).2.2 := by
      simp [spL, show p ≠ 0 by omega]
    exact spGroupT_nb (spN_le p) (by omega) (by rw [hl']; exact NBv.mono' hpi (by omega))
      (by rw [hl']; exact NBv.mono' hei (by omega))

/-- **Groups `p ..< p + m`' values are numbered below their end.** -/
theorem spGL_nb : ∀ m p, p + m ≤ 22 → NumBelow (spGLEnd p m) (Stmt.valsList (spGL p m))
  | 0, _, _ => NumBelow.nil _
  | m + 1, p, hpm => by
      have hnb := spGroupP_nb (show p < 22 by omega)
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · simp only [spGL, List.append_nil]
        have e : spGLEnd p 1 = spEnd p := by simp [spGLEnd]
        rw [e]; exact hnb
      · have e : spGLEnd (p + 1) m = spGLEnd p (m + 1) := by
          unfold spGLEnd; simp only [show m ≠ 0 by omega, ↓reduceIte, Nat.add_eq_zero_iff]
          congr 1; omega
        have hle : spEnd p ≤ spGLEnd (p + 1) m := by
          unfold spGLEnd; simp only [show m ≠ 0 by omega, ↓reduceIte]
          have := spState_le_end (p + 1 + m - 1)
          have := spState_mono (p := p + 1) (q := p + 1 + m - 1) (by omega) (by omega)
          rw [← spState_succ_end (show p < 21 by omega)] at *
          omega
        simp only [spGL, valsList_append]
        rw [← e]
        exact (hnb.mono hle).append (spGL_nb m (p + 1) (by omega))

/-- **Groups `p ..< p + m` complete**, each with the digest's digits and the values loaded. -/
theorem spGroupsC (digest : Digest) (values : Sphincs.ChainIndex → Digest) (hm : MemOK rd 64) :
    ∀ m p, p + m ≤ 22 → ∀ σ, SpBefore p σ →
      Completes C rd (spState p).2.2 (spGLEnd p m) (spGL p m) σ
        (fun σ' => (∀ q, p ≤ q → q < p + m → SpGP digest values q σ') ∧ SpBefore (p + m) σ')
  | 0, p, _, σ, hσ => ⟨σ, Ext.refl _ _ _, ⟨fun q h1 h2 => by omega, by simpa using hσ⟩, fun _ _ hn => hn⟩
  | m + 1, p, hpm, σ, hσ => by
      have hp : p < 22 := by omega
      have hg := spGroupP_complete (C := C) hp (spK_lt digest p) hm σ hσ
        (fun t => spCv values (3 * p + t)) (fun t _ => spCv_canon _ _)
      have hnb := spGroupP_nb hp
      have hbefore : ∀ σ', SpGood spPad σ' → SpBefore (p + 1) σ' := fun σ' h => by
        simpa [SpBefore] using h
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · simp only [spGL, List.append_nil]
        have e : spGLEnd p 1 = spEnd p := by simp [spGLEnd]
        rw [e]
        exact hg.mono le_rfl le_rfl (fun σ' hσ' => ⟨fun q h1 h2 => by
          have : q = p := by omega
          subst this; exact ⟨hσ'.1, hσ'.2.1⟩, hbefore σ' hσ'.2.2⟩)
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
        simp only [spGL]
        refine Completes.append (m := spEnd p) (by have := spState_le_end p; omega)
          (by rw [← e]; exact hle) hnb hg (fun σ1 _ hp1 => ?_)
        have ih := spGroupsC digest values hm m (p + 1) (by omega) σ1 (hbefore σ1 hp1.2.2)
        rw [hst, e] at ih
        refine (ih.keep (Q := SpGP digest values p) (Q' := SpGP digest values p) ⟨hp1.1, hp1.2.1⟩
          (fun σ' he' hq => hq.keep he' le_rfl)).mono le_rfl le_rfl
          (fun σ' ⟨⟨hr, hb⟩, hq⟩ => ⟨fun q h1 h2 => ?_, by rwa [show p + 1 + m = p + (m + 1) by omega] at hb⟩)
        rcases Nat.lt_or_ge q (p + 1) with h | h
        · have : q = p := by omega
          subst this; exact hq
        · exact hr q h (by omega)

theorem spGL_full : spGL 0 22 = spGs.1 ++ spLast.1 := by
  rw [spGL_snoc 21 0, ← spGL_eq 21 0 (by norm_num), ← spGs_fst, spLast_eq]
  rfl

theorem spGLEnd_full : spGLEnd 0 22 = spC := by
  unfold spGLEnd
  simp only [show (22 : Nat) ≠ 0 by norm_num, ↓reduceIte]
  rw [spC, spLast_eq]
  rfl

theorem spC_ge : 24 ≤ spC := by
  rw [← spGLEnd_full]
  unfold spGLEnd
  simp only [show (22 : Nat) ≠ 0 by norm_num, ↓reduceIte, show 0 + 22 - 1 = 21 by norm_num]
  have := spState_le_end 21
  have := (spState_in (p := 21) (by norm_num) le_rfl).2.2
  omega

/-- **The powers and the groups complete**, the digits the digest's and the values loaded. -/
theorem spCode_complete (digest : Digest) (values : Sphincs.ChainIndex → Digest) (hm : MemOK rd 64)
    (σ : Val) (h0 : IsCanonical128 (σ (.n 0))) (h1 : IsCanonical128 (σ (.n 1))) :
    Completes C rd 3 spC (spPowers ++ (spGs.1 ++ spLast.1)) σ
      (fun σ' => (∀ s < 10, σ' (.n (3 + s)) = gen ^ s) ∧ (∀ q < 22, SpGP digest values q σ') ∧
        SpGood spPad σ') ∧
    NumBelow spC (Stmt.valsList (spPowers ++ (spGs.1 ++ spLast.1))) := by
  have hseq : SeqOK 3 spPowers 13 := seqB_ok (by decide +kernel)
  rw [← spGL_full, ← spGLEnd_full]
  have hst0 : (spState 0).2.2 = 13 := by rw [spState_zero]
  have hC := spC_ge
  rw [← spGLEnd_full] at hC
  refine ⟨Completes.append (m := 13) (by norm_num) (by omega) hseq.numBelow (seq_completes hseq σ)
    (fun σ1 he1 hp1 => ?_), ?_⟩
  · have hpow : ∀ s < 10, σ1 (.n (3 + s)) = gen ^ s := by
      intro s hs
      have e : σ1 (.n (3 + s)) = word (2 ^ s) 0 0 := hp1.atom (a := .const (.n (3 + s)) _) (by
        simp only [spPowers, cst, List.mem_map, List.mem_range]
        exact ⟨s, hs, rfl⟩)
      rw [e, word_eq_eOfNat, Value.gen_pow_eq_eOfNat (by omega)]
    have hag : AgreeBelow 3 σ σ1 := he1.agree
    have hg := spGroupsC (C := C) digest values hm 22 0 (by norm_num) σ1
      (by simp only [SpBefore, ↓reduceIte]
          exact ⟨by rw [← hag 0 (by norm_num)]; exact h0, by rw [← hag 1 (by norm_num)]; exact h1⟩)
    rw [hst0] at hg
    refine (hg.keep (Q := fun σ => ∀ s < 10, σ (.n (3 + s)) = gen ^ s)
      (Q' := fun σ => ∀ s < 10, σ (.n (3 + s)) = gen ^ s) hpow
      (fun σ' he' hq s hs => by rw [he'.apply (Or.inl (by omega))]; exact hq s hs)).mono le_rfl le_rfl
      (fun σ' ⟨⟨hr, hb⟩, hq⟩ => ⟨hq, fun q hq' => hr q (Nat.zero_le _) (by omega),
        by simpa [SpBefore] using hb⟩)
  · rw [valsList_append]
    have hnb := spGL_nb 22 0 (by norm_num)
    exact (hseq.numBelow.mono (by omega)).append hnb

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
  obtain ⟨s2, hpad, hg⟩ := spGroupsT_sound (C := C) (rd := rd) (σ := σ) 21 0 (by norm_num) h
  have hpad := hpad rfl (by norm_num)
  rw [spLast_eq] at s2
  obtain ⟨-, -, kL, hkL, hxL, haL⟩ := spGroupT_sound s2
  have hgrp : ∀ p < 22, SpGroupOK rd σ p := by
    intro p hp
    by_cases hp21 : p < 21
    · simpa using hg p hp21
    · have : p = 21 := by omega
      subst this
      exact ⟨kL, by simpa [spN] using hkL, hxL, by simpa [spN] using haL⟩
  obtain ⟨-, hprod, henc⟩ := spCodeword_sound hpow hpad hgrp
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

/-- The codeword's product and encoding lie below the checks. -/
theorem spEP_lt : spEnc false 1 (spState 21).2.2 < spC ∧ spProd false 1 (spState 21).2.2 < spC := by
  have h := spEnc_lt_end 63 1 false (spState 21).2.2 (spState 21).1 (spState 21).2.1
  have e : spC = spArmB 63 1 false (spState 21).2.2 (spState 21).1 (spState 21).2.1 (4 ^ 1) := by
    rw [spC, spLast_eq, spGroupT_end]
  rw [← e] at h
  unfold spEnc at h
  exact ⟨by unfold spEnc; omega, by omega⟩

/-- **The checks complete**, the encoding the argument's and the product the target. -/
theorem spCheck_complete (σ : Val)
    (henc : σ (.n (spEnc false 1 (spState 21).2.2)) = σ (.n 2))
    (hprod : σ (.n (spProd false 1 (spState 21).2.2)) = spTarget) :
    Completes C rd spC (spC + 3) spChecks σ
      (fun σ' => σ' (.n (spC + 2)) = σ (.n 1) + word (tw 2) 0 0) := by
  obtain ⟨hE, hP⟩ := spEP_lt
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
  obtain ⟨hE, hP⟩ := spEP_lt
  have hC := spC_ge
  intro v hv
  simp only [spChecks, cst, addS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with (rfl | rfl) | rfl | (rfl | rfl) | rfl | (rfl | rfl | rfl)
  all_goals exact ⟨_, by omega, rfl⟩

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
    have h := (spPost_q (q := i / 3) 0 (by positivity) (spN_mod i hi)).1.2
    have := spEnd_le_C hp
    exact ⟨_, rfl, by omega⟩

/-- **The leaf's message completes** on canonical cells, over the padding run. -/
theorem spLeaf_complete (σ : Val) (hp : PadOK σ spPad) (hc : ∀ v ∈ spLeafCells, IsCanonical128 (σ v)) :
    Completes C rd (spC + 3) spLeafK.2.1 spLeafK.1 σ (fun _ => True) ∧
      NumBelow spLeafK.2.1 (Stmt.valsList spLeafK.1) := by
  have hC := spC_ge
  obtain ⟨h1, h2, -⟩ := kMsg_complete (C := C) (rd := rd) (pad := spPad)
    (cells := spLeafCells.map KC.cell) (len := 1056) (tailRun := false) (b := spC + 3) σ hp
    (by simp [spPad]; omega) (fun c hcm => by
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hcm
      obtain ⟨j, ej, hj⟩ := spLeafCells_lt v hv
      exact ⟨⟨j, hj, ej⟩, hc v hv⟩) (fun h => by simp at h)
  exact ⟨h1, h2⟩

theorem spLeafCells_KCb : ∀ c ∈ spLeafCells.map KC.cell, KCb (spC + 3) c := by
  intro c hcm
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hcm
  obtain ⟨j, ej, hj⟩ := spLeafCells_lt v hv
  exact ⟨j, hj, ej⟩

theorem spLeafK_le : spC + 3 ≤ spLeafK.2.1 :=
  kMsg_le (by simp [spPad]; have := spC_ge; omega) spLeafCells_KCb

theorem spLeafK_out : spLeafK.2.2 < spLeafK.2.1 := by
  have := kMsg_out spPad (spLeafCells.map KC.cell) 1056 false (spC + 3)
  show (kMsg spPad (spLeafCells.map KC.cell) 1056 false none (spC + 3)).2.2 <
    (kMsg spPad (spLeafCells.map KC.cell) 1056 false none (spC + 3)).2.1
  omega

theorem spLeaf_nb : NumBelow spLeafK.2.1 (Stmt.valsList spLeafK.1) :=
  kMsg_numBelow (by simp [spPad]; have := spC_ge; omega) spLeafCells_KCb

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
      (fun σ' => ((∀ q < 22, SpGP digest values q σ') ∧ SpGood spPad σ') ∧
        σ' (.n (spC + 2)) = σI (.n 1) + word (tw 2) 0 0) := by
    refine Completes.append (m := spC) (by omega) (by omega) hnbA hA.withHolds
      (fun σ2 he2 ⟨⟨hpow, hgp, hgd⟩, hh2⟩ => ?_)
    have hag2 : AgreeBelow 3 σI σ2 := he2.agree
    have h22 : σ2 (.n 2) = cellOf128 digest := by rw [← hag2 2 (by norm_num)]; exact i2
    have h21 : σ2 (.n 1) = σI (.n 1) := (hag2 1 (by norm_num)).symm
    have hs := (holdsList_split_atoms (xs := spPowers) rfl hh2).2
    rw [show spGs.1 ++ spLast.1 = spGs.1 ++ (spLast.1 ++ []) by simp] at hs
    obtain ⟨henc, hprod⟩ := spVals hs hpow hgp hT
    refine ((spCheck_complete (C := C) (rd := rd) σ2 (by rw [henc, h22]) hprod).keep
      (Q := fun σ => (∀ q < 22, SpGP digest values q σ) ∧ SpGood spPad σ)
      (Q' := fun σ => (∀ q < 22, SpGP digest values q σ) ∧ SpGood spPad σ) ⟨hgp, hgd⟩
      (fun σ' he' hq => ⟨fun q hq' => (hq.1 q hq').keep he' (spEnd_le_C hq'),
        spGood_congr (B := spC) (by simp [spPad]; omega) (by omega) he'.agree hq.2⟩)).mono le_rfl le_rfl
      (fun σ' ⟨h1, h2⟩ => ⟨h2, by rw [h1, h21]⟩)
  -- the leaf
  have hLe : spC + 3 ≤ spLeafK.2.1 := spLeafK_le
  have hnbB : NumBelow (spC + 3) (Stmt.valsList ((spPowers ++ (spGs.1 ++ spLast.1)) ++ spChecks)) := by
    rw [valsList_append]; exact (hnbA.mono (by omega)).append spChecks_nb
  have hL : Completes C rd 3 spLeafK.2.1 (((spPowers ++ (spGs.1 ++ spLast.1)) ++ spChecks) ++ spLeafK.1) σI
      (fun σ' => ∀ q < 22, SpGP digest values q σ') := by
    refine Completes.append (m := spC + 3) (by omega) hLe hnbB hB (fun σ3 he3 ⟨⟨hgp3, hgd3⟩, h32⟩ => ?_)
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
    refine ((spLeaf_complete (C := C) (rd := rd) σ3 hgd3.2.2 hcells).1.keep
      (Q := fun σ => ∀ q < 22, SpGP digest values q σ) (Q' := fun σ => ∀ q < 22, SpGP digest values q σ) hgp3
      (fun σ' he' hq q hq' => (hq q hq').keep he' (by have := spEnd_le_C hq'; omega))).mono le_rfl le_rfl
      (fun σ' h => h.2)
  -- the copy
  have hlt : spLeafK.2.2 < spLeafK.2.1 := spLeafK_out
  have hnbL : NumBelow spLeafK.2.1
      (Stmt.valsList (((spPowers ++ (spGs.1 ++ spLast.1)) ++ spChecks) ++ spLeafK.1)) := by
    rw [valsList_append]; exact (hnbB.mono hLe).append spLeaf_nb
  have hD : Completes C rd 3 (spLeafK.2.1 + 1)
      ((((spPowers ++ (spGs.1 ++ spLast.1)) ++ spChecks) ++ spLeafK.1) ++ [copyS (.n spLeafK.2.1) (.n spLeafK.2.2)])
      σI (fun σ' => ∀ q < 22, SpGP digest values q σ') := by
    refine Completes.append (m := spLeafK.2.1) (by omega) (by omega) hnbL hL (fun σ4 he4 hgp4 => ?_)
    have hext : Ext spLeafK.2.1 (spLeafK.2.1 + 1) σ4 (upds σ4 [(spLeafK.2.1, σ4 (.n spLeafK.2.2))]) :=
      upds_ext σ4 _ (by simp)
    refine completes_atoms rfl hext (fun q hq => (hgp4 q hq).keep hext
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
