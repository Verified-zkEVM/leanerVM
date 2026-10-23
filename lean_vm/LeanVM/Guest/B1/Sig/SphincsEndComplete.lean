/-
  LeanVM.Guest.B1.Sig.SphincsEndComplete

  The codeword, the one-time leaf and the tree of `verify_sig_lean_sphincs` complete, up to the
  root's check.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsMidComplete
public import LeanVM.Guest.B1.Sig.XmssCore

/-!
# The codeword, the leaf and the tree, complete

`sEnd_complete`: from the powers' end, the codeword dispatching on the digits of `N` (the
encoding's digest the literal of its 64 digits, which sum to `123`), its chains' starts `vals`, the
leaf address, the leaf and the tree over the index's bits and the siblings `sibs`: the root is
canonical and the hints are kept.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

attribute [local irreducible] kMsg codewordT merkleT

variable {C : CallRel} {rd : Reader}

theorem sCw_eq : sCw = codewordT (sWc sEnc.2.1) 21 sTarget (.n sEnc.2.2) (sEnc.2.1 + 10) :=
  codewordT_weq sW_weq _ _ _ (by norm_num)

theorem sEnc_ge : sB + 38 ≤ sEnc.2.1 ∧ sEnc.2.2 + 13 ≤ sEnc.2.1 := by
  have hB := sB_ge
  obtain ⟨f1, -, -⟩ := sFb_shape
  have hcellsNB : ∀ c ∈ sTops.map KC.cell, KCb (sFb.2.1 + 1) c := by
    intro c hc
    simp only [sTops, List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, List.mem_map] at hc
    rcases hc with ((rfl | rfl) | ⟨v, hv, rfl⟩) | rfl
    · exact ⟨162, by omega, rfl⟩
    · exact ⟨164, by omega, rfl⟩
    · obtain ⟨k, hk, e⟩ := List.getElem_of_mem hv
      have hk16 : k < 16 := by rw [sTops_count] at hk; exact hk
      have := sT_nb hk16
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some, e] at this
      exact this.mono' (by omega)
    · exact ⟨_, by omega, rfl⟩
  have hE1 : sFb.2.1 + 1 ≤ sEnc.2.1 := kMsg_le (by simp only [sPad]; omega) hcellsNB
  exact ⟨by omega, kMsg_out _ _ _ _ _⟩

theorem sNode_min (l : Nat) : sNode l = sNode (min l 25) := by
  simp only [sNode, V.mk.injEq, true_and]
  omega

theorem sEndPre_split : sCw.1 ++ sEndPre = sCw.1 ++ ([cst sCw.2.1 (word (tw 2) 0 0),
    addS (.n (sCw.2.1 + 1)) (sNode 0) (.n sCw.2.1)] ++ (sLeaf.1 ++ sMk.1)) := by
  simp only [sEndPre, List.append_assoc]

/-- **The codeword, the leaf and the tree complete.** -/
theorem sEnd_complete (hm : MemOK rd 256) (σ : Val) (hg : SGood sEnc.2.1 σ) {N : Nat}
    (hN : σ (.n sEnc.2.2) = lit (∑ i ∈ Finset.range 64, N / 4 ^ i % 4 * 4 ^ i))
    (hs : ∑ i ∈ Finset.range 64, N / 4 ^ i % 4 = 123)
    (vals : Nat → E) (hv : ∀ i, IsCanonical128 (vals i))
    {bits : Nat → Bool} (hbits : ∀ l < 26, σ (sBit l) = if bits l then 1 else 0)
    (hnodes : ∀ l < 26, IsCanonical128 (σ (sNode l)))
    {sibs : Nat → E} (hsc : ∀ l < 26, IsCanonical128 (sibs l)) :
    Completes C rd (sEnc.2.1 + 10) sMk.2.1 (sCw.1 ++ sEndPre) σ
      (fun σ' => IsCanonical128 (σ' sMk.2.2) ∧ ∀ σ'', AgreeBelow sMk.2.1 σ' σ'' →
        (∀ q ≤ 21, σ'' (.n (cwState sW (sEnc.2.1 + 10) q).2.2) = ofK (gpow (nDigits 21 N q))) ∧
        (∀ i < 64, σ'' (cwPos sW 21 (sEnc.2.1 + 10) (nDigits 21 N) i) = vals i) ∧
        ∀ l < 26, mSib σ'' sBit l (mBase sNodeOf 0 l sLeaf.2.1) = sibs l) := by
  have hB := sB_ge
  obtain ⟨hE1, hE2⟩ := sEnc_ge
  set pb := sEnc.2.1 with hpb
  have hpb132 : 132 ≤ pb := by omega
  -- the bounds
  have b1 : pb + 10 < sCw.2.1 := by
    rw [sCw_eq]
    exact cwBase_lt (sWc pb) (q := 0) (G := 21) _ _ _ (by norm_num)
  have htips : sCw.2.2 = (List.range 64).map (cwTip sW (pb + 10)) :=
    codewordT_tips sW (G := 21) (by norm_num) _ _ _
  have htipNB : ∀ i < 64, NBv sCw.2.1 (cwTip sW (pb + 10) i) := by
    intro i hi
    obtain ⟨j, ej, hj⟩ := cwTip_lt sW (G := 21) sTarget (.n sEnc.2.2) (pb + 10)
      (by norm_num) (show i < 3 * 21 + 1 by omega)
    exact ⟨j, hj, ej⟩
  have hcells : ∀ c ∈ (sPP :: V.n (sCw.2.1 + 1) :: sCw.2.2).map KC.cell, ∃ v, c = KC.cell v ∧
      (v = sPP ∨ v = .n (sCw.2.1 + 1) ∨ ∃ i < 64, v = cwTip sW (pb + 10) i) := by
    intro c hc
    simp only [List.map_cons, List.mem_cons, htips, List.map_map, List.mem_map,
      List.mem_range, Function.comp_apply] at hc
    rcases hc with rfl | rfl | ⟨i, hi, rfl⟩
    · exact ⟨_, rfl, Or.inl rfl⟩
    · exact ⟨_, rfl, Or.inr (Or.inl rfl)⟩
    · exact ⟨_, rfl, Or.inr (Or.inr ⟨i, hi, rfl⟩)⟩
  have hcellNB : ∀ c ∈ (sPP :: V.n (sCw.2.1 + 1) :: sCw.2.2).map KC.cell, KCb (sCw.2.1 + 2) c := by
    intro c hc
    obtain ⟨v, rfl, hv'⟩ := hcells c hc
    rcases hv' with rfl | rfl | ⟨i, hi, rfl⟩
    · exact ⟨2, by omega, rfl⟩
    · exact ⟨_, by omega, rfl⟩
    · exact (htipNB i hi).mono' (by omega)
  have b2 : sCw.2.1 + 2 ≤ sLeaf.2.1 := kMsg_le (show sPad + 5 ≤ sCw.2.1 + 2 by simp only [sPad]; omega) hcellNB
  have b3 : sLeaf.2.1 ≤ sMk.2.1 := merkleT_snd_ge ..
  have hout : sLeaf.2.2 + 13 ≤ sLeaf.2.1 := kMsg_out _ _ _ _ _
  -- the codeword
  have hdig : ∀ i ∈ Finset.range (3 * 21 + 1), digK (nDigits 21 N) i = N / 4 ^ i % 4 :=
    fun i hi => digK_nDigits 21 N (Finset.mem_range.mp hi)
  have hs' : ∑ i ∈ Finset.range (3 * 21 + 1), N / 4 ^ i % 4 = 123 := hs
  have hsum2 : ∑ i ∈ Finset.range (3 * 21 + 1), digK (nDigits 21 N) i * 4 ^ i =
      ∑ i ∈ Finset.range 64, N / 4 ^ i % 4 * 4 ^ i :=
    Finset.sum_congr rfl fun i hi => by rw [hdig i hi]
  have hcw := codewordT_complete (C := C) (rd := rd) (sWc_shape hpb132) (sWc_canon hpb132) (sWc_atoms pb)
    (fun σ hg => sWc_sound hg) (fun σ hg => sWc_pow hg) (G := 21) (target := sTarget) (d0 := .n sEnc.2.2)
    (b := pb + 10) (by norm_num) le_rfl (by omega) le_rfl (fun i hi => hm i (by omega)) (sWc_pw pb)
    ⟨_, by omega, rfl⟩ (nDigits 21 N) (fun q _ => nDigits_lt 21 N q) vals hv σ hg
    (by rw [Finset.sum_congr rfl hdig, hs', sTarget_eq])
    (by rw [hsum2, hN])
  rw [← sCw_eq] at hcw
  have hcwNB : NumBelow sCw.2.1 (Stmt.valsList sCw.1) := by
    rw [sCw_eq]
    exact codewordT_numBelow (sWc_shape hpb132) (by omega) le_rfl (sWc_pw pb) ⟨_, by omega, rfl⟩
  rw [sEndPre_split]
  refine Completes.append (m := sCw.2.1) (le_of_lt b1) (by omega) hcwNB hcw (fun σ2 he2 hp2 => ?_)
  obtain ⟨hg2, htip2, hdg2, hkp2⟩ := hp2
  have hag2 : AgreeBelow (pb + 10) σ σ2 := he2.agree
  -- the leaf's address
  have hseq : SeqOK sCw.2.1 [cst sCw.2.1 (word (tw 2) 0 0), addS (.n (sCw.2.1 + 1)) (sNode 0) (.n sCw.2.1)]
      (sCw.2.1 + 2) := ⟨rfl, ⟨rfl, ⟨131, by omega, rfl⟩, ⟨_, by omega, rfl⟩⟩, rfl⟩
  refine Completes.seq hseq (by omega) (fun σ3 he3 hh3 => ?_)
  have hag3 : AgreeBelow sCw.2.1 σ2 σ3 := he3.agree
  have e1 : σ3 (.n sCw.2.1) = word (tw 2) 0 0 := hh3.atom (List.mem_cons_self ..)
  have e2 : σ3 (.n (sCw.2.1 + 1)) = σ3 (sNode 0) + σ3 (.n sCw.2.1) :=
    hh3.atom (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have tr3 : ∀ k < pb + 10, σ3 (.n k) = σ (.n k) := fun k hk => by
    rw [hag3.apply ⟨k, by omega, rfl⟩, hag2.apply ⟨k, hk, rfl⟩]
  have hn3 : σ3 (sNode 0) = σ (sNode 0) := tr3 131 (by omega)
  have hpad3 : PadOK σ3 sPad := hg.2.2.1.congr (b := pb + 10) (by simp only [sPad]; omega)
    (fun k hk => (tr3 k hk).symm)
  -- the leaf
  have hck : ∀ c ∈ (sPP :: V.n (sCw.2.1 + 1) :: sCw.2.2).map KC.cell, KCb (sCw.2.1 + 2) c ∧ KCc σ3 c := by
    intro c hc
    refine ⟨hcellNB c hc, ?_⟩
    obtain ⟨v, rfl, hv'⟩ := hcells c hc
    show IsCanonical128 (σ3 v)
    rcases hv' with rfl | rfl | ⟨i, hi, rfl⟩
    · show IsCanonical128 (σ3 (.n 2)); rw [tr3 2 (by omega)]; exact hg.1
    · rw [e2, e1, hn3]; exact canon_add hg.2.1 (canon_word _ _)
    · rw [hag3.apply (htipNB i hi), cwTip_weq sW_weq _ i (by omega)]
      exact htip2 i (by omega)
  obtain ⟨hk1, hk2, -⟩ := kMsg_complete (C := C) (rd := rd) (tailRun := false) (len := 1056) σ3 hpad3
    (by simp only [sPad]; omega) hck (fun h => by simp at h)
  refine Completes.append (m := sLeaf.2.1) b2 b3 hk2 hk1.withHolds (fun σ4 he4 hp4 => ?_)
  have hag4 : AgreeBelow (sCw.2.1 + 2) σ3 σ4 := he4.agree
  have hlk : AtomsHold rd σ4 sLeaf.1 := atomsHold_of_holdsList (kMsg_atoms ..) hp4.2
  have hpad4 : PadOK σ4 sPad := hpad3.congr (by simp only [sPad]; omega) hag4
  have hleafc : IsCanonical128 (σ4 (.n sLeaf.2.2)) := by
    rw [sLeaf_sound hpad4 hlk]; exact canon_hcell _
  -- the path
  have tr4 : ∀ k < pb + 10, σ4 (.n k) = σ (.n k) := fun k hk => by
    rw [hag4.apply ⟨k, by omega, rfl⟩, tr3 k hk]
  have hmk := merkleT_complete (C := C) (rd := rd) (pad := sPad) (pp := sPP) (bitOf := sBit)
    (nodeOf := sNodeOf) (addrOf := sAddrOf) (bits := bits) (sibs := sibs) 26 0
    (.n sLeaf.2.2) sLeaf.2.1 σ4 hpad4 (by simp only [sPad]; omega) ⟨2, by omega, rfl⟩
    ⟨_, by omega, rfl⟩
    (fun j hj => by
      rw [Nat.zero_add]
      exact ⟨⟨30 + j, by omega, rfl⟩, by rw [show sBit j = V.n (30 + j) from rfl, tr4 _ (by omega)]; exact hbits j hj⟩)
    (fun l nd h => by
      simp only [sNodeOf] at h
      split at h
      · cases h
      · cases h
        rw [sNode_min]
        refine ⟨⟨56 + 3 * (25 - min (l + 1) 25), by omega, rfl⟩, ?_⟩
        rw [show sNode (min (l + 1) 25) = V.n (56 + 3 * (25 - min (l + 1) 25)) from rfl, tr4 _ (by omega)]
        exact hnodes _ (by omega))
    (by show IsCanonical128 (σ4 (.n 2)); rw [tr4 2 (by omega)]; exact hg.1) hleafc
    (fun j hj => by rw [Nat.zero_add]; exact hsc j hj)
  obtain ⟨σ5, he5, ⟨-, hc5, hsib5⟩, hh5⟩ := hmk
  refine ⟨σ5, he5, ⟨hc5, fun σ'' hag'' => ?_⟩, hh5⟩
  have tr : ∀ k < sCw.2.1, σ'' (.n k) = σ2 (.n k) := fun k hk => by
    rw [hag''.apply ⟨k, by omega, rfl⟩, he5.apply (Or.inl (by omega)), hag4.apply ⟨k, by omega, rfl⟩,
      hag3.apply ⟨k, hk, rfl⟩]
  refine ⟨fun q hq => ?_, fun i hi => ?_, fun l hl => ?_⟩
  · -- the digits
    have hlt := cwBase_lt (sWc pb) (G := 21) sTarget (.n sEnc.2.2) (pb + 10) hq
    rw [← sCw_eq] at hlt
    rw [cwState_weq sW_weq _ q (by omega), tr _ hlt]
    exact hdg2 q hq
  · -- the starts
    obtain ⟨j, ej, hj⟩ := cwPos_lt (sWc pb) sTarget (.n sEnc.2.2) (pb + 10) (G := 21)
      (by norm_num) (fun q _ => nDigits_lt 21 N q) (show i < 3 * 21 + 1 by omega)
    rw [← sCw_eq] at hj
    rw [cwPos_weq sW_weq 21 _ _ i (by omega) (by norm_num), ej, tr j hj, ← ej]
    exact hkp2 i (by omega)
  · -- the siblings
    have hs5 := hsib5 l hl
    rw [Nat.zero_add] at hs5
    have hlt : mBase sNodeOf 0 l sLeaf.2.1 + 2 ≤ sMk.2.1 :=
      mBase_lt sPad sPP sBit sNodeOf sAddrOf 26 0 (.n sLeaf.2.2) sLeaf.2.1 l hl
    unfold mSib at hs5 ⊢
    rw [show sBit l = V.n (30 + l) from rfl, hag''.apply ⟨30 + l, by omega, rfl⟩,
      hag''.apply ⟨mBase sNodeOf 0 l sLeaf.2.1, by omega, rfl⟩,
      hag''.apply ⟨mBase sNodeOf 0 l sLeaf.2.1 + 1, by omega, rfl⟩]
    exact hs5

end
end LeanVM.Guest.B1.Sig
