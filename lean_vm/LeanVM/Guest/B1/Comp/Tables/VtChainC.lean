/-
  LeanVM.Guest.B1.Comp.Tables.VtChainC

  `verify_tables`' completeness over a completeness model: the windows chained, phase by phase.
-/

module

public import LeanVM.Guest.B1.Comp.Tables.VtWindowsC
public import LeanVM.Guest.B1.Comp.Tables.VtAtB
public import LeanVM.Guest.B1.Tables.VerifyTablesComplete

/-!
# The chain over a completeness model

`VerifyTablesCChain.lean`, `VerifyTablesCChain2.lean` and `VerifyTablesComplete.lean` under a
completeness model's semantics: `vt_consB`, `vt_consHB` chain the windows (`vt_cons`,
`vt_consH`); the windows free of `BLAKE2S` are the deployed ones carried over
(`Completes.toRelB` over `vtFree`, their freedom checked by the kernel), the hashing ones the
model's (`VtWindowsC.lean`): `vt_phaseB1C`, `vt_phaseB2C`, `vt_pre4273C`, `vt_ev_runC`,
`vt_phaseDC`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig LeanVM.E2E.Complete

@[expose] public section

/-- **Two windows in sequence under `S`**, the first's facts kept (`vt_cons`). -/
theorem vt_consB {S : BlakeSem} {C : CallRel} {rd : Reader} {a l1 l2 lo mid hi : ℕ} {σ : Val}
    {P Q : Val → Prop} (hlo : lo ≤ mid) (hhi : mid ≤ hi)
    (hnb : NumBelow mid (Stmt.valsList ((vtPre.drop a).take l1)))
    (h1 : CompletesB S C rd lo mid ((vtPre.drop a).take l1) σ P)
    (hP : ∀ σ1 σ2 : Val, (∀ k < mid, σ2 (.n k) = σ1 (.n k)) → P σ1 → P σ2)
    (h2 : ∀ σ', Ext lo mid σ σ' → P σ' →
      CompletesB S C rd mid hi ((vtPre.drop (a + l1)).take l2) σ' Q) :
    CompletesB S C rd lo hi ((vtPre.drop a).take (l1 + l2)) σ (fun σ'' => P σ'' ∧ Q σ'') := by
  rw [List.take_add, List.drop_drop]
  refine CompletesB.append hlo hhi hnb h1 fun σ' he hp => ?_
  obtain ⟨σ'', he', hq, hh⟩ := h2 σ' he hp
  exact ⟨σ'', he', ⟨hP σ' σ'' (fun k hk => he'.apply (Or.inl hk)) hp, hq⟩, hh⟩

/-- **Two windows in sequence under `S`**, the first's facts kept and its statements holding for
the second (`vt_consH`). -/
theorem vt_consHB {S : BlakeSem} {C : CallRel} {rd : Reader} {a l1 l2 lo mid hi : ℕ} {σ : Val}
    {P Q : Val → Prop} (hlo : lo ≤ mid) (hhi : mid ≤ hi)
    (hnb : NumBelow mid (Stmt.valsList ((vtPre.drop a).take l1)))
    (h1 : CompletesB S C rd lo mid ((vtPre.drop a).take l1) σ P)
    (hP : ∀ σ1 σ2 : Val, (∀ k < mid, σ2 (.n k) = σ1 (.n k)) → P σ1 → P σ2)
    (h2 : ∀ σ', Ext lo mid σ σ' → P σ' → (∀ (next : Prop) (kret : List E → Prop), next →
      Stmt.HoldsListB S C rd σ' ((vtPre.drop a).take l1) next kret) →
      CompletesB S C rd mid hi ((vtPre.drop (a + l1)).take l2) σ' Q) :
    CompletesB S C rd lo hi ((vtPre.drop a).take (l1 + l2)) σ (fun σ'' => P σ'' ∧ Q σ'') := by
  obtain ⟨σ1, he1, hp1, hh1⟩ := h1
  have h1' : CompletesB S C rd lo mid ((vtPre.drop a).take l1) σ (fun σ' => P σ' ∧
      ∀ (next : Prop) (kret : List E → Prop), next →
        Stmt.HoldsListB S C rd σ' ((vtPre.drop a).take l1) next kret) := ⟨σ1, he1, ⟨hp1, hh1⟩, hh1⟩
  refine (vt_consB hlo hhi hnb h1' (fun σ1 σ2 hag hp => ⟨hP σ1 σ2 hag hp.1, fun next kret hn =>
    (holdsListB_frame hnb (fun k hk => (hag k hk).symm) next kret).mp (hp.2 next kret hn)⟩)
    fun σ' he hp => h2 σ' he hp.1 hp.2).mono le_rfl le_rfl fun σ'' h => ⟨h.1.1, h.2⟩

section
variable {rd : Reader}

set_option maxRecDepth 100000 in
/-- **Statements `1574 ..< 1808` over a completeness model** (`vt_phaseB1`): `block_index_mle` hinted, the selectors `0`, `1`, `2` with the
boundary block, the memory block and the bytecode block between them. -/
theorem vt_phaseB1C {CM : CompModel} (hSel : VtSelComplete) (hG1 : VtGlue1) (hG3 : VtGlue3) {κ : ℕ}
    (hκ : 6 ≤ κ) (hlow : LowDef κ rd) {σ : Val}
    {cur zeta bk sq fpw pool cplen idxc offP pbim pI2 pI3 m0 m1 m2 : E} {point : List E} {logMem : ℕ}
    {cv : Digest} {ks off : ℕ → ℕ} {ptr : ℕ → E}
    (h2 : σ (.n 2) = cur) (h5 : σ (.n 5) = zeta) (h6 : σ (.n 6) = gen ^ point.length) (h9 : σ (.n 9) = bk)
    (h10 : σ (.n 10) = sq) (h11 : σ (.n 11) = fpw) (h13 : σ (.n 13) = pool) (h14 : σ (.n 14) = cplen)
    (hcv : (σ (.n 19), σ (.n 20)) = digestScalars cv) (h128 : σ (.n 128) = offP) (h1817 : σ (.n 1817) = idxc)
    (hpl : point.length < 33) (hz : ReadsAt rd zeta point) (hsq : ∀ j < 34, LoadHolds rd sq j (gen ^ 2 ^ j))
    (hm : ∀ i < 65, SelMem rd bk offP point ks off ptr i) (hfpw : ∀ i < 16, ∃ v, LoadHolds rd fpw i v)
    (hidxc : ∀ t < 34, LoadHolds rd idxc t (1 + gen ^ 2 ^ t))
    (hk1 : ks (selBlk.getD 1 0) = logMem) (hk2 : ks (selBlk.getD 2 0) = 18) (h0lm : 0 < logMem)
    (hlmp : logMem ≤ point.length) (hlm32 : logMem ≤ 32) (h18p : 18 ≤ point.length)
    (hpI2 : ReadsAt rd pI2 (idxChainW point logMem))
    (hb1 : LoadHolds rd pbim 1 ((idxChainW point logMem).getD logMem 0))
    (hpI3 : ReadsAt rd pI3 (idxChainW point 18)) (hb2 : LoadHolds rd pbim 2 ((idxChainW point 18).getD 18 0))
    (hcur : ReadsAt rd cur [m0, m1, m2]) (hpool : ReadsAt rd pool [m0, m1, m2])
    (hcpl : ∀ j < 3, LoadHolds rd cplen j (gen ^ logMem)) (hA : ObsAns CM.hm cv [m0, m1, m2]) :
    CompletesB CM.sem (coreProgram.RelB CM.sem rd) rd 1852 2077
      ((vtPre.drop 1574).take (3 + (28 + (11 + (28 + (80 + (28 + 56))))))) σ (fun σ' =>
        σ' (.n 1852) = pbim ∧ (∀ i < 3, SelPost point ks off ptr i σ') ∧ σ' (.n 1925) = pI2 ∧
          σ' (.n 1937) = m0 ∧ σ' (.n 1955) = m1 ∧ σ' (.n 1973) = m2 ∧
          (σ' (.n 1986), σ' (.n 1987)) = digestScalars (obsAllT CM.hm cv [m0, m1, m2]) ∧ σ' (.n 2029) = pI3) := by
  have stS : ∀ i lo, selVal.getD i 0 = lo → ∀ σ1 σ2 : Val, (∀ k < lo + 27, σ2 (.n k) = σ1 (.n k)) →
      SelPost point ks off ptr i σ1 → SelPost point ks off ptr i σ2 := fun i lo hlo σ1 σ2 hag hp => by
    subst hlo; unfold SelPost at hp ⊢; simp +contextual (disch := omega) only [hag]; exact hp
  refine (vt_consB (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel)) ((vt_c_bim pbim).toRelB freeOn_vtFree (by decide +kernel))
    (by vt_stable) fun σ1 e1 p1 =>
    vt_consB (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      ((vt_c_sel' hSel hκ hlow hpl hz hsq (by norm_num : 0 < 65) (hm 0 (by norm_num)) (by decide) (by decide)
        (by rw [Ext.app' e1 5 (by norm_num), h5]) (by rw [Ext.app' e1 6 (by norm_num), h6])
        (by rw [Ext.app' e1 9 (by norm_num), h9]) (by rw [Ext.app' e1 10 (by norm_num), h10])
        (by rw [Ext.app' e1 128 (by norm_num), h128])).toRelB freeOn_vtFree (by decide +kernel)) (stS 0 1855 (by decide)) fun σ2 e2 p2 =>
    vt_consB (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      ((hG1 rd σ2 fpw (by rw [Ext.app' e2 11 (by norm_num), Ext.app' e1 11 (by norm_num), h11]) hfpw).toRelB freeOn_vtFree (by decide +kernel))
      (fun _ _ _ _ => trivial) fun σ3 e3 _ =>
    vt_consB (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      ((vt_c_sel' hSel hκ hlow hpl hz hsq (by norm_num : 1 < 65) (hm 1 (by norm_num)) (by decide) (by decide)
        (by simp (disch := omega) only [Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h5)
        (by simp (disch := omega) only [Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h6)
        (by simp (disch := omega) only [Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h9)
        (by simp (disch := omega) only [Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h10)
        (by simp (disch := omega) only [Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h128)).toRelB freeOn_vtFree (by decide +kernel)) (stS 1 1893 (by decide)) fun σ4 e4 p4 =>
    vt_consB (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      (vt_glue2C (CM := CM) (rd := rd) (σ := σ4) (cur := cur) (fpw := fpw) (pool := pool)
        (cplen := cplen) (zeta := zeta) (idxc := idxc) (bim := pbim) (pI := pI2) (point := point)
        (by simp (disch := omega) only [Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h2)
        (by simp (disch := omega) only [Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h5)
        (by simp (disch := omega) only [Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h11)
        (by simp (disch := omega) only [Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h13)
        (by simp (disch := omega) only [Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h14)
        (by simp (disch := omega) only [Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h1817)
        (by simp (disch := omega) only [Ext.app' e4, Ext.app' e3, Ext.app' e2]; exact p1)
        (by rw [← hk1]; exact (show selVal.getD 1 0 = 1893 by decide) ▸ p4.2.1)
        (by simp (disch := omega) only [Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact hcv)
        h0lm hlmp hz hidxc hpI2 hb1 hfpw hcur hpool hcpl hlm32 hA) (by vt_stable) fun σ5 e5 _ =>
    vt_consB (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      ((vt_c_sel' hSel hκ hlow hpl hz hsq (by norm_num : 2 < 65) (hm 2 (by norm_num)) (by decide) (by decide)
        (by simp (disch := omega) only [Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h5)
        (by simp (disch := omega) only [Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h6)
        (by simp (disch := omega) only [Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h9)
        (by simp (disch := omega) only [Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h10)
        (by simp (disch := omega) only [Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h128)).toRelB freeOn_vtFree (by decide +kernel))
      (stS 2 1997 (by decide)) fun σ6 e6 p6 =>
    (hG3 rd σ6 fpw zeta idxc pbim pI3 point
      (by simp (disch := omega) only [Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h5)
      (by simp (disch := omega) only [Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h11)
      (by simp (disch := omega) only [Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h1817)
      (by simp (disch := omega) only [Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2]; exact p1)
      (by rw [← hk2]; exact (show selVal.getD 2 0 = 1997 by decide) ▸ p6.2.1) h18p hz hidxc hpI3 hb2 hfpw).toRelB freeOn_vtFree (by decide +kernel)).mono le_rfl le_rfl ?_
  rintro σ' ⟨q1, q2, -, q4, ⟨q25, q37, q55, q73, q86⟩, q6, q29⟩
  refine ⟨q1, fun i hi => ?_, q25, q37, q55, q73, q86, q29⟩
  interval_cases i
  · exact q2
  · exact q4
  · exact q6

end

section
variable {rd : Reader}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **Statements `1808 ..< 4273` over a completeness model** (`vt_phaseB2`): the selectors `3 ..< 37` with the pure windows after them,
the push side's padding and the pull side, the selectors `37 ..< 65` with theirs. -/
theorem vt_phaseB2C {CM : CompModel} (hSel : VtSelComplete) {κ : ℕ} (hκ : 6 ≤ κ) (hlow : LowDef κ rd)
    {σ : Val} {cur zeta bk sq fpw pool cplen offP pbim mF bF : E} {point : List E} {cv : Digest}
    {ks off : ℕ → ℕ} {ptr : ℕ → E}
    (h2 : σ (.n 2) = cur) (h5 : σ (.n 5) = zeta) (h6 : σ (.n 6) = gen ^ point.length) (h9 : σ (.n 9) = bk)
    (h10 : σ (.n 10) = sq) (h11 : σ (.n 11) = fpw) (h13 : σ (.n 13) = pool) (h14 : σ (.n 14) = cplen)
    (h128 : σ (.n 128) = offP) (h1852 : σ (.n 1852) = pbim)
    (hcv : (σ (.n 1986), σ (.n 1987)) = digestScalars cv)
    (hpl : point.length < 33) (hz : ReadsAt rd zeta point) (hsq : ∀ j < 34, LoadHolds rd sq j (gen ^ 2 ^ j))
    (hm : ∀ i < 65, SelMem rd bk offP point ks off ptr i)
    (hbk : ∀ b < 102, LoadHolds rd bk b (gen ^ ks b)) (hks : ∀ b < 102, ks b < 34)
    (hfpw : ∀ i < 16, ∃ v, LoadHolds rd fpw i v) (hc3 : LoadHolds rd cur 3 mF) (hc4 : LoadHolds rd cur 4 bF)
    (hp3 : ∀ j < 3, ∃ v, LoadHolds rd pool j v) (hpm : LoadHolds rd pool 3 mF) (hpb : LoadHolds rd pool 4 bF)
    (hl3 : LoadHolds rd cplen 3 (gen ^ ks 38)) (hl4 : LoadHolds rd cplen 4 (gen ^ ks 39))
    (hb1 : ∃ v, LoadHolds rd pbim 1 v) (hb2 : ∃ v, LoadHolds rd pbim 2 v)
    (hA : ObsAns CM.hm cv [mF, bF]) :
    CompletesB CM.sem (coreProgram.RelB CM.sem rd) rd 2077 4554
      ((vtPre.drop 1808).take ((2798 - 1808) + (28 + (571 + ((4206 - 3397) + (28 + (4273 - 4234))))))) σ
      (fun σ' => (∀ j < 33, SelPost point ks off ptr (3 + j) σ') ∧ SelPost point ks off ptr 36 σ' ∧
        σ' (.n 3359) = mF ∧ σ' (.n 3409) = bF ∧
        (σ' (.n 3422), σ' (.n 3423)) = digestScalars (obsCvT CM.hm (obsCvT CM.hm cv mF) bF) ∧
        (∀ j < 27, SelPost point ks off ptr (37 + j) σ') ∧ SelPost point ks off ptr 64 σ') := by
  have stS : ∀ i lo, selVal.getD i 0 = lo → ∀ σ1 σ2 : Val, (∀ k < lo + 27, σ2 (.n k) = σ1 (.n k)) →
      SelPost point ks off ptr i σ1 → SelPost point ks off ptr i σ2 := fun i lo hlo σ1 σ2 hag hp => by
    subst hlo; unfold SelPost at hp ⊢; simp +contextual (disch := omega) only [hag]; exact hp
  have stR : ∀ i0 d lo, (∀ j < d, selVal.getD (i0 + j) 0 + 27 ≤ lo) → ∀ σ1 σ2 : Val,
      (∀ k < lo, σ2 (.n k) = σ1 (.n k)) → (∀ j < d, SelPost point ks off ptr (i0 + j) σ1) →
      ∀ j < d, SelPost point ks off ptr (i0 + j) σ2 := fun i0 d lo hb σ1 σ2 hag hp j hj => by
    have hb' := hb j hj
    have := hp j hj
    unfold SelPost at this ⊢; simp +contextual (disch := omega) only [hag]; exact this
  refine (vt_consB (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
    ((vt_sel_run' hSel hκ hlow hpl hz hsq hm 33 3 (by decide +kernel) (by norm_num) (by decide) (by decide)
      (by decide) (by decide) h5 h6 h9 h10 h128).toRelB freeOn_vtFree (by decide +kernel))
    (stR 3 33 3034 (by decide)) fun σ1 e1 _ =>
    vt_consB (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      ((vt_c_sel' hSel hκ hlow hpl hz hsq (by norm_num : 36 < 65) (hm 36 (by norm_num)) (by decide) (by decide)
        (by rw [Ext.app' e1 5 (by norm_num), h5]) (by rw [Ext.app' e1 6 (by norm_num), h6])
        (by rw [Ext.app' e1 9 (by norm_num), h9]) (by rw [Ext.app' e1 10 (by norm_num), h10])
        (by rw [Ext.app' e1 128 (by norm_num), h128])).toRelB freeOn_vtFree (by decide +kernel)) (stS 36 3034 (by decide)) fun σ2 e2 _ =>
    vt_consB (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      (vt_glue4C (CM := CM) κ hκ rd hlow σ2 cur bk fpw pool cplen pbim mF bF ks cv
        (by simp (disch := omega) only [Ext.app' e2, Ext.app' e1]; exact h2)
        (by simp (disch := omega) only [Ext.app' e2, Ext.app' e1]; exact h9)
        (by simp (disch := omega) only [Ext.app' e2, Ext.app' e1]; exact h11)
        (by simp (disch := omega) only [Ext.app' e2, Ext.app' e1]; exact h13)
        (by simp (disch := omega) only [Ext.app' e2, Ext.app' e1]; exact h14)
        (by simp (disch := omega) only [Ext.app' e2, Ext.app' e1]; exact h1852)
        (by simp (disch := omega) only [Ext.app' e2, Ext.app' e1]; exact hcv)
        hbk hks hfpw hc3 hc4 hp3 hpm hpb hl3 hl4 hb1 hb2 hA) (by vt_stable) fun σ3 e3 _ =>
    vt_consB (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      ((vt_sel_run' hSel hκ hlow hpl hz hsq hm 27 37 (by decide +kernel) (by norm_num) (by decide) (by decide)
        (by decide) (by decide)
        (by simp (disch := omega) only [Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h5)
        (by simp (disch := omega) only [Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h6)
        (by simp (disch := omega) only [Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h9)
        (by simp (disch := omega) only [Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h10)
        (by simp (disch := omega) only [Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h128)).toRelB freeOn_vtFree (by decide +kernel))
      (stR 37 27 4488 (by decide)) fun σ4 e4 _ =>
    vt_consB (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      ((vt_c_sel' hSel hκ hlow hpl hz hsq (by norm_num : 64 < 65) (hm 64 (by norm_num)) (by decide) (by decide)
        (by simp (disch := omega) only [Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h5)
        (by simp (disch := omega) only [Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h6)
        (by simp (disch := omega) only [Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h9)
        (by simp (disch := omega) only [Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h10)
        (by simp (disch := omega) only [Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h128)).toRelB freeOn_vtFree (by decide +kernel))
      (stS 64 4488 (by decide)) fun σ5 _ _ =>
    ((vt_c_gap (by decide +kernel) σ5).toRelB freeOn_vtFree (by decide +kernel))).mono le_rfl le_rfl ?_
  rintro σ' ⟨q1, q2, ⟨q59, q09, q22⟩, q3, q4, -⟩
  exact ⟨q1, q2, q59, q09, q22, q3, q4⟩

end

section
variable {rd : Reader}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- **Statements `0 ..< 4273` over a completeness model** (`vt_pre4273`): the prelude, the block order, the padding weights, `idxc_tab`, the
selectors and the bus's sums and reads. -/
theorem vt_pre4273C {CM : CompModel} {κ : ℕ} (hκ : 7 ≤ κ) (hlow : LowDef κ rd) {σ : Val}
    {cur zeta bk sq fpw pool cplen dims rowsP bv mF bF m0 m1 m2 : E} {point : List E} {logMem : ℕ}
    {rowsN : List ℕ} {cv : Digest} {ptr : ℕ → E}
    (hcv : (σ (.n 0), σ (.n 1)) = digestScalars cv) (h2 : σ (.n 2) = cur) (h5 : σ (.n 5) = zeta)
    (h6 : σ (.n 6) = gen ^ point.length) (h7 : σ (.n 7) = dims) (h8 : σ (.n 8) = rowsP)
    (h9 : σ (.n 9) = bk) (h10 : σ (.n 10) = sq) (h11 : σ (.n 11) = fpw) (h13 : σ (.n 13) = pool)
    (h14 : σ (.n 14) = cplen)
    (hrl : rowsN.length = 6) (hτ : ∀ t < 6, log2Ceil (rowsN.getD t 0) < 29)
    (hτp : ∀ t < 6, log2Ceil (rowsN.getD t 0) ≤ point.length) (h16 : 16 ≤ logMem) (h32 : logMem ≤ 32)
    (hlmp : logMem ≤ point.length) (h18p : 18 ≤ point.length) (hpl : point.length < 33)
    (hso1 : ∀ r < 37, LoadHolds rd (ptr 0) r
      (gen ^ (stackOrder ((List.range 37).map (vtKs logMem (fun t => log2Ceil (rowsN.getD t 0))))).getD r 0))
    (hso2 : ∀ r < 28, LoadHolds rd (ptr 0) (74 + r)
      (gen ^ (74 + (stackOrder ((List.range 28).map fun i =>
        vtKs logMem (fun t => log2Ceil (rowsN.getD t 0)) (74 + i))).getD r 0)))
    (hside : ∀ b < 102, LoadHolds rd (ptr 1) b (word (vtBlockSide b) 0 0))
    (hbk : ∀ b < 102, LoadHolds rd bk b (gen ^ vtKs logMem (fun t => log2Ceil (rowsN.getD t 0)) b))
    (hsq : ∀ j < 34, LoadHolds rd sq j (gen ^ 2 ^ j))
    (hoff1 : ∀ i < 37, LoadHolds rd (ptr 2) i (gen ^ (stackOffsets ((List.range 37).map
      (vtKs logMem fun t => log2Ceil (rowsN.getD t 0)))).1.getD i 0))
    (hoff2 : ∀ i < 28, LoadHolds rd (ptr 2) (74 + i) (gen ^ (stackOffsets ((List.range 28).map fun i =>
      vtKs logMem (fun t => log2Ceil (rowsN.getD t 0)) (74 + i))).1.getD i 0))
    (hdims : ReadsAt rd dims (gen ^ logMem :: rowsN.map fun n ↦ gen ^ log2Ceil n))
    (hrows : ReadsAt rd rowsP (rowsN.map eOfNat)) (hz : ReadsAt rd zeta point)
    (hidx : ∀ t < 34, LoadHolds rd (ptr 3) t (1 + gen ^ 2 ^ t))
    (hm : ∀ i < 65, SelMem rd bk (ptr 2) point (vtKs logMem fun t => log2Ceil (rowsN.getD t 0))
      (selOff (vtKs logMem fun t => log2Ceil (rowsN.getD t 0))) ptr i)
    (hfpw : ∀ i < 16, ∃ v, LoadHolds rd fpw i v)
    (hpI2 : ReadsAt rd (ptr 11) (idxChainW point logMem))
    (hb1 : LoadHolds rd (ptr 4) 1 ((idxChainW point logMem).getD logMem 0))
    (hpI3 : ReadsAt rd (ptr 15) (idxChainW point 18)) (hb2 : LoadHolds rd (ptr 4) 2 ((idxChainW point 18).getD 18 0))
    (hcur : ReadsAt rd cur [m0, m1, m2, mF, bF]) (hpool : ReadsAt rd pool [m0, m1, m2, mF, bF])
    (hcpl : ∀ j < 4, LoadHolds rd cplen j (gen ^ logMem)) (hcpl4 : LoadHolds rd cplen 4 (gen ^ 18))
    (hA : ObsAns CM.hm cv [m0, m1, m2, mF, bF]) :
    CompletesB CM.sem (coreProgram.RelB CM.sem rd) rd 19 4554
      ((vtPre.drop 0).take ((213 + (1225 + (67 + 69))) + ((3 + (28 + (11 + (28 + (80 + (28 + 56)))))) +
        ((2798 - 1808) + (28 + (571 + ((4206 - 3397) + (28 + (4273 - 4234))))))))) σ (fun σ' =>
      σ' (.n 19) = σ (.n 0) ∧ σ' (.n 20) = σ (.n 1) ∧ σ' (.n 21) = σ (.n 16) ∧
        σ' (.n 22) = σ (.n 17) ∧ σ' (.n 23) = σ (.n 18) ∧ σ' (.n 24) = ptr 0 ∧ σ' (.n 25) = ptr 1 ∧
        σ' (.n 128) = ptr 2 ∧ σ' (.n 1732) = bv ∧
        (∀ t < 6, σ' (.n (1739 + 14 * t)) =
          paddingWeight (point.take (log2Ceil (rowsN.getD t 0))) (rowsN.getD t 0)) ∧
        σ' (.n 1817) = ptr 3 ∧ σ' (.n 1852) = ptr 4 ∧ σ' (.n 1925) = ptr 11 ∧ σ' (.n 2029) = ptr 15 ∧
        (∀ i < 65, SelPost point (vtKs logMem fun t => log2Ceil (rowsN.getD t 0))
          (selOff (vtKs logMem fun t => log2Ceil (rowsN.getD t 0))) ptr i σ') ∧
        σ' (.n 1937) = m0 ∧ σ' (.n 1955) = m1 ∧ σ' (.n 1973) = m2 ∧ σ' (.n 3359) = mF ∧
        σ' (.n 3409) = bF ∧
        (σ' (.n 3422), σ' (.n 3423)) = digestScalars (obsCvT CM.hm (obsCvT CM.hm (obsAllT CM.hm cv [m0, m1, m2]) mF) bF)) := by
  have hk1 : vtKs logMem (fun t => log2Ceil (rowsN.getD t 0)) (selBlk.getD 1 0) = logMem := by
    simp [vtKs, blockKappaSrc, blockKappaAdj, selBlk]
  have hk2 : vtKs logMem (fun t => log2Ceil (rowsN.getD t 0)) (selBlk.getD 2 0) = 18 := by
    simp [vtKs, blockKappaSrc, blockKappaAdj, selBlk]
  have k38 : vtKs logMem (fun t => log2Ceil (rowsN.getD t 0)) 38 = logMem := by
    simp [vtKs, blockKappaSrc, blockKappaAdj]
  have k39 : vtKs logMem (fun t => log2Ceil (rowsN.getD t 0)) 39 = 18 := by
    simp [vtKs, blockKappaSrc, blockKappaAdj]
  have hks := vtKs_lt h32 hτ
  have hcur3 : ReadsAt rd cur [m0, m1, m2] := fun k hk => by
    have hk' : k < 3 := by simpa using hk
    have := hcur k (by simp; omega)
    interval_cases k <;> exact this
  have hpool3 : ReadsAt rd pool [m0, m1, m2] := fun k hk => by
    have hk' : k < 3 := by simpa using hk
    have := hpool k (by simp; omega)
    interval_cases k <;> exact this
  refine (vt_consB (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
    ((vt_phaseA vt_sort_complete hκ hlow (bv := bv) hks h5 h7 h8 h9 h10 hso1 hso2 hside hbk hsq hoff1 hoff2
      hdims hrows hz hrl hτ hτp hidx).toRelB freeOn_vtFree (by decide +kernel))
    (by vt_stable) fun σ1 e1 p1 =>
    vt_consB (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      (vt_phaseB1C (CM := CM) vt_sel_complete vt_glue1 vt_glue3 (by omega) hlow (σ := σ1) (cv := cv)
        (by rw [Ext.app' e1 2 (by norm_num), h2]) (by rw [Ext.app' e1 5 (by norm_num), h5])
        (by rw [Ext.app' e1 6 (by norm_num), h6]) (by rw [Ext.app' e1 9 (by norm_num), h9])
        (by rw [Ext.app' e1 10 (by norm_num), h10]) (by rw [Ext.app' e1 11 (by norm_num), h11])
        (by rw [Ext.app' e1 13 (by norm_num), h13]) (by rw [Ext.app' e1 14 (by norm_num), h14])
        (by rw [p1.1, p1.2.1, hcv]) p1.2.2.2.2.2.2.2.1 p1.2.2.2.2.2.2.2.2.2.2
        hpl hz hsq hm hfpw hidx hk1 hk2 (by omega) hlmp h32 h18p hpI2 hb1 hpI3 hb2 hcur3 hpool3
        (fun j hj => hcpl j (by omega)) (obsAns_left (xs := [m0, m1, m2]) (ys := [mF, bF]) hA))
      (fun σ1 σ2 hag hp => by
        obtain ⟨q1, q2, q3⟩ := hp
        refine ⟨by rw [hag _ (by norm_num), q1], fun i hi => selPost_stable (m := 2077)
          (by interval_cases i <;> decide) hag (q2 i hi), ?_⟩
        simp only [hag _ (by norm_num : 1925 < 2077), hag _ (by norm_num : 1937 < 2077),
          hag _ (by norm_num : 1955 < 2077), hag _ (by norm_num : 1973 < 2077),
          hag _ (by norm_num : 1986 < 2077), hag _ (by norm_num : 1987 < 2077),
          hag _ (by norm_num : 2029 < 2077)]
        exact q3) fun σ2 e2 p2 =>
    vt_phaseB2C (CM := CM) vt_sel_complete (by omega) hlow (σ := σ2) (cv := obsAllT CM.hm cv [m0, m1, m2])
      (by simp (disch := omega) only [Ext.app' e2, Ext.app' e1]; exact h2)
      (by simp (disch := omega) only [Ext.app' e2, Ext.app' e1]; exact h5)
      (by simp (disch := omega) only [Ext.app' e2, Ext.app' e1]; exact h6)
      (by simp (disch := omega) only [Ext.app' e2, Ext.app' e1]; exact h9)
      (by simp (disch := omega) only [Ext.app' e2, Ext.app' e1]; exact h10)
      (by simp (disch := omega) only [Ext.app' e2, Ext.app' e1]; exact h11)
      (by simp (disch := omega) only [Ext.app' e2, Ext.app' e1]; exact h13)
      (by simp (disch := omega) only [Ext.app' e2, Ext.app' e1]; exact h14)
      (by simp (disch := omega) only [Ext.app' e2]; exact p1.2.2.2.2.2.2.2.1)
      p2.1 p2.2.2.2.2.2.2.1 hpl hz hsq hm hbk hks hfpw (hcur 3 (by norm_num)) (hcur 4 (by norm_num))
      (fun j hj => ⟨_, hpool j (by simp; omega)⟩) (hpool 3 (by norm_num)) (hpool 4 (by norm_num))
      (by rw [k38]; exact hcpl 3 (by norm_num)) (by rw [k39]; exact hcpl4) ⟨_, hb1⟩ ⟨_, hb2⟩
      (obsAns_right (xs := [m0, m1, m2]) (ys := [mF, bF]) hA)).mono
    le_rfl le_rfl ?_
  rintro σ' ⟨⟨c19, c20, c21, c22, c23, q24, q25, q128, b0, hpw, q1817⟩, ⟨q1852, s3, q25', q37, q55, q73, -, q29⟩,
    r1, r36, q59, q09, q22, r2, r64⟩
  refine ⟨c19, c20, c21, c22, c23, q24, q25, q128, b0, fun t ht => (hpw t ht).2, q1817, q1852, q25', q29,
    fun i hi => ?_, q37, q55, q73, q59, q09, q22⟩
  by_cases a3 : i < 3
  · exact s3 i a3
  by_cases a36 : i < 36
  · simpa [show 3 + (i - 3) = i by omega] using r1 (i - 3) (by omega)
  by_cases a37 : i < 37
  · obtain rfl : i = 36 := by omega
    exact r36
  by_cases a64 : i < 64
  · simpa [show 37 + (i - 37) = i by omega] using r2 (i - 37) (by omega)
  · obtain rfl : i = 64 := by omega
    exact r64

end

/-! ## The evaluations -/

/-- The state before evaluation `j`, at a hash model's total hash (`cvE`). -/
def cvET (M : HashModel) (cv0 : Digest) (ws : ℕ → E) (j : ℕ) : Digest :=
  obsAllT M cv0 ((List.range j).map ws)

theorem cvET_succ (M : HashModel) (cv0 : Digest) (ws : ℕ → E) (j : ℕ) :
    cvET M cv0 ws (j + 1) = obsCvT M (cvET M cv0 ws j) (ws j) := by
  rw [cvET, cvET, List.range_succ, List.map_append, List.map_cons, List.map_nil, obsAllT_append]
  rfl

section
variable {rd : Reader}

/-- **A run of one table's evaluations over a completeness model** (`vt_ev_run`), from evaluation
`j0`, its `g^τ` at `evTau j0`. -/
theorem vt_ev_runC {CM : CompModel} {cur pool cplen g : E} {ws : ℕ → E} {cv0 : Digest}
    (hmem : ∀ j < 104, LoadHolds rd cur j (ws j) ∧ LoadHolds rd pool (5 + j) (ws j))
    (hans : ∀ j < 104, obsCvM CM.hm (cvET CM.hm cv0 ws j) (ws j) =
      some (obsCvT CM.hm (cvET CM.hm cv0 ws j) (ws j))) :
    ∀ (d j0 : ℕ), j0 + d ≤ 104 → (∀ j < d, evStmt.getD (j0 + j) 0 = evStmt.getD j0 0 + 16 * j ∧
      evVal.getD (j0 + j) 0 = evVal.getD j0 0 + 16 * j ∧ evTau.getD (j0 + j) 0 = evTau.getD j0 0) →
    (∀ j < d, LoadHolds rd cplen (5 + (j0 + j)) g) →
    ∀ σ : Val, σ (.n 4651) = cur → σ (.n 13) = pool → σ (.n 14) = cplen → σ (.n (evTau.getD j0 0)) = g →
      (σ (.n (evSt j0)), σ (.n (evSt j0 + 1))) = digestScalars (cvET CM.hm cv0 ws j0) →
      CompletesB CM.sem (coreProgram.RelB CM.sem rd) rd (evVal.getD j0 0) (evVal.getD j0 0 + 16 * d)
        ((vtPre.drop (evStmt.getD j0 0)).take (16 * d)) σ (fun σ' =>
          (∀ j < d, σ' (.n (evVal.getD (j0 + j) 0)) = ws (j0 + j)) ∧
            (0 < d → (σ' (.n (evVal.getD (j0 + d - 1) 0 + 13)), σ' (.n (evVal.getD (j0 + d - 1) 0 + 14))) =
              digestScalars (cvET CM.hm cv0 ws (j0 + d))))
  | 0, j0, _, _, _, σ, _, _, _, _, _ => by
    simp only [Nat.mul_zero, Nat.add_zero, List.take_zero]
    exact CompletesB.nil _ _ σ ⟨fun j hj => absurd hj (Nat.not_lt_zero j), fun h => absurd h (Nat.lt_irrefl 0)⟩
  | d + 1, j0, hjd, hcon, hcpl, σ, h4651, h13, h14, htau, hst => by
    have hj0 : j0 < 104 := by omega
    obtain ⟨ht0, -, hst0, hc0⟩ := ev_tau_lt j0 hj0
    have hc1 := hcon 1
    have hs : ∀ j < d, evStmt.getD (j0 + 1 + j) 0 = evStmt.getD (j0 + 1) 0 + 16 * j ∧
        evVal.getD (j0 + 1 + j) 0 = evVal.getD (j0 + 1) 0 + 16 * j ∧
        evTau.getD (j0 + 1 + j) 0 = evTau.getD (j0 + 1) 0 := fun j hj => by
      obtain ⟨a1, b1, c1⟩ := hcon 1 (by omega)
      obtain ⟨a2, b2, c2⟩ := hcon (1 + j) (by omega)
      rw [show j0 + 1 + j = j0 + (1 + j) by omega, a2, b2, c2, a1, b1, c1]
      exact ⟨by omega, by omega, rfl⟩
    have hunit : CompletesB CM.sem (coreProgram.RelB CM.sem rd) rd (evVal.getD j0 0) (evVal.getD j0 0 + 16)
        ((vtPre.drop (evStmt.getD j0 0)).take 16) σ (fun σ' =>
          σ' (.n (evVal.getD j0 0)) = ws j0 ∧ σ' (.n (evVal.getD j0 0 + 15)) = ws j0 ∧
            (σ' (.n (evVal.getD j0 0 + 13)), σ' (.n (evVal.getD j0 0 + 14))) =
              digestScalars (obsCvT CM.hm (cvET CM.hm cv0 ws j0) (ws j0))) :=
      vt_ev_completeC j0 hj0 rd σ cur pool cplen (ws j0) g (cvET CM.hm cv0 ws j0) h4651 h13 h14 htau hst
        (hmem j0 hj0).1 (hmem j0 hj0).2 (by simpa using hcpl 0 (by omega)) (hans j0 hj0)
    have IH := vt_ev_runC (CM := CM) (cplen := cplen) (g := g) (cv0 := cv0) hmem hans d (j0 + 1)
    rcases d with _ | d
    · rw [show 16 * (0 + 1) = 16 from rfl]
      refine hunit.mono le_rfl le_rfl fun σ' q => ⟨fun j hj => ?_, fun _ => ?_⟩
      · obtain rfl : j = 0 := by omega
        simpa using q.1
      · simpa [cvET_succ] using q.2.2
    obtain ⟨a1, b1, c1⟩ := hc1 (by omega)
    simp only [Nat.mul_one] at a1 b1
    rw [show 16 * (d + 1 + 1) = 16 + 16 * (d + 1) by ring]
    refine (vt_consB (Q := fun σ'' => (∀ j < d + 1, σ'' (.n (evVal.getD (j0 + 1 + j) 0)) = ws (j0 + 1 + j)) ∧
        (0 < d + 1 → (σ'' (.n (evVal.getD (j0 + 1 + (d + 1) - 1) 0 + 13)),
          σ'' (.n (evVal.getD (j0 + 1 + (d + 1) - 1) 0 + 14))) = digestScalars (cvET CM.hm cv0 ws (j0 + 1 + (d + 1)))))
      (by omega) (by omega) (numBelow_of_B (ev_nb j0 hj0)) hunit
      (fun σ1 σ2 hag hp => by simp +contextual (disch := omega) only [hag]; exact hp)
      fun σ' e p => ?_).mono le_rfl le_rfl ?_
    · rw [← a1, ← b1]
      have hr := IH (by omega) hs
        (fun j hj => by rw [show j0 + 1 + j = j0 + (j + 1) by omega]; exact hcpl (j + 1) (by omega)) σ'
        (by rw [Ext.app' e _ (by omega), h4651]) (by rw [Ext.app' e _ (by omega), h13])
        (by rw [Ext.app' e _ (by omega), h14])
        (by rw [c1, Ext.app' e _ (by omega), htau])
        (by
          simp only [evSt, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, cvET_succ]
          rw [show evVal.getD j0 0 + 13 + 1 = evVal.getD j0 0 + 14 by omega]
          exact p.2.2)
      rw [show evVal.getD (j0 + 1) 0 + 16 * (d + 1) = evVal.getD j0 0 + (16 + 16 * (d + 1)) by omega] at hr
      exact hr
    · rintro σ'' ⟨⟨q0, -⟩, qr, qs⟩
      refine ⟨fun j hj => ?_, fun _ => ?_⟩
      · rcases j with _ | j
        · simpa using q0
        · rw [show j0 + (j + 1) = j0 + 1 + j by omega]; exact qr j (by omega)
      · rw [show j0 + (d + 1 + 1) - 1 = j0 + 1 + (d + 1) - 1 by omega,
          show j0 + (d + 1 + 1) = j0 + 1 + (d + 1) by omega]
        exact qs (by omega)
/-- `vt_ev_runC` at literal positions (`vt_ev_run'`). -/
theorem vt_ev_runC' {CM : CompModel} {cur pool cplen g : E} {ws : ℕ → E} {cv0 : Digest}
    (hmem : ∀ j < 104, LoadHolds rd cur j (ws j) ∧ LoadHolds rd pool (5 + j) (ws j))
    (hans : ∀ j < 104, obsCvM CM.hm (cvET CM.hm cv0 ws j) (ws j) =
      some (obsCvT CM.hm (cvET CM.hm cv0 ws j) (ws j))) (d j0 : ℕ) (hd : 0 < d)
    (hjd : j0 + d ≤ 104) (hcon : ∀ j < d, evStmt.getD (j0 + j) 0 = evStmt.getD j0 0 + 16 * j ∧
      evVal.getD (j0 + j) 0 = evVal.getD j0 0 + 16 * j ∧ evTau.getD (j0 + j) 0 = evTau.getD j0 0)
    (hcpl : ∀ j < d, LoadHolds rd cplen (5 + (j0 + j)) g) {lo st s so tv : ℕ} (hlo : evVal.getD j0 0 = lo)
    (hst : evStmt.getD j0 0 = st) (hs : evSt j0 = s) (hso : evVal.getD (j0 + d - 1) 0 + 13 = so)
    (htv : evTau.getD j0 0 = tv) {σ : Val} (h4651 : σ (.n 4651) = cur) (h13 : σ (.n 13) = pool)
    (h14 : σ (.n 14) = cplen) (htau : σ (.n tv) = g)
    (hcv : (σ (.n s), σ (.n (s + 1))) = digestScalars (cvET CM.hm cv0 ws j0)) :
    CompletesB CM.sem (coreProgram.RelB CM.sem rd) rd lo (lo + 16 * d) ((vtPre.drop st).take (16 * d)) σ (fun σ' =>
      (∀ j < d, σ' (.n (lo + 16 * j)) = ws (j0 + j)) ∧
        (σ' (.n so), σ' (.n (so + 1))) = digestScalars (cvET CM.hm cv0 ws (j0 + d))) := by
  subst hlo hst hs hso htv
  refine (vt_ev_runC hmem hans d j0 hjd hcon hcpl σ h4651 h13 h14 htau hcv).mono le_rfl le_rfl
    fun σ' ⟨q1, q2⟩ => ⟨fun j hj => by rw [← (hcon j hj).2.1]; exact q1 j hj, ?_⟩
  rw [show evVal.getD (j0 + d - 1) 0 + 13 + 1 = evVal.getD (j0 + d - 1) 0 + 14 by omega]
  exact q2 hd


set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- **Statements `4374 ..< 7854` over a completeness model** (`vt_phaseD`): the first table's `g^τ`, then per table its evaluations and its
constraint window, which reads the next table's `g^τ`. -/
theorem vt_phaseDC {CM : CompModel} (hAir : VtAirComplete) {σ : Val}
    {cur pool cplen fpw dims pC pP : E} {n : ℕ} {τ : ℕ → ℕ} {ws : ℕ → E} {cv0 : Digest}
    (h7 : σ (.n 7) = dims) (h11 : σ (.n 11) = fpw) (h13 : σ (.n 13) = pool) (h14 : σ (.n 14) = cplen)
    (h4554 : σ (.n 4554) = gen ^ n) (h4639 : σ (.n 4639) = pC) (h4655 : σ (.n 4655) = pP)
    (h4651 : σ (.n 4651) = cur) (hcv0 : (σ (.n 4649), σ (.n (4649 + 1))) = digestScalars (cvET CM.hm cv0 ws 0))
    (hdims : ∀ t < 6, LoadHolds rd dims (t + 1) (gen ^ τ t)) (hτn : ∀ t < 6, τ t ≤ n)
    (hfpw : ∀ i < 16, ∃ v, LoadHolds rd fpw i v) (hpC : ∀ t < 6, ∃ v, LoadHolds rd pC (n - τ t) v)
    (hpP : ∀ t < 6, ∃ v, LoadHolds rd pP (τ t) v)
    (hmem : ∀ j < 104, LoadHolds rd cur j (ws j) ∧ LoadHolds rd pool (5 + j) (ws j))
    (hcpl : ∀ t < 6, ∀ j < evCnt.getD t 0, LoadHolds rd cplen (5 + (evFirst.getD t 0 + j)) (gen ^ τ t))
    (hans : ∀ j < 104, obsCvM CM.hm (cvET CM.hm cv0 ws j) (ws j) =
      some (obsCvT CM.hm (cvET CM.hm cv0 ws j) (ws j))) :
    CompletesB CM.sem (coreProgram.RelB CM.sem rd) rd 4660 8140
      ((vtPre.drop 4374).take (1 + (16 * 15 + ((4863 - 4615) + (16 * 15 + ((5392 - 5103) + (16 * 8 + ((5669 - 5520) + (16 * 15 + ((6192 - 5909) + (16 * 14 + ((6694 - 6416) + (16 * 37 + ((7854 - 7286))))))))))))))) σ (fun σ' =>
        (∀ j < 104, σ' (.n (evVal.getD j 0)) = ws j) ∧
          (σ' (.n 7569), σ' (.n (7569 + 1))) = digestScalars (cvET CM.hm cv0 ws 104)) := by
  refine (vt_consB (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
    ((vt_c_tau h7 (hdims 0 (by norm_num))).toRelB freeOn_vtFree (by decide +kernel)) (by vt_stable) fun σ1 e1 p1 =>
    vt_consB (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      (vt_ev_runC' (CM := CM) hmem hans 15 0 (by norm_num) (by norm_num) (by decide +kernel)
        (fun j hj => hcpl 0 (by norm_num) j hj) (lo := 4661) (st := 4375) (s := 4649) (so := 4898) (tv := 4660)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by simp (disch := omega) only [Ext.app' e1]; exact h4651) (by simp (disch := omega) only [Ext.app' e1]; exact h13) (by simp (disch := omega) only [Ext.app' e1]; exact h14)
        p1
        (by simp (disch := omega) only [Ext.app' e1]; exact hcv0))
      (by vt_stable) fun σ2 e2 p2 =>
    vt_consB (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      ((vt_air' hAir 0 (by norm_num) (lo := 4901) (hi := 5149) (a := 4615) (b := 4863) (tv := 4660)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (tvn := 5148) (τn := τ 1) (by decide) (by simp (disch := omega) only [Ext.app' e2, Ext.app' e1]; exact h11) (by simp (disch := omega) only [Ext.app' e2, Ext.app' e1]; exact h7) (by simp (disch := omega) only [Ext.app' e2, Ext.app' e1]; exact h4639) (by simp (disch := omega) only [Ext.app' e2, Ext.app' e1]; exact h4655) (by simp (disch := omega) only [Ext.app' e2, Ext.app' e1]; exact h4554)
        (by simp (disch := omega) only [Ext.app' e2, Ext.app' e1]; exact p1) (hτn 0 (by norm_num)) hfpw (hpC 0 (by norm_num)) (hpP 0 (by norm_num)) (fun h => hdims 1 (by norm_num))).toRelB freeOn_vtFree (by decide +kernel))
      (by vt_stable) fun σ3 e3 p3 =>
    vt_consB (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      (vt_ev_runC' (CM := CM) hmem hans 15 15 (by norm_num) (by norm_num) (by decide +kernel)
        (fun j hj => hcpl 1 (by norm_num) j hj) (lo := 5149) (st := 4863) (s := 4898) (so := 5386) (tv := 5148)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by simp (disch := omega) only [Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h4651) (by simp (disch := omega) only [Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h13) (by simp (disch := omega) only [Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h14)
        (p3 (by norm_num))
        (by simp (disch := omega) only [Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact (p2.2)))
      (by vt_stable) fun σ4 e4 p4 =>
    vt_consB (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      ((vt_air' hAir 1 (by norm_num) (lo := 5389) (hi := 5678) (a := 5103) (b := 5392) (tv := 5148)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (tvn := 5677) (τn := τ 2) (by decide) (by simp (disch := omega) only [Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h11) (by simp (disch := omega) only [Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h7) (by simp (disch := omega) only [Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h4639) (by simp (disch := omega) only [Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h4655) (by simp (disch := omega) only [Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h4554)
        (by simp (disch := omega) only [Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact (p3 (by norm_num))) (hτn 1 (by norm_num)) hfpw (hpC 1 (by norm_num)) (hpP 1 (by norm_num)) (fun h => hdims 2 (by norm_num))).toRelB freeOn_vtFree (by decide +kernel))
      (by vt_stable) fun σ5 e5 p5 =>
    vt_consB (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      (vt_ev_runC' (CM := CM) hmem hans 8 30 (by norm_num) (by norm_num) (by decide +kernel)
        (fun j hj => hcpl 2 (by norm_num) j hj) (lo := 5678) (st := 5392) (s := 5386) (so := 5803) (tv := 5677)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by simp (disch := omega) only [Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h4651) (by simp (disch := omega) only [Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h13) (by simp (disch := omega) only [Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h14)
        (p5 (by norm_num))
        (by simp (disch := omega) only [Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact (p4.2)))
      (by vt_stable) fun σ6 e6 p6 =>
    vt_consB (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      ((vt_air' hAir 2 (by norm_num) (lo := 5806) (hi := 5955) (a := 5520) (b := 5669) (tv := 5677)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (tvn := 5954) (τn := τ 3) (by decide) (by simp (disch := omega) only [Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h11) (by simp (disch := omega) only [Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h7) (by simp (disch := omega) only [Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h4639) (by simp (disch := omega) only [Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h4655) (by simp (disch := omega) only [Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h4554)
        (by simp (disch := omega) only [Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact (p5 (by norm_num))) (hτn 2 (by norm_num)) hfpw (hpC 2 (by norm_num)) (hpP 2 (by norm_num)) (fun h => hdims 3 (by norm_num))).toRelB freeOn_vtFree (by decide +kernel))
      (by vt_stable) fun σ7 e7 p7 =>
    vt_consB (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      (vt_ev_runC' (CM := CM) hmem hans 15 38 (by norm_num) (by norm_num) (by decide +kernel)
        (fun j hj => hcpl 3 (by norm_num) j hj) (lo := 5955) (st := 5669) (s := 5803) (so := 6192) (tv := 5954)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by simp (disch := omega) only [Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h4651) (by simp (disch := omega) only [Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h13) (by simp (disch := omega) only [Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h14)
        (p7 (by norm_num))
        (by simp (disch := omega) only [Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact (p6.2)))
      (by vt_stable) fun σ8 e8 p8 =>
    vt_consB (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      ((vt_air' hAir 3 (by norm_num) (lo := 6195) (hi := 6478) (a := 5909) (b := 6192) (tv := 5954)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (tvn := 6477) (τn := τ 4) (by decide) (by simp (disch := omega) only [Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h11) (by simp (disch := omega) only [Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h7) (by simp (disch := omega) only [Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h4639) (by simp (disch := omega) only [Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h4655) (by simp (disch := omega) only [Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h4554)
        (by simp (disch := omega) only [Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact (p7 (by norm_num))) (hτn 3 (by norm_num)) hfpw (hpC 3 (by norm_num)) (hpP 3 (by norm_num)) (fun h => hdims 4 (by norm_num))).toRelB freeOn_vtFree (by decide +kernel))
      (by vt_stable) fun σ9 e9 p9 =>
    vt_consB (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      (vt_ev_runC' (CM := CM) hmem hans 14 53 (by norm_num) (by norm_num) (by decide +kernel)
        (fun j hj => hcpl 4 (by norm_num) j hj) (lo := 6478) (st := 6192) (s := 6192) (so := 6699) (tv := 6477)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by simp (disch := omega) only [Ext.app' e9, Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h4651) (by simp (disch := omega) only [Ext.app' e9, Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h13) (by simp (disch := omega) only [Ext.app' e9, Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h14)
        (p9 (by norm_num))
        (by simp (disch := omega) only [Ext.app' e9, Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact (p8.2)))
      (by vt_stable) fun σ10 e10 p10 =>
    vt_consB (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      ((vt_air' hAir 4 (by norm_num) (lo := 6702) (hi := 6980) (a := 6416) (b := 6694) (tv := 6477)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (tvn := 6979) (τn := τ 5) (by decide) (by simp (disch := omega) only [Ext.app' e10, Ext.app' e9, Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h11) (by simp (disch := omega) only [Ext.app' e10, Ext.app' e9, Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h7) (by simp (disch := omega) only [Ext.app' e10, Ext.app' e9, Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h4639) (by simp (disch := omega) only [Ext.app' e10, Ext.app' e9, Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h4655) (by simp (disch := omega) only [Ext.app' e10, Ext.app' e9, Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h4554)
        (by simp (disch := omega) only [Ext.app' e10, Ext.app' e9, Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact (p9 (by norm_num))) (hτn 4 (by norm_num)) hfpw (hpC 4 (by norm_num)) (hpP 4 (by norm_num)) (fun h => hdims 5 (by norm_num))).toRelB freeOn_vtFree (by decide +kernel))
      (by vt_stable) fun σ11 e11 p11 =>
    vt_consB (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      (vt_ev_runC' (CM := CM) hmem hans 37 67 (by norm_num) (by norm_num) (by decide +kernel)
        (fun j hj => hcpl 5 (by norm_num) j hj) (lo := 6980) (st := 6694) (s := 6699) (so := 7569) (tv := 6979)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by simp (disch := omega) only [Ext.app' e11, Ext.app' e10, Ext.app' e9, Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h4651) (by simp (disch := omega) only [Ext.app' e11, Ext.app' e10, Ext.app' e9, Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h13) (by simp (disch := omega) only [Ext.app' e11, Ext.app' e10, Ext.app' e9, Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h14)
        (p11 (by norm_num))
        (by simp (disch := omega) only [Ext.app' e11, Ext.app' e10, Ext.app' e9, Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact (p10.2)))
      (by vt_stable) fun σ12 e12 p12 =>
    ((vt_air' hAir 5 (by norm_num) (lo := 7572) (hi := 8140) (a := 7286) (b := 7854) (tv := 6979)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (tvn := 0) (τn := 0) (by decide) (by simp (disch := omega) only [Ext.app' e12, Ext.app' e11, Ext.app' e10, Ext.app' e9, Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h11) (by simp (disch := omega) only [Ext.app' e12, Ext.app' e11, Ext.app' e10, Ext.app' e9, Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h7) (by simp (disch := omega) only [Ext.app' e12, Ext.app' e11, Ext.app' e10, Ext.app' e9, Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h4639) (by simp (disch := omega) only [Ext.app' e12, Ext.app' e11, Ext.app' e10, Ext.app' e9, Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h4655) (by simp (disch := omega) only [Ext.app' e12, Ext.app' e11, Ext.app' e10, Ext.app' e9, Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h4554)
        (by simp (disch := omega) only [Ext.app' e12, Ext.app' e11, Ext.app' e10, Ext.app' e9, Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact (p11 (by norm_num))) (hτn 5 (by norm_num)) hfpw (hpC 5 (by norm_num)) (hpP 5 (by norm_num)) (fun h => absurd h (by norm_num))).toRelB freeOn_vtFree (by decide +kernel))).mono le_rfl le_rfl ?_
  rintro σ' ⟨-, ⟨v0, -⟩, -, ⟨v1, -⟩, -, ⟨v2, -⟩, -, ⟨v3, -⟩, -, ⟨v4, -⟩, -, ⟨v5, s5⟩, -⟩
  refine ⟨fun j hj => ?_, s5⟩
  have hv : ∀ j < 104, evVal.getD j 0 =
      if j < 15 then 4661 + 16 * j else if j < 30 then 5149 + 16 * (j - 15) else if j < 38 then
        5678 + 16 * (j - 30) else if j < 53 then 5955 + 16 * (j - 38) else if j < 67 then
          6478 + 16 * (j - 53) else 6980 + 16 * (j - 67) := by decide +kernel
  rw [hv j hj]
  by_cases c0 : j < 15
  · simpa [c0] using v0 j c0
  by_cases c1 : j < 30
  · simpa [c0, c1, show 15 + (j - 15) = j by omega] using v1 (j - 15) (by omega)
  by_cases c2 : j < 38
  · simpa [c0, c1, c2, show 30 + (j - 30) = j by omega] using v2 (j - 30) (by omega)
  by_cases c3 : j < 53
  · simpa [c0, c1, c2, c3, show 38 + (j - 38) = j by omega] using v3 (j - 38) (by omega)
  by_cases c4 : j < 67
  · simpa [c0, c1, c2, c3, c4, show 53 + (j - 53) = j by omega] using v4 (j - 53) (by omega)
  · simpa [c0, c1, c2, c3, c4, show 67 + (j - 67) = j by omega] using v5 (j - 67) (by omega)
end

end
end LeanVM.Guest.B1.VerifySub
