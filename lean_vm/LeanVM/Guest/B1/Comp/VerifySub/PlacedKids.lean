/-
  LeanVM.Guest.B1.Comp.VerifySub.PlacedKids

  `verify_sub`'s callees complete, placed, within weights, over a completeness model.
-/

module

public import LeanVM.Guest.B1.Comp.VerifySub.PlacedPath

/-!
# `verify_sub`'s callees, placed, over a completeness model

`CPlaced4.lean`'s `vsKids1_completeW`, `vsOpenKid_completeW`, `vsTermKid_completeW` over a
`CompModel` at a run record: the hashing callees from the model's placed shapes
(`CompleteGkrAtWC`, `CompleteTablesAtWC`, `CompleteFlockAtWC`, `CompleteOpenAtBC`), the callees free
of `BLAKE2S` (`vsFree`: `g_power_of_word`, `log2_ceil_in_the_exponent`, `assert_canonical`, the two
loops, `certify_placement`, `check_opening_terminal`) from their deployed placed completeness
(`completeAtBS_of_freeOn`, `completeAtWS_of_freeOn`), each within its weight under `CM.sem`
(`VsWeightHypsS`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.E2E.Complete
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

variable {S : BlakeSem} {rd : Reader}

/-- A tree of a function of `vsFree` valid under `S` is valid. -/
theorem valid_of_validB_vsFree {t : Tree} {a r : List E} (hn : t.name ∈ vsFree)
    (hv : t.ValidB S coreProgram rd a r) : t.Valid coreProgram rd a r := by
  rw [← validB_deployed]
  exact (validB_freeOn (S' := blakeDeployed) freeOn_vsFree t a r hn).mp hv

/-- **`__loop84`'s bodies over the run record's `rs_chain`** (`loop84_bodies`). -/
theorem loop84_bodiesC {D : VsData} {R : VsRunC} {P : VsPtrs} {out : E} (hm : VsMem0C rd D R P out)
    (hs : D.s.length = 64) : ∀ j < 64, Loop84Body rd P.zpart P.mcs P.rs (gen ^ j) := by
  intro j hj
  obtain ⟨a0, b0, hlen⟩ := rsChainC_at D.s R.mcs (j := j) (by omega)
  obtain ⟨a1, b1, -⟩ := rsChainC_at D.s R.mcs (j := j + 1) (by omega)
  have hr : ∀ k < 4, LoadHolds rd (P.rs * (gen ^ j * gen ^ j)) k
      ((rsChainC D.s R.mcs).getD (2 * j + k) 0) :=
    fun k hk => by
      rw [gen_pow_two_mul, loadHolds_mul_gen_pow]
      exact readsAt_getD hm.rs (by rw [hlen]; omega)
  refine ⟨D.s.getD j 0, gen ^ j, rsSumC D.s R.mcs j, R.mcs, R.mcs_length, hm.mcs, ?_, ?_, ?_, ?_, ?_⟩
  · rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact readsAt_getD hm.zpart (by omega)
  · have := hr 0 (by omega); rwa [Nat.add_zero, a0] at this
  · have := hr 1 (by omega); rwa [b0] at this
  · have := hr 2 (by omega); rwa [show 2 * j + 2 = 2 * (j + 1) by ring, a1, pow_succ] at this
  · have := hr 3 (by omega)
    rw [show 2 * j + 3 = 2 * (j + 1) + 1 by ring, b1] at this
    convert this using 1
    simp only [rsSumC, List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero]
    ring

variable {fs : String → ℕ} {cert : String → V → ℕ} {bytecode : List K} {D : VsData} {R : VsRunC}
  {CM : CompModel} {fp lpA sqA outA : ℕ} {off kap pt : E} {Θ : Type}

/-- Read a callee's weight off `vsBdWS`. -/
macro "vs_bdwS" : tactic => `(tactic| simp (config := { decide := true }) [vsBdWS])

/-- **The calls before the dispatch are complete within weights over the model**
(`vsKids1_completeW`). -/
theorem vsKids1_completeWC {κ : ℕ} (hb : bytecode.length = 2 ^ 22) (hok : D.OkC CM bytecode R)
    (htok : D.TOk bytecode) {Bs : VsBounds} {w : Θ → String → ℕ} (H : VsWeightHypsS CM.sem w)
    {Bsw : VsBoundsW Θ} (hG : CompleteGkrAtWC CM fs cert κ w Bs.gkr Bsw.gkr)
    (hT : CompleteTablesAtWC CM fs cert κ bytecode TCtx w Bs.tab Bsw.tab)
    (hF : CompleteFlockAtWC CM fs cert κ w Bs.fl Bsw.fl) (hPl : CompletePlaceAtB fs cert κ PCtx Bs.pl)
    (hκ : 7 ≤ κ) :
    ∀ k ∈ vsKids1C fs D R fp lpA sqA outA, k.taken = true →
      Main.CompleteAtWS CM.sem fs cert w κ k.f k.Lin k.args k.Out (vsBd fs Bs k)
        (vsBdWS w H Bsw k) := by
  intro k hk ht
  have FB : ∀ {f : String}, f ∈ vsFree → ∀ {Lin : Main.Layout} {args : List E}
      {Out : List E → Main.Layout → Prop} {B : ℕ}, CompleteAtB fs cert κ f Lin args Out B →
      CompleteAtBS CM.sem fs cert κ f Lin args Out B :=
    fun hf _ _ _ _ h => completeAtBS_of_freeOn freeOn_vsFree hf h
  have hc : ∀ x : E, IsCanonical128 x →
      CompleteAtB fs cert κ "assert_canonical" [] [x] (Returns [0]) (fs "assert_canonical") :=
    fun x hx => completeAt_of_rel_pureBat ac_pure (by simp)
      (fun rd _ => (assert_canonical_iff rd [x] [0]).mpr ⟨hx, rfl⟩) κ
      fun rd t hn hv hb => assert_canonical_totalLe fs rd t _ _ hn hv hb
  obtain ⟨hN, hl⟩ := pushTotal_boundsC hb hok
  have M := fun rd (hm : MemL rd (vsAllLC fs D R fp lpA sqA outA)) =>
    vsAll_memC (off := 0) (kap := 0) (pt := 0) hm
  have CE := cur_eqs (fs := fs) (fp := fp) (D := D) (off := 0) (kap := 0) (pt := 0)
  obtain ⟨-, hl28, hst⟩ := stack_factsC hb hok
  have hq8 : D.hs.getD 5 0 + 8 < 34 := by
    have := qflock_bound hb hok.rows_length hok.stack_le; simp only [VsData.hs]; omega
  have hE : ∀ q ∈ expL lpA sqA, q ∈ vsAllLC fs D R fp lpA sqA outA := fun q hq =>
    List.mem_append_right _ (List.mem_append_left _ hq)
  have e0 : word 1 0 0 = ofK (Parameters.gpow 0) := by
    rw [word_one, Parameters.gpow, pow_zero, ofK_one]
  simp only [vsKids1C, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (Main.CompleteAtB.toWS_weightLe (FB (by simp [vsFree])
      ((gpw6_completeAt' fs cert κ (by have := hok.rate_le; omega) sqA).mono le_rfl (by vs_bd)))
      H.gpw_le).wmono fun θ => by vs_bdwS
  · exact (Main.CompleteAtB.toWS_weightLe (FB (by simp [vsFree])
      ((gpw6_completeAt' fs cert κ (by have := hok.logMem_le; omega) sqA).mono le_rfl (by vs_bd)))
      H.gpw_le).wmono fun θ => by vs_bdwS
  · exact (Main.CompleteAtB.toWS_weightLe (FB (by simp [vsFree])
      ((log2L0_completeAt (by omega) hN hl lpA sqA _ hE).mono le_rfl (by vs_bd)))
      H.l2a_le).wmono fun θ => by vs_bdwS
  · exact (Main.CompleteAtB.toWS_weightLe (FB (by simp [vsFree])
      ((hc _ (isCanonical128_digestScalars _).1).mono le_rfl (by vs_bd))) H.ac_le).wmono
      fun θ => by vs_bdwS
  · exact (Main.CompleteAtB.toWS_weightLe (FB (by simp [vsFree])
      ((hc _ (isCanonical128_digestScalars _).2).mono le_rfl (by vs_bd))) H.ac_le).wmono
      fun θ => by vs_bdwS
  · have h := hG R.cvB _ D.xsG D.gr D.cvG (vsB fs fp D 2 + 10) (vsB fs fp D 7) _ hok.depth_lt hok.gkr
      hok.point_length hok.values_length fun rd _ hm => ⟨by
        have := (stream_at hok.rows_length (M rd hm).1.stream).1
        rwa [CE.1] at this, (M rd hm).1.zeta⟩
    rw [← hok.point_length, depth_eqC hb hok, values_eqC hok, ← CE.1] at h
    exact (Main.CompleteAtWS.bmono h (by vs_bd)).wmono fun θ => by vs_bdwS
  · have h := hT D.pi D.logMem R.alphas D.gr.2.1 D.gr.2.2 D.cvG D.xsT D.cvT D.rows D.bus D.claims
      R.beta D.bv D.rm D.gzcn (vsB fs fp D 2 + 10 + D.xsG.length) (vsB fs fp D 7) lpA sqA
      (vsB fs fp D 4) (vsB fs fp D 3) (vsB fs fp D 6) (vsB fs fp D 9) (vsB fs fp D 0)
      (vsB fs fp D 1) (vsB fs fp D 10) _ hb (by
        rw [hok.point_length]; unfold pushDepth; rw [layoutOf_logBytecode hb]; rfl)
      (by rw [hok.point_length]; exact hok.depth_lt) (by rw [htok.gzcn, htok.chis_len])
      hok.logMem_ge hok.logMem_le R.alphas_length hok.values_length
      hok.rows_length hok.rows_log hok.claims_length hok.tables fun rd _ hm => by
        obtain ⟨h0, ht, hc, hp⟩ := M rd hm
        refine ⟨?_, h0.zeta, ht, h0.rows, ?_, ?_, h0.fpw, h0.pool, tctx_ofC hok htok h0.zeta hc hp⟩
        · have := (stream_at hok.rows_length h0.stream).2.1
          rwa [CE.2.1] at this
        · have := h0.dims
          rwa [dims_eq] at this
        · have := h0.bk
          rwa [hsMap_eq] at this
    rw [← CE.2.1, depth_eqC hb hok] at h
    exact (Main.CompleteAtWS.bmono h (by vs_bd)).wmono fun θ => by vs_bdwS
  · have h := hF D.tau D.cvT D.xsF D.cvF D.zSkip D.alpha D.mv D.chi D.rcs D.s
      (vsB fs fp D 2 + 10 + D.xsG.length + D.xsT.length) (vsB fs fp D 11) (vsB fs fp D 12)
      (vsB fs fp D 13) _ (tau_ltC hok) hok.chi_length hok.rcs_length hok.s_length hok.flock
      fun rd _ hm => ⟨by
        have := (stream_at hok.rows_length (M rd hm).1.stream).2.2.1
        rwa [CE.2.2.1] at this, (M rd hm).1.zchis, (M rd hm).1.lrs, (M rd hm).1.zpart⟩
    rw [← CE.2.2.1] at h
    exact (Main.CompleteAtWS.bmono h (by vs_bd)).wmono fun θ => by vs_bdwS
  · have L : ∀ (fs' : String → ℕ) (rd : Reader) (t : Tree) (rets : List E), t.name = "__loop84" →
        t.Valid coreProgram rd [word 1 0 0, (vsPtrsAt fs fp D 0 0 0).zpart,
          (vsPtrsAt fs fp D 0 0 0).mcs, (vsPtrsAt fs fp D 0 0 0).rs] rets → t.BufsOk coreProgram →
        t.total fs' ≤ 64 * (2 * fs' "__loop84") := fun fs' rd t rets hn hv hb => by
      have h := loop84_totalLe fs' rd t [word 1 0 0, (vsPtrsAt fs fp D 0 0 0).zpart,
        (vsPtrsAt fs fp D 0 0 0).mcs, (vsPtrsAt fs fp D 0 0 0).rs] _ hn ⟨0, e0, by decide⟩ hv hb
      simp only [List.getD_cons_zero, e0, logG_spec (show (0 : ℕ) < 2 ^ 64 - 1 by decide),
        Nat.sub_zero] at h
      exact h
    refine (Main.CompleteAtB.toWS_total (FB (by simp [vsFree])
      ((completeAt_of_rel_pureBat loop84_pure (by simp)
      (fun rd hm => ?_) κ (B := 64 * (2 * fs "__loop84")) fun rd t hn hv hb => L fs rd t _ hn hv hb).mono
        le_rfl (by vs_bd))) (Bw := vsBdWS w H Bsw _) fun θ rd t rets hn hv hb =>
      (L (w θ) rd t rets hn (valid_of_validB_vsFree (by rw [hn]; simp [vsFree]) hv) hb).trans
        (by vs_bdwS))
    rw [word_one, ← pow_zero gen]
    exact loop84_complete (loop84_bodiesC (M rd hm).1 hok.s_length)
  · have hτ : D.tau ≠ 0 := by
      intro h0
      simp only [h0, pow_zero, word_one, CharTwo.add_self_eq_zero, ne_eq, not_true_eq_false,
        decide_false, Bool.false_eq_true] at ht
    have hτ29 := tau_ltC hok
    have L : ∀ (fs' : String → ℕ) (rd : Reader) (t : Tree) (rets : List E), t.name = "__loop85" →
        t.Valid coreProgram rd [word 1 0 0, gen ^ D.tau,
          (vsPtrsAt fs fp D 0 0 0).zvals * word 256 0 0, (vsPtrsAt fs fp D 0 0 0).zchis * word 256 0 0]
          rets → t.BufsOk coreProgram → t.total fs' ≤ 28 * (2 * fs' "__loop85") :=
      fun fs' rd t rets hn hv hb => by
        have h := loop85_totalLe fs' rd t [word 1 0 0, gen ^ D.tau,
          (vsPtrsAt fs fp D 0 0 0).zvals * word 256 0 0, (vsPtrsAt fs fp D 0 0 0).zchis * word 256 0 0]
          _ hn ⟨0, D.tau, e0, gen_pow_eq_ofK _, Nat.pos_of_ne_zero hτ, by omega⟩ hv hb
        simp only [List.getD_cons_zero, List.getD_cons_succ, e0, gen_pow_eq_ofK,
          logG_spec (show (0 : ℕ) < 2 ^ 64 - 1 by decide),
          logG_spec (show D.tau < 2 ^ 64 - 1 by omega), Nat.sub_zero] at h
        exact le_trans h (Nat.mul_le_mul_right _ (by omega))
    refine (Main.CompleteAtB.toWS_total (FB (by simp [vsFree])
      ((completeAt_of_rel_pureBat loop85_pure (by simp)
      (fun rd hm => ?_) κ (B := 28 * (2 * fs "__loop85")) fun rd t hn hv hb => L fs rd t _ hn hv hb).mono
        le_rfl (by vs_bd))) (Bw := vsBdWS w H Bsw _) fun θ rd t rets hn hv hb =>
      (L (w θ) rd t rets hn (valid_of_validB_vsFree (by rw [hn]; simp [vsFree]) hv) hb).trans
        (by vs_bdwS))
    have w8 : word 256 0 0 = gen ^ 8 := word_two_pow (a := 8) (by decide)
    have hm0 := (M rd hm).1
    rw [word_one, ← pow_zero gen, w8]
    refine loop85_complete (Nat.pos_of_ne_zero hτ) (by have := tau_ltC hok; unfold ordG; omega) rfl
      fun j _ hj => ?_
    have hcl := hok.chi_length
    refine ⟨D.chi.getD (8 + j) 0, ?_, ?_⟩
    · rw [mul_assoc, ← pow_add, loadHolds_mul_gen_pow, Nat.add_zero]
      exact readsAt_getD hm0.zchis (by omega)
    · rw [mul_assoc, ← pow_add, loadHolds_mul_gen_pow, Nat.add_zero]
      have : D.fpoint.getD (8 + j) 0 = D.chi.getD (8 + j) 0 := by
        rw [VsData.fpoint, List.getD_eq_getElem _ _ (by simp [hok.rcs_length]; omega),
          List.getElem_append_right (by simp [hok.rcs_length]), List.getElem_drop,
          List.getD_eq_getElem _ _ (by omega)]
        simp only [List.length_reverse, hok.rcs_length]
        congr 1; omega
      rw [← this]; exact readsAt_getD hm0.zvals (by simp [VsData.fpoint, hok.rcs_length]; omega)
  · exact (Main.CompleteAtB.toWS_weightLe (FB (by simp [vsFree])
      ((hPl _ _ _ D.logMem D.hs _ hok.logMem_le (hs_lengthC hok) (hs_ltC hok) hq8 fun rd _ hm =>
        ⟨(M rd hm).2.1, (M rd hm).1.kbase⟩).mono le_rfl (by vs_bd))) H.pl_le).wmono
      fun θ => by vs_bdwS
  · exact (Main.CompleteAtB.toWS_weightLe (FB (by simp [vsFree])
      ((log2L15_completeAt (by omega) hst (by omega) lpA sqA _ hE).mono le_rfl (by vs_bd)))
      H.l2b_le).wmono fun θ => by vs_bdwS

/-- **The opening is complete within weights over the model** (`vsOpenKid_completeW`). -/
theorem vsOpenKid_completeWC {κ : ℕ}
    {CapOk : ℕ → ℕ → Digest → Digest → List E → List Opening → E → Prop}
    {B : ℕ} {w : Θ → String → ℕ} (H : VsWeightHypsS CM.sem w) (hok : D.OkC CM bytecode R)
    (hO : CompleteOpenAtBC CM fs cert κ CapOk B)
    (hcap : CapOk (layoutOf bytecode D.logMem D.rows).stackLog D.rate D.root R.cvL D.xsW D.os
      (R.target D)) :
    let k := vsOpenKidC fs bytecode D R fp lpA sqA outA
    Main.CompleteAtWS CM.sem fs cert w κ k.f k.Lin k.args k.Out B fun θ => H.os θ := by
  intro k
  have h := hO _ D.rate hok.stack_ge hok.stack_le hok.rate_ge hok.rate_le D.root R.cvL D.xsW D.os D.w
    D.cvW D.roots' (R.target D) _ (vsAllLC fs D R fp lpA sqA outA) hok.opening hcap fun rd _ hm => by
      have := (stream_at hok.rows_length
        (vsAll_memC (off := 0) (kap := 0) (pt := 0) hm).1.stream).2.2.2
      rwa [curW_eq] at this
  rw [← curW_eq] at h
  exact Main.CompleteAtB.toWS_weightLe h fun θ =>
    H.os_le θ _ _ hok.stack_ge hok.stack_le hok.rate_ge hok.rate_le

/-- **The terminal is complete within weights over the model** (`vsTermKid_completeW`), from its
deployed placed completeness (free of `BLAKE2S`). -/
theorem vsTermKid_completeWC {κ : ℕ} (hb : bytecode.length = 2 ^ 22) (hok : D.OkC CM bytecode R)
    (htok : D.TOk bytecode) {B : ℕ} {w : Θ → String → ℕ} {Bw : Θ → ℕ}
    (hE : CompleteTermAtW fs cert κ TCtx PCtx w B Bw) {Lc : Main.Layout} {b : ℕ}
    (hc : ∀ rd, MemL rd Lc → PCtx rd (columnKappas D.logMem 18 D.hs) off kap) :
    let k := vsTermKidC fs D R fp lpA sqA outA off kap (ofK (Parameters.gpow b)) Lc
      [(b, D.w.point ++ List.replicate (pointCap - D.w.point.length) 0)]
    Main.CompleteAtWS CM.sem fs cert w κ k.f k.Lin k.args k.Out B Bw := by
  intro k
  refine completeAtWS_of_freeOn freeOn_vsFree (by simp [k, vsTermKidC, vsFree]) ?_
  refine hE (layoutOf bytecode D.logMem D.rows) D.bus D.claims R.lam D.fpoint (ringCoefficients R.mcs)
    D.w D.chis _ _ hok.accepts htok.point_vars htok.gzcn fun rd _ hm => ?_
  obtain ⟨h12, h3⟩ := Main.memL_append.mp hm
  obtain ⟨h1, h2⟩ := Main.memL_append.mp h12
  obtain ⟨hm0, -, hchi, hcp⟩ := vsAll_memC (off := off) (kap := kap) (pt := ofK (Parameters.gpow b)) h1
  have htc := tctx_ofC hok htok hm0.zeta hchi hcp
  rw [depth_eqC hb hok] at htc
  exact ⟨termPre_ofC hb hok htc (hc rd h2) (hypKappa rd) hm0.lam hm0.zvals hm0.ctab
    (h3 _ List.mem_cons_self), hchi⟩

end
end LeanVM.Guest.B1.VerifySub
