/-
  LeanVM.Guest.B1.Main.AggRegionC

  `aggregate_claims`' completeness in the uniform region-indexed form under a semantics `S` over
  an answered hash (`AggRegion.lean` over `S` and `Ha`, the honest words over `Ht`).
-/

module

public import LeanVM.Guest.B1.Main.AggCompleteC
public import LeanVM.Guest.B1.Main.AggRegion
public import LeanVM.Guest.B1.Main.AggSizeS

/-!
# `aggregate_claims`, by regions, over an answered hash

`aggBufsH Ht`, `aggOwnLH Ht`: the honest contents and layout of the fifteen `HeapBuf`s over
`Ht` (`aggBufs`, `aggOwnL`), giving `AggMemH Ht` (`aggMemH_of_memL`). `agC_bs22`, `agC_bs28`: the
batching sumchecks from the answered runs (`AggAns`), by `BsRowsC`. `aggregateC_claims_relAtIn`:
`aggregate_claims_relAtIn` under `S`, the callees placed by `relAtInB_uniform_of_supp`, the body
by `agBodyC_holds`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node

@[expose] public section

variable {S : BlakeSem} {Ha : List UInt8 → Option Digest} (Ht : List UInt8 → Digest) {rd : Reader}

/-! ## The layouts -/

/-- **The honest contents of `aggregate_claims`' `HeapBuf`s**, in allocation order. -/
noncomputable def aggBufsH (cs : List ChildClaims) (h : BatchHints) (fresh carried : E) : List (List E) :=
  let n := cs.length
  let rs := (agRbH Ht cs h).1.1
  let rM := (agRmH Ht cs h).1.1
  [h.bytecodeRounds.flatMap (fun r => [r.1, r.2]), h.matrixRounds.flatMap (fun r => [r.1, r.2]),
    (List.range n).map (fun c => fresh * gen ^ (106 * c)),
    (List.range n).map (fun c => carried * gen ^ (53 * c)),
    (List.range (n + 1)).flatMap (fun c =>
      [(digestScalars (obsAllH Ht (agCv1H Ht cs) ((cs.take c).flatMap childCells))).1,
        (digestScalars (obsAllH Ht (agCv1H Ht cs) ((cs.take c).flatMap childCells))).2]),
    (List.range n).flatMap (fun c => [((agLBH Ht cs).getD c (0, 0)).1, ((agLBH Ht cs).getD c (0, 0)).2]),
    (List.range (n + 1)).flatMap (fun c => [(digestScalars (sqIt2H Ht (agCvAH Ht cs) c)).1,
      (digestScalars (sqIt2H Ht (agCvAH Ht cs) c)).2,
      sumE (List.zipWith bcTerm (cs.take c) ((agLBH Ht cs).take c))]),
    rs,
    (List.range (n + 1)).map (fun c =>
      sumE (List.zipWith (bcWeight rs) (cs.take c) ((agLBH Ht cs).take c))),
    (List.range n).flatMap (fun c => [((agLMH Ht cs h).getD c (0, 0, 0)).1,
      ((agLMH Ht cs h).getD c (0, 0, 0)).2.1, ((agLMH Ht cs h).getD c (0, 0, 0)).2.2]),
    (List.range (n + 1)).flatMap (fun c => [(digestScalars (sqIt3H Ht (agRbH Ht cs h).2 c)).1,
      (digestScalars (sqIt3H Ht (agRbH Ht cs h).2 c)).2,
      sumE (List.zipWith mtTerm (cs.take c) ((agLMH Ht cs h).take c))]),
    rM,
    (List.range 6).flatMap (fun t => (List.range (2 ^ (t + 1))).map (etK (rM.take 6) (t + 1))),
    (List.range 6).flatMap (fun t =>
      (List.range (2 ^ (t + 1))).map (etK ((rM.drop 14).take 6) (t + 1))),
    (List.range (n + 1)).flatMap (fun c =>
      [sumE (List.zipWith (mtWeightA rM) (cs.take c) ((agLMH Ht cs h).take c)),
        sumE (List.zipWith (mtWeightB rM) (cs.take c) ((agLMH Ht cs h).take c))])]

/-- `aggregate_claims`' `HeapBuf`s at `fp`. -/
noncomputable def aggOwnLH (fs : String → ℕ) (fp : ℕ) (cs : List ChildClaims) (h : BatchHints) (fresh carried : E) :
    Layout :=
  (bases (fp + fs "aggregate_claims") (aggSizes cs.length)).zip (aggBufsH Ht cs h fresh carried)

/-! ## The layouts give the memory facts -/

/-- **The fifteen `HeapBuf`s held**, one `ReadsAt` each at `aggPtrs`. -/
theorem memL_ownH {fs : String → ℕ} {fp : ℕ} {cs : List ChildClaims} {h : BatchHints}
    {fresh carried : E} (hL : MemL rd (aggOwnLH Ht fs fp cs h fresh carried)) :
    let P := aggPtrs fs fp cs.length
    let B := aggBufsH Ht cs h fresh carried
    ReadsAt rd P.msgB (B.getD 0 []) ∧ ReadsAt rd P.msgM (B.getD 1 []) ∧
      ReadsAt rd P.frow (B.getD 2 []) ∧ ReadsAt rd P.crow (B.getD 3 []) ∧
      ReadsAt rd P.absb (B.getD 4 []) ∧ ReadsAt rd P.lamB (B.getD 5 []) ∧
      ReadsAt rd P.bcc (B.getD 6 []) ∧ ReadsAt rd P.rs (B.getD 7 []) ∧
      ReadsAt rd P.wB (B.getD 8 []) ∧ ReadsAt rd P.lamM (B.getD 9 []) ∧
      ReadsAt rd P.mcc (B.getD 10 []) ∧ ReadsAt rd P.rM (B.getD 11 []) ∧
      ReadsAt rd P.eqR (B.getD 12 []) ∧ ReadsAt rd P.eqC (B.getD 13 []) ∧
      ReadsAt rd P.wsum (B.getD 14 []) := by
  simp only [aggOwnLH, aggSizes, bases, aggBufsH, List.zip_cons_cons, List.zip_nil_right, memL_cons,
    memL_nil, and_true] at hL
  simp only [aggPtrs, aggSizes, bases, aggBufsH, List.getD_cons_zero, List.getD_cons_succ]
  exact hL

theorem aggMemH_of_memL {fs : String → ℕ} {fp : ℕ} {cs : List ChildClaims} {h : BatchHints}
    {fresh carried : E} (hbr : h.bytecodeRounds.length = 22) (hmr : h.matrixRounds.length = 28)
    (hL : MemL rd (aggOwnLH Ht fs fp cs h fresh carried)) :
    AggMemH Ht rd (aggPtrs fs fp cs.length) fresh carried cs h := by
  obtain ⟨m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14⟩ := memL_ownH Ht hL
  simp only [aggBufsH, List.getD_cons_zero, List.getD_cons_succ] at m0 m1 m2 m3 m4 m5 m6 m7
  simp only [aggBufsH, List.getD_cons_zero, List.getD_cons_succ] at m8 m9 m10 m11 m12 m13 m14
  have r4 := readsAt_range_flatMap (w := 2) (fun _ _ => rfl) m4
  have r5 := readsAt_range_flatMap (w := 2) (fun _ _ => rfl) m5
  have r6 := readsAt_range_flatMap (w := 3) (fun _ _ => rfl) m6
  have r9 := readsAt_range_flatMap (w := 3) (fun _ _ => rfl) m9
  have r10 := readsAt_range_flatMap (w := 3) (fun _ _ => rfl) m10
  have r14 := readsAt_range_flatMap (w := 2) (fun _ _ => rfl) m14
  refine ⟨fun r hr => readsAt_pairs m0 r (by omega), fun r hr => readsAt_pairs m1 r (by omega),
    fun c hc => ⟨readsAt_range_map m2 c hc, readsAt_range_map m3 c hc⟩,
    fun c hc => ⟨by simpa using r4 c (by omega) 0 (by omega),
      by simpa using r4 c (by omega) 1 (by omega)⟩,
    fun c hc => ⟨by simpa using r5 c hc 0 (by omega), by simpa using r5 c hc 1 (by omega)⟩,
    fun c hc => ⟨by simpa using r6 c (by omega) 0 (by omega),
      by simpa using r6 c (by omega) 1 (by omega), by simpa using r6 c (by omega) 2 (by omega)⟩,
    m7, fun c hc => readsAt_range_map m8 c (by omega),
    fun c hc => ⟨by simpa using r9 c hc 0 (by omega), by simpa using r9 c hc 1 (by omega),
      by simpa using r9 c hc 2 (by omega)⟩,
    fun c hc => ⟨by simpa using r10 c (by omega) 0 (by omega),
      by simpa using r10 c (by omega) 1 (by omega), by simpa using r10 c (by omega) 2 (by omega)⟩,
    m11, readsAt_eqLayers m12, readsAt_eqLayers m13,
    fun c hc => ⟨by simpa using r14 c (by omega) 0 (by omega),
      by simpa using r14 c (by omega) 1 (by omega)⟩⟩

theorem length_aggBufsH {cs : List ChildClaims} {h : BatchHints} {fresh carried : E}
    (hbr : h.bytecodeRounds.length = 22) (hmr : h.matrixRounds.length = 28) :
    (aggBufsH Ht cs h fresh carried).map List.length = aggSizes cs.length := by
  have hrb : (agRbH Ht cs h).1.1.length = 22 := by rw [agRbH, batchRoundsWithH_length, hbr]
  have hrm : (agRmH Ht cs h).1.1.length = 28 := by rw [agRmH, batchRoundsWithH_length, hmr]
  have l2 : ∀ (m : ℕ) (f : ℕ → E) (g : ℕ → E),
      ((List.range m).flatMap fun c => [f c, g c]).length = 2 * m := fun m f g => by
    rw [length_flatMap_range]; simp [mul_comm]
  have l3 : ∀ (m : ℕ) (f g k : ℕ → E),
      ((List.range m).flatMap fun c => [f c, g c, k c]).length = 3 * m := fun m f g k => by
    rw [length_flatMap_range]; simp [mul_comm]
  have lp : ∀ l : List (E × E), (l.flatMap fun r => [r.1, r.2]).length = 2 * l.length := fun l => by
    induction l with
    | nil => rfl
    | cons a l ih => simp [List.flatMap_cons, ih]; ring
  have le : ∀ rs : List E,
      ((List.range 6).flatMap fun t => (List.range (2 ^ (t + 1))).map (etK rs (t + 1))).length =
        126 := fun rs => by
    rw [length_flatMap_range]; simp [Finset.sum_range_succ]
  simp only [aggBufsH, aggSizes, List.map_cons, List.map_nil, lp, hbr, hmr, List.length_map,
    List.length_range, l2, l3, hrb, hrm, le, List.cons.injEq, and_true]
  and_intros
  all_goals trivial


/-! ## The batching sumchecks -/

section Callees

variable {Ht} {cs : List ChildClaims} {h : BatchHints} {fresh carried : E} {P : AggPtrs}

theorem agC_bs22 (hBs : BsRowsC S Ha) (hA : AggAns Ha Ht cs h) (hbr : h.bytecodeRounds.length = 22)
    (hM : AggMemH Ht rd P fresh carried cs h) :
    coreProgram.RelB S rd "batch_sumcheck__L22"
      [(digestScalars (sqIt2H Ht (agCvAH Ht cs) cs.length)).1,
        (digestScalars (sqIt2H Ht (agCvAH Ht cs) cs.length)).2,
        P.msgB, sumE (List.zipWith bcTerm cs (agLBH Ht cs)), P.rs]
      [(digestScalars (agRbH Ht cs h).2).1, (digestScalars (agRbH Ht cs h).2).2, (agRbH Ht cs h).1.2] :=
  hBs.bs22 rd _ _ ⟨_, h.bytecodeRounds, _, _, _, rfl, hbr,
    fun r hr => by
      have := hM.msgB r (by rwa [hbr] at hr)
      rwa [List.getD_eq_getElem _ _ hr] at this, hA.runB, hM.rs, rfl⟩

theorem agC_bs28 (hBs : BsRowsC S Ha) (hA : AggAns Ha Ht cs h) (hmr : h.matrixRounds.length = 28)
    (hM : AggMemH Ht rd P fresh carried cs h) :
    coreProgram.RelB S rd "batch_sumcheck__L28"
      [(digestScalars (sqIt3H Ht (agRbH Ht cs h).2 cs.length)).1,
        (digestScalars (sqIt3H Ht (agRbH Ht cs h).2 cs.length)).2, P.msgM,
        sumE (List.zipWith mtTerm cs (agLMH Ht cs h)), P.rM]
      [(digestScalars (agRmH Ht cs h).2).1, (digestScalars (agRmH Ht cs h).2).2, (agRmH Ht cs h).1.2] :=
  hBs.bs28 rd _ _ ⟨_, h.matrixRounds, _, _, _, rfl, hmr,
    fun r hr => by
      have := hM.msgM r (by rwa [hmr] at hr)
      rwa [List.getD_eq_getElem _ _ hr] at this, hA.runM, hM.rM, rfl⟩

end Callees

/-! ## The relation, by regions -/

variable {Ht}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **`aggregate_claims`, by regions** (G:3319-3486; TRIAGE #77): for nonempty claims `cs` of the
guest's shape, at most `16`, hints of `22` and `28` rounds whose batching closes on `d`, the
children's public inputs, fresh and carried claims at `g^ap`, `g^af`, `g^ac` and `defer_stmt` at
`g^ad`, at every `fp` one size `n`, covering the frame and the `HeapBuf`s, serves every memory
holding `aggregate_claims`' `HeapBuf`s at `fp` and the caller's buffers: `aggregate_claims` holds
by a tree placed at `fp`, of `n` words, loading from its own data or the caller's buffers. -/
theorem aggregateC_claims_relAtIn (hF : FsRowsC S Ha) (hBs : BsRowsC S Ha) (fs : String → ℕ)
    (cert : String → V → ℕ) {cs : List ChildClaims} {h : BatchHints} {d : DeferredClaim}
    (hA : AggAns Ha Ht cs h) (hne : cs ≠ []) (hlen : cs.length ≤ 16)
    (hb : Id.run (batchWith (m := Id) Ht aggSeedD cs h) = some d) (hbr : h.bytecodeRounds.length = 22)
    (hmr : h.matrixRounds.length = 28)
    (hsh : ∀ c ∈ cs, FreshShaped c.fresh ∧ c.carried.bytecodePoint.length = 22 ∧
      c.carried.matrixPoint.length = 28) (ap af ac ad fp : ℕ) :
    ∃ n, fs "aggregate_claims" + (aggSizes cs.length).sum ≤ n ∧ n ≤ aggBound fs cs.length ∧
      ∀ rd : Reader, MemL rd (aggOwnLH Ht fs fp cs h (ofK (gpow af)) (ofK (gpow ac)) ++
        aggExtL ap af ac ad cs d) →
      RelAtInB S coreProgram fs cert rd (RegionL (aggExtL ap af ac ad cs d)) (fun _ => False) fp n
        "aggregate_claims" [gen ^ cs.length, ofK (gpow ap), ofK (gpow af), ofK (gpow ac),
          ofK (gpow ad)] [] := by
  classical
  have hn0 : 0 < cs.length := List.length_pos_iff.mpr hne
  set L := aggOwnLH Ht fs fp cs h (ofK (gpow af)) (ofK (gpow ac)) ++ aggExtL ap af ac ad cs d with hLdef
  set SR := RegionL L with hS
  set P := aggPtrs fs fp cs.length with hP
  set σ := agValH Ht cs h P (ofK (gpow ap)) (ofK (gpow af)) (ofK (gpow ac)) (ofK (gpow ad)) with hσ
  set es := agPre.flatMap (slEvs σ) with hes
  have hwf : Stmt.wfList coreProgram agBody = true := by
    have := coreProgram_wf Data.core29 (List.mem_of_find?_eq_some find_aggregate_claims)
    rwa [core29_body] at this
  have hw := walk_straight σ [] agPre agPre_straight
  rw [← agBody_eq] at hw
  obtain ⟨e1, e2, e3, e4⟩ := straight_parts σ agPre agPre_straight
  rw [agPre_allocs] at e1 e2
  rw [agPre_addrs] at e3
  rw [agPre_calls] at e4
  have hK : 1 + gen ^ cs.length ≠ 0 := one_add_gen_pow_ne_zero hn0 (by unfold ordG; omega)
  have hlt : ∀ e ≤ 3 * cs.length + 3, e < 2 ^ 64 - 1 := fun e he => by
    have : 3 * cs.length + 3 < 2 ^ 64 - 1 := by norm_num; omega
    omega
  have t33 : σ (.n 33) ≠ 0 := by simp only [hσ, agValH]; ag_look; exact hK
  have t48 : σ (.n 48) ≠ 0 := by simp only [hσ, agValH]; ag_look; exact hK
  have t67 : σ (.n 67) ≠ 0 := by simp only [hσ, agValH]; ag_look; exact hK
  have t82 : σ (.n 82) ≠ 0 := by simp only [hσ, agValH]; ag_look; exact hK
  have t513 : σ (.n 513) ≠ 0 := by simp only [hσ, agValH]; ag_look; exact hK
  have g0 : logG (σ (.n 0)) = cs.length := by
    rw [show σ (.n 0) = gen ^ cs.length by simp only [hσ, agValH]; ag_look]
    exact logG_gen_pow (hlt _ (by omega))
  have g30 : logG (σ (.n 30)) = 2 * cs.length + 2 := by
    rw [show σ (.n 30) = gen ^ (2 * cs.length + 2) by simp only [hσ, agValH]; ag_look; ring]
    exact logG_gen_pow (hlt _ (by omega))
  have g37 : logG (σ (.n 37)) = 2 * cs.length := by
    rw [show σ (.n 37) = gen ^ (2 * cs.length) by simp only [hσ, agValH]; ag_look; ring]
    exact logG_gen_pow (hlt _ (by omega))
  have g42 : logG (σ (.n 42)) = 3 * cs.length + 3 := by
    rw [show σ (.n 42) = gen ^ (3 * cs.length + 3) by simp only [hσ, agValH]; ag_look; ring]
    exact logG_gen_pow (hlt _ (by omega))
  have g63 : logG (σ (.n 63)) = cs.length + 1 := by
    rw [show σ (.n 63) = gen ^ (cs.length + 1) by simp only [hσ, agValH]; ag_look; ring]
    exact logG_gen_pow (hlt _ (by omega))
  have g73 : logG (σ (.n 73)) = 3 * cs.length := by
    rw [show σ (.n 73) = gen ^ (3 * cs.length) by simp only [hσ, agValH]; ag_look; ring]
    exact logG_gen_pow (hlt _ (by omega))
  have g78 : logG (σ (.n 78)) = 3 * cs.length + 3 := by
    rw [show σ (.n 78) = gen ^ (3 * cs.length + 3) by simp only [hσ, agValH]; ag_look; ring]
    exact logG_gen_pow (hlt _ (by omega))
  have g508 : logG (σ (.n 508)) = 2 * cs.length + 2 := by
    rw [show σ (.n 508) = gen ^ (2 * cs.length + 2) by simp only [hσ, agValH]; ag_look; ring]
    exact logG_gen_pow (hlt _ (by omega))
  have hall : allocs σ es = aggSizes cs.length := by
    rw [e2]
    simp only [List.map_cons, List.map_nil, Sum.elim_inl, Sum.elim_inr, id, g0, g30, g37, g42, g63,
      g73, g78, g508, aggSizes]
  have hbuf : (allocDsts es).map σ = (bases (fp + fs "aggregate_claims") (allocs σ es)).map
      fun b => ofK (gpow b) := by
    rw [e1, hall]
    simp only [List.map_cons, List.map_nil, hσ, agValH]
    ag_look
    simp only [hP, aggPtrs, aggSizes, bases, List.map_cons, List.map_nil, List.getD_cons_zero,
      List.getD_cons_succ]
  have hown : ∀ i, RegionL (aggOwnLH Ht fs fp cs h (ofK (gpow af)) (ofK (gpow ac))) i →
      ownData cert fp (fp + fs "aggregate_claims") "aggregate_claims" (allocs σ es) es i :=
    fun i hi => Or.inl (by rw [hall]; exact region_zip _ _ _ (length_aggBufsH Ht hbr hmr) i hi)
  have hSR : ∀ i, SR i → RegionL (aggExtL ap af ac ad cs d) i ∨
      ownData cert fp (fp + fs "aggregate_claims") "aggregate_claims" (allocs σ es) es i :=
    fun i hi => (regionL_append.mp hi).elim (fun h => Or.inr (hown i h)) Or.inl
  by_cases hex : ∃ rd1, MemL rd1 L
  swap
  · exact ⟨_, le_rfl, by unfold aggBound; omega, fun rd hL => absurd ⟨rd, hL⟩ hex⟩
  obtain ⟨rd1, h1⟩ := hex
  -- the restriction of one memory to the layouts
  have h0 : MemL (restrict rd1 SR) L := memL_restrict h1 fun i hi => hi
  obtain ⟨ho0, he0⟩ := memL_append.mp h0
  have hM0 := aggMemH_of_memL Ht hbr hmr ho0
  obtain ⟨hC0, hd0⟩ := childClaimsAt_of_memL hsh he0
  have hsupp := restrict_supp' rd1 SR
  obtain ⟨m95, k95⟩ := relAtInB_uniform_of_supp fs cert coreProgram_wf aggPure (g := "__loop95")
    (by simp) hsupp (agC_loop95 hF hA hn0 hC0 hM0)
  obtain ⟨m96, k96⟩ := relAtInB_uniform_of_supp fs cert coreProgram_wf aggPure (g := "__loop96")
    (by simp) hsupp (agC_loop96 hF hA hn0 hC0 hM0)
  obtain ⟨m22, k22⟩ := relAtInB_uniform_of_supp fs cert coreProgram_wf aggPure
    (g := "batch_sumcheck__L22") (by simp) hsupp (agC_bs22 hBs hA hbr hM0)
  obtain ⟨m97, k97⟩ := relAtInB_uniform_of_supp fs cert coreProgram_wf aggPure (g := "__loop97")
    (by simp) hsupp (agC_loop97 hn0 hbr hC0 hM0)
  obtain ⟨m98, k98⟩ := relAtInB_uniform_of_supp fs cert coreProgram_wf aggPure (g := "__loop98")
    (by simp) hsupp (agC_loop98 hF hA hn0 hC0 hM0)
  obtain ⟨m28, k28⟩ := relAtInB_uniform_of_supp fs cert coreProgram_wf aggPure
    (g := "batch_sumcheck__L28") (by simp) hsupp (agC_bs28 hBs hA hmr hM0)
  obtain ⟨m99, k99⟩ := relAtInB_uniform_of_supp fs cert coreProgram_wf aggPure (g := "__loop99")
    (by simp) hsupp (agC_loop99 hn0 hmr hC0 hM0)
  have hs0 := walkB_sat agBody hwf (agBodyC_holds hF hBs hA hne hb hbr hmr hC0 hd0 P hM0)
  rw [hw] at hs0
  have hloadS := loadsB_of_supp hsupp fun e he => (hs0.1 e he).1
  have hx : ∀ A v, restrict rd1 SR A = some v → restrict rd1 SR A = some v := fun _ _ h => h
  have b95 : m95 ≤ cs.length * fs "__loop95" + fs "__loop95" := by
    obtain ⟨t, hn, hv, hbo, -, ht, -⟩ := k95 0 _ hx; rw [← ht]; exact loop95S_total hn0 hn hv hbo
  have b96 : m96 ≤ cs.length * fs "__loop96" + fs "__loop96" := by
    obtain ⟨t, hn, hv, hbo, -, ht, -⟩ := k96 0 _ hx; rw [← ht]; exact loop96S_total hn0 hn hv hbo
  have b97 : m97 ≤ cs.length * fs "__loop97" + fs "__loop97" := by
    obtain ⟨t, hn, hv, hbo, -, ht, -⟩ := k97 0 _ hx; rw [← ht]; exact loop97S_total hn0 hn hv hbo
  have b98 : m98 ≤ cs.length * fs "__loop98" + fs "__loop98" := by
    obtain ⟨t, hn, hv, hbo, -, ht, -⟩ := k98 0 _ hx; rw [← ht]; exact loop98S_total hn0 hn hv hbo
  have b99 : m99 ≤ cs.length * fs "__loop99" + fs "__loop99" := by
    obtain ⟨t, hn, hv, hbo, -, ht, -⟩ := k99 0 _ hx; rw [← ht]; exact loop99S_total hn0 hn hv hbo
  have b22 : m22 = fs "batch_sumcheck__L22" := by
    obtain ⟨t, hn, hv, hbo, -, ht, -⟩ := k22 0 _ hx; rw [← ht]; exact bs22S_total hn hv hbo
  have b28 : m28 = fs "batch_sumcheck__L28" := by
    obtain ⟨t, hn, hv, hbo, -, ht, -⟩ := k28 0 _ hx; rw [← ht]; exact bs28S_total hn hv hbo
  refine ⟨fs "aggregate_claims" + (allocs σ es).sum +
    (m95 + (m96 + (m22 + (m97 + (m98 + (m28 + (m99 + 0))))))), by rw [hall]; omega,
    by rw [hall]; unfold aggBound; omega, fun rd hL => ?_⟩
  obtain ⟨ho, he⟩ := memL_append.mp hL
  obtain ⟨hC, hd⟩ := childClaimsAt_of_memL hsh he
  have hs := walkB_sat agBody hwf (agBodyC_holds hF hBs hA hne hb hbr hmr hC hd P (aggMemH_of_memL Ht hbr hmr ho))
  rw [hw] at hs
  have hext : ∀ A v, restrict rd1 SR A = some v → rd A = some v := fun A v hA => by
    obtain ⟨i, rfl, hi⟩ := restrict_supp hA
    rw [restrict_of ⟨i, rfl, hi⟩] at hA
    rw [memL_agree hL h1 i hi]; exact hA
  refine relAtInB_of_walk (Dk := fun _ => False)
    (N := m95 + (m96 + (m22 + (m97 + (m98 + (m28 + (m99 + 0)))))))
    coreProgram_wf find_aggregate_claims (Or.inl aggregate_claims_not_loop)
    (by simp only [show Fn.params Data.core29 = [.n 0, .n 1, .n 2, .n 3, .n 4] from rfl,
      List.map_cons, List.map_nil, hσ, agValH]; ag_look) (by rw [core29_body]; exact hw) rfl
    (fun e he => (hs.1 e he).1) hbuf (by rw [e3]; simp) ?_ ?_ (fun _ h => h.elim)
  · rw [e4]
    simp only [List.map_cons, List.map_nil, mkCall, KidsFromInB, ne_eq, t33, t48, t67, t82, t513,
      not_false_eq_true, decide_true, ↓reduceIte]
    refine ⟨m95, _, SR, fun _ => False, rfl, fun i hi => Or.inl (hSR i hi), ?_,
      m96, _, SR, fun _ => False, rfl, fun i hi => Or.inl (hSR i hi), ?_,
      m22, _, SR, fun _ => False, rfl, fun i hi => Or.inl (hSR i hi), ?_,
      m97, _, SR, fun _ => False, rfl, fun i hi => Or.inl (hSR i hi), ?_,
      m98, _, SR, fun _ => False, rfl, fun i hi => Or.inl (hSR i hi), ?_,
      m28, _, SR, fun _ => False, rfl, fun i hi => Or.inl (hSR i hi), ?_,
      m99, _, SR, fun _ => False, rfl, fun i hi => Or.inl (hSR i hi), ?_, rfl, fun i hi => ?_⟩
    all_goals try (simp only [hσ, agValH]; ag_look)
    exacts [k95 _ rd hext, k96 _ rd hext, k22 _ rd hext, k97 _ rd hext, k98 _ rd hext, k28 _ rd hext,
      k99 _ rd hext, by simp at hi]
  · intro A hA
    obtain ⟨i, hi, hSi⟩ := hloadS A hA
    exact ⟨i, hi, (hSR i hSi).elim (fun h => Or.inr (Or.inl h)) Or.inl⟩

end
end LeanVM.Guest.B1.Main
