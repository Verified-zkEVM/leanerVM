/-
  LeanVM.Guest.B1.Comp.VerifySub.PlacedPath

  `verify_sub`'s buffers, honest calls, path, frames and loads over a completeness model, at a
  run record: the model version of `CPlaced0`–`CPlaced7`'s pieces that read the run's hashes.
-/

module

public import LeanVM.Guest.B1.Comp.VerifySub.PlacedIface

/-!
# `verify_sub`'s path, placed, over a completeness model

The deployed `CPlaced*` files take the run's hashes from `VsData` (`D.alphas`, `D.beta`, `D.cvB`,
`D.mcs`, `D.cvL`, `D.lam`, `D.target`, `D.fresh`); over a model they are a run record's
(`VsRunC`). The rest (`vsSizes`, `vsPtrsAt`, `vsPre1`, `vsEvs`, `vs_parts`, `InBuf`, `PlaceOut`,
`OpenOutK`, `TOk`) reads no hash and is the deployed.

* the buffers `vsBufsC`, the layouts `vsOwnLC`, `vsExtLC`, `vsAllLC` and their memory
  (`vsAll_memC`);
* the honest calls `vsTriplesC`, `vsCC`; the path `vs_runC` from `vs_bodyC`, its frames
  `vs_callsC`;
* the callees before the dispatch, the opening and the terminal (`vsKids1C`, `vsOpenKidC`,
  `vsTermKidC`) and the frames' match (`match1C`, `matchOpenC`, `matchTermC`);
* the buffers placed (`vsBufs_fitC`, `vs_allocsC`) and the loads (`vs_loadC`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Sig LeanVM.E2E.Complete
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-! ## The run's facts over the model -/

section Facts

variable {CM : CompModel} {D : VsData} {R : VsRunC} {bytecode : List K} {rd : Reader} {P : VsPtrs}

theorem tau_ltC (hok : D.OkC CM bytecode R) : D.tau < 29 := by
  unfold VsData.tau VsData.hs
  rw [List.getD_eq_getElem _ _ (by simp [hok.rows_length]), List.getElem_map]
  exact hok.rows_log _ (List.getElem_mem _)

theorem values_eqC (hok : D.OkC CM bytecode R) :
    D.gr.2.2 = [D.gr.2.2.getD 0 0, D.gr.2.2.getD 1 0, D.gr.2.2.getD 2 0] := by
  have := hok.values_length
  match h : D.gr.2.2, this with
  | [a, b, c], _ => rfl

theorem stack_factsC (hb : bytecode.length = 2 ^ 22) (hok : D.OkC CM bytecode R) :
    (layoutOf bytecode D.logMem D.rows).stackLog = max 15 (log2Ceil D.stackTot) ∧
      log2Ceil D.stackTot ≤ 28 ∧ D.stackTot < 2 ^ 34 := by
  have h : (layoutOf bytecode D.logMem D.rows).stackLog = max 15 (log2Ceil D.stackTot) :=
    stackLog_eq hb D.logMem D.rows
  have h2 := hok.stack_le
  refine ⟨h, by rw [h] at h2; exact le_trans (le_max_right _ _) h2, ?_⟩
  rw [h] at h2
  exact lt_of_le_of_lt (le_two_pow_log2Ceil _) (Nat.pow_lt_pow_right (by decide) (by omega))

theorem pushTotal_boundsC (hb : bytecode.length = 2 ^ 22) (hok : D.OkC CM bytecode R) :
    D.pushTotal < 2 ^ 34 ∧ log2Ceil D.pushTotal < 34 := by
  have hdep : log2Ceil D.pushTotal < 33 := by
    rw [← depth_eqC hb hok, hok.point_length]; exact hok.depth_lt
  exact ⟨lt_of_le_of_lt (le_two_pow_log2Ceil _) (Nat.pow_lt_pow_right (by decide) (by omega)),
    by omega⟩

theorem bus_pointC (hok : D.OkC CM bytecode R) : D.bus.point = D.gr.2.1 := by
  have hT0 := hok.tables (.claimed ⟨D.gr.2.1.take (layoutOf bytecode D.logMem D.rows).logBytecode ++
    R.alphas, D.bv, 0, 0, [], [], [], 0⟩) (bytecodeAtM_claimed _ bytecode)
  rw [tablesSeg_pointM hT0]

theorem busPoint_lengthC (hok : D.OkC CM bytecode R) : D.bus.point.length < 33 := by
  rw [bus_pointC hok, hok.point_length]; exact hok.depth_lt

/-- **The tables' context** (`tctx_of`) over the model. -/
theorem tctx_ofC (hok : D.OkC CM bytecode R) (htok : D.TOk bytecode) (hz : ReadsAt rd P.zeta D.gr.2.1)
    (hchi : ReadsAt rd P.chi D.chis) (hcp : ReadsAt rd P.cplen (cplenWords D)) :
    TCtx rd (layoutOf bytecode D.logMem D.rows) D.bus D.claims
      [P.zeta, P.chi, D.rm, gen ^ D.gr.2.1.length, D.gzcn, P.cplen] := by
  have hbp := bus_pointC hok
  refine ⟨D.chis, by rw [hbp]; exact hz, by rw [hbp], hchi, htok.gzcn,
    by rw [hbp]; exact htok.chis_le, hok.claims_length, htok.columns, fun j p hj => ?_⟩
  obtain ⟨h1, h2, h3⟩ := htok.points j p hj
  refine ⟨fun hjn => ?_, fun h5 => by rw [hbp]; exact h1 h5, h2, h3⟩
  have hcl : (cplenWords D).length = nPooled := by
    simp [cplenWords, hok.claims_length, nPooled, nClaims]
  have hjl : j < (cplenWords D).length := by rw [hcl]; exact hjn
  have := hcp j hjl
  convert this using 2
  simp only [List.getElem?_map] at hj
  simp only [cplenWords, List.getElem_map, List.getElem_take]
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hj
  obtain ⟨_, hcj⟩ := List.getElem?_eq_some_iff.mp hc
  simp only [hcj]

/-- **The terminal's precondition** (`termPre_of`) over the model, at the run's `λ` and ring
challenges. -/
theorem termPre_ofC {TC : Reader → Layout → BusResult → List ColumnClaim → List E → Prop}
    {PC : Reader → List ℕ → E → E → Prop} (hb : bytecode.length = 2 ^ 22) (hok : D.OkC CM bytecode R)
    (htc : TC rd (layoutOf bytecode D.logMem D.rows) D.bus D.claims
      [P.zeta, P.chi, D.rm, gen ^ log2Ceil D.pushTotal, D.gzcn, P.cplen])
    (hpc : PC rd (columnKappas D.logMem 18 D.hs) P.off P.kap) (hK : HypKappa PC rd)
    (hlam : ReadsAt rd P.lam (powersFrom R.lam R.lam nClaims)) (hzv : ReadsAt rd P.zvals D.fpoint)
    (hct : ReadsAt rd P.ctab (ringCoefficients R.mcs))
    (hpt : ReadsAt rd P.pt (D.w.point ++ List.replicate (pointCap - D.w.point.length) 0)) :
    TermPre TC PC rd (layoutOf bytecode D.logMem D.rows) D.bus D.claims R.lam D.fpoint
      (ringCoefficients R.mcs) D.w [P.zeta, P.chi, D.rm, gen ^ log2Ceil D.pushTotal, D.gzcn,
        gen ^ D.logMem, gen ^ D.tau, P.cplen, P.lam, P.off, P.kap, P.zvals, P.ctab, P.pt, D.w.inner,
        D.w.residual, D.w.target] := by
  obtain ⟨hsl, hl28, -⟩ := stack_factsC hb hok
  refine ⟨htc, ?_, ?_, rfl, rfl, ?_, hzv, hct, hpt, rfl, rfl, rfl, ?_⟩
  · rw [layoutOf_logBytecode hb]; exact hpc
  · exact hK _ _ _ hpc hl28
  · rw [hok.claims_length]; exact hlam
  · refine ⟨by simp only [layoutOf], by simp only [layoutOf], hok.stack_le,
      by rw [layoutOf_logMemory]; have := hok.logMem_ge; omega, busPoint_lengthC hok, hok.open_point,
      ?_, by simp [ringCoefficients, kBits]⟩
    rw [layoutOf_heights]
    simp [VsData.fpoint, hok.rcs_length, hok.chi_length, VsData.tau, VsData.hs, opBlake2s]
    omega

end Facts

/-! ## The buffers and the layouts -/

/-- **The buffers' honest words at a run record** (`vsBufs`). -/
def vsBufsC (D : VsData) (R : VsRunC) : List (List E) :=
  [D.claims.map (·.value), cplenWords D, D.stream, D.rows.map eOfNat,
    gen ^ D.logMem :: D.hs.map (gen ^ ·), kappaBase (gen ^ D.logMem) (D.hs.map (gen ^ ·)),
    blockKappas (gen ^ D.logMem) (D.hs.map (gen ^ ·)), D.gr.2.1, R.alphas, eqKernel R.alphas, D.chis,
    D.chi, D.rcs, D.s, R.mcs, ringCoefficients R.mcs, D.fpoint, rsChainC D.s R.mcs,
    powersFrom R.lam R.lam nClaims]

/-- The caller's words `verify_sub` reads: the exponent tables and `defer_out`'s cells at the run
record's claims (`vsExtL`). -/
def vsExtLC (lpA sqA outA : ℕ) (D : VsData) (R : VsRunC) : Main.Layout :=
  expL lpA sqA ++ [(outA, Node.fixedCells (R.fresh D))]

/-- `verify_sub`'s own buffers at `fp` (`vsOwnL`). -/
def vsOwnLC (fs : String → ℕ) (fp : ℕ) (D : VsData) (R : VsRunC) : Main.Layout :=
  bufL (fp + fs "verify_sub") (vsSizes D) (vsBufsC D R)

/-- `verify_sub`'s own words and the caller's (`vsAllL`). -/
def vsAllLC (fs : String → ℕ) (D : VsData) (R : VsRunC) (fp lpA sqA outA : ℕ) : Main.Layout :=
  vsOwnLC fs fp D R ++ vsExtLC lpA sqA outA D R

theorem vsBufsC_ofD (D : VsData) : vsBufsC D (VsRunC.ofD D) = vsBufs D := by
  simp only [vsBufsC, vsBufs, VsRunC.alphas_ofD, VsRunC.mcs_ofD, VsRunC.lam_ofD, rsChainC_deployed]

theorem vsExtLC_ofD (lpA sqA outA : ℕ) (D : VsData) :
    vsExtLC lpA sqA outA D (VsRunC.ofD D) = vsExtL lpA sqA outA D := by
  simp only [vsExtLC, vsExtL, VsRunC.fresh_ofD]

section Memory

variable {CM : CompModel} {rd : Reader} {D : VsData} {R : VsRunC} {bytecode : List K}
  {fs : String → ℕ} {fp lpA sqA outA : ℕ} {off kap pt : E}

theorem vsMem0C_of (hL : MemL rd (vsOwnLC fs fp D R))
    (ho : ReadsAt rd (ofK (Parameters.gpow outA)) (Node.fixedCells (R.fresh D))) :
    VsMem0C rd D R (vsPtrsAt fs fp D off kap pt) (ofK (Parameters.gpow outA)) := by
  have g := fun i (hi : i < 19) xs (hx : (vsBufsC D R).getD i [] = xs) =>
    hx ▸ memL_bufL_get (i := i) hL (by simp [vsSizes]; omega) (by simp [vsBufsC]; omega)
  exact ⟨g 2 (by omega) _ (by simp [vsBufsC]), g 0 (by omega) _ (by simp [vsBufsC]),
    g 3 (by omega) _ (by simp [vsBufsC]), g 4 (by omega) _ (by simp [vsBufsC]),
    g 5 (by omega) _ (by simp [vsBufsC]), g 6 (by omega) _ (by simp [vsBufsC]),
    g 7 (by omega) _ (by simp [vsBufsC]), g 8 (by omega) _ (by simp [vsBufsC]),
    g 9 (by omega) _ (by simp [vsBufsC]), g 11 (by omega) _ (by simp [vsBufsC]),
    g 12 (by omega) _ (by simp [vsBufsC]), g 13 (by omega) _ (by simp [vsBufsC]),
    g 14 (by omega) _ (by simp [vsBufsC]), g 15 (by omega) _ (by simp [vsBufsC]),
    g 16 (by omega) _ (by simp [vsBufsC]), g 17 (by omega) _ (by simp [vsBufsC]),
    g 18 (by omega) _ (by simp [vsBufsC]), ho⟩

theorem cplen_ofC (hL : MemL rd (vsOwnLC fs fp D R)) :
    ReadsAt rd (vsPtrsAt fs fp D off kap pt).cplen (cplenWords D) := by
  have g := memL_bufL_get (i := 1) hL (by simp [vsSizes]) (by simp [vsBufsC])
  simp only [vsBufsC, List.getD_cons_succ, List.getD_cons_zero] at g
  exact g

theorem chis_ofC (hL : MemL rd (vsOwnLC fs fp D R)) :
    ReadsAt rd (vsPtrsAt fs fp D off kap pt).chi D.chis := by
  have g := memL_bufL_get (i := 10) hL (by simp [vsSizes]) (by simp [vsBufsC])
  simp only [vsBufsC, List.getD_cons_succ, List.getD_cons_zero] at g
  exact g

theorem vsAll_memC (h : MemL rd (vsAllLC fs D R fp lpA sqA outA)) :
    VsMem0C rd D R (vsPtrsAt fs fp D off kap pt) (ofK (Parameters.gpow outA)) ∧
      ExpTables rd (ofK (Parameters.gpow lpA)) (ofK (Parameters.gpow sqA)) ∧
      ReadsAt rd (vsPtrsAt fs fp D off kap pt).chi D.chis ∧
      ReadsAt rd (vsPtrsAt fs fp D off kap pt).cplen (cplenWords D) := by
  obtain ⟨h1, h2⟩ := Main.memL_append.mp h
  obtain ⟨h3, h4⟩ := Main.memL_append.mp h2
  exact ⟨vsMem0C_of h1 (h4 _ List.mem_cons_self), expTables_of h3, chis_ofC h1, cplen_ofC h1⟩

theorem gpwSq_memC (h : MemL rd (vsAllLC fs D R fp lpA sqA outA)) : MemL rd [(sqA, gpwSq)] := by
  have h2 := h (sqA, (List.range sizeBits).map fun j => gen ^ 2 ^ j)
    (by simp [vsAllLC, vsExtLC, expL])
  intro q hq
  simp only [List.mem_singleton] at hq
  subst hq
  intro j hj
  have := h2 j (by simp [gpwSq, sizeBits] at hj ⊢; omega)
  simpa [gpwSq] using this

theorem vsBufs_fitC (hok : D.OkC CM bytecode R) (htok : D.TOk bytecode) :
    List.Forall₂ (fun c s => c.length ≤ s) (vsBufsC D R) (vsSizes D) := by
  have hd : D.gr.2.1.length < 33 := by rw [hok.point_length]; exact hok.depth_lt
  have hτ := tau_ltC hok
  have hal : R.alphas.length = 4 := R.alphas_length
  simp only [vsBufsC, vsSizes, List.forall₂_cons, List.Forall₂.nil, and_true]
  refine ⟨by rw [List.length_map, hok.claims_length], by simp [cplenWords, hok.claims_length, nClaims],
    htok.stream_le, by simp [hok.rows_length], by simp [hs_lengthC hok],
    by simp [kappaBase, hs_lengthC hok], by simp [blockKappas], le_rfl, by omega,
    by rw [length_eqKernel, hal]; rfl, by have := htok.chis_le; omega, by rw [hok.chi_length]; omega,
    by rw [hok.rcs_length], by rw [hok.s_length], by rw [R.mcs_length],
    by simp [ringCoefficients, kBits], by simp [VsData.fpoint, hok.rcs_length, hok.chi_length]; omega,
    by rw [(rsChainC_at D.s R.mcs (j := 0) (by omega)).2.2], by rw [length_powersFrom]⟩

theorem fixedCells_lengthC (hb : bytecode.length = 2 ^ 22) (hok : D.OkC CM bytecode R) :
    (Node.fixedCells (R.fresh D)).length = 106 := by
  have := depth_geC hb hok
  have hal : R.alphas.length = 4 := R.alphas_length
  simp [Node.fixedCells, VsRunC.fresh, hal, hok.rcs_length, hok.s_length, hok.chi_length]
  omega

end Memory

/-! ## The honest calls -/

/-- **The calls of the honest run at a run record** (`vsTriples`). -/
noncomputable def vsTriplesC (bytecode : List K) (D : VsData) (R : VsRunC) (P : VsPtrs) (lp sq : E) :
    List (String × List E × List E) :=
  [("g_power_of_word__L6", [eOfNat D.rate, sq], [gen ^ D.rate]),
    ("g_power_of_word__L6", [eOfNat D.logMem, sq], [gen ^ D.logMem]),
    ("log2_ceil_in_the_exponent__L0_L34", [gen ^ D.pushTotal, lp, sq], [gen ^ log2Ceil D.pushTotal]),
    ("assert_canonical", [D.x0], [0]), ("assert_canonical", [D.x1], [0]),
    ("verify_bus_gkr", [(digestScalars R.cvB).1, (digestScalars R.cvB).2, curG P,
      gen ^ log2Ceil D.pushTotal, P.zeta],
      [(digestScalars D.cvG).1, (digestScalars D.cvG).2, curT D P, D.gr.2.2.getD 0 0,
        D.gr.2.2.getD 1 0, D.gr.2.2.getD 2 0]),
    ("verify_tables", [(digestScalars D.cvG).1, (digestScalars D.cvG).2, curT D P,
      (digestScalars D.pi).1, (digestScalars D.pi).2, P.zeta, gen ^ log2Ceil D.pushTotal, P.dims,
      P.rows, P.bk, sq, P.fpw, R.beta, P.pool, P.cplen, P.chi, D.gr.2.2.getD 0 0, D.gr.2.2.getD 1 0,
      D.gr.2.2.getD 2 0], [(digestScalars D.cvT).1, (digestScalars D.cvT).2, curF D P, D.gzcn, D.bv,
        D.rm]),
    ("verify_flock", [(digestScalars D.cvT).1, (digestScalars D.cvT).2, curF D P, gen ^ D.tau, P.zchis,
      P.lrs, P.zpart], [(digestScalars D.cvF).1, (digestScalars D.cvF).2, curW D P, D.zSkip, D.alpha,
        D.mv]),
    ("__loop84", [word 1 0 0, P.zpart, P.mcs, P.rs], []),
    ("__loop85", [word 1 0 0, gen ^ D.tau, P.zvals * word 256 0 0, P.zchis * word 256 0 0], []),
    ("certify_placement", [P.kbase, sq], [gen ^ D.stackTot, P.off, P.kap]),
    ("log2_ceil_in_the_exponent__L15_L34", [gen ^ D.stackTot, lp, sq],
      [gen ^ max 15 (log2Ceil D.stackTot)]),
    (openName (layoutOf bytecode D.logMem D.rows).stackLog D.rate,
      [(digestScalars R.cvL).1, (digestScalars R.cvL).2, R.target D, D.x0, D.x1, curW D P],
      [D.w.target, P.pt, D.w.inner, D.w.residual]),
    ("check_opening_terminal", [P.zeta, P.chi, D.rm, gen ^ log2Ceil D.pushTotal, D.gzcn,
      gen ^ D.logMem, gen ^ D.tau, P.cplen, P.lam, P.off, P.kap, P.zvals, P.ctab, P.pt, D.w.inner,
      D.w.residual, D.w.target], [])]

/-- **Membership in the honest calls at a run record**, as a call relation (`vsC`). -/
noncomputable def vsCC (bytecode : List K) (D : VsData) (R : VsRunC) (P : VsPtrs) (lp sq : E) : CallRel :=
  fun f a r => (f, a, r) ∈ vsTriplesC bytecode D R P lp sq

theorem vsCallsOkC_mem {bytecode : List K} {D : VsData} {R : VsRunC} {P : VsPtrs} {lp sq : E} :
    VsCallsOkC (vsCC bytecode D R P lp sq) bytecode D R P lp sq := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, fun _ => ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
    simp only [vsCC, vsTriplesC, List.mem_cons, true_or, or_true]

/-- **A path's entered frames hold of `C`** when its events do under `S` (`calls_ok`). -/
theorem calls_okB {S : BlakeSem} {C : CallRel} {rd : Reader} {σ : Val} {es : List Memory.Ev}
    (h : ∀ e ∈ es, e.OkB S C rd σ) :
    ∀ c ∈ calls es, c.taken = true → C c.f (c.args.map σ) (c.rets.map σ) := by
  intro c hc ht
  obtain ⟨e, he, hce⟩ := List.mem_filterMap.mp hc
  match e, hce with
  | .call f args rets, hce =>
    simp only [Ev.call?, Option.some.injEq] at hce
    subst hce
    exact (h _ he).2 f args rets rfl
  | .skip f args, hce =>
    simp only [Ev.call?, Option.some.injEq] at hce
    subst hce
    simp at ht

/-! ## The path -/

section Path

variable {CM : CompModel} {rd : Reader} {D : VsData} {R : VsRunC} {P : VsPtrs} {out lp sq : E}
  {bytecode : List K}

set_option maxRecDepth 100000 in
/-- **The honest path over the model** (`vs_run`): a valuation taking the run record's values, its
parameters the arguments, walks the body through `open_stacked__L{sel}`, every event holding under
`CM.sem` of the honest calls. -/
theorem vs_runC (hlow : LowDef 6 rd) (hb : bytecode.length = 2 ^ 22) (hR : R.Ans CM D)
    (hok : D.OkC CM bytecode R) (ht : ExpTables rd lp sq) (hm : VsMem0C rd D R P out) :
    ∃ (σ : Val) (sel : ℕ), sel < 28 ∧ Fixes σ (vsG11C D R P lp sq out) ∧
      (Fn.params Data.core15).map σ = [(digestScalars D.pi).1, (digestScalars D.pi).2,
        (digestScalars D.seed).1, (digestScalars D.seed).2, lp, sq, out] ∧
      walk σ (Fn.body Data.core15) = .ret (vsEvs σ sel) [] ∧
      (∀ e ∈ vsEvs σ sel, e.OkB CM.sem (vsCC bytecode D R P lp sq) rd σ) ∧
      Stmt.HoldsListB CM.sem (vsCC bytecode D R P lp sq) rd σ vsBody True (fun r => r = []) := by
  set σ0 := upds (fun _ => 0) (vsG0 D lp sq out)
  have h0 : Fixes σ0 (vsG0 D lp sq out) := by
    intro p hp; simp only [vsG0, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [σ0, vsG0, upds_n]
  obtain ⟨σ, he, hfix, hh⟩ :=
    vs_bodyC (C := vsCC bytecode D R P lp sq) hlow hb hR hok ht hm vsCallsOkC_mem σ0 h0
  have hH : Stmt.HoldsListB CM.sem (vsCC bytecode D R P lp sq) rd σ (vsBody ++ [.ret []]) True
      (fun r => r = []) := by
    rw [holdsListB_append]; exact hh _ _ rfl
  have hd := hH
  rw [vsBody_split, List.append_assoc, List.cons_append, holdsListB_append,
    holdsListB_noRet _ vsPre1_noRet] at hd
  obtain ⟨-, hd⟩ := hd
  simp only [Stmt.HoldsListB, vsDisp, Stmt.HoldsB] at hd
  obtain ⟨⟨sel, hsel, hx, -⟩, -⟩ := hd
  have hsel' : sel < 28 := by simpa [openNames] using hsel
  have hw := vs_walk σ hsel' hx
  have hwf : Stmt.wfList coreProgram (vsBody ++ [.ret []]) = true := by
    have := coreProgram_wf Data.core15 (List.mem_of_find?_eq_some find_verify_sub)
    rwa [core15_body'] at this
  have hs := walkB_sat _ hwf hH
  rw [hw] at hs
  refine ⟨σ, sel, hsel', hfix, ?_, by rw [core15_body']; exact hw, hs.1, hh _ _ trivial⟩
  have hp : ∀ k < 7, σ (.n k) = σ0 (.n k) := fun k hk => he.apply (Or.inl hk)
  simp only [core15_params, List.map_cons, List.map_nil, hp 0 (by omega), hp 1 (by omega),
    hp 2 (by omega), hp 3 (by omega), hp 4 (by omega), hp 5 (by omega), hp 6 (by omega)]
  simp [σ0, vsG0, upds_n]

/-- **The path's frames over the model** (`vs_calls`), the entered ones holding of the honest
calls. -/
theorem vs_callsC {σ : Val} {sel : ℕ}
    (h : ∀ e ∈ vsEvs σ sel, e.OkB CM.sem (vsCC bytecode D R P lp sq) rd σ) :
    calls (vsEvs σ sel) = (vsPre1.filterMap Main.Stmt.callS).map (Main.mkCall σ) ++
      [⟨openNames.getD sel "", [.n 1171, .n 1172, .n 1627, .n 419, .n 434, .n 726],
        [.n 1648, .n 1649, .n 1650, .n 1651], true⟩,
        ⟨"check_opening_terminal", [.n 418, .n 709, .n 715, .n 417, .n 713, .n 144, .n 718, .n 8,
          .n 1180, .n 1630, .n 1631, .n 734, .n 733, .n 1649, .n 1650, .n 1651, .n 1648], [],
          true⟩] ∧
      ∀ c ∈ calls (vsEvs σ sel), c.taken = true →
        (c.f, c.args.map σ, c.rets.map σ) ∈ vsTriplesC bytecode D R P lp sq := by
  refine ⟨?_, calls_okB h⟩
  rw [(vs_parts σ sel).2.2.2.1, vsPost2_calls]
  simp [Main.mkCall]

end Path

/-! ## The callees -/

variable (fs : String → ℕ) (bytecode : List K) (D : VsData) (R : VsRunC)

/-- **The calls before the dispatch at a run record** (`vsKids1`). -/
noncomputable def vsKids1C (fp lpA sqA outA : ℕ) : List Kid :=
  let P := vsPtrsAt fs fp D 0 0 0
  let lp := ofK (Parameters.gpow lpA)
  let sq := ofK (Parameters.gpow sqA)
  let LA := vsAllLC fs D R fp lpA sqA outA
  [⟨"g_power_of_word__L6", true, [eOfNat D.rate, sq], [(sqA, gpwSq)], Returns [gen ^ D.rate]⟩,
    ⟨"g_power_of_word__L6", true, [eOfNat D.logMem, sq], [(sqA, gpwSq)], Returns [gen ^ D.logMem]⟩,
    ⟨"log2_ceil_in_the_exponent__L0_L34", true, [gen ^ D.pushTotal, lp, sq], LA,
      Returns [gen ^ log2Ceil D.pushTotal]⟩,
    ⟨"assert_canonical", true, [D.x0], [], Returns [0]⟩,
    ⟨"assert_canonical", true, [D.x1], [], Returns [0]⟩,
    ⟨"verify_bus_gkr", true, [(digestScalars R.cvB).1, (digestScalars R.cvB).2, curG P,
      gen ^ log2Ceil D.pushTotal, P.zeta], LA,
      Returns [(digestScalars D.cvG).1, (digestScalars D.cvG).2, curT D P, D.gr.2.2.getD 0 0,
        D.gr.2.2.getD 1 0, D.gr.2.2.getD 2 0]⟩,
    ⟨"verify_tables", true, [(digestScalars D.cvG).1, (digestScalars D.cvG).2, curT D P,
      (digestScalars D.pi).1, (digestScalars D.pi).2, P.zeta, gen ^ log2Ceil D.pushTotal, P.dims,
      P.rows, P.bk, sq, P.fpw, R.beta, P.pool, P.cplen, P.chi, D.gr.2.2.getD 0 0, D.gr.2.2.getD 1 0,
      D.gr.2.2.getD 2 0], LA,
      Returns [(digestScalars D.cvT).1, (digestScalars D.cvT).2, curF D P, D.gzcn, D.bv, D.rm]⟩,
    ⟨"verify_flock", true, [(digestScalars D.cvT).1, (digestScalars D.cvT).2, curF D P, gen ^ D.tau,
      P.zchis, P.lrs, P.zpart], LA,
      Returns [(digestScalars D.cvF).1, (digestScalars D.cvF).2, curW D P, D.zSkip, D.alpha, D.mv]⟩,
    ⟨"__loop84", true, [word 1 0 0, P.zpart, P.mcs, P.rs], LA, Returns []⟩,
    ⟨"__loop85", decide (word 1 0 0 + gen ^ D.tau ≠ 0),
      [word 1 0 0, gen ^ D.tau, P.zvals * word 256 0 0, P.zchis * word 256 0 0], LA, Returns []⟩,
    ⟨"certify_placement", true, [P.kbase, sq], LA, PlaceOut D⟩,
    ⟨"log2_ceil_in_the_exponent__L15_L34", true, [gen ^ D.stackTot, lp, sq], LA,
      Returns [gen ^ max 15 (log2Ceil D.stackTot)]⟩]

/-- **The opening at a run record** (`vsOpenKid`). -/
noncomputable def vsOpenKidC (fp lpA sqA outA : ℕ) : Kid :=
  ⟨openName (layoutOf bytecode D.logMem D.rows).stackLog D.rate, true,
    [(digestScalars R.cvL).1, (digestScalars R.cvL).2, R.target D, D.x0, D.x1,
      curW D (vsPtrsAt fs fp D 0 0 0)], vsAllLC fs D R fp lpA sqA outA, OpenOutK D⟩

/-- **The terminal at a run record** (`vsTermKid`). -/
noncomputable def vsTermKidC (fp lpA sqA outA : ℕ) (off kap pt : E) (Lc Lo : Main.Layout) : Kid :=
  let P := vsPtrsAt fs fp D off kap pt
  ⟨"check_opening_terminal", true, [P.zeta, P.chi, D.rm, gen ^ log2Ceil D.pushTotal, D.gzcn,
    gen ^ D.logMem, gen ^ D.tau, P.cplen, P.lam, P.off, P.kap, P.zvals, P.ctab, P.pt, D.w.inner,
    D.w.residual, D.w.target], vsAllLC fs D R fp lpA sqA outA ++ Lc ++ Lo, Returns []⟩

variable {fs bytecode D R}

/-! ## The frames match their callees -/

/-- Read a call's words off the honest calls at a run record. -/
macro "vs_decC" h:ident : tactic => `(tactic| simp (config := { decide := true })
  [vsTriplesC, lit_ne_open, open_ne_lit, getD_ne_lit] at $h:ident)

section Match

variable {fp lpA sqA outA : ℕ} {off kap pt : E} {CM : CompModel}

/-- **The calls before the dispatch match their callees** (`match1`). -/
theorem match1C (hok : D.OkC CM bytecode R) {σ : Val}
    (hfix : Fixes σ (vsG11C D R (vsPtrsAt fs fp D off kap pt) (ofK (Parameters.gpow lpA))
      (ofK (Parameters.gpow sqA)) (ofK (Parameters.gpow outA))))
    (hT : ∀ c ∈ (vsPre1.filterMap Main.Stmt.callS).map (Main.mkCall σ), c.taken = true →
      (c.f, c.args.map σ, c.rets.map σ) ∈ vsTriplesC bytecode D R (vsPtrsAt fs fp D off kap pt)
        (ofK (Parameters.gpow lpA)) (ofK (Parameters.gpow sqA)))
    {outs : List (List E × Main.Layout)} (ho : OutsOk (vsKids1C fs D R fp lpA sqA outA) outs)
    (hpl : (outs.getD 10 ([], [])).1 = [gen ^ D.stackTot, off, kap]) :
    CallsMatch σ ((vsPre1.filterMap Main.Stmt.callS).map (Main.mkCall σ))
      (vsKids1C fs D R fp lpA sqA outA) outs := by
  obtain ⟨o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, rfl⟩ :=
    list12 (ho.length.trans (by simp [vsKids1C]))
  simp only [OutsOk, vsKids1C, Returns, forall_const] at ho
  obtain ⟨⟨r0, -⟩, ⟨r1, -⟩, ⟨r2, -⟩, ⟨r3, -⟩, ⟨r4, -⟩, ⟨r5, -⟩, ⟨r6, -⟩, ⟨r7, -⟩, ⟨r8, -⟩, h9, -,
    ⟨r11, -⟩, -⟩ := ho
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hpl
  rw [vsPre1_calls] at hT ⊢
  simp only [List.map_cons, List.map_nil, Main.mkCall, List.mem_cons, List.mem_nil_iff, or_false,
    forall_eq_or_imp, forall_eq, forall_const] at hT
  simp only [List.map_cons, List.map_nil, Main.mkCall, CallsMatch, vsKids1C]
  have e121 : σ (.n 121) = eOfNat D.rate := hfix.get (by vs_memC)
  have e15 : σ (.n 15) = eOfNat D.logMem := hfix.get (by vs_memC)
  have e5 : σ (.n 5) = ofK (Parameters.gpow sqA) := hfix.get (by vs_memC)
  have e419 : σ (.n 419) = D.x0 := hfix.get (by vs_memC)
  have e434 : σ (.n 434) = D.x1 := hfix.get (by vs_memC)
  have e1160 : σ (.n 1160) = word 1 0 0 + gen ^ D.tau := hfix.get (by vs_memC)
  have hne : (eOfNat D.rate = eOfNat D.logMem) = False := eq_false fun h => by
    have := eOfNat_inj (by have := hok.rate_le; omega) (by have := hok.logMem_le; omega) h
    have := hok.rate_le; have := hok.logMem_ge; omega
  have hne' : (eOfNat D.logMem = eOfNat D.rate) = False := eq_false fun h => of_eq_false hne h.symm
  clear hfix
  rw [e121, e5] at hT
  rw [e15, e419, e434, e1160] at hT
  obtain ⟨hT0, hT1, hT2, hT3, hT4, hT5, hT6, hT7, hT8, hT9, hT10, hT11⟩ := hT
  vs_decC hT0; vs_decC hT1; vs_decC hT2; vs_decC hT3; vs_decC hT4; vs_decC hT5; vs_decC hT6
  vs_decC hT7; vs_decC hT8; vs_decC hT9; vs_decC hT10; vs_decC hT11
  simp only [hne, hne', false_and, or_false] at hT0 hT1
  replace hT3 : σ (.n 449) = 0 := Or.elim hT3 id And.right
  replace hT4 : σ (.n 450) = 0 := Or.elim hT4 And.right id
  simp only [vsPtrsAt, curG, curT, curF, curW] at *
  simp_all

/-- **The opening matches its callee** (`matchOpen`). -/
theorem matchOpenC {σ : Val} {sel : ℕ}
    (hT : (openNames.getD sel "", [σ (.n 1171), σ (.n 1172), σ (.n 1627), σ (.n 419), σ (.n 434),
      σ (.n 726)], [σ (.n 1648), σ (.n 1649), σ (.n 1650), σ (.n 1651)]) ∈
        vsTriplesC bytecode D R (vsPtrsAt fs fp D off kap pt) (ofK (Parameters.gpow lpA))
          (ofK (Parameters.gpow sqA)))
    {o : List E × Main.Layout} (hpt : o.1 = [D.w.target, pt, D.w.inner, D.w.residual]) :
    CallsMatch σ [⟨openNames.getD sel "", [.n 1171, .n 1172, .n 1627, .n 419, .n 434, .n 726],
      [.n 1648, .n 1649, .n 1650, .n 1651], true⟩] [vsOpenKidC fs bytecode D R fp lpA sqA outA] [o] := by
  vs_decC hT
  simp only [vsPtrsAt, curG, curT, curF, curW] at *
  simp only [CallsMatch, vsOpenKidC, vsPtrsAt, curG, curT, curF, curW, List.map_cons, List.map_nil]
  simp_all

/-- **The terminal matches its callee** (`matchTerm`). -/
theorem matchTermC {σ : Val} {Lc Lo : Main.Layout}
    (hT : ("check_opening_terminal", [σ (.n 418), σ (.n 709), σ (.n 715), σ (.n 417), σ (.n 713),
      σ (.n 144), σ (.n 718), σ (.n 8), σ (.n 1180), σ (.n 1630), σ (.n 1631), σ (.n 734), σ (.n 733),
      σ (.n 1649), σ (.n 1650), σ (.n 1651), σ (.n 1648)], []) ∈
        vsTriplesC bytecode D R (vsPtrsAt fs fp D off kap pt) (ofK (Parameters.gpow lpA))
          (ofK (Parameters.gpow sqA)))
    {o : List E × Main.Layout} (hr : o.1 = []) :
    CallsMatch σ [⟨"check_opening_terminal", [.n 418, .n 709, .n 715, .n 417, .n 713, .n 144, .n 718,
      .n 8, .n 1180, .n 1630, .n 1631, .n 734, .n 733, .n 1649, .n 1650, .n 1651, .n 1648], [], true⟩]
      [vsTermKidC fs D R fp lpA sqA outA off kap pt Lc Lo] [o] := by
  vs_decC hT
  simp only [vsPtrsAt] at *
  simp only [CallsMatch, vsTermKidC, vsPtrsAt, List.map_cons, List.map_nil]
  simp_all

end Match

/-! ## The buffers placed and the loads -/

section Loads

variable {fp lpA sqA outA : ℕ} {off kap pt : E} {CM : CompModel}

theorem vs_allocsC (hb : bytecode.length = 2 ^ 22) (hok : D.OkC CM bytecode R) {σ : Val}
    {lp sq out : E} (hfix : Fixes σ (vsG11C D R (vsPtrsAt fs fp D off kap pt) lp sq out)) (sel : ℕ) :
    allocs σ (vsEvs σ sel) = vsSizes D ∧
      (allocDsts (vsEvs σ sel)).map σ =
        (bases (fp + fs "verify_sub") (vsSizes D)).map fun b => ofK (Parameters.gpow b) := by
  obtain ⟨h1, h2, -⟩ := vs_parts σ sel
  rw [vsPre1_allocs] at h1 h2
  have e417 : σ (.n 417) = gen ^ log2Ceil D.pushTotal := hfix.get (by vs_memC)
  have e720 : σ (.n 720) = ofK (Parameters.gpow (D.tau + 8)) := by
    rw [hfix.get (k := 720) (e := gen ^ D.tau * word 256 0 0) (by vs_memC),
      show word 256 0 0 = gen ^ 8 from word_two_pow (a := 8) (by decide), ← pow_add, gen_pow_eq_ofK]
  have hA : Fixes σ (allocFix (vsPtrsAt fs fp D off kap pt)) := hfix.sub (by
    intro p hp; simp only [allocFix, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;> vs_memC)
  have hl : log2Ceil D.pushTotal < 2 ^ 64 - 1 := by
    have := (pushTotal_boundsC hb hok).2; omega
  refine ⟨?_, ?_⟩
  · rw [h2]
    simp only [List.map_cons, List.map_nil, Sum.elim_inl, Sum.elim_inr, id, e417, e720,
      gen_pow_eq_ofK, logG_spec hl,
      logG_spec (show D.tau + 8 < 2 ^ 64 - 1 by have := tau_ltC hok; omega)]
    rw [← depth_eqC hb hok]
    rfl
  · rw [h1]
    simp only [allocFix, Fixes, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
      forall_eq] at hA
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩ := hA
    simp only [List.map_cons, List.map_nil, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12,
      a13, a14, a15, a16, a17, a18, vsPtrsAt, vsBases, vsSizes, bases]
    simp

/-- **Each load of the body reads `verify_sub`'s buffers or the caller's words** (`vs_load`). -/
theorem vs_loadC (hb : bytecode.length = 2 ^ 22) (hok : D.OkC CM bytecode R) {σ : Val}
    (hfix : Fixes σ (vsG11C D R (vsPtrsAt fs fp D off kap pt) (ofK (Parameters.gpow lpA))
      (ofK (Parameters.gpow sqA)) (ofK (Parameters.gpow outA))))
    (q : V × ℕ) (hq : loadOkB q = true) :
    ∃ i, (σ q.1).limb 0 * Parameters.gpow q.2 = Parameters.gpow i ∧
      (InBuf fs fp D i ∨ RegionL (vsExtLC lpA sqA outA D R) i) := by
  set P := vsPtrsAt fs fp D off kap pt
  have own : ∀ t, t < 19 → ∀ v, σ (.n v) = ofK (Parameters.gpow (vsB fs fp D t)) → ∀ o,
      o < (vsSizes D).getD t 0 → ∃ i, (σ (.n v)).limb 0 * Parameters.gpow o = Parameters.gpow i ∧
        (InBuf fs fp D i ∨ RegionL (vsExtLC lpA sqA outA D R) i) :=
    fun t ht v hv o ho => ⟨vsB fs fp D t + o, by rw [hv, Main.addr_ofK],
      Or.inl ⟨t, ht, by omega, by omega⟩⟩
  have hd := depth_geC hb hok
  have hτ := tau_ltC hok
  obtain ⟨p, o⟩ := q
  simp only [loadOkB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.any_eq_true, List.mem_range, or_assoc] at hq
  rcases hq with ⟨rfl, ho⟩ | ⟨rfl, ho⟩ | ⟨rfl, ho⟩ | ⟨rfl, ho⟩ | ⟨rfl, ho⟩ | ⟨rfl, ho⟩ | ⟨rfl, ho⟩ |
    ⟨rfl, ho⟩ | ⟨rfl, ho⟩ | ⟨rfl, ho⟩ | ⟨rfl, ho⟩ | ⟨rfl, ho⟩ | ⟨rfl, ho⟩ | ⟨rfl, ho⟩ | ⟨rfl, ho⟩ |
    ⟨rfl, ho⟩ | ⟨rfl, rfl⟩ | ⟨rfl, ho⟩ | ⟨rfl, ho⟩ | ⟨⟨b, hb37, rfl⟩, rfl⟩
  · exact own 0 (by omega) 7 (hfix.get (k := 7) (e := P.pool) (by vs_memC)) _ (by simp [vsSizes]; omega)
  · exact own 2 (by omega) 14 (hfix.get (k := 14) (e := P.stream) (by vs_memC)) _
      (by simp [vsSizes]; omega)
  · exact own 3 (by omega) 30 (hfix.get (k := 30) (e := P.rows) (by vs_memC)) _
      (by simp [vsSizes]; omega)
  · exact own 4 (by omega) 143 (hfix.get (k := 143) (e := P.dims) (by vs_memC)) _
      (by simp [vsSizes]; omega)
  · exact own 5 (by omega) 155 (hfix.get (k := 155) (e := P.kbase) (by vs_memC)) _
      (by simp [vsSizes]; omega)
  · exact own 6 (by omega) 163 (hfix.get (k := 163) (e := P.bk) (by vs_memC)) _
      (by simp [vsSizes]; omega)
  · exact own 7 (by omega) 418 (hfix.get (k := 418) (e := P.zeta) (by vs_memC)) _
      (by simp [vsSizes]; omega)
  · exact own 8 (by omega) 451 (hfix.get (k := 451) (e := P.alpha) (by vs_memC)) _
      (by simp [vsSizes]; omega)
  · exact own 9 (by omega) 508 (hfix.get (k := 508) (e := P.fpw) (by vs_memC)) _
      (by simp [vsSizes]; omega)
  · exact own 11 (by omega) 721 (hfix.get (k := 721) (e := P.zchis) (by vs_memC)) _
      (by simp [vsSizes]; omega)
  · exact own 12 (by omega) 722 (hfix.get (k := 722) (e := P.lrs) (by vs_memC)) _
      (by simp [vsSizes]; omega)
  · exact own 13 (by omega) 723 (hfix.get (k := 723) (e := P.zpart) (by vs_memC)) _
      (by simp [vsSizes]; omega)
  · exact own 14 (by omega) 732 (hfix.get (k := 732) (e := P.mcs) (by vs_memC)) _
      (by simp [vsSizes]; omega)
  · exact own 15 (by omega) 733 (hfix.get (k := 733) (e := P.ctab) (by vs_memC)) _
      (by simp [vsSizes]; omega)
  · exact own 16 (by omega) 734 (hfix.get (k := 734) (e := P.zvals) (by vs_memC)) _
      (by simp [vsSizes]; omega)
  · exact own 17 (by omega) 1144 (hfix.get (k := 1144) (e := P.rs) (by vs_memC)) _
      (by simp [vsSizes]; omega)
  · have h1149 : σ (.n 1149) = ofK (Parameters.gpow (vsB fs fp D 17 + 128)) := by
      have hrs : P.rs = ofK (Parameters.gpow (vsB fs fp D 17)) := rfl
      rw [hfix.get (k := 1149) (e := P.rs * word 325 0 0) (by vs_memC), word325, gen_pow_eq_ofK, hrs,
        ← Parameters.ofK_mul, Parameters.gpow, Parameters.gpow, ← pow_add]
    refine ⟨vsB fs fp D 17 + 128 + 1, by rw [h1149, Main.addr_ofK], Or.inl ⟨17, by omega, by omega, ?_⟩⟩
    simp [vsSizes]
  · exact own 18 (by omega) 1180 (hfix.get (k := 1180) (e := P.lam) (by vs_memC)) _
      (by simp [vsSizes]; omega)
  · have h6 : σ (.n 6) = ofK (Parameters.gpow outA) := hfix.get (by vs_memC)
    refine ⟨outA + o, by rw [h6, Main.addr_ofK], Or.inr ⟨(outA, Node.fixedCells (R.fresh D)),
      by simp [vsExtLC], by simp, by simp [fixedCells_lengthC hb hok]; omega⟩⟩
  · have hk : pkap D b < 34 := by
      have := pushKappas_le D.logMem D.hs (hs_lengthC hok) hok.logMem_le (hs_ltC hok) b hb37
      unfold pkap; omega
    have hp : σ (.n (pushK b + 1)) = ofK (Parameters.gpow (sqA + pkap D b)) := by
      rw [hfix.get (k := pushK b + 1) (e := ofK (Parameters.gpow sqA) * gen ^ pkap D b)
        (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
          (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _
            (List.mem_append_right _ (List.mem_map.mpr ⟨b, List.mem_range.mpr (by omega), rfl⟩))))))))]
      rw [gen_pow_eq_ofK, ← Parameters.ofK_mul, Parameters.gpow, Parameters.gpow, ← pow_add]
    refine ⟨sqA + pkap D b + 0, by rw [hp, Main.addr_ofK], Or.inr ⟨(sqA, (List.range sizeBits).map
      fun j => gen ^ 2 ^ j), by simp [vsExtLC, expL], by simp, by simp [sizeBits]; omega⟩⟩

end Loads

end
end LeanVM.Guest.B1.VerifySub
