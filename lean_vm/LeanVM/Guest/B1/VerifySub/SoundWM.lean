/-
  LeanVM.Guest.B1.VerifySub.SoundWM

  `verify_sub`'s soundness over a hash model with its witnesses named: the public input, the
  seed, the fixed claims and the child proof as explicit functions of its valuation, the openings
  from `open_stacked`'s witness function.
-/

module

public import LeanVM.Guest.B1.VerifySub.SoundM
public import LeanVM.Guest.B1.VerifySub.ConsumeM
public import LeanVM.Guest.B1.VerifySub.SoundW

/-!
# `verify_sub` is sound over a hash model, its witnesses named

`SoundW.lean` over a hash model `M`. The witnesses are `SoundW.lean`'s (`vsPiOf`, `vsSeedOf`,
`vsFreshOf`, `vsProofOf`): they are read off the valuation and the memory, and do not depend on
the hash. `VsOutcomeM M` is `VsOutcome` with the deferring verifier over the model's hash
(`verifyDeferredWith M.H … = some true`).

`verify_sub_sound_wCM`: for a call relation `C` below the program's under `M.sem`, over the
hashing callees' soundness over the model (`open_stacked`'s with the witness function `wO` over
`C`, `SoundOpenWCM`) and the others' as deployed, every valuation of `verify_sub`'s body under
`M.sem` with its calls in `C` gives `VsOutcomeM`. The stream's length is what the phases read
(`RunsToM.length_eq`, `RunsWithM.length_eq` with `Consume.lean`'s counts).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {S : BlakeSem} {M : HashModel} {rd : Reader} {σ : Val}

/-- **What `verify_sub` establishes over a hash model, its witnesses named** (`VsOutcome` over
`M.H`). -/
def VsOutcomeM (M : HashModel) (bytecode : List K) (rd : Reader) (σ : Val)
    (wO : String → List E → List E → List Opening) : Prop :=
  (σ (.n 0), σ (.n 1)) = digestScalars (vsPiOf σ) ∧ (σ (.n 2), σ (.n 3)) = digestScalars (vsSeedOf σ) ∧
    FreshShaped (vsFreshOf σ) ∧ ReadsAt rd (σ (.n 6)) (Node.fixedCells (vsFreshOf σ)) ∧
    verifyDeferredWith M.H bytecode (vsSeedOf σ) (vsPiOf σ) (vsFreshOf σ)
      (vsProofOf bytecode rd σ wO) = some true

/-- At the deployed model the outcome is `VsOutcome`. -/
theorem vsOutcomeM_deployed {bytecode : List K} {wO : String → List E → List E → List Opening} :
    VsOutcomeM HashModel.deployed bytecode rd σ wO ↔ VsOutcome bytecode rd σ wO := by
  simp only [VsOutcomeM, VsOutcome, verifyDeferredWith_deployed]

/-! ## The copies to `defer_out` -/

/-- The first load of each copy to `defer_out`, under `S` (`vs_copies`). -/
theorem vs_copiesB (h : VsHoldsB S rd σ) :
    (∀ k < 18, LoadHolds rd (σ (.n 418)) k (σ (.n (1652 + k)))) ∧
      (∀ k < 4, LoadHolds rd (σ (.n 451)) k (σ (.n (1670 + k)))) ∧
      (∀ k < 8, LoadHolds rd (σ (.n 721)) k (σ (.n (1674 + 2 * k)))) ∧
      (∀ k < 8, LoadHolds rd (σ (.n 722)) k (σ (.n (1675 + 2 * k)))) ∧
      ∀ k < 64, LoadHolds rd (σ (.n 723)) k (σ (.n (1690 + k))) := by
  have hz : ∀ k < 18, (stmtsEqb [.atom (.load (.n (1652 + k)) (.n 418) k)]
      ((vsPre.drop (1928 + 2 * k)).take 1) &&
      Stmt.freeInList vsFree [.atom (.load (.n (1652 + k)) (.n 418) k)]) = true := by
    decide +kernel
  have ha : ∀ k < 4, (stmtsEqb [.atom (.load (.n (1670 + k)) (.n 451) k)]
      ((vsPre.drop (1964 + 2 * k)).take 1) &&
      Stmt.freeInList vsFree [.atom (.load (.n (1670 + k)) (.n 451) k)]) = true := by
    decide +kernel
  have hc : ∀ k < 8, (stmtsEqb [.atom (.load (.n (1674 + 2 * k)) (.n 721) k)]
      ((vsPre.drop (1975 + 4 * k)).take 1) &&
      Stmt.freeInList vsFree [.atom (.load (.n (1674 + 2 * k)) (.n 721) k)]) = true := by
    decide +kernel
  have hr : ∀ k < 8, (stmtsEqb [.atom (.load (.n (1675 + 2 * k)) (.n 722) k)]
      ((vsPre.drop (1977 + 4 * k)).take 1) &&
      Stmt.freeInList vsFree [.atom (.load (.n (1675 + 2 * k)) (.n 722) k)]) = true := by
    decide +kernel
  have hs : ∀ k < 64, (stmtsEqb [.atom (.load (.n (1690 + k)) (.n 723) k)]
      ((vsPre.drop (2007 + 2 * k)).take 1) &&
      Stmt.freeInList vsFree [.atom (.load (.n (1690 + k)) (.n 723) k)]) = true := by
    decide +kernel
  exact ⟨fun k hk => h.atomF _ _ (hz k hk), fun k hk => h.atomF _ _ (ha k hk),
    fun k hk => h.atomF _ _ (hc k hk), fun k hk => h.atomF _ _ (hr k hk),
    fun k hk => h.atomF _ _ (hs k hk)⟩

/-- The claims `verify_sub` exports are the values it copies, under `S` (`vs_fresh_eq`). -/
theorem vs_fresh_eqB (h : VsHoldsB S rd σ) {P alphas chi rcs s : List E} (hP : 18 ≤ P.length)
    (hPr : ReadsAt rd (σ (.n 418)) P) (hal : alphas.length = 4) (har : ReadsAt rd (σ (.n 451)) alphas)
    (hcl : 8 ≤ chi.length) (hcr : ReadsAt rd (σ (.n 721)) chi) (hrl : rcs.length = 8)
    (hrr : ReadsAt rd (σ (.n 722)) rcs) (hsl : s.length = 64) (hsr : ReadsAt rd (σ (.n 723)) s) :
    (⟨P.take 18 ++ alphas, σ (.n 714), σ (.n 728), σ (.n 727), chi.take 8, rcs.reverse, s,
      σ (.n 729)⟩ : FixedClaims) = vsFreshOf σ := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := vs_copiesB h
  have hP' : ReadsAt rd (σ (.n 418)) (P.take 18) := fun k hk => by
    rw [List.getElem_take]; exact hPr k (by simp at hk; omega)
  have hc' : ReadsAt rd (σ (.n 721)) (chi.take 8) := fun k hk => by
    rw [List.getElem_take]; exact hcr k (by simp at hk; omega)
  rw [vsFreshOf, map_range_eq_of_loads (by simp; omega) hP' c1, map_range_eq_of_loads hal har c2,
    map_range_eq_of_loads (by simp; omega) hc' c3, map_range_eq_of_loads hrl hrr c4,
    map_range_eq_of_loads hsl hsr c5]

/-! ## The theorem -/

/-- **`verify_sub` is sound over a hash model, its witnesses named** (TRIAGE #44;
`verify_sub_sound_wC` over `M`): on a memory of `2^κ` words, `6 ≤ κ ≤ 32`, over the exponent
tables, for a bytecode of `2^22` words, for a call relation `C` below the program's under
`M.sem`, given the hashing callees' soundness over the model, `open_stacked`'s with the witness
function `wO` over `C`, and the others' as deployed, every valuation of `verify_sub`'s body under
`M.sem` with its calls in `C` gives `VsOutcomeM`. -/
theorem verify_sub_sound_wCM {C : CallRel} {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (Lm : MemImage κ)
    (hCle : CallRel.Le C (coreProgram.RelB M.sem Lm.read)) {bytecode : List K}
    (hb : bytecode.length = 2 ^ 22)
    {TCtx : Reader → Layout → BusResult → List ColumnClaim → List E → Prop}
    {PCtx : Reader → List ℕ → E → E → Prop}
    (hgkr : SoundGkrM M Lm.read) (htab : SoundTablesM M bytecode TCtx Lm.read)
    (hfl : SoundFlockM M Lm.read) (hpl : SoundPlace PCtx Lm.read) (hkap : HypKappa PCtx Lm.read)
    {wO : String → List E → List E → List Opening} (hop : SoundOpenWCM M Lm.read C wO)
    (hterm : SoundTerm TCtx PCtx Lm.read) (hvC : VsHoldsCB M.sem C Lm.read σ)
    (ht : ExpTables Lm.read (σ (.n 4)) (σ (.n 5))) :
    VsOutcomeM M bytecode Lm.read σ wO := by
  have hv := hvC.rel hCle
  -- the seed, the sizes, the root
  obtain ⟨seed, pi, cvS, hseed, hpi, hS, h12⟩ := vs_seedM (hv.to 2136) (by decide)
  obtain ⟨hrd, hst, hrows⟩ := vs_readsM hv h12
  obtain ⟨r, hr1, hr2, h121, h138⟩ := vs_rateB hκ hκ6 Lm hv ht
  obtain ⟨m, hm1, hm2, h15, h144⟩ := vs_logMemB hκ hκ6 Lm (hv.to 2136) (by decide) ht
  obtain ⟨cvA, hA, h134⟩ := hst 8 le_rfl
  obtain ⟨l8, l9, ⟨cv10, h10, h447⟩, root, hroot⟩ := vs_rootM hv h134
  obtain ⟨hdims, hbase, hbk⟩ := vs_kappasB (hv.to 2136) (by decide)
  -- the bus challenges
  obtain ⟨alphas, cvB, hB, har, h499⟩ := vs_alphasM hv h447
  have hal : alphas.length = 4 := sqAllM_length hB
  have hfpw := vs_fpwB (hv.to 2136) (by decide) hal har
  obtain ⟨cvC, hC, h690, h698, h700⟩ := vs_betaM hv h499
  -- GKR
  have cG := hv.call 806 "verify_bus_gkr" [.n 690, .n 691, .n 700, .n 417, .n 418]
    [.n 701, .n 702, .n 703, .n 704, .n 705, .n 706] (by decide +kernel)
  simp only [List.map_cons, List.map_nil] at cG
  obtain ⟨cvG0, depth, xsG, gr, cvG, hcvG0, h417, hdepth, hxsG, hrunG, hptl, hvl, hzeta, hretsG⟩ :=
    hgkr _ _ _ _ _ _ cG
  rw [h690] at hcvG0
  have ecvG0 := digestScalars_injective hcvG0
  subst ecvG0
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at hretsG
  obtain ⟨r701, r702, r703, hgr⟩ := hretsG
  have e707 := hv.atomF 807 (.copy (.n 707) (.n 701)) (by decide +kernel)
  have e708 := hv.atomF 808 (.copy (.n 708) (.n 702)) (by decide +kernel)
  simp only [Atom.Holds] at e707 e708
  -- the tables
  have cT := hv.call 810 "verify_tables" [.n 707, .n 708, .n 703, .n 0, .n 1, .n 418, .n 417,
    .n 143, .n 30, .n 163, .n 5, .n 508, .n 698, .n 7, .n 8, .n 709, .n 704, .n 705, .n 706]
    [.n 710, .n 711, .n 712, .n 713, .n 714, .n 715] (by decide +kernel)
  simp only [List.map_cons, List.map_nil] at cT
  rw [h144] at hdims hbk hbase
  have hpre : TablesPre Lm.read (σ (.n 4)) pi m alphas gr.2.1 gr.2.2
      [σ (.n 707), σ (.n 708), σ (.n 703), σ (.n 0), σ (.n 1), σ (.n 418), σ (.n 417),
        σ (.n 143), σ (.n 30), σ (.n 163), σ (.n 5), σ (.n 508), σ (.n 698), σ (.n 7), σ (.n 8),
        σ (.n 709), σ (.n 704), σ (.n 705), σ (.n 706)] :=
    ⟨hpi, hzeta, by rw [h417, hptl], by omega, hm1, hm2,
      ⟨dimsWords σ, by simp [dimsWords], hdims, hbk⟩, ht, hal, hfpw, hgr.symm⟩
  obtain ⟨cvT0, xsT, cvT, rowsN, bus, claims, hcvT0, hrl, hrowsR, hdimsR, hlogs, hxsT, hrunT,
    hcl, hpool, hctx, hfsT, hcurT⟩ := htab _ _ _ _ _ _ _ _ hpre cT
  rw [e707, e708, r701, r702] at hcvT0
  have ecvT0 := digestScalars_injective hcvT0
  subst ecvT0
  -- the rows and their heights
  have hrowsW : ∀ t < 6, σ (.n (rdB (t + 1))) = eOfNat (rowsN.getD t 0) := fun t ht' => by
    rw [List.getD_eq_getElem _ _ (by omega)]
    have := hrowsR t (by simp [hrl]; omega)
    rw [List.getElem_map] at this
    exact loadHolds_unique (hrows t ht') this
  have hann := readWords_eq σ hrl h15 h121 hrowsW
  rw [hann] at hA
  have hdw : dimsWords σ = (rowsN.map log2Ceil).map (gen ^ ·) := by
    have := readsAt_unique (by simp [dimsWords, hrl]) hdims hdimsR
    rw [List.cons.injEq] at this
    rw [this.2, List.map_map]
    rfl
  have hhs : ∀ h ∈ rowsN.map log2Ceil, h < 29 := by
    intro x hx; obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx; exact hlogs n hn
  have hhl : (rowsN.map log2Ceil).length = 6 := by simp [hrl]
  -- the bus depth
  obtain ⟨N, hN, h416, hlN, h417'⟩ := vs_busMuB hκ hκ6 Lm hv ht
  have hS' := vs_depthB hv ht hm2 hhl hhs h144 hdw
  have hSlt : ((pushKappas m (rowsN.map log2Ceil)).map (2 ^ ·)).sum ≤ 37 * 2 ^ 32 := by
    have := sum_le_of_le ((pushKappas m (rowsN.map log2Ceil)).map (2 ^ ·)) (2 ^ 32) (by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
      obtain ⟨b, hb', rfl⟩ := List.getElem_of_mem hk
      have := pushKappas_le m _ hhl hm2 hhs b (by rw [pushKappas_length m _ hhl] at hb'; exact hb')
      rw [List.getD_eq_getElem _ _ hb'] at this
      exact Nat.pow_le_pow_right (by decide) this)
    rwa [List.length_map, pushKappas_length m _ hhl] at this
  rw [h416] at hS'
  have eN := gen_pow_inj (by omega) (by omega) hS'
  rw [h417'] at h417
  have edepth := gen_pow_inj (by omega) (by omega) h417
  have hpd := pushDepth_eq hb m rowsN hrl
  rw [← eN] at hpd
  rw [← hpd] at edepth
  have hd18 : 18 ≤ depth := by
    rw [← edepth, hpd, eN]
    have : 2 ^ 17 < ((pushKappas m (rowsN.map log2Ceil)).map (2 ^ ·)).sum := by
      simp only [pushKappas, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      have := Nat.one_le_two_pow (n := m)
      omega
    exact log2Ceil_ge this
  -- Flock
  have e710 := hv.atomF 811 (.copy (.n 716) (.n 710)) (by decide +kernel)
  have e711 := hv.atomF 812 (.copy (.n 717) (.n 711)) (by decide +kernel)
  have l718 := hv.atomF 813 (.load (.n 718) (.n 143) 6) (by decide +kernel)
  simp only [Atom.Holds] at e710 e711 l718
  have h718 : σ (.n 718) = gen ^ (rowsN.map log2Ceil).getD 5 0 := by
    have := hdimsR 6 (by simp [hrl])
    rw [loadHolds_unique l718 this]
    simp only [List.getElem_cons_succ, List.getElem_map]
    rw [List.getD_eq_getElem _ _ (by simp [hrl]), List.getElem_map]
  have hτ : (rowsN.map log2Ceil).getD 5 0 < 29 := by
    rw [List.getD_eq_getElem _ _ (by simp [hrl])]
    exact hhs _ (List.getElem_mem _)
  have cF := hv.call 819 "verify_flock" [.n 716, .n 717, .n 712, .n 718, .n 721, .n 722, .n 723]
    [.n 724, .n 725, .n 726, .n 727, .n 728, .n 729] (by decide +kernel)
  simp only [List.map_cons, List.map_nil] at cF
  rw [h718] at cF
  obtain ⟨cvF0, xsF, cvF, zSkip, alpha, mv, chi, rcs, sl, hcvF0, hxsF, hchil, hrcsl, hsll, hchi,
    hrcs, hsr, hrunF, hretsF⟩ := hfl _ _ _ _ _ _ _ _ hτ cF
  rw [e710, e711, hfsT] at hcvF0
  have ecvF0 := digestScalars_injective hcvF0
  subst ecvF0
  simp only [List.cons.injEq] at hretsF
  obtain ⟨r724, r725, r726, r727, r728, r729, -⟩ := hretsF
  -- the ring switch
  have e724 := hv.atomF 820 (.copy (.n 730) (.n 724)) (by decide +kernel)
  have e725 := hv.atomF 821 (.copy (.n 731) (.n 725)) (by decide +kernel)
  simp only [Atom.Holds] at e724 e725
  have h730 : (σ (.n 730), σ (.n 731)) = digestScalars cvF := by rw [e724, e725, r724, r725]
  obtain ⟨mcs, cvR, hR, hmc, h810⟩ := vs_mapChallengesM hv h730
  have hmcl : mcs.length = 6 := sqAllM_length hR
  have hct := vs_ctableB hv hmcl hmc
  have htr := vs_transposedB hv hsll hsr hmcl hmc
  have hzv := vs_zvalsB hv hτ h718 hchil hrcsl hchi hrcs
  -- the batching
  obtain ⟨cvL, hL, h1171, h1179, hlp, h1627⟩ :=
    vs_lamM hv h810 (by rw [List.length_map, hcl]) hpool
  rw [htr, List.length_map] at h1627
  -- the placement and the stack's size
  have cP := hv.callF 1913 "certify_placement" [.n 155, .n 5] [.n 1629, .n 1630, .n 1631]
    (by decide +kernel)
  simp only [List.map_cons, List.map_nil] at cP
  rw [hdw] at hbase
  obtain ⟨off, kap, hretsP, hpctx⟩ := hpl _ _ _ m _ _ ht hm2 hhl hhs hbase cP
  simp only [List.cons.injEq] at hretsP
  obtain ⟨r1629, r1630, r1631, -⟩ := hretsP
  obtain ⟨N2, hN2, h1629, hμ1, hμ2, hopen⟩ :=
    vs_stackSelCB hκ hκ6 Lm hCle hvC ht hr1 hr2 h138
  have hST := stackTotal_lt m (rowsN.map log2Ceil) hm2 hhs
  rw [r1629] at h1629
  have eST := gen_pow_inj (by omega) (by omega) h1629
  rw [← eST] at hμ1 hμ2 hopen
  have hsl : (layoutOf bytecode m rowsN).stackLog =
      max 15 (log2Ceil (stackTotal (columnKappas m 18 (rowsN.map log2Ceil)))) :=
    stackLog_eq hb m rowsN
  rw [← hsl] at hμ1 hμ2 hopen
  -- the opening, at the openings `wO` names
  obtain ⟨cvW0, xsW, w, cvW, roots', hcvW0, hxsW, hrunW, pt, hretsW, hpt, hwl⟩ :=
    hop _ _ hμ1 hμ2 hr1 hr2 root _ _ _ _ _ _ _ hroot hopen
  generalize hos : wO (openName (layoutOf bytecode m rowsN).stackLog r)
    [σ (.n 1171), σ (.n 1172), σ (.n 1627), σ (.n 419), σ (.n 434), σ (.n 726)]
    [σ (.n 1648), σ (.n 1649), σ (.n 1650), σ (.n 1651)] = os at hrunW
  rw [h1171] at hcvW0
  have ecvW0 := digestScalars_injective hcvW0
  subst ecvW0
  simp only [List.cons.injEq] at hretsW
  obtain ⟨r1648, r1649, r1650, r1651, -⟩ := hretsW
  -- the terminal
  have hkb := hkap _ _ _ hpctx (by rw [hsl] at hμ2; omega)
  have hbusp : bus.point.length < 33 := by
    have hT0 := hrunT (.claimed ⟨gr.2.1.take (layoutOf bytecode m rowsN).logBytecode ++ alphas,
      σ (.n 714), 0, 0, [], [], [], 0⟩) (bytecodeAtM_claimed _ bytecode)
    rw [tablesSeg_pointM hT0, hptl]; exact hdepth
  have cE := hv.callF 1927 "check_opening_terminal" [.n 418, .n 709, .n 715, .n 417, .n 713,
    .n 144, .n 718, .n 8, .n 1180, .n 1630, .n 1631, .n 734, .n 733, .n 1649, .n 1650, .n 1651,
    .n 1648] [] (by decide +kernel)
  simp only [List.map_cons, List.map_nil] at cE
  have hacc := hterm (layoutOf bytecode m rowsN) bus claims (σ (.n 1179))
    (rcs.reverse ++ chi.drop 8) (ringCoefficients mcs) w
    [σ (.n 418), σ (.n 709), σ (.n 715), σ (.n 417), σ (.n 713), σ (.n 144), σ (.n 718), σ (.n 8),
      σ (.n 1180), σ (.n 1630), σ (.n 1631), σ (.n 734), σ (.n 733), σ (.n 1649), σ (.n 1650),
      σ (.n 1651), σ (.n 1648)]
    ⟨hctx, (by rw [r1630, r1631, layoutOf_logMemory, layoutOf_logBytecode hb,
        layoutOf_heights]; exact hpctx), (by rw [r1631]; exact hkb), (by rw [h144, layoutOf_logMemory]),
      (by rw [h718, layoutOf_heights]; rfl), (by rw [hcl]; exact hlp), hzv,
      (readsAt_of_getD fun k hk => hct k (by simpa [ringCoefficients, kBits] using hk)),
      (by rw [r1649]; exact hpt), r1650, r1651, r1648, (by simp only [layoutOf]),
      (by simp only [layoutOf]), (by omega), (by rw [layoutOf_logMemory]; omega), hbusp,
      (by rw [hwl]), (by rw [layoutOf_heights]; simp [hrcsl, hchil, opBlake2s]; omega),
      (by simp [ringCoefficients, kBits])⟩ cE
  -- the claims and the phases' runs at them
  rw [← r727, ← r728, ← r729] at hrunF
  have hrows32 : ∀ n ∈ rowsN, n ≤ 2 ^ 32 := fun n hn =>
    le_trans (le_two_pow_log2Ceil n) (Nat.pow_le_pow_right (by decide) (by have := hlogs n hn; omega))
  set cc : FixedClaims := ⟨gr.2.1.take 18 ++ alphas, σ (.n 714), σ (.n 728), σ (.n 727),
      chi.take 8, rcs.reverse, sl, σ (.n 729)⟩ with hcc
  rw [← edepth] at hrunG
  rw [h1627, h1179] at hrunW
  rw [h1179] at hacc
  rw [h698] at hrunT
  have hT := hrunT (.claimed cc) (by rw [layoutOf_logBytecode hb]; exact bytecodeAtM_claimed cc bytecode)
  have hF : RunsToM M (verifyFlock (.claimed cc) (blake2sR1csLogSize +
      (layoutOf bytecode m rowsN).tableLogHeights.getD opBlake2s 0)) cvT xsF
      (rcs.reverse ++ chi.drop 8, sl) cvF := by
    rw [layoutOf_heights]; exact hrunF (.claimed cc) (matricesAtM_claimed cc)
  -- the explicit witnesses are these
  have hm64 : m < 2 ^ 64 := by omega
  have eLog : vsLogMem σ = m := by rw [vsLogMem, h15, kToNat_eOfNat_limb0 hm64]
  have eRate : vsRate σ = r := by rw [vsRate, h121, kToNat_eOfNat_limb0 (by omega)]
  have eRows : vsRows σ = rowsN := by
    refine List.ext_getElem (by simp [vsRows, hrl]) fun t h1 h2 => ?_
    simp only [vsRows, List.getElem_map, List.getElem_range]
    have ht6 : t < 6 := by simpa [vsRows] using h1
    rw [hrowsW t ht6, List.getD_eq_getElem _ _ h2, kToNat_eOfNat_limb0]
    have := hrows32 _ (List.getElem_mem h2)
    omega
  have eLay : vsLayout bytecode σ = layoutOf bytecode m rowsN := by rw [vsLayout, eLog, eRows]
  have ePi : vsPiOf σ = pi := cellsDigest_eq hpi
  have eSeed : vsSeedOf σ = seed := cellsDigest_eq hseed
  have eFresh : vsFreshOf σ = cc := by
    rw [hcc]
    exact (vs_fresh_eqB hv (by omega) hzeta hal har (by omega) hchi hrcsl
      hrcs hsll hsr).symm
  -- the stream: the words read, in order, from the buffer
  have lG := (RunsToM.length_eq hrunG (reads_gkrPhase _)).1
  have lT := (RunsToM.length_eq hT (reads_tablesSeg cc (by simp [layoutOf_heights, hrl]; rfl)
    _ _ _ _ _)).1
  have lF := (RunsToM.length_eq hF (reads_verifyFlock cc _)).1
  have lW := (RunsWithM.length_eq hrunW (reads_whirOpen _ _ _)).1
  have hstream : announce m rowsN r ++ σ (.n 419) :: σ (.n 434) :: (xsG ++ (xsT ++ (xsF ++ xsW))) =
      streamAt Lm.read (σ (.n 14)) (vsStreamLen bytecode σ) := by
    have hlen : (announce m rowsN r ++ σ (.n 419) :: σ (.n 434) ::
        (xsG ++ (xsT ++ (xsF ++ xsW)))).length = vsStreamLen bytecode σ := by
      simp only [vsStreamLen, eLay, eRate, List.length_append, List.length_cons, lG, lT, lF, lW,
        announce, List.length_map, hrl, List.length_nil]
      omega
    rw [← hlen]
    apply readsAt_eq_streamAt
    have h8 : ReadsAt Lm.read (σ (.n 14)) (announce m rowsN r) := by
      rw [← hann]
      intro k hk
      simp only [readWords, List.length_map, List.length_range] at hk
      simpa [readWords] using hrd k hk
    have hal8 : (announce m rowsN r).length = 8 := by simp [announce, hrl]
    have h10 : ReadsAt Lm.read (σ (.n 14)) (announce m rowsN r ++ [σ (.n 419), σ (.n 434)]) := by
      refine readsAt_append h8 fun k hk => ?_
      rw [hal8]
      match k, hk with
      | 0, _ => exact l8
      | 1, _ => exact l9
    rw [h700] at hxsG
    have hG := readsAt_shift hxsG
    have hTs := readsAt_shift (j := 10 + xsG.length) (p := σ (.n 14)) (by
      rw [pow_add, ← mul_assoc, ← h700, ← r703]; exact hxsT)
    have hFs := readsAt_shift (j := 10 + xsG.length + xsT.length) (p := σ (.n 14)) (by
      rw [pow_add, ← mul_assoc, pow_add, ← mul_assoc, ← h700, ← r703, ← hcurT]; exact hxsF)
    have hWs := readsAt_shift (j := 10 + xsG.length + xsT.length + xsF.length) (p := σ (.n 14)) (by
      rw [pow_add, ← mul_assoc, pow_add, ← mul_assoc, pow_add, ← mul_assoc, ← h700, ← r703,
        ← hcurT, ← r726]; exact hxsW)
    have hall := readsAt_append (readsAt_append (readsAt_append (readsAt_append h10
      (fun k hk => by rw [List.length_append, hal8]; exact hG k hk))
      (fun k hk => by simp only [List.length_append, hal8, List.length_cons, List.length_nil];
                      rw [show 8 + 2 + xsG.length + k = 10 + xsG.length + k by omega]; exact hTs k hk))
      (fun k hk => by simp only [List.length_append, hal8, List.length_cons, List.length_nil];
                      rw [show 8 + 2 + xsG.length + xsT.length + k = 10 + xsG.length + xsT.length + k by omega]
                      exact hFs k hk))
      (fun k hk => by simp only [List.length_append, hal8, List.length_cons, List.length_nil];
                      rw [show 8 + 2 + xsG.length + xsT.length + xsF.length + k =
                        10 + xsG.length + xsT.length + xsF.length + k by omega]
                      exact hWs k hk)
    simpa only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] using hall
  have eProof : vsProofOf bytecode Lm.read σ wO = ⟨announce m rowsN r ++ σ (.n 419) :: σ (.n 434) ::
      (xsG ++ (xsT ++ (xsF ++ xsW))), os⟩ := by
    rw [vsProofOf, ← hstream, eLay, eRate, ← hos]
    rfl
  -- the deferring verifier accepts
  refine ⟨by rw [ePi]; exact hpi, by rw [eSeed]; exact hseed, ?_, ?_, ?_⟩
  · rw [eFresh]
    refine ⟨?_, ?_, by simp [hcc, hrcsl], by simp [hcc, hsll]⟩
    · simp only [hcc, List.length_append, List.length_take, hptl, hal]; omega
    · simp only [hcc, List.length_take, hchil]; omega
  · rw [eFresh, hcc]
    exact vs_deferB hv (by omega) hzeta hal har (by omega) hchi hrcsl hrcs hsll hsr
  · rw [eSeed, ePi, eFresh, eProof]
    refine verifyDeferredWith_true hb seed pi cc hm1 hm2 hr1 hr2 hrl hrows32 hμ1 hμ2 hroot hS hA
      h10 hB hC (gr := gr) (bus := bus) (claims := claims)
      (fp := rcs.reverse ++ chi.drop 8) (s := sl) (w := w) (roots' := roots')
      (cvG := cvG) (cvT := cvT) (cvF := cvF) (cvW := cvW)
      (xsG := xsG) (xsT := xsT) (xsF := xsF) (xsW := xsW) (os := os) ?_ ?_ ?_ hR hL ?_ ?_
    · convert hrunG using 2
    · convert hT using 2
    · convert hF using 2
    · convert hrunW using 2
    · convert hacc using 2

/-- **`verify_sub` is sound over a hash model, its witnesses named**: `verify_sub_sound_wCM` over
the program's call relation under `M.sem`. -/
theorem verify_sub_sound_wM {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (Lm : MemImage κ)
    {bytecode : List K} (hb : bytecode.length = 2 ^ 22)
    {TCtx : Reader → Layout → BusResult → List ColumnClaim → List E → Prop}
    {PCtx : Reader → List ℕ → E → E → Prop}
    (hgkr : SoundGkrM M Lm.read) (htab : SoundTablesM M bytecode TCtx Lm.read)
    (hfl : SoundFlockM M Lm.read) (hpl : SoundPlace PCtx Lm.read) (hkap : HypKappa PCtx Lm.read)
    {wO : String → List E → List E → List Opening}
    (hop : SoundOpenWCM M Lm.read (coreProgram.RelB M.sem Lm.read) wO)
    (hterm : SoundTerm TCtx PCtx Lm.read) (hv : VsHoldsB M.sem Lm.read σ)
    (ht : ExpTables Lm.read (σ (.n 4)) (σ (.n 5))) :
    VsOutcomeM M bytecode Lm.read σ wO :=
  verify_sub_sound_wCM hκ hκ6 Lm (fun _ _ _ h => h) hb hgkr htab hfl hpl hkap hop hterm hv ht

end
end LeanVM.Guest.B1.VerifySub
