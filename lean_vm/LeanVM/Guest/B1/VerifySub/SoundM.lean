/-
  LeanVM.Guest.B1.VerifySub.SoundM

  `verify_sub`'s soundness over a hash model: its relation under the model's semantics, over the
  callees' soundness over the model, implies that the deferring verifier over the model's hash
  accepts.
-/

module

public import LeanVM.Guest.B1.VerifySub.TailB
public import LeanVM.Guest.B1.VerifySub.RunM
public import LeanVM.Guest.B1.VerifySub.Sound
public import LeanVM.Guest.Value.NodeSome

/-!
# `verify_sub` is sound over a hash model (TRIAGE #44)

`verify_sub_model`: on a memory of `2^κ` words, `6 ≤ κ ≤ 32`, over the exponent tables, for a
bytecode of `2^22` words, given the hashing callees' soundness over the model (`SoundGkrM`,
`SoundTablesM`, `SoundFlockM`, `SoundOpenM`) and the others' as deployed (`SoundPlace`,
`HypKappa`, `SoundTerm`: `certify_placement` and `check_opening_terminal` are free of
`BLAKE2S`), `verify_sub`'s relation under `M.sem` implies `MeaningVerifySubWith M`: the deferring
verifier over the model's hash accepts the proof made of the words the guest read and the
openings `open_stacked` read, `verifyDeferredWith M.H bytecode seed pi c π = some true`.

The proof is `verify_sub_sound`'s, every chain state the model's answer: the seed `M.H (seed ‖
pi)` (`vs_seedM`), the words absorbed (`vs_readsM`, `vs_rootM`: `obsAllM`), the challenges
squeezed (`vs_alphasM`, `vs_betaM`, `vs_mapChallengesM`, `vs_lamM`: `sqAllM`, `sqCvM`), the
callees' runs (`RunsToM`, `RunsWithM`); `verifyDeferredWith_true` assembles them.
`meaningVerifySubWith_deployed`: at the deployed model the meaning is `MeaningVerifySub`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {S : BlakeSem} {M : HashModel} {rd : Reader} {σ : Val}

/-! ## The meaning -/

/-- **`verify_sub`'s meaning over a hash model** (`MeaningVerifySub` over `M.H`): the cells are a
public input `pi` and a seed, and for some fixed claims `c` of the guest's shape and some proof
`π` the deferring verifier over the model's hash accepts `π` for `pi` under the seed, with
`fixedCells c` at `defer_out`. -/
def MeaningVerifySubWith (M : HashModel) (bytecode : List K) (rd : Reader) :
    List E → List E → Prop
  | [pi0, pi1, s0, s1, _, _, out], [] =>
      ∃ (seed pi : Digest) (c : FixedClaims) (π : Proof), (s0, s1) = digestScalars seed ∧
        (pi0, pi1) = digestScalars pi ∧ verifyDeferredWith M.H bytecode seed pi c π = some true ∧
        FreshShaped c ∧ ReadsAt rd out (Node.fixedCells c)
  | _, _ => False

theorem verifyDeferredWith_deployed {bytecode : List K} {seed pi : Digest} {c : FixedClaims}
    {π : Proof} : verifyDeferredWith HashModel.deployed.H bytecode seed pi c π = some true ↔
      verifyDeferred bytecode seed pi c π = true := by
  rw [show HashModel.deployed.H = someBlake from rfl, verifyDeferredWith_some, Option.some.injEq]

/-- At the deployed model the meaning is `MeaningVerifySub`. -/
theorem meaningVerifySubWith_deployed {bytecode : List K} {rd : Reader} {args rets : List E} :
    MeaningVerifySubWith HashModel.deployed bytecode rd args rets ↔
      MeaningVerifySub bytecode rd args rets := by
  unfold MeaningVerifySubWith MeaningVerifySub
  split <;> simp only [verifyDeferredWith_deployed]

/-! ## Results a program always returns, over the model -/

variable (M) in
/-- Every run of `p` over the model returns a value satisfying `Q`. -/
def RetsM {α : Type} (Q : α → Prop) (p : Prog α) : Prop :=
  ∀ s a s', runM M p s = some (some (a, s')) → Q a

theorem retsM_ret {α : Type} {Q : α → Prop} {a : α} (h : Q a) : RetsM M Q (Prog.ret a) :=
  fun s b s' hr => by
    have hr' : some (some (a, s)) = some (some (b, s')) := hr
    simp only [Option.some.injEq, Prod.mk.injEq] at hr'
    exact hr'.1 ▸ h

theorem retsM_bind {α β : Type} {Q : α → Prop} {R : β → Prop} {p : Prog α} {f : α → Prog β}
    (hp : RetsM M Q p) (hf : ∀ x, Q x → RetsM M R (f x)) : RetsM M R (p >>= f) := fun s b s' hr => by
  rw [prog_bind_eq, runM_bind] at hr
  cases h : runM M p s with
  | none => rw [h] at hr; exact absurd hr (by simp)
  | some o =>
    rw [h] at hr
    cases o with
    | none => exact absurd hr (by simp)
    | some r => exact hf r.1 (hp s r.1 r.2 (by rw [h])) _ _ _ hr

theorem retsM_true {α : Type} (p : Prog α) : RetsM M (fun _ => True) p := fun _ _ _ _ => trivial

theorem busRest_pointM (ev : Evaluations) (layout : Layout) (alphas : List E) (beta : E)
    (point treeValues : List E) :
    RetsM M (fun b => b.point = point) (busRest ev layout alphas beta point treeValues) := by
  unfold busRest
  exact retsM_bind (retsM_true _) fun _ _ => retsM_bind (retsM_true _) fun _ _ =>
    retsM_bind (retsM_true _) fun _ _ => retsM_bind (retsM_true _) fun _ _ => retsM_ret rfl

theorem tablesSeg_pointM {ev : Evaluations} {layout : Layout} {pi : Digest} {alphas : List E}
    {beta : E} {point treeValues : List E} {cv cv' : Digest} {xs : List E} {bus : BusResult}
    {claims : List ColumnClaim}
    (h : RunsToM M (tablesSeg ev layout pi alphas beta point treeValues) cv xs (bus, claims) cv') :
    bus.point = point := by
  have hr : RetsM M (fun r : BusResult × List ColumnClaim => r.1.point = point)
      (tablesSeg ev layout pi alphas beta point treeValues) := by
    unfold tablesSeg
    exact retsM_bind (busRest_pointM ev layout alphas beta point treeValues) fun b hb =>
      retsM_bind (retsM_true _) fun _ _ => retsM_bind (retsM_true _) fun _ _ => retsM_ret hb
  exact hr _ _ _ (h [] [] [])

theorem bytecodeAtM_claimed (c : FixedClaims) (words : List K) :
    BytecodeAtM M (.claimed c) words c.bytecodePoint c.bytecodeValue := fun _ => by
  simp only [Evaluations.claimed, Prog.bind_eq, Prog.pure_eq]
  rfl

theorem matricesAtM_claimed (c : FixedClaims) :
    MatricesAtM M (.claimed c) c.alpha c.zSkip c.rowPoint c.columnPoint c.slices c.matrixValue :=
  fun _ => by
    simp only [Evaluations.claimed, Prog.bind_eq, Prog.pure_eq]
    rfl

/-! ## The bus depth -/

/-- **The bus depth is the push side's under `S`** (`vs_depth`). -/
theorem vs_depthB (h : VsHoldsB S rd σ) (ht : ExpTables rd (σ (.n 4)) (σ (.n 5))) {m : ℕ}
    (hm : m ≤ 32) {hs : List ℕ} (hl : hs.length = 6) (hh : ∀ h ∈ hs, h < 29)
    (h144 : σ (.n 144) = gen ^ m) (hdw : dimsWords σ = hs.map (gen ^ ·)) :
    σ (.n 416) = gen ^ ((pushKappas m hs).map (2 ^ ·)).sum := by
  obtain ⟨-, -, hbk⟩ := vs_kappasB (h.to 2136) (by decide)
  obtain ⟨hp, hprod⟩ := vs_pushB h
  rw [h144, hdw] at hbk
  have hq : ∀ b < 37, σ (.n (pushK b + 2)) = gen ^ 2 ^ (pushKappas m hs).getD b 0 := by
    intro b hb
    obtain ⟨l1, l2⟩ := hp b hb
    have hk : σ (.n (pushK b)) = gen ^ (pushKappas m hs).getD b 0 := by
      rw [← blockKappas_pow m hs hl b hb, List.getD_eq_getElem _ _ (by simp [blockKappas]; omega)]
      exact loadHolds_unique l1 (hbk b (by simp [blockKappas]; omega))
    rw [hk, loadHolds_mul_gen_pow, Nat.add_zero] at l2
    exact loadHolds_unique l2 (ht _ (by have := pushKappas_le m hs hl hm hh b hb; show _ < 34; omega)).2
  rw [hprod, List.map_congr_left (fun b hb => hq b (List.mem_range.mp hb))]
  have hlen := pushKappas_length m hs hl
  rw [← map_getD_range (pushKappas m hs) (2 ^ ·), hlen, prod_map_gen_pow]

/-! ## The theorem -/

/-- **`verify_sub` is sound over a hash model** (TRIAGE #44; `verify_sub_sound` over `M`). -/
theorem verify_sub_model {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (Lm : MemImage κ) {bytecode : List K}
    (hb : bytecode.length = 2 ^ 22)
    {TCtx : Reader → Layout → BusResult → List ColumnClaim → List E → Prop}
    {PCtx : Reader → List ℕ → E → E → Prop}
    (hgkr : SoundGkrM M Lm.read) (htab : SoundTablesM M bytecode TCtx Lm.read)
    (hfl : SoundFlockM M Lm.read) (hpl : SoundPlace PCtx Lm.read) (hkap : HypKappa PCtx Lm.read)
    (hop : SoundOpenM M Lm.read) (hterm : SoundTerm TCtx PCtx Lm.read) {args : List E}
    (ht : ExpTables Lm.read (args.getD 4 0) (args.getD 5 0))
    (h : coreProgram.RelB M.sem Lm.read "verify_sub" args []) :
    MeaningVerifySubWith M bytecode Lm.read args [] := by
  obtain ⟨σ, rfl, hv⟩ := verify_sub_holdsB h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at ht
  -- the seed, the sizes, the root
  obtain ⟨seed, pi, cvS, hseed, hpi, hS, h12⟩ := vs_seedM (hv.to 2136) (by decide)
  obtain ⟨hrd, hst, hrows⟩ := vs_readsM hv h12
  obtain ⟨r, hr1, hr2, h121, h138⟩ := vs_rateB hκ hκ6 Lm hv ht
  obtain ⟨m, hm1, hm2, h15, h144⟩ := vs_logMemB hκ hκ6 Lm (hv.to 2136) (by decide) ht
  obtain ⟨cvA, hA, h134⟩ := hst 8 le_rfl
  obtain ⟨-, -, ⟨cv10, h10, h447⟩, root, hroot⟩ := vs_rootM hv h134
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
    vs_stackSelCB (C := coreProgram.RelB M.sem Lm.read) hκ hκ6 Lm (fun _ _ _ h => h) hv ht hr1 hr2
      h138
  have hST := stackTotal_lt m (rowsN.map log2Ceil) hm2 hhs
  rw [r1629] at h1629
  have eST := gen_pow_inj (by omega) (by omega) h1629
  rw [← eST] at hμ1 hμ2 hopen
  have hsl : (layoutOf bytecode m rowsN).stackLog =
      max 15 (log2Ceil (stackTotal (columnKappas m 18 (rowsN.map log2Ceil)))) :=
    stackLog_eq hb m rowsN
  rw [← hsl] at hμ1 hμ2 hopen
  -- the opening
  obtain ⟨os, cvW0, xsW, w, cvW, roots', hcvW0, hxsW, hrunW, pt, hretsW, hpt, hwl⟩ :=
    hop _ _ hμ1 hμ2 hr1 hr2 root _ _ _ _ _ _ _ hroot hopen
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
  -- the deferring verifier accepts
  rw [← r727, ← r728, ← r729] at hrunF
  have hrows32 : ∀ n ∈ rowsN, n ≤ 2 ^ 32 := fun n hn =>
    le_trans (le_two_pow_log2Ceil n) (Nat.pow_le_pow_right (by decide) (by have := hlogs n hn; omega))
  set cc : FixedClaims := ⟨gr.2.1.take 18 ++ alphas, σ (.n 714), σ (.n 728), σ (.n 727),
      chi.take 8, rcs.reverse, sl, σ (.n 729)⟩ with hcc
  refine ⟨seed, pi, cc, ⟨announce m rowsN r ++ σ (.n 419) :: σ (.n 434) ::
      (xsG ++ (xsT ++ (xsF ++ xsW))), os⟩, hseed, hpi, ?_, ?_, ?_⟩
  · rw [← edepth] at hrunG
    rw [h1627, h1179] at hrunW
    rw [h1179] at hacc
    rw [h698] at hrunT
    have hT := hrunT (.claimed cc) (by rw [layoutOf_logBytecode hb]; exact bytecodeAtM_claimed cc bytecode)
    have hF : RunsToM M (verifyFlock (.claimed cc) (blake2sR1csLogSize +
        (layoutOf bytecode m rowsN).tableLogHeights.getD opBlake2s 0)) cvT xsF
        (rcs.reverse ++ chi.drop 8, sl) cvF := by
      rw [layoutOf_heights]; exact hrunF (.claimed cc) (matricesAtM_claimed cc)
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
  · refine ⟨?_, ?_, by simp [hcc, hrcsl], by simp [hcc, hsll]⟩
    · simp only [hcc, List.length_append, List.length_take, hptl, hal]; omega
    · simp only [hcc, List.length_take, hchil]; omega
  · exact vs_deferB hv (by omega) hzeta hal har (by omega) hchi hrcsl hrcs hsll hsr

end
end LeanVM.Guest.B1.VerifySub
