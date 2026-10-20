/-
  LeanVM.Guest.B1.VerifySub.SoundW

  `verify_sub`'s soundness with its witnesses named: the public input, the seed, the fixed
  claims and the child proof as explicit functions of its valuation, the openings from
  `open_stacked`'s witness function.
-/

module

public import LeanVM.Guest.B1.VerifySub.Sound
public import LeanVM.Guest.B1.VerifySub.Consume
public import LeanVM.Guest.B1.VerifySub.InterfaceW

/-!
# `verify_sub` is sound, its witnesses named

For a valuation `σ` of `verify_sub`'s body (`VsHolds`):

* `vsPiOf σ`, `vsSeedOf σ`: the digests of the cells `σ 0, σ 1` and `σ 2, σ 3`;
* `vsFreshOf σ`: the fixed claims, the values `verify_sub` copies to `defer_out`;
* `vsProofOf bytecode rd σ wO`: the proof whose stream is the first `vsStreamLen bytecode σ`
  words of the hinted `stream` buffer `σ 14` (`vsStreamLen` counts what each phase reads at the
  announced sizes, `Consume.lean`), and whose openings are `open_stacked`'s, `wO name args rets`
  at the dispatched candidate's name and the dispatch's argument and return words.

`verify_sub_sound_w`: over the callees' soundness, `open_stacked`'s with the witness function
`wO` (`SoundOpenW`), the deferring verifier accepts `vsProofOf bytecode rd σ wO` for `vsPiOf σ`
under `vsSeedOf σ` with the claims `vsFreshOf σ`, of the guest's shape and at `defer_out`.
`verify_sub_sound'` recovers the meaning (`MeaningVerifySub`) from the relation.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

/-! ## Words of the memory -/

/-- The `n` words of the memory from `p`: the word at `p·g^k`, or `0`. -/
def streamAt (rd : Reader) (p : E) (n : ℕ) : List E :=
  (List.range n).map fun k ↦ (rd (p.limb 0 * Parameters.gpow k)).getD 0

theorem readsAt_eq_streamAt {p : E} {xs : List E} (h : ReadsAt rd p xs) :
    xs = streamAt rd p xs.length := by
  refine List.ext_getElem (by simp [streamAt]) fun k h1 h2 => ?_
  simp [streamAt, (h k h1).2]

theorem readsAt_shift {p : E} {j : ℕ} {xs : List E} (h : ReadsAt rd (p * gen ^ j) xs) :
    ∀ k (hk : k < xs.length), LoadHolds rd p (j + k) xs[k] := fun k hk =>
  (loadHolds_mul_gen_pow rd p j k _).mp (h k hk)

/-! ## The witnesses -/

/-- The digest of two cells, or the zero digest. -/
def cellsDigest (a b : E) : Digest := (digestOfScalars (a, b)).getD default

theorem cellsDigest_eq {a b : E} {d : Digest} (h : (a, b) = digestScalars d) : cellsDigest a b = d := by
  rw [cellsDigest, h, digestOfScalars_digestScalars]
  rfl

/-- The public input: the digest of `pi_0, pi_1`. -/
def vsPiOf (σ : Val) : Digest := cellsDigest (σ (.n 0)) (σ (.n 1))

/-- The seed: the digest of `seed_0, seed_1`. -/
def vsSeedOf (σ : Val) : Digest := cellsDigest (σ (.n 2)) (σ (.n 3))

/-- The fixed claims: the values `verify_sub` copies to `defer_out` (G:2265-2279). -/
def vsFreshOf (σ : Val) : FixedClaims :=
  ⟨(List.range 18).map (fun k ↦ σ (.n (1652 + k))) ++ (List.range 4).map (fun k ↦ σ (.n (1670 + k))),
    σ (.n 714), σ (.n 728), σ (.n 727), (List.range 8).map (fun k ↦ σ (.n (1674 + 2 * k))),
    ((List.range 8).map fun k ↦ σ (.n (1675 + 2 * k))).reverse,
    (List.range 64).map (fun k ↦ σ (.n (1690 + k))), σ (.n 729)⟩

/-- The announced memory log. -/
def vsLogMem (σ : Val) : ℕ := kToNat ((σ (.n 15)).limb 0)

/-- The announced row counts. -/
def vsRows (σ : Val) : List ℕ := (List.range 6).map fun t ↦ kToNat ((σ (.n (rdB (t + 1)))).limb 0)

/-- The announced rate. -/
def vsRate (σ : Val) : ℕ := kToNat ((σ (.n 121)).limb 0)

/-- The layout of the announced sizes. -/
def vsLayout (bytecode : List K) (σ : Val) : Layout := layoutOf bytecode (vsLogMem σ) (vsRows σ)

/-- The words the child proof's stream has at the announced sizes: the eight sizes and the
stack's root, then what GKR, the tables, Flock and the stacked opening read. -/
def vsStreamLen (bytecode : List K) (σ : Val) : ℕ :=
  10 + (gkrLen (pushDepth (vsLayout bytecode σ)) + (tablesLen (vsLayout bytecode σ) +
    (flockLen (blake2sR1csLogSize + (vsLayout bytecode σ).tableLogHeights.getD opBlake2s 0) +
      whirLen (vsLayout bytecode σ).stackLog (vsRate σ))))

/-- The arguments of the dispatched `open_stacked`. -/
def vsOpenArgs (σ : Val) : List E :=
  [σ (.n 1171), σ (.n 1172), σ (.n 1627), σ (.n 419), σ (.n 434), σ (.n 726)]

/-- The returns of the dispatched `open_stacked`. -/
def vsOpenRets (σ : Val) : List E := [σ (.n 1648), σ (.n 1649), σ (.n 1650), σ (.n 1651)]

/-- **The child proof**: the first `vsStreamLen` words of the `stream` buffer, and the openings
of the dispatched `open_stacked`, by the witness function `wO`. -/
def vsProofOf (bytecode : List K) (rd : Reader) (σ : Val)
    (wO : String → List E → List E → List Opening) : Proof :=
  ⟨streamAt rd (σ (.n 14)) (vsStreamLen bytecode σ),
    wO (openName (vsLayout bytecode σ).stackLog (vsRate σ)) (vsOpenArgs σ) (vsOpenRets σ)⟩

/-- **What `verify_sub` establishes, its witnesses named**: the cells are those of `vsPiOf σ` and
`vsSeedOf σ`, the claims `vsFreshOf σ` have the guest's shape and are at `defer_out`, and the
deferring verifier accepts `vsProofOf bytecode rd σ wO`. -/
def VsOutcome (bytecode : List K) (rd : Reader) (σ : Val)
    (wO : String → List E → List E → List Opening) : Prop :=
  (σ (.n 0), σ (.n 1)) = digestScalars (vsPiOf σ) ∧ (σ (.n 2), σ (.n 3)) = digestScalars (vsSeedOf σ) ∧
    FreshShaped (vsFreshOf σ) ∧ ReadsAt rd (σ (.n 6)) (Node.fixedCells (vsFreshOf σ)) ∧
    verifyDeferred bytecode (vsSeedOf σ) (vsPiOf σ) (vsFreshOf σ) (vsProofOf bytecode rd σ wO) = true

/-! ## The copies to `defer_out` -/

/-- The first load of each copy to `defer_out`. -/
theorem vs_copies (h : VsHolds rd σ) :
    (∀ k < 18, LoadHolds rd (σ (.n 418)) k (σ (.n (1652 + k)))) ∧
      (∀ k < 4, LoadHolds rd (σ (.n 451)) k (σ (.n (1670 + k)))) ∧
      (∀ k < 8, LoadHolds rd (σ (.n 721)) k (σ (.n (1674 + 2 * k)))) ∧
      (∀ k < 8, LoadHolds rd (σ (.n 722)) k (σ (.n (1675 + 2 * k)))) ∧
      ∀ k < 64, LoadHolds rd (σ (.n 723)) k (σ (.n (1690 + k))) := by
  have hz : ∀ k < 18, stmtsEqb [.atom (.load (.n (1652 + k)) (.n 418) k)]
      ((vsPre.drop (1928 + 2 * k)).take 1) = true := by
    decide +kernel
  have ha : ∀ k < 4, stmtsEqb [.atom (.load (.n (1670 + k)) (.n 451) k)]
      ((vsPre.drop (1964 + 2 * k)).take 1) = true := by
    decide +kernel
  have hc : ∀ k < 8, stmtsEqb [.atom (.load (.n (1674 + 2 * k)) (.n 721) k)]
      ((vsPre.drop (1975 + 4 * k)).take 1) = true := by
    decide +kernel
  have hr : ∀ k < 8, stmtsEqb [.atom (.load (.n (1675 + 2 * k)) (.n 722) k)]
      ((vsPre.drop (1977 + 4 * k)).take 1) = true := by
    decide +kernel
  have hs : ∀ k < 64, stmtsEqb [.atom (.load (.n (1690 + k)) (.n 723) k)]
      ((vsPre.drop (2007 + 2 * k)).take 1) = true := by
    decide +kernel
  exact ⟨fun k hk => h.atom _ _ (hz k hk), fun k hk => h.atom _ _ (ha k hk),
    fun k hk => h.atom _ _ (hc k hk), fun k hk => h.atom _ _ (hr k hk),
    fun k hk => h.atom _ _ (hs k hk)⟩

theorem map_range_eq_of_loads {p : E} {l : List E} {n : ℕ} (hl : l.length = n) (hr : ReadsAt rd p l)
    {f : ℕ → E} (hf : ∀ k < n, LoadHolds rd p k (f k)) : (List.range n).map f = l :=
  List.ext_getElem (by simp [hl]) fun k h1 h2 => by
    simp only [List.getElem_map, List.getElem_range]
    exact loadHolds_unique (hf k (by simpa using h1)) (hr k h2)

/-- The claims `verify_sub` exports are the values it copies. -/
theorem vs_fresh_eq (h : VsHolds rd σ) {P alphas chi rcs s : List E} (hP : 18 ≤ P.length)
    (hPr : ReadsAt rd (σ (.n 418)) P) (hal : alphas.length = 4) (har : ReadsAt rd (σ (.n 451)) alphas)
    (hcl : 8 ≤ chi.length) (hcr : ReadsAt rd (σ (.n 721)) chi) (hrl : rcs.length = 8)
    (hrr : ReadsAt rd (σ (.n 722)) rcs) (hsl : s.length = 64) (hsr : ReadsAt rd (σ (.n 723)) s) :
    (⟨P.take 18 ++ alphas, σ (.n 714), σ (.n 728), σ (.n 727), chi.take 8, rcs.reverse, s,
      σ (.n 729)⟩ : FixedClaims) = vsFreshOf σ := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := vs_copies h
  have hP' : ReadsAt rd (σ (.n 418)) (P.take 18) := fun k hk => by
    rw [List.getElem_take]; exact hPr k (by simp at hk; omega)
  have hc' : ReadsAt rd (σ (.n 721)) (chi.take 8) := fun k hk => by
    rw [List.getElem_take]; exact hcr k (by simp at hk; omega)
  rw [vsFreshOf, map_range_eq_of_loads (by simp; omega) hP' c1, map_range_eq_of_loads hal har c2,
    map_range_eq_of_loads (by simp; omega) hc' c3, map_range_eq_of_loads hrl hrr c4,
    map_range_eq_of_loads hsl hsr c5]

/-! ## The theorem -/

/-- **`verify_sub` is sound, its witnesses named** (TRIAGE #44): on a memory of `2^κ` words,
`6 ≤ κ ≤ 32`, over the exponent tables, for a bytecode of `2^22` words, given the callees'
soundness, `open_stacked`'s with the witness function `wO`, every valuation of `verify_sub`'s
body gives `VsOutcome`. -/
theorem verify_sub_sound_w {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (Lm : MemImage κ) {bytecode : List K}
    (hb : bytecode.length = 2 ^ 22)
    {TCtx : Reader → Layout → BusResult → List ColumnClaim → List E → Prop}
    {PCtx : Reader → List ℕ → E → E → Prop}
    (hgkr : SoundGkr Lm.read) (htab : SoundTables bytecode TCtx Lm.read) (hfl : SoundFlock Lm.read)
    (hpl : SoundPlace PCtx Lm.read) (hkap : HypKappa PCtx Lm.read)
    {wO : String → List E → List E → List Opening} (hop : SoundOpenW Lm.read wO)
    (hterm : SoundTerm TCtx PCtx Lm.read) (hv : VsHolds Lm.read σ)
    (ht : ExpTables Lm.read (σ (.n 4)) (σ (.n 5))) :
    VsOutcome bytecode Lm.read σ wO := by
  -- the seed, the sizes, the root
  obtain ⟨seed, pi, hseed, hpi, h12⟩ := vs_seed (hv.to 2136) (by decide)
  obtain ⟨hrd, hst, hrows⟩ := vs_reads hv h12
  obtain ⟨r, hr1, hr2, h121, h138⟩ := vs_rate hκ hκ6 Lm hv ht
  obtain ⟨m, hm1, hm2, h15, h144⟩ := vs_logMem hκ hκ6 Lm (hv.to 2136) (by decide) ht
  obtain ⟨l8, l9, h447, root, hroot⟩ := vs_root hv (hst 8 le_rfl)
  obtain ⟨hdims, hbase, hbk⟩ := vs_kappas (hv.to 2136) (by decide)
  -- the bus challenges
  obtain ⟨har, h499⟩ := vs_alphas hv h447
  have hal : (sqAll 4 (obsAll (obsAll (blake2sBytes (digestBytes seed ++ digestBytes pi))
      (readWords σ 8)) [σ (.n 419), σ (.n 434)])).1.length = 4 := by simp [sqAll_eq]
  have hfpw := vs_fpw (hv.to 2136) (by decide) hal har
  obtain ⟨h690, h698, h700⟩ := vs_beta hv h499
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
  have e707 := hv.atom 807 (.copy (.n 707) (.n 701)) (by decide +kernel)
  have e708 := hv.atom 808 (.copy (.n 708) (.n 702)) (by decide +kernel)
  simp only [Atom.Holds] at e707 e708
  -- the tables
  have cT := hv.call 810 "verify_tables" [.n 707, .n 708, .n 703, .n 0, .n 1, .n 418, .n 417,
    .n 143, .n 30, .n 163, .n 5, .n 508, .n 698, .n 7, .n 8, .n 709, .n 704, .n 705, .n 706]
    [.n 710, .n 711, .n 712, .n 713, .n 714, .n 715] (by decide +kernel)
  simp only [List.map_cons, List.map_nil] at cT
  rw [h144] at hdims hbk hbase
  have hpre : TablesPre Lm.read (σ (.n 4)) pi m
      (sqAll 4 (obsAll (obsAll (blake2sBytes (digestBytes seed ++ digestBytes pi))
        (readWords σ 8)) [σ (.n 419), σ (.n 434)])).1 gr.2.1 gr.2.2
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
  rw [hann] at h447 har hal hfpw hpre hrunT
  have hdw : dimsWords σ = (rowsN.map log2Ceil).map (gen ^ ·) := by
    have := readsAt_unique (by simp [dimsWords, hrl]) hdims hdimsR
    rw [List.cons.injEq] at this
    rw [this.2, List.map_map]
    rfl
  have hhs : ∀ h ∈ rowsN.map log2Ceil, h < 29 := by
    intro x hx; obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx; exact hlogs n hn
  have hhl : (rowsN.map log2Ceil).length = 6 := by simp [hrl]
  -- the bus depth
  obtain ⟨N, hN, h416, hlN, h417'⟩ := vs_busMu hκ hκ6 Lm hv ht
  have hS := vs_depth hv ht hm2 hhl hhs h144 hdw
  have hSlt : ((pushKappas m (rowsN.map log2Ceil)).map (2 ^ ·)).sum ≤ 37 * 2 ^ 32 := by
    have := sum_le_of_le ((pushKappas m (rowsN.map log2Ceil)).map (2 ^ ·)) (2 ^ 32) (by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
      obtain ⟨b, hb', rfl⟩ := List.getElem_of_mem hk
      have := pushKappas_le m _ hhl hm2 hhs b (by rw [pushKappas_length m _ hhl] at hb'; exact hb')
      rw [List.getD_eq_getElem _ _ hb'] at this
      exact Nat.pow_le_pow_right (by decide) this)
    rwa [List.length_map, pushKappas_length m _ hhl] at this
  rw [h416] at hS
  have eN := gen_pow_inj (by omega) (by omega) hS
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
  have e710 := hv.atom 811 (.copy (.n 716) (.n 710)) (by decide +kernel)
  have e711 := hv.atom 812 (.copy (.n 717) (.n 711)) (by decide +kernel)
  have l718 := hv.atom 813 (.load (.n 718) (.n 143) 6) (by decide +kernel)
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
  have e724 := hv.atom 820 (.copy (.n 730) (.n 724)) (by decide +kernel)
  have e725 := hv.atom 821 (.copy (.n 731) (.n 725)) (by decide +kernel)
  simp only [Atom.Holds] at e724 e725
  have h730 : (σ (.n 730), σ (.n 731)) = digestScalars cvF := by rw [e724, e725, r724, r725]
  obtain ⟨hmc, h810⟩ := vs_mapChallenges hv h730
  have hmcl : (sqAll 6 cvF).1.length = 6 := by simp [sqAll_eq]
  have hct := vs_ctable hv hmcl hmc
  have htr := vs_transposed hv hsll hsr hmcl hmc
  have hzv := vs_zvals hv hτ h718 hchil hrcsl hchi hrcs
  -- the batching
  obtain ⟨h1171, h1179, hlp, h1627⟩ := vs_lam hv h810 (by rw [List.length_map, hcl]) hpool
  rw [htr, List.length_map] at h1627
  -- the placement and the stack's size
  have cP := hv.call 1913 "certify_placement" [.n 155, .n 5] [.n 1629, .n 1630, .n 1631]
    (by decide +kernel)
  simp only [List.map_cons, List.map_nil] at cP
  rw [hdw] at hbase
  obtain ⟨off, kap, hretsP, hpctx⟩ := hpl _ _ _ m _ _ ht hm2 hhl hhs hbase cP
  simp only [List.cons.injEq] at hretsP
  obtain ⟨r1629, r1630, r1631, -⟩ := hretsP
  obtain ⟨N2, hN2, h1629, hμ1, hμ2, hopen⟩ := vs_stackSel hκ hκ6 Lm hv ht hr1 hr2 h138
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
    have hT0 := hrunT (.claimed ⟨gr.2.1.take (layoutOf bytecode m rowsN).logBytecode ++
      (sqAll 4 (obsAll (obsAll (blake2sBytes (digestBytes seed ++ digestBytes pi))
        (announce m rowsN r)) [σ (.n 419), σ (.n 434)])).1, σ (.n 714), 0, 0, [], [], [], 0⟩)
      (bytecodeAt_claimed _ bytecode)
    rw [tablesSeg_point hT0, hptl]; exact hdepth
  have cE := hv.call 1927 "check_opening_terminal" [.n 418, .n 709, .n 715, .n 417, .n 713,
    .n 144, .n 718, .n 8, .n 1180, .n 1630, .n 1631, .n 734, .n 733, .n 1649, .n 1650, .n 1651,
    .n 1648] [] (by decide +kernel)
  simp only [List.map_cons, List.map_nil] at cE
  have hacc := hterm (layoutOf bytecode m rowsN) bus claims (σ (.n 1179))
    (rcs.reverse ++ chi.drop 8) (ringCoefficients (sqAll 6 cvF).1) w
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
  set cc : FixedClaims := ⟨gr.2.1.take 18 ++ (sqAll 4 (obsAll (obsAll
      (blake2sBytes (digestBytes seed ++ digestBytes pi)) (announce m rowsN r))
      [σ (.n 419), σ (.n 434)])).1, σ (.n 714), σ (.n 728), σ (.n 727), chi.take 8, rcs.reverse, sl,
      σ (.n 729)⟩ with hcc
  rw [← edepth, hann] at hrunG
  rw [h1627, h1179] at hrunW
  rw [h1179] at hacc
  rw [h698] at hrunT
  have hT := hrunT (.claimed cc) (by rw [layoutOf_logBytecode hb]; exact bytecodeAt_claimed cc bytecode)
  have hF : RunsTo (verifyFlock (.claimed cc) (blake2sR1csLogSize +
      (layoutOf bytecode m rowsN).tableLogHeights.getD opBlake2s 0)) cvT xsF
      (rcs.reverse ++ chi.drop 8, sl) cvF := by
    rw [layoutOf_heights]; exact hrunF (.claimed cc) (matricesAt_claimed cc)
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
    exact (vs_fresh_eq hv (by omega) hzeta hal har (by omega) hchi hrcsl
      hrcs hsll hsr).symm
  -- the stream: the words read, in order, from the buffer
  have lG := (RunsTo.length_eq hrunG (reads_gkrPhase _)).1
  have lT := (RunsTo.length_eq hT (reads_tablesSeg cc (by simp [layoutOf_heights, hrl]; rfl)
    _ _ _ _ _)).1
  have lF := (RunsTo.length_eq hF (reads_verifyFlock cc _)).1
  have lW := (RunsWith.length_eq hrunW (reads_whirOpen _ _ _)).1
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
    exact vs_defer hv (by omega) hzeta hal har (by omega) hchi hrcsl hrcs hsll hsr
  · rw [eSeed, ePi, eFresh, eProof]
    refine verifyDeferred_true hb seed pi cc hm1 hm2 hr1 hr2 hrl hrows32 hμ1 hμ2 hroot
      (cv10 := obsAll (obsAll (blake2sBytes (digestBytes seed ++ digestBytes pi)) (announce m rowsN r))
        [σ (.n 419), σ (.n 434)]) (gr := gr) (bus := bus) (claims := claims)
      (fp := rcs.reverse ++ chi.drop 8) (s := sl) (w := w) (roots' := roots') (cvG := cvG)
      (cvT := cvT) (cvF := cvF) (cvW := cvW) (xsG := xsG) (xsT := xsT) (xsF := xsF) (xsW := xsW)
      rfl ?_ ?_ ?_ ?_ ?_
    · convert hrunG using 2
    · convert hT using 2
      rw [hann]
    · convert hF using 2
    · convert hrunW using 2
    · convert hacc using 2

/-- The meaning, from `verify_sub_sound_w`: `verify_sub`'s relation, under the same callees and
`open_stacked`'s soundness (`SoundOpen`), gives `MeaningVerifySub`. -/
theorem verify_sub_sound' {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (Lm : MemImage κ) {bytecode : List K}
    (hb : bytecode.length = 2 ^ 22)
    {TCtx : Reader → Layout → BusResult → List ColumnClaim → List E → Prop}
    {PCtx : Reader → List ℕ → E → E → Prop}
    (hgkr : SoundGkr Lm.read) (htab : SoundTables bytecode TCtx Lm.read) (hfl : SoundFlock Lm.read)
    (hpl : SoundPlace PCtx Lm.read) (hkap : HypKappa PCtx Lm.read) (hop : SoundOpen Lm.read)
    (hterm : SoundTerm TCtx PCtx Lm.read) {args : List E}
    (ht : ExpTables Lm.read (args.getD 4 0) (args.getD 5 0))
    (h : coreProgram.Rel Lm.read "verify_sub" args []) :
    MeaningVerifySub bytecode Lm.read args [] := by
  obtain ⟨σ, rfl, hv⟩ := verify_sub_holds h
  obtain ⟨wO, hwO⟩ := exists_soundOpenW hop
  simp only [List.getD_cons_succ, List.getD_cons_zero] at ht
  obtain ⟨hpi, hseed, hsh, hout, hacc⟩ :=
    verify_sub_sound_w hκ hκ6 Lm hb hgkr htab hfl hpl hkap hwO hterm hv ht
  exact ⟨_, _, _, _, hseed, hpi, hacc, hsh, hout⟩

end
end LeanVM.Guest.B1.VerifySub
