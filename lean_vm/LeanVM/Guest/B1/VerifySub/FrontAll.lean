/-
  LeanVM.Guest.B1.VerifySub.FrontAll

  `verify_sub` up to its three calls, assembled: what its first statements establish.
-/

module

public import LeanVM.Guest.B1.VerifySub.Front
public import LeanVM.Guest.B1.VerifySub.Mid
public import LeanVM.Guest.B1.VerifySub.Ctab
public import LeanVM.Guest.B1.VerifySub.Tail
public import LeanVM.Guest.B1.Tables.InterfaceC
public import LeanVM.Guest.B1.Bits.AssertCanonical

/-!
# The front of `verify_sub`, assembled

`vs_front`: the statements from the seed to the calls of `verify_bus_gkr`, `verify_tables` and
`verify_keccak` (G:3152-3248), under their callees' statements, establish `VsFront`: the seed,
the announced words absorbed, the root, the bus challenges and `β`, the rate and the memory's
log, the rows and heights certified by `verify_tables` (`dims_g`, `kappa_base`, `block_kappa`
on them), the bus depth, the GKR's and the tables' runs and outputs, and `verify_keccak`'s call.

`verify_bus_gkr` needs `g_bus_mu ≠ 1`, which the push total gives once `verify_tables` has
certified the heights: `verify_tables` is first applied at the empty point when `g_bus_mu = 1`
(its precondition then holds), which contradicts the push total.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The push total of the memory's log `m` and the heights `hs`. -/
def pushTotal (m : ℕ) (hs : List ℕ) : ℕ := ((List.range 54).map fun b ↦ 2 ^ pushKappa m hs b).sum

/-- The bus challenges' values. -/
def vsAlphas (σ : Val) : List E := [σ (.n 579), σ (.n 599), σ (.n 619), σ (.n 639)]

/-- **What `verify_sub`'s front establishes.** -/
structure VsFront (bytecode : List K) (C : CallRel) (rd : Reader) (σ : Val) : Type where
  seed : Digest
  pi : Digest
  hseed : (σ (.n 2), σ (.n 3)) = digestScalars seed
  hpi : (σ (.n 0), σ (.n 1)) = digestScalars pi
  hcap0 : [σ (.n 22), σ (.n 23), σ (.n 24), σ (.n 25), σ (.n 26)] =
    capOf (keccakF (seedInput seed pi))
  h10 : σ (.n 10) = 0
  h11 : σ (.n 11) = 0
  h12 : σ (.n 12) = 0
  h13 : σ (.n 13) = 0
  hw : ∀ i < 8, WordAt rd σ i (vsX i)
  hrw : ∀ i < 6, LoadHolds rd (σ (.n 28)) i (σ (.n (vsX (i + 1))))
  w8 : WordAt rd σ 8 537
  w9 : WordAt rd σ 9 547
  hc537 : IsCanonical128 (σ (.n 537))
  hc547 : IsCanonical128 (σ (.n 547))
  hab8 : (⟨[σ (.n 22), σ (.n 23), σ (.n 24), σ (.n 25), σ (.n 26)], []⟩ : Fs).absorbAll
      (vsWords σ) dsObserve =
    ⟨[σ (.n 77), σ (.n 78), σ (.n 79), σ (.n 80), σ (.n 81)],
      [(σ (.n 82), dsObserve), (σ (.n 92), dsObserve), (σ (.n 102), dsObserve),
        (σ (.n 112), dsObserve)]⟩
  habR : (((⟨[σ (.n 77), σ (.n 78), σ (.n 79), σ (.n 80), σ (.n 81)],
      [(σ (.n 82), dsObserve), (σ (.n 92), dsObserve), (σ (.n 102), dsObserve),
        (σ (.n 112), dsObserve)]⟩ : Fs).absorb (σ (.n 537)) dsObserve).absorb (σ (.n 547))
      dsObserve) =
    ⟨[σ (.n 532), σ (.n 533), σ (.n 534), σ (.n 535), σ (.n 536)],
      [(σ (.n 537), dsObserve), (σ (.n 547), dsObserve)]⟩
  halpha : (⟨[σ (.n 532), σ (.n 533), σ (.n 534), σ (.n 535), σ (.n 536)],
      [(σ (.n 537), dsObserve), (σ (.n 547), dsObserve)]⟩ : Fs).squeezeN 4 =
    (vsAlphas σ, ⟨[σ (.n 628), σ (.n 629), σ (.n 630), σ (.n 631), σ (.n 632)], []⟩)
  hbeta : (⟨[σ (.n 628), σ (.n 629), σ (.n 630), σ (.n 631), σ (.n 632)], []⟩ : Fs).squeeze =
    (σ (.n 836), ⟨[σ (.n 825), σ (.n 826), σ (.n 827), σ (.n 828), σ (.n 829)], []⟩)
  halphaR : ReadsAt rd (σ (.n 559)) (vsAlphas σ)
  hfpw : ReadsAt rd (σ (.n 640)) (eqKernel (vsAlphas σ))
  lir : ℕ
  logMem : ℕ
  hl1 : 1 ≤ lir
  hl4 : lir ≤ 4
  e112 : σ (.n 112) = eOfNat lir
  e124 : σ (.n 124) = gen ^ (lir - 1)
  hm16 : 16 ≤ logMem
  hm32 : logMem ≤ 32
  e29 : σ (.n 29) = eOfNat logMem
  e130 : σ (.n 130) = gen ^ logMem
  rowsN : List ℕ
  hrowsL : rowsN.length = 6
  hrows : ReadsAt rd (σ (.n 28)) (rowsN.map eOfNat)
  hdims : ReadsAt rd (σ (.n 129)) (gen ^ logMem :: (Tables.tableHeightsOf rowsN).map (gen ^ ·))
  hh29 : ∀ h ∈ Tables.tableHeightsOf rowsN, h < 29
  hkb : ReadsAt rd (σ (.n 141)) (1 :: gen ^ logMem :: (Tables.tableHeightsOf rowsN).map (gen ^ ·))
  hbk : ReadsAt rd (σ (.n 149))
    (Tables.blockKappaWords (gen ^ logMem) ((Tables.tableHeightsOf rowsN).map (gen ^ ·)))
  e522 : σ (.n 522) = gen ^ log2Ceil (pushTotal logMem (Tables.tableHeightsOf rowsN))
  hdep : log2Ceil (pushTotal logMem (Tables.tableHeightsOf rowsN)) < 33
  xsG : List E
  r : E × List E × List E
  capG : List E
  hxsG : ReadsAt rd (σ (.n 27) * gen ^ 10) xsG
  hrunG : RunsTo (Tables.gkrPhase (log2Ceil (pushTotal logMem (Tables.tableHeightsOf rowsN))))
    ⟨[σ (.n 825), σ (.n 826), σ (.n 827), σ (.n 828), σ (.n 829)], []⟩ xsG r ⟨capG, []⟩
  hptL : r.2.1.length = log2Ceil (pushTotal logMem (Tables.tableHeightsOf rowsN))
  hvL : r.2.2.length = 3
  hzeta : ReadsAt rd (σ (.n 523)) r.2.1
  hretG : [σ (.n 839), σ (.n 840), σ (.n 841), σ (.n 842), σ (.n 843), σ (.n 844), σ (.n 845),
    σ (.n 846), σ (.n 847)] = capG ++ [σ (.n 27) * gen ^ 10 * gen ^ xsG.length] ++ r.2.2
  xsT : List E
  capT : List E
  bus : BusResult
  claims : List ColumnClaim
  hxsT : ReadsAt rd (σ (.n 844)) xsT
  hrunT : ∀ ev, Tables.BytecodeAt ev bytecode
      (r.2.1.take (Tables.layoutOf bytecode logMem rowsN).logBytecode ++ vsAlphas σ) (σ (.n 856)) →
    RunsTo (Tables.tablesSeg ev (Tables.layoutOf bytecode logMem rowsN) pi (vsAlphas σ) (σ (.n 836))
      r.2.1 r.2.2) ⟨[σ (.n 839), σ (.n 840), σ (.n 841), σ (.n 842), σ (.n 843)], []⟩ xsT
      (bus, claims) ⟨capT, []⟩
  hclaimsL : claims.length = Tables.nClaims
  hpool : ReadsAt rd (σ (.n 7)) (claims.map (·.value))
  hctx : Tables.TCtx rd (Tables.layoutOf bytecode logMem rowsN) bus claims
    [σ (.n 523), σ (.n 848), σ (.n 857), σ (.n 522), σ (.n 855), σ (.n 8)]
  hcapT : [σ (.n 849), σ (.n 850), σ (.n 851), σ (.n 852), σ (.n 853)] = capT
  e854 : σ (.n 854) = σ (.n 844) * gen ^ xsT.length
  l858 : LoadHolds rd (σ (.n 129)) 6 (σ (.n 858))
  e862 : σ (.n 862) = σ (.n 7) * word 1899956092796928 0 0
  hkc : C "verify_keccak" [σ (.n 849), σ (.n 850), σ (.n 851), σ (.n 852), σ (.n 853), σ (.n 854),
      σ (.n 858), σ (.n 848), σ (.n 862), σ (.n 859), σ (.n 860)]
    [σ (.n 863), σ (.n 864), σ (.n 865), σ (.n 866), σ (.n 867), σ (.n 868), σ (.n 869), σ (.n 870)]
  hcopy : ∀ i < 5, σ (.n (871 + i)) = σ (.n (863 + i))

theorem gSquares_of_exp {rd : Reader} {lp sq : E} (h : ExpTables rd lp sq) :
    ReadsAt rd sq Tables.gSquaresList := by
  intro k hk
  simp only [Tables.gSquaresList, List.length_map, List.length_range] at hk
  simpa [Tables.gSquaresList] using (h k hk).2

theorem readsAt_ext {rd : Reader} {p : E} {xs ys : List E} (hl : xs.length = ys.length)
    (hx : ReadsAt rd p xs) (hy : ReadsAt rd p ys) : xs = ys :=
  List.ext_getElem hl fun k h1 h2 ↦ loadHolds_unique (hx k h1) (hy k h2)

theorem pushTotal_ge (m : ℕ) (hs : List ℕ) : 2 ^ m ≤ pushTotal m hs := by
  unfold pushTotal
  have : 2 ^ pushKappa m hs 1 ∈ (List.range 54).map fun b ↦ 2 ^ pushKappa m hs b :=
    List.mem_map.2 ⟨1, by simp, rfl⟩
  have h1 : pushKappa m hs 1 = m := by simp [pushKappa, Tables.blockKappaSrc, Tables.blockKappaAdj]
  rw [h1] at this
  exact List.le_sum_of_mem this


theorem vsPushT_noRet : Stmt.noRetList vsPushT = true := by decide +kernel

/-- The rows certified by a `verify_tables` call, at any point its precondition admits. -/
theorem tables_heights {bytecode : List K} {rd : Reader} {pi : Digest} {logMem : ℕ}
    {alphas point values : List E} {σ : Val}
    (hT : Tables.TablesOut bytecode pi logMem alphas point values rd
      [σ (.n 839), σ (.n 840), σ (.n 841), σ (.n 842), σ (.n 843), σ (.n 844), σ (.n 0), σ (.n 1),
        σ (.n 523), σ (.n 522), σ (.n 129), σ (.n 28), σ (.n 149), σ (.n 5), σ (.n 640),
        σ (.n 836), σ (.n 7), σ (.n 8), σ (.n 848), σ (.n 845), σ (.n 846), σ (.n 847)]
      [σ (.n 849), σ (.n 850), σ (.n 851), σ (.n 852), σ (.n 853), σ (.n 854), σ (.n 855),
        σ (.n 856), σ (.n 857)]) :
    ∃ rowsN : List ℕ, rowsN.length = 6 ∧
      ReadsAt rd (σ (.n 129)) (gen ^ logMem :: (Tables.tableHeightsOf rowsN).map (gen ^ ·)) ∧
      ∀ h ∈ Tables.tableHeightsOf rowsN, h < 29 := by
  obtain ⟨-, -, rowsN, -, -, hl, -, hd, hh, -⟩ := hT
  exact ⟨rowsN, hl, hd, hh⟩

theorem tableHeights_length (rowsN : List ℕ) (h : rowsN.length = 6) :
    (Tables.tableHeightsOf rowsN).length = 6 := by
  simp [Tables.tableHeightsOf, h, tableLogFloors]

/-- **`verify_sub`'s front.** -/
theorem vs_front {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (L : MemImage κ) {C : CallRel}
    (hC : CallRel.Le C (coreProgram.Rel L.read)) (bytecode : List K)
    (hgkr : Tables.verify_bus_gkr_SpecC L.read C) (htab : Tables.verify_tables_SpecC bytecode L.read C)
    {σ : Val} {next : Prop} {kret : List E → Prop}
    (hexp : ExpTables L.read (σ (.n 4)) (σ (.n 5)))
    (h : Stmt.HoldsList C L.read σ (vsHeadT ++ vsReadsT ++ vsSizesT ++ vsKappaT ++ vsPushT ++
      vsRootsT ++ vsAlphasT ++ vsFpwT ++ vsCallsT) next kret) :
    Nonempty (VsFront bytecode C L.read σ) ∧ next := by
  simp only [holdsList_append] at h
  obtain ⟨h10, h11, h12, h13, hk, h⟩ := vsHeadT_holds h
  obtain ⟨seed, pi, hseed, hpi, hcap0⟩ := vs_seed hk h10 h11 h12 h13
  obtain ⟨hw, hrw, hk50, h⟩ := vsReadsT_holds h
  obtain ⟨lir, logMem, hl1, hl4, e112, e124, hm16, hm32, e29, e130, ds, hdsL, hdims0, hkb0, h⟩ :=
    vsSizesT_holds hκ hκ6 L hC h
  obtain ⟨hbk0, h⟩ := vsKappaT_holds hdsL hkb0 h
  obtain ⟨hP, h⟩ := (holdsList_noRet vsPushT vsPushT_noRet _ _).1 h
  obtain ⟨hk649, w8, w9, ca1, ca2, h⟩ := vsRootsT_holds h
  obtain ⟨halpha, halphaR, h⟩ := vsAlphasT_holds h10 h11 h12 h13 w8 w9 h
  obtain ⟨hfpw, h⟩ := vsFpwT_holds (alphas := vsAlphas σ) rfl halphaR h
  obtain ⟨hbeta, h⟩ := vsSqzT_holds h10 h11 h12 h13 h
  obtain ⟨e838, cg, ct, l858, e862, ck, hcopy, hn⟩ := vsCallsT_holds h
  have hc537 := ((assert_canonical_holds L.read _ _).1 (hC _ _ _ ca1)).1
  have hc547 := ((assert_canonical_holds L.read _ _).1 (hC _ _ _ ca2)).1
  have ct' : C "verify_tables" [σ (.n 839), σ (.n 840), σ (.n 841), σ (.n 842), σ (.n 843),
      σ (.n 844), σ (.n 0), σ (.n 1), σ (.n 523), σ (.n 522), σ (.n 129), σ (.n 28), σ (.n 149),
      σ (.n 5), σ (.n 640), σ (.n 836), σ (.n 7), σ (.n 8), σ (.n 848), σ (.n 845), σ (.n 846),
      σ (.n 847)] [σ (.n 849), σ (.n 850), σ (.n 851), σ (.n 852), σ (.n 853), σ (.n 854),
      σ (.n 855), σ (.n 856), σ (.n 857)] := ct
  have hTA : ∀ point : List E, ReadsAt L.read (σ (.n 523)) point →
      σ (.n 522) = gen ^ point.length → point.length < 33 →
      Tables.TablesOut bytecode pi logMem (vsAlphas σ) point [σ (.n 845), σ (.n 846), σ (.n 847)]
        L.read _ _ := fun point hp hg hl ↦ htab pi logMem (vsAlphas σ) point _ _ _
      (by
        simp only [Tables.TablesPre]
        exact ⟨hpi, hp, hg, hl, hm16, hm32, ⟨ds, hdsL, hdims0, hbk0⟩, gSquares_of_exp hexp, rfl,
          hfpw, trivial⟩) ct'
  -- the push total, once the heights are certified
  have hpush : ∀ rowsN : List ℕ, rowsN.length = 6 →
      ReadsAt L.read (σ (.n 129)) (gen ^ logMem :: (Tables.tableHeightsOf rowsN).map (gen ^ ·)) →
      (∀ h ∈ Tables.tableHeightsOf rowsN, h < 29) →
      ds = (Tables.tableHeightsOf rowsN).map (gen ^ ·) ∧
      σ (.n 522) = gen ^ log2Ceil (pushTotal logMem (Tables.tableHeightsOf rowsN)) ∧
        log2Ceil (pushTotal logMem (Tables.tableHeightsOf rowsN)) < 34 := by
    intro rowsN hrl hd hh
    have eds : ds = (Tables.tableHeightsOf rowsN).map (gen ^ ·) := by
      have := readsAt_ext (by simp [hdsL, tableHeights_length rowsN hrl]) hdims0 hd
      simpa using this
    subst eds
    obtain ⟨e, b, -⟩ := vsPushT_holds hκ hκ6 L hC hexp (tableHeights_length rowsN hrl) hh hm32
      hbk0 hP
    exact ⟨rfl, e, b⟩
  have hpos : ∀ rowsN : List ℕ, 0 < log2Ceil (pushTotal logMem (Tables.tableHeightsOf rowsN)) :=
    fun rowsN ↦ lt_log2Ceil_iff.2 (lt_of_lt_of_le (by
      have := Nat.one_lt_two_pow_iff.2 (show logMem ≠ 0 by omega)
      simpa using this) (pushTotal_ge logMem _))
  have hne : σ (.n 522) ≠ 1 := by
    intro h1
    obtain ⟨rowsN, hrl, hd, hh⟩ := tables_heights (hTA [] (fun k hk ↦ absurd hk (by simp))
      (by rw [h1, List.length_nil, pow_zero]) (by simp))
    obtain ⟨-, e, b⟩ := hpush rowsN hrl hd hh
    rw [h1, ← pow_zero gen] at e
    have := gen_pow_inj (by norm_num) (by omega) e
    have := hpos rowsN
    omega
  obtain ⟨depth, xsG, r, capG, hgmu, hdlt, hxsG, hrunG, hptL, hvL, hzeta, hretG⟩ :=
    hgkr _ _ (by simpa using hne) cg
  have hretG' : [σ (.n 839), σ (.n 840), σ (.n 841), σ (.n 842), σ (.n 843), σ (.n 844)] ++
      [σ (.n 845), σ (.n 846), σ (.n 847)] = (capG ++ [σ (.n 838) * gen ^ xsG.length]) ++ r.2.2 :=
    hretG
  obtain ⟨hret1, hvals⟩ := List.append_inj' hretG' (by rw [hvL]; rfl)
  rw [show [σ (.n 839), σ (.n 840), σ (.n 841), σ (.n 842), σ (.n 843), σ (.n 844)] =
    [σ (.n 839), σ (.n 840), σ (.n 841), σ (.n 842), σ (.n 843)] ++ [σ (.n 844)] from rfl] at hret1
  obtain ⟨hcapG, h844⟩ := List.append_inj' hret1 rfl
  simp only [List.cons.injEq, and_true] at h844
  have hT := hTA r.2.1 hzeta (by rw [hptL]; exact hgmu) (by rw [hptL]; exact hdlt)
  obtain ⟨xsT, capT, rowsN, bus, claims, hrl, hrows, hdims, hh, hxsT, hrunT, hcl, hpool, hctx,
    hcapT, e854⟩ := hT
  obtain ⟨eds, e522, hlt⟩ := hpush rowsN hrl hdims hh
  have edep : depth = log2Ceil (pushTotal logMem (Tables.tableHeightsOf rowsN)) :=
    gen_pow_inj (by omega) (by omega) (hgmu.symm.trans e522)
  rw [eds] at hbk0 hkb0
  rw [edep] at hrunG hptL hdlt
  refine ⟨⟨VsFront.mk
    (seed := seed) (pi := pi) (hseed := hseed) (hpi := hpi) (hcap0 := hcap0) (h10 := h10)
    (h11 := h11) (h12 := h12) (h13 := h13) (hw := hw) (hrw := hrw) (w8 := w8) (w9 := w9)
    (hc537 := hc537)
    (hc547 := hc547) (hab8 := vs_absorb8 hw hk50) (habR := vs_absorbRoot hw hk649)
    (halpha := halpha) (hbeta := hbeta) (halphaR := halphaR) (hfpw := hfpw) (lir := lir)
    (logMem := logMem) (hl1 := hl1) (hl4 := hl4) (e112 := e112) (e124 := e124) (hm16 := hm16)
    (hm32 := hm32) (e29 := e29) (e130 := e130) (rowsN := rowsN) (hrowsL := hrl) (hrows := hrows)
    (hdims := hdims) (hh29 := hh) (hkb := hkb0) (hbk := hbk0) (e522 := e522) (hdep := hdlt)
    (xsG := xsG) (r := r) (capG := capG) (hxsG := (by rw [← e838]; exact hxsG)) (hrunG := ?_)
    (hptL := hptL) (hvL := hvL) (hzeta := hzeta)
    (hretG := (by rw [← e838]; exact hretG')) (xsT := xsT) (capT := capT)
    (bus := bus) (claims := claims) (hxsT := hxsT) (hrunT := ?_) (hclaimsL := hcl)
    (hpool := hpool) (hctx := hctx) (hcapT := hcapT) (e854 := e854) (l858 := l858) (e862 := e862)
    (hkc := ck) (hcopy := hcopy)⟩, hn⟩
  · exact hrunG
  · rw [← hvals]; exact hrunT

end
end LeanVM.Guest.B1.VerifySub
