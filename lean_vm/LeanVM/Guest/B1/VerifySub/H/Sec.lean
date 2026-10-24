/-
  LeanVM.Guest.B1.VerifySub.H.Sec

  The sections' data (`VsSecData`) of `verify_sub`'s honest valuation on an honest child: the
  memory holding the own buffers and the caller's words, the callees' results the honest ones.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.Vals
public import LeanVM.Guest.B1.VerifySub.H.Kids

/-!
# The sections' data, honestly

`vsSec`: with the own buffers' honest words (`ChildSegs.ownW`) at the pointers `bs`, the exponent
tables and the child's fixed cells at `lpE`, `sqE`, `outE`, the memory defined below `2^κ`
(`κ ≥ 16`) and the callees' results the honest ones (`g_power_of_word`'s, `verify_tables`',
`verify_keccak`'s, the stack's log), the honest valuation on the oracle `vsW bs outs` has the
sections' data: `vsCPre_complete` applies.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node

@[expose] public section

theorem readsAt_getD' {rd : Reader} {p : E} {xs : List E} {k : ℕ} (h : ReadsAt rd p xs)
    (hk : k < xs.length) : LoadHolds rd p k (xs.getD k 0) := by
  rw [List.getD_eq_getElem _ _ hk]; exact h k hk

variable {rd : Reader} {args : List E}

theorem vsRetVars_runs : (∀ i < 9, (vsRetVars.getD 5 []).getD i 0 = 839 + i) ∧
    (∀ i < 9, (vsRetVars.getD 6 []).getD i 0 = 849 + i) ∧
    (∀ i < 8, (vsRetVars.getD 7 []).getD i 0 = 863 + i) ∧
    (∀ i < 5, (vsRetVars.getD 11 []).getD i 0 = 1906 + i) := by decide

theorem vsRetVars_lens : (vsRetVars.getD 5 []).length = 9 ∧ (vsRetVars.getD 6 []).length = 9 ∧
    (vsRetVars.getD 7 []).length = 8 ∧ (vsRetVars.getD 11 []).length = 5 := by decide

set_option maxRecDepth 100000 in
theorem vs_e124 (hl : args.length = 7) {w : ℕ → E} {lir : ℕ}
    (e122 : vsσ rd w args (.n 122) = gen ^ lir) (h1 : 1 ≤ lir) :
    vsσ rd w args (.n 124) = gen ^ (lir - 1) := by
  have hG := vsSizesT_good (rd := rd) (w := w) hl
  have g1 := hG (vsMul 122 124 123) (by
    rw [vsSizesT]
    exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have g2 := hG (vsConst 123 (word 2 0 0)) (by
    rw [vsSizesT]; exact List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self))
  simp only [vsMul, vsConst, GoodS] at g1 g2
  simp only [Good] at g2
  rw [good_mul_old (by decide) g1, e122, g2, word_gen]
  have : gen ^ lir = gen ^ (lir - 1) * gen := by rw [← pow_succ, Nat.sub_add_cancel h1]
  rw [this, mul_assoc, mul_inv_cancel₀ gen_ne_zero, mul_one]

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

theorem stream_length (S : ChildSegs bytecode seed c) : 10 ≤ c.proof.stream.length := by
  have := S.hrowsL
  rw [S.hstream]; simp; omega

theorem rows_eq : ∃ a b c d e f, S.rowsN = [a, b, c, d, e, f] := by
  match h : S.rowsN, S.hrowsL with
  | [a, b, c, d, e, f], _ => exact ⟨a, b, c, d, e, f, rfl⟩

theorem words_getD7 : S.words.getD 7 0 = eOfNat S.rate := by
  obtain ⟨a, b, c, d, e, f, hr⟩ := S.rows_eq
  simp [ChildSegs.words, hr]

theorem words_getD_rows {i : ℕ} (hi : i < 6) :
    S.words.getD (i + 1) 0 = (S.rowsN.map eOfNat).getD i 0 := by
  obtain ⟨a, b, c, d, e, f, hr⟩ := S.rows_eq
  interval_cases i <;> simp [ChildSegs.words, hr]

theorem poolW_length (hbl : bytecode.length = 2 ^ 23) : S.H.poolW.length = 165 := by
  obtain ⟨hok, hx, -, hlen⟩ := S.H_run hbl
  have h1 := hok.hx5
  have h2 := hok.hxR
  have hf : S.H.evsT.flatten.length = 157 := by
    have := congrArg List.length hx
    simp only [List.length_append, h1, h2] at this
    omega
  simp [Tables.VtHonest.poolW, Tables.VtHonest.pcW, h1, hf]

theorem rchs_length : S.rchs.length = 6 := by
  have := congrArg (fun p ↦ p.1.length) S.hchs
  simp only [squeezeN_len] at this
  simp [ChildSegs.rchs, ← this]

theorem s7_eta (hbl : bytecode.length = 2 ^ 23) : S.s7 = ⟨S.s7.cap, []⟩ := by
  have h := S.runK
  rw [S.hlayout, (S.lanes hbl).1, (S.lanes hbl).2.1, (S.H_run hbl).2.2.1] at h
  obtain ⟨K, hK⟩ := keccakSeg_capOf h (S.runK' hbl).2.2.2.2
  rw [hK]

end ChildSegs

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **The sections' data of the honest valuation on an honest child.** -/
theorem vsSec {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {seed : Digest} {c : Child}
    (S : ChildSegs bytecode seed c) {lpE sqE outE : ℕ}
    (hargs : args = [(digestScalars (statementDigest seed c.statement)).1,
      (digestScalars (statementDigest seed c.statement)).2, (digestScalars seed).1,
      (digestScalars seed).2, ofK (gpow lpE), ofK (gpow sqE), ofK (gpow outE)])
    (bs : List ℕ) (outs : List (List E × Main.Layout)) {κ : ℕ} (hκ : 16 ≤ κ) (hlow : LowDef κ rd)
    (hmem : ∀ i < 16, ReadsAt rd (ofK (gpow (bs.getD i 0))) (S.ownW.getD i []))
    (hlp : ReadsAt rd (ofK (gpow lpE)) ((List.range 34).map fun j ↦ eOfNat (2 ^ j)))
    (hsq : ReadsAt rd (ofK (gpow sqE)) Tables.gSquaresList)
    (hfx : ReadsAt rd (ofK (gpow outE)) (fixedCells c.fresh))
    (o0 : (outs.getD 0 ([], [])).1 = [gen ^ S.rate])
    (o1 : (outs.getD 1 ([], [])).1 = [gen ^ S.logMem])
    (o6 : (outs.getD 6 ([], [])).1 = S.H.retsH (S.vtB bs sqE))
    (o7 : (outs.getD 7 ([], [])).1 =
      S.s7.cap ++ [ofK (gpow (S.cK bs)) * gen ^ S.xsK.length, S.word, S.m0])
    (o10 : (outs.getD 10 ([], [])).1 = [gen ^ max 15 (log2Ceil (Tables.stackTotal S.kappas))]) :
    ∃ D : VsSecData rd (vsW bs outs) args,
      D.vals = (fun i ↦ S.H.poolW.getD (vsKept i) 0) ∧ D.m = S.μs ∧ D.r = S.rate ∧
      D.τg = gen ^ S.τ ∧ VsFrontH S rd (vsσ rd (vsW bs outs) args) ∧
      vsσ rd (vsW bs outs) args (.n 1323) = S.lam ∧
      S.s8 = ⟨[vsσ rd (vsW bs outs) args (.n 966), vsσ rd (vsW bs outs) args (.n 967),
        vsσ rd (vsW bs outs) args (.n 968), vsσ rd (vsW bs outs) args (.n 969),
        vsσ rd (vsW bs outs) args (.n 970)], []⟩ ∧
      vsσ rd (vsW bs outs) args (.n 870) = S.m0 ∧ vsChs (vsσ rd (vsW bs outs) args) = S.chs := by
  have hl : args.length = 7 := by rw [hargs]; rfl
  have ptr : ∀ i < 16, vsσ rd (vsW bs outs) args (.n (vsAllocVars.getD i 0)) =
      ofK (gpow (bs.getD i 0)) := fun i hi ↦ vs_alloc_ptr hl bs outs hi
  have ret : ∀ j < 13, ∀ k < (vsRetVars.getD j []).length,
      vsσ rd (vsW bs outs) args (.n ((vsRetVars.getD j []).getD k 0)) =
        (outs.getD j ([], [])).1.getD k 0 := fun j hj k hk ↦ vs_ret_val hl bs outs hj hk
  have m : ∀ i < 16, ReadsAt rd (vsσ rd (vsW bs outs) args (.n (vsAllocVars.getD i 0)))
      (S.ownW.getD i []) := fun i hi ↦ by rw [ptr i hi]; exact hmem i hi
  have par : ∀ i < 7, vsσ rd (vsW bs outs) args (.n i) = args.getD i 0 :=
    fun i hi ↦ vsC_param hl hi
  have hsl := S.hs_length
  have hh := S.hh29 hbl
  -- the stream
  have mS : ReadsAt rd (vsσ rd (vsW bs outs) args (.n 27)) (vsStreamW c.proof.stream) :=
    m 2 (by norm_num)
  have hsl10 := S.stream_length
  have hws : ∀ i < 10, LoadHolds rd (vsσ rd (vsW bs outs) args (.n 27)) i
      (c.proof.stream.getD i 0) := fun i hi ↦ by
    have := readsAt_getD' mS (k := i) (by simp [vsStreamW]; omega)
    rwa [vsStreamW, List.getD_append _ _ _ _ (by omega)] at this
  have F := vsH_spec hbl S hargs hws
  obtain ⟨hw8, hx8, hx9⟩ := S.stream_getD
  generalize hσ : vsσ rd (vsW bs outs) args = σ at *
  -- the callees' results
  have e122 : σ (.n 122) = gen ^ S.rate := by
    have := ret 0 (by norm_num) 0 (by decide); rw [o0] at this; exact this
  have e130 : σ (.n 130) = gen ^ S.logMem := by
    have := ret 1 (by norm_num) 0 (by decide); rw [o1] at this; exact this
  obtain ⟨K7, hK7⟩ := S.s7_capOf hbl
  have e863 : ∀ i < 5, σ (.n (863 + i)) = (capOf K7).getD i 0 := fun i hi ↦ by
    have := ret 7 (by norm_num) i (by rw [vsRetVars_lens.2.2.1]; omega)
    rw [vsRetVars_runs.2.2.1 i (by omega), o7, hK7,
      List.getD_append _ _ _ _ (by simp [capOf]; omega)] at this
    exact this
  have e870 : σ (.n 870) = S.m0 := by
    have := ret 7 (by norm_num) 7 (by decide)
    rw [vsRetVars_runs.2.2.1 7 (by norm_num), o7, hK7] at this
    exact this
  have e856 : σ (.n 856) = c.fresh.bytecodeValue := by
    have := ret 6 (by norm_num) 7 (by decide)
    rw [vsRetVars_runs.2.1 7 (by norm_num), o6] at this
    exact this
  have e1890 : σ (.n 1890) = gen ^ S.μs := by
    have := ret 10 (by norm_num) 0 (by decide)
    rw [o10] at this
    simp only [vsRetVars, List.getD_cons_zero, List.getD_cons_succ] at this
    rw [this, ChildSegs.μs, S.hlayout, stackLog_eq hbl]
    rfl
  -- the memory's words
  have hcount : S.hs.map Hints.count = S.hs.map (gen ^ ·) :=
    List.map_congr_left fun x hx ↦ count_eq_gen (by have := hh x hx; omega)
  have hdims : ReadsAt rd (σ (.n 129)) (gen ^ S.logMem :: S.hs.map Hints.count) := m 4 (by norm_num)
  have hkb : ReadsAt rd (σ (.n 141)) (1 :: gen ^ S.logMem :: S.hs.map Hints.count) :=
    m 5 (by norm_num)
  have hbk : ReadsAt rd (σ (.n 149))
      (Tables.blockKappaWords (gen ^ S.logMem) (S.hs.map (gen ^ ·))) := by
    have := m 6 (by norm_num); rw [← hcount]; exact this
  have hexp : ExpTables rd (σ (.n 4)) (σ (.n 5)) := by
    rw [par 4 (by norm_num), par 5 (by norm_num), hargs]
    intro j hj
    refine ⟨?_, ?_⟩
    · have := readsAt_getD' hlp (k := j) (by simpa using hj)
      simpa [List.getD_eq_getElem?_getD, hj] using this
    · have := readsAt_getD' hsq (k := j) (by simpa [Tables.gSquaresList] using hj)
      simpa [Tables.gSquaresList, List.getD_eq_getElem?_getD, hj] using this
  -- the bus challenges
  have mA : ReadsAt rd (σ (.n 559)) S.alphas := m 8 (by norm_num)
  have hA4 : vsAlphas σ = S.alphas := F.halphas
  have mA' : ReadsAt rd (σ (.n 559)) (vsAlphas σ) := by rw [hA4]; exact mA
  have mF : ReadsAt rd (σ (.n 640)) (eqKernel (vsAlphas σ)) := by
    rw [hA4]; exact m 9 (by norm_num)
  -- `dims_g[6]`
  have hd6 : LoadHolds rd (σ (.n 129)) 6 (gen ^ S.τ) := by
    have := readsAt_getD' hdims (k := 6) (by simp [hsl])
    rw [show (gen ^ S.logMem :: S.hs.map Hints.count).getD 6 0 = Hints.count (S.hs.getD 5 0) by
      rw [List.getD_cons_succ, List.getD_eq_getElem _ _ (by simp [hsl]), List.getElem_map,
        List.getD_eq_getElem _ _ (by omega)]] at this
    rw [count_eq_gen (by have := (S.τ_bounds hbl).2.1; unfold ChildSegs.τ at this; omega)] at this
    exact this
  -- the copies of `verify_keccak`'s capacity
  have hcp := (vsCallsT_complete (rd := rd) (w := vsW bs outs) (C := fun _ _ _ ↦ True)
    (next := True) (kret := fun _ ↦ True) hl (τg := gen ^ S.τ) (by rw [hσ]; exact hd6) trivial
    trivial trivial trivial).2.2.2.1
  rw [hσ] at hcp
  have hc871 : ∀ i < 5, IsCanonical128 (σ (.n (871 + i))) := fun i hi ↦ by
    rw [hcp i hi, e863 i hi]
    exact Tables.tb_capOf_canonical _ _ (by
      rw [List.getD_eq_getElem _ _ (by simp [capOf]; omega)]; exact List.getElem_mem _)
  -- the ring map
  have hM := vsH_maps (rd := rd) (w := vsW bs outs) hl (by rw [hσ]; exact hc871)
  rw [hσ] at hM
  have hs7 : (⟨[σ (.n 871), σ (.n 872), σ (.n 873), σ (.n 874), σ (.n 875)], []⟩ : Fs) = S.s7 := by
    have hc := fun i (hi : i < 5) ↦ (hcp i hi).trans (e863 i hi)
    have h0 : σ (.n 871) = cellsOfState K7 false 8 := hc 0 (by norm_num)
    have h1 : σ (.n 872) = cellsOfState K7 false 9 := hc 1 (by norm_num)
    have h2 : σ (.n 873) = cellsOfState K7 false 10 := hc 2 (by norm_num)
    have h3 : σ (.n 874) = cellsOfState K7 false 11 := hc 3 (by norm_num)
    have h4 : σ (.n 875) = cellsOfState K7 false 12 := hc 4 (by norm_num)
    rw [S.s7_eta hbl, hK7, h0, h1, h2, h3, h4]
    rfl
  have hchs := S.hchs
  rw [← hs7, hM.1] at hchs
  simp only [Prod.mk.injEq] at hchs
  obtain ⟨ech, es8⟩ := hchs
  -- the batching challenge
  have hL := vsH_lam (rd := rd) (w := vsW bs outs) hl (by rw [hσ]; exact hM.2)
  rw [hσ] at hL
  have elam : σ (.n 1323) = S.lam := by
    rw [ChildSegs.lam, ← es8, hL]
  -- the fixed cells
  have hfx' : ReadsAt rd (σ (.n 6)) (S.point.take 19 ++ S.alphas ++ [c.fresh.bytecodeValue]) := by
    rw [par 6 (by norm_num), hargs]
    have := hfx
    rw [fixedCells, S.fresh_eq hbl] at this
    exact this
  have hμ := S.μ_bounds hbl
  have hpl := (S.runG' hbl).2.2.1
  have hal : S.alphas.length = 4 := by
    have := congrArg List.length hA4; simpa [vsAlphas] using this.symm
  refine ⟨{
    hl := hl
    hc4 := fun i hi ↦ by
      have c1 := digest_canonical (statementDigest seed c.statement)
      have c2 := digest_canonical seed
      rw [hargs]
      interval_cases i
      · exact c1.1
      · exact c1.2
      · exact c2.1
      · exact c2.2
    ws := c.proof.stream
    hws := fun i hi ↦ by rw [hσ]; exact hws i (by omega)
    hrows := fun i hi ↦ by
      rw [hσ, hw8 (i + 1) (by omega), S.words_getD_rows hi]
      exact readsAt_getD' (m 3 (by norm_num)) (by simp [S.hrowsL]; omega)
    hcap22 := by rw [hσ]; exact F.hcap22
    κ := κ
    hκ6 := by omega
    hlow := hlow
    lir := S.rate
    logMem := S.logMem
    hl1 := S.hr1
    hl4 := S.hr4
    hm16 := S.h16
    hm32 := S.h32
    e112 := by rw [hσ]; have := F.hx 7 (by norm_num); rw [hw8 7 (by norm_num), S.words_getD7] at this; exact this
    e29 := by rw [hσ]; have := F.hx 0 (by norm_num); rw [hw8 0 (by norm_num)] at this; exact this
    e122 := by rw [hσ]; exact e122
    e130 := by rw [hσ]; exact e130
    hs := S.hs
    hsl := hsl
    hh := hh
    hdims := by rw [hσ]; exact hdims
    hkb := by rw [hσ]; exact hkb
    hcount := hcount
    hbk := by rw [hσ]; exact hbk
    hexp := by rw [hσ]; exact hexp
    hin := by rw [hσ]; exact F.hin
    x0 := S.x0
    x1 := S.x1
    hw8 := by rw [hσ, ← hx8]; exact hws 8 (by norm_num)
    hw9 := by rw [hσ, ← hx9]; exact hws 9 (by norm_num)
    hz := by rw [hσ]; exact F.hz
    hcap532 := by rw [hσ]; exact F.hc532
    hA := fun k hk ↦ by
      rw [hσ]
      have := readsAt_getD' mA' (k := k) (by simp [vsAlphas]; omega)
      interval_cases k <;> exact this
    a0 := σ (.n 579)
    a1 := σ (.n 599)
    a2 := σ (.n 619)
    a3 := σ (.n 639)
    ha := by rw [hσ]; exact mA'
    hfp := by rw [hσ]; exact mF
    hcap628 := by rw [hσ]; exact F.hc628
    τg := gen ^ S.τ
    hd6 := by rw [hσ]; exact hd6
    hcap871 := by rw [hσ]; exact hc871
    hM := fun k hk ↦ by
      rw [hσ]
      have mC : ReadsAt rd (σ (.n 876)) S.rchs := m 13 (by norm_num)
      have := readsAt_getD' mC (k := k) (by rw [S.rchs_length]; omega)
      rw [ChildSegs.rchs, ← ech] at this
      interval_cases k
      · show LoadHolds rd (σ (.n 876)) 0 (σ (.n 870)); rw [e870]; exact this
      all_goals exact this
    chs := S.rchs
    hcl := S.rchs_length
    hchs := by rw [hσ]; exact m 13 (by norm_num)
    hct := by rw [hσ]; exact m 14 (by norm_num)
    hcap966 := by rw [hσ]; exact hM.2
    vals := fun i ↦ S.H.poolW.getD (vsKept i) 0
    hpool := fun i hi ↦ by
      rw [hσ]
      have mP : ReadsAt rd (σ (.n 7)) S.H.poolW := m 0 (by norm_num)
      exact readsAt_getD' mP (by rw [S.poolW_length hbl]; exact vsKept_lt hi)
    hlam := fun i hi ↦ by
      rw [hσ, elam]
      have mL : ReadsAt rd (σ (.n 1324)) (lamW S.lam) := m 15 (by norm_num)
      have := readsAt_getD' mL (k := vsKept i) (by rw [lamW_length]; exact vsKept_lt hi)
      have hk : vsKept i ∈ (List.range Tables.nClaims).filter
          (fun j ↦ Tables.claimColumns.getD j 0 ∉ keccakOutputColumns) := by
        rw [kept_eq]; exact List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩
      have hnot := (List.mem_filter.1 hk).2
      simp only [decide_eq_true_eq] at hnot
      rw [lamW, List.getD_eq_getElem _ _ (by simpa using vsKept_lt hi), List.getElem_map,
        List.getElem_range, ite_eq_right_of_eq_false _ _ (eq_false hnot), poolRank_kept i hi,
        add_comm] at this
      exact this
    m := S.μs
    r := S.rate
    hm22 := S.hmu22
    hm28 := S.hmu28
    hr1 := S.hr1
    hr4 := S.hr4
    e1890 := by rw [hσ]; exact e1890
    e124 := vs_e124 hl (by rw [hσ]; exact e122) S.hr1
    zs := fun k ↦ S.point.getD k 0
    al := fun k ↦ S.alphas.getD k 0
    hzeta := fun k hk ↦ by
      rw [hσ]
      have mZ : ReadsAt rd (σ (.n 523)) S.point := m 7 (by norm_num)
      exact readsAt_getD' mZ (by rw [hpl]; omega)
    halpha := fun k hk ↦ by rw [hσ]; exact readsAt_getD' mA (by omega)
    hout := fun k hk ↦ by
      rw [hσ]
      have := readsAt_getD' hfx' (k := k) (by
        simp only [List.length_append, List.length_take, List.length_cons, List.length_nil, hpl, hal]
        omega)
      rw [List.append_assoc, List.getD_append _ _ _ _ (by simp only [List.length_take, hpl]; omega),
        List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk, ← List.getD_eq_getElem?_getD]
        at this
      exact this
    hout' := fun k hk ↦ by
      rw [hσ]
      have := readsAt_getD' hfx' (k := 19 + k) (by
        simp only [List.length_append, List.length_take, List.length_cons, List.length_nil, hpl, hal]
        omega)
      rw [List.getD_append _ _ _ _ (by simp only [List.length_append, List.length_take, hpl, hal]; omega),
        List.getD_append_right _ _ _ _ (by simp only [List.length_take, hpl]; omega)] at this
      simpa [hpl, show min 19 S.μ = 19 by omega] using this
    hout23 := by
      rw [hσ, e856]
      have := readsAt_getD' hfx' (k := 23) (by
        simp only [List.length_append, List.length_take, List.length_cons, List.length_nil, hpl, hal]
        omega)
      rw [List.getD_append_right _ _ _ _ (by simp only [List.length_append, List.length_take, hpl, hal]; omega)] at this
      simpa [hpl, hal, show min 19 S.μ = 19 by omega] using this }, ?_⟩
  subst hσ
  exact ⟨rfl, rfl, rfl, rfl, F, elam, es8.symm, e870, ech⟩

end
end LeanVM.Guest.B1.VerifySub
