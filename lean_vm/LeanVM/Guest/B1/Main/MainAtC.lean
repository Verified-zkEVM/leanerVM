/-
  LeanVM.Guest.B1.Main.MainAtS

  `MainAt.lean` under any semantics of `BLAKE2S` (`S : BlakeSem`).
-/

module

public import LeanVM.Guest.B1.Main.MainAt
public import LeanVM.Guest.B1.Main.AggRegionC
public import LeanVM.Guest.B1.Main.MainWordsC
public import LeanVM.Guest.B1.Main.MainCS
public import LeanVM.Guest.B1.Main.WeightBS

/-!
# `MainAt.lean` under any `BLAKE2S` semantics

Each definition and lemma of `MainAt.lean` that mentions the semantics, with `S : BlakeSem` a
parameter and a `S` in its name.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1 (DisjL disj_nil disj_append bufL_disj Within LowDef CompleteAtB CompleteRelB Returns Kid CallsMatch OutsOk OutsIn
  RegionsOk outRegion kidsFromIn_of_kidsB kidsBound regionsOk_of memL_lins relAtIn_dmono within_append bufL
  bufL_region bufL_within)

@[expose] public section

variable {S : BlakeSem}

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-! ## `aggregate_claims` -/

/-- **`aggregate_claims`, complete under `S` over the answered hash `Ha`**
(`aggregate_claims_completeAt`): the batching from the guest's baked start closing over `Ha`, read
over `HdOf Ha`; reading the caller's buffers `aggExtL`, within `aggBound`. -/
theorem aggregateC_claims_completeAt {Ha : List UInt8 → Option Digest} (hF : FsRowsC S Ha)
    (hBs : BsRowsC S Ha) (κ : ℕ) {cs : List ChildClaims} {h : BatchHints}
    {d : DeferredClaim} (hne : cs ≠ []) (hlen : cs.length ≤ 16)
    (hb : batchWith (m := Option) Ha aggSeedD cs h = some (some d))
    (hbr : h.bytecodeRounds.length = 22) (hmr : h.matrixRounds.length = 28)
    (hsh : ∀ c ∈ cs, FreshShaped c.fresh ∧ c.carried.bytecodePoint.length = 22 ∧
      c.carried.matrixPoint.length = 28) (ap af ac ad : ℕ) :
    CompleteAtBS S fs cert κ "aggregate_claims" (aggExtL ap af ac ad cs d)
      [gen ^ cs.length, ofK (gpow ap), ofK (gpow af), ofK (gpow ac), ofK (gpow ad)] (Returns [])
      (aggBound fs cs.length) := by
  obtain ⟨hA, hbH⟩ := aggAns_of (Ht := HdOf Ha) (hag_HdOf Ha) hb
  intro fp
  obtain ⟨n, hn, hnB, hR⟩ := aggregateC_claims_relAtIn hF hBs fs cert hA hne hlen hbH hbr hmr hsh
    ap af ac ad fp
  refine ⟨n, aggOwnLH (HdOf Ha) fs fp cs h (ofK (gpow af)) (ofK (gpow ac)), [], [], ⟨rfl, rfl⟩, ?_,
    by simpa [aggOwnLH, bufL] using (bufL_disj (fp + fs "aggregate_claims") (aggSizes cs.length)
      (aggBufsH (HdOf Ha) cs h (ofK (gpow af)) (ofK (gpow ac)))
      (forall₂_of_map_length _ _ (length_aggBufsH (HdOf Ha) hbr hmr))),
    hnB, fun rd _ hL => relAtInS_dmono (hR rd (by simpa using hL)) fun i hi => ?_⟩
  · have := bufL_within (fp + fs "aggregate_claims") (aggSizes cs.length)
      (aggBufsH (HdOf Ha) cs h (ofK (gpow af)) (ofK (gpow ac)))
      (forall₂_of_map_length _ _ (length_aggBufsH (HdOf Ha) hbr hmr))
    simpa [aggOwnLH, bufL] using this.mono (b' := fp) (n' := n) (by omega) (by omega)
  · obtain ⟨q, hq, _⟩ := hi; simp at hq

/-! ## `main`'s own words -/

variable {Ha : List UInt8 → Option Digest} {κ : ℕ} {VsGood : VerifySub.VsData → VerifySub.VsRunC → Prop} {Bd : CalleeBounds} {fp : ℕ}
  {W : MainWords}

/-- **`MainOkS` from `main`'s words**, under the trivial call relation: the bounds, the signer
pair, the running counts, the leaf's `defer_stmt` and the public input. -/
theorem mainOkS_of_words (hκ : 16 ≤ κ) (hW : MainWordsOkC S fs Ha κ VsGood fp W) {rd : Reader}
    (hl : LowDef κ rd) (hL : MemL rd (mainIn fs fp W)) (hp0 : rd 1 = some (digestScalars W.stDig).1)
    (hp1 : rd g = some (digestScalars W.stDig).2) :
    MainOkS S (fun _ _ _ => True) rd (mainRunAt fs fp W) where
  low := hl.mono hκ
  total := hW.total
  nc := hW.nc
  rd1 := hW.rd1
  da := hW.da
  ud := hW.ud
  dau := hW.dau
  rx := hW.rx
  rs := hW.rs
  decl := hW.decl
  tables := trivial
  loop0 := fun _ => trivial
  daList := trivial
  xList := trivial
  sList := trivial
  loop1 := fun _ => trivial
  loop2 := fun _ => trivial
  sig := hW.sig
  sigp := mainIn_reads hL 3 (by omega)
  loop3 := fun _ => trivial
  loop4 := fun _ => trivial
  daVerify := fun _ => trivial
  daCover := fun _ => trivial
  written0 := hW.written0.load hL
  loop5 := fun _ => trivial
  writtenN := hW.writtenN.load hL
  leaf := fun h0 => by
    have := mainIn_reads hL 9 (by omega)
    simp only [MainWords.bufs, List.getD_cons_succ, List.getD_cons_zero, hW.leaf h0] at this
    exact this
  agg := fun _ => trivial
  stmt := trivial
  pub0 := hp0
  pub1 := hp1

/-! ## `main`'s path at `fp` -/

set_option maxRecDepth 100000 in
theorem mainS_allocs {rd : Reader} (hW : MainWordsOkC S fs Ha κ VsGood fp W) :
    mainAllocs.map (fun x => x.2.elim id fun s => logG (mainVal rd (mainRunAt fs fp W) s)) =
      W.sizes := by
  have ht := hW.total
  have hnc := hW.nc
  have hd := hW.dau
  unfold MainWords.total at ht
  simp only [mainAllocs, List.map_cons, List.map_nil, Sum.elim_inl, Sum.elim_inr, id, mainVal,
    mainRunAt]
  b1_look
  simp only [MainWords.sizes, MainWords.total, List.cons.injEq, and_true]
  have hlg : ∀ {x : E} (e : ℕ), x = gen ^ e → e < 2 ^ 64 - 1 → logG x = e :=
    fun e hx he => by rw [hx]; exact logG_gen_pow'' he
  and_intros
  all_goals first | trivial | exact hlg _ (by ring) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- **`main` at `fp`, from its callees**: the callees after `exponent_tables` as `Kid`s reading
`mainIn`, within bounds `bs` (`KidsBS`), matching `main`'s frames under its valuation. -/
theorem mainS_relAtIn_coreW {Θ : Type} {w : Θ → String → ℕ} (Wt : ∀ θ, MainWeightHypsS S fs (w θ))
    (hκ : 16 ≤ κ) (hW : MainWordsOkC S fs Ha κ VsGood fp W) (ks : List Kid)
    (bs : List ℕ) (bws : List (Θ → ℕ)) (hks : KidsWS S fs cert w κ ks bs bws)
    (hsub : ∀ k ∈ ks, SubL k.Lin (mainIn fs fp W))
    (hcm : ∀ rd, ∀ outs, OutsOk ks outs → CallsMatch (mainVal rd (mainRunAt fs fp W))
      ((mainFronts (decide (W.rd = 1)) (decide (W.nc = 0))).map
        (mkCall (mainVal rd (mainRunAt fs fp W)))) ks outs) :
    ∃ (m : ℕ) (L : Layout), Within (mainIn fs fp W ++ L) (fp + fs "main") m ∧
      DisjL (mainIn fs fp W ++ L) ∧ m ≤ W.sizes.sum + (fs "exponent_tables" + 68 + bs.sum) ∧
      ∀ rd, LowDef κ rd → MemL rd (mainIn fs fp W ++ L) →
        rd 1 = some (digestScalars W.stDig).1 → rd g = some (digestScalars W.stDig).2 →
        RelAtInWS S fs cert w rd (fun i => i < 2) (fun _ => False) fp (fs "main" + m)
          "main" [] [] fun θ => w θ "main" + ((Wt θ).Bexp + (bws.map (· θ)).sum) := by
  set b0 := fp + fs "main" with hb0
  set bK := b0 + W.sizes.sum with hbK
  set n0 := fs "exponent_tables" + [34, 34].sum + 0 with hn0
  obtain ⟨N, Lk, outs, ho, hWk, hDk, hNb, -, hK⟩ := kidsFromInWS_of_kidsW (fs := fs) (cert := cert) (w := w) κ
    ks bs bws hks (bK + n0)
  have hf := forall₂_of_map_length _ _ hW.lens
  have hWx : Within (mainLexp fs fp W) bK n0 := by
    intro q hq
    simp only [mainLexp, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> simp only [mainExpBase, expTbl1, expTbl2, List.length_map,
      List.length_range, hn0, List.sum_cons, List.sum_nil] <;> omega
  have hWin : Within (mainIn fs fp W) b0 (W.sizes.sum + n0) := by
    rw [mainIn, within_append]
    exact ⟨(bufL_within _ _ _ hf).mono le_rfl (by omega), hWx.mono (by omega) (by omega)⟩
  have hDx : DisjL (mainLexp fs fp W) := by
    simp only [mainLexp, DisjL, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, List.Pairwise.nil, and_true, IsEmpty.forall_iff, implies_true]
    left; simp [expTbl1]
  have hDin : DisjL (mainIn fs fp W) :=
    disj_append (bufL_disj _ _ _ hf) hDx (bufL_within _ _ _ hf) hWx (by omega)
  refine ⟨W.sizes.sum + (n0 + N), Lk, ?_, disj_append hDin hDk hWin hWk (by omega), ?_,
    fun rd hl hL hp0 hp1 => ?_⟩
  · rw [within_append]
    exact ⟨hWin.mono le_rfl (by omega), hWk.mono (by omega) (by omega)⟩
  · simp only [hn0, List.sum_cons, List.sum_nil]
    omega
  obtain ⟨hLin, hLk⟩ := memL_append.mp hL
  set R := mainRunAt fs fp W with hR
  set σ := mainVal rd R with hσ
  have hok := mainOkS_of_words hκ hW hl hLin hp0 hp1
  have hH := mainS_body_holds hok
  have hwf : Stmt.wfList coreProgram mainBody = true := by
    have := coreProgram_wf Data.core0 (List.mem_of_find?_eq_some find_main)
    rwa [core0_body] at this
  have hw := walk_mainBody σ
  have hsat := walkB_sat mainBody hwf hH
  rw [hw] at hsat
  have hb1 : decide (σ (.n 112) = 0) = decide (W.rd = 1) := branch1 hW.rd1
  have hb2 : decide (σ (.n 155) = 0) = decide (W.nc = 0) := branch2 hW.nc
  obtain ⟨q1, q2, q3, q4⟩ := mainLin_parts (decide (W.rd = 1)) (decide (W.nc = 0))
  obtain ⟨e1, e2, e3, e4⟩ := straight_parts σ _ (mainLin_straight (decide (W.rd = 1)) (decide (W.nc = 0)))
  rw [q1] at e1 e2
  rw [q2] at e3
  rw [q3] at e4
  have hal : allocs σ (mainEvs σ) = W.sizes := by
    rw [allocs_mainEvs, hb1, hb2, e2]; exact mainS_allocs hW
  have hdst : (allocDsts (mainEvs σ)).map σ =
      (bases b0 (allocs σ (mainEvs σ))).map fun b => ofK (gpow b) := by
    rw [allocDsts_mainEvs, hb1, hb2, e1, hal]
    simp only [mainAllocs, List.map_cons, List.map_nil, hσ, mainVal, hR, mainRunAt]
    b1_look
    rfl
  have hcalls : calls (mainEvs σ) =
      ⟨"exponent_tables", [], [.n 65, .n 66], true⟩ :: (mainFronts (decide (W.rd = 1))
        (decide (W.nc = 0))).map (mkCall σ) := by
    rw [calls_mainEvs, hb1, hb2, e4]; rfl
  have hexp : MemL rd (mainLexp fs fp W) := (memL_append.mp hLin).2
  have hown : ∀ i, RegionL (mainLb fs fp W) i →
      ownData cert fp b0 "main" W.sizes (mainEvs σ) i := fun i hi =>
    Or.inl (bufL_region _ _ _ (forall₂_of_map_length _ _ hW.lens) i hi)
  have hexpRel := exponentS_tables_relAtIn (S := S) (fs := fs) (cert := cert) bK rd hexp
  have hk : KidsFromInWS S fs cert w rd σ
      (fun i => i < 2 ∨ ownData cert fp b0 "main" (allocs σ (mainEvs σ)) (mainEvs σ) i)
      (fun _ => False) (calls (mainEvs σ)) ((fun θ => (Wt θ).Bexp) :: bws)
      (b0 + (allocs σ (mainEvs σ)).sum) (n0 + N)
      (fun i => (False ∨ (true = true ∧ RegionL (mainLexp fs fp W) i)) ∨ outRegion ks outs i) := by
    rw [hcalls, hal]
    refine ⟨n0, N, RegionL [], RegionL (mainLexp fs fp W), rfl,
      fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq, ?_, ?_⟩
    · simp only [↓reduceIte, List.map_nil, List.map_cons]
      have e65 : σ (.n 65) = ofK (gpow (bK + fs "exponent_tables")) := by
        simp only [hσ, mainVal, hR, mainRunAt]; b1_look; rfl
      have e66 : σ (.n 66) = ofK (gpow (bK + fs "exponent_tables" + 34)) := by
        simp only [hσ, mainVal, hR, mainRunAt]; b1_look; rfl
      rw [e65, e66]
      exact relAtInWS_of_weightLe (Bf := fun θ _ => (Wt θ).Bexp) hexpRel fun θ => (Wt θ).exp
    · refine hK rd σ _ _ _ (hcm rd outs ho) hl hLk
        (memL_lins fun k hk' => (hsub k hk').1 rd hLin) (regionsOk_of fun k hk' _ i hi => ?_)
      rcases regionL_append_or ((hsub k hk').2 i hi) with h | h
      · exact Or.inl (Or.inr (hown i h))
      · exact Or.inr (Or.inr ⟨rfl, h⟩)
  have := relAtInWS_of_walk (fs := fs) (cert := cert) (w := w) (R := fun i => i < 2)
    (D := fun _ => False) (fp := fp) (σ := σ) (rd := rd) (args := []) (rets := [])
    find_main (Or.inl main_not_loop) rfl (by rw [core0_body]; exact hw) rfl
    (fun e he => (hsat.1 e he).1) hdst (by rw [addrs_mainEvs, hb1, hb2, e3]; simp) hk ?_
    (fun i hi => hi.elim)
  · rw [hal, Nat.add_assoc] at this
    exact this.wmono fun θ => by simp only [List.map_cons, List.sum_cons]; omega
  · have hreg : ∀ j < 10, ∀ k < W.sizes.getD j 0,
        ownData cert fp b0 "main" (allocs σ (mainEvs σ)) (mainEvs σ) (mainBase fs fp W j + k) := by
      intro j hj k hk
      rw [hal]
      refine hown _ (regionL_of_mem (mainLb_mem j hj) ?_)
      rw [getD_map_length, hW.lens]
      exact hk
    have hbuf : ∀ j < 10, ∀ k < W.sizes.getD j 0, ∃ i,
        (mainPtr fs fp W j).limb 0 * Parameters.gpow k = Parameters.gpow i ∧
        (ownData cert fp b0 "main" (allocs σ (mainEvs σ)) (mainEvs σ) i ∨ i < 2 ∨
          ((False ∨ (true = true ∧ RegionL (mainLexp fs fp W) i)) ∨ outRegion ks outs i)) :=
      fun j hj k hk => ⟨mainBase fs fp W j + k, addr_ofK _ _, Or.inl (hreg j hj k hk)⟩
    intro A hA
    rw [loadAddrs_mainEvs, hb1, hb2, LeanVM.Guest.B1.loadAddrs_straight σ _ (mainLin_straight _ _), q4,
      List.mem_map] at hA
    obtain ⟨q, hq, rfl⟩ := hA
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    have p3 : σ (.n 102) = mainPtr fs fp W 3 := by simp only [hσ, mainVal, hR, mainRunAt]; b1_look
    have p8 : σ (.n 145) = mainPtr fs fp W 8 := by simp only [hσ, mainVal, hR, mainRunAt]; b1_look
    have p9 : σ (.n 153) = mainPtr fs fp W 9 := by simp only [hσ, mainVal, hR, mainRunAt]; b1_look
    have p151 : σ (.n 151) = mainPtr fs fp W 8 * gen ^ W.nc := by
      simp only [hσ, mainVal, hR, mainRunAt]; b1_look
    have p211 : σ (.n 211) = 1 := by simp only [hσ, mainVal]; b1_look
    have p215 : σ (.n 215) = 1 * gen := by simp only [hσ, mainVal]; b1_look
    have s3 : W.sizes.getD 3 0 = 2 := rfl
    have s8 : W.sizes.getD 8 0 = W.nc + 1 := rfl
    have s9 : W.sizes.getD 9 0 = 53 := rfl
    rcases hq with (((rfl | rfl | rfl | rfl) | hq) | rfl | rfl)
    · rw [p3]; exact hbuf 3 (by omega) 0 (by rw [s3]; omega)
    · rw [p3]; exact hbuf 3 (by omega) 1 (by rw [s3]; omega)
    · rw [p8]; exact hbuf 8 (by omega) 0 (by rw [s8]; omega)
    · rw [p151]
      refine ⟨mainBase fs fp W 8 + W.nc, ?_, Or.inl (hreg 8 (by omega) W.nc (by rw [s8]; omega))⟩
      rw [mainPtr, ofK_gpow_mul_gen, addr_ofK, Nat.add_zero]
    · cases hb : decide (W.nc = 0) <;> simp only [hb, Bool.false_eq_true, ↓reduceIte,
        List.not_mem_nil] at hq
      simp only [leafLoads, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
        List.not_mem_nil, or_false] at hq
      rcases hq with ((⟨k, hk, rfl⟩ | rfl) | ⟨k, hk, rfl⟩) | rfl | rfl <;> rw [p9]
      · exact hbuf 9 (by omega) k (by rw [s9]; omega)
      · exact hbuf 9 (by omega) 22 (by rw [s9]; omega)
      · exact hbuf 9 (by omega) (23 + k) (by rw [s9]; omega)
      · exact hbuf 9 (by omega) 51 (by rw [s9]; omega)
      · exact hbuf 9 (by omega) 52 (by rw [s9]; omega)
    · rw [p211]
      exact ⟨0, by rw [← ofK_one, limb_ofK]; simp [Parameters.gpow], Or.inr (Or.inl (by omega))⟩
    · rw [p215]
      exact ⟨1, by rw [one_mul, gen_eq_ofK, limb_ofK]; simp [Parameters.gpow], Or.inr (Or.inl (by omega))⟩

/-! ## `main`'s callees after `exponent_tables` -/

section Match

variable (rd : Reader)

set_option maxRecDepth 100000 in
theorem mainS_cm8 (hW : MainWordsOkC S fs Ha κ VsGood fp W) (o : List (List E × Layout))
    (ho : OutsOk (mainKids8 fs fp W) o) :
    CallsMatch (mainVal rd (mainRunAt fs fp W)) (mainFronts8.map (mkCall (mainVal rd (mainRunAt fs fp W))))
      (mainKids8 fs fp W) o := by
  have ht := hW.total
  have hd := hW.dau
  have hrx := hW.rx
  have hrs := hW.rs
  unfold MainWords.total at ht
  match o, ho with
  | [o1, o2, o3, o4, o5, o6, o7, o8], ho =>
    simp only [OutsOk, mainKids8, Returns, forall_const] at ho
    obtain ⟨h1, ⟨e2, -⟩, ⟨e3, -⟩, ⟨e4, -⟩, h5, h6, h7, h8, -⟩ := ho
    simp only [mainFronts8, List.map_cons, List.map_nil, mkCall, CallsMatch, mainKids8, mainVal,
      mainRunAt, mainSq]
    b1_look
    simp only [true_and, and_true, forall_const]
    refine ⟨by rw [← pow_add]; exact one_add_gen_pow_dec (by omega), fun h => (h1 h).1.symm, e2.symm, e3.symm, e4.symm,
      one_add_gen_pow_dec (by omega), fun h => (h5 h).1.symm, one_add_gen_pow_dec (by omega),
      fun h => (h6 h).1.symm, one_add_gen_pow_dec (by omega), fun h => (h7 h).1.symm,
      one_add_gen_pow_dec (by omega), fun h => (h8 h).1.symm⟩

set_option maxRecDepth 100000 in
theorem mainS_cm5 (hW : MainWordsOkC S fs Ha κ VsGood fp W) (o : List (List E × Layout))
    (ho : OutsOk [mainKid5 fs fp W] o) :
    CallsMatch (mainVal rd (mainRunAt fs fp W)) ([mainFront5].map (mkCall (mainVal rd (mainRunAt fs fp W))))
      [mainKid5 fs fp W] o := by
  match o, ho with
  | [o1], ho =>
    simp only [OutsOk, mainKid5, Returns] at ho
    simp only [mainFront5, List.map_cons, List.map_nil, mkCall, CallsMatch, mainKid5, mainVal,
      mainRunAt, mainSq]
    b1_look
    simp only [true_and, and_true]
    refine ⟨one_add_gen_pow_dec (by have := hW.nc; omega), fun h => (ho.1 h).1.symm⟩

end Match

theorem mainS_hcm (hW : MainWordsOkC S fs Ha κ VsGood fp W) (ksAgg : List Kid)
    (hAgg : ∀ rd o, OutsOk ksAgg o → CallsMatch (mainVal rd (mainRunAt fs fp W))
      ((if decide (W.nc = 0) then [] else [mainFrontAgg]).map (mkCall (mainVal rd (mainRunAt fs fp W))))
      ksAgg o) :
    ∀ rd outs, OutsOk (mainKids8 fs fp W ++ (if W.rd = 1 then mainKidsDa fs fp W else []) ++
        [mainKid5 fs fp W] ++ ksAgg ++ [mainKidSd fs fp W]) outs →
      CallsMatch (mainVal rd (mainRunAt fs fp W))
        ((mainFronts (decide (W.rd = 1)) (decide (W.nc = 0))).map
          (mkCall (mainVal rd (mainRunAt fs fp W))))
        (mainKids8 fs fp W ++ (if W.rd = 1 then mainKidsDa fs fp W else []) ++
          [mainKid5 fs fp W] ++ ksAgg ++ [mainKidSd fs fp W]) outs := by
  intro rd outs ho
  obtain ⟨a4, s, rfl, ha4, hs⟩ := outsOk_append _ _ _ ho
  obtain ⟨a3, sa, rfl, ha3, hsa⟩ := outsOk_append _ _ _ ha4
  obtain ⟨a2, s5, rfl, ha2, hs5⟩ := outsOk_append _ _ _ ha3
  obtain ⟨a1, sd, rfl, ha1, hsd⟩ := outsOk_append _ _ _ ha2
  simp only [mainFronts, List.map_append]
  refine callsMatch_append _ _ _ _ _ _ (callsMatch_append _ _ _ _ _ _ (callsMatch_append _ _ _ _ _ _
    (callsMatch_append _ _ _ _ _ _ (mainS_cm8 rd hW _ ha1) ?_) (mainS_cm5 rd hW _ hs5)) (hAgg rd _ hsa))
    (main_cmSd rd _ hs)
  by_cases hr : W.rd = 1
  · simp only [hr, decide_true, ↓reduceIte] at hsd ⊢
    exact main_cmDa rd _ hsd
  · simp only [hr, decide_false, Bool.false_eq_true, ↓reduceIte] at hsd ⊢
    exact callsMatch_nil _ hsd

/-! ## The callees' completeness -/

theorem mainS_kb8 (H : CalleesAtC Ha S fs cert κ VsGood Bd) (hκ : 16 ≤ κ) (hW : MainWordsOkC S fs Ha κ VsGood fp W) :
    KidsBS S fs cert κ (mainKids8 fs fp W) (mainBs8 fs Bd W) := by
  have ht := hW.total
  unfold MainWords.total at ht
  simp only [KidsBS, mainKids8, mainBs8, List.forall₂_cons, List.Forall₂.nil, and_true,
    Bool.true_eq_false, IsEmpty.forall_iff, decide_eq_true_eq, decide_eq_false_iff_not]
  refine ⟨⟨fun htk => ?_, fun _ => by omega⟩, fun _ => ?_, fun _ => ?_, fun _ => ?_,
    ⟨fun htk => ?_, fun _ => by omega⟩, ⟨fun htk => ?_, fun _ => by omega⟩,
    ⟨fun htk => ?_, fun _ => by omega⟩, ⟨fun htk => ?_, fun _ => by omega⟩⟩
  · exact quietLoopS_completeAt loop0_quiet κ _ (fun rd => loop0S_complete (m := W.da + W.ud) (by omega)
      (pow_add _ _ _).symm) fun rd t hn hv hbo => loop0S_total (by omega) hn (by rwa [← pow_add] at hv) hbo
  · obtain ⟨cl, hcl, h⟩ := hW.daList
    have := H.da_list_digest cl _ _ _ h
    rwa [hcl] at this
  · obtain ⟨cs, hcs, h⟩ := hW.xList
    have := H.claim_list_digest cs _ _ _ h
    rwa [hcs, Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)] at this
  · obtain ⟨cs, hcs, h⟩ := hW.sList
    have := H.claim_list_digest cs _ _ _ h
    rwa [hcs, Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)] at this
  · exact quietLoopS_completeAt loop1_quiet κ _ (fun rd => loop1S_complete (by omega) rfl)
      fun rd t hn hv hbo => loop1S_total (by omega) hn hv hbo
  · exact quietLoopS_completeAt loop2_quiet κ _ (fun rd => loop2S_complete (by omega) rfl)
      fun rd t hn hv hbo => loop2S_total (by omega) hn hv hbo
  · have := loop3S_completeAt (S := S) (fs := fs) (cert := cert) H.verify_lean_xmss hκ (M := W.dx + W.ux)
      (m := W.rx) (cb := mainBase fs fp W 4) (tb := mainBase fs fp W 1) (by omega)
      (by have := hW.rx; omega) (by omega) W.slX hW.xSlot (mainIn fs fp W) hW.xMark hW.xSig
    rw [pow_add] at this
    exact this
  · have := loop4S_completeAt (S := S) (fs := fs) (cert := cert) H.verify_sig_lean_sphincs hκ
      (M := W.ds + W.us) (Lx := W.dx + W.ux) (m := W.rs) (cb := mainBase fs fp W 4)
      (tb := mainBase fs fp W 2) (w := gen ^ W.rx) (by omega) (by have := hW.rs; omega) (by omega)
      W.slS hW.sSlot (mainIn fs fp W) hW.sMark hW.sSig
    rw [pow_add, pow_add] at this
    exact this

variable (S) in
/-- The weights of the calls of the raw signatures and the claim lists. -/
def mainBws8S {Θ : Type} {w : Θ → String → ℕ} (Bd : CalleeBounds) (Wt : ∀ θ, MainWeightHypsS S fs (w θ))
    (W : MainWords) : List (Θ → ℕ) :=
  [fun θ => (W.da + W.ud) * (Wt θ).Kl0, fun θ => (Wt θ).Bdl, fun θ => (Wt θ).αcl * Bd.cl W.dx / 1000,
    fun θ => (Wt θ).αcl * Bd.cl W.ds / 1000, fun θ => W.ux * (Wt θ).Kl1, fun θ => W.us * (Wt θ).Kl2,
    fun θ => W.rx * (Wt θ).Kl3, fun θ => W.rs * (Wt θ).Kl4]

theorem mainS_kw8 {Θ : Type} {w : Θ → String → ℕ} (Wt : ∀ θ, MainWeightHypsS S fs (w θ))
    (H : CalleesAtC Ha S fs cert κ VsGood Bd) (hκ : 16 ≤ κ) (hW : MainWordsOkC S fs Ha κ VsGood fp W) :
    KidsWS S fs cert w κ (mainKids8 fs fp W) (mainBs8 fs Bd W) (mainBws8S S Bd Wt W) := by
  have ht := hW.total
  have hrx := hW.rx
  have hrs := hW.rs
  unfold MainWords.total at ht
  have hb := mainS_kb8 H hκ hW
  obtain ⟨⟨b0, b0'⟩, hb⟩ := List.forall₂_cons.mp hb
  obtain ⟨⟨b1, -⟩, hb⟩ := List.forall₂_cons.mp hb
  obtain ⟨⟨b2, -⟩, hb⟩ := List.forall₂_cons.mp hb
  obtain ⟨⟨b3, -⟩, hb⟩ := List.forall₂_cons.mp hb
  obtain ⟨⟨b4, b4'⟩, hb⟩ := List.forall₂_cons.mp hb
  obtain ⟨⟨b5, b5'⟩, hb⟩ := List.forall₂_cons.mp hb
  obtain ⟨⟨b6, b6'⟩, hb⟩ := List.forall₂_cons.mp hb
  obtain ⟨⟨b7, b7'⟩, -⟩ := List.forall₂_cons.mp hb
  refine ⟨fun h => CompleteAtB.toWS (b0 h) fun θ rd t rets hn hv hbo => ?_, b0',
    fun h => CompleteAtB.toWS_weightLe (Bf := fun θ _ => (Wt θ).Bdl) (b1 h) fun θ => (Wt θ).dl,
    fun h => by simp at h,
    fun h => CompleteAtB.toWS_tot (b2 h) fun θ => (Wt θ).cl, fun h => by simp at h,
    fun h => CompleteAtB.toWS_tot (b3 h) fun θ => (Wt θ).cl, fun h => by simp at h,
    fun h => CompleteAtB.toWS (b4 h) fun θ rd t rets hn hv hbo => ?_, b4',
    fun h => CompleteAtB.toWS (b5 h) fun θ rd t rets hn hv hbo => ?_, b5',
    fun h => CompleteAtB.toWS (b6 h) fun θ rd t rets hn hv hbo => ?_, b6',
    fun h => CompleteAtB.toWS (b7 h) fun θ rd t rets hn hv hbo => ?_, b7', trivial⟩
  · simp only [decide_eq_true_eq] at h
    exact (Wt θ).l0.from_one (by omega) (by omega) (by simp) (by simp [pow_add])
      rd t rets hn hv hbo
  · simp only [decide_eq_true_eq] at h
    exact (Wt θ).l1.from_one (by omega) (by omega) (by simp) (by simp)
      rd t rets hn hv hbo
  · simp only [decide_eq_true_eq] at h
    exact (Wt θ).l2.from_one (by omega) (by omega) (by simp) (by simp)
      rd t rets hn hv hbo
  · simp only [decide_eq_true_eq] at h
    exact (Wt θ).l3.from_one (by omega) (by omega) (by simp) (by simp)
      rd t rets hn hv hbo
  · simp only [decide_eq_true_eq] at h
    exact (Wt θ).l4.from_one (by omega) (by omega) (by simp) (by simp)
      rd t rets hn hv hbo

variable (S) in
/-- **`main`'s weight** at `ω`: its own, the exponent tables', and its callees' after them. -/
noncomputable def mainWeightS (ω : String → ℕ) (Bd : CalleeBounds) (H : MainWeightHypsS S fs ω) (W : MainWords) : ℕ :=
  ω "main" + (H.Bexp + ((W.da + W.ud) * H.Kl0 + H.Bdl + H.αcl * Bd.cl W.dx / 1000 +
    H.αcl * Bd.cl W.ds / 1000 + W.ux * H.Kl1 + W.us * H.Kl2 + W.rx * H.Kl3 + W.rs * H.Kl4 +
    (if W.rd = 1 then Bd.daVerifyW ω W.drows + H.Bcov else 0) +
    loopSum (ω "__loop5") (fun c => childWS S ω Bd H (W.child c)) 0 W.nc +
    (if W.nc = 0 then 0 else H.cAgg + H.dAgg * W.nc) + H.Bsd))

set_option maxHeartbeats 1000000 in
/-- **`main`, placed** (G:3119-3316; TRIAGE #76): at `fp`, for `main`'s words within what its
callees need, one size, within its buffers, the exponent tables and `mainKidsBound`, and one
layout serve every memory holding `main`'s words, the callees' and the public input at words `0`,
`1`: `main` holds by a tree placed at `fp`, loading from its own data or its header, within
`mainWeightS` at every `w θ`. -/
theorem mainS_relAtInW {Θ : Type} {w : Θ → String → ℕ} (Wt : ∀ θ, MainWeightHypsS S fs (w θ))
    (H : CalleesAtC Ha S fs cert κ VsGood Bd) (hF : FsRowsC S Ha) (hBs : BsRowsC S Ha) (hκ : 16 ≤ κ)
    (hW : MainWordsOkC S fs Ha κ VsGood fp W) :
    ∃ (m : ℕ) (L : Layout), Within (mainIn fs fp W ++ L) (fp + fs "main") m ∧
      DisjL (mainIn fs fp W ++ L) ∧
      m ≤ W.sizes.sum + (fs "exponent_tables" + 68 + mainKidsBound fs Bd W) ∧
      ∀ rd, LowDef κ rd → MemL rd (mainIn fs fp W ++ L) →
        rd 1 = some (digestScalars W.stDig).1 → rd g = some (digestScalars W.stDig).2 →
        RelAtInWS S fs cert w rd (fun i => i < 2) (fun _ => False) fp (fs "main" + m)
          "main" [] [] fun θ => mainWeightS S (w θ) Bd (Wt θ) W := by
  set bsDa : List ℕ := if W.rd = 1 then [Bd.daVerify W.drows, Bd.cover] else [] with hbsDa
  set bwsDa : List (Θ → ℕ) := if W.rd = 1 then [fun θ => Bd.daVerifyW (w θ) W.drows,
    fun θ => (Wt θ).Bcov] else [] with hbwsDa
  set b5 := loopSum (fs "__loop5") (fun c => childBd fs Bd (W.child c)) 0 W.nc with hb5
  set bw5 : Θ → ℕ := fun θ => loopSum (w θ "__loop5") (fun c => childWS S (w θ) Bd (Wt θ) (W.child c)) 0 W.nc
    with hbw5
  have hDa : KidsWS S fs cert w κ (if W.rd = 1 then mainKidsDa fs fp W else []) bsDa bwsDa := by
    by_cases hr : W.rd = 1
    · simp only [hbsDa, hbwsDa, hr, ↓reduceIte]
      refine ⟨fun _ => ?_, fun h => by simp at h, fun _ => ?_,
        fun h => by simp at h, trivial⟩
      · obtain ⟨wt, root, vd, ho, hrows, h⟩ := hW.daVerify hr
        rw [← hrows]
        exact (H.da_verify wt root vd ho _ _ _ h).reindex w
      · obtain ⟨i, h⟩ := hW.daCover hr
        exact CompleteAtB.toWS_weightLe (Bf := fun θ _ => (Wt θ).Bcov) (H.cover_da_root i _ _ _ h)
          fun θ => (Wt θ).cov
    · simp only [hbsDa, hbwsDa, hr, ↓reduceIte]; trivial
  have h5 : KidsWS S fs cert w κ [mainKid5 fs fp W] [b5] [bw5] := by
    refine ⟨fun htk => ?_, fun htk => ?_, trivial⟩
    · simp only [mainKid5, decide_eq_true_eq] at htk
      exact loop5C_completeAtW H Wt hκ hW.nc (by omega) (mainIn fs fp W) W.child hW.children
    · simp only [mainKid5, decide_eq_false_iff_not, not_not] at htk
      simp only [mainKid5, hb5, htk, loopSum, le_refl]
  have hpre : KidsWS S fs cert w κ (mainKids8 fs fp W ++ (if W.rd = 1 then mainKidsDa fs fp W else []) ++
      [mainKid5 fs fp W]) (mainBs8 fs Bd W ++ bsDa ++ [b5]) (mainBws8S S Bd Wt W ++ bwsDa ++ [bw5]) :=
    ((mainS_kw8 Wt H hκ hW).append hDa).append h5
  have hsd : KidsWS S fs cert w κ [mainKidSd fs fp W] [Bd.sd] [fun θ => (Wt θ).Bsd] := by
    refine ⟨fun _ => ?_, fun h => by simp [mainKidSd] at h, trivial⟩
    obtain ⟨sig, cells, h⟩ := hW.stmt
    exact CompleteAtB.toWS_weightLe (Bf := fun θ _ => (Wt θ).Bsd) (H.statement_digest sig cells _ _ _ h)
      fun θ => (Wt θ).sd
  have hsum : (mainBs8 fs Bd W ++ bsDa ++ [b5]).sum + Bd.sd + (if W.nc = 0 then 0 else aggBound fs W.nc) =
      mainKidsBound fs Bd W := by
    simp only [mainKidsBound, List.sum_append, List.sum_cons, List.sum_nil, hbsDa, sum_ite_pair, hb5]
    omega
  have hwsum : ∀ θ, ((mainBws8S S Bd Wt W ++ bwsDa ++ [bw5]).map (· θ)).sum + (Wt θ).Bsd +
      (if W.nc = 0 then 0 else (Wt θ).cAgg + (Wt θ).dAgg * W.nc) + (Wt θ).Bexp + w θ "main" =
      mainWeightS S (w θ) Bd (Wt θ) W := by
    intro θ
    by_cases hr : W.rd = 1 <;>
      simp only [mainWeightS, mainBws8S, hbwsDa, hbw5, hr, ↓reduceIte, List.map_append, List.map_cons,
        List.map_nil, List.sum_append, List.sum_cons, List.sum_nil] <;> omega
  have hsubPre : ∀ k ∈ mainKids8 fs fp W ++ (if W.rd = 1 then mainKidsDa fs fp W else []) ++
      [mainKid5 fs fp W], SubL k.Lin (mainIn fs fp W) := by
    intro k hk
    refine SubL.of_mem fun q hq => ?_
    simp only [List.mem_append, List.mem_singleton] at hk
    rcases hk with (hk | hk) | rfl
    · simp only [mainKids8, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hq
    · by_cases hr : W.rd = 1
      · simp only [hr, ↓reduceIte, mainKidsDa, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> exact hq
      · simp [hr] at hk
    · exact hq
  by_cases hnc : W.nc = 0
  · refine (fun hc => ?_) (mainS_relAtIn_coreW (cert := cert) Wt hκ hW _ _ _ ((hpre.append
      (show KidsWS S fs cert w κ [] [] [] from trivial)).append hsd) (fun k hk => ?_)
      (mainS_hcm hW [] fun rd o ho => by simp only [hnc, decide_true, ↓reduceIte]; exact callsMatch_nil o ho))
    · obtain ⟨m, L, h1, h2, h3, h4⟩ := hc
      refine ⟨m, L, h1, h2, ?_, fun rd hl hL hp0 hp1 => (h4 rd hl hL hp0 hp1).wmono fun θ => ?_⟩
      · rw [← hsum]
        simp only [List.sum_append, List.sum_cons, List.sum_nil, hnc, ↓reduceIte] at h3 ⊢
        omega
      · have := hwsum θ
        simp only [List.append_nil, List.map_append, List.map_cons, List.map_nil, List.sum_append,
          List.sum_cons, List.sum_nil, hnc, ↓reduceIte] at this ⊢
        omega
    · simp only [List.append_nil, List.mem_append, List.mem_singleton] at hk
      rcases hk with hk | rfl
      · exact hsubPre k (by simp only [List.mem_append, List.mem_singleton]; exact hk)
      · exact SubL.of_mem fun q hq => hq
  · obtain ⟨cs, h, d, hlen, hb, hbr, hmr, hsh, hcpi, hfr, hcar, hdT⟩ := hW.agg hnc
    have hagg : KidsWS S fs cert w κ [mainKidAgg fs fp W cs d] [aggBound fs W.nc]
        [fun θ => (Wt θ).cAgg + (Wt θ).dAgg * W.nc] := by
      refine ⟨fun _ => ?_, fun h => by simp [mainKidAgg] at h, trivial⟩
      have := aggregateC_claims_completeAt (fs := fs) (cert := cert) hF hBs κ
        (by intro h0; rw [h0] at hlen; exact hnc hlen.symm) (by rw [hlen]; exact hW.nc) hb hbr hmr hsh
        (mainBase fs fp W 5) (mainBase fs fp W 6) (mainBase fs fp W 7) (mainBase fs fp W 9)
      rw [hlen] at this
      exact CompleteAtB.toWS this fun θ rd t rets hn hv hbo => (Wt θ).agg rd t _ rets W.nc hn hv hbo
        (by simp [mainKidAgg, gen_pow_eq_ofK]) (by omega) (by have := hW.nc; omega)
    refine (fun hc => ?_) (mainS_relAtIn_coreW (cert := cert) Wt hκ hW _ _ _ ((hpre.append hagg).append hsd)
      (fun k hk => ?_)
      (mainS_hcm hW [mainKidAgg fs fp W cs d] fun rd o ho => by
        simp only [hnc, decide_false, Bool.false_eq_true, ↓reduceIte]; exact main_cmAgg rd cs d o ho))
    · obtain ⟨m, L, h1, h2, h3, h4⟩ := hc
      refine ⟨m, L, h1, h2, ?_, fun rd hl hL hp0 hp1 => (h4 rd hl hL hp0 hp1).wmono fun θ => ?_⟩
      · rw [← hsum]
        simp only [List.sum_append, List.sum_cons, List.sum_nil, hnc, ↓reduceIte] at h3 ⊢
        omega
      · have := hwsum θ
        simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
          List.sum_cons, List.sum_nil, hnc, ↓reduceIte] at this ⊢
        omega
    · simp only [List.mem_append, List.mem_singleton] at hk
      rcases hk with (hk | rfl) | rfl
      · exact hsubPre k (by simp only [List.mem_append, List.mem_singleton]; exact hk)
      · refine SubL.of_mem fun q hq => ?_
        simp only [mainKidAgg, aggExtL, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl
        · rw [← hcpi]; exact mainIn_mem 5 (by omega)
        · rw [← hfr]; exact mainIn_mem 6 (by omega)
        · rw [← hcar]; exact mainIn_mem 7 (by omega)
        · rw [← hdT]; exact mainIn_mem 9 (by omega)
      · exact SubL.of_mem fun q hq => hq

end
end LeanVM.Guest.B1.Main
