/-
  LeanVM.Guest.B1.Main.HonestMainC

  `main`'s own callees' preconditions on its honest words over a hash (`HonestMain.lean` over the
  total hash `Ht`, the digests answered by `Ha`): the claim lists, the DA list, the raw
  signatures, the direct DA claim, the signer set, the statement's digest, the running counts.
-/

module

public import LeanVM.Guest.B1.Main.HonestWordsC
public import LeanVM.Guest.B1.Main.HonestMain

/-!
# `main`'s callees, honestly, over a hash

`HonestMain.lean`'s lemmas at `honestWordsC Ht` (`honC_…`): each digest a callee returns is the
one over `Ht`, answered by `Ha` (the hypotheses `Ha … = some …`), so each precondition is the
`…C` one over `Ha`; the signatures verify and the blob matrix opens with `Ha`'s answers
(`XmssHeldWith`, `SphincsHeldWith`, `DaHeldWith`); the signer set's row is `FsRowsC`'s one block.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.Hints (direct)
open LeanVM.Guest.End (Limits coverage)
open LeanVM.Guest.B1 (LowDef DaClaimsAt Meaning_verify_lean_xmssWith Meaning_verify_sig_lean_sphincsWith)
open LeanVM.Guest.B1.Digest (SquaresAt CellsAt)

@[expose] public section

variable (fs : String → ℕ) (Ht : List UInt8 → Digest) {Ha : List UInt8 → Option Digest} {fp : ℕ} {seed : Digest} {s : NodeStatement} {w : NodeWitness}
  {rd : Reader}

/-! ## Reading the tables -/




/-! ## The declared lists -/

theorem honC_daList (hlim : Limits s w)
    (hda : daListDigestWith Ha s.claims.da = some (daListDigestH Ht s.claims.da))
    (hL : MemL rd (mainIn fs fp (honestWordsC Ht seed s w))) :
    DaListPreAtC Ha s.claims.da rd [mainPtr fs fp (honestWordsC Ht seed s w) 0, gen ^ s.claims.da.length]
      [(digestScalars (daListDigestH Ht s.claims.da)).1, (digestScalars (daListDigestH Ht s.claims.da)).2] := by
  have h := mainIn_reads hL 0 (by omega)
  simp only [MainWords.bufs, honestWordsC, List.getD_cons_zero, List.flatMap_append] at h
  exact ⟨hlim.daRoots.1, rfl, daClaimsAt_of_reads (readsAt_append'.mp h).1, _, hda, rfl⟩

theorem honC_xList (hlim : Limits s w)
    (hx : xmssListDigestWith Ha s.claims.xmss = some (xmssListDigestH Ht s.claims.xmss))
    (hL : MemL rd (mainIn fs fp (honestWordsC Ht seed s w))) :
    ClPreAtC Ha (s.claims.xmss.flatMap xCellsOf) rd
      [mainPtr fs fp (honestWordsC Ht seed s w) 1, gen ^ s.claims.xmss.length,
        ofK (gpow (mainExpBase fs fp (honestWordsC Ht seed s w) + 34))]
      [(digestScalars (xmssListDigestH Ht s.claims.xmss)).1,
        (digestScalars (xmssListDigestH Ht s.claims.xmss)).2] := by
  have h := mainIn_reads hL 1 (by omega)
  simp only [MainWords.bufs, honestWordsC, List.getD_cons_succ, List.getD_cons_zero,
    List.flatMap_append] at h
  have ht : (honestWordsC Ht seed s w).total < 2 ^ 16 := by
    have h0 := honest_total (seed := seed) hlim
    simp only [MainWords.total, honestWords] at h0
    simp only [MainWords.total, honestWordsC]; omega
  refine ⟨squaresAt_of_mainIn fs hL, s.claims.xmss.length,
    by simp only [MainWords.total, honestWordsC] at ht; omega, rfl,
    length_flatMap_const _ 4 _ fun c _ => xCellsOf_length c, (readsAt_append'.mp h).1,
    xCellsOf_canonical _, _, ?_, rfl⟩
  rw [xCellsOf_bytes]; exact hx

theorem honC_sList (hlim : Limits s w)
    (hs : sphincsListDigestWith Ha s.claims.sphincs = some (sphincsListDigestH Ht s.claims.sphincs))
    (hL : MemL rd (mainIn fs fp (honestWordsC Ht seed s w))) :
    ClPreAtC Ha (s.claims.sphincs.flatMap sCellsOf) rd
      [mainPtr fs fp (honestWordsC Ht seed s w) 2, gen ^ s.claims.sphincs.length,
        ofK (gpow (mainExpBase fs fp (honestWordsC Ht seed s w) + 34))]
      [(digestScalars (sphincsListDigestH Ht s.claims.sphincs)).1,
        (digestScalars (sphincsListDigestH Ht s.claims.sphincs)).2] := by
  have h := mainIn_reads hL 2 (by omega)
  simp only [MainWords.bufs, honestWordsC, List.getD_cons_succ, List.getD_cons_zero,
    List.flatMap_append] at h
  have ht : (honestWordsC Ht seed s w).total < 2 ^ 16 := by
    have h0 := honest_total (seed := seed) hlim
    simp only [MainWords.total, honestWords] at h0
    simp only [MainWords.total, honestWordsC]; omega
  refine ⟨squaresAt_of_mainIn fs hL, s.claims.sphincs.length,
    by simp only [MainWords.total, honestWordsC] at ht; omega, rfl,
    length_flatMap_const _ 4 _ fun c _ => sCellsOf_length c, (readsAt_append'.mp h).1,
    sCellsOf_canonical _, _, ?_, rfl⟩
  rw [sCellsOf_bytes]; exact hs


/-! ## The coverage marks -/




theorem honC_cov_length : (honestWordsC Ht seed s w).cov.length = (honestWordsC Ht seed s w).total := by
  simp only [honestWordsC, List.length_append, covOf_length, MainWords.total]

/-- **A leanXMSS writer's mark**: writer `r`'s slot holds `g^(gX r)`. -/
theorem honC_markX {r : ℕ} (hr : r < (writersX s w).length) :
    (planX s w).1.getD r 0 < s.claims.xmss.length + (planX s w).2.length ∧
    CellL (mainIn fs fp (honestWordsC Ht seed s w))
      (mainBase fs fp (honestWordsC Ht seed s w) 4 + (planX s w).1.getD r 0) (gen ^ gX s w r) := by
  have hreg := region_slots s.claims.xmss (writersX s w)
  rw [show assign s.claims.xmss [] [] (writersX s w) = planX s w from rfl] at hreg
  obtain ⟨l1, hnd, hsl⟩ := hreg
  have hs := (hsl r hr).1
  refine ⟨hs, cellL_of_getD (mainIn_mem 4 (by omega)) _ ?_ ?_⟩
  · simp only [MainWords.bufs, List.getD_cons_succ, List.getD_cons_zero]
    rw [honC_cov_length]; simp only [MainWords.total, honestWordsC]; omega
  · simp only [MainWords.bufs, List.getD_cons_succ, List.getD_cons_zero, honestWordsC]
    rw [List.append_assoc, getD_app_left (by rw [covOf_length]; exact hs)]
    exact covOf_getD hnd (by omega) hs

/-- **A leanSPHINCS writer's mark.** -/
theorem honC_markS {r : ℕ} (hr : r < (writersS s w).length) :
    (planS s w).1.getD r 0 < s.claims.sphincs.length + (planS s w).2.length ∧
    CellL (mainIn fs fp (honestWordsC Ht seed s w))
      (mainBase fs fp (honestWordsC Ht seed s w) 4 + (s.claims.xmss.length + (planX s w).2.length +
        (planS s w).1.getD r 0)) (gen ^ gS s w r) := by
  have hreg := region_slots s.claims.sphincs (writersS s w)
  rw [show assign s.claims.sphincs [] [] (writersS s w) = planS s w from rfl] at hreg
  obtain ⟨l1, hnd, hsl⟩ := hreg
  have hs := (hsl r hr).1
  refine ⟨hs, cellL_of_getD (mainIn_mem 4 (by omega)) _ ?_ ?_⟩
  · simp only [MainWords.bufs, List.getD_cons_succ, List.getD_cons_zero]
    rw [honC_cov_length]; simp only [MainWords.total, honestWordsC]; omega
  · simp only [MainWords.bufs, List.getD_cons_succ, List.getD_cons_zero, honestWordsC]
    rw [List.append_assoc, getD_app_right (covOf_length _ _ _),
      getD_app_left (by rw [covOf_length]; exact hs)]
    exact covOf_getD hnd (by omega) hs

/-- **A DA writer's mark.** -/
theorem honC_markD {r : ℕ} (hr : r < (writersD s w).length) :
    (planD s w).1.getD r 0 < s.claims.da.length + (planD s w).2.length ∧
    CellL (mainIn fs fp (honestWordsC Ht seed s w))
      (mainBase fs fp (honestWordsC Ht seed s w) 4 + (s.claims.xmss.length + (planX s w).2.length +
        (s.claims.sphincs.length + (planS s w).2.length) + (planD s w).1.getD r 0)) (gen ^ gD s w r) := by
  have hreg := region_slots s.claims.da (writersD s w)
  rw [show assign s.claims.da [] [] (writersD s w) = planD s w from rfl] at hreg
  obtain ⟨l1, hnd, hsl⟩ := hreg
  have hs := (hsl r hr).1
  refine ⟨hs, cellL_of_getD (mainIn_mem 4 (by omega)) _ ?_ ?_⟩
  · simp only [MainWords.bufs, List.getD_cons_succ, List.getD_cons_zero]
    rw [honC_cov_length]; simp only [MainWords.total, honestWordsC]; omega
  · simp only [MainWords.bufs, List.getD_cons_succ, List.getD_cons_zero, honestWordsC]
    rw [getD_app_right (by rw [List.length_append, covOf_length, covOf_length])]
    exact covOf_getD hnd (by omega) hs

/-! ## The tables' entries at the writers' slots -/

theorem honC_xEntry (hL : MemL rd (mainIn fs fp (honestWordsC Ht seed s w))) {r : ℕ}
    (hr : r < (writersX s w).length) {cl : XmssClaim} (hc : (writersX s w)[r]? = some cl) :
    ReadsAt rd (mainPtr fs fp (honestWordsC Ht seed s w) 1 * gen ^ (4 * (planX s w).1.getD r 0))
      (xCellsOf cl) := by
  have hreg := region_slots s.claims.xmss (writersX s w)
  rw [show assign s.claims.xmss [] [] (writersX s w) = planX s w from rfl] at hreg
  obtain ⟨hs, he⟩ := hreg.2.2 r hr
  have h : ReadsAt rd (mainPtr fs fp (honestWordsC Ht seed s w) 1)
      ((s.claims.xmss ++ (planX s w).2).flatMap xCellsOf) := mainIn_reads hL 1 (by omega)
  have := readsAt_flatMap4 xCellsOf_length h ((planX s w).1.getD r 0) (by simp only [List.length_append]; exact hs)
  rw [hc, List.getElem?_eq_getElem (by simpa using hs), Option.some.injEq] at he
  rw [he] at this
  exact this

theorem honC_sEntry (hL : MemL rd (mainIn fs fp (honestWordsC Ht seed s w))) {r : ℕ}
    (hr : r < (writersS s w).length) {cl : SphincsClaim} (hc : (writersS s w)[r]? = some cl) :
    ReadsAt rd (mainPtr fs fp (honestWordsC Ht seed s w) 2 * gen ^ (4 * (planS s w).1.getD r 0))
      (sCellsOf cl) := by
  have hreg := region_slots s.claims.sphincs (writersS s w)
  rw [show assign s.claims.sphincs [] [] (writersS s w) = planS s w from rfl] at hreg
  obtain ⟨hs, he⟩ := hreg.2.2 r hr
  have h : ReadsAt rd (mainPtr fs fp (honestWordsC Ht seed s w) 2)
      ((s.claims.sphincs ++ (planS s w).2).flatMap sCellsOf) := mainIn_reads hL 2 (by omega)
  have := readsAt_flatMap4 sCellsOf_length h ((planS s w).1.getD r 0) (by simp only [List.length_append]; exact hs)
  rw [hc, List.getElem?_eq_getElem (by simpa using hs), Option.some.injEq] at he
  rw [he] at this
  exact this

theorem honC_dEntry (hL : MemL rd (mainIn fs fp (honestWordsC Ht seed s w))) {r : ℕ}
    (hr : r < (writersD s w).length) {cl : DaClaim} (hc : (writersD s w)[r]? = some cl) :
    ReadsAt rd (mainPtr fs fp (honestWordsC Ht seed s w) 0 * gen ^ (4 * (planD s w).1.getD r 0))
      (daCellsOf cl) := by
  have hreg := region_slots s.claims.da (writersD s w)
  rw [show assign s.claims.da [] [] (writersD s w) = planD s w from rfl] at hreg
  obtain ⟨hs, he⟩ := hreg.2.2 r hr
  have h : ReadsAt rd (mainPtr fs fp (honestWordsC Ht seed s w) 0)
      ((s.claims.da ++ (planD s w).2).flatMap daCellsOf) := mainIn_reads hL 0 (by omega)
  have := readsAt_flatMap4 daCellsOf_length h ((planD s w).1.getD r 0) (by simp only [List.length_append]; exact hs)
  rw [hc, List.getElem?_eq_getElem (by simpa using hs), Option.some.injEq] at he
  rw [he] at this
  exact this


/-- **A raw leanXMSS signature verifies its slot's claim.** -/
theorem honC_xSig (hX : List.Forall₂ (XmssHeldWith Ha w.children) s.claims.xmss w.xmss)
    (hL : MemL rd (mainIn fs fp (honestWordsC Ht seed s w))) {c : ℕ} (hc : c < hrx s w) :
    Meaning_verify_lean_xmssWith Ha rd [mainPtr fs fp (honestWordsC Ht seed s w) 1 *
      gen ^ (4 * (planX s w).1.getD c 0)] [] := by
  have hmem : (direct s.claims.xmss w.xmss)[c]'hc ∈ direct s.claims.xmss w.xmss := List.getElem_mem _
  have hv := direct_mem hX hmem
  have he := honC_xEntry fs Ht hL (by rw [writersX_len]; omega) (writersX_raw hc)
  exact ⟨_, rfl, rfl, _, _, claimAt_of_reads he, _, hv⟩

/-- **A raw leanSPHINCS signature verifies its slot's claim.** -/
theorem honC_sSig (hS : List.Forall₂ (SphincsHeldWith Ha w.children) s.claims.sphincs w.sphincs)
    (hL : MemL rd (mainIn fs fp (honestWordsC Ht seed s w))) {c : ℕ} (hc : c < hrs s w) :
    Meaning_verify_sig_lean_sphincsWith Ha rd [mainPtr fs fp (honestWordsC Ht seed s w) 2 *
      gen ^ (4 * (planS s w).1.getD c 0)] [] := by
  have hmem : (direct s.claims.sphincs w.sphincs)[c]'hc ∈ direct s.claims.sphincs w.sphincs :=
    List.getElem_mem _
  have hv := direct_mem hS hmem
  have he := honC_sEntry fs Ht hL (by rw [writersS_len]; omega) (writersS_raw hc)
  exact ⟨_, rfl, rfl, _, _, claimAt_of_reads he, _, hv⟩

/-! ## The direct DA claim -/

theorem honC_daVerify (hD : List.Forall₂ (DaHeldWith Ha daPadCell daPadRow w.children) s.claims.da w.da)
    (h1 : hrd s w = 1) :
    ∃ (wt : Da.Witness) (root vd : Digest), wt.OpensWith Ha daPadCell daPadRow root vd ∧
      wt.rows.length = (honestWordsC Ht seed s w).drows ∧
      ∀ rd, MemL rd (mainIn fs fp (honestWordsC Ht seed s w)) →
        DaVerifyPreAt root vd rd [ofK (gpow (mainExpBase fs fp (honestWordsC Ht seed s w) + 34))]
          [(honestWordsC Ht seed s w).dr.1, (honestWordsC Ht seed s w).dr.2.1, (honestWordsC Ht seed s w).dr.2.2.1,
            (honestWordsC Ht seed s w).dr.2.2.2] := by
  unfold hrd at h1
  match hd : direct s.claims.da w.da, h1 with
  | [p], _ =>
    have hv := direct_mem hD (p := p) (by rw [hd]; exact List.mem_singleton_self p)
    refine ⟨p.2, p.1.1, p.1.2, hv, by simp [honestWordsC, hd], fun rd hL => ⟨squaresAt_of_mainIn fs hL, ?_, ?_⟩⟩ <;>
      simp [honestWordsC, hd, drOf]


theorem honC_daCover (hlim : Limits s w) (h1 : hrd s w = 1) (hL : MemL rd (mainIn fs fp (honestWordsC Ht seed s w))) :
    CoverPreAt ((planD s w).1.getD 0 0) rd [mainPtr fs fp (honestWordsC Ht seed s w) 0,
      mainPtr fs fp (honestWordsC Ht seed s w) 4 * (gen ^ s.claims.xmss.length * gen ^ (planX s w).2.length *
        (gen ^ s.claims.sphincs.length * gen ^ (planS s w).2.length)),
      gen ^ s.claims.da.length * gen ^ (planD s w).2.length, gen ^ hrx s w * gen ^ hrs s w]
      [(honestWordsC Ht seed s w).dr.1, (honestWordsC Ht seed s w).dr.2.1, (honestWordsC Ht seed s w).dr.2.2.1,
        (honestWordsC Ht seed s w).dr.2.2.2] := by
  have hr : 0 < (writersD s w).length := by rw [writersD_len]; omega
  obtain ⟨hs, hc⟩ := honC_markD fs Ht (seed := seed) (fp := fp) hr
  have hdau := honest_dau hlim
  have hm := hc.load hL
  rw [gD_raw (by omega), Nat.add_zero, pow_add] at hm
  have he := honC_dEntry fs Ht hL hr (writersD_raw (by omega))
  refine ⟨s.claims.da.length + (planD s w).2.length, by omega, hs,
    (pow_add _ _ _).symm, loadHolds_cover hm, ?_⟩
  unfold hrd at h1
  match hd : direct s.claims.da w.da, h1 with
  | [p], _ =>
    simp only [hd, List.getElem_cons_zero] at he
    simp only [honestWordsC, hd, drOf]
    exact he

/-! ## The running counts -/

theorem honC_wTab_getD (c : ℕ) (hc : c ≤ w.children.length) :
    (honestWordsC Ht seed s w).wTab.getD c 0 = gen ^ hbase s w c := by
  simp only [honestWordsC]
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp

theorem honC_written (c : ℕ) (hc : c ≤ w.children.length) :
    CellL (mainIn fs fp (honestWordsC Ht seed s w)) (mainBase fs fp (honestWordsC Ht seed s w) 8 + c)
      (gen ^ hbase s w c) :=
  cellL_of_getD (mainIn_mem 8 (by omega)) c (by simp [MainWords.bufs, honestWordsC]; omega)
    (honC_wTab_getD (Ht := Ht) c hc)

/-! ## The statement -/

theorem honC_stmt {bytecode : List K} (hb : bytecode.length = 2 ^ 22)
    (hsh : s.defer.Shaped bytecode) {pi : Digest}
    (hpi : Digest.stmtDigestOfWith Ha seed (signersDigestH Ht s.claims.xmss s.claims.sphincs)
      (daListDigestH Ht s.claims.da) s.defer.cells = some pi)
    (hL : MemL rd (mainIn fs fp (honestWordsC Ht seed s w))) :
    SdPreAtC Ha (signersDigestH Ht s.claims.xmss s.claims.sphincs) s.defer.cells rd
      [(digestScalars seed).1, (digestScalars seed).2,
      mainPtr fs fp (honestWordsC Ht seed s w) 3, (digestScalars (daListDigestH Ht s.claims.da)).1,
      (digestScalars (daListDigestH Ht s.claims.da)).2, mainPtr fs fp (honestWordsC Ht seed s w) 9]
      [(digestScalars pi).1, (digestScalars pi).2] := by
  have h3 : ReadsAt rd (mainPtr fs fp (honestWordsC Ht seed s w) 3)
      [(digestScalars (signersDigestH Ht s.claims.xmss s.claims.sphincs)).1,
        (digestScalars (signersDigestH Ht s.claims.xmss s.claims.sphincs)).2] :=
    mainIn_reads hL 3 (by omega)
  have h9 : ReadsAt rd (mainPtr fs fp (honestWordsC Ht seed s w) 9) s.defer.cells :=
    mainIn_reads hL 9 (by omega)
  exact ⟨seed, daListDigestH Ht s.claims.da, defer_cells_length hb hsh, rfl, h3 0 (by simp),
    h3 1 (by simp), rfl, h9, pi, hpi, rfl⟩

/-- **The signer set's block under `S`**: answered by `Ha`, it checks (`hon_sig`). -/
theorem honC_sig {S : BlakeSem} (hF : FsRowsC S Ha) {a b d : Digest}
    (h : Ha (digestBytes a ++ digestBytes b) = some d) :
    S.check ![(digestScalars a).1, (digestScalars a).2, (digestScalars b).1, (digestScalars b).2]
      ivCells.1 ivCells.2 (digestScalars d).1 (digestScalars d).2 (metadataCell 64 true) := by
  refine hF.oneBlock (fun i => ?_) ?_
  · fin_cases i
    exacts [(isCanonical128_digestScalars a).1, (isCanonical128_digestScalars a).2,
      (isCanonical128_digestScalars b).1, (isCanonical128_digestScalars b).2]
  · rw [← h, digestBytes_eq, digestBytes_eq]
    congr 1

end
end LeanVM.Guest.B1.Main
