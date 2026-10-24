/-
  LeanVM.Guest.B1.Opening.QueriesPlacedD0

  `opening_queries` deeper is `CompleteAtB`.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlacedD1

/-!
# `opening_queries` deeper, `CompleteAtB`

As at level 0 (`oqMain1_completeAtB`), a deeper specialization (`base = 0`, `odd = 0`, one query an
iteration): `oqMain0_completeAtB`, its own layout its chain buffer and its iterations' frame runs
(`OqFits0`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-- The frames fit a deeper specialization's frame run. -/
def OqFits0 (fs : String → ℕ) (cert : String → V → ℕ) (loop : String) (s : Oq) : Prop :=
  cert loop (.n (oqCh s 10 true)) + 4 * s.pd ≤ fs loop

/-- **`opening_queries` deeper is `CompleteAtB`.** -/
theorem oqMain0_completeAtB (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ)
    {s : Oq} (hs : s.RowShape) (hb0 : s.base = 0) (hpd : 4 * s.pd ≤ 80) (hpd1 : 1 ≤ s.pd)
    (hcd : 2 ≤ s.cd) (hcd8 : s.cd ≤ 8) {name loop : String} {fm fl : Fn}
    (hfm : coreProgram.find? name = some fm)
    (hpm : fm.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6])
    (hbm : fm.body = oqMainT s 0 loop)
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop0T s loop) (hlp : coreProgram.loop loop = true)
    (hfit : OqFits0 fs cert loop s)
    {Lin : Main.Layout} {N : ℕ} (hN : N + 1 < ordG) {ecap eflags eqp ewp : ℕ} {lam lamN : E}
    (hlam : lam ≠ 0) {w : ℕ → E} {eb qs : ℕ → ℕ} {rows : ℕ → List K} {sibs : ℕ → List Digest}
    (hst : ∀ k < N, qs k < 2 ^ (s.pd + s.cd) ∧ (rows k).length = s.R ∧ (sibs k).length = s.pd)
    (hreg : OqLinReg (RegionL Lin) s ecap eflags eqp ewp eb qs N)
    (hmem : ∀ rd, LowDef κ rd → MemL rd Lin →
      OqLinMem rd s (ofK (Parameters.gpow ecap)) (ofK (Parameters.gpow eflags))
        (ofK (Parameters.gpow ewp)) (ofK (Parameters.gpow eqp)) w eb qs rows sibs N) :
    CompleteAtB fs cert κ name Lin
      [ofK (Parameters.gpow ecap), ofK (Parameters.gpow eflags), lam, lamN,
        ofK (Parameters.gpow eqp), ofK (Parameters.gpow ewp), gen ^ N]
      (Returns [oqChain 0 s.base lam⁻¹ (fun k ↦ rowDot s.base s.I (rows k) w) N * lamN])
      (fs name + (N + 1) + (N + 1) * fs loop) := by
  intro fp
  set ds : ℕ → E := fun k ↦ rowDot s.base s.I (rows k) w with hds
  set c1 := cert loop (.n (oqCh s 10 true)) with hc1
  set bL := fp + fs name + (N + 1) with hbL
  obtain ⟨chainL, hchainL⟩ : ∃ L : Main.Layout,
      L = [(fp + fs name, oqChainVals 0 s.base lam ds N)] := ⟨_, rfl⟩
  obtain ⟨blk, hblk⟩ : ∃ blk : ℕ → Main.Layout, blk = fun j ↦
    [(bL + j * fs loop + c1, oqRunCells s.pd (rows j) (qs j) (sibs j))] := ⟨_, rfl⟩
  obtain ⟨iters, hiters⟩ : ∃ L : Main.Layout, L = (List.range N).flatMap blk := ⟨_, rfl⟩
  have hlenR : ∀ (row : List K) (q : ℕ) (sb : List Digest),
      (oqRunCells s.pd row q sb).length = 4 * s.pd := fun _ _ _ ↦ by simp [oqRunCells]
  have wChain : Within chainL (fp + fs name) (N + 1) := by
    intro x hx
    simp only [hchainL, List.mem_singleton] at hx
    subst hx
    simp [oqChainVals]
  have wBlk : ∀ j, Within (blk j) (bL + j * fs loop) (fs loop) := by
    intro j x hx
    simp only [hblk, List.mem_singleton] at hx
    subst hx
    have h1 : c1 + 4 * s.pd ≤ fs loop := hfit
    simp only [hlenR]; omega
  have dBlk : ∀ j, DisjL (blk j) := fun j ↦ by rw [hblk]; exact List.pairwise_singleton _ _
  obtain ⟨dIt, wIt⟩ := disjL_flatMap_range bL (fs loop) blk wBlk dBlk N
  rw [← hiters] at dIt wIt
  set n := fs name + (N + 1) + (N + 1) * fs loop with hn
  have hNf : (N + 1) * fs loop = N * fs loop + fs loop := by ring
  have wAll : Within (chainL ++ iters) fp n :=
    within_append.mpr ⟨wChain.mono (by omega) (by omega), wIt.mono (by omega) (by omega)⟩
  have dAll : DisjL (chainL ++ iters) :=
    disj_append (by rw [hchainL]; exact List.pairwise_singleton _ _) dIt wChain wIt le_rfl
  refine ⟨n, chainL ++ iters, _, [], ⟨rfl, rfl⟩, by simpa using wAll,
    by simpa using dAll, le_rfl, fun rd hlow hm ↦ ?_⟩
  rw [List.nil_append, Main.memL_append, Main.memL_append] at hm
  obtain ⟨⟨hmChain, hmIt⟩, hmLin⟩ := hm
  obtain ⟨hw, hk⟩ := hmem rd hlow hmLin
  have hch : ∀ i ≤ N, LoadHolds rd (ofK (Parameters.gpow (fp + fs name))) i
      (oqChain 0 s.base lam⁻¹ ds i) := by
    intro i hi
    have := hmChain (fp + fs name, oqChainVals 0 s.base lam ds N) (by rw [hchainL]; simp) i
      (by simp [oqChainVals]; omega)
    simpa [oqChainVals] using this
  refine relAtIn_dmono (D := fun _ ↦ False) ?_ (fun i hi ↦ absurd hi (regionL_nil i))
  refine oqMain0_placed (hNv := oqChain 0 s.base lam⁻¹ ds N)
    (r := rows) (w := fun _ ↦ w) (q := qs) (sb := sibs)
    (bp := fun j ↦ ofK (Parameters.gpow (eb j))) (v := fun j ↦ oqChain 0 s.base lam⁻¹ ds j)
    coreProgram_wf fs cert hs hpd hpd1 hcd hcd8 hfm hpm hbm hfl hpl hbl hlp hN hlam
    (by simpa [oqChain] using hch 0 (by omega)) (hch N le_rfl) (fun j hj ↦ ?_)
  have hk1 := hk j hj
  obtain ⟨qa, ra, sa⟩ := hst j hj
  have hra : ReadsAt rd (ofK (Parameters.gpow (bL + j * fs loop + c1)))
      (oqRunCells s.pd (rows j) (qs j) (sibs j)) :=
    hmIt (bL + j * fs loop + c1, oqRunCells s.pd (rows j) (qs j) (sibs j))
      (by rw [hiters]; exact List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, by rw [hblk]; simp⟩)
  refine ⟨qdOk_of_run ra sa qa hra hw hk1.2.2.1 hk1.2.2.2.1 hk1.2.2.2.2, hk1.1, hk1.2.1,
    hch j (by omega), ?_, ⟨eqp + j, ?_, Or.inl (hreg.2 j hj).1⟩,
    (oqQReg_of hreg hj).mono fun i hi ↦ Or.inl hi, fun e he ↦ ?_⟩
  · have := hch (j + 1) (by omega)
    rw [oqChain_succ_zero hb0] at this
    exact this
  · rw [addr_gpow, Nat.add_zero]
  · refine ⟨fp + fs name + (j + e), ?_, Or.inr ⟨by omega, by omega⟩⟩
    rw [addr_gpow, Nat.add_assoc]

end
end LeanVM.Guest.B1
