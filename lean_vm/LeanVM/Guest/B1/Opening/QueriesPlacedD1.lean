/-
  LeanVM.Guest.B1.Opening.QueriesPlacedD1

  `opening_queries` at level 0 is `CompleteAtB`.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlacedL
public import LeanVM.Guest.B1.Opening.QueriesMainW

/-!
# `opening_queries` at level 0, `CompleteAtB`

The honest data of the call: the iterations `N`, the queries' positions `qs`, rows `rows` and
siblings below the cap `sibs`, the weights `w`, the bit runs at `g^(eb k)`; the caller's buffers
at `g^ecap` (the cap), `g^eflags`, `g^eqp` (the bit pointers), `g^ewp` (the weights).

* `OqLinMem`: what every memory holding the caller's words `Lin` holds: the weights, the bit
  pointers and bits, each query's cap leaf (its path's top) and its flag;
* `OqLinReg`: those words lie in `Lin`'s region.

`oqMain1_completeAtB`: the function is `CompleteAtB` on `Lin`, returning the chain's end times
`λ_n`, its own layout its chain buffer (`oqChainVals`) and its queries' frame runs
(`oqRunCells`) where the bump allocator and the frame certificate put them (`OqFits1`), by a tree
of at most `fs name + (N + 1) + (N + 1) * fs loop` words (the odd query runs in the frame).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-- **What the memory holds of `opening_queries`' caller's words**: the weights at `wp`, and for
each query `k < Q` its bit pointer `qptrs[k] = g^(eb k)`, its position's bits there, its cap leaf
(its path's top) and its parent's flag. -/
def OqLinMem (rd : Reader) (s : Oq) (cap flags wp qptrs : E) (w : ℕ → E) (eb qs : ℕ → ℕ)
    (rows : ℕ → List K) (sibs : ℕ → List Digest) (Q : ℕ) : Prop :=
  (∀ l < s.lo + s.I / s.lo, LoadHolds rd wp l (w l)) ∧
    ∀ k < Q, LoadHolds rd qptrs k (ofK (Parameters.gpow (eb k))) ∧
      (∀ l < s.pd + s.cd, LoadHolds rd (ofK (Parameters.gpow (eb k))) l (bitE ((qs k).testBit l))) ∧
      LoadHolds rd cap (2 * (2 ^ s.cd + qs k / 2 ^ s.pd))
        (digestScalars (climbD (hashWords (rows k)) (qs k) (sibs k))).1 ∧
      LoadHolds rd cap (2 * (2 ^ s.cd + qs k / 2 ^ s.pd) + 1)
        (digestScalars (climbD (hashWords (rows k)) (qs k) (sibs k))).2 ∧
      LoadHolds rd flags (2 ^ (s.cd - 1) + qs k / 2 ^ (s.pd + 1)) 1

/-- **Where those words lie**: in the region `R`. -/
def OqLinReg (R : ℕ → Prop) (s : Oq) (ecap eflags eqp ewp : ℕ) (eb qs : ℕ → ℕ) (Q : ℕ) : Prop :=
  (∀ l < s.lo + s.I / s.lo, R (ewp + l)) ∧
    ∀ k < Q, R (eqp + k) ∧ (∀ l < s.pd + s.cd, R (eb k + l)) ∧
      R (eflags + (qs k / 2 ^ (s.pd + 1) + 2 ^ (s.cd - 1))) ∧
      ∀ e < 2, R (ecap + (2 * (2 ^ s.cd + qs k / 2 ^ s.pd) + e))

/-- The frames fit a level-0 specialization's frame runs: the odd first query's in the function's
frame, the iteration's two in the loop helper's, apart. -/
structure OqFits1 (fs : String → ℕ) (cert : String → V → ℕ) (name loop : String) (s : Oq)
    (odd : ℕ) : Prop where
  main : odd = 1 → cert name (.n (oqCh s 13 true)) + 4 * s.pd ≤ fs name
  q1 : cert loop (.n (oqCh s 11 true)) + 4 * s.pd ≤ fs loop
  q2 : cert loop (.n (oqCh s (oqE1 s + 1) false)) + 4 * s.pd ≤ fs loop
  apart : cert loop (.n (oqCh s 11 true)) + 4 * s.pd ≤ cert loop (.n (oqCh s (oqE1 s + 1) false)) ∨
    cert loop (.n (oqCh s (oqE1 s + 1) false)) + 4 * s.pd ≤ cert loop (.n (oqCh s 11 true))

theorem cap_index (q pd cd e : ℕ) :
    4 * (q / 2 ^ (pd + 1)) + (if q.testBit pd then 2 else 0) + (2 ^ (cd + 1) + e) =
      2 * (2 ^ cd + q / 2 ^ pd) + e := by
  have hsplit : q / 2 ^ pd = 2 * (q / 2 ^ (pd + 1)) + (if q.testBit pd then 1 else 0) := by
    rw [Nat.testBit_eq_decide_div_mod_eq, pow_succ, ← Nat.div_div_eq_div_mul]
    by_cases h : q / 2 ^ pd % 2 = 1
    · simp [h]; omega
    · simp [h]; omega
  rw [hsplit, pow_succ]
  split <;> ring

theorem limb_addr (b k : ℕ) : (ofK (Parameters.gpow b)).limb 0 * Parameters.gpow k =
    Parameters.gpow (b + k) := Main.addr_ofK b k

/-- The query region `OqQReg` from `OqLinReg`. -/
theorem oqQReg_of {R : ℕ → Prop} {s : Oq} {ecap eflags eqp ewp : ℕ}
    {eb qs : ℕ → ℕ} {Q : ℕ} (h : OqLinReg R s ecap eflags eqp ewp eb qs Q) {k : ℕ} (hk : k < Q) :
    OqQReg R s (ofK (Parameters.gpow ecap)) (ofK (Parameters.gpow eflags))
      (ofK (Parameters.gpow ewp)) (ofK (Parameters.gpow (eb k))) (qs k) := by
  obtain ⟨-, b, f, c⟩ := h.2 k hk
  refine ⟨fun off ho ↦ ⟨_, limb_addr _ _, h.1 off ho⟩, fun off ho ↦ ⟨_, limb_addr _ _, b off ho⟩,
    ⟨_, by rw [addr_gpow, Nat.add_assoc], f⟩, fun e he ↦ ⟨_, by rw [addr_gpow], ?_⟩⟩
  rw [Nat.add_assoc, cap_index _ _ _ _]
  exact c e he

theorem OqQReg.mono {R R' : ℕ → Prop} {s : Oq} {cap flags wp bp : E} {q : ℕ}
    (h : OqQReg R s cap flags wp bp q) (hR : ∀ i, R i → R' i) : OqQReg R' s cap flags wp bp q :=
  ⟨fun o ho ↦ let ⟨i, h1, h2⟩ := h.w o ho; ⟨i, h1, hR i h2⟩,
    fun o ho ↦ let ⟨i, h1, h2⟩ := h.b o ho; ⟨i, h1, hR i h2⟩,
    let ⟨i, h1, h2⟩ := h.f; ⟨i, h1, hR i h2⟩,
    fun e he ↦ let ⟨i, h1, h2⟩ := h.c e he; ⟨i, h1, hR i h2⟩⟩

theorem regionL_nil (i : ℕ) : ¬ RegionL [] i := by simp [RegionL]

/-- **`opening_queries` at level 0 is `CompleteAtB`.** -/
theorem oqMain1_completeAtB (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ)
    {s : Oq} (hs : s.RowShape) (hb1 : s.base = 1) (hpd : 4 * s.pd ≤ 80) (hpd1 : 1 ≤ s.pd)
    (hcd : 2 ≤ s.cd) (hcd8 : s.cd ≤ 8) {odd : ℕ} (hodd : odd ≤ 1) {name loop : String} {fm fl : Fn}
    (hfm : coreProgram.find? name = some fm)
    (hpm : fm.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6])
    (hbm : fm.body = oqMainT s odd loop)
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop1T s odd loop) (hlp : coreProgram.loop loop = true)
    (hfit : OqFits1 fs cert name loop s odd)
    {Lin : Main.Layout} {N : ℕ} (hN : N + 1 < ordG) {ecap eflags eqp ewp : ℕ} {lam lamN : E}
    (hlam : lam ≠ 0) {w : ℕ → E} {eb qs : ℕ → ℕ} {rows : ℕ → List K} {sibs : ℕ → List Digest}
    (hst : ∀ k < odd + 2 * N, qs k < 2 ^ (s.pd + s.cd) ∧ (rows k).length = s.R ∧
      (sibs k).length = s.pd)
    (hreg : OqLinReg (RegionL Lin) s ecap eflags eqp ewp eb qs (odd + 2 * N))
    (hmem : ∀ rd, LowDef κ rd → MemL rd Lin →
      OqLinMem rd s (ofK (Parameters.gpow ecap)) (ofK (Parameters.gpow eflags))
        (ofK (Parameters.gpow ewp)) (ofK (Parameters.gpow eqp)) w eb qs rows sibs (odd + 2 * N)) :
    CompleteAtB fs cert κ name Lin
      [ofK (Parameters.gpow ecap), ofK (Parameters.gpow eflags), lam, lamN,
        ofK (Parameters.gpow eqp), ofK (Parameters.gpow ewp), gen ^ N]
      (Returns [oqChain odd s.base lam⁻¹ (fun k ↦ rowDot s.base s.I (rows k) w) N * lamN])
      (fs name + (N + 1) + (N + 1) * fs loop) := by
  intro fp
  set ds : ℕ → E := fun k ↦ rowDot s.base s.I (rows k) w with hds
  set cap := ofK (Parameters.gpow ecap)
  set flags := ofK (Parameters.gpow eflags)
  set wp := ofK (Parameters.gpow ewp)
  set qptrs := ofK (Parameters.gpow eqp)
  set cm := cert name (.n (oqCh s 13 true)) with hcm
  set c1 := cert loop (.n (oqCh s 11 true)) with hc1
  set c2 := cert loop (.n (oqCh s (oqE1 s + 1) false)) with hc2
  set bL := fp + fs name + (N + 1) with hbL
  obtain ⟨mainRun, hmainRun⟩ : ∃ L : Main.Layout, L = if odd = 1 then
      [(fp + cm, oqRunCells s.pd (rows 0) (qs 0) (sibs 0))] else [] := ⟨_, rfl⟩
  obtain ⟨chainL, hchainL⟩ : ∃ L : Main.Layout,
      L = [(fp + fs name, oqChainVals odd s.base lam ds N)] := ⟨_, rfl⟩
  obtain ⟨blk, hblk⟩ : ∃ blk : ℕ → Main.Layout, blk = fun j ↦
    [(bL + j * fs loop + c1, oqRunCells s.pd (rows (odd + 2 * j)) (qs (odd + 2 * j)) (sibs (odd + 2 * j))),
      (bL + j * fs loop + c2, oqRunCells s.pd (rows (odd + 2 * j + 1)) (qs (odd + 2 * j + 1))
        (sibs (odd + 2 * j + 1)))] := ⟨_, rfl⟩
  obtain ⟨iters, hiters⟩ : ∃ L : Main.Layout, L = (List.range N).flatMap blk := ⟨_, rfl⟩
  have hlenR : ∀ (row : List K) (q : ℕ) (sb : List Digest),
      (oqRunCells s.pd row q sb).length = 4 * s.pd := fun _ _ _ ↦ by simp [oqRunCells]
  -- the layout's place
  have wMain : Within mainRun fp (fs name) := by
    intro x hx
    rw [hmainRun] at hx
    split_ifs at hx with ho
    · simp only [List.mem_singleton] at hx
      subst hx
      have := hfit.main ho
      simp only [hlenR]; omega
    · simp at hx
  have dMain : DisjL mainRun := by
    rw [hmainRun]; split_ifs
    · exact List.pairwise_singleton _ _
    · exact disj_nil
  have wChain : Within chainL (fp + fs name) (N + 1) := by
    intro x hx
    simp only [hchainL, List.mem_singleton] at hx
    subst hx
    simp [oqChainVals]
  have wBlk : ∀ j, Within (blk j) (bL + j * fs loop) (fs loop) := by
    intro j x hx
    simp only [hblk, List.mem_cons, List.not_mem_nil, or_false] at hx
    have h1 := hfit.q1; have h2 := hfit.q2
    rcases hx with rfl | rfl <;> simp only [hlenR] <;> omega
  have dBlk : ∀ j, DisjL (blk j) := by
    intro j
    simp only [hblk, DisjL, List.pairwise_cons, List.mem_singleton, forall_eq, hlenR]
    refine ⟨?_, by simp, List.Pairwise.nil⟩
    rcases hfit.apart with h | h
    · left; omega
    · right; omega
  obtain ⟨dIt, wIt⟩ := disjL_flatMap_range bL (fs loop) blk wBlk dBlk N
  rw [← hiters] at dIt wIt
  set n := fs name + (N + 1) + (N + 1) * fs loop with hn
  have hNf : (N + 1) * fs loop = N * fs loop + fs loop := by ring
  have wCI : Within (chainL ++ iters) (fp + fs name) ((N + 1) + N * fs loop) :=
    within_append.mpr ⟨wChain.mono le_rfl (by omega), wIt.mono (by omega) (by omega)⟩
  have wAll : Within (mainRun ++ (chainL ++ iters)) fp n :=
    within_append.mpr ⟨wMain.mono le_rfl (by omega), wCI.mono (by omega) (by omega)⟩
  have dAll : DisjL (mainRun ++ (chainL ++ iters)) :=
    disj_append dMain (disj_append (by rw [hchainL]; exact List.pairwise_singleton _ _) dIt wChain wIt le_rfl)
      wMain wCI (le_refl _)
  refine ⟨n, mainRun ++ (chainL ++ iters), _, [], ⟨rfl, rfl⟩, by simpa using wAll,
    by simpa using dAll, le_rfl, fun rd hlow hm ↦ ?_⟩
  rw [List.nil_append, Main.memL_append, Main.memL_append, Main.memL_append] at hm
  obtain ⟨⟨hmMain, hmChain, hmIt⟩, hmLin⟩ := hm
  obtain ⟨hw, hk⟩ := hmem rd hlow hmLin
  -- the chain buffer
  have hch : ∀ i ≤ N, LoadHolds rd (ofK (Parameters.gpow (fp + fs name))) i
      (oqChain odd s.base lam⁻¹ ds i) := by
    intro i hi
    have := hmChain (fp + fs name, oqChainVals odd s.base lam ds N) (by rw [hchainL]; simp) i
      (by simp [oqChainVals]; omega)
    simpa [oqChainVals] using this
  have hRL : ∀ i, RegionL Lin i → RegionL Lin i := fun _ h ↦ h
  refine relAtIn_dmono (D := fun _ ↦ False) ?_ (fun i hi ↦ absurd hi (regionL_nil i))
  refine oqMain1_placed (r := rows 0) (w := w) (q := qs 0) (sb := sibs 0)
    (bp := ofK (Parameters.gpow (eb 0))) (hNv := oqChain odd s.base lam⁻¹ ds N)
    (r1 := fun j ↦ rows (odd + 2 * j)) (r2 := fun j ↦ rows (odd + 2 * j + 1))
    (w1 := fun _ ↦ w) (w2 := fun _ ↦ w) (q1 := fun j ↦ qs (odd + 2 * j))
    (q2 := fun j ↦ qs (odd + 2 * j + 1)) (sb1 := fun j ↦ sibs (odd + 2 * j))
    (sb2 := fun j ↦ sibs (odd + 2 * j + 1)) (bp1 := fun j ↦ ofK (Parameters.gpow (eb (odd + 2 * j))))
    (bp2 := fun j ↦ ofK (Parameters.gpow (eb (odd + 2 * j + 1))))
    (v := fun j ↦ oqChain odd s.base lam⁻¹ ds j)
    coreProgram_wf fs cert hs hpd hpd1 hcd hcd8 hodd hfm hpm hbm hfl hpl hbl hlp hN hlam
    (fun ho ↦ ?_) (fun ho ↦ ?_) (hch N le_rfl) (fun j hj ↦ ?_)
  · -- the odd first query
    subst ho
    obtain ⟨b0, bits0, c00, c01, f0⟩ := hk 0 (by omega)
    obtain ⟨q0, r0, s0⟩ := hst 0 (by omega)
    have hrun : ReadsAt rd (ofK (Parameters.gpow (fp + cm))) (oqRunCells s.pd (rows 0) (qs 0) (sibs 0)) :=
      hmMain (fp + cm, oqRunCells s.pd (rows 0) (qs 0) (sibs 0)) (by rw [hmainRun]; simp)
    refine ⟨b0, bits0, qdOk_of_run r0 s0 q0 hrun hw c00 c01 f0, ?_,
      ⟨_, limb_addr _ _, (hreg.2 0 (by omega)).1⟩, oqQReg_of hreg (by omega)⟩
    have := hch 0 (by omega)
    simpa [oqChain] using this
  · have := hch 0 (by omega)
    simpa [oqChain, ho] using this
  · -- an iteration
    have hk1 := hk (odd + 2 * j) (by omega)
    have hk2 := hk (odd + 2 * j + 1) (by omega)
    obtain ⟨qa, ra, sa⟩ := hst (odd + 2 * j) (by omega)
    obtain ⟨qb, rb, sb⟩ := hst (odd + 2 * j + 1) (by omega)
    have hrun : ∀ x ∈ blk j, ReadsAt rd (ofK (Parameters.gpow x.1)) x.2 := fun x hx ↦
      hmIt x (by rw [hiters]; exact List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, hx⟩)
    have hra := hrun (bL + j * fs loop + c1, oqRunCells s.pd (rows (odd + 2 * j)) (qs (odd + 2 * j))
      (sibs (odd + 2 * j))) (by rw [hblk]; simp)
    have hrb := hrun (bL + j * fs loop + c2, oqRunCells s.pd (rows (odd + 2 * j + 1))
      (qs (odd + 2 * j + 1)) (sibs (odd + 2 * j + 1))) (by rw [hblk]; simp)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hch j (by omega), ?_, fun e he ↦ ?_,
      (oqQReg_of hreg (by omega)).mono fun i hi ↦ Or.inl hi,
      (oqQReg_of hreg (by omega)).mono fun i hi ↦ Or.inl hi, fun e he ↦ ?_⟩
    · exact qdOk_of_run ra sa qa hra hw hk1.2.2.1 hk1.2.2.2.1 hk1.2.2.2.2
    · exact qdOk_of_run rb sb qb hrb hw hk2.2.2.1 hk2.2.2.2.1 hk2.2.2.2.2
    · rw [show 2 * j + odd = odd + 2 * j by omega]; exact hk1.1
    · exact hk1.2.1
    · rw [show 2 * j + odd + 1 = odd + 2 * j + 1 by omega]; exact hk2.1
    · exact hk2.2.1
    · have := hch (j + 1) (by omega)
      rw [oqChain_succ_one hb1] at this
      exact this
    · refine ⟨eqp + (odd + 2 * j + e), ?_, Or.inl (hreg.2 _ (by omega)).1⟩
      rw [mul_assoc, ← pow_add, ← two_mul, addr_gpow]
      congr 1; omega
    · refine ⟨fp + fs name + (j + e), ?_, Or.inr ⟨by omega, by omega⟩⟩
      rw [addr_gpow, Nat.add_assoc]

end
end LeanVM.Guest.B1
