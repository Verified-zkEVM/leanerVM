/-
  LeanVM.Guest.B1.Comp.Tables.GkrAtC

  `verify_bus_gkr` complete in the placed form over a completeness model, by a bounded tree within
  weights, and the deployed placed completeness recovered at `CompModel.deployed`.
-/

module

public import LeanVM.Guest.B1.Comp.Tables.GkrAllC
public import LeanVM.Guest.B1.Comp.Tables.IfaceC
public import LeanVM.Guest.B1.Tables.VtCGkrB
public import LeanVM.Guest.B1.Tables.VtCSizeS

/-!
# `verify_bus_gkr`, placed, over a completeness model

`Tables/GkrAt.lean` and `Tables/VtCGkrB.lean` over a `CompModel`:

* the buffers' honest words at the model's total hash (`gkrOwnT`), read back into
  `verify_bus_gkr`'s honest memory over the model (`gkrMemC_at`);
* the loops' valid trees under any semantics (`vtcS_l11_total`, `vtcS_l101_total`,
  `vtcS_l10_total`);
* `verify_bus_gkr_completeAtWC`: `CompleteGkrAtWC` at its frame, its `HeapBuf`s and its two loops,
  from the answered run's trace (`exists_traceM`), the body over the model (`gkr_holdsC`) and the
  loops over the model (`gkr_loop10C`, `gkr_loop11C`), by `vtcS_completeAt_iteW`.

At `CompModel.deployed` it is the deployed `verify_bus_gkr_completeAtW`
(`verify_bus_gkr_completeAtW_of_comp`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.E2E.Complete
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-! ## The buffers over a hash model -/

theorem gkrOwnT_fit (M : HashModel) (T : GkrTrace) {μ : ℕ} (hμ : μ < 33) (cv : Digest) (cur pts : E) :
    List.Forall₂ (fun c s => c.length ≤ s) (gkrOwnT M T μ cv cur pts) (gkrSizes μ) := by
  have hl : ∀ i, (gLay T (μ % 2) cur pts i ++ List.replicate 8 0).length = 16 := fun i => rfl
  have hr : ∀ i, (gRow (T.P i)).length = 40 := fun i => by simp [gRow]
  simp only [gkrOwnT, gkrSizes, List.forall₂_cons, List.Forall₂.nil, and_true]
  refine ⟨?_, ?_, ?_, by decide, by decide⟩
  · rw [gLayWT, List.length_append, length_flatMap_range_const hl]
    rcases Nat.mod_two_eq_zero_or_one μ with h | h <;> simp [h, gLay0T] <;> omega
  · rw [gRndW, List.length_append, gRnds_length, List.length_replicate, gPos_eq]
    have : μ / 2 * (μ / 2) ≤ 16 * 16 := Nat.mul_le_mul (by omega) (by omega)
    have : μ / 2 * (μ % 2) ≤ 16 := by
      rcases Nat.mod_two_eq_zero_or_one μ with h | h <;> rw [h] <;> omega
    omega
  · rw [gPtsW, List.length_append, length_flatMap_range_const hr, List.length_replicate]
    omega


section
variable {M : HashModel} {T : GkrTrace} {μ : ℕ} {cv : Digest} {cur : E} {b : ℕ}

theorem mem_layT : (b, gLayWT M T μ cv cur (ofK (Parameters.gpow (gP μ b)))) ∈
    bufL b (gkrSizes μ) (gkrOwnT M T μ cv cur (ofK (Parameters.gpow (gP μ b)))) := by simp [bufL, gkrBases, gkrOwnT]

theorem mem_ptsT : (gP μ b, gPtsW T μ) ∈ bufL b (gkrSizes μ) (gkrOwnT M T μ cv cur (ofK (Parameters.gpow (gP μ b)))) := by
  simp [bufL, gkrBases, gkrOwnT]

theorem mem_pbT : (gP μ b + 1640, vbgPb) ∈ bufL b (gkrSizes μ) (gkrOwnT M T μ cv cur (ofK (Parameters.gpow (gP μ b)))) := by
  simp [bufL, gkrBases, gkrOwnT]

theorem mem_dsT : (gP μ b + 1640 + 33, vbgDs) ∈
    bufL b (gkrSizes μ) (gkrOwnT M T μ cv cur (ofK (Parameters.gpow (gP μ b)))) := by simp [bufL, gkrBases, gkrOwnT]

theorem gLayWT_length : (gLayWT M T μ cv cur (ofK (Parameters.gpow (gP μ b)))).length = 8 * (μ + 2) := by
  have hl : ∀ i, (gLay T (μ % 2) cur (ofK (Parameters.gpow (gP μ b))) i ++ List.replicate 8 0).length = 16 := fun i => rfl
  rw [gLayWT, List.length_append, length_flatMap_range_const hl]
  rcases Nat.mod_two_eq_zero_or_one μ with h | h
  · simp [h]; omega
  · simp [h, gLay0T]; omega

/-- **The buffers' memory loads what `GkrMemC` says.** -/
theorem gkrMemC_at {rd : Reader} (h : MemL rd (bufL b (gkrSizes μ) (gkrOwnT M T μ cv cur (ofK (Parameters.gpow (gP μ b)))))) :
    GkrMemC M rd T μ cv cur (ofK (Parameters.gpow b)) (ofK (Parameters.gpow (b + 8 * (μ + 2)))) (ofK (Parameters.gpow (gP μ b)))
      (ofK (Parameters.gpow (gP μ b + 1640))) (ofK (Parameters.gpow (gP μ b + 1640 + 33))) :=
  gkrMemC_of (h _ mem_layT) (h (b + 8 * (μ + 2), gRndW T μ cur) (by simp [bufL, gkrBases, gkrOwnT]))
    (h _ mem_ptsT) (h _ mem_pbT) (h _ mem_dsT)

end

/-- The two loops' frames: on the caller's words and the buffers from `b`. -/
noncomputable def gkrKidsT (M : HashModel) (T : GkrTrace) (μ : ℕ) (cv : Digest) (c z : ℕ) (Lin : Main.Layout) (b : ℕ) : List Kid :=
  [⟨"__loop10", decide (μ / 2 ≠ 0), [word 1 0 0, gen ^ (μ / 2), ofK (Parameters.gpow (gP μ b + 1640 + 33)), gen ^ μ,
      ofK (Parameters.gpow b), ofK (Parameters.gpow (b + 8 * (μ + 2)))],
      Lin ++ bufL b (gkrSizes μ) (gkrOwnT M T μ cv (ofK (Parameters.gpow c)) (ofK (Parameters.gpow (gP μ b)))), Returns []⟩,
    ⟨"__loop11", decide (μ ≠ 0), [word 1 0 0, gen ^ μ, ofK (Parameters.gpow z),
      ofK (Parameters.gpow (gP μ b)) * gen ^ (40 * (μ % 2 + μ / 2))],
      Lin ++ bufL b (gkrSizes μ) (gkrOwnT M T μ cv (ofK (Parameters.gpow c)) (ofK (Parameters.gpow (gP μ b)))), Returns []⟩]

/-! ## The loops' trees under any semantics -/

section
variable {S : BlakeSem} {fs : String → ℕ}

/-- `sumcheck_round5`'s valid trees are its frame. -/
theorem vtcS_sr5_total {rd : Reader} {t : Tree} {args rets : List E} (hn : t.name = "sumcheck_round5")
    (hv : t.ValidB S coreProgram rd args rets) (hbo : t.BufsOk coreProgram) :
    t.total fs = fs "sumcheck_round5" :=
  vtcS_leaf_total (S := S) find_sumcheck_round5 vtc_core7 vtc_p5.1 vtc_p5.2.1 vtc_p5.2.2 hn hv hbo

/-- **`__loop11`'s trees** over `m` iterations. -/
theorem vtcS_l11_total {rd : Reader} {m : ℕ} {rest : List E} {t : Tree} {rets : List E} (hm : 0 < m)
    (hn : t.name = "__loop11") (hv : t.ValidB S coreProgram rd (1 :: gen ^ m :: rest) rets)
    (hbo : t.BufsOk coreProgram) : t.total fs ≤ m * (fs "__loop11" + 0) + fs "__loop11" := by
  refine vtcS_loop_total (S := S) (fs := fs) find_loop11 vtc_core41 vtc_p11.1 vtc_p11.2.1 rd m rest 0 ?_ m 0 t rets
    (by omega) hm hn (by rwa [pow_zero]) hbo
  intro σ j _ hp hes
  simp only [show Fn.params Data.core41 = [.n 0, .n 1, .n 2, .n 3] from rfl, List.map_cons,
    List.map_nil, List.cons.injEq] at hp
  obtain ⟨h0, h1, hr⟩ := hp
  subst hr
  have a7 := vtcS_atom hes (vtc_mem (l := vtcP11) 4 rfl)
  have a8 := vtcS_atom hes (vtc_mem (l := vtcP11) 5 rfl)
  have a9 := vtcS_atom hes (vtc_mem (l := vtcP11) 6 rfl)
  have a10 := vtcS_atom hes (vtc_mem (l := vtcP11) 7 rfl)
  have a11 := vtcS_atom hes (vtc_mem (l := vtcP11) 8 rfl)
  simp only [Atom.HoldsB, word_gen] at a7 a8 a9 a10 a11
  refine ⟨by rw [a9, a8, a7, h0, h1], by simp [a11, a10, h0, h1], fun kids hk _ => ?_⟩
  rw [vtc_p11.2.2] at hk
  match kids, hk with
  | [], _ => simp [Tree.totalKids]

/-- **`__loop101`'s trees** over `m` rounds, each with its `sumcheck_round5`. -/
theorem vtcS_l101_total {rd : Reader} {m : ℕ} {rest : List E} {t : Tree} {rets : List E} (hm : 0 < m)
    (hn : t.name = "__loop101") (hv : t.ValidB S coreProgram rd (1 :: gen ^ m :: rest) rets)
    (hbo : t.BufsOk coreProgram) :
    t.total fs ≤ m * (fs "__loop101" + fs "sumcheck_round5") + fs "__loop101" := by
  refine vtcS_loop_total (S := S) (fs := fs) find_loop101 vtc_core574 vtc_p101.1 vtc_p101.2.1 rd m rest _ ?_ m 0 t
    rets (by omega) hm hn (by rwa [pow_zero]) hbo
  intro σ j _ hp hes
  simp only [show Fn.params Data.core574 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5] from rfl,
    List.map_cons, List.map_nil, List.cons.injEq] at hp
  obtain ⟨h0, h1, hr⟩ := hp
  subst hr
  have a22 := vtcS_atom hes (vtc_mem (l := vtcP101) 17 rfl)
  have a23 := vtcS_atom hes (vtc_mem (l := vtcP101) 18 rfl)
  have a24 := vtcS_atom hes (vtc_mem (l := vtcP101) 19 rfl)
  have a25 := vtcS_atom hes (vtc_mem (l := vtcP101) 20 rfl)
  have a26 := vtcS_atom hes (vtc_mem (l := vtcP101) 21 rfl)
  simp only [Atom.HoldsB, word_gen] at a22 a23 a24 a25 a26
  refine ⟨by rw [a24, a23, a22, h0, h1], by simp [a26, a25, h0, h1], fun kids hk hbk => ?_⟩
  rw [vtc_p101.2.2] at hk
  simp only [List.map_cons, List.map_nil, Main.mkCall] at hk
  match kids, hk, hbk with
  | [k], ⟨hnk, hvk, _⟩, ⟨hbk, _⟩ =>
    simp only [↓reduceIte] at hvk
    simp [Tree.totalKids, vtcS_sr5_total hnk hvk hbk]

/-- **`__loop10`'s trees** over `m ≤ 16` layers, on a memory holding `ds[μ] = g^s`, `s ≤ 1`, at
`dsb·g^μ`. -/
theorem vtcS_l10_total {rd : Reader} {m s : ℕ} {dsb gmu lay rnd : E} {t : Tree} {rets : List E}
    (hm : 0 < m) (hm16 : m ≤ 16) (hs : s ≤ 1) (hds : LoadHolds rd (dsb * gmu) 0 (gen ^ s))
    (hn : t.name = "__loop10") (hv : t.ValidB S coreProgram rd [1, gen ^ m, dsb, gmu, lay, rnd] rets)
    (hbo : t.BufsOk coreProgram) : t.total fs ≤ m * (fs "__loop10" + vtcK10 fs) + fs "__loop10" := by
  refine vtcS_loop_total (S := S) (fs := fs) find_loop10 vtc_core40 vtc_p10.1 vtc_p10.2.1 rd m [dsb, gmu, lay, rnd]
    _ ?_ m 0 t rets (by omega) hm hn (by rwa [pow_zero]) hbo
  intro σ j hj hp hes
  simp only [show Fn.params Data.core40 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5] from rfl,
    List.map_cons, List.map_nil, List.cons.injEq] at hp
  obtain ⟨h0, h1, h2, h3, h4, h5, -⟩ := hp
  have a6 := vtcS_atom hes (vtc_mem (l := vtcP10) 0 rfl)
  have a7 := vtcS_atom hes (vtc_mem (l := vtcP10) 1 rfl)
  have l8 := vtcS_atom hes (vtc_mem (l := vtcP10) 2 rfl)
  have a9 := vtcS_atom hes (vtc_mem (l := vtcP10) 3 rfl)
  have a43 := vtcS_atom hes (vtc_mem (l := vtcP10) 41 rfl)
  have a44 := vtcS_atom hes (vtc_mem (l := vtcP10) 42 rfl)
  have a45 := vtcS_atom hes (vtc_mem (l := vtcP10) 43 rfl)
  have a326 := vtcS_atom hes (vtc_mem (l := vtcP10) 312 rfl)
  have a327 := vtcS_atom hes (vtc_mem (l := vtcP10) 313 rfl)
  have a328 := vtcS_atom hes (vtc_mem (l := vtcP10) 314 rfl)
  have a329 := vtcS_atom hes (vtc_mem (l := vtcP10) 315 rfl)
  have a330 := vtcS_atom hes (vtc_mem (l := vtcP10) 316 rfl)
  simp only [Atom.HoldsB, word_gen, word_one] at a6 a7 l8 a9 a43 a44 a45 a326 a327 a328 a329 a330
  refine ⟨by rw [a328, a327, a326, h0, h1], by simp [a330, a329, h0, h1, h2, h3, h4, h5],
    fun kids hk hbk => ?_⟩
  rw [a7, h2, h3] at l8
  have e8 := loadHolds_unique l8 hds
  have e9 : σ (.n 9) = gen ^ (2 * j + s) := by rw [a9, a6, e8, h0, ← pow_add, ← pow_add]; ring_nf
  rw [vtc_p10.2.2] at hk
  simp only [List.map_cons, List.map_nil, Main.mkCall] at hk
  match kids, hk, hbk with
  | [k], ⟨hnk, hvk, _⟩, ⟨hbk, _⟩ =>
    simp only [Tree.totalKids, Nat.add_zero]
    by_cases hz : σ (.n 44) = 0
    · simp only [hz, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at hvk
      obtain ⟨⟨g, σ', rfl⟩, -⟩ := hvk
      simp only [Tree.name] at hnk
      simp only [Tree.total, hnk, vtcK10]
      omega
    · simp only [hz, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, List.map_cons,
        List.map_nil] at hvk
      rw [a45, e9] at hvk
      have hpos : 0 < 2 * j + s := by
        rcases Nat.eq_zero_or_pos (2 * j + s) with h | h
        · exfalso; apply hz; rw [a44, a43, e9, h, pow_zero]; exact e_add_self 1
        · exact h
      have := vtcS_l101_total (S := S) (fs := fs) hpos hnk hvk hbk
      have hle : (2 * j + s) * (fs "__loop101" + fs "sumcheck_round5") ≤
          31 * (fs "__loop101" + fs "sumcheck_round5") := Nat.mul_le_mul_right _ (by omega)
      simp only [vtcK10]
      omega

end

/-! ## `verify_bus_gkr`, placed -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`verify_bus_gkr` is complete, placed, by a tree of at most `vtcGkrBound fs` words weighing
at most `vtcGkrBoundW (w θ)`** (TRIAGE #37): `CompleteGkrAtW`, on memories defined below `2^κ`,
`κ ≥ 6`. -/
theorem verify_bus_gkr_completeAtWC (CM : CompModel) (fs : String → ℕ) (cert : String → V → ℕ)
    {Θ : Type} (w : Θ → String → ℕ) {κ : ℕ} (hκ : 6 ≤ κ) :
    CompleteGkrAtWC CM fs cert κ w (vtcGkrBound fs) fun θ => vtcGkrBoundW (w θ) := by
  intro cv μ xs r cv' c z Lin hμ hrun hpl hvl hLin
  obtain ⟨T, hT⟩ := exists_traceM hrun
  obtain ⟨hs1, hs2, hs3⟩ := vbg_straight
  have h2k : 33 ≤ 2 ^ κ := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hκ)
  have hxl : 2 + 6 * (μ % 2) ≤ xs.length := by
    rw [hT.xs_len, ← hT.ys_len _ le_rfl]; simp [gCur]
  refine Main.CompleteAtWS.bmono (vtcS_completeAt_iteW (S := CM.sem) find_vbg vbg_not_loop κ Lin _ _ vbg_body' hs1 (by decide) hs2
    hs3 (decide (μ % 2 = 0)) (vbg_addrs _) (gkrSizes μ)
    (fun fp => gkrOwnT CM.hm T μ cv (ofK (Parameters.gpow c)) (ofK (Parameters.gpow (gP μ (fp + fs "verify_bus_gkr")))))
    (fun fp => gkrOwnT_fit CM.hm T hμ _ _ _) (fun fp => gkrKidsT CM.hm T μ cv c z Lin (fp + fs "verify_bus_gkr"))
    (vtcGkrBd fs) (fun k θ => vtcGkrBd (w θ) k) (vtcGkrKB fs) (fun θ => vtcGkrKB (w θ)) ?_ ?_ ?_ ?_ ?_ ?_) ?_
  · intro fp k hk ht
    simp only [gkrKidsT, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · refine vtcS_completeAt_of_rel_lowW (S := CM.sem) (B := fun fs' => vtcGkrBd fs' _) pure10 (by simp) κ
        (fun rd hlow hL rd' hag => ?_) (fun fs' rd hL t rets' hn hv hbo => ?_)
      swap
      · obtain ⟨-, hL2⟩ := Main.memL_append.mp hL
        have hM := gkrMemC_at (M := CM.hm) hL2
        have hds : LoadHolds rd (ofK (Parameters.gpow (gP μ (fp + fs "verify_bus_gkr") + 1640 + 33)) * gen ^ μ) 0
            (gen ^ (μ % 2)) := loadHolds_unshift (by rw [← vbgDs_get hμ]; exact hM.ds μ (by omega)) rfl
        have hm : 0 < μ / 2 := by simp only [decide_eq_true_eq] at ht; omega
        rw [word_one] at hv
        have := vtcS_l10_total (S := CM.sem) (fs := fs') hm (by omega) (Nat.le_of_lt_succ (Nat.mod_lt _ (by omega))) hds hn hv hbo
        have hle : μ / 2 * (fs' "__loop10" + vtcK10 fs') ≤ 16 * (fs' "__loop10" + vtcK10 fs') :=
          Nat.mul_le_mul_right _ (by omega)
        simp (config := { decide := true }) only [vtcGkrBd, ↓reduceIte]
        omega
      obtain ⟨hL1, hL2⟩ := Main.memL_append.mp hL
      have hM := gkrMemC_at (M := CM.hm) (memL_of_agree hL2 fun i hi => hag i (regionL_append.mpr (Or.inr hi)))
      have hx := readsAt_transfer (fun rd h1 h2 => (hLin rd h1 h2).1) hlow hL1
        fun i hi => hag i (regionL_append.mpr (Or.inl hi))
      have hm : 0 < μ / 2 := by simp only [decide_eq_true_eq] at ht; omega
      rw [word_one]; exact gkr_loop10C hT hμ hM hx hm
    · refine vtcS_completeAt_of_rel_lowW (S := CM.sem) (B := fun fs' => vtcGkrBd fs' _) pure11 (by simp) κ
        (fun rd hlow hL rd' hag => ?_) (fun fs' rd hL t rets' hn hv hbo => ?_)
      swap
      · have hm : 0 < μ := by simp only [decide_eq_true_eq] at ht; omega
        rw [word_one] at hv
        have := vtcS_l11_total (S := CM.sem) (fs := fs') hm hn hv hbo
        have hle : μ * (fs' "__loop11" + 0) ≤ 32 * (fs' "__loop11" + 0) := Nat.mul_le_mul_right _ (by omega)
        simp (config := { decide := true }) only [vtcGkrBd, ↓reduceIte]
        omega
      obtain ⟨hL1, hL2⟩ := Main.memL_append.mp hL
      have hM := gkrMemC_at (M := CM.hm) (memL_of_agree hL2 fun i hi => hag i (regionL_append.mpr (Or.inr hi)))
      have hz := readsAt_transfer (fun rd h1 h2 => (hLin rd h1 h2).2) hlow hL1
        fun i hi => hag i (regionL_append.mpr (Or.inl hi))
      have hm : 0 < μ := by simp only [decide_eq_true_eq] at ht; omega
      rw [word_one]; exact gkr_loop11C hT hM hz hμ hm
  · intro fp k hk _ i hi
    simp only [gkrKidsT, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl <;> exact regionL_append.mp hi
  · intro fp rd hB hL k hk
    simp only [gkrKidsT, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl <;> exact Main.memL_append.mpr ⟨hL, hB⟩
  · intro fp outs ho rd hlow hB hL
    set b := fp + fs "verify_bus_gkr" with hb
    have hM := gkrMemC_at (M := CM.hm) hB
    obtain ⟨hx, hz⟩ := hLin rd hlow hL
    obtain ⟨rc1, rck, rc2⟩ := rc_complete_low hlow (K := 33) (e := μ) h2k hμ
    refine ⟨vbgσT CM.hm (ofK (Parameters.gpow z)) (digestScalars cv).1 (digestScalars cv).2 (ofK (Parameters.gpow c)) (gen ^ μ)
      (ofK (Parameters.gpow b)) (ofK (Parameters.gpow (b + 8 * (μ + 2)))) (ofK (Parameters.gpow (gP μ b))) (ofK (Parameters.gpow (gP μ b + 1640)))
      (ofK (Parameters.gpow (gP μ b + 1640 + 33))) (rcLow rd μ 33).1 (rcLow rd μ 33).2.1 (rcLow rd μ 33).2.2
      T.cnt⁻¹ T.x0 T.cnt (gen ^ (μ % 2)) (gen ^ (μ / 2)) (ofK (Parameters.gpow c) * gen ^ gCur (μ % 2) (μ / 2))
      (ofK (Parameters.gpow (gP μ b)) * gen ^ (40 * (μ % 2 + μ / 2)))
      ((T.P (μ / 2)).values.getD 0 0) ((T.P (μ / 2)).values.getD 1 0) ((T.P (μ / 2)).values.getD 2 0)
      cv (T.C (μ / 2)) T.oes, ?_, rfl,
      gkr_holdsC hT hμ hM hx hz (by rw [gen_pow_eq_ofK]; exact rc1) rc2
        (by rw [word_g32, gen_pow_eq_ofK, gen_pow_eq_ofK]; exact rck), ?_, ?_, ?_, ?_⟩
    · show gen ^ (μ % 2) + word 1 0 0 = 0 ↔ _
      rw [word_one]
      rcases Nat.mod_two_eq_zero_or_one μ with h | h
      · rw [h]; simp only [pow_zero, decide_true, iff_true]; exact e_add_self 1
      · rw [h]; simp only [pow_one, one_ne_zero, decide_false, Bool.false_eq_true, iff_false]
        intro h0
        exact gen_pow_ne_of_lt (a := 0) (b := 1) (by omega) (by omega) (by rw [pow_zero, pow_one, add_comm]; exact h0)
    · rw [vbg_allocs]
      simp only [List.map_cons, List.map_nil, Sum.elim_inr, Sum.elim_inl, id]
      have e9 : (((gen ^ μ * word 4 0 0) * (gen ^ μ * word 4 0 0)) * ((gen ^ μ * word 4 0 0) * (gen ^ μ * word 4 0 0))) *
          (((gen ^ μ * word 4 0 0) * (gen ^ μ * word 4 0 0)) * ((gen ^ μ * word 4 0 0) * (gen ^ μ * word 4 0 0))) =
          gen ^ (8 * (μ + 2)) := by
        rw [gk_word4, ← pow_add, ← pow_add, ← pow_add, ← pow_add]; congr 1; ring
      show [logG (((((gen ^ μ * word 4 0 0) * (gen ^ μ * word 4 0 0)) * ((gen ^ μ * word 4 0 0) * (gen ^ μ * word 4 0 0))) *
          (((gen ^ μ * word 4 0 0) * (gen ^ μ * word 4 0 0)) * ((gen ^ μ * word 4 0 0) * (gen ^ μ * word 4 0 0))))),
        3448, 1640, 33, 33] = _
      rw [e9, logG_g _ (by omega)]; rfl
    · rw [vbg_allocs]; rfl
    · rw [vbg_calls]
      obtain ⟨o1, o2, rfl⟩ : ∃ o1 o2, outs = [o1, o2] := by
        match outs, ho.length with
        | [o1, o2], _ => exact ⟨o1, o2, rfl⟩
      simp only [List.map_cons, List.map_nil, Main.mkCall, gkrKidsT]
      refine ⟨rfl, gk_dec (by omega), fun h => ⟨rfl, by rw [(ho.1 h).1]; rfl⟩, rfl, gk_dec hμ,
        fun h => ⟨rfl, by rw [(ho.2.1 h).1]; rfl⟩, trivial⟩
    · intro q hq
      have hbq := List.all_eq_true.mp (vbg_loads _) q hq
      obtain ⟨t, ht, htq⟩ := List.any_eq_true.mp hbq
      obtain ⟨p, off⟩ := q
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at htq
      obtain ⟨⟨hp, hlo⟩, hhi⟩ := htq
      have hlay := gLayWT_length (M := CM.hm) (T := T) (μ := μ) (cv := cv) (cur := ofK (Parameters.gpow c)) (b := b)
      have hpts := gPtsW_length (T := T) (μ := μ)
      have L2 : off < 2 → ∃ i, (ofK (Parameters.gpow c)).limb 0 * Parameters.gpow off = Parameters.gpow i ∧ (RegionL Lin i ∨
          RegionL (bufL b (gkrSizes μ) (gkrOwnT CM.hm T μ cv (ofK (Parameters.gpow c)) (ofK (Parameters.gpow (gP μ b))))) i) := fun h => by
        obtain ⟨i, hi, hr⟩ := addr_in_region (fun rd h1 h2 => (hLin rd h1 h2).1) hlow hL (j := off) (by omega)
        exact ⟨i, hi, Or.inl hr⟩
      have L144 : μ % 2 = 1 → off < 6 → ∃ i, (ofK (Parameters.gpow c) * word 4 0 0).limb 0 * Parameters.gpow off = Parameters.gpow i ∧
          (RegionL Lin i ∨ RegionL (bufL b (gkrSizes μ) (gkrOwnT CM.hm T μ cv (ofK (Parameters.gpow c)) (ofK (Parameters.gpow (gP μ b))))) i) :=
        fun hs h => by
        obtain ⟨i, hi, hr⟩ := addr_in_region (fun rd h1 h2 => (hLin rd h1 h2).1) hlow hL (j := 2 + off)
          (by omega)
        refine ⟨i, ?_, Or.inl hr⟩
        rw [gk_word4, addr_gen, ← hi, addr_k, Nat.add_assoc]
      have Lbuf : ∀ (a : ℕ) (w : List E) (m off' : ℕ),
          (a, w) ∈ bufL b (gkrSizes μ) (gkrOwnT CM.hm T μ cv (ofK (Parameters.gpow c)) (ofK (Parameters.gpow (gP μ b)))) →
          m + off' < w.length → ∃ i, (ofK (Parameters.gpow a) * gen ^ m).limb 0 * Parameters.gpow off' = Parameters.gpow i ∧
          (RegionL Lin i ∨ RegionL (bufL b (gkrSizes μ) (gkrOwnT CM.hm T μ cv (ofK (Parameters.gpow c)) (ofK (Parameters.gpow (gP μ b))))) i) :=
        fun a w m off' hm ho' => by
        obtain ⟨i, hi, hr⟩ := gk_region hm ho'
        exact ⟨i, by rw [addr_gen, Nat.add_assoc, hi], Or.inr hr⟩
      have Lbuf0 : ∀ (a : ℕ) (w : List E) (off' : ℕ),
          (a, w) ∈ bufL b (gkrSizes μ) (gkrOwnT CM.hm T μ cv (ofK (Parameters.gpow c)) (ofK (Parameters.gpow (gP μ b)))) →
          off' < w.length → ∃ i, (ofK (Parameters.gpow a)).limb 0 * Parameters.gpow off' = Parameters.gpow i ∧
          (RegionL Lin i ∨ RegionL (bufL b (gkrSizes μ) (gkrOwnT CM.hm T μ cv (ofK (Parameters.gpow c)) (ofK (Parameters.gpow (gP μ b))))) i) :=
        fun a w off' hm ho' => by
        obtain ⟨i, hi, hr⟩ := gk_region hm ho'
        exact ⟨i, by rw [addr_k, hi], Or.inr hr⟩
      have e297 : ofK (Parameters.gpow b) * (((gen ^ μ * gen ^ μ) * (gen ^ μ * gen ^ μ)) * ((gen ^ μ * gen ^ μ) * (gen ^ μ * gen ^ μ))) =
          ofK (Parameters.gpow b) * gen ^ (8 * μ) := by
        simp only [← pow_add]; congr 2; ring
      rcases Nat.mod_two_eq_zero_or_one μ with hs | hs
      · simp only [vbgLoadT, hs, decide_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          (dsimp only at hp hlo hhi ⊢; subst hp)
        · exact L2 hhi
        · exact Lbuf0 _ _ _ mem_layT (by rw [hlay]; omega)
        · exact Lbuf0 _ _ _ mem_pbT (by simp [vbgPb]; omega)
        · exact Lbuf0 _ _ _ mem_dsT (by simp [vbgDs]; omega)
        · exact Lbuf _ _ μ off mem_dsT (by simp [vbgDs]; omega)
        · exact Lbuf _ _ μ off mem_pbT (by simp [vbgPb]; omega)
        · exact Lbuf _ _ μ off mem_pbT (by simp [vbgPb]; omega)
        · show ∃ i, (ofK (Parameters.gpow b) * (((gen ^ μ * gen ^ μ) * (gen ^ μ * gen ^ μ)) *
            ((gen ^ μ * gen ^ μ) * (gen ^ μ * gen ^ μ)))).limb 0 * Parameters.gpow off = Parameters.gpow i ∧ _
          rw [e297]; exact Lbuf _ _ (8 * μ) off mem_layT (by rw [hlay]; omega)
      · simp only [vbgLoadT, hs, show ¬ (1 = 0) from by omega, decide_false, Bool.false_eq_true, ↓reduceIte,
          List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          (dsimp only at hp hlo hhi ⊢; subst hp)
        · exact L2 hhi
        · exact Lbuf0 _ _ _ mem_layT (by rw [hlay]; omega)
        · exact Lbuf0 _ _ _ mem_pbT (by simp [vbgPb]; omega)
        · exact Lbuf0 _ _ _ mem_dsT (by simp [vbgDs]; omega)
        · exact Lbuf _ _ μ off mem_dsT (by simp [vbgDs]; omega)
        · exact L144 hs hhi
        · show ∃ i, (ofK (Parameters.gpow (gP μ b)) * word 1099511627776 0 0).limb 0 * Parameters.gpow off = Parameters.gpow i ∧ _
          rw [word_g40]; exact Lbuf _ _ 40 off mem_ptsT (by rw [hpts]; omega)
        · exact Lbuf _ _ μ off mem_pbT (by simp [vbgPb]; omega)
        · exact Lbuf _ _ μ off mem_pbT (by simp [vbgPb]; omega)
        · show ∃ i, (ofK (Parameters.gpow b) * (((gen ^ μ * gen ^ μ) * (gen ^ μ * gen ^ μ)) *
            ((gen ^ μ * gen ^ μ) * (gen ^ μ * gen ^ μ)))).limb 0 * Parameters.gpow off = Parameters.gpow i ∧ _
          rw [e297]; exact Lbuf _ _ (8 * μ) off mem_layT (by rw [hlay]; omega)
  · intro fp
    simp only [kidsBound, gkrKidsT, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vtcGkrKB]
    split_ifs <;> (try simp (config := { decide := true }) only [vtcGkrBd, ↓reduceIte]) <;> omega
  · intro fp θ
    simp only [Main.kidsBoundW, gkrKidsT, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vtcGkrKB]
    split_ifs <;> (try simp (config := { decide := true }) only [vtcGkrBd, ↓reduceIte]) <;> omega
  · simp only [gkrSizes, List.sum_cons, List.sum_nil, vtcGkrBound]
    omega


/-- **The deployed `verify_bus_gkr_completeAtW`**, from the model's at `CompModel.deployed`. -/
theorem verify_bus_gkr_completeAtW_of_comp (fs : String → ℕ) (cert : String → V → ℕ) {Θ : Type}
    (w : Θ → String → ℕ) {κ : ℕ} (hκ : 6 ≤ κ) :
    CompleteGkrAtW fs cert κ w (vtcGkrBound fs) fun θ => vtcGkrBoundW (w θ) :=
  (verify_bus_gkr_completeAtWC CompModel.deployed fs cert w hκ).toDeployed

end
end LeanVM.Guest.B1.VerifySub
