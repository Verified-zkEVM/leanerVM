/-
  LeanVM.Guest.B1.Comp.Da.Vector

  `da_vector_cell` and `da_vector_dispatch` complete under any semantics: the rows chained from
  the state handed to them hold, so the relation does.
-/

module

public import LeanVM.Guest.B1.Comp.Basic
public import LeanVM.Guest.B1.Da.VectorM

/-!
# The vector hash's cells, backward, under any semantics

`da_vector_cell__L{final}` runs 96 blocks of the vector's chunk from the state handed to it (a
window, pattern C). Its backward half holds under every semantics, from W2's rows
(`Meaning_da_vector_cellB S`, over `ChainSteps S`): the deployed honest run is over an abstract
chain of states already (`vx_core_holds`), and only its rows change (`vxBlkB_bwd`,
`vx_core_holdsB`). `da_vector_cell_compB`, `da_vector_dispatch_compB`; at `blakeDeployed` the
deployed backward directions (`da_vector_cell_of_compB`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

section
variable {S : BlakeSem}

theorem vxBlkB_bwd {rd : Reader} {σ : Val} {final : Bool} {j : ℕ} {m : Fin 4 → E}
    {s0 s1 o0 o1 d : E}
    (hq : ![σ (.n (vxQ (4 * j))), σ (.n (vxQ (4 * j + 1))), σ (.n (vxQ (4 * j + 2))),
        σ (.n (vxQ (4 * j + 3)))] = m)
    (h0 : σ (.n (vxSt final j)) = s0) (h1 : σ (.n (vxSt final j + 1)) = s1)
    (h2 : σ (.n (vxSt final (j + 1))) = o0) (h3 : σ (.n (vxSt final (j + 1) + 1)) = o1)
    (hmd : σ (.n (vxMdI final j)) = d)
    (hc : j % 32 ≠ 31 → σ (.n (vxK (j / 32) + 4 * (j % 32))) = word (64 * (j % 32 + 1)) 0 0 ∧
      σ (.n (vxK (j / 32) + 4 * (j % 32) + 1)) =
        σ (.n (vxBase (j / 32))) + σ (.n (vxK (j / 32) + 4 * (j % 32))))
    (hf : final = true ∧ j = 95 → σ (.n 3858) = mdF ∧ σ (.n 3859) = σ (.n 3733) + σ (.n 3858))
    (hcomp : S.check m s0 s1 o0 o1 d) :
    ∀ a ∈ vxBlk final j, a.HoldsB S rd σ := by
  have hC : S.check ![σ (.n (vxQ (4 * j))), σ (.n (vxQ (4 * j + 1))), σ (.n (vxQ (4 * j + 2))),
      σ (.n (vxQ (4 * j + 3)))] (σ (.n (vxSt final j))) (σ (.n (vxSt final j + 1)))
      (σ (.n (vxSt final (j + 1)))) (σ (.n (vxSt final (j + 1) + 1))) (σ (.n (vxMdI final j))) := by
    rw [hq, h0, h1, h2, h3, hmd]; exact hcomp
  unfold vxBlk
  split_ifs with g1 g2
  · simp only [List.cons_append, List.nil_append, List.forall_mem_cons, Atom.HoldsB,
      forall_mem_nil_iff, and_true]
    exact ⟨(hf g2).1, (hf g2).2, hC⟩
  · simp only [List.nil_append, List.forall_mem_cons, Atom.HoldsB, forall_mem_nil_iff, and_true]
    exact hC
  · simp only [List.forall_mem_cons, Atom.HoldsB, forall_mem_nil_iff, and_true]
    exact ⟨(hc g1).1, (hc g1).2, hC⟩

/-- **The honest run's atoms hold under any semantics**, over an abstract chain of states whose
rows `S` checks (`vx_core_holds`). -/
theorem vx_core_holdsB {final : Bool} {rd : Reader} {xb h0 h1 ctr o0 o1 wp : E} {wsf cvf : ℕ → E}
    {st : ℕ → E × E}
    (hcv : ∀ k < 4, LoadHolds rd (ctr * (xb * xb * xb)) k (cvf k))
    (hfr : IsInK wp ∧ ∀ k < 256, ∀ v, rd (wp.limb 0 * Parameters.gpow k) = some v → v = wsf k)
    (e0 : st 0 = (h0, h1)) (ho : st 96 = (o0, o1))
    (hcomp : ∀ j < 96, S.check (vxBlocks wsf j) (st j).1 (st j).2 (st (j + 1)).1
      (st (j + 1)).2 (vxMd final cvf j)) :
    let σ : Val := fun v => vxVals final xb h0 h1 ctr wp wsf cvf st (vxMd final cvf) v.idx
    (∀ a ∈ vxAtoms final, a.HoldsB S rd σ) ∧
      [σ (.n (vxF final + 1)), σ (.n (vxF final + 2)), σ (.n (vxF final + 3))] = [o0, o1, wp] ∧
      [Core.V.n 0, .n 1, .n 2, .n 3].map σ = [xb, h0, h1, ctr] := by
  intro σ
  have hσ : ∀ k, σ (.n k) = vxVals final xb h0 h1 ctr wp wsf cvf st (vxMd final cvf) k :=
    fun _ => rfl
  -- the states and metadata words
  have hst : ∀ i ≤ 96, σ (.n (vxSt final i)) = (st i).1 ∧ σ (.n (vxSt final i + 1)) = (st i).2 := by
    intro i hi
    unfold vxSt
    by_cases i0 : i = 0
    · subst i0
      rw [ite_pos' rfl, e0]
      exact ⟨rfl, rfl⟩
    rw [ite_neg' i0]
    by_cases i96 : final = true ∧ i = 96
    · rw [ite_pos' i96]
      obtain ⟨hf, rfl⟩ := i96
      subst hf
      exact ⟨rfl, rfl⟩
    rw [ite_neg' i96]
    by_cases l : (i - 1) % 32 = 31
    · rw [ite_pos' l]
      have hw : (i - 1) / 32 < 3 := by omega
      have hi32 : i = 32 * ((i - 1) / 32) + 32 := by omega
      generalize hw' : (i - 1) / 32 = w at hw hi32 ⊢
      subst hi32
      interval_cases w
      · exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
      · cases final
        · exact ⟨rfl, rfl⟩
        · exact absurd ⟨rfl, rfl⟩ i96
    · rw [ite_neg' l]
      have hw : (i - 1) / 32 < 3 := by omega
      have hb : (i - 1) % 32 < 31 := by omega
      have a := vxVals_bv final xb h0 h1 ctr wp wsf cvf st (vxMd final cvf) (r := 2) hw hb (by omega)
      have b := vxVals_bv final xb h0 h1 ctr wp wsf cvf st (vxMd final cvf) (r := 3) hw hb (by omega)
      have e : 32 * ((i - 1) / 32) + (i - 1) % 32 + 1 = i := by omega
      simp only [vxBv, List.getD_cons_succ, List.getD_cons_zero, e] at a b
      exact ⟨a, b⟩
  have hbase : ∀ w < 3, σ (.n (vxBase w)) = cvf w := fun w hw => by
    interval_cases w <;> rfl
  have hend : ∀ w < 3, σ (.n (vxEnd w)) = cvf (w + 1) := fun w hw => by
    interval_cases w <;> rfl
  have hmd : ∀ j < 96, σ (.n (vxMdI final j)) = vxMd final cvf j := by
    intro j hj
    unfold vxMdI
    by_cases l : j % 32 = 31
    · rw [ite_pos' l]
      by_cases f : final = true ∧ j = 95
      · rw [ite_pos' f]
        obtain ⟨hf, rfl⟩ := f
        subst hf
        rfl
      · rw [ite_neg' f, hend (j / 32) (by omega)]
        unfold vxMd; rw [ite_pos' l, ite_neg' f]
    · rw [ite_neg' l]
      have a := vxVals_bv final xb h0 h1 ctr wp wsf cvf st (vxMd final cvf) (r := 1) (w := j / 32)
        (b := j % 32) (by omega) (by omega) (by omega)
      have e : 32 * (j / 32) + j % 32 = j := by omega
      simp only [vxBv, List.getD_cons_succ, List.getD_cons_zero, e] at a
      exact a
  have hpair : ∀ q < 384, σ (.n (vxQ q)) = vxCell wsf q := by
    intro q hq
    obtain ⟨p, r, hr, rfl⟩ : ∃ p r, r < 3 ∧ q = 3 * p + r := ⟨q / 3, q % 3, by omega, by omega⟩
    have e1 : (3 * p + r) / 3 = p := by omega
    have e2 : (3 * p + r) % 3 = r := by omega
    unfold vxQ vxCell
    rw [e1, e2, hσ, vxVals_pair final xb h0 h1 ctr wp wsf cvf st (vxMd final cvf) (by omega)
      (by omega) (by omega)]
    obtain ⟨p1, p2, p3⟩ := pair_cells (wsf (2 * p)) (wsf (2 * p + 1))
    interval_cases r
    · simpa [pairVals] using p1
    · simpa [pairVals] using p2
    · simpa [pairVals] using p3
  have hblk : ∀ j < 96, ∀ a ∈ vxBlk final j, a.HoldsB S rd σ := by
    intro j hj
    refine vxBlkB_bwd (m := vxBlocks wsf j) ?_ (hst j (by omega)).1 (hst j (by omega)).2
      (hst (j + 1) (by omega)).1 (hst (j + 1) (by omega)).2 (hmd j hj) (fun l => ?_) (fun f => ?_)
      (hcomp j hj)
    · simp only [vxBlocks]
      rw [hpair (4 * j) (by omega), hpair (4 * j + 1) (by omega), hpair (4 * j + 2) (by omega),
        hpair (4 * j + 3) (by omega)]
    · have a := vxVals_bv final xb h0 h1 ctr wp wsf cvf st (vxMd final cvf) (r := 0) (w := j / 32)
        (b := j % 32) (by omega) (by omega) (by omega)
      have a1 := vxVals_bv final xb h0 h1 ctr wp wsf cvf st (vxMd final cvf) (r := 1) (w := j / 32)
        (b := j % 32) (by omega) (by omega) (by omega)
      have e : 32 * (j / 32) + j % 32 = j := by omega
      simp only [vxBv, List.getD_cons_succ, List.getD_cons_zero, e, Nat.add_zero] at a a1
      refine ⟨a, ?_⟩
      rw [hσ, a1, hbase (j / 32) (by omega), hσ, a]
      unfold vxMd; rw [ite_neg' l]
    · obtain ⟨hf, rfl⟩ := f
      subst hf
      exact ⟨rfl, rfl⟩
  -- the counter words' atoms
  have hpre0 : ∀ a ∈ vxPre0, a.HoldsB S rd σ := by
    simp only [vxPre0, List.forall_mem_cons, Atom.HoldsB, forall_mem_nil_iff, and_true]
    exact ⟨rfl, rfl, rfl, hcv 0 (by omega), rfl, rfl, rfl, hcv 1 (by omega)⟩
  have hpre1 : ∀ a ∈ vxPre 1, a.HoldsB S rd σ := by
    simp only [vxPre, vxK, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reducePow,
      List.forall_mem_cons, Atom.HoldsB, forall_mem_nil_iff, and_true]
    have l := (loadHolds_mul_gen_pow (ctr * (xb * xb * xb)) 1 1 (cvf 2)).mpr (hcv 2 (by omega))
    rw [pow_one, ← word_gen, mul_assoc ctr (xb * xb * xb) (word 2 0 0)] at l
    exact ⟨rfl, rfl, rfl, rfl, rfl, l⟩
  have hpre2 : ∀ a ∈ vxPre 2, a.HoldsB S rd σ := by
    simp only [vxPre, vxK, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reducePow,
      List.forall_mem_cons, Atom.HoldsB, forall_mem_nil_iff, and_true]
    have l := (loadHolds_mul_gen_pow (ctr * (xb * xb * xb)) 2 1 (cvf 3)).mpr (hcv 3 (by omega))
    rw [← word4, mul_assoc ctr (xb * xb * xb) (word 4 0 0)] at l
    exact ⟨rfl, rfl, rfl, rfl, rfl, l⟩
  have hF : σ (.n (vxF final + 1)) = σ (.n (vxSt final 96)) ∧
      σ (.n (vxF final + 2)) = σ (.n (vxSt final 96 + 1)) ∧
      σ (.n (vxF final + 3)) = σ (.n (vxF final)) ∧
      σ (.n (vxF final)) = wp ∧ [σ (.n (vxF final + 1)), σ (.n (vxF final + 2)),
        σ (.n (vxF final + 3))] = [o0, o1, wp] := by
    cases final
    · refine ⟨rfl, rfl, rfl, rfl, ?_⟩
      show [(st 96).1, (st 96).2, wp] = _
      rw [ho]
    · refine ⟨rfl, rfl, rfl, rfl, ?_⟩
      show [(st 96).1, (st 96).2, wp] = _
      rw [ho]
  refine ⟨?_, hF.2.2.2.2, rfl⟩
  simp only [vxAtoms, List.forall_mem_append, forall_mem_flatMap_range,
    List.forall_mem_cons, Atom.HoldsB, forall_mem_nil_iff, and_true, true_and]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨fun i hi => ?_, rfl, rfl⟩, hpre0⟩, fun b hb => hblk b (by omega)⟩, hpre1⟩,
    fun b hb => hblk (32 + b) (by omega)⟩, hpre2⟩, fun b hb => hblk (64 + b) (by omega)⟩,
    ⟨?_, fun k hk v hv => ?_⟩, hF.1, hF.2.1, hF.2.2.1⟩
  · exact (forall_holdsB_noBlake (by simp [vxPair, atomNoBlake])).mpr
      (vxPair_bwd (s := wsf (2 * i)) (t := wsf (2 * i + 1))
        (fun r hr hr2 => vxVals_pair final xb h0 h1 ctr wp wsf cvf st (vxMd final cvf) hi hr hr2)
        (vxVals_w final xb h0 h1 ctr wp wsf cvf st (vxMd final cvf) (k := 2 * i) (by omega))
        (vxVals_w final xb h0 h1 ctr wp wsf cvf st (vxMd final cvf) (k := 2 * i + 1) (by omega)))
  · rw [hF.2.2.2.1]; exact hfr.1
  · simp only [List.length_map, List.length_range] at hk
    rw [hF.2.2.2.1] at hv
    simp only [List.getElem_map, List.getElem_range]
    rw [hσ, vxVals_w final xb h0 h1 ctr wp wsf cvf st (vxMd final cvf) hk]
    exact hfr.2 k hk v hv

/-- The honest run under any semantics, over an abstract chain of states (`vx_bwd_core`). -/
theorem vx_bwd_coreB {final : Bool} {rd : Reader} {xb h0 h1 ctr o0 o1 wp : E} {wsf cvf : ℕ → E}
    {st : ℕ → E × E}
    (hcv : ∀ k < 4, LoadHolds rd (ctr * (xb * xb * xb)) k (cvf k))
    (hfr : IsInK wp ∧ ∀ k < 256, ∀ v, rd (wp.limb 0 * Parameters.gpow k) = some v → v = wsf k)
    (e0 : st 0 = (h0, h1)) (ho : st 96 = (o0, o1))
    (hcomp : ∀ j < 96, S.check (vxBlocks wsf j) (st j).1 (st j).2 (st (j + 1)).1
      (st (j + 1)).2 (vxMd final cvf j)) :
    coreProgram.RelB S rd (vxName final) [xb, h0, h1, ctr] [o0, o1, wp] := by
  obtain ⟨ha, hr, hp⟩ := vx_core_holdsB hcv hfr e0 ho hcomp
  rw [relB_of_find (find_vx final)]
  refine ⟨_, hp, ?_⟩
  rw [vxBody, holdsListB_atoms]
  exact ⟨ha, hr⟩

/-- **`da_vector_cell__L{final}` is complete under any semantics**: its rows chained from the
state give the relation. -/
theorem da_vector_cell_compB {final : Bool} {rd : Reader} {args rets : List E}
    (h : Meaning_da_vector_cellB S final rd args rets) :
    coreProgram.RelB S rd (vxName final) args rets := by
  obtain ⟨xb, h0, h1, ctr, o0, o1, wp, rfl, rfl, ws, cv, hwl, hcl, hcv, hch, hfr⟩ := h
  obtain ⟨sts, hst0, hout, hsteps⟩ := hch
  refine vx_bwd_coreB (wsf := (ws.getD · 0)) (cvf := (cv.getD · 0)) (st := sts)
    (fun k hk => ?_) ⟨hfr.1, fun k hk v hv => hfr.2 k (by omega) v hv⟩ hst0 hout hsteps
  have := hcv k (by omega)
  rwa [← List.getD_eq_getElem _ 0] at this

/-- **`da_vector_dispatch` is complete under any semantics.** -/
theorem da_vector_dispatch_compB {rd : Reader} {args rets : List E}
    (h : Meaning_da_vector_dispatchB S rd args rets) :
    coreProgram.RelB S rd "da_vector_dispatch" args rets := by
  rw [relB_of_find find_vd]
  simp only [Fn.SemB, vdBody, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons,
    List.map_nil]
  have hk := isInK_gen_pow 127
  obtain ⟨xb, rest, rfl, hx, hM⟩ := h
  obtain ⟨_, h0, h1, ctr, o0, o1, wp, ha, rfl, -⟩ := id hM
  simp only [List.cons.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  refine ⟨listVal [xb, h0, h1, ctr, word 9223372036854775983 0 0, xb + word 9223372036854775983 0 0,
    o0, o1, wp, o0, o1, wp, o0, o1, wp, o0, o1, wp], rfl, ?_⟩
  simp only [listVal, List.getD_cons_succ, List.getD_cons_zero, word_g127, true_and, and_true]
  refine ⟨(isInK_add_left hx).mpr hk, fun hz => ?_, fun hnz => ?_⟩
  · have h := e_add_eq_zero_iff.mp hz
    rw [decide_eq_true h] at hM
    exact da_vector_cell_compB (final := true) hM
  · have h : xb ≠ gen ^ 127 := fun h => hnz (e_add_eq_zero_iff.mpr h)
    rw [decide_eq_false h] at hM
    exact da_vector_cell_compB (final := false) hM

end

/-! ## At the deployed semantics -/

theorem da_vector_cell_of_compB {final : Bool} {rd : Reader} {args rets : List E}
    (h : Meaning_da_vector_cell final rd args rets) :
    coreProgram.Rel rd (vxName final) args rets := by
  rw [← relB_deployed]
  obtain ⟨xb, h0, h1, ctr, o0, o1, wp, ha, hr, ws, cv, hwl, hcl, hcv, hch, hfr⟩ := h
  have hch' : ChainSteps blakeDeployed (h0, h1) (vxBlocks (ws.getD · 0)) (vxMd final (cv.getD · 0))
      96 (o0, o1) := by
    rcases hch with ⟨h96, -⟩ | ⟨-, hd, hst0, hcan, hout⟩
    · omega
    · exact ⟨fun i => digestScalars (chainRun hd (vxBlocks (ws.getD · 0)) (vxMd final (cv.getD · 0)) i),
        hst0.symm, hout.symm, steps_of_chainCells hcan⟩
  exact da_vector_cell_compB ⟨xb, h0, h1, ctr, o0, o1, wp, ha, hr, ws, cv, hwl, hcl, hcv, hch', hfr⟩

end
end LeanVM.Guest.B1.Digest
