/-
  LeanVM.Guest.B1.Da.VectorM

  `da_vector_cell` and `da_vector_dispatch` under any semantics of `BLAKE2S`: the rows a column's
  part of the vector hash checked, from the state handed to it.
-/

module

public import LeanVM.Guest.B1.Da.Column
public import LeanVM.Guest.B1.Digest.CommonM

/-!
# The vector hash's columns over any semantics

`da_vector_cell__L{final}` continues the vector hash from the state `(h0, h1)` it is handed over
its 96 blocks (`Vector.lean`). Under a semantics `S` it states the rows it checked
(`Meaning_da_vector_cellB`, over `ChainSteps S`, pattern C); `da_verify` knows the state is a
prefix and extends it. `da_vector_dispatch` selects the specialization (`Meaning_da_vector_dispatchB`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- **`da_vector_cell__L{final}(xb, h0, h1, counters)` under `S`**: some 256 weights, the four
counter words at `counters·xb³`, the rows chained from `(h0, h1)` over the weights' 96 blocks
ending in `(o0, o1)`, and `wp` the weights' frame address. -/
def Meaning_da_vector_cellB (S : BlakeSem) (final : Bool) (rd : Reader) (args rets : List E) :
    Prop :=
  ∃ xb h0 h1 ctr o0 o1 wp, args = [xb, h0, h1, ctr] ∧ rets = [o0, o1, wp] ∧
    ∃ ws cv : List E, ws.length = 256 ∧ cv.length = 4 ∧ CellsAt rd (ctr * (xb * xb * xb)) cv ∧
      ChainSteps S (h0, h1) (vxBlocks (ws.getD · 0)) (vxMd final (cv.getD · 0)) 96 (o0, o1) ∧
      FrameRun rd wp ws

section
variable {S : BlakeSem}

/-- The facts of block `j` of `da_vector_cell`'s chain under `S` (`vxBlk_fwd`). -/
theorem vxBlkB_fwd {rd : Reader} {σ : Val} {final : Bool} {j : ℕ}
    (h : ∀ a ∈ vxBlk final j, a.HoldsB S rd σ) :
    S.check ![σ (.n (vxQ (4 * j))), σ (.n (vxQ (4 * j + 1))), σ (.n (vxQ (4 * j + 2))),
        σ (.n (vxQ (4 * j + 3)))] (σ (.n (vxSt final j))) (σ (.n (vxSt final j + 1)))
        (σ (.n (vxSt final (j + 1)))) (σ (.n (vxSt final (j + 1) + 1))) (σ (.n (vxMdI final j))) ∧
      (j % 32 ≠ 31 → σ (.n (vxMdI final j)) = σ (.n (vxBase (j / 32))) + word (64 * (j % 32 + 1)) 0 0) ∧
      (j % 32 = 31 → ¬(final = true ∧ j = 95) → vxMdI final j = vxEnd (j / 32)) ∧
      (final = true ∧ j = 95 → σ (.n (vxMdI final j)) = σ (.n 3733) + mdF) := by
  by_cases h1 : j % 32 = 31
  · have hm : vxMdI final j = if final = true ∧ j = 95 then 3859 else vxEnd (j / 32) := by
      unfold vxMdI; rw [ite_pos' h1]
    by_cases h2 : final = true ∧ j = 95
    · rw [vxBlk, ite_pos' h1, ite_pos' h2] at h
      simp only [List.cons_append, List.nil_append, List.forall_mem_cons, Atom.HoldsB,
        forall_mem_nil_iff, and_true] at h
      obtain ⟨c, a, b⟩ := h
      exact ⟨b, fun h' => absurd h1 h', fun _ h' => absurd h2 h',
        fun _ => by rw [hm, ite_pos' h2, a, c]⟩
    · rw [vxBlk, ite_pos' h1, ite_neg' h2] at h
      simp only [List.nil_append, List.forall_mem_cons, Atom.HoldsB, forall_mem_nil_iff,
        and_true] at h
      exact ⟨h, fun h' => absurd h1 h', fun _ _ => by rw [hm, ite_neg' h2],
        fun h' => absurd h' h2⟩
  · rw [vxBlk, ite_neg' h1] at h
    simp only [List.forall_mem_cons, Atom.HoldsB, forall_mem_nil_iff, and_true] at h
    obtain ⟨c, a, b⟩ := h
    have hm : vxMdI final j = vxK (j / 32) + 4 * (j % 32) + 1 := by
      unfold vxMdI; rw [ite_neg' h1]
    refine ⟨b, fun _ => by rw [hm, a, c], fun h' => absurd h' h1, fun h' => absurd (by omega) h1⟩

/-- **`da_vector_cell__L{final}`'s outcome under `S`, its weights named** `ws` (`VecOut`). -/
def VecOutB (S : BlakeSem) (final : Bool) (rd : Reader) (args rets : List E) (ws : List E) :
    Prop :=
  ∃ xb h0 h1 ctr o0 o1 wp, args = [xb, h0, h1, ctr] ∧ rets = [o0, o1, wp] ∧ ws.length = 256 ∧
    ∃ cv : List E, cv.length = 4 ∧ CellsAt rd (ctr * (xb * xb * xb)) cv ∧
      ChainSteps S (h0, h1) (vxBlocks (ws.getD · 0)) (vxMd final (cv.getD · 0)) 96 (o0, o1) ∧
      FrameRun rd wp ws

/-- The outcome with its weights named gives the meaning. -/
theorem meaning_of_vecOutB {final : Bool} {rd : Reader} {args rets ws : List E}
    (h : VecOutB S final rd args rets ws) : Meaning_da_vector_cellB S final rd args rets := by
  obtain ⟨xb, h0, h1, ctr, o0, o1, wp, ha, hr, hl, cv, hcl, hcv, hch, hfr⟩ := h
  exact ⟨xb, h0, h1, ctr, o0, o1, wp, ha, hr, ws, cv, hl, hcl, hcv, hch, hfr⟩

set_option maxRecDepth 10000 in
/-- **`da_vector_cell__L{final}` on a valuation of its body, under `S`, its witness named**: the
outcome holds of the weights the valuation hints (`vxWs`). -/
theorem da_vector_cell_outB {final : Bool} {C : CallRel} {rd : Reader} {σ : Val}
    {args rets : List E} (hp : ([.n 0, .n 1, .n 2, .n 3] : List V).map σ = args)
    (hb : Stmt.HoldsListB S C rd σ (vxBody final) False (fun rs => rs = rets)) :
    VecOutB S final rd args rets (vxWs σ) := by
  simp only [vxBody, vxAtoms, holdsListB_atoms, holdsListB_ret, List.forall_mem_append,
    forall_mem_flatMap_range, List.forall_mem_cons, Atom.HoldsB, forall_mem_nil_iff, and_true,
    true_and, List.map_cons, List.map_nil] at hb hp
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hP, c60, c61⟩, hpre0⟩, hb0⟩, hpre1⟩, hb1⟩, hpre2⟩, hb2⟩, ⟨hfk, hfr⟩, o1, o2, o3⟩,
    hr⟩ := hb
  have hP : ∀ p < 128, ∀ a ∈ vxPair p, a.Holds rd σ := fun p hp =>
    (forall_holdsB_noBlake (by simp [vxPair, atomNoBlake])).mp (hP p hp)
  let wsf : ℕ → E := fun k => σ (.n (k + 4))
  let cvl : List E := [σ (.n 3465), σ (.n 3469), σ (.n 3601), σ (.n 3733)]
  have hB : ∀ j < 96, ∀ a ∈ vxBlk final j, a.HoldsB S rd σ := by
    intro j hj
    rcases (show j < 32 ∨ (32 ≤ j ∧ j < 64) ∨ 64 ≤ j by omega) with h | ⟨h1, h2⟩ | h
    · exact hb0 j h
    · have := hb1 (j - 32) (by omega); rwa [show 32 + (j - 32) = j by omega] at this
    · have := hb2 (j - 64) (by omega); rwa [show 64 + (j - 64) = j by omega] at this
  have hcell : ∀ q < 384, σ (.n (vxQ q)) = vxCell wsf q := fun q hq => by
    have := vxCell_of_pair (σ := σ) (p := q / 3) (vxPair_fwd (hP (q / 3) (by omega)))
      (q % 3) (by omega)
    rwa [show 3 * (q / 3) + q % 3 = q by omega] at this
  -- the counter words
  simp only [vxPre0, List.forall_mem_cons, forall_mem_nil_iff, and_true] at hpre0
  obtain ⟨m62, m63, m64, l65, m66, m67, m68, l69⟩ := hpre0
  simp only [vxPre, vxK, List.forall_mem_cons, forall_mem_nil_iff, and_true,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reducePow] at hpre1 hpre2
  obtain ⟨n1, n2, n3, n4, n5, l1⟩ := hpre1
  obtain ⟨q1, q2, q3, q4, q5, l2⟩ := hpre2
  have hcv : CellsAt rd (σ (.n 3) * (σ (.n 0) * σ (.n 0) * σ (.n 0))) cvl := by
    intro k hk
    simp only [cvl, List.length_cons, List.length_nil] at hk
    interval_cases k
    · rw [m64, m63, m62] at l65; exact l65
    · rw [m68, m67, m66] at l69; exact l69
    · rw [n5, n4, n3, n2, n1, word_gen, ← pow_one gen, ← mul_assoc, loadHolds_mul_gen_pow] at l1
      exact l1
    · rw [q5, q4, q3, q2, q1, word4, ← mul_assoc, loadHolds_mul_gen_pow] at l2
      exact l2
  -- the chain
  have hbase : ∀ w < 3, σ (.n (vxBase w)) = cvl.getD w 0 := fun w hw => by
    interval_cases w <;> rfl
  have hend : ∀ w < 3, σ (.n (vxEnd w)) = cvl.getD (w + 1) 0 := fun w hw => by
    interval_cases w <;> rfl
  have hch := chainSteps_of_steps (S := S) (n := 96)
    (st := fun i => (σ (.n (vxSt final i)), σ (.n (vxSt final i + 1))))
    (blocks := fun j => ![σ (.n (vxQ (4 * j))), σ (.n (vxQ (4 * j + 1))), σ (.n (vxQ (4 * j + 2))),
      σ (.n (vxQ (4 * j + 3)))]) (md := fun j => σ (.n (vxMdI final j)))
    (fun j hj => (vxBlkB_fwd (hB j hj)).1)
  rw [chainSteps_congr (b' := vxBlocks (((List.range 256).map wsf).getD · 0))
    (md' := vxMd final (cvl.getD · 0))
    (fun j hj => by
      rw [← vxBlocks_congr (fun k hk => (getD_map_range wsf hk).symm) hj]
      simp only [vxBlocks]
      rw [hcell (4 * j) (by omega), hcell (4 * j + 1) (by omega), hcell (4 * j + 2) (by omega),
        hcell (4 * j + 3) (by omega)])
    (fun j hj => by
      obtain ⟨-, e1, e2, e3⟩ := vxBlkB_fwd (hB j hj)
      unfold vxMd
      by_cases h1 : j % 32 = 31
      · rw [ite_pos' h1]
        by_cases h2 : final = true ∧ j = 95
        · rw [ite_pos' h2, e3 h2]; rfl
        · rw [ite_neg' h2]; show σ (.n (vxMdI final j)) = _
          rw [e2 h1 h2, hend (j / 32) (by omega)]
      · rw [ite_neg' h1, e1 h1, hbase (j / 32) (by omega)])] at hch
  have hs0 : vxSt final 0 = 3460 := rfl
  simp only [hs0] at hch
  rw [c60, c61] at hch
  have hws : vxWs σ = (List.range 256).map wsf := rfl
  rw [hws]
  refine ⟨σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n (vxSt final 96)),
    σ (.n (vxSt final 96 + 1)), σ (.n (vxF final)), hp.symm, ?_, by simp, cvl,
    rfl, hcv, hch, hfk, fun k hk v hv => ?_⟩
  · rw [← hr, o1, o2, o3]
  · simp only [List.length_map, List.length_range] at hk
    rw [hfr k (by simpa using hk) v hv, getD_map_range wsf hk]
    simp only [List.getElem_map, List.getElem_range]
    rfl

/-- **`da_vector_cell__L{final}` is sound under any semantics.** -/
theorem da_vector_cell_B {final : Bool} {rd : Reader} {args rets : List E}
    (h : coreProgram.RelB S rd (vxName final) args rets) :
    Meaning_da_vector_cellB S final rd args rets := by
  rw [relB_of_find (find_vx final)] at h
  obtain ⟨σ, hp, hb⟩ := h
  exact meaning_of_vecOutB (da_vector_cell_outB hp hb)

/-- **`da_vector_dispatch(xb, h0, h1, counters)` under `S`**: `xb` is in `K`, and the vector cell
runs, final exactly at `xb = g^127`. -/
def Meaning_da_vector_dispatchB (S : BlakeSem) (rd : Reader) (args rets : List E) : Prop :=
  ∃ xb rest, args = xb :: rest ∧ IsInK xb ∧
    Meaning_da_vector_cellB S (decide (xb = gen ^ 127)) rd args rets

/-- **`da_vector_dispatch` is sound under any semantics.** -/
theorem da_vector_dispatch_B {rd : Reader} {args rets : List E}
    (h : coreProgram.RelB S rd "da_vector_dispatch" args rets) :
    Meaning_da_vector_dispatchB S rd args rets := by
  rw [relB_of_find find_vd] at h
  simp only [Fn.SemB, vdBody, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons,
    List.map_nil] at h
  have hk := isInK_gen_pow 127
  obtain ⟨σ, rfl, c4, a5, hk5, hz, hnz⟩ := h
  rw [a5, c4, word_g127] at hk5 hz hnz
  have hx : IsInK (σ (.n 0)) := by
    rw [add_comm] at hk5; exact (isInK_add_left hk).mp hk5
  refine ⟨σ (.n 0), [σ (.n 1), σ (.n 2), σ (.n 3)], rfl, hx, ?_⟩
  by_cases h : σ (.n 0) = gen ^ 127
  · obtain ⟨hc, c9, c10, c11, c15, c16, c17, hr⟩ := hz (e_add_eq_zero_iff.mpr h)
    rw [decide_eq_true h, ← hr, c15, c16, c17, c9, c10, c11]
    exact da_vector_cell_B (final := true) hc
  · obtain ⟨hc, c9, c10, c11, c15, c16, c17, hr⟩ := hnz (fun h' => h (e_add_eq_zero_iff.mp h'))
    rw [decide_eq_false h, ← hr, c15, c16, c17, c9, c10, c11]
    exact da_vector_cell_B (final := false) hc

end

end
end LeanVM.Guest.B1.Digest
