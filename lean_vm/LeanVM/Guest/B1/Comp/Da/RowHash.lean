/-
  LeanVM.Guest.B1.Comp.Da.RowHash

  `__loop93`, the row digests, over a completeness model.
-/

module

public import LeanVM.Guest.B1.Comp.Digest.Common
public import LeanVM.Guest.B1.Da.VerifyM

/-!
# The row digests over a completeness model

The backward half of `l93_step` over a `CompModel`, from W2's step over the model's answers
(`L93StepM CM.hm`: the row's 128 cells, the answer for their bytes stored at the row tree's leaf):
the 32 blocks check through the model's chain of the cells' bytes (`blocksOf_bytes`,
`CompModel.chain_checks_blocks`). `rh_bwdB` (the atoms under any semantics from their rows),
`l93_step_bwdC`, and the loop `l93_rel_bwdC`.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.E2E.Complete

@[expose] public section

/-- `__loop93`'s atoms under any semantics, from their rows (`rh_bwd`). -/
theorem rh_bwdB {S : BlakeSem} {rd : Reader} {x W pb rt P : E} {cs : List E} {st : ℕ → E × E}
    (hlen : cs.length = 128) (hP : LoadHolds rd (pb * x) 0 P) (hcells : CellsAt rd P cs)
    (e0 : st 0 = digestScalars paramIv)
    (hc : ∀ j < 32, S.check (blocksOf cs j) (st j).1 (st j).2 (st (j + 1)).1 (st (j + 1)).2 (rhMd j))
    (hout : CellsAt rd (rt * (x * x)) [(st 32).1, (st 32).2]) :
    ∀ a ∈ rhAtoms, a.HoldsB S rd (fun v => rhVals x W pb rt P cs st v.idx) := by
  have hl : ∀ k < 128, LoadHolds rd P k (cs.getD k 0) := fun k hk => by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact hcells k (by omega)
  obtain ⟨o0, o1⟩ := cellsAt_two.mp hout
  simp only [rhAtoms, List.forall_mem_append, forall_mem_flatMap_range, List.forall_mem_cons,
    Atom.HoldsB, forall_mem_nil_iff, and_true]
  refine ⟨⟨⟨rfl, hP, hl 0 (by omega), hl 1 (by omega), hl 2 (by omega), hl 3 (by omega), ?_, ?_,
    rfl, ?_⟩, fun i hi => rhBlkB_iff.mpr ?_⟩, rfl, rfl, o0, o1, word_gen.symm, rfl, rfl,
    word_gen.symm, rfl⟩
  · show (st 0).1 = _; rw [e0, iv0_word]
  · show (st 0).2 = _; rw [e0, iv1_word]
  · exact hc 0 (by omega)
  · have v : ∀ r < 7, rhVals x W pb rt P cs st (7 * (i + 1) + 8 + r) = _ := fun r hr =>
      rhVals_blk x W pb rt P cs st (b := i + 1) (by omega) (by omega) hr
    have m : rhVals x W pb rt P cs st (7 * (i + 1) + 12) = rhMd (i + 1) := v 4 (by omega)
    have s0 := rhVals_st x W pb rt P cs st (b := i + 1) (by omega) (by omega)
    have s1 := rhVals_st x W pb rt P cs st (b := i + 1 + 1) (by omega) (by omega)
    have v0 : rhVals x W pb rt P cs st (7 * (i + 1) + 8 + 0) = cs.getD (4 * (i + 1)) 0 :=
      v 0 (by omega)
    have v1 : rhVals x W pb rt P cs st (7 * (i + 1) + 8 + 1) = cs.getD (4 * (i + 1) + 1) 0 :=
      v 1 (by omega)
    have v2 : rhVals x W pb rt P cs st (7 * (i + 1) + 8 + 2) = cs.getD (4 * (i + 1) + 2) 0 :=
      v 2 (by omega)
    have v3 : rhVals x W pb rt P cs st (7 * (i + 1) + 8 + 3) = cs.getD (4 * (i + 1) + 3) 0 :=
      v 3 (by omega)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [v0]; exact hl _ (by omega)
    · rw [v1]; exact hl _ (by omega)
    · rw [v2]; exact hl _ (by omega)
    · rw [v3]; exact hl _ (by omega)
    · rw [m, rhMd_word]
    · rw [v0, v1, v2, v3, m, s0.1, s0.2, s1.1, s1.2]
      exact hc (i + 1) (by omega)

/-- **One row digest over a completeness model** (`l93_step`'s backward half). -/
theorem l93_step_bwdC {CM : CompModel} (rd : Reader) (W pb rt x : E)
    (h : L93StepM CM.hm rd pb rt x) (hk : IsInK (x * gen + W))
    (hnext : x * gen + W ≠ 0 →
      coreProgram.RelB CM.sem rd "__loop93" (x * gen :: [W, pb, rt]) []) :
    ∃ fn, coreProgram.find? "__loop93" = some fn ∧
      fn.SemB CM.sem (coreProgram.RelB CM.sem rd) rd (x :: [W, pb, rt]) [] := by
  refine ⟨_, find_l93, ?_⟩
  simp only [Fn.SemB, rhBody, holdsListB_atoms, Stmt.HoldsListB, Stmt.HoldsB, List.map_cons,
    List.map_nil]
  obtain ⟨P, cs, hP, hlen, hcells, hcan, c0, c1, hout, d, hd, hcd⟩ := h
  have hg : ∀ k < 128, IsCanonical128 (cs.getD k 0) := fun k hk => by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact hcan _ (List.getElem_mem _)
  have hcanb : ∀ j < 32, ∀ r, IsCanonical128 (blocksOf cs j r) := fun j hj r => by
    fin_cases r
    exacts [hg (4 * j) (by omega), hg (4 * j + 1) (by omega), hg (4 * j + 2) (by omega),
      hg (4 * j + 3) (by omega)]
  have hH : CM.H ((List.range (31 + 1)).flatMap fun j => blockBytes (blocksOf cs j)) = some d := by
    rw [blocksOf_bytes cs 32 (by omega)]; exact hd
  have hchk := CM.chain_checks_blocks (md := rhMd) hH (fun j hj r => hcanb j (by omega) r)
    (fun j hj => by unfold rhMd; congr 1; simp only [decide_eq_false_iff_not]; omega) rfl
  set X := (List.range (31 + 1)).flatMap fun j => blockBytes (blocksOf cs j) with hX
  have hlenX : X.length = 64 * 32 := by rw [hX, CompModel.length_flatMap_blocks]
  have h32 : CM.chainSt X d 32 = (c0, c1) := by
    rw [hcd]; exact CM.chainSt_succ_of d (n := 31) (by rw [hlenX])
  refine ⟨fun v => rhVals x W pb rt P cs (CM.chainSt X d) v.idx, rfl,
    rh_bwdB hlen hP hcells (CM.chainSt_zero X d) (fun j hj => hchk j (by omega)) (by rw [h32]; exact hout),
    hk, hnext, trivial⟩

/-- **The row digests' loop over a completeness model** (`l93_iff`'s backward half). -/
theorem l93_rel_bwdC {CM : CompModel} (rd : Reader) (W pb rt : E) {k m : ℕ} (hkm : k < m)
    (hW : W = gen ^ m) (hall : ∀ j, k ≤ j → j < m → L93StepM CM.hm rd pb rt (gen ^ j)) :
    coreProgram.RelB CM.sem rd "__loop93" (gen ^ k :: [W, pb, rt]) [] :=
  loopB_bwd (B := fun x => L93StepM CM.hm rd pb rt x)
    (fun x hB hK hn => l93_step_bwdC rd W pb rt x hB hK hn) hkm hW hall

end
end LeanVM.Guest.B1.Digest
