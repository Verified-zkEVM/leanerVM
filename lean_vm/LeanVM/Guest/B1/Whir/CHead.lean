/-
  LeanVM.Guest.B1.Whir.CHead

  The head of open_stacked, honestly.
-/

module

public import LeanVM.Guest.B1.Whir.CLevels

/-!
# The head, honestly

`osHead_complete`: on the first round polynomial's two words `c0`, `c2` at the cursor and the
commitment's root stored at `level_roots`, the head holds at the values `headF` (the words, the
fixed buffers at the pointers `P`), and the levels start from its state.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- The head's values from `9`. -/
def headVals (c : OsCfg) (target : E) (P : OsPtrs) (c0 c2 : E) : List E :=
  [c0, c2, target + c2, gw (4 * c.capLen), P.caps, gw c.capLen, P.flags, gw c.yrLen, P.fmsg,
    gw (2 * c.levels.length), P.roots, gw c.nFolds, P.fch, gw c.levels.length, P.betas,
    gw (c.levels.length * c.maxQ), P.qw, gw c.posLen, P.qpos, gw c.posLen, P.qbp,
    gw (c.levels.length * ligColsCap), P.oodz, gw (c.levels.length * oodSlots), P.ood]

/-- The head's values. -/
def headF (c : OsCfg) (σ : Val) (P : OsPtrs) (c0 c2 : E) : ℕ → E :=
  fun i ↦ (headVals c (σ (.n 5)) P c0 c2).getD (i - 9) 0

/-- **The head, honestly.** -/
theorem osHead_complete {c : OsCfg} (σ : Val) (P : OsPtrs) {c0 c2 : E}
    (h0 : LoadHolds rd (σ (.n 8)) 0 c0) (h2 : LoadHolds rd (σ (.n 8)) 1 c2)
    (hr0 : LoadHolds rd P.roots 0 (σ (.n 6))) (hr1 : LoadHolds rd P.roots 1 (σ (.n 7)))
    (hcan : AllCanonical [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)]) :
    BlkF C rd σ 9 34 (headF c σ P c0 c2) (osHead c).1
      (fun σ' ↦ LvsSt σ' (osHead c).2
        ⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], [(c0, dsObserve), (c2, dsObserve)]⟩
        [c0, σ (.n 5) + c2, c2] (σ (.n 5)) (σ (.n 8) * gen ^ 2) ∧ ptrsOf σ' = P ∧
        AgreeBelow 9 σ σ') := by
  intro σ' hg hr
  have V : ∀ j < 25, σ' (.n (9 + j)) = (headVals c (σ (.n 5)) P c0 c2).getD j 0 :=
    fun j hj ↦ by rw [hr _ (by omega) (by omega)]; simp only [headF, Nat.add_sub_cancel_left]
  have v0 := V 0 (by omega); have v1 := V 1 (by omega); have v2 := V 2 (by omega)
  have v3 := V 3 (by omega); have v4 := V 4 (by omega); have v5 := V 5 (by omega)
  have v6 := V 6 (by omega); have v7 := V 7 (by omega); have v8 := V 8 (by omega)
  have v9 := V 9 (by omega); have v10 := V 10 (by omega); have v11 := V 11 (by omega)
  have v12 := V 12 (by omega); have v13 := V 13 (by omega); have v14 := V 14 (by omega)
  have v15 := V 15 (by omega); have v16 := V 16 (by omega); have v17 := V 17 (by omega)
  have v18 := V 18 (by omega); have v19 := V 19 (by omega); have v20 := V 20 (by omega)
  have v21 := V 21 (by omega); have v22 := V 22 (by omega); have v23 := V 23 (by omega)
  have v24 := V 24 (by omega)
  simp only [headVals, List.getD_cons_zero, List.getD_cons_succ, Nat.reduceAdd, Nat.add_zero]
    at v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24
  have g0 := hg 0 (by omega); have g1 := hg 1 (by omega); have g2 := hg 2 (by omega)
  have g3 := hg 3 (by omega); have g4 := hg 4 (by omega); have g5 := hg 5 (by omega)
  have g6 := hg 6 (by omega); have g7 := hg 7 (by omega); have g8 := hg 8 (by omega)
  refine ⟨?_, ?_, ?_, hg⟩
  · simp only [osHead, osHeap, List.cons_append, List.nil_append, allOk_cons, allOk_nil, and_true,
      StmtOk, Atom.Holds, osCaps, osFlags, osRoots, v0, v1, v2, v3, v5, v7, v9, v10, v11, v13,
      v15, v17, v19, v21, v23, g5, g6, g7, g8, true_and, and_self]
    exact ⟨h0, h2, hr0, hr1⟩
  · refine ⟨?_, ?_, ?_, ?_, rfl, (show 2 ≤ 8 by omega), ⟨?_, show 9 < 34 by omega,
      show 10 < 34 by omega, show 8 < 34 by omega, show 9 < 34 by omega, show 11 < 34 by omega,
      show 10 < 34 by omega, show 5 < 34 by omega⟩, le_rfl, ?_, trivial, fun p hp ↦ by cases hp⟩
    · simp only [OsSt.F, OsSt.fsv, osHead, List.map_cons, List.map_nil, g0, g1, g2, g3, g4, v0, v1]
    · simp only [OsSt.quad, osHead, v0, v1, v2]
    · simp only [osHead, g5]
    · simp only [OsSt.cur, osHead, g8]
    · intro f hf
      simp only [osHead, List.mem_cons, List.not_mem_nil, or_false] at hf
      show f < 34
      omega
    · simp only [OsSt.fsv, osHead, List.map_cons, List.map_nil, g0, g1, g2, g3, g4]; exact hcan
  · cases P
    simp only [ptrsOf, osCaps, osFlags, osFmsg, osRoots, osFch, osBetas, osQw, osQpos, osQbp,
      osOodz, osOod, v4, v6, v8, v10, v12, v14, v16, v18, v20, v22, v24]

end
end LeanVM.Guest.B1.Whir
