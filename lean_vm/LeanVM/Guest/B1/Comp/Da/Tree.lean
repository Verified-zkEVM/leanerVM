/-
  LeanVM.Guest.B1.Comp.Da.Tree

  `da_levels` over a completeness model: an answered tree in memory makes every level loop hold.
-/

module

public import LeanVM.Guest.B1.Comp.Digest.Common
public import LeanVM.Guest.B1.Da.TreeM

/-!
# Trees over a completeness model

The backward half of `da_levels_iff` over a `CompModel`, from W2's meaning over the model's
answers (`Meaning_da_levelsWith CM.hm k`: the levels of the answered tree `nodeM` in memory,
`TreeAns` every pair answered by its parent): each pair's row is the model's (`pair_comp`, the
dual of `pair_model`), so every level loop's iterations hold (`steps_of_treeMemC`, `lv_step_bwdB`,
`lv_rel_bwdB`), and `da_levels_comp`. At `CompModel.deployed` the deployed backward direction
(`da_levels_of_comp`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.E2E.Complete

@[expose] public section

/-- **One hash of a tree level over a completeness model** (the dual of `pair_model`): the pair's
row checks from the IV to the model's answer. -/
theorem pair_comp (CM : CompModel) {a b d : Digest} (hd : CM.H (digestBytes a ++ digestBytes b) = some d) :
    CM.sem.check ![(digestScalars a).1, (digestScalars a).2, (digestScalars b).1,
      (digestScalars b).2] (digestScalars paramIv).1 (digestScalars paramIv).2 (digestScalars d).1
      (digestScalars d).2 (metadataCell 64 true) := by
  rw [← blockBytes_pair] at hd
  refine CM.check_one (fun r => ?_) hd
  fin_cases r
  exacts [(isCanonical128_digestScalars a).1, (isCanonical128_digestScalars a).2,
    (isCanonical128_digestScalars b).1, (isCanonical128_digestScalars b).2]

/-- One frame of a level loop under any semantics, backward (`lv_step`'s backward half). -/
theorem lv_step_bwdB {S : BlakeSem} {rd : Reader} {k l : ℕ} (hk : k ≤ 10) (hl : l < k)
    (W tree : E) (x : E) (h : LvStepB S rd tree (lvOff k l) (lvOff k (l + 1)) x)
    (hk21 : IsInK (x * gen + W))
    (hnext : x * gen + W ≠ 0 → coreProgram.RelB S rd (lvName k l) (x * gen :: [W, tree]) []) :
    ∃ fn, coreProgram.find? (lvName k l) = some fn ∧
      fn.SemB S (coreProgram.RelB S rd) rd (x :: [W, tree]) [] := by
  refine ⟨_, find_lv k l hk hl, ?_⟩
  have hgw : ∀ m, 1 ≤ m → m ≤ k → word (gw (lvOff k m)) 0 0 = gen ^ lvOff k m := fun m hm1 hm => by
    refine gw_spec ?_ (by
      unfold lvOff; have := Nat.pow_le_pow_right (n := 2) (by norm_num) hk; omega)
    interval_cases k <;> interval_cases m <;> decide
  obtain ⟨c0, c1, c2, c3, o0, o1, hin, hc, hout⟩ := h
  rw [cellsAt_four] at hin
  rw [cellsAt_two] at hout
  rcases Nat.eq_zero_or_pos l with rfl | hl1
  · obtain ⟨l10, l11, l12, l13⟩ := hin
    obtain ⟨l17, l18⟩ := hout
    have h0 : lvOff k 0 = 0 := by simp [lvOff]
    rw [h0, pow_zero, mul_one] at l10 l11 l12 l13
    rw [Nat.zero_add, ← hgw 1 (by omega) (by omega)] at l17 l18
    simp only [↓reduceIte, Fn.SemB, lvBody0, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, iv0_word, iv1_word, md64_word]
    refine ⟨listVal [x, W, tree, x * x, x * x * (x * x), tree * (x * x * (x * x)),
      word (gw (lvOff k 1)) 0 0, tree * word (gw (lvOff k 1)) 0 0, x * x,
      tree * word (gw (lvOff k 1)) 0 0 * (x * x), c0, c1, c2, c3, (digestScalars paramIv).1,
      (digestScalars paramIv).2, metadataCell 64 true, o0, o1, word 2 0 0, x * word 2 0 0,
      x * word 2 0 0 + W, word 2 0 0, x * word 2 0 0], rfl, ?_⟩
    simp only [listVal, List.getD_cons_succ, List.getD_cons_zero, true_and]
    rw [word_gen]
    exact ⟨l10, l11, l12, l13, hc, l17, l18, hk21, hnext, trivial⟩
  · obtain ⟨l12, l13, l14, l15⟩ := hin
    obtain ⟨l19, l20⟩ := hout
    rw [← hgw l (by omega) (by omega)] at l12 l13 l14 l15
    rw [← hgw (l + 1) (by omega) (by omega)] at l19 l20
    simp only [show l ≠ 0 by omega, ↓reduceIte, Fn.SemB, lvBody, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, iv0_word,
      iv1_word, md64_word]
    refine ⟨listVal [x, W, tree, word (gw (lvOff k l)) 0 0, tree * word (gw (lvOff k l)) 0 0,
      x * x, x * x * (x * x), tree * word (gw (lvOff k l)) 0 0 * (x * x * (x * x)),
      word (gw (lvOff k (l + 1))) 0 0, tree * word (gw (lvOff k (l + 1))) 0 0, x * x,
      tree * word (gw (lvOff k (l + 1))) 0 0 * (x * x), c0, c1, c2, c3, (digestScalars paramIv).1,
      (digestScalars paramIv).2, metadataCell 64 true, o0, o1, word 2 0 0, x * word 2 0 0,
      x * word 2 0 0 + W, word 2 0 0, x * word 2 0 0], rfl, ?_⟩
    simp only [listVal, List.getD_cons_succ, List.getD_cons_zero, true_and]
    rw [word_gen]
    exact ⟨l12, l13, l14, l15, hc, l19, l20, hk21, hnext, trivial⟩

/-- **A level loop under any semantics, backward** (`lv_rel`'s backward half). -/
theorem lv_rel_bwdB {S : BlakeSem} {rd : Reader} {k l : ℕ} (hk : k ≤ 10) (hl : l < k) (tree : E)
    (h : ∀ j < 2 ^ (k - l - 1), LvStepB S rd tree (lvOff k l) (lvOff k (l + 1)) (gen ^ j)) :
    coreProgram.RelB S rd (lvName k l) [gen ^ 0, gen ^ 2 ^ (k - l - 1), tree] [] :=
  loopB_bwd (B := fun x => LvStepB S rd tree (lvOff k l) (lvOff k (l + 1)) x)
    (fun x hB hK hn => lv_step_bwdB hk hl _ tree x hB hK hn) Nat.one_le_two_pow rfl
    (fun j _ hj => h j hj)

/-- **The levels, backward, over a completeness model** (`steps_of_treeMem`): an answered tree in
memory makes every loop iteration hold. -/
theorem steps_of_treeMemC {CM : CompModel} {rd : Reader} {tree : E} {k : ℕ} {leaf : ℕ → Digest}
    (hP : ∀ l ≤ k, TreeMemN rd tree k (nodeM CM.hm leaf) l) (hA : TreeAns CM.hm leaf k) :
    ∀ l < k, ∀ j < 2 ^ (k - l - 1),
      LvStepB CM.sem rd tree (lvOff k l) (lvOff k (l + 1)) (gen ^ j) := by
  intro l hl j hj
  have hpow : 2 ^ (k - l) = 2 * 2 ^ (k - l - 1) := by rw [← pow_succ']; congr 1; omega
  obtain ⟨n0, n1⟩ := hP l hl.le (2 * j) (by omega)
  obtain ⟨n2, n3⟩ := hP l hl.le (2 * j + 1) (by omega)
  obtain ⟨s0, s1⟩ := hP (l + 1) hl (j) (by rwa [show k - (l + 1) = k - l - 1 by omega])
  rw [show lvOff k l + 2 * (2 * j) = lvOff k l + 4 * j by ring] at n0 n1
  rw [show lvOff k l + 2 * (2 * j + 1) = lvOff k l + 4 * j + 2 by ring] at n2 n3
  rw [show lvOff k l + 4 * j + 2 + 1 = lvOff k l + 4 * j + 3 by ring] at n3
  refine lvStepB_iff.mpr ⟨_, _, _, _, _, _, n0, n1, n2, n3, ?_, s0, s1⟩
  exact pair_comp CM (hA l hl j hj)

/-- **`da_levels__L{2^k}_L{k}` is complete over a completeness model**: the answered tree of the
leaves in memory gives the relation. -/
theorem da_levels_comp {CM : CompModel} {rd : Reader} (k : ℕ) (hk : k ≤ 10) (args rets : List E)
    (hm : Meaning_da_levelsWith CM.hm k rd args rets) :
    coreProgram.RelB CM.sem rd (dlNames.getD k "") args rets := by
  rw [relB_of_find (find_dl k hk)]
  have hnr : ∀ l, Stmt.noRetList (dlBlk k l) = true := fun l => by
    simp [dlBlk, Stmt.noRetList, Stmt.noRet]
  simp only [Fn.SemB, dlBody, holdsListB_flatMap k (dlBlk k) hnr]
  simp only [dlBlk, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, and_true, List.map_cons,
    List.map_nil]
  obtain ⟨tree, r0, r1, rfl, rfl, h⟩ := hm
  have e := dlVals_blk k tree r0 r1
  obtain ⟨e1, e2⟩ := dlVals_end k tree r0 r1
  refine ⟨fun v => dlVals k tree r0 r1 v.idx, rfl, fun l hl => ?_, ?_, ?_, ?_⟩
  · dsimp only
    rw [show 1 + 5 * l = 1 + 5 * l + 0 by rfl, e l 0 hl (by omega),
      show 2 + 5 * l = 1 + 5 * l + 1 by omega, e l 1 hl (by omega),
      show 3 + 5 * l = 1 + 5 * l + 2 by omega, e l 2 hl (by omega),
      show 4 + 5 * l = 1 + 5 * l + 3 by omega, e l 3 hl (by omega),
      show 5 + 5 * l = 1 + 5 * l + 4 by omega, e l 4 hl (by omega)]
    simp only [List.getD_cons_succ, List.getD_cons_zero, true_and]
    rw [word_one, gw_end hk hl]
    refine ⟨by rw [gen_pow_eq_ofK, ← ofK_one, ← ofK_add]; exact ofK_isInK _, fun _ => ?_⟩
    rw [← pow_zero gen]
    rcases h with ⟨rfl, -⟩ | ⟨-, leaf, hP, hA, -⟩
    · omega
    · exact lv_rel_bwdB hk hl _
        (steps_of_treeMemC (fun l hl => treeMemN_iff.mpr (hP l hl)) hA l hl)
  · show LoadHolds rd tree (4 * 2 ^ k - 4) (dlVals k tree r0 r1 (1 + 5 * k))
    rw [e1]
    rcases h with ⟨rfl, hc⟩ | ⟨-, leaf, hP, -, hr⟩
    · exact (cellsAt_two.mp hc).1
    · obtain ⟨n0, -⟩ := treeMemN_iff.mpr (hP k le_rfl) 0 (by simp)
      rw [show lvOff k k + 2 * 0 = 4 * 2 ^ k - 4 by simp [lvOff]] at n0
      rw [show r0 = (digestScalars (nodeM CM.hm leaf k 0)).1 from congrArg Prod.fst hr]
      exact n0
  · show LoadHolds rd tree (4 * 2 ^ k - 3) (dlVals k tree r0 r1 (2 + 5 * k))
    rw [e2]
    rcases h with ⟨rfl, hc⟩ | ⟨-, leaf, hP, -, hr⟩
    · exact (cellsAt_two.mp hc).2
    · obtain ⟨-, n1⟩ := treeMemN_iff.mpr (hP k le_rfl) 0 (by simp)
      rw [show lvOff k k + 2 * 0 + 1 = 4 * 2 ^ k - 3 by
        simp [lvOff]; have := Nat.one_le_two_pow (n := k); omega] at n1
      rw [show r1 = (digestScalars (nodeM CM.hm leaf k 0)).2 from congrArg Prod.snd hr]
      exact n1
  · show [dlVals k tree r0 r1 (1 + 5 * k), dlVals k tree r0 r1 (2 + 5 * k)] = _
    rw [e1, e2]

/-! ## At the deployed model -/

theorem pairM_deployed (a b : Digest) : pairM CompModel.deployed.hm a b = hashPair a b := rfl

theorem nodeM_deployed (leaf : ℕ → Digest) : ∀ l i,
    nodeM CompModel.deployed.hm leaf l i = nodeD leaf l i := fun l i =>
  (nodeD_eq_nodeH leaf l i).symm

theorem treeAns_deployed (leaf : ℕ → Digest) (k : ℕ) : TreeAns CompModel.deployed.hm leaf k :=
  fun l _ i _ => by
    show some (hashPair _ _) = some _
    rw [nodeM_deployed, nodeM_deployed, nodeM_deployed]
    rfl

theorem meaning_da_levelsWith_of_deployed {rd : Reader} {k : ℕ} {args rets : List E}
    (h : Meaning_da_levels k rd args rets) : Meaning_da_levelsWith CompModel.deployed.hm k rd args rets := by
  obtain ⟨tree, r0, r1, ha, hr, h⟩ := h
  refine ⟨tree, r0, r1, ha, hr, ?_⟩
  rcases h with h | ⟨hk, leaf, hP, hroot⟩
  · exact Or.inl h
  · refine Or.inr ⟨hk, leaf, fun l hl i hi => ?_, treeAns_deployed leaf k, ?_⟩
    · rw [nodeM_deployed]; exact hP l hl i hi
    · rw [nodeM_deployed]; exact hroot

theorem da_levels_of_comp {rd : Reader} (k : ℕ) (hk : k ≤ 10) (args rets : List E)
    (h : Meaning_da_levels k rd args rets) :
    coreProgram.Rel rd (dlNames.getD k "") args rets := by
  rw [← relB_deployed]
  exact da_levels_comp (CM := CompModel.deployed) k hk args rets
    (meaning_da_levelsWith_of_deployed h)

end
end LeanVM.Guest.B1.Digest
