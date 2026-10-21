/-
  LeanVM.Guest.B1.Da.TreeM

  `da_levels` under a hash model: a tree whose every node is the answered hash of its children,
  and LeanDA's tree over an answered hash (`treeRootWith`) as its root.
-/

module

public import LeanVM.Guest.B1.Da.Tree
public import LeanVM.Guest.B1.Digest.CommonM
public import LeanVM.Spec.DaWith

/-!
# Trees over a hash model

`Tree.lean`'s tree `nodeD` hashes pairs with BLAKE2s (`hashPair`). Over a `HashModel` a node is
the model's answer to its children's bytes (`pairM`, `nodeM`), and the tree is *answered*
(`TreeAns`): every pair's hash is the answer the parent holds. Then:

* `da_levels_model`: `da_levels`' relation under the model's semantics gives the answered tree of
  the leaves in memory (`Meaning_da_levelsWith`), and `levels_rootM` its root from the leaves;
* `treeRootWith_nodeM`: LeanDA's tree over the answered hash (`Da.treeRootWith`, `Spec/DaWith`) of
  an answered tree's leaves is `some` of its root; `treeRootWith_blocks` the same for a tree over
  blocks of leaves, the tree over the blocks' roots.

`nodeH` is the tree over any pair hash; the shifts and congruences of `Link.lean` hold for it.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-! ## Trees over a pair hash -/

/-- Node `i` of level `l` over the leaves `leaf`, pairs hashed by `hp`. -/
def nodeH (hp : Digest → Digest → Digest) (leaf : ℕ → Digest) : ℕ → ℕ → Digest
  | 0, i => leaf i
  | l + 1, i => hp (nodeH hp leaf l (2 * i)) (nodeH hp leaf l (2 * i + 1))

/-- The deployed tree is the tree over BLAKE2s pairs. -/
theorem nodeD_eq_nodeH (leaf : ℕ → Digest) : ∀ l i, nodeD leaf l i = nodeH hashPair leaf l i
  | 0, _ => rfl
  | l + 1, i => by rw [nodeD, nodeH, nodeD_eq_nodeH leaf l, nodeD_eq_nodeH leaf l]

/-- A tree one level higher is the tree over the leaves' pairs. -/
theorem nodeH_succ (hp : Digest → Digest → Digest) (leaf : ℕ → Digest) : ∀ l i,
    nodeH hp leaf (l + 1) i = nodeH hp (fun i => hp (leaf (2 * i)) (leaf (2 * i + 1))) l i
  | 0, i => rfl
  | l + 1, i => by rw [nodeH, nodeH_succ hp leaf l, nodeH_succ hp leaf l, nodeH]

/-- A tree's nodes depend only on the leaves below them. -/
theorem nodeH_congr (hp : Digest → Digest → Digest) {L L' : ℕ → Digest} {k : ℕ}
    (h : ∀ t < 2 ^ k, L t = L' t) : ∀ l ≤ k, ∀ i < 2 ^ (k - l), nodeH hp L l i = nodeH hp L' l i
  | 0, _, i, hi => h i (by simpa using hi)
  | l + 1, hl, i, hi => by
    have hpow : 2 ^ (k - l) = 2 * 2 ^ (k - (l + 1)) := by
      rw [← pow_succ']; congr 1; omega
    rw [nodeH, nodeH, nodeH_congr hp h l (by omega) (2 * i) (by omega),
      nodeH_congr hp h l (by omega) (2 * i + 1) (by omega)]

/-- The model's answer to a pair of digests, `default` where it does not answer. -/
def pairM (M : HashModel) (a b : Digest) : Digest := ansD M (digestBytes a ++ digestBytes b)

/-- The tree over the model's pair answers. -/
abbrev nodeM (M : HashModel) (leaf : ℕ → Digest) : ℕ → ℕ → Digest := nodeH (pairM M) leaf

/-- **An answered tree of depth `k`**: every pair's hash, below the root, is answered, by the
parent node. -/
def TreeAns (M : HashModel) (leaf : ℕ → Digest) (k : ℕ) : Prop :=
  ∀ l < k, ∀ i < 2 ^ (k - l - 1),
    M.H (digestBytes (nodeM M leaf l (2 * i)) ++ digestBytes (nodeM M leaf l (2 * i + 1))) =
      some (nodeM M leaf (l + 1) i)

/-- An answered tree depends only on its leaves. -/
theorem treeAns_congr {M : HashModel} {L L' : ℕ → Digest} {k : ℕ} (h : ∀ t < 2 ^ k, L t = L' t)
    (hA : TreeAns M L k) : TreeAns M L' k := by
  intro l hl i hi
  have hpow : 2 ^ (k - l) = 2 * 2 ^ (k - l - 1) := by rw [← pow_succ']; congr 1; omega
  have hA := hA l hl i hi
  simp only [nodeM] at hA ⊢
  rw [← nodeH_congr _ h l hl.le (2 * i) (by omega), ← nodeH_congr _ h l hl.le (2 * i + 1) (by omega),
    ← nodeH_congr _ h (l + 1) hl i (by rwa [show k - (l + 1) = k - l - 1 by omega])]
  exact hA

/-! ## `da_levels` -/

/-- **`da_levels__L{2^k}_L{k}(tree)` over a hash model**: for `k = 0` the root is the cells at
`tree`; otherwise the `2^k` leaves at `tree` are digests, every level of their answered tree is in
memory, and the root is returned. -/
def Meaning_da_levelsWith (M : HashModel) (k : ℕ) (rd : Reader) (args rets : List E) : Prop :=
  ∃ tree r0 r1, args = [tree] ∧ rets = [r0, r1] ∧
    (k = 0 ∧ CellsAt rd tree [r0, r1] ∨ 1 ≤ k ∧ ∃ leaf : ℕ → Digest,
      (∀ l ≤ k, ∀ i < 2 ^ (k - l), CellsAt rd (tree * gen ^ (lvOff k l + 2 * i))
        [(digestScalars (nodeM M leaf l i)).1, (digestScalars (nodeM M leaf l i)).2]) ∧
      TreeAns M leaf k ∧ (r0, r1) = digestScalars (nodeM M leaf k 0))

/-- Iteration `x` of a level loop under `S`: the pair at `tree·g^ao·x⁴` checked into the node at
`tree·g^bo·x²`. -/
def LvStepB (S : BlakeSem) (rd : Reader) (tree : E) (ao bo : ℕ) (x : E) : Prop :=
  ∃ c0 c1 c2 c3 o0 o1, CellsAt rd (tree * gen ^ ao * (x * x * (x * x))) [c0, c1, c2, c3] ∧
    S.check ![c0, c1, c2, c3] (digestScalars paramIv).1 (digestScalars paramIv).2 o0 o1
      (metadataCell 64 true) ∧
    CellsAt rd (tree * gen ^ bo * (x * x)) [o0, o1]

section Levels

variable {S : BlakeSem}

/-- One frame of a level loop under `S` (`lv_step`'s forward direction). -/
theorem lv_stepB {rd : Reader} {k l : ℕ} (hk : k ≤ 10) (hl : l < k) (W tree : E) (C : CallRel)
    (x : E)
    (h : ∃ fn, coreProgram.find? (lvName k l) = some fn ∧ fn.SemB S C rd (x :: [W, tree]) []) :
    LvStepB S rd tree (lvOff k l) (lvOff k (l + 1)) x ∧ IsInK (x * gen + W) ∧
      (x * gen + W ≠ 0 → C (lvName k l) (x * gen :: [W, tree]) []) := by
  obtain ⟨fn, hfn, h⟩ := h
  rw [find_lv k l hk hl, Option.some.injEq] at hfn
  subst hfn
  have hgw : ∀ m, 1 ≤ m → m ≤ k → word (gw (lvOff k m)) 0 0 = gen ^ lvOff k m := fun m hm1 hm => by
    refine gw_spec ?_ (by
      unfold lvOff; have := Nat.pow_le_pow_right (n := 2) (by norm_num) hk; omega)
    interval_cases k <;> interval_cases m <;> decide
  rcases Nat.eq_zero_or_pos l with rfl | hl1
  · simp only [↓reduceIte, Fn.SemB, lvBody0, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, LvStepB, cellsAt_four,
      cellsAt_two, iv0_word, iv1_word, md64_word, Nat.zero_add] at h ⊢
    have h0 : lvOff k 0 = 0 := by simp [lvOff]
    rw [h0, pow_zero, mul_one, ← hgw 1 (by omega) (by omega)]
    obtain ⟨σ, hp, m3, m4, m5, c6, m7, m8, m9, l10, l11, l12, l13, c14, c15, c16, hc, l17, l18,
      c19, m20, a21, c22, m23, hk21, hnext, -⟩ := h
    simp only [List.cons.injEq, and_true] at hp
    obtain ⟨rfl, rfl, rfl⟩ := hp
    rw [m5, m4, m3] at l10 l11 l12 l13
    rw [m9, m8, m7, c6] at l17 l18
    rw [c14, c15, c16] at hc
    rw [a21, m20, c19, word_gen] at hk21 hnext
    rw [m23, c22, word_gen] at hnext
    exact ⟨⟨_, _, _, _, _, _, ⟨l10, l11, l12, l13⟩, hc, ⟨l17, l18⟩⟩, hk21, hnext⟩
  · simp only [show l ≠ 0 by omega, ↓reduceIte, Fn.SemB, lvBody, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, LvStepB,
      cellsAt_four, cellsAt_two] at h ⊢
    rw [← hgw l (by omega) (by omega), ← hgw (l + 1) (by omega) (by omega)]
    obtain ⟨σ, hp, c3, m4, m5, m6, m7, c8, m9, m10, m11, l12, l13, l14, l15, c16, c17, c18, hc,
      l19, l20, c21, m22, a23, c24, m25, hk23, hnext, -⟩ := h
    simp only [List.cons.injEq, and_true] at hp
    obtain ⟨rfl, rfl, rfl⟩ := hp
    rw [m7, m6, m5, m4, c3] at l12 l13 l14 l15
    rw [m11, m10, m9, c8] at l19 l20
    rw [c16, c17, c18] at hc
    rw [a23, m22, c21, word_gen] at hk23 hnext
    rw [m25, c24, word_gen] at hnext
    exact ⟨⟨_, _, _, _, _, _, ⟨l12, l13, l14, l15⟩, hc, ⟨l19, l20⟩⟩, hk23, hnext⟩

/-- **A level loop under `S`** runs its `2^(k-l-1)` iterations. -/
theorem lv_relB {rd : Reader} {k l : ℕ} (hk : k ≤ 10) (hl : l < k) (tree : E)
    (h : coreProgram.RelB S rd (lvName k l) [gen ^ 0, gen ^ 2 ^ (k - l - 1), tree] []) :
    ∀ j < 2 ^ (k - l - 1), LvStepB S rd tree (lvOff k l) (lvOff k (l + 1)) (gen ^ j) := by
  have hc : 2 ^ (k - l - 1) ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨m, hm0, hmN, hfirst, hall⟩ :=
    loopB_fwd (B := fun _ x => LvStepB S rd tree (lvOff k l) (lvOff k (l + 1)) x)
      (fun _ _ _ _ h => h) (lv_stepB hk hl _ tree) 0 h
  intro j hj
  have hmw : m = 2 ^ (k - l - 1) := by
    rcases Nat.lt_or_ge (2 ^ (k - l - 1)) m with hlt | hge
    · exact absurd rfl (hfirst _ (by have := Nat.one_le_two_pow (n := k - l - 1); omega) hlt)
    · exact (gen_pow_inj' (by omega) (by omega) hmN).symm
  exact hall j (by omega) (by omega)

end Levels

/-- A level step under `S`, as reads of the tree. -/
theorem lvStepB_iff {S : BlakeSem} {rd : Reader} {tree : E} {ao bo j : ℕ} :
    LvStepB S rd tree ao bo (gen ^ j) ↔ ∃ c0 c1 c2 c3 o0 o1,
      LoadHolds rd tree (ao + 4 * j) c0 ∧ LoadHolds rd tree (ao + 4 * j + 1) c1 ∧
      LoadHolds rd tree (ao + 4 * j + 2) c2 ∧ LoadHolds rd tree (ao + 4 * j + 3) c3 ∧
      S.check ![c0, c1, c2, c3] (digestScalars paramIv).1 (digestScalars paramIv).2 o0 o1
        (metadataCell 64 true) ∧
      LoadHolds rd tree (bo + 2 * j) o0 ∧ LoadHolds rd tree (bo + 2 * j + 1) o1 := by
  simp only [LvStepB, ptr_pow4]
  simp only [ptr_pow2, cellsAt_four, cellsAt_two, loadHolds_mul_gen_pow, Nat.add_zero, and_assoc]

/-- The tree levels of the nodes `N` in memory, as reads. -/
def TreeMemN (rd : Reader) (tree : E) (k : ℕ) (N : ℕ → ℕ → Digest) (l : ℕ) : Prop :=
  ∀ i < 2 ^ (k - l), LoadHolds rd tree (lvOff k l + 2 * i) (digestScalars (N l i)).1 ∧
    LoadHolds rd tree (lvOff k l + 2 * i + 1) (digestScalars (N l i)).2

/-- The levels in memory, as reads through the tree's pointer. -/
theorem treeMemN_iff {rd : Reader} {tree : E} {k : ℕ} {N : ℕ → ℕ → Digest} {l : ℕ} :
    TreeMemN rd tree k N l ↔ ∀ i < 2 ^ (k - l), CellsAt rd (tree * gen ^ (lvOff k l + 2 * i))
      [(digestScalars (N l i)).1, (digestScalars (N l i)).2] := by
  simp only [TreeMemN, cellsAt_two, loadHolds_mul_gen_pow, Nat.add_zero]

/-- **One hash of a tree level under a model**: the pair's answered hash. -/
theorem pair_model {M : HashModel} {a b : Digest} {o0 o1 : E}
    (hc : M.sem.check ![(digestScalars a).1, (digestScalars a).2, (digestScalars b).1,
        (digestScalars b).2] (digestScalars paramIv).1 (digestScalars paramIv).2 o0 o1
        (metadataCell 64 true)) :
    M.H (digestBytes a ++ digestBytes b) = some (pairM M a b) ∧
      (o0, o1) = digestScalars (pairM M a b) := by
  obtain ⟨d, hd, hout⟩ := HashModel.one_block (M := M) hc
  rw [blockBytes_pair] at hd
  rw [pairM, ansD_of hd]
  exact ⟨hd, hout⟩

/-- **The levels, forward, under a model**: the loops' iterations make every level the answered
tree of its leaves. -/
theorem treeMem_of_stepsM {M : HashModel} {rd : Reader} {tree : E} {k : ℕ} (hk1 : 1 ≤ k)
    (hsteps : ∀ l < k, ∀ j < 2 ^ (k - l - 1),
      LvStepB M.sem rd tree (lvOff k l) (lvOff k (l + 1)) (gen ^ j)) :
    ∃ leaf, (∀ l ≤ k, TreeMemN rd tree k (nodeM M leaf) l) ∧ TreeAns M leaf k := by
  let leaf := fun i => cellsDigest (cellAt rd tree (2 * i)) (cellAt rd tree (2 * i + 1))
  have h0 : lvOff k 0 = 0 := by simp [lvOff]
  have hmem : ∀ l ≤ k, TreeMemN rd tree k (nodeM M leaf) l := by
    intro l hl
    induction l with
    | zero =>
      intro i hi
      obtain ⟨c0, c1, c2, c3, o0, o1, l0, l1, l2, l3, hc, -, -⟩ :=
        lvStepB_iff.mp (hsteps 0 hk1 (i / 2) (by
          have : 2 ^ (k - 0) = 2 * 2 ^ (k - 0 - 1) := by rw [← pow_succ']; congr 1; omega
          omega))
      have hcan := (M.canonical hc).1
      rw [h0, Nat.zero_add] at l0 l1 l2 l3
      rw [h0, Nat.zero_add]
      simp only [nodeM, nodeH, leaf]
      rcases Nat.mod_two_eq_zero_or_one i with hr | hr
      · rw [show 4 * (i / 2) = 2 * i by omega] at l0 l1
        rw [cellAt_of_load l0, cellAt_of_load l1,
          digestScalars_cellsDigest (by simpa using hcan 0) (by simpa using hcan 1)]
        exact ⟨l0, l1⟩
      · rw [show 4 * (i / 2) + 2 = 2 * i by omega] at l2
        rw [show 4 * (i / 2) + 3 = 2 * i + 1 by omega] at l3
        rw [cellAt_of_load l2, cellAt_of_load l3,
          digestScalars_cellsDigest (by simpa using hcan 2) (by simpa using hcan 3)]
        exact ⟨l2, l3⟩
    | succ l ih =>
      have hP := ih (by omega)
      intro i hi
      obtain ⟨c0, c1, c2, c3, o0, o1, l0, l1, l2, l3, hc, s0, s1⟩ :=
        lvStepB_iff.mp (hsteps l (by omega) i (by rwa [show k - l - 1 = k - (l + 1) by omega]))
      have hpow : 2 ^ (k - l) = 2 * 2 ^ (k - (l + 1)) := by rw [← pow_succ']; congr 1; omega
      obtain ⟨n0, n1⟩ := hP (2 * i) (by omega)
      obtain ⟨n2, n3⟩ := hP (2 * i + 1) (by omega)
      rw [show lvOff k l + 2 * (2 * i) = lvOff k l + 4 * i by ring] at n0 n1
      rw [show lvOff k l + 2 * (2 * i + 1) = lvOff k l + 4 * i + 2 by ring] at n2 n3
      rw [show lvOff k l + 4 * i + 2 + 1 = lvOff k l + 4 * i + 3 by ring] at n3
      rw [loadHolds_unique l0 n0, loadHolds_unique l1 n1, loadHolds_unique l2 n2,
        loadHolds_unique l3 n3] at hc
      have hout := (pair_model hc).2
      have e0 := congrArg Prod.fst hout
      have e1 := congrArg Prod.snd hout
      simp only at e0 e1
      rw [e0] at s0
      rw [e1] at s1
      exact ⟨s0, s1⟩
  refine ⟨leaf, hmem, fun l hl i hi => ?_⟩
  obtain ⟨c0, c1, c2, c3, o0, o1, l0, l1, l2, l3, hc, -, -⟩ :=
    lvStepB_iff.mp (hsteps l hl i hi)
  have hpow : 2 ^ (k - l) = 2 * 2 ^ (k - l - 1) := by rw [← pow_succ']; congr 1; omega
  obtain ⟨n0, n1⟩ := hmem l hl.le (2 * i) (by omega)
  obtain ⟨n2, n3⟩ := hmem l hl.le (2 * i + 1) (by omega)
  rw [show lvOff k l + 2 * (2 * i) = lvOff k l + 4 * i by ring] at n0 n1
  rw [show lvOff k l + 2 * (2 * i + 1) = lvOff k l + 4 * i + 2 by ring] at n2 n3
  rw [show lvOff k l + 4 * i + 2 + 1 = lvOff k l + 4 * i + 3 by ring] at n3
  rw [loadHolds_unique l0 n0, loadHolds_unique l1 n1, loadHolds_unique l2 n2,
    loadHolds_unique l3 n3] at hc
  exact (pair_model hc).1

/-- **`da_levels__L{2^k}_L{k}` is sound under a hash model.** -/
theorem da_levels_model {M : HashModel} {rd : Reader} (k : ℕ) (hk : k ≤ 10) (args rets : List E)
    (h : coreProgram.RelB M.sem rd (dlNames.getD k "") args rets) :
    Meaning_da_levelsWith M k rd args rets := by
  rw [relB_of_find (find_dl k hk)] at h
  have hnr : ∀ l, Stmt.noRetList (dlBlk k l) = true := fun l => by
    simp [dlBlk, Stmt.noRetList, Stmt.noRet]
  simp only [Fn.SemB, dlBody, holdsListB_flatMap k (dlBlk k) hnr] at h
  simp only [dlBlk, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, and_true, List.map_cons,
    List.map_nil] at h
  obtain ⟨σ, hp, hlev, l1, l2, hr⟩ := h
  refine ⟨σ (.n 0), σ (.n (1 + 5 * k)), σ (.n (2 + 5 * k)), hp.symm, hr.symm, ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · exact Or.inl ⟨rfl, cellsAt_two.mpr ⟨by simpa using l1, by simpa using l2⟩⟩
  have hsteps : ∀ l < k, ∀ j < 2 ^ (k - l - 1),
      LvStepB M.sem rd (σ (.n 0)) (lvOff k l) (lvOff k (l + 1)) (gen ^ j) := by
    intro l hl
    obtain ⟨c1, c2, a3, c4, c5, -, hnext⟩ := hlev l hl
    rw [a3, c1, c2, word_one, gw_end hk hl] at hnext
    have hne : (1 : E) + gen ^ 2 ^ (k - l - 1) ≠ 0 := by
      rw [add_comm]
      exact gen_pow_ne_one Nat.one_le_two_pow
        (lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (by omega : k - l - 1 ≤ 10))
          (by norm_num))
    have h := hnext hne
    rw [c4, c5, word_one, gw_end hk hl, ← pow_zero gen] at h
    exact lv_relB hk hl _ h
  obtain ⟨leaf, hP, hA⟩ := treeMem_of_stepsM hk1 hsteps
  refine Or.inr ⟨hk1, leaf, fun l hl => treeMemN_iff.mp (hP l hl), hA, ?_⟩
  obtain ⟨n0, n1⟩ := hP k le_rfl 0 (by simp)
  have hoff : lvOff k k + 2 * 0 = 4 * 2 ^ k - 4 := by simp [lvOff]
  rw [hoff] at n0 n1
  rw [show 4 * 2 ^ k - 4 + 1 = 4 * 2 ^ k - 3 by have := Nat.one_le_two_pow (n := k); omega] at n1
  rw [loadHolds_unique l1 n0, loadHolds_unique l2 n1]

/-- **A tree's root from its leaves, under a model**: the leaves stored at `tree·g^(2i)` make the
tree `da_levels` built their answered tree, and its root the one returned. -/
theorem levels_rootM {M : HashModel} {rd : Reader} {k : ℕ} {tree r0 r1 : E} {L : ℕ → Digest}
    (h : Meaning_da_levelsWith M k rd [tree] [r0, r1])
    (hl : ∀ i < 2 ^ k, CellsAt rd (tree * gen ^ (2 * i))
      [(digestScalars (L i)).1, (digestScalars (L i)).2]) :
    (r0, r1) = digestScalars (nodeM M L k 0) ∧ TreeAns M L k := by
  obtain ⟨tree', r0', r1', ha, hr, hm⟩ := h
  simp only [List.cons.injEq, and_true] at ha hr
  obtain ⟨rfl⟩ := ha
  obtain ⟨rfl, rfl⟩ := hr
  rcases hm with ⟨rfl, hc⟩ | ⟨hk, leaf, hlv, hA, hroot⟩
  · have h0 := hl 0 (by norm_num)
    rw [Nat.mul_zero, pow_zero, mul_one] at h0
    obtain ⟨a0, a1⟩ := cellsAt_two.mp hc
    obtain ⟨b0, b1⟩ := cellsAt_two.mp h0
    rw [loadHolds_unique a0 b0, loadHolds_unique a1 b1]
    exact ⟨rfl, fun l hl => absurd hl (by omega)⟩
  · have hagree : ∀ t < 2 ^ k, leaf t = L t := fun t ht => by
      refine digestScalars_injective ?_
      have h1 := hlv 0 (Nat.zero_le _) t (by simpa using ht)
      rw [lvOff, Nat.sub_zero, Nat.sub_self, Nat.zero_add] at h1
      obtain ⟨a0, a1⟩ := cellsAt_two.mp h1
      obtain ⟨b0, b1⟩ := cellsAt_two.mp (hl t ht)
      exact Prod.ext (loadHolds_unique a0 b0) (loadHolds_unique a1 b1)
    refine ⟨?_, treeAns_congr hagree hA⟩
    rw [hroot]
    simp only [nodeM]
    rw [nodeH_congr _ hagree k le_rfl 0 (by simp)]

/-! ## LeanDA's tree over the answered hash -/

/-- A `mapM` over `Option` whose every step on the list is answered is `some` of the map. -/
theorem mapM_option_some_mem {α β : Type} (f : α → Option β) (g : α → β) :
    ∀ l : List α, (∀ a ∈ l, f a = some (g a)) → l.mapM f = some (l.map g)
  | [], _ => rfl
  | a :: l, hf => by
    rw [List.mapM_cons, hf a (by simp),
      mapM_option_some_mem f g l fun b hb => hf b (by simp [hb])]
    rfl

/-- LeanDA's pair of two digests is their bytes. -/
theorem pairBytes_toBytes (a b : Digest) :
    LeanDa.pairBytes (Da.toBytes a) (Da.toBytes b) = digestBytes a ++ digestBytes b := by
  rw [LeanDa.pairBytes, toBytes_toList, toBytes_toList]

/-- **LeanDA's tree over the answered hash** of an answered tree's leaves is `some` of its root,
with any fuel above the depth. -/
theorem treeRootFuel_nodeM {M : HashModel} : ∀ (k : ℕ) (leaf : ℕ → Digest) (fuel : ℕ),
    k ≤ fuel → TreeAns M leaf k →
    Da.treeRootFuel (Da.daHash M.H) fuel ((List.range (2 ^ k)).map fun i => Da.toBytes (leaf i)) =
      some (Da.toBytes (nodeM M leaf k 0))
  | 0, leaf, fuel, _, _ => by
    cases fuel <;> simp [Da.treeRootFuel, nodeM, nodeH]
  | k + 1, leaf, fuel, hf, hA => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hlen : ((List.range (2 ^ (k + 1))).map fun i => Da.toBytes (leaf i)).length =
        2 * 2 ^ k := by simp [pow_succ, mul_comm]
    have hlev : Da.treeLevelWith (Da.daHash M.H)
        ((List.range (2 ^ (k + 1))).map fun i => Da.toBytes (leaf i)) =
        some ((List.range (2 ^ k)).map fun i => Da.toBytes (nodeM M leaf 1 i)) := by
      rw [Da.treeLevelWith, hlen, show 2 * 2 ^ k / 2 = 2 ^ k by omega]
      refine mapM_option_some_mem _ _ _ fun i hi => ?_
      have hi' := List.mem_range.mp hi
      rw [List.getD_eq_getElem _ _ (by rw [hlen]; omega),
        List.getD_eq_getElem _ _ (by rw [hlen]; omega)]
      simp only [List.getElem_map, List.getElem_range]
      rw [pairBytes_toBytes, Da.daHash]
      have := hA 0 (by omega) i (by simpa using hi')
      simp only [nodeM, nodeH] at this ⊢
      rw [this]
      rfl
    rw [Da.treeRootFuel, ite_neg' (by rw [hlen]; have := Nat.one_le_two_pow (n := k); omega), hlev]
    simp only [Option.bind_eq_bind, Option.bind_some]
    have hA' : TreeAns M (fun i => pairM M (leaf (2 * i)) (leaf (2 * i + 1))) k := by
      intro l hl i hi
      have := hA (l + 1) (by omega) i (by rwa [show k + 1 - (l + 1) - 1 = k - l - 1 by omega])
      simp only [nodeM] at this ⊢
      rw [nodeH_succ, nodeH_succ, nodeH_succ] at this
      exact this
    have := treeRootFuel_nodeM k (fun i => pairM M (leaf (2 * i)) (leaf (2 * i + 1))) f
      (by omega) hA'
    simp only [nodeM] at this ⊢
    rw [nodeH_succ]
    exact this

/-- **LeanDA's tree over the answered hash** (`Da.treeRootWith`) of an answered tree's leaves is
`some` of its root. -/
theorem treeRootWith_nodeM {M : HashModel} {k : ℕ} {leaf : ℕ → Digest} (hA : TreeAns M leaf k) :
    Da.treeRootWith (Da.daHash M.H) ((List.range (2 ^ k)).map fun i => Da.toBytes (leaf i)) =
      some (Da.toBytes (nodeM M leaf k 0)) :=
  treeRootFuel_nodeM k leaf _ (by simpa using (Nat.lt_two_pow_self (n := k)).le) hA

/-! ## Trees over blocks -/

section Blocks

variable (hp : Digest → Digest → Digest) (a c : ℕ) (L : ℕ → ℕ → Digest)

/-- The leaves of `2^c` blocks of `2^a`, in one row. -/
def blkLeaf (m : ℕ) : Digest := L (m / 2 ^ a) (m % 2 ^ a)

/-- The block trees' nodes, in the whole tree. -/
theorem nodeH_blk : ∀ l ≤ a, ∀ j t, t < 2 ^ (a - l) →
    nodeH hp (blkLeaf a L) l (2 ^ (a - l) * j + t) = nodeH hp (L j) l t
  | 0, _, j, t, ht => by
    simp only [nodeH, blkLeaf, Nat.sub_zero] at ht ⊢
    have hp0 : 0 < 2 ^ a := by positivity
    rw [show (2 ^ a * j + t) / 2 ^ a = j by
        rw [Nat.add_comm, Nat.add_mul_div_left _ _ hp0, Nat.div_eq_of_lt ht, Nat.zero_add],
      show (2 ^ a * j + t) % 2 ^ a = t by
        rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]]
  | l + 1, hl, j, t, ht => by
    have hpow : 2 ^ (a - l) = 2 * 2 ^ (a - (l + 1)) := by rw [← pow_succ']; congr 1; omega
    rw [nodeH, nodeH,
      show 2 * (2 ^ (a - (l + 1)) * j + t) = 2 ^ (a - l) * j + 2 * t by rw [hpow]; ring,
      show 2 ^ (a - l) * j + 2 * t + 1 = 2 ^ (a - l) * j + (2 * t + 1) by ring,
      nodeH_blk l (by omega) j (2 * t) (by omega), nodeH_blk l (by omega) j (2 * t + 1) (by omega)]

/-- The top tree's nodes, in the whole tree. -/
theorem nodeH_top : ∀ c' i, nodeH hp (blkLeaf a L) (a + c') i =
    nodeH hp (fun j => nodeH hp (L j) a 0) c' i
  | 0, i => by
    show nodeH hp (blkLeaf a L) (a + 0) i = nodeH hp (L i) a 0
    simpa using nodeH_blk hp a L a le_rfl i 0 (by simp)
  | c' + 1, i => by
    rw [← Nat.add_assoc, nodeH, nodeH, nodeH_top c' (2 * i), nodeH_top c' (2 * i + 1)]

end Blocks

/-- A run of `k·n` indices mapped, cut into `n` runs of `k` (`Link.map_range_mul`). -/
theorem map_range_mul_blocks {α : Type} (k : ℕ) (g : ℕ → α) :
    ∀ n, (List.range (k * n)).map g =
      (List.range n).flatMap fun b => (List.range k).map fun r => g (k * b + r)
  | 0 => by simp
  | n + 1 => by
      rw [show k * (n + 1) = k * n + k by ring, List.range_add, List.map_append,
        map_range_mul_blocks k g n, List.range_succ, List.flatMap_append, List.map_map]
      simp [Function.comp_def]

/-- A tree over answered blocks under an answered tree of their roots is answered. -/
theorem treeAns_blocks {M : HashModel} {a c : ℕ} {L : ℕ → ℕ → Digest}
    (hA : ∀ j < 2 ^ c, TreeAns M (L j) a) (hT : TreeAns M (fun j => nodeM M (L j) a 0) c) :
    TreeAns M (blkLeaf a L) (a + c) := by
  intro l hl i hi
  simp only [nodeM]
  rcases Nat.lt_or_ge l a with hla | hla
  · -- inside a block
    set P := 2 ^ (a - l - 1) with hP
    have hP0 : 0 < P := by positivity
    have hpow : 2 ^ (a - l) = 2 * P := by rw [hP, ← pow_succ']; congr 1; omega
    have hpow1 : 2 ^ (a - (l + 1)) = P := by rw [hP]; congr 1
    have hi' : i < P * 2 ^ c := by
      rwa [hP, ← pow_add, show a - l - 1 + c = a + c - l - 1 by omega]
    set j := i / P
    set t := i % P
    have hj : j < 2 ^ c := (Nat.div_lt_iff_lt_mul hP0).mpr (by rwa [mul_comm])
    have ht : t < P := Nat.mod_lt _ hP0
    have hi2 : i = P * j + t := (Nat.div_add_mod i P).symm
    have e0 : 2 * i = 2 ^ (a - l) * j + 2 * t := by rw [hpow, hi2]; ring
    have e1 : 2 * i + 1 = 2 ^ (a - l) * j + (2 * t + 1) := by rw [hpow, hi2]; ring
    have e2 : i = 2 ^ (a - (l + 1)) * j + t := by rw [hpow1]; exact hi2
    rw [e0, show 2 ^ (a - l) * j + 2 * t + 1 = 2 ^ (a - l) * j + (2 * t + 1) by ring,
      nodeH_blk _ a L l hla.le j (2 * t) (by omega),
      nodeH_blk _ a L l hla.le j (2 * t + 1) (by omega)]
    conv_rhs => rw [e2, nodeH_blk _ a L (l + 1) hla j t (by omega)]
    exact hA j hj l hla t (by rw [← hP]; exact ht)
  · -- the top tree
    obtain ⟨c', rfl⟩ : ∃ c', l = a + c' := ⟨l - a, by omega⟩
    rw [nodeH_top, nodeH_top, show a + c' + 1 = a + (c' + 1) by ring, nodeH_top]
    exact hT c' (by omega) i (by rwa [show c - c' - 1 = a + c - (a + c') - 1 by omega])

/-- **LeanDA's tree over blocks, over the answered hash**: `2^c` blocks of `2^a` leaves, each an
answered tree, under an answered tree of their roots, give `some` of the top root. -/
theorem treeRootWith_blocks {M : HashModel} {a c : ℕ} {L : ℕ → ℕ → Digest}
    (hA : ∀ j < 2 ^ c, TreeAns M (L j) a) (hT : TreeAns M (fun j => nodeM M (L j) a 0) c) :
    Da.treeRootWith (Da.daHash M.H) ((List.range (2 ^ c)).flatMap fun j =>
        (List.range (2 ^ a)).map fun i => Da.toBytes (L j i)) =
      some (Da.toBytes (nodeM M (fun j => nodeM M (L j) a 0) c 0)) := by
  have e : (List.range (2 ^ c)).flatMap (fun j => (List.range (2 ^ a)).map fun i =>
      Da.toBytes (L j i)) = (List.range (2 ^ (a + c))).map fun m => Da.toBytes (blkLeaf a L m) := by
    rw [pow_add, map_range_mul_blocks]
    refine List.flatMap_congr fun j _ => List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    have hp : 0 < 2 ^ a := by positivity
    simp only [blkLeaf]
    rw [show (2 ^ a * j + i) / 2 ^ a = j by
        rw [Nat.add_comm, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hi', Nat.zero_add],
      show (2 ^ a * j + i) % 2 ^ a = i by
        rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi']]
  rw [e, treeRootWith_nodeM (treeAns_blocks hA hT), nodeM, nodeH_top]

end
end LeanVM.Guest.B1.Digest
