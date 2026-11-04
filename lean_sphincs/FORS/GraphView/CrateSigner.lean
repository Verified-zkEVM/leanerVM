import FORS.GraphView.Cost

/-! The crate's signer (`Seeded.sign`) on a fixed answer function: each tree it builds once gives
the model's root and path (`eval_treeNodeWithPath_fst`, `eval_treeNodeWithPath_snd`), each FORS tree
the model's key pair and opening (`eval_forsOpenOnce`), and, for a full or layered key, the layers
from the bottom up the model's layers (`eval_signLayersUp`): its signature is the model's
(`eval_sign_eq_finishSign`). Its hash calls (`hashCalls_sign`): the randomizer, the digest, each FORS
tree once, and per layer, until the first failed search, the search and on success the chain values
and the whole tree. -/

open OracleComp OracleSpec

namespace FORS.Security.GraphView

variable [Params]
open Concrete Completeness Seeded Prefix

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

variable (f : QueryImpl HashSpec Id)

/-! ### A layer's tree -/

section Tree

variable (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (seed : MasterSeed)
  (target : Nat)

theorem eval_treeNodeWithPath_fst : ∀ level nodeIdx,
    (evalWithAnswerFn f (treeNodeWithPath parameter lay tree seed target level nodeIdx :
      OracleComp HashSpec (Digest × (Nat → Digest)))).1 =
      evalWithAnswerFn f (treeNode parameter lay tree seed level nodeIdx : OracleComp HashSpec Digest)
  | 0, nodeIdx => by
      simp only [treeNodeWithPath, treeNode, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  | level + 1, nodeIdx => by
      simp only [treeNodeWithPath, treeNode, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
        eval_treeNodeWithPath_fst level]

/-- The bit of `target` at `level` splits its node at `level + 1` into its children. -/
theorem div_two_pow_succ (target level : Nat) :
    target / 2 ^ level = 2 * (target / 2 ^ (level + 1)) + if target.testBit level then 1 else 0 := by
  have h := Nat.div_add_mod (target / 2 ^ level) 2
  rw [Nat.div_div_eq_div_mul, ← pow_succ] at h
  have hbit : (target / 2 ^ level) % 2 = if target.testBit level then 1 else 0 := by
    rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
    rcases Nat.mod_two_eq_zero_or_one (target / 2 ^ level) with h0 | h1
    · simp [h0]
    · simp [h1]
  omega

theorem eval_treeNodeWithPath_snd : ∀ level nodeIdx, target / 2 ^ level = nodeIdx → ∀ k < level,
    (evalWithAnswerFn f (treeNodeWithPath parameter lay tree seed target level nodeIdx :
      OracleComp HashSpec (Digest × (Nat → Digest)))).2 k =
      evalWithAnswerFn f (treeNode parameter lay tree seed k (Nat.xor (target / 2 ^ k) 1) :
        OracleComp HashSpec Digest)
  | 0, _, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | level + 1, nodeIdx, hnode, k, hk => by
      have hsplit := div_two_pow_succ target level
      rw [hnode] at hsplit
      simp only [treeNodeWithPath, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
      by_cases hb : target.testBit level
      · simp only [hb, ↓reduceIte] at hsplit ⊢
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
        · rw [Function.update_of_ne (Nat.ne_of_lt hk)]
          exact eval_treeNodeWithPath_snd level _ hsplit k hk
        · rw [Function.update_self, eval_treeNodeWithPath_fst, hsplit]
          have hx : Nat.xor (2 * nodeIdx + 1) 1 = 2 * nodeIdx := by
            change (2 * nodeIdx + 1) ^^^ 1 = 2 * nodeIdx
            rw [Nat.xor_one_of_odd ⟨nodeIdx, rfl⟩]
            omega
          rw [hx]
      · simp only [hb, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hsplit ⊢
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
        · rw [Function.update_of_ne (Nat.ne_of_lt hk)]
          exact eval_treeNodeWithPath_snd level _ (by omega) k hk
        · rw [Function.update_self, eval_treeNodeWithPath_fst, hsplit]
          have hx : Nat.xor (2 * nodeIdx) 1 = 2 * nodeIdx + 1 := by
            change (2 * nodeIdx) ^^^ 1 = 2 * nodeIdx + 1
            rw [Nat.xor_one_of_even ⟨nodeIdx, by omega⟩]
          rw [hx]

theorem hashCalls_treeNodeWithPath : ∀ level nodeIdx,
    hashCalls f (treeNodeWithPath parameter lay tree seed target level nodeIdx :
      OracleComp HashSpec (Digest × (Nat → Digest))) =
      hashCalls f (treeNode parameter lay tree seed level nodeIdx : OracleComp HashSpec Digest)
  | 0, nodeIdx => by
      simp only [treeNodeWithPath, treeNode, hashCalls_bind, hashCalls_pure, Nat.add_zero]
  | level + 1, nodeIdx => by
      simp only [treeNodeWithPath, treeNode, hashCalls_bind, hashCalls_pure,
        hashCalls_treeNodeWithPath level, eval_treeNodeWithPath_fst, hashCalls_tweakableHash]

end Tree

/-! ### A FORS tree -/

section Fors

variable (parameter : PublicParameter) (index : Index) (κ : FTree) (seed : MasterSeed)
  (target : FLeaf)

theorem eval_forsSubtree_fst : ∀ height node,
    (evalWithAnswerFn f (forsSubtree parameter index κ seed target height node :
      OracleComp HashSpec (Digest × Digest × (Nat → Digest)))).1 =
      forsNodeValue f parameter index κ seed (height + 1) node
  | 0, node => by
      simp only [forsSubtree, forsNodeValue, Seeded.forsNode, evalWithAnswerFn_bind,
        evalWithAnswerFn_pure]
  | height + 1, node => by
      simp only [forsSubtree, forsNodeValue, Seeded.forsNode, evalWithAnswerFn_bind,
        evalWithAnswerFn_pure]
      rw [← forsNodeValue, ← forsNodeValue, ← eval_forsSubtree_fst height,
        ← eval_forsSubtree_fst height]

theorem hashCalls_forsSubtree : ∀ height node,
    hashCalls f (forsSubtree parameter index κ seed target height node :
      OracleComp HashSpec (Digest × Digest × (Nat → Digest))) =
      hashCalls f (Seeded.forsNode parameter index κ seed (height + 1) node :
        OracleComp HashSpec Digest)
  | 0, node => by
      simp only [forsSubtree, Seeded.forsNode, hashCalls_bind, hashCalls_pure, Nat.add_zero]
  | height + 1, node => by
      simp only [forsSubtree, Seeded.forsNode, hashCalls_bind, hashCalls_pure, Nat.add_zero,
        hashCalls_forsSubtree height]
      rw [eval_forsSubtree_fst, eval_forsSubtree_fst]
      split <;> simp only [forsNodeValue, hashCalls_tweakableHash, hashCalls_pure]

/-- The pair of leaves of a FORS tree that holds `target`: its two leaves are below `2^a`. -/
theorem pair_lt (target : FLeaf) : 2 * (target.val / 2) + 1 < 2 ^ forsHeight := by
  have ht := target.isLt
  have ha := Params.forsHeight_ge
  have hpow : 2 ^ forsHeight = 2 * 2 ^ (forsHeight - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  omega

theorem hashHalf_even (n : Nat) (output : HashOutput) :
    hashHalf (2 * n) output = hashHalf 0 output := by
  simp [hashHalf]

theorem hashHalf_odd (n : Nat) (output : HashOutput) :
    hashHalf (2 * n + 1) output = hashHalf 1 output := by
  simp [hashHalf, Nat.add_mod]

theorem eval_forsSubtree_secret : ∀ height node, target.val / 2 ^ (height + 1) = node →
    (evalWithAnswerFn f (forsSubtree parameter index κ seed target height node :
      OracleComp HashSpec (Digest × Digest × (Nat → Digest)))).2.1 =
      forsSecretValue f parameter index κ seed target
  | 0, node, hnode => by
      have hlt := pair_lt target
      rw [zero_add, pow_one] at hnode
      subst hnode
      have hleft : 2 * (target.val / 2) % 2 ^ forsHeight = 2 * (target.val / 2) :=
        Nat.mod_eq_of_lt (by omega)
      have hp : leafPair (⟨2 * (target.val / 2) % 2 ^ forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩ :
          FLeaf) = leafPair target := by
        apply Fin.ext; simp only [leafPair, hleft]; omega
      simp only [forsSubtree, evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_deriveOutput,
        forsSecretValue_eq, hp]
  | height + 1, node, hnode => by
      have hsplit := div_two_pow_succ target.val (height + 1)
      rw [hnode] at hsplit
      simp only [forsSubtree, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
      by_cases hb : target.val.testBit (height + 1)
      · simp only [hb, ↓reduceIte] at hsplit ⊢
        exact eval_forsSubtree_secret height _ hsplit
      · simp only [hb, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hsplit ⊢
        exact eval_forsSubtree_secret height _ hsplit

theorem eval_forsSubtree_path : ∀ height node, target.val / 2 ^ (height + 1) = node → ∀ k ≤ height,
    (evalWithAnswerFn f (forsSubtree parameter index κ seed target height node :
      OracleComp HashSpec (Digest × Digest × (Nat → Digest)))).2.2 k =
      forsNodeValue f parameter index κ seed k (Nat.xor (target.val / 2 ^ k) 1)
  | 0, node, hnode, k, hk => by
      obtain rfl : k = 0 := Nat.le_zero.mp hk
      have hlt := pair_lt target
      rw [zero_add, pow_one] at hnode
      subst hnode
      have hleft : 2 * (target.val / 2) % 2 ^ forsHeight = 2 * (target.val / 2) :=
        Nat.mod_eq_of_lt (by omega)
      have hright : (2 * (target.val / 2) + 1) % 2 ^ forsHeight = 2 * (target.val / 2) + 1 :=
        Nat.mod_eq_of_lt hlt
      have hsplit := div_two_pow_succ target.val 0
      simp only [pow_zero, Nat.div_one, zero_add, pow_one] at hsplit
      simp only [forsSubtree, evalWithAnswerFn_bind, evalWithAnswerFn_pure, pow_zero, Nat.div_one,
        forsNodeValue, Seeded.forsNode, Seeded.forsSecret, forsLeafHash, eval_tweakableHash,
        eval_deriveOutput]
      by_cases hb : target.val.testBit 0
      · simp only [hb, ↓reduceIte] at hsplit ⊢
        have hx : Nat.xor target.val 1 = 2 * (target.val / 2) := by
          change target.val ^^^ 1 = _
          rw [Nat.xor_one_of_odd ⟨target.val / 2, hsplit⟩]
          omega
        have hpair : leafPair (⟨Nat.xor target.val 1 % 2 ^ forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩ :
            FLeaf) = leafPair ⟨2 * (target.val / 2) % 2 ^ forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩ := by
          apply Fin.ext; simp only [leafPair, hx]
        have hleaf : (⟨Nat.xor target.val 1 % 2 ^ forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩ : FLeaf) =
            ⟨2 * (target.val / 2) % 2 ^ forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩ := by
          apply Fin.ext; simp only [hx]
        have hh : hashHalf (Nat.xor target.val 1 % 2 ^ forsHeight) = hashHalf 0 := by
          funext output; rw [hx, hleft]; exact hashHalf_even _ output
        rw [hpair, hleaf, hh]
      · simp only [hb, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hsplit ⊢
        have hx : Nat.xor target.val 1 = 2 * (target.val / 2) + 1 := by
          change target.val ^^^ 1 = _
          rw [Nat.xor_one_of_even ⟨target.val / 2, by omega⟩]
          omega
        have hpair : leafPair (⟨Nat.xor target.val 1 % 2 ^ forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩ :
            FLeaf) = leafPair ⟨2 * (target.val / 2) % 2 ^ forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩ := by
          apply Fin.ext; simp only [leafPair, hx, hright, hleft]; omega
        have hleaf : (⟨Nat.xor target.val 1 % 2 ^ forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩ : FLeaf) =
            ⟨(2 * (target.val / 2) + 1) % 2 ^ forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩ := by
          apply Fin.ext; simp only [hx]
        have hh : hashHalf (Nat.xor target.val 1 % 2 ^ forsHeight) = hashHalf 1 := by
          funext output; rw [hx, hright]; exact hashHalf_odd _ output
        rw [hpair, hleaf, hh]
  | height + 1, node, hnode, k, hk => by
      have hsplit := div_two_pow_succ target.val (height + 1)
      rw [hnode] at hsplit
      simp only [forsSubtree, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
      by_cases hb : target.val.testBit (height + 1)
      · simp only [hb, ↓reduceIte] at hsplit ⊢
        rcases Nat.lt_or_eq_of_le hk with hk | rfl
        · rw [Function.update_of_ne (by omega)]
          exact eval_forsSubtree_path height _ hsplit k (by omega)
        · rw [Function.update_self, eval_forsSubtree_fst, hsplit]
          have hx : Nat.xor (2 * node + 1) 1 = 2 * node := by
            change (2 * node + 1) ^^^ 1 = 2 * node
            rw [Nat.xor_one_of_odd ⟨node, rfl⟩]
            omega
          rw [hx]
      · simp only [hb, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hsplit ⊢
        rcases Nat.lt_or_eq_of_le hk with hk | rfl
        · rw [Function.update_of_ne (by omega)]
          exact eval_forsSubtree_path height _ hsplit k (by omega)
        · rw [Function.update_self, eval_forsSubtree_fst, hsplit]
          have hx : Nat.xor (2 * node) 1 = 2 * node + 1 := by
            change (2 * node) ^^^ 1 = 2 * node + 1
            rw [Nat.xor_one_of_even ⟨node, by omega⟩]
          rw [hx]

theorem top_div (target : FLeaf) :
    target.val / 2 ^ (forsHeight - 2 + 1) = if target.val.testBit (forsHeight - 1) then 1 else 0 := by
  have ha := Params.forsHeight_ge
  rw [show forsHeight - 2 + 1 = forsHeight - 1 by omega]
  have h := div_two_pow_succ target.val (forsHeight - 1)
  rw [show forsHeight - 1 + 1 = forsHeight by omega, Nat.div_eq_of_lt target.isLt] at h
  omega

theorem eval_treeOpenOnce :
    evalWithAnswerFn f (treeOpenOnce parameter index κ target seed :
      OracleComp HashSpec ((Digest × Digest) × TreeOpening)) =
      ((forsNodeValue f parameter index κ seed (forsHeight - 1) 0,
        forsNodeValue f parameter index κ seed (forsHeight - 1) 1),
        evalWithAnswerFn f (Seeded.treeOpen parameter index κ target seed :
          OracleComp HashSpec TreeOpening)) := by
  have ha := Params.forsHeight_ge
  have htop := top_div target
  have hsucc : forsHeight - 2 + 1 = forsHeight - 1 := by omega
  rw [eval_treeOpen]
  simp only [treeOpenOnce, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rw [eval_forsSubtree_fst, eval_forsSubtree_fst, hsucc]
  by_cases hb : target.val.testBit (forsHeight - 1)
  · simp only [hb, ↓reduceIte] at htop ⊢
    refine Prod.ext rfl ?_
    show TreeOpening.mk _ _ = TreeOpening.mk _ _
    congr 1
    · exact eval_forsSubtree_secret f parameter index κ seed target _ 1 htop
    · funext level
      by_cases hl : level.val = forsHeight - 1
      · simp only [hl, Function.update_self]
        rw [← hsucc, htop]
        rfl
      · rw [Function.update_of_ne hl]
        exact eval_forsSubtree_path f parameter index κ seed target _ 1 htop _ (by omega)
  · simp only [hb, Bool.false_eq_true, ↓reduceIte] at htop ⊢
    refine Prod.ext rfl ?_
    show TreeOpening.mk _ _ = TreeOpening.mk _ _
    congr 1
    · exact eval_forsSubtree_secret f parameter index κ seed target _ 0 htop
    · funext level
      by_cases hl : level.val = forsHeight - 1
      · simp only [hl, Function.update_self]
        rw [← hsucc, htop]
        rfl
      · rw [Function.update_of_ne hl]
        exact eval_forsSubtree_path f parameter index κ seed target _ 0 htop _ (by omega)

theorem hashCalls_treeOpenOnce :
    hashCalls f (treeOpenOnce parameter index κ target seed :
      OracleComp HashSpec ((Digest × Digest) × TreeOpening)) = 2 * (5 * 2 ^ (forsHeight - 2) - 1) := by
  have ha := Params.forsHeight_ge
  simp only [treeOpenOnce, hashCalls_bind, hashCalls_pure, hashCalls_forsSubtree]
  rw [hashCalls_forsNode f parameter index κ seed _ _ (by omega),
    hashCalls_forsNode f parameter index κ seed _ _ (by omega)]
  omega

end Fors

section ForsOpen

variable (parameter : PublicParameter) (index : Index) (seed : MasterSeed)

theorem eval_forsOpenOnce (leaves : FTree → FLeaf) :
    evalWithAnswerFn f (forsOpenOnce parameter index leaves seed :
      OracleComp HashSpec (ForsKey × (FTree → TreeOpening))) =
      (evalWithAnswerFn f (Seeded.forsKey parameter index seed : OracleComp HashSpec ForsKey),
        evalWithAnswerFn f (Seeded.forsOpen parameter index leaves seed :
          OracleComp HashSpec (FTree → TreeOpening))) := by
  simp only [forsOpenOnce, Seeded.forsKey, Seeded.forsOpen, evalWithAnswerFn_bind,
    evalWithAnswerFn_pure, eval_sequenceFin, eval_treeOpenOnce]
  rfl

theorem hashCalls_forsOpenOnce (leaves : FTree → FLeaf) :
    hashCalls f (forsOpenOnce parameter index leaves seed :
      OracleComp HashSpec (ForsKey × (FTree → TreeOpening))) = forsKeyCost := by
  simp only [forsOpenOnce, hashCalls_bind, hashCalls_pure, hashCalls_sequenceFin,
    hashCalls_treeOpenOnce, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    Nat.add_zero, forsKeyCost]

end ForsOpen

/-! ### A full or layered key -/

section Full

variable (hfull : subtreeHeight = totalHeight)
include hfull

theorem keptHeight_of_full (lay : Layer) : keptHeight lay = layerHeight lay := by
  by_cases h : lay.val = 0
  · have htop : lay = topLayer := Fin.ext h
    subst htop
    rw [keptHeight_top, layerHeight_top, hfull, heightBelow_top]
    have := maxLayerHeight_add
    rw [heightBelow_top] at this
    omega
  · exact keptHeight_of_ne_top lay h

theorem keptPosition_of_full (parameter : PublicParameter) (lay : Layer) :
    keptPosition parameter lay = 0 := by
  unfold keptPosition subtreePosition
  split
  · rw [hfull, Nat.sub_self, pow_zero, Nat.mod_one]
  · rfl

theorem landed_of_full (parameter : PublicParameter) (index : Index) : Landed parameter index := by
  unfold Landed subtreePosition
  rw [hfull, Nat.div_eq_of_lt index.isLt, Nat.sub_self, pow_zero, Nat.mod_one]

theorem eval_treeRoot_of_full (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) :
    evalWithAnswerFn f (Seeded.treeRoot parameter lay tree seed : OracleComp HashSpec Digest) =
      evalWithAnswerFn f (treeNode parameter lay tree seed (layerHeight lay) 0 :
        OracleComp HashSpec Digest) := by
  simp only [Seeded.treeRoot, keptHeight_of_full hfull, Nat.sub_self, Seeded.spineNode,
    keptPosition_of_full hfull]

theorem eval_treePath_of_full (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) (leaf : LeafIndex) :
    evalWithAnswerFn f (Seeded.treePath parameter lay tree seed leaf :
      OracleComp HashSpec (Fin (layerHeight lay) → Digest)) = fun level =>
      evalWithAnswerFn f (treeNode parameter lay tree seed level.val
        (Nat.xor (leaf.val / 2 ^ level.val) 1) : OracleComp HashSpec Digest) := by
  funext level
  rw [eval_treePath, ite_eq_left (by rw [keptHeight_of_full hfull]; exact level.isLt)]
  rfl

/-- The message the layer one above `layerFromBottom j` signs: the root of that layer's tree on the
path. -/
theorem layerMessageValue_up (sk : Seeded.SecretKey) (index : Index) (j : Nat)
    (hj : j + 1 < numLayers) :
    layerMessageValue f sk index (layerFromBottom (j + 1)) = rootPayload (evalWithAnswerFn f
      (treeNode sk.parameter (layerFromBottom j) (treeIndexAt index (layerFromBottom j)) sk.seed
        (layerHeight (layerFromBottom j)) 0 : OracleComp HashSpec Digest)) := by
  have hbelow : (layerFromBottom (j + 1)).val + 1 < numLayers := by
    simp only [layerFromBottom]; omega
  have hlay : (⟨(layerFromBottom (j + 1)).val + 1, hbelow⟩ : Layer) = layerFromBottom j := by
    apply Fin.ext; simp only [layerFromBottom]; omega
  rw [layerMessageValue_above f sk index _ hbelow, hlay, eval_treeRoot_of_full f hfull]

end Full

theorem layerFromBottom_zero : layerFromBottom 0 = bottomLayer := rfl

theorem layerFromBottom_injective {i j : Nat} (hi : i < numLayers) (hj : j < numLayers)
    (h : layerFromBottom i = layerFromBottom j) : i = j := by
  have := congrArg Fin.val h
  simp only [layerFromBottom] at this
  omega

/-- Every layer is `layerFromBottom` of its distance to the bottom. -/
theorem layerFromBottom_rev (lay : Layer) : layerFromBottom (numLayers - 1 - lay.val) = lay := by
  apply Fin.ext; simp only [layerFromBottom]; omega

/-! ### The layers from the bottom up -/

section Layers

attribute [local irreducible] encodingAttemptLimit Seeded.otsSignFrom Seeded.otsSign firstEncoding
  ReferenceChoice.search

variable (sk : Seeded.SecretKey) (index : Index)

/-- The model's signature of layer `lay`. -/
noncomputable def modelLayer (lay : Layer) : Option (LayerSignature lay) :=
  evalWithAnswerFn f (Seeded.signLayer sk index lay : OracleComp HashSpec (Option (LayerSignature lay)))

theorem modelLayer_eq (lay : Layer) :
    modelLayer f sk index lay =
      (evalWithAnswerFn f (otsSign sk.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
        sk.seed (layerMessageValue f sk index lay) :
          OracleComp HashSpec (Option (Counter × (ChainIndex → Digest))))).map fun pair =>
        ⟨pair.1, pair.2, evalWithAnswerFn f (Seeded.treePath sk.parameter lay (treeIndexAt index lay)
          sk.seed (leafIndexAt index lay) : OracleComp HashSpec (Fin (layerHeight lay) → Digest))⟩ := by
  simp only [modelLayer, Seeded.signLayer, evalWithAnswerFn_bind, layerMessageValue]
  cases evalWithAnswerFn f (otsSign sk.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
      sk.seed (evalWithAnswerFn f (Seeded.layerMessage sk index lay : OracleComp HashSpec HashInput)) :
        OracleComp HashSpec (Option (Counter × (ChainIndex → Digest)))) <;>
    simp only [evalWithAnswerFn_pure, evalWithAnswerFn_bind, Option.map_none, Option.map_some]

variable (hfull : subtreeHeight = totalHeight)
include hfull

/-- What `signLayersUp` gives for the layers `j, j + 1, ...` from the bottom: the model's layers. -/
theorem eval_signLayersUp_some : ∀ remaining j, j + remaining = numLayers →
    ∀ data, evalWithAnswerFn f (signLayersUp sk.parameter sk.seed index remaining j
        (layerMessageValue f sk index (layerFromBottom j)) :
          OracleComp HashSpec (Option (Layer → LayerData))) = some data →
    ∀ i < remaining, modelLayer f sk index (layerFromBottom (j + i)) =
      some (layersOfData data (layerFromBottom (j + i)))
  | 0, _, _, _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | remaining + 1, j, hj, data, hdata, i, hi => by
      have hjl : j < numLayers := by omega
      set lay := layerFromBottom j with hlay
      simp only [signLayersUp, evalWithAnswerFn_bind] at hdata
      rcases hots : evalWithAnswerFn f (otsSign sk.parameter lay (treeIndexAt index lay)
          (leafIndexAt index lay) sk.seed (layerMessageValue f sk index lay) :
            OracleComp HashSpec (Option (Counter × (ChainIndex → Digest)))) with _ | ⟨counter, values⟩
      · rw [← hlay, hots] at hdata
        simp only [evalWithAnswerFn_pure] at hdata
        cases hdata
      rw [← hlay, hots] at hdata
      simp only [evalWithAnswerFn_bind] at hdata
      set built := evalWithAnswerFn f (treeNodeWithPath sk.parameter lay (treeIndexAt index lay)
        sk.seed (leafIndexAt index lay).val (layerHeight lay) 0 :
          OracleComp HashSpec (Digest × (Nat → Digest))) with hbuilt
      rcases hrest : evalWithAnswerFn f (signLayersUp sk.parameter sk.seed index remaining (j + 1)
          (rootPayload built.1) : OracleComp HashSpec (Option (Layer → LayerData))) with _ | rest
      · rw [hrest] at hdata
        simp only [evalWithAnswerFn_pure, Option.map_none] at hdata
        cases hdata
      rw [hrest] at hdata
      simp only [evalWithAnswerFn_pure, Option.map_some, Option.some.injEq] at hdata
      subst hdata
      rcases i with _ | i
      · -- the layer `j` itself
        rw [Nat.add_zero, ← hlay, modelLayer_eq, hots]
        simp only [Option.map_some, layersOfData, Function.update_self]
        congr 2
        rw [eval_treePath_of_full f hfull]
        funext level
        rw [hbuilt, eval_treeNodeWithPath_snd f sk.parameter lay (treeIndexAt index lay) sk.seed _
          (layerHeight lay) 0 (Nat.div_eq_of_lt (leafIndexAt_lt index lay)) level.val level.isLt]
      · -- the layers above
        have hj1 : j + 1 < numLayers := by omega
        have hmsg : rootPayload built.1 = layerMessageValue f sk index (layerFromBottom (j + 1)) := by
          rw [layerMessageValue_up f hfull sk index j hj1, hbuilt, eval_treeNodeWithPath_fst]
        rw [hmsg] at hrest
        have hih := eval_signLayersUp_some remaining (j + 1) (by omega) rest hrest i (by omega)
        rw [show j + (i + 1) = j + 1 + i by omega, hih]
        simp only [layersOfData]
        rw [Function.update_of_ne]
        intro heq
        have := layerFromBottom_injective (by omega) hjl heq
        omega

/-- `signLayersUp` fails exactly when some layer's search fails. -/
theorem eval_signLayersUp_none : ∀ remaining j, j + remaining = numLayers →
    evalWithAnswerFn f (signLayersUp sk.parameter sk.seed index remaining j
        (layerMessageValue f sk index (layerFromBottom j)) :
          OracleComp HashSpec (Option (Layer → LayerData))) = none →
    ∃ i < remaining, modelLayer f sk index (layerFromBottom (j + i)) = none
  | 0, _, _, hnone => by
      simp only [signLayersUp, evalWithAnswerFn_pure] at hnone
      cases hnone
  | remaining + 1, j, hj, hnone => by
      have hjl : j < numLayers := by omega
      set lay := layerFromBottom j with hlay
      simp only [signLayersUp, evalWithAnswerFn_bind] at hnone
      rcases hots : evalWithAnswerFn f (otsSign sk.parameter lay (treeIndexAt index lay)
          (leafIndexAt index lay) sk.seed (layerMessageValue f sk index lay) :
            OracleComp HashSpec (Option (Counter × (ChainIndex → Digest)))) with _ | ⟨counter, values⟩
      · refine ⟨0, Nat.zero_lt_succ _, ?_⟩
        rw [Nat.add_zero, ← hlay, modelLayer_eq, hots, Option.map_none]
      rw [← hlay, hots] at hnone
      simp only [evalWithAnswerFn_bind] at hnone
      set built := evalWithAnswerFn f (treeNodeWithPath sk.parameter lay (treeIndexAt index lay)
        sk.seed (leafIndexAt index lay).val (layerHeight lay) 0 :
          OracleComp HashSpec (Digest × (Nat → Digest))) with hbuilt
      rcases hrest : evalWithAnswerFn f (signLayersUp sk.parameter sk.seed index remaining (j + 1)
          (rootPayload built.1) : OracleComp HashSpec (Option (Layer → LayerData))) with _ | rest
      · rcases remaining with _ | remaining
        · simp only [signLayersUp, evalWithAnswerFn_pure] at hrest
          cases hrest
        have hj1 : j + 1 < numLayers := by omega
        have hmsg : rootPayload built.1 = layerMessageValue f sk index (layerFromBottom (j + 1)) := by
          rw [layerMessageValue_up f hfull sk index j hj1, hbuilt, eval_treeNodeWithPath_fst]
        rw [hmsg] at hrest
        obtain ⟨i, hi, hmodel⟩ := eval_signLayersUp_none (remaining + 1) (j + 1) (by omega) hrest
        exact ⟨i + 1, by omega, by rw [show j + (i + 1) = j + 1 + i by omega]; exact hmodel⟩
      · rw [hrest] at hnone
        simp only [evalWithAnswerFn_pure, Option.map_some] at hnone
        cases hnone

/-- The crate's signer's layers are the model's. -/
theorem eval_signLayersUp :
    (evalWithAnswerFn f (signLayersUp sk.parameter sk.seed index numLayers 0
        (rootsPayload (evalWithAnswerFn f (Seeded.forsKey sk.parameter index sk.seed :
          OracleComp HashSpec ForsKey))) :
          OracleComp HashSpec (Option (Layer → LayerData)))).map layersOfData =
      allSome fun lay => modelLayer f sk index lay := by
  rw [← layerMessageValue_bottom f sk index, ← layerFromBottom_zero]
  rcases hres : evalWithAnswerFn f (signLayersUp sk.parameter sk.seed index numLayers 0
      (layerMessageValue f sk index (layerFromBottom 0)) :
        OracleComp HashSpec (Option (Layer → LayerData))) with _ | data
  · obtain ⟨i, hi, hnone⟩ := eval_signLayersUp_none f sk index hfull numLayers 0 (by omega) hres
    rw [Option.map_none]
    unfold allSome
    rw [dite_eq_right]
    intro hall
    have := hall (layerFromBottom (0 + i))
    simp only [hnone, Option.isSome_none, Bool.false_eq_true] at this
  · have hsome := eval_signLayersUp_some f sk index hfull numLayers 0 (by omega) data hres
    have hlay (lay : Layer) : modelLayer f sk index lay = some (layersOfData data lay) := by
      have h := hsome (numLayers - 1 - lay.val) (by omega)
      rwa [Nat.zero_add, layerFromBottom_rev] at h
    rw [Option.map_some]
    unfold allSome
    rw [dite_eq_left (fun lay => by simp only [hlay, Option.isSome_some])]
    congr 1
    funext lay
    simp only [hlay, Option.get_some]

/-- **The crate's signature is the model's**, for a full or layered key: the model's assembly at
the randomizer the crate derives. -/
theorem eval_sign_eq_finishSign (message : Message) :
    evalWithAnswerFn f (Seeded.sign sk message : OracleComp HashSpec (Option Signature)) =
      evalWithAnswerFn f (Seeded.finishSign sk message
        (evalWithAnswerFn f (deriveRandomizer sk.parameter sk.seed message :
          OracleComp HashSpec (Randomness × Randomness))).1) := by
  simp only [Seeded.sign, Seeded.finishSign, evalWithAnswerFn_bind, eval_forsOpenOnce,
    sequenceLayers, Completeness.eval_sequenceDep]
  generalize (evalWithAnswerFn f (deriveRandomizer sk.parameter sk.seed message :
    OracleComp HashSpec (Randomness × Randomness))).1 = randomness
  generalize digestIndex (evalWithAnswerFn f (messageDigest sk.parameter sk.root message randomness :
    OracleComp HashSpec MessageDigest)) = index
  have h := eval_signLayersUp f sk index hfull
  simp only [modelLayer] at h
  rw [← h]
  rcases evalWithAnswerFn f (signLayersUp sk.parameter sk.seed index numLayers 0
      (rootsPayload (evalWithAnswerFn f (Seeded.forsKey sk.parameter index sk.seed :
        OracleComp HashSpec ForsKey))) :
        OracleComp HashSpec (Option (Layer → LayerData))) with _ | data <;> rfl

/-- Whether the search of layer `lay` succeeds, on its message. -/
noncomputable def layerFoundUp (lay : Layer) : Bool :=
  (firstEncoding f sk.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
    (layerMessageValue f sk index lay) encodingAttemptLimit 0).isSome

/-- The hash calls of layer `lay` of the crate's signer: the counter search, and on success the
chain values and the whole tree, built once. -/
noncomputable def layerCostUp (lay : Layer) : Nat :=
  hashCalls f (ReferenceChoice.search sk.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
    (layerMessageValue f sk index lay) encodingAttemptLimit 0) +
    if layerFoundUp f sk index lay then 160 + (226 * 2 ^ layerHeight lay - 1) else 0

theorem hashCalls_signLayersUp (remaining : Nat) : ∀ j, j + remaining = numLayers →
    hashCalls f (signLayersUp sk.parameter sk.seed index remaining j
        (layerMessageValue f sk index (layerFromBottom j)) :
          OracleComp HashSpec (Option (Layer → LayerData))) =
      seqCost (fun i : Fin remaining => layerFoundUp f sk index (layerFromBottom (j + i.val)))
        (fun i => layerCostUp f sk index (layerFromBottom (j + i.val))) := by
  induction remaining with
  | zero => intro j _; simp only [signLayersUp, hashCalls_pure, seqCost]
  | succ remaining ih =>
      intro j hj
      set lay := layerFromBottom j with hlay
      have hhead : seqCost (fun i : Fin (remaining + 1) =>
            layerFoundUp f sk index (layerFromBottom (j + i.val)))
          (fun i => layerCostUp f sk index (layerFromBottom (j + i.val))) =
          layerCostUp f sk index lay + if layerFoundUp f sk index lay then
            seqCost (fun i : Fin remaining => layerFoundUp f sk index (layerFromBottom (j + 1 + i.val)))
              (fun i => layerCostUp f sk index (layerFromBottom (j + 1 + i.val))) else 0 := by
        have hshift : ∀ i : Fin remaining, j + i.succ.val = j + 1 + i.val := by
          intro i; simp only [Fin.val_succ]; omega
        simp only [seqCost, Fin.val_zero, Nat.add_zero, hshift, ← hlay]
      obtain ⟨found, hfound⟩ : ∃ found, firstEncoding f sk.parameter lay (treeIndexAt index lay)
          (leafIndexAt index lay) (layerMessageValue f sk index lay) encodingAttemptLimit 0 = found :=
        ⟨_, rfl⟩
      have hf : layerFoundUp f sk index lay = found.isSome := by rw [← hfound]; rfl
      have hc : layerCostUp f sk index lay =
          hashCalls f (ReferenceChoice.search sk.parameter lay (treeIndexAt index lay)
            (leafIndexAt index lay) (layerMessageValue f sk index lay) encodingAttemptLimit 0) +
          if found.isSome then 160 + (226 * 2 ^ layerHeight lay - 1) else 0 := by
        rw [← hfound]; rfl
      rw [hhead, hc, hf, signLayersUp, hashCalls_bind]
      simp only [← hlay]
      rw [show (otsSign sk.parameter lay (treeIndexAt index lay) (leafIndexAt index lay) sk.seed
          (layerMessageValue f sk index lay) : OracleComp HashSpec _) = otsSignFrom sk.parameter lay
          (treeIndexAt index lay) (leafIndexAt index lay) sk.seed (layerMessageValue f sk index lay)
          encodingAttemptLimit 0 from by rw [otsSign], hashCalls_otsSignFrom_search,
        otsSignFrom_eq_firstEncoding, hfound]
      cases found with
      | none => simp only [Option.map_none, hashCalls_pure, Option.isSome_none, Bool.false_eq_true,
          ↓reduceIte, Nat.add_zero]
      | some pair =>
          simp only [Option.map_some, hashCalls_bind, hashCalls_treeNodeWithPath, hashCalls_treeNode,
            Option.isSome_some, ↓reduceIte, hashCalls_pure]
          rcases remaining with _ | remaining
          · simp only [signLayersUp, seqCost, hashCalls_pure]
            omega
          · have hj1 : j + 1 < numLayers := by omega
            have hmsg : rootPayload (evalWithAnswerFn f (treeNodeWithPath sk.parameter lay
                (treeIndexAt index lay) sk.seed (leafIndexAt index lay).val (layerHeight lay) 0 :
                  OracleComp HashSpec (Digest × (Nat → Digest)))).1 =
                layerMessageValue f sk index (layerFromBottom (j + 1)) := by
              rw [layerMessageValue_up f hfull sk index j hj1, eval_treeNodeWithPath_fst]
            rw [hmsg, ih (j + 1) (by omega)]
            omega

/-- **The crate signer's hash calls**: the randomizer, the digest, each FORS tree once, then the
layers from the bottom up until the first failed search. -/
theorem hashCalls_sign (message : Message) :
    hashCalls f (Seeded.sign sk message : OracleComp HashSpec (Option Signature)) =
      1 + digestCalls + forsKeyCost +
        seqCost (fun i : Fin numLayers => layerFoundUp f sk (digestIndex (evalWithAnswerFn f
          (messageDigest sk.parameter sk.root message (evalWithAnswerFn f (deriveRandomizer
            sk.parameter sk.seed message : OracleComp HashSpec (Randomness × Randomness))).1 :
              OracleComp HashSpec MessageDigest))) (layerFromBottom i.val))
          (fun i => layerCostUp f sk (digestIndex (evalWithAnswerFn f
          (messageDigest sk.parameter sk.root message (evalWithAnswerFn f (deriveRandomizer
            sk.parameter sk.seed message : OracleComp HashSpec (Randomness × Randomness))).1 :
              OracleComp HashSpec MessageDigest))) (layerFromBottom i.val)) := by
  simp only [Seeded.sign, hashCalls_bind, hashCalls_messageDigest, hashCalls_forsOpenOnce,
    eval_forsOpenOnce]
  have hderive : hashCalls f (deriveRandomizer sk.parameter sk.seed message :
      OracleComp HashSpec (Randomness × Randomness)) = 1 := by
    simp only [deriveRandomizer, hashCalls_bind, hashCalls_oracleHash, hashCalls_pure]
  rw [hderive]
  generalize (evalWithAnswerFn f (deriveRandomizer sk.parameter sk.seed message :
    OracleComp HashSpec (Randomness × Randomness))).1 = randomness
  generalize digestIndex (evalWithAnswerFn f (messageDigest sk.parameter sk.root message randomness :
    OracleComp HashSpec MessageDigest)) = index
  rw [← layerMessageValue_bottom f sk index, ← layerFromBottom_zero,
    hashCalls_signLayersUp f sk index hfull numLayers 0 (by omega)]
  simp only [Nat.zero_add]
  split <;> simp only [hashCalls_pure] <;> omega

end Layers

end FORS.Security.GraphView
