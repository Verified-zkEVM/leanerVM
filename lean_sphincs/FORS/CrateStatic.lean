import FORS.Crate
import FORS.GraphView.Cost

/-!
# The crate's algorithms against FORS's, on a fixed answer function

On every answer function `f`, the crate's key generation and signer (`Crate.keygen`,
`Crate.sign`, `Crate.lean`) give the public key and the signatures of FORS's
(`Seeded.keygen`, `Seeded.sign`, upstream's), the signer with the key FORS's key generation gives
on `f`, and make at least FORS's hash calls (`eval_keygen`, `hashCalls_keygen`, `eval_sign`,
`hashCalls_sign`). The crate builds each tree once, level by level, where FORS's signer computes
the siblings of a path and folds the path again; the crate also rebuilds the top tree at each
signature, which pays for FORS's landing call and for the one call per lower layer by which
FORS's recovery of a root exceeds a tree built once.
-/

open OracleComp

namespace FORS.Crate

variable [Params]

open Concrete Completeness Security.Prefix Security.GraphView

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] digestAttemptLimit encodingAttemptLimit

variable (f : QueryImpl HashSpec Id)

/-! ### Lists of computations -/

theorem eval_mapM {α β : Type} (φ : α → OracleComp HashSpec β) (l : List α) :
    evalWithAnswerFn f (l.mapM φ) = l.map fun a => evalWithAnswerFn f (φ a) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.mapM_cons, evalWithAnswerFn_bind, evalWithAnswerFn_pure, ih,
      List.map_cons]

theorem hashCalls_mapM {α β : Type} (φ : α → OracleComp HashSpec β) (l : List α) :
    hashCalls f (l.mapM φ) = (l.map fun a => hashCalls f (φ a)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.mapM_cons, hashCalls_bind, hashCalls_pure, ih, List.map_cons,
      List.sum_cons, Nat.add_zero]

theorem sum_map_const {α : Type} (l : List α) (c : Nat) (g : α → Nat) (h : ∀ a ∈ l, g a = c) :
    (l.map g).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, h a List.mem_cons_self,
        ih fun b hb => h b (List.mem_cons_of_mem _ hb)]
      ring

/-! ### Merkle levels -/

theorem levelNode_cons_zero (below : List Digest) (rest : List (List Digest)) (j : Nat) :
    levelNode (below :: rest) 0 j = below.getD j 0 := rfl

theorem levelNode_cons_succ (below : List Digest) (rest : List (List Digest)) (z j : Nat) :
    levelNode (below :: rest) (z + 1) j = levelNode rest z j := rfl

section Merkle

variable (node : Nat → Nat → HashInput → OracleComp HashSpec Digest) (T : Nat → Nat → Digest)
  (H : Nat)

/-- The levels built from honest nodes are the honest nodes: node `j` of level `z` of the levels
over the nodes of height `height` is the node `j` at height `height + z`. -/
theorem levelNode_merkleLevelsFrom
    (hnode : ∀ h j, h < H → evalWithAnswerFn f (node (h + 1) j
      (nodePayload (T h (2 * j)) (T h (2 * j + 1)))) = T (h + 1) j) :
    ∀ remaining height (below : List Digest), height + remaining ≤ H →
      below.length = 2 ^ remaining → (∀ i < below.length, below.getD i 0 = T height i) →
      ∀ z ≤ remaining, ∀ j < 2 ^ (remaining - z),
        levelNode (evalWithAnswerFn f (merkleLevelsFrom node height below remaining)) z j =
          T (height + z) j := by
  intro remaining
  induction remaining with
  | zero =>
      intro height below _ hlen hbelow z hz j hj
      obtain rfl : z = 0 := by omega
      simp only [merkleLevelsFrom, evalWithAnswerFn_pure]
      rw [levelNode_cons_zero, Nat.add_zero]
      exact hbelow j (by simp at hj; omega)
  | succ remaining ih =>
      intro height below hH hlen hbelow z hz j hj
      simp only [merkleLevelsFrom, evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_mapM]
      cases z with
      | zero =>
          rw [levelNode_cons_zero, Nat.add_zero]
          exact hbelow j (by rw [hlen]; exact hj)
      | succ z =>
          rw [levelNode_cons_succ]
          have hhalf : below.length / 2 = 2 ^ remaining := by rw [hlen, pow_succ]; omega
          rw [show height + (z + 1) = height + 1 + z by omega]
          exact ih (height + 1) _ (by omega) (by simp [hhalf])
            (fun i hi => by
              simp only [List.length_map, List.length_range] at hi
              rw [List.getD_eq_getElem _ _ (by simpa using hi)]
              simp only [List.getElem_map, List.getElem_range]
              have h1 : 2 * i < below.length := by omega
              have h2 : 2 * i + 1 < below.length := by omega
              rw [hbelow _ h1, hbelow _ h2]
              exact hnode height i (by omega))
            z (by omega) j (by simpa [Nat.add_sub_add_right] using hj)

/-- The levels cost one call per node above the leaves. -/
theorem hashCalls_merkleLevelsFrom
    (hcost : ∀ h j p, h ≤ H → 0 < h → hashCalls f (node h j p) = 1) :
    ∀ remaining height (below : List Digest), height + remaining ≤ H →
      below.length = 2 ^ remaining →
        hashCalls f (merkleLevelsFrom node height below remaining) = 2 ^ remaining - 1 := by
  intro remaining
  induction remaining with
  | zero => intro _ _ _ _; rfl
  | succ remaining ih =>
      intro height below hH hlen
      have hhalf : below.length / 2 = 2 ^ remaining := by rw [hlen, pow_succ]; omega
      simp only [merkleLevelsFrom, hashCalls_bind, hashCalls_pure, hashCalls_mapM, eval_mapM,
        Nat.add_zero]
      rw [sum_map_const _ 1 _ (fun j _ => hcost _ _ _ (by omega) (by omega)),
        ih (height + 1) _ (by omega) (by simp [hhalf])]
      simp only [List.length_range, hhalf, Nat.mul_one, pow_succ]
      have := Nat.two_pow_pos remaining
      omega

end Merkle

theorem levelNode_merkleLevels (node : Nat → Nat → HashInput → OracleComp HashSpec Digest)
    (T : Nat → Nat → Digest) (H : Nat)
    (hnode : ∀ h j, h < H → evalWithAnswerFn f (node (h + 1) j
      (nodePayload (T h (2 * j)) (T h (2 * j + 1)))) = T (h + 1) j)
    (leaves : List Digest) (hlen : leaves.length = 2 ^ H)
    (hleaves : ∀ i < leaves.length, leaves.getD i 0 = T 0 i) (z : Nat) (hz : z ≤ H)
    (j : Nat) (hj : j < 2 ^ (H - z)) :
    levelNode (evalWithAnswerFn f (merkleLevels node leaves H)) z j = T z j := by
  have := levelNode_merkleLevelsFrom f node T H hnode H 0 leaves (by omega) hlen hleaves z hz j hj
  rwa [Nat.zero_add] at this

theorem getD_map_range {β : Type} (g : Nat → β) (n i : Nat) (d : β) (hi : i < n) :
    ((List.range n).map g).getD i d = g i := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

/-! ### A layer's tree -/

theorem eval_otsPublicLeaf (key : ExpandedKey) (lay : Layer) (tree : TreeIndex) (i : Nat) :
    evalWithAnswerFn f (otsPublicLeaf key lay tree (leafOfNat i) : OracleComp HashSpec Digest) =
      node f key.publicSeed lay tree key.secretSeed 0 i := by
  simp only [otsPublicLeaf, Completeness.node, Seeded.treeNode, evalWithAnswerFn_bind]

theorem levelNode_treeLevels (key : ExpandedKey) (lay : Layer) (tree : TreeIndex) (z : Nat)
    (hz : z ≤ layerHeight lay) (j : Nat) (hj : j < 2 ^ (layerHeight lay - z)) :
    levelNode (evalWithAnswerFn f (treeLevels key lay tree : OracleComp HashSpec _)) z j =
      node f key.publicSeed lay tree key.secretSeed z j := by
  simp only [treeLevels, evalWithAnswerFn_bind]
  refine levelNode_merkleLevels f _ _ (layerHeight lay) (fun h j _ => ?_) _ (by simp [eval_mapM])
    (fun i hi => ?_) z hz j hj
  · rw [eval_tweakableHash, node_succ]
  · simp only [eval_mapM, List.length_map, List.length_range] at hi ⊢
    rw [getD_map_range _ _ _ _ hi, eval_otsPublicLeaf]

theorem hashCalls_otsPublicLeaf (key : ExpandedKey) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) :
    hashCalls f (otsPublicLeaf key lay tree leaf : OracleComp HashSpec Digest) = 257 := by
  simp only [otsPublicLeaf, hashCalls_bind, hashCalls_oneTimePublicKey, leafHash,
    hashCalls_tweakableHash]

theorem hashCalls_treeLevels (key : ExpandedKey) (lay : Layer) (tree : TreeIndex) :
    hashCalls f (treeLevels key lay tree : OracleComp HashSpec _) = 258 * 2 ^ layerHeight lay - 1 := by
  simp only [treeLevels, hashCalls_bind, hashCalls_mapM, merkleLevels]
  rw [sum_map_const _ 257 _ (fun _ _ => hashCalls_otsPublicLeaf f _ _ _ _),
    hashCalls_merkleLevelsFrom f _ (layerHeight lay) (fun _ _ _ _ _ => hashCalls_tweakableHash _ _ _ _)
      _ 0 _ (by omega) (by simp [eval_mapM])]
  simp only [List.length_range]
  have := Nat.two_pow_pos (layerHeight lay)
  omega

/-! ### FORS -/

theorem xor_one_lt {x n : Nat} (hn : 0 < n) (hx : x < 2 ^ n) : x ^^^ 1 < 2 ^ n :=
  Nat.xor_lt_two_pow hx (Nat.one_lt_two_pow (by omega))

theorem shiftRight_xor_lt {leaf H z : Nat} (hleaf : leaf < 2 ^ H) (hz : z < H) :
    (leaf >>> z) ^^^ 1 < 2 ^ (H - z) := by
  refine xor_one_lt (by omega) ?_
  rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add,
    Nat.sub_add_cancel hz.le]
  exact hleaf

theorem forsLeafOfNat_val (leaf : FLeaf) : forsLeafOfNat leaf.val = leaf :=
  Fin.ext (Nat.mod_eq_of_lt leaf.isLt)

theorem eval_forsNodeHash (key : ExpandedKey) (index : Index) (κ : FTree) (h j : Nat)
    (hh : h < forsHeight) :
    evalWithAnswerFn f (forsNodeHash key.publicSeed index κ (h + 1) j
      (nodePayload (forsNodeValue f key.publicSeed index κ key.secretSeed h (2 * j))
        (forsNodeValue f key.publicSeed index κ key.secretSeed h (2 * j + 1))) :
        OracleComp HashSpec Digest) =
      forsNodeValue f key.publicSeed index κ key.secretSeed (h + 1) j := by
  rw [forsNodeValue_succ f _ _ _ _ _ _ hh]
  simp only [forsNodeHash, Nat.add_sub_cancel, dite_eq_left hh, eval_tweakableHash]
  rfl

theorem eval_forsLeaf (key : ExpandedKey) (index : Index) (κ : FTree) (s : Nat) :
    evalWithAnswerFn f (forsLeafHash key.publicSeed index κ (forsLeafOfNat s)
      (evalWithAnswerFn f (prf key (.fors index κ (forsLeafOfNat s)) : OracleComp HashSpec Digest)) :
        OracleComp HashSpec Digest) =
      forsNodeValue f key.publicSeed index κ key.secretSeed 0 s := by
  simp only [forsNodeValue, Seeded.forsNode, Seeded.forsSecret, evalWithAnswerFn_bind, prf]
  rfl

theorem eval_forsTreeOpen (key : ExpandedKey) (index : Index) (κ : FTree) (leaf : FLeaf) :
    evalWithAnswerFn f (forsTreeOpen key index κ leaf : OracleComp HashSpec (Digest × TreeOpening)) =
      (rootValue f key.publicSeed index key.secretSeed κ,
        evalWithAnswerFn f (Seeded.treeOpen key.publicSeed index κ leaf key.secretSeed :
          OracleComp HashSpec TreeOpening)) := by
  have ha := forsHeight_pos
  have hlevels : ∀ z ≤ forsHeight, ∀ j < 2 ^ (forsHeight - z),
      levelNode (evalWithAnswerFn f (merkleLevels (forsNodeHash key.publicSeed index κ)
        ((List.range (2 ^ forsHeight)).map fun s => evalWithAnswerFn f
          (forsLeafHash key.publicSeed index κ (forsLeafOfNat s)
            (((List.range (2 ^ forsHeight)).map fun s => evalWithAnswerFn f
              (prf key (.fors index κ (forsLeafOfNat s)) : OracleComp HashSpec Digest)).getD s 0) :
            OracleComp HashSpec Digest)) forsHeight : OracleComp HashSpec _)) z j =
        forsNodeValue f key.publicSeed index κ key.secretSeed z j := by
    intro z hz j hj
    refine levelNode_merkleLevels f _ _ forsHeight (fun h j hh => eval_forsNodeHash f key index κ h j hh)
      _ (by simp) (fun i hi => ?_) z hz j hj
    simp only [List.length_map, List.length_range] at hi
    rw [getD_map_range _ _ _ _ hi, getD_map_range _ _ _ _ hi, eval_forsLeaf]
  simp only [forsTreeOpen, evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_mapM, eval_treeOpen]
  refine Prod.ext ?_ ?_
  · exact hlevels forsHeight le_rfl 0 (by simp)
  · simp only
    congr 1
    · rw [getD_map_range _ _ _ _ leaf.isLt, forsLeafOfNat_val]
      simp only [forsSecretValue, Seeded.forsSecret, prf]
    · funext z
      rw [hlevels z.val z.isLt.le _ (shiftRight_xor_lt leaf.isLt z.isLt), Nat.shiftRight_eq_div_pow]
      rfl

theorem hashCalls_forsTreeOpen (key : ExpandedKey) (index : Index) (κ : FTree) (leaf : FLeaf) :
    hashCalls f (forsTreeOpen key index κ leaf : OracleComp HashSpec (Digest × TreeOpening)) =
      3 * 2 ^ forsHeight - 1 := by
  simp only [forsTreeOpen, hashCalls_bind, hashCalls_mapM, hashCalls_pure, merkleLevels,
    Nat.add_zero]
  rw [sum_map_const _ 1 _ (fun _ _ => by simp [prf]),
    sum_map_const _ 1 _ (fun _ _ => by simp [forsLeafHash]),
    hashCalls_merkleLevelsFrom f _ forsHeight (fun h j p hh h0 => by
      simp only [forsNodeHash, dite_eq_left (show h - 1 < forsHeight by omega),
        hashCalls_tweakableHash]) _ 0 _ (by omega) (by simp [eval_mapM])]
  simp only [List.length_range, Nat.mul_one]
  have := Nat.two_pow_pos forsHeight
  omega

theorem eval_forsOpen (key : ExpandedKey) (index : Index) (leaves : FTree → FLeaf) :
    evalWithAnswerFn f (forsOpen key index leaves : OracleComp HashSpec (Digest × (FTree → TreeOpening))) =
      (evalWithAnswerFn f (Seeded.forsKey key.publicSeed index key.secretSeed : OracleComp HashSpec Digest),
        evalWithAnswerFn f (Seeded.forsOpen key.publicSeed index leaves key.secretSeed :
          OracleComp HashSpec (FTree → TreeOpening))) := by
  simp only [forsOpen, evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_sequenceFin,
    eval_forsTreeOpen, forsKey_eq, Seeded.forsOpen]

theorem hashCalls_forsOpen (key : ExpandedKey) (index : Index) (leaves : FTree → FLeaf) :
    hashCalls f (forsOpen key index leaves : OracleComp HashSpec (Digest × (FTree → TreeOpening))) =
      forsTrees * (3 * 2 ^ forsHeight - 1) + 1 := by
  simp only [forsOpen, hashCalls_bind, hashCalls_sequenceFin, hashCalls_forsTreeOpen,
    hashCalls_forsPublicKey, hashCalls_pure, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, Nat.add_zero]

/-! ### Key generation -/

/-- FORS's key keeps every tree whole (`Params.full`). -/
theorem keptHeight_full (lay : Layer) : keptHeight lay = layerHeight lay := by
  by_cases h : lay.val = 0
  · have hl : lay = topLayer := Fin.ext h
    subst hl
    rw [keptHeight_top, layerHeight_top, Params.full]
    have := maxLayerHeight_add
    omega
  · exact keptHeight_of_ne_top lay h

theorem keptPosition_full (parameter : PublicParameter) (lay : Layer) :
    keptPosition parameter lay = 0 := by
  unfold keptPosition
  split
  · exact subtreePosition_eq_zero parameter
  · rfl

theorem eval_treeRoot_full (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) :
    evalWithAnswerFn f (Seeded.treeRoot parameter lay tree seed : OracleComp HashSpec Digest) =
      node f parameter lay tree seed (layerHeight lay) 0 := by
  simp only [Seeded.treeRoot, keptHeight_full, Nat.sub_self, Seeded.spineNode, keptPosition_full]
  rfl

/-- The key FORS's key generation gives, as the crate's expanded key. -/
def keyOf (sk : Seeded.SecretKey) : ExpandedKey := ⟨sk.seed, sk.prf, sk.parameter⟩

theorem eval_expandKey (seed : MasterSeed) :
    evalWithAnswerFn f (expandKey seed : OracleComp HashSpec ExpandedKey) =
      keyOf (evalWithAnswerFn f (Seeded.keygen seed)).2 := by
  simp only [expandKey, Seeded.keygen, Seeded.keygenFromSeed, derivePublicSeed, derivePrf,
    evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_oracleHash, keyOf]

theorem eval_keygen_snd_root (seed : MasterSeed) :
    (evalWithAnswerFn f (Seeded.keygen seed)).2.root =
      node f (evalWithAnswerFn f (Seeded.keygen seed)).2.parameter topLayer rootTree seed
        (layerHeight topLayer) 0 := by
  simp only [Seeded.keygen, Seeded.keygenFromSeed, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
    eval_treeRoot_full]

theorem eval_keygen_snd_seed (seed : MasterSeed) :
    (evalWithAnswerFn f (Seeded.keygen seed)).2.seed = seed := by
  simp only [Seeded.keygen, Seeded.keygenFromSeed, evalWithAnswerFn_bind, evalWithAnswerFn_pure]

theorem eval_keygen_fst (seed : MasterSeed) :
    (evalWithAnswerFn f (Seeded.keygen seed)).1 =
      ⟨(evalWithAnswerFn f (Seeded.keygen seed)).2.root,
        (evalWithAnswerFn f (Seeded.keygen seed)).2.parameter⟩ := by
  simp only [Seeded.keygen, Seeded.keygenFromSeed, evalWithAnswerFn_bind, evalWithAnswerFn_pure]

/-- The top tree's root, from its levels, is the public root. -/
theorem levelNode_top (seed : MasterSeed) :
    levelNode (evalWithAnswerFn f (treeLevels (keyOf (evalWithAnswerFn f (Seeded.keygen seed)).2)
        topLayer rootTree : OracleComp HashSpec _)) (layerHeight topLayer) 0 =
      (evalWithAnswerFn f (Seeded.keygen seed)).2.root := by
  rw [levelNode_treeLevels f _ _ _ _ le_rfl 0 (by simp), eval_keygen_snd_root]
  simp only [keyOf, eval_keygen_snd_seed]

/-- **Key generation**: the crate's public key is FORS's, its secret key `SK.seed`. -/
theorem eval_keygen (seed : MasterSeed) :
    evalWithAnswerFn f (keygen seed : OracleComp HashSpec (PublicKey × MasterSeed)) =
      ((evalWithAnswerFn f (Seeded.keygen seed)).1, seed) := by
  simp only [keygen, keygenInternal, evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_expandKey,
    levelNode_top, eval_keygen_fst]
  rfl

theorem hashCalls_expandKey (seed : MasterSeed) :
    hashCalls f (expandKey seed : OracleComp HashSpec ExpandedKey) = 2 := by
  simp only [expandKey, hashCalls_bind, hashCalls_oracleHash, hashCalls_pure]

/-- **Key generation's hash calls**: the crate makes FORS's: the expansion and the top tree. -/
theorem hashCalls_keygen_eq (seed : MasterSeed) :
    hashCalls f (keygen seed : OracleComp HashSpec (PublicKey × MasterSeed)) =
      hashCalls f (Seeded.keygen seed) := by
  rw [Seeded.keygen, hashCalls_keygenFromSeed, keygenHashCost]
  simp only [keygen, keygenInternal, hashCalls_bind, hashCalls_expandKey, hashCalls_treeLevels,
    hashCalls_pure, keptHeight_full, Nat.sub_self]
  have := Nat.two_pow_pos (layerHeight topLayer)
  omega

theorem hashCalls_keygen (seed : MasterSeed) :
    hashCalls f (Seeded.keygen seed) ≤
      hashCalls f (keygen seed : OracleComp HashSpec (PublicKey × MasterSeed)) :=
  (hashCalls_keygen_eq f seed).ge

/-! ### A layer -/

theorem leafIndexAt_lt (index : Index) (lay : Layer) :
    (leafIndexAt index lay).val < 2 ^ layerHeight lay :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

/-- The crate's layer, on the honest value below it, signs as FORS's layer and gives the root of
its tree. -/
theorem eval_signLayer (sk : Seeded.SecretKey) (top : List (List Digest))
    (htop : top = evalWithAnswerFn f (treeLevels (keyOf sk) topLayer rootTree : OracleComp HashSpec _))
    (index : Index) (lay : Layer) :
    evalWithAnswerFn f (signLayer (keyOf sk) top index lay (belowValue f sk index lay) :
        OracleComp HashSpec (Option (LayerSignature lay × Digest))) =
      (evalWithAnswerFn f (Seeded.signLayer sk index lay :
          OracleComp HashSpec (Option (LayerSignature lay)))).map fun part =>
        (part, node f sk.parameter lay (treeIndexAt index lay) sk.seed (layerHeight lay) 0) := by
  simp only [signLayer, otsSign, Seeded.signLayer, Seeded.signLayerWith, evalWithAnswerFn_bind,
    rootPayload_belowValue, layerMessageValue]
  generalize hm : evalWithAnswerFn f (Seeded.layerMessage sk index lay : OracleComp HashSpec HashInput) = msg
  simp only [keyOf]
  cases evalWithAnswerFn f (Seeded.otsSign sk.parameter lay (treeIndexAt index lay)
      (leafIndexAt index lay) sk.seed msg :
        OracleComp HashSpec (Option (Counter × (ChainIndex → Digest)))) with
  | none => rfl
  | some pair =>
      obtain ⟨counter, values⟩ := pair
      have hL : ∀ L : List (List Digest), L = evalWithAnswerFn f
          (treeLevels (keyOf sk) lay (treeIndexAt index lay) : OracleComp HashSpec _) →
          some ((⟨counter, values, fun z => levelNode L z.val
              ((leafIndexAt index lay).val >>> z.val ^^^ 1)⟩ : LayerSignature lay),
            levelNode L (layerHeight lay) 0) =
          (some (counter, values)).map fun pair =>
            ((⟨pair.1, pair.2, evalWithAnswerFn f (Seeded.treePath sk.parameter lay
              (treeIndexAt index lay) sk.seed (leafIndexAt index lay) :
                OracleComp HashSpec (Fin (layerHeight lay) → Digest))⟩ : LayerSignature lay),
              node f sk.parameter lay (treeIndexAt index lay) sk.seed (layerHeight lay) 0) := by
        rintro L rfl
        simp only [Option.map_some]
        congr 2
        · congr 1
          funext z
          rw [eval_treePath, ite_eq_left_of_eq_true _ _ (eq_true (by rw [keptHeight_full]; exact z.isLt)),
            levelNode_treeLevels f _ _ _ _ z.isLt.le _
              (shiftRight_xor_lt (leafIndexAt_lt index lay) z.isLt), Nat.shiftRight_eq_div_pow]
          rfl
        · exact levelNode_treeLevels f _ _ _ _ le_rfl 0 (by simp)
      by_cases htl : lay = topLayer
      · subst htl
        simp only [ite_true, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
        exact hL top (by rw [htop, treeIndexAt_top])
      · simp only [htl, ite_false, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
        exact hL _ rfl

end FORS.Crate
