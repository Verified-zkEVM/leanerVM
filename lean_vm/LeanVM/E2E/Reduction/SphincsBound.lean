/-
  LeanVM.E2E.Reduction.SphincsBound

  The hash queries of leanSPHINCS's verification, honest key generation and signer: the forest,
  the one-time signature, the tree and the grinding loops.
-/

module

public import LeanVM.E2E.Reduction.VerifyBound

/-!
# leanSPHINCS's verification, key generation and signer are query-bounded

* **Verification** (`Concrete.verify`, independent of the parameter set) makes at most
  `sphincsVerifyBound = 686` queries: the message digest, the forest key's recovery (`8` coordinates
  of `2 (6 · 4 + 1 + 2) + 1 + 3` queries, and the roots' hash) and the one-time leaf with the tree
  path (`1 + 64 · 3 + 1 + 26`) (`verify_isTotalQueryBound`).
* **Key generation** (`Seeded.keygenFromSeed`) makes at most `sphincsKeygenBound = 1 + 226 · 2^b +
  2 (26 - b)` at subtree height `b`: the scheme seed, the parameter, the kept subtree's
  `226 · 2^b - 1` and the surrogate spine (lean_sphincs's exact count `keygenCost + 1`,
  `keygenFromSeed_isTotalQueryBound`).
* **A signature** (`Seeded.sign`) makes at most `sphincsSignBound = 2^33 + 118,387 +
  sphincsPathBound`: the randomizer, at most `2^32` grinding attempts, the digest, the forest
  opening (`59,040`), the forest key (`59,121`), at most `2^32` counter trials and an opening
  (`224`), and the authentication path `sphincsPathBound = Σ_{l < 26} (l < b ? 226 · 2^l - 1 : 1)`
  (`sign_isTotalQueryBound`).

These are the `cs`, `csk` and `css` of `aggregate_no_forgery`.
-/

namespace LeanVM.E2E

open OracleSpec OracleComp _root_.Sphincs _root_.Sphincs.Concrete

@[expose] public section

/-! ### Building blocks -/

/-- One oracle call is one query. -/
theorem sOracleHash_isTotalQueryBound (x : Sphincs.HashInput) :
    IsTotalQueryBound (oracleHash x : OracleComp Sphincs.HashSpec Sphincs.HashOutput) 1 := by
  change IsTotalQueryBound ((liftM (Sphincs.HashSpec.query x) : OracleComp Sphincs.HashSpec _) >>=
    fun o ↦ pure o) 1
  exact isTotalQueryBound_query_bind_iff.mpr ⟨Nat.one_pos, fun _ ↦ trivial⟩

/-- A tweakable hash makes one query. -/
theorem sTweakableHash_isTotalQueryBound (p : Sphincs.PublicParameter) (d : Sphincs.HashDomain)
    (x : Sphincs.HashInput) :
    IsTotalQueryBound (tweakableHash p d x : OracleComp Sphincs.HashSpec Sphincs.Digest) 1 :=
  isTotalQueryBound_bind (n₂ := 0) (sOracleHash_isTotalQueryBound _) fun _ ↦
    isQueryBound_pure _ _ _ _

/-- **A sequence of computations, the `i`-th with at most `b i` queries,** makes at most their
sum. -/
theorem sSequenceFin_isTotalQueryBound_sum {α : Type} :
    ∀ {n : ℕ} (c : Fin n → OracleComp Sphincs.HashSpec α) (b : Fin n → ℕ),
      (∀ i, IsTotalQueryBound (c i) (b i)) →
      IsTotalQueryBound (Sphincs.Concrete.sequenceFin c) (∑ i, b i)
  | 0, _, _, _ => trivial
  | n + 1, c, b, h => by
    simp only [Sphincs.Concrete.sequenceFin]
    have := isTotalQueryBound_bind (n₁ := b 0) (n₂ := (∑ i : Fin n, b i.succ) + 0) (h 0) fun hd ↦
      isTotalQueryBound_bind (ob := fun tl ↦ (pure (fun i ↦ Fin.cases hd tl i) :
        OracleComp Sphincs.HashSpec (Fin (n + 1) → α)))
        (sSequenceFin_isTotalQueryBound_sum (fun i ↦ c i.succ) (fun i ↦ b i.succ)
          fun i ↦ h i.succ) fun _ ↦ trivial
    rwa [Fin.sum_univ_succ, ← Nat.add_zero (b 0 + _), Nat.add_assoc]

/-- **A sequence of computations each with at most `b` queries** makes at most `n · b`. -/
theorem sSequenceFin_isTotalQueryBound {α : Type} (b : ℕ) {n : ℕ}
    (c : Fin n → OracleComp Sphincs.HashSpec α) (h : ∀ i, IsTotalQueryBound (c i) b) :
    IsTotalQueryBound (Sphincs.Concrete.sequenceFin c) (n * b) := by
  have := sSequenceFin_isTotalQueryBound_sum c (fun _ ↦ b) h
  rwa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this

/-- A chain walk of `steps` steps makes at most `steps` queries. -/
theorem sChainWalk_isTotalQueryBound (p : Sphincs.PublicParameter) (lay : Sphincs.Layer)
    (tree : TreeIndex) (leaf : LeafIndex) (c : Sphincs.ChainIndex) (start : ℕ) :
    ∀ (steps : ℕ) (v : Sphincs.Digest), IsTotalQueryBound
      (chainWalk p lay tree leaf c start steps v : OracleComp Sphincs.HashSpec Sphincs.Digest) steps
  | 0, _ => trivial
  | steps + 1, v => by
    simp only [chainWalk]
    refine isTotalQueryBound_bind (sChainWalk_isTotalQueryBound p lay tree leaf c start steps v)
      fun _ ↦ ?_
    split
    · exact sTweakableHash_isTotalQueryBound _ _ _
    · trivial

/-- A forest chain walk of `steps` steps makes at most `steps` queries. -/
theorem forestWalk_isTotalQueryBound (p : Sphincs.PublicParameter) (index : Index) (c : Coord)
    (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (i : FChain) (start : ℕ) :
    ∀ (steps : ℕ) (v : Sphincs.Digest), IsTotalQueryBound
      (forestWalk p index c s j a i start steps v : OracleComp Sphincs.HashSpec Sphincs.Digest) steps
  | 0, _ => trivial
  | steps + 1, v => by
    simp only [forestWalk]
    refine isTotalQueryBound_bind (forestWalk_isTotalQueryBound p index c s j a i start steps v)
      fun _ ↦ ?_
    split
    · exact sTweakableHash_isTotalQueryBound _ _ _
    · trivial

/-- A tree fold of `levels` levels makes at most `levels` queries. -/
theorem sTreeFold_isTotalQueryBound (p : Sphincs.PublicParameter) (lay : Sphincs.Layer)
    (tree : TreeIndex) (leaf : LeafIndex) (path : ℕ → Sphincs.Digest) :
    ∀ (levels : ℕ) (v : Sphincs.Digest), IsTotalQueryBound
      (treeFold p lay tree leaf path levels v : OracleComp Sphincs.HashSpec Sphincs.Digest) levels
  | 0, _ => trivial
  | levels + 1, v => by
    simp only [treeFold]
    refine isTotalQueryBound_bind (sTreeFold_isTotalQueryBound p lay tree leaf path levels v)
      fun _ ↦ ?_
    split <;> exact sTweakableHash_isTotalQueryBound _ _ _

/-- A sub-tree fold of `levels` levels makes at most `levels` queries. -/
theorem subFold_isTotalQueryBound (p : Sphincs.PublicParameter) (index : Index) (c : Coord)
    (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (path : Fin subHeight → Sphincs.Digest) :
    ∀ (levels : ℕ) (v : Sphincs.Digest), IsTotalQueryBound
      (subFold p index c s j a path levels v : OracleComp Sphincs.HashSpec Sphincs.Digest) levels
  | 0, _ => trivial
  | levels + 1, v => by
    simp only [subFold]
    refine isTotalQueryBound_bind (subFold_isTotalQueryBound p index c s j a path levels v)
      fun _ ↦ ?_
    split
    · split <;> exact sTweakableHash_isTotalQueryBound _ _ _
    · trivial

/-- A top-tree fold of `levels` levels makes at most `levels` queries. -/
theorem topFold_isTotalQueryBound (p : Sphincs.PublicParameter) (index : Index) (c : Coord)
    (s : SuperIdx) (path : Fin topHeight → Sphincs.Digest) :
    ∀ (levels : ℕ) (v : Sphincs.Digest), IsTotalQueryBound
      (topFold p index c s path levels v : OracleComp Sphincs.HashSpec Sphincs.Digest) levels
  | 0, _ => trivial
  | levels + 1, v => by
    simp only [topFold]
    refine isTotalQueryBound_bind (topFold_isTotalQueryBound p index c s path levels v)
      fun _ ↦ ?_
    split
    · split <;> exact sTweakableHash_isTotalQueryBound _ _ _
    · trivial

/-! ### Verification -/

/-- A child leaf's recovery: `6` chains of at most `4` steps and the leaf hash. -/
theorem childRecover_isTotalQueryBound (p : Sphincs.PublicParameter) (index : Index) (c : Coord)
    (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (word : Codeword) (values : FChain → Sphincs.Digest) :
    IsTotalQueryBound (childRecover p index c s j a word values :
      OracleComp Sphincs.HashSpec Sphincs.Digest) (childChains * chainTop + 1) := by
  unfold childRecover
  exact isTotalQueryBound_bind (sSequenceFin_isTotalQueryBound chainTop _ fun i ↦
    (forestWalk_isTotalQueryBound _ _ _ _ _ _ _ _ _ _).mono (Nat.le_of_lt_succ (word i).isLt))
    fun _ ↦ sTweakableHash_isTotalQueryBound _ _ _

/-- A coordinate's recovery: two sub-trees (a child leaf and two levels each), the super-child and
three top levels. -/
theorem coordRecover_isTotalQueryBound (p : Sphincs.PublicParameter) (index : Index) (c : Coord)
    (mark : CoordMark) (opening : CoordOpening) :
    IsTotalQueryBound (coordRecover p index c mark opening :
      OracleComp Sphincs.HashSpec (Sphincs.Digest × Sphincs.Digest)) 58 := by
  unfold coordRecover
  refine (isTotalQueryBound_bind (sSequenceFin_isTotalQueryBound (childChains * chainTop + 1 +
    ((subHeight - 1) + 0)) _ fun j ↦ isTotalQueryBound_bind (childRecover_isTotalQueryBound _ _ _ _
      _ _ _ _) fun _ ↦ isTotalQueryBound_bind (subFold_isTotalQueryBound _ _ _ _ _ _ _ _ _)
        fun _ ↦ isQueryBound_pure _ _ _ _) fun _ ↦
    isTotalQueryBound_bind (sTweakableHash_isTotalQueryBound _ _ _) fun _ ↦
      isTotalQueryBound_bind (n₂ := 0) (topFold_isTotalQueryBound _ _ _ _ _ _ _) fun _ ↦
        isQueryBound_pure _ _ _ _).mono ?_
  simp [childChains, chainTop, subHeight, topHeight]

/-- The forest key's recovery: `8` coordinates and the roots' hash. -/
theorem forestRecover_isTotalQueryBound (p : Sphincs.PublicParameter) (index : Index)
    (marks : Coord → CoordMark) (opening : Coord → CoordOpening) :
    IsTotalQueryBound (forestRecover p index marks opening :
      OracleComp Sphincs.HashSpec Sphincs.Digest) (forestCoords * 58 + 1) := by
  unfold forestRecover
  exact isTotalQueryBound_bind (sSequenceFin_isTotalQueryBound 58 _ fun _ ↦
    coordRecover_isTotalQueryBound _ _ _ _ _) fun _ ↦ sTweakableHash_isTotalQueryBound _ _ _

/-- An encoding makes one query. -/
theorem encode_isTotalQueryBound (p : Sphincs.PublicParameter) (lay : Sphincs.Layer)
    (tree : TreeIndex) (leaf : LeafIndex) (msg : Sphincs.Digest) (counter : Counter) :
    IsTotalQueryBound (encode p lay tree leaf msg counter :
      OracleComp Sphincs.HashSpec (Option Sphincs.Encoding)) 1 :=
  isTotalQueryBound_bind (n₂ := 0) (sTweakableHash_isTotalQueryBound _ _ _) fun _ ↦
    isQueryBound_pure _ _ _ _

/-- The one-time leaf: the encoding, `64` chains of at most `3` steps and the leaf hash. -/
theorem sOtsLeaf_isTotalQueryBound (p : Sphincs.PublicParameter) (lay : Sphincs.Layer)
    (tree : TreeIndex) (leaf : LeafIndex) (msg : Sphincs.Digest) (counter : Counter)
    (values : Sphincs.ChainIndex → Sphincs.Digest) :
    IsTotalQueryBound (otsLeaf p lay tree leaf msg counter values :
      OracleComp Sphincs.HashSpec (Option Sphincs.Digest))
      (1 + (Sphincs.numChains * 3 + (1 + 0))) := by
  unfold otsLeaf encode
  rw [bind_assoc]
  refine isTotalQueryBound_bind (sOracleHash_isTotalQueryBound _) fun _ ↦ ?_
  rw [pure_bind]
  split
  · exact isTotalQueryBound_bind (sSequenceFin_isTotalQueryBound 3 _ fun i ↦
      (sChainWalk_isTotalQueryBound _ _ _ _ _ _ _ _).mono (Nat.sub_le _ _)) fun _ ↦
        isTotalQueryBound_bind (sTweakableHash_isTotalQueryBound _ _ _) fun _ ↦
          isQueryBound_pure _ _ _ _
  · exact isQueryBound_pure _ _ _ _

/-- The hash queries of one layer's verification: the one-time leaf and the tree fold. -/
def sphincsLayerVerifyBound : ℕ := 1 + (Sphincs.numChains * 3 + (1 + 0)) + maxLayerHeight

/-- The layers' walk: per layer the one-time leaf and the tree fold. -/
theorem verifyLayers_isTotalQueryBound (p : Sphincs.PublicParameter) (index : Index)
    (σ : Sphincs.Signature) (remaining : ℕ) (msg : Sphincs.Digest) :
    IsTotalQueryBound (verifyLayers p index σ remaining msg :
      OracleComp Sphincs.HashSpec (Option Sphincs.Digest)) (remaining * sphincsLayerVerifyBound) := by
  induction remaining generalizing msg with
  | zero => trivial
  | succ remaining ih =>
    simp only [verifyLayers]
    split
    next hl =>
      -- the layer's height as a variable: a goal with a concrete tree fold would be reduced
      generalize hL : layerHeight ⟨remaining, hl⟩ = L
      refine (isTotalQueryBound_bind (n₁ := 1 + (Sphincs.numChains * 3 + (1 + 0)))
        (n₂ := L + remaining * sphincsLayerVerifyBound)
        (sOtsLeaf_isTotalQueryBound _ _ _ _ _ _ _) fun o ↦ ?_).mono ?_
      · rcases o with _ | v
        · exact isQueryBound_pure _ _ _ _
        · exact isTotalQueryBound_bind (sTreeFold_isTotalQueryBound _ _ _ _ _ _ _) fun _ ↦ ih _
      · have : sphincsLayerVerifyBound = 1 + (Sphincs.numChains * 3 + (1 + 0)) + maxLayerHeight :=
          rfl
        have hL' : L = maxLayerHeight := hL ▸ rfl
        rw [Nat.succ_mul]
        omega
    next => exact isQueryBound_pure _ _ _ _

/-- The hash queries of leanSPHINCS's verification. -/
def sphincsVerifyBound : ℕ := 686

/-- **leanSPHINCS's verification makes at most `sphincsVerifyBound` hash queries.** -/
theorem sphincsVerify_isTotalQueryBound (pk : Sphincs.PublicKey) (msg : Sphincs.Message)
    (σ : Sphincs.Signature) :
    IsTotalQueryBound (Sphincs.Concrete.verify pk msg σ : OracleComp Sphincs.HashSpec Bool)
      sphincsVerifyBound := by
  simp only [Concrete.verify, messageDigest, messageDigestCall, bind_assoc, pure_bind]
  refine (isTotalQueryBound_bind (sOracleHash_isTotalQueryBound _) fun _ ↦
    isTotalQueryBound_bind (forestRecover_isTotalQueryBound _ _ _ _) fun _ ↦
      isTotalQueryBound_bind (n₂ := 0) (verifyLayers_isTotalQueryBound _ _ _ _ _) fun o ↦ ?_).mono ?_
  · rcases o with _ | r <;> exact isQueryBound_pure _ _ _ _
  · simp [sphincsVerifyBound, sphincsLayerVerifyBound, forestCoords, Sphincs.numLayers,
      Sphincs.numChains, maxLayerHeight]

/-! ### Key generation -/

/-- A one-time key's seed derivations: `32` queries. -/
theorem sOtsSecrets_isTotalQueryBound (p : Sphincs.PublicParameter) (lay : Sphincs.Layer)
    (tree : TreeIndex) (leaf : LeafIndex) (seed : Sphincs.MasterSeed) :
    IsTotalQueryBound (Seeded.otsSecrets p lay tree leaf seed :
      OracleComp Sphincs.HashSpec (Sphincs.ChainIndex → Sphincs.Digest)) 32 := by
  unfold Seeded.otsSecrets
  exact isTotalQueryBound_bind (n₂ := 0) (sSequenceFin_isTotalQueryBound 1 _ fun _ ↦
    sOracleHash_isTotalQueryBound _) fun _ ↦ isQueryBound_pure _ _ _ _

/-- The chain walks of a one-time key, each at most `3` steps: `64 · 3` queries. -/
theorem sChainWalks_isTotalQueryBound (p : Sphincs.PublicParameter) (lay : Sphincs.Layer)
    (tree : TreeIndex) (leaf : LeafIndex) (steps : Sphincs.ChainIndex → ℕ)
    (hsteps : ∀ i, steps i ≤ Sphincs.chainLength - 1) (secrets : Sphincs.ChainIndex → Sphincs.Digest) :
    IsTotalQueryBound (sequenceFin fun chainIdx ↦ chainWalk p lay tree leaf chainIdx 0 (steps chainIdx)
      (secrets chainIdx) : OracleComp Sphincs.HashSpec (Sphincs.ChainIndex → Sphincs.Digest))
      (Sphincs.numChains * 3) :=
  sSequenceFin_isTotalQueryBound 3 _ fun i ↦
    (sChainWalk_isTotalQueryBound _ _ _ _ _ _ _ _).mono (hsteps i)

/-- The hash queries of a leanSPHINCS tree node at `level`. -/
def sphincsNodeBound (level : ℕ) : ℕ := 226 * 2 ^ level - 1

/-- **A tree node at `level` makes at most `sphincsNodeBound level` queries**: `2^level` one-time
keys of `32 + 64 · 3 + 1` and `2^level - 1` inner nodes. -/
theorem sTreeNode_isTotalQueryBound (p : Sphincs.PublicParameter) (lay : Sphincs.Layer)
    (tree : TreeIndex) (seed : Sphincs.MasterSeed) :
    ∀ (level node : ℕ), IsTotalQueryBound (Seeded.treeNode p lay tree seed level node :
      OracleComp Sphincs.HashSpec Sphincs.Digest) (sphincsNodeBound level)
  | 0, node => by
    simp only [Seeded.treeNode, Seeded.oneTimePublicKey, bind_assoc]
    refine (isTotalQueryBound_bind (sOtsSecrets_isTotalQueryBound p lay tree _ seed) fun secrets ↦
      isTotalQueryBound_bind (sChainWalks_isTotalQueryBound p lay tree _ (fun _ ↦ chainLength - 1)
        (fun _ ↦ le_rfl) secrets) fun _ ↦ sTweakableHash_isTotalQueryBound _ _ _).mono ?_
    simp [sphincsNodeBound, Sphincs.numChains]
  | level + 1, node => by
    simp only [Seeded.treeNode]
    refine (isTotalQueryBound_bind (sTreeNode_isTotalQueryBound p lay tree seed level (2 * node))
      fun _ ↦ isTotalQueryBound_bind (sTreeNode_isTotalQueryBound p lay tree seed level
        (2 * node + 1)) fun _ ↦ sTweakableHash_isTotalQueryBound _ _ _).mono ?_
    simp only [sphincsNodeBound, pow_succ]
    have : 1 ≤ 2 ^ level := Nat.one_le_two_pow
    omega

/-- A surrogate makes at most one query. -/
theorem surrogate_isTotalQueryBound (p : Sphincs.PublicParameter) (seed : Sphincs.MasterSeed)
    (level : ℕ) :
    IsTotalQueryBound (Seeded.surrogate p seed level : OracleComp Sphincs.HashSpec Sphincs.Digest)
      1 := by
  unfold Seeded.surrogate
  split
  · exact isTotalQueryBound_bind (n₂ := 0) (sOracleHash_isTotalQueryBound _) fun _ ↦
      isQueryBound_pure _ _ _ _
  · trivial

/-! ### Signing -/

/-- A child's seed derivations: `3` queries. -/
theorem forestSecrets_isTotalQueryBound (p : Sphincs.PublicParameter) (index : Index) (c : Coord)
    (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (seed : Sphincs.MasterSeed) :
    IsTotalQueryBound (Seeded.forestSecrets p index c s j a seed :
      OracleComp Sphincs.HashSpec (FChain → Sphincs.Digest)) 3 := by
  unfold Seeded.forestSecrets
  exact isTotalQueryBound_bind (n₂ := 0) (sSequenceFin_isTotalQueryBound 1 _ fun _ ↦
    sOracleHash_isTotalQueryBound _) fun _ ↦ isQueryBound_pure _ _ _ _

/-- The hash queries of a sub-tree node at `level`. -/
def subNodeBound (level : ℕ) : ℕ := 29 * 2 ^ level - 1

/-- A sub-tree node at `level`: `2^level` child leaves of `3 + 6 · 4 + 1` and the inner nodes. -/
theorem subNode_isTotalQueryBound (p : Sphincs.PublicParameter) (index : Index) (c : Coord)
    (s : SuperIdx) (j : SubIdx) (seed : Sphincs.MasterSeed) :
    ∀ (level node : ℕ), IsTotalQueryBound (Seeded.subNode p index c s j seed level node :
      OracleComp Sphincs.HashSpec Sphincs.Digest) (subNodeBound level)
  | 0, node => by
    simp only [Seeded.subNode, Seeded.childLeaf]
    refine (isTotalQueryBound_bind (forestSecrets_isTotalQueryBound _ _ _ _ _ _ _) fun _ ↦
      isTotalQueryBound_bind (sSequenceFin_isTotalQueryBound chainTop _ fun _ ↦
        forestWalk_isTotalQueryBound _ _ _ _ _ _ _ _ _ _) fun _ ↦
          sTweakableHash_isTotalQueryBound _ _ _).mono ?_
    simp [subNodeBound, childChains, chainTop]
  | level + 1, node => by
    simp only [Seeded.subNode]
    refine (isTotalQueryBound_bind (subNode_isTotalQueryBound p index c s j seed level (2 * node))
      fun _ ↦ isTotalQueryBound_bind (n₂ := 1) (subNode_isTotalQueryBound p index c s j seed level
        (2 * node + 1)) fun _ ↦ ?_).mono ?_
    · split
      · exact sTweakableHash_isTotalQueryBound _ _ _
      · trivial
    · simp only [subNodeBound, pow_succ]
      have : 1 ≤ 2 ^ level := Nat.one_le_two_pow
      omega

/-- A super-child: the two level-2 nodes of its two sub-trees and its hash. -/
theorem superNode_isTotalQueryBound (p : Sphincs.PublicParameter) (index : Index) (c : Coord)
    (s : SuperIdx) (seed : Sphincs.MasterSeed) :
    IsTotalQueryBound (Seeded.superNode p index c s seed :
      OracleComp Sphincs.HashSpec Sphincs.Digest) 461 := by
  unfold Seeded.superNode
  refine (isTotalQueryBound_bind (sSequenceFin_isTotalQueryBound (subNodeBound (subHeight - 1) +
    (subNodeBound (subHeight - 1) + 0)) _ fun _ ↦ isTotalQueryBound_bind
      (subNode_isTotalQueryBound _ _ _ _ _ _ _ _) fun _ ↦ isTotalQueryBound_bind
        (subNode_isTotalQueryBound _ _ _ _ _ _ _ _) fun _ ↦ isQueryBound_pure _ _ _ _) fun _ ↦
    sTweakableHash_isTotalQueryBound _ _ _).mono ?_
  simp [subNodeBound, subHeight]

/-- The hash queries of a top-tree node at `level`. -/
def topNodeBound (level : ℕ) : ℕ := 462 * 2 ^ level - 1

/-- A top-tree node at `level`: `2^level` super-children and the inner nodes. -/
theorem topNode_isTotalQueryBound (p : Sphincs.PublicParameter) (index : Index) (c : Coord)
    (seed : Sphincs.MasterSeed) :
    ∀ (level node : ℕ), IsTotalQueryBound (Seeded.topNode p index c seed level node :
      OracleComp Sphincs.HashSpec Sphincs.Digest) (topNodeBound level)
  | 0, node => by
    simp only [Seeded.topNode]
    exact (superNode_isTotalQueryBound _ _ _ _ _).mono (by simp [topNodeBound])
  | level + 1, node => by
    simp only [Seeded.topNode]
    refine (isTotalQueryBound_bind (topNode_isTotalQueryBound p index c seed level (2 * node))
      fun _ ↦ isTotalQueryBound_bind (n₂ := 1) (topNode_isTotalQueryBound p index c seed level
        (2 * node + 1)) fun _ ↦ ?_).mono ?_
    · split
      · exact sTweakableHash_isTotalQueryBound _ _ _
      · trivial
    · simp only [topNodeBound, pow_succ]
      have : 1 ≤ 2 ^ level := Nat.one_le_two_pow
      omega

/-- The forest key: the two level-3 nodes of every coordinate and the roots' hash. -/
theorem forestKey_isTotalQueryBound (p : Sphincs.PublicParameter) (index : Index)
    (seed : Sphincs.MasterSeed) :
    IsTotalQueryBound (Seeded.forestKey p index seed :
      OracleComp Sphincs.HashSpec Sphincs.Digest) 59121 := by
  unfold Seeded.forestKey
  refine (isTotalQueryBound_bind (sSequenceFin_isTotalQueryBound (topNodeBound (topHeight - 1) +
    (topNodeBound (topHeight - 1) + 0)) _ fun _ ↦ isTotalQueryBound_bind
      (topNode_isTotalQueryBound _ _ _ _ _ _) fun _ ↦ isTotalQueryBound_bind
        (topNode_isTotalQueryBound _ _ _ _ _ _) fun _ ↦ isQueryBound_pure _ _ _ _) fun _ ↦
    sTweakableHash_isTotalQueryBound _ _ _).mono ?_
  simp [topNodeBound, topHeight, forestCoords]

/-- A coordinate's opening: per sub-tree the derivations, the chains and the three path nodes,
then the four top path nodes. -/
theorem coordOpen_isTotalQueryBound (p : Sphincs.PublicParameter) (index : Index) (c : Coord)
    (mark : CoordMark) (seed : Sphincs.MasterSeed) :
    IsTotalQueryBound (Seeded.coordOpen p index c mark seed :
      OracleComp Sphincs.HashSpec CoordOpening) 7380 := by
  unfold Seeded.coordOpen
  refine (isTotalQueryBound_bind (sSequenceFin_isTotalQueryBound (3 + (childChains * chainTop +
    ((∑ level : Fin subHeight, subNodeBound level) + 0))) _ fun _ ↦ isTotalQueryBound_bind
      (forestSecrets_isTotalQueryBound _ _ _ _ _ _ _) fun _ ↦ isTotalQueryBound_bind
        (sSequenceFin_isTotalQueryBound chainTop _ fun _ ↦
          (forestWalk_isTotalQueryBound _ _ _ _ _ _ _ _ _ _).mono (Nat.sub_le _ _)) fun _ ↦
        isTotalQueryBound_bind (sSequenceFin_isTotalQueryBound_sum _
          (fun level : Fin subHeight ↦ subNodeBound level) fun level ↦
            subNode_isTotalQueryBound _ _ _ _ _ _ level.val _) fun _ ↦
              isQueryBound_pure _ _ _ _) fun _ ↦
    isTotalQueryBound_bind (n₂ := 0) (sSequenceFin_isTotalQueryBound_sum _
      (fun level : Fin topHeight ↦ topNodeBound level) fun level ↦
        topNode_isTotalQueryBound _ _ _ _ level.val _) fun _ ↦ isQueryBound_pure _ _ _ _).mono ?_
  decide

/-- The forest opening: `8` coordinates. -/
theorem forestOpen_isTotalQueryBound (p : Sphincs.PublicParameter) (index : Index)
    (marks : Coord → CoordMark) (seed : Sphincs.MasterSeed) :
    IsTotalQueryBound (Seeded.forestOpen p index marks seed :
      OracleComp Sphincs.HashSpec (Coord → CoordOpening)) (forestCoords * 7380) :=
  sSequenceFin_isTotalQueryBound 7380 _ fun _ ↦ coordOpen_isTotalQueryBound _ _ _ _ _

/-- The counter trials: one encoding per trial, then one opening of `32 + 64 · 3` queries. -/
theorem sOtsSignFrom_isTotalQueryBound (p : Sphincs.PublicParameter) (lay : Sphincs.Layer)
    (tree : TreeIndex) (leaf : LeafIndex) (seed : Sphincs.MasterSeed) (msg : Sphincs.Digest) :
    ∀ (attempts counter : ℕ), IsTotalQueryBound (Seeded.otsSignFrom p lay tree leaf seed msg attempts
      counter : OracleComp Sphincs.HashSpec _) (attempts + 224)
  | 0, _ => trivial
  | attempts + 1, counter => by
    simp only [Seeded.otsSignFrom]
    refine (isTotalQueryBound_bind (n₂ := attempts + 224) (encode_isTotalQueryBound _ _ _ _ _ _)
      fun o ↦ ?_).mono (by omega)
    rcases o with _ | e
    · exact sOtsSignFrom_isTotalQueryBound p lay tree leaf seed msg attempts (counter + 1)
    · refine (isTotalQueryBound_bind (sOtsSecrets_isTotalQueryBound _ _ _ _ _) fun secrets ↦
        isTotalQueryBound_bind (n₂ := 0) (sChainWalks_isTotalQueryBound _ _ _ _ _
          (fun i ↦ Nat.le_sub_one_of_lt (Fin.isLt _)) secrets) fun _ ↦
            isQueryBound_pure _ _ _ _).mono ?_
      simp only [Sphincs.numChains]
      omega

/-! ### The parameter set's parts -/

variable [Sphincs.Params]

/-- The spine above the kept subtree: the subtree's root, then a surrogate and a node per step. -/
theorem spineNode_isTotalQueryBound (p : Sphincs.PublicParameter) (lay : Sphincs.Layer)
    (tree : TreeIndex) (seed : Sphincs.MasterSeed) :
    ∀ steps : ℕ, IsTotalQueryBound (Seeded.spineNode p lay tree seed steps :
      OracleComp Sphincs.HashSpec Sphincs.Digest) (sphincsNodeBound subtreeHeight + 2 * steps)
  | 0 => sTreeNode_isTotalQueryBound _ _ _ _ _ _
  | steps + 1 => by
    simp only [Seeded.spineNode]
    refine (isTotalQueryBound_bind (spineNode_isTotalQueryBound p lay tree seed steps) fun _ ↦
      isTotalQueryBound_bind (n₂ := 1) (surrogate_isTotalQueryBound _ _ _) fun _ ↦ ?_).mono
        (by omega)
    split <;> exact sTweakableHash_isTotalQueryBound _ _ _

/-- The hash queries of leanSPHINCS's key generation at the parameter set's subtree height. -/
def sphincsKeygenBound : ℕ := 1 + (226 * 2 ^ subtreeHeight + 2 * (totalHeight - subtreeHeight))

/-- **leanSPHINCS's key generation makes at most `sphincsKeygenBound` hash queries.** -/
theorem sphincsKeygenFromSeed_isTotalQueryBound (seed : Sphincs.MasterSeed) :
    IsTotalQueryBound (Seeded.keygenFromSeed seed) sphincsKeygenBound := by
  unfold Seeded.keygenFromSeed Seeded.keygenFromMaster Seeded.treeRoot schemeSeed deriveKey
  simp only [bind_assoc, pure_bind]
  refine (isTotalQueryBound_bind (sOracleHash_isTotalQueryBound _) fun _ ↦
    isTotalQueryBound_bind (sOracleHash_isTotalQueryBound _) fun _ ↦
      isTotalQueryBound_bind (n₂ := 0) (spineNode_isTotalQueryBound _ _ _ _ _) fun _ ↦
        isQueryBound_pure _ _ _ _).mono ?_
  have : 1 ≤ 2 ^ subtreeHeight := Nat.one_le_two_pow
  simp only [sphincsKeygenBound, sphincsNodeBound]
  omega

/-- The hash queries of an authentication path at the parameter set's subtree height: the kept
subtree's sibling nodes below level `b`, a surrogate from level `b` on. -/
def sphincsPathBound : ℕ :=
  ∑ level : Fin maxLayerHeight, if level.val < subtreeHeight then sphincsNodeBound level else 1

/-- An authentication path makes at most `sphincsPathBound` queries. -/
theorem sTreePath_isTotalQueryBound (p : Sphincs.PublicParameter) (lay : Sphincs.Layer)
    (tree : TreeIndex) (seed : Sphincs.MasterSeed) (leaf : LeafIndex) :
    IsTotalQueryBound (Seeded.treePath p lay tree seed leaf : OracleComp Sphincs.HashSpec _)
      sphincsPathBound := by
  unfold Seeded.treePath sphincsPathBound
  refine sSequenceFin_isTotalQueryBound_sum _ _ fun level ↦ ?_
  split
  · exact sTreeNode_isTotalQueryBound _ _ _ _ _ _
  · exact surrogate_isTotalQueryBound _ _ _

/-- The grinding attempts: one digest call each. -/
theorem signDigestLoop_isTotalQueryBound (sk : Seeded.SecretKey) (msg : Sphincs.Message) :
    ∀ (attempts : ℕ) (r : Sphincs.Randomness), IsTotalQueryBound (Seeded.signDigestLoop sk msg
      attempts r : OracleComp Sphincs.HashSpec _) attempts
  | 0, _ => trivial
  | attempts + 1, r => by
    simp only [Seeded.signDigestLoop, Seeded.signAttempt, messageDigestCall, bind_assoc]
    refine (isTotalQueryBound_bind (sOracleHash_isTotalQueryBound _) fun _ ↦ ?_).mono
      (Nat.add_comm _ _).le
    split
    · rw [pure_bind]
      exact isQueryBound_pure _ _ _ _
    · rw [pure_bind]
      exact signDigestLoop_isTotalQueryBound sk msg attempts _

/-- The hash queries of one layer's signature: the forest key, the counter trials and the path. -/
def sphincsLayerBound : ℕ := 59121 + ((encodingAttemptLimit + 224) + (sphincsPathBound + 0))

/-- One layer's signature makes at most `sphincsLayerBound` queries. -/
theorem sSignLayer_isTotalQueryBound (sk : Seeded.SecretKey) (index : Index) (lay : Sphincs.Layer) :
    IsTotalQueryBound (Seeded.signLayer sk index lay : OracleComp Sphincs.HashSpec _)
      sphincsLayerBound := by
  unfold Seeded.signLayer Seeded.layerMessage Seeded.otsSign
  refine isTotalQueryBound_bind (forestKey_isTotalQueryBound _ _ _) fun _ ↦
    isTotalQueryBound_bind (sOtsSignFrom_isTotalQueryBound _ _ _ _ _ _ _ _) fun o ↦ ?_
  rcases o with _ | ⟨counter, values⟩
  · exact isQueryBound_pure _ _ _ _
  · exact isTotalQueryBound_bind (sTreePath_isTotalQueryBound _ _ _ _ _) fun _ ↦
      isQueryBound_pure _ _ _ _

/-- The hash queries of a leanSPHINCS signature at the parameter set's subtree height. -/
def sphincsSignBound : ℕ :=
  1 + (digestAttemptLimit + (1 + (forestCoords * 7380 + (sphincsLayerBound + 0))))

theorem sphincsSignBound_eq : sphincsSignBound = 8590052979 + sphincsPathBound := by
  unfold sphincsSignBound sphincsLayerBound
  generalize sphincsPathBound = P
  have h1 : digestAttemptLimit = 4294967296 := by norm_num [digestAttemptLimit]
  have h2 : encodingAttemptLimit = 4294967296 := by norm_num [encodingAttemptLimit]
  have h3 : forestCoords = 8 := rfl
  rw [h1, h2, h3]
  omega

/-- **leanSPHINCS's signer makes at most `sphincsSignBound` hash queries.** -/
theorem sphincsSign_isTotalQueryBound (sk : Seeded.SecretKey) (msg : Sphincs.Message) :
    IsTotalQueryBound (Seeded.sign sk msg : OracleComp Sphincs.HashSpec _) sphincsSignBound := by
  have hD := signDigestLoop_isTotalQueryBound sk msg
  have hF := forestOpen_isTotalQueryBound sk.parameter
  have hL := sSignLayer_isTotalQueryBound sk
  unfold sphincsSignBound
  simp only [Seeded.sign, deriveRandomizer, messageDigest, messageDigestCall, sequenceLayers,
    bind_assoc, pure_bind]
  -- the grinding loop, the forest opening and the layer's signature as variables: a goal with
  -- these concrete computations would be reduced
  generalize digestAttemptLimit = A
  generalize (Seeded.signDigestLoop sk msg : ℕ → Sphincs.Randomness → OracleComp Sphincs.HashSpec _)
    = DL at hD ⊢
  generalize (Seeded.forestOpen sk.parameter : Index → (Coord → CoordMark) → Sphincs.MasterSeed →
    OracleComp Sphincs.HashSpec _) = FO at hF ⊢
  generalize (Seeded.signLayer sk : Index → (lay : Sphincs.Layer) →
    OracleComp Sphincs.HashSpec (Option (LayerSignature lay))) = SL at hL ⊢
  refine isTotalQueryBound_bind (sOracleHash_isTotalQueryBound _) fun _ ↦
    isTotalQueryBound_bind (hD _ _) fun o ↦ ?_
  rcases o with _ | ⟨r, i⟩
  · exact isQueryBound_pure _ _ _ _
  · refine isTotalQueryBound_bind (sOracleHash_isTotalQueryBound _) fun _ ↦
      isTotalQueryBound_bind (hF _ _ _) fun _ ↦
        isTotalQueryBound_bind (n₂ := 0) (hL _ _) fun o' ↦ ?_
    rcases o' with _ | top <;> exact isQueryBound_pure _ _ _ _

end
end LeanVM.E2E
