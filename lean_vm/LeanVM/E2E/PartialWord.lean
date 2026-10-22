/-
  LeanVM.E2E.PartialWord

  Partial words (decision E2E-10 of `docs/roadmap/e2e-security.md`): a committed level-0 word
  some of whose Merkle subtrees are given only as digests, its root, and the stacks it binds.
-/

module

public import LeanVM.Protocol.EndToEnd.Candidates
public import LeanVM.Protocol.Compile.Prover

/-!
# Partial words

The deployed verifier opens a few columns of a node's stack commitment, so a prover may leave a
subtree of its Merkle tree uncomputed, an arbitrary digest at an inner node. V_I reads such a
commitment as a *partial word* (`PWord`, decision E2E-10, `docs/roadmap/partial-words.md`): the
rows, and *holes*, nodes of the tree given only as a digest (`hole k j`: node `j` of level `k`,
the leaves at level `0`). A row with a hole on its path to the root is not present.

* `pTreeRootM`: the root, computed top-down, a hole's digest standing for its subtree; a full
  word (`PWord.full`, no hole) has the deployed root (`pTreeRootM_full`).
* `SCandidates`: the stacks agreeing with the word on at least `A` *present* columns, a column
  under a hole counting as a disagreement; on a full word, the candidates (`sCandidates_full`).
* `mem_sCandidates_of_candidates`: a word without holes equal to `W` has `W`'s candidates.
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.Whir

@[expose] public section

/-! ## Partial words and their roots -/

/-- **A partial word**: the rows of a committed matrix, and the nodes of its Merkle tree given
only as digests (`hole k j`: node `j` of level `k`, the leaves at level `0`). Rows under a hole
are not read. -/
structure PWord where
  /-- The rows (read only where no hole covers them). -/
  word : Word
  /-- The holes: the nodes given as digests, by level and index. -/
  hole : ℕ → ℕ → Option Digest

/-- A full word: no hole. -/
def PWord.full (W : Word) : PWord := ⟨W, fun _ _ ↦ none⟩

/-- A full word's rows are the word's. -/
@[simp] theorem PWord.word_full (W : Word) : (PWord.full W).word = W := rfl

/-- Row `p` of a tree of height `ht` is present: no hole on its path to the root. -/
def PWord.Present (P : PWord) (ht p : ℕ) : Prop := ∀ k ≤ ht, P.hole k (p / 2 ^ k) = none

/-- Every row of a tree of height `ht` is present: the word has no hole in the tree. -/
def PWord.Full (P : PWord) (ht : ℕ) : Prop := ∀ p < 2 ^ ht, P.Present ht p

/-- A full word has no hole. -/
theorem PWord.full_full (W : Word) (ht : ℕ) : (PWord.full W).Full ht := fun _ _ _ _ ↦ rfl

section M

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest)

/-- Node `j` of level `k` of a partial tree: its hole's digest, or the hash of its row (level
`0`, `leafHashesM`'s) or of its two children (`parentsM`'s). -/
def pNodeM (P : PWord) : ℕ → ℕ → m Digest
  | 0, j => match P.hole 0 j with
    | some d => pure d
    | none => H ((P.word j).flatMap kBytes)
  | k + 1, j => match P.hole (k + 1) j with
    | some d => pure d
    | none => do
      let l ← pNodeM P k (2 * j)
      let r ← pNodeM P k (2 * j + 1)
      H (digestBytes l ++ digestBytes r)

/-- **The root of a partial tree** of height `ht`. -/
def pTreeRootM (ht : ℕ) (P : PWord) : m Digest := pNodeM H P ht 0

end M

/-! ## A full word's root is the deployed root -/

section Pure

variable {D : Type} (hp : D → D → D)

/-- The top-down node of the tree over the level `g`. -/
def tdNode (g : ℕ → D) : ℕ → ℕ → D
  | 0, j => g j
  | k + 1, j => hp (tdNode g k (2 * j)) (tdNode g k (2 * j + 1))

theorem tdNode_pairs (g : ℕ → D) :
    ∀ k j, tdNode hp (fun j ↦ hp (g (2 * j)) (g (2 * j + 1))) k j = tdNode hp g (k + 1) j
  | 0, j => rfl
  | k + 1, j => by
    simp only [tdNode] at *
    rw [tdNode_pairs g k (2 * j), tdNode_pairs g k (2 * j + 1)]
    rfl

/-- The bottom-up root of a level is its top-down root. -/
theorem rootOfLevel_ofFn : ∀ (k : ℕ) (g : ℕ → D),
    MerkleTree.rootOfLevel hp k (Vector.ofFn fun i : Fin (2 ^ k) ↦ g i) = tdNode hp g k 0
  | 0, g => by simp [MerkleTree.rootOfLevel, tdNode]
  | k + 1, g => by
    have e : MerkleTree.parents hp (Vector.ofFn fun i : Fin (2 ^ (k + 1)) ↦ g i) =
        Vector.ofFn fun i : Fin (2 ^ k) ↦ hp (g (2 * i)) (g (2 * i + 1)) := by
      ext i hi
      simp [MerkleTree.parents]
    rw [MerkleTree.rootOfLevel, e]
    exact (rootOfLevel_ofFn k (fun j ↦ hp (g (2 * j)) (g (2 * j + 1)))).trans
      (tdNode_pairs hp g k 0)

end Pure

/-- The nodes of a full word's tree, in `Id`. -/
theorem pNodeM_full (H : Bytes → Digest) (W : Word) :
    ∀ k j, pNodeM (m := Id) (fun x ↦ pure (H x)) (PWord.full W) k j =
      tdNode (nodeHash H) (fun i ↦ leafHash H (W i)) k j
  | 0, j => rfl
  | k + 1, j => by
    show (do
        let l ← pNodeM (m := Id) (fun x ↦ pure (H x)) (PWord.full W) k (2 * j)
        let r ← pNodeM (m := Id) (fun x ↦ pure (H x)) (PWord.full W) k (2 * j + 1)
        pure (H (digestBytes l ++ digestBytes r)) : Id Digest) = _
    rw [pNodeM_full H W k (2 * j), pNodeM_full H W k (2 * j + 1)]
    rfl

/-- **A full word's partial tree has the deployed Merkle root.** -/
theorem pTreeRootM_full (H : Bytes → Digest) (ht : ℕ) (W : Word) :
    pTreeRootM (m := Id) (fun x ↦ pure (H x)) ht (PWord.full W) = treeRoot H ht W := by
  rw [pTreeRootM, pNodeM_full, treeRoot, MerkleTree.root, leavesOf, Vector.map_ofFn]
  exact (rootOfLevel_ofFn (nodeHash H) ht (fun i ↦ leafHash H (W i))).symm

/-! ## The stacks a partial word binds -/

/-- The encoding of `q` agrees with the partial word `P` at every lane of every column of `S`,
every one of them present. -/
def SAgrees (μ R ht : ℕ) (P : PWord) (q : Column μ)
    (S : Finset (Fin (2 ^ (μ - laneBits + R)))) : Prop :=
  ∀ v ∈ S, P.Present ht v ∧ ∀ u, laneOf P.word u v = enc (μ - laneBits) R (blockOf q u) v

/-- **The candidates of a partial word** (strict): the stacks whose encoding agrees with it on at
least `A` present columns; a column under a hole counts as a disagreement. -/
def SCandidates (μ R A ht : ℕ) (P : PWord) : Set (Column μ) :=
  {q | ∃ S, A ≤ S.card ∧ SAgrees μ R ht P q S}

/-- A full word's candidates are its candidates. -/
theorem sCandidates_full (μ R A ht : ℕ) (W : Word) :
    SCandidates μ R A ht (PWord.full W) = Candidates μ R A W := by
  ext q
  show (∃ S, A ≤ S.card ∧ SAgrees μ R ht (PWord.full W) q S) ↔
    ∃ S, A ≤ S.card ∧ EndToEnd.Agrees μ R W q S
  refine exists_congr fun S ↦ and_congr_right fun _ ↦ ?_
  exact ⟨fun h v hv u ↦ (h v hv).2 u, fun h v hv ↦ ⟨fun _ _ ↦ rfl, h v hv⟩⟩

/-- **A word without holes equal to `W` on every row has `W`'s candidates.** -/
theorem mem_sCandidates_of_candidates {μ R A ht : ℕ} {W : Word} {P : PWord}
    (hfull : ∀ v < 2 ^ (μ - laneBits + R), P.Present ht v)
    (h : ∀ v < 2 ^ (μ - laneBits + R), W v = P.word v) {q : Column μ}
    (hq : q ∈ Candidates μ R A W) : q ∈ SCandidates μ R A ht P := by
  obtain ⟨S, hS, hag⟩ := hq
  refine ⟨S, hS, fun v hv ↦ ⟨hfull v v.isLt, fun u ↦ ?_⟩⟩
  rw [← hag v hv u]
  simp only [laneOf, h v v.isLt]

end
end LeanVM.E2E
