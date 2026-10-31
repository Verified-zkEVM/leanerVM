module

public import LeanDa.WithHash

/-!
# The statement's LeanDA is the hash-parameter form, the hash over the permutation

The statement's LeanDA hashes with Keccak-256 over the permutation it is given
(`keccakDigestBytes`); Benedikt Wagner's framework and its proofs take the hash as a parameter of
its own (`LeanDa.WithHash`). Each statement definition is the hash-parameter one with the hash
Keccak-256 over the permutation (`hashOver π`, `keccakDigestBytes P`), by unfolding, and by
induction for the recursive ones (`merkleRoot_eq_withHash`, `treeRoot_eq_withHash`,
`walkM_eq_withHash`, `merkleRootM_eq_withHash`); so the statement's games are the hash-parameter
ones (`positionBindingGame_eq_withHash`, …), and its end statements follow from those
(`positionBindingRpm_of_withHash`, …).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal Common

namespace LeanDa

open LeanVM.Semantics (KeccakState)

/-! ## The commitment -/

section Pure

variable (π : KeccakState → KeccakState)

/-- Keccak-256 over `π`, LeanDA's 32 bytes: the hash of the statement's pure algorithms. -/
abbrev hashOver (bytes : List UInt8) : DigestBytes := Id.run (keccakDigestBytes π bytes)

theorem up_eq_withHash : up π = upWithHash (hashOver π) := rfl

theorem merkleRoot_eq_withHash : ∀ (d : ℕ) (f : ℕ → DigestBytes),
    merkleRoot π d f = merkleRootWithHash (hashOver π) d f
  | 0, _ => rfl
  | d + 1, f => by rw [merkleRoot, merkleRootWithHash, up_eq_withHash, merkleRoot_eq_withHash d]

theorem merklePath_eq_withHash : ∀ (d : ℕ) (f : ℕ → DigestBytes) (idx : ℕ),
    merklePath π d f idx = merklePathWithHash (hashOver π) d f idx
  | 0, _, _ => rfl
  | d + 1, f, idx =>
    by rw [merklePath, merklePathWithHash, up_eq_withHash, merklePath_eq_withHash d]

theorem rowRoot_eq_withHash {r : ℕ} (c : Fin (r * 128) → Cell) :
    rowRoot π c = rowRootWithHash (hashOver π) c := by
  rw [rowRoot, rowRootWithHash, merkleRoot_eq_withHash]; rfl

theorem colRoot_eq_withHash {r : ℕ} (c : Fin (r * 128) → Cell) :
    colRoot π c = colRootWithHash (hashOver π) c := by
  rw [colRoot, colRootWithHash, merkleRoot_eq_withHash]; rfl

theorem commitCells_eq_withHash {r : ℕ} (c : Fin (r * 128) → Cell) :
    commitCells π c = commitCellsWithHash (hashOver π) c := by
  rw [commitCells, commitCellsWithHash, rowRoot_eq_withHash, colRoot_eq_withHash]

theorem openCell_eq_withHash {r : ℕ} (c : Fin (r * 128) → Cell) (p : Fin (r * 128)) :
    openCell π c p = openCellWithHash (hashOver π) c p := by
  rw [openCell, openCellWithHash, rowRoot_eq_withHash, merklePath_eq_withHash]; rfl

theorem treeRoot_eq_withHash (nodes : List DigestBytes) :
    treeRoot π nodes = treeRootWithHash (hashOver π) nodes := by
  induction h : nodes.length using Nat.strong_induction_on generalizing nodes with
  | _ n ih =>
    rw [treeRoot, treeRootWithHash]
    split
    · rfl
    · have hlt : (treeLevel π nodes).length < n := by
        simp only [treeLevel, List.length_map, List.length_range]; omega
      exact ih _ hlt _ rfl

theorem commitCodewords_eq_withHash (rows : List (List K)) :
    commitCodewords π rows = commitCodewordsWithHash (hashOver π) rows := by
  simp only [commitCodewords, commitCodewordsWithHash, treeRoot_eq_withHash]; rfl

theorem vectorDigest_eq_withHash (vector : List E) :
    vectorDigest π vector = vectorDigestWithHash (hashOver π) vector := rfl

end Pure

/-! ## The duplex, the openings' check and the relation -/

section Monadic

variable {m : Type → Type} [Monad m] (P : KeccakState → m KeccakState)

theorem membershipChallengesM_eq_withHash (root : DigestBytes) :
    membershipChallengesM P root = membershipChallengesMWithHash (keccakDigestBytes P) P root :=
  rfl

theorem walkM_eq_withHash : ∀ (idx : ℕ) (node : DigestBytes) (path : List DigestBytes),
    walkM P idx node path = walkMWithHash (keccakDigestBytes P) idx node path
  | _, _, [] => rfl
  | idx, node, s :: rest => by
    simp only [walkM, walkMWithHash, walkM_eq_withHash]

theorem verifyCellM_eq_withHash (r : ℕ) (com : DigestBytes) (p : Fin (r * 128)) (x : Cell)
    (τ : Opening) :
    verifyCellM P r com p x τ = verifyCellMWithHash (keccakDigestBytes P) r com p x τ := by
  simp only [verifyCellM, verifyCellMWithHash, walkM_eq_withHash]

theorem merkleRootM_eq_withHash : ∀ (d : ℕ) (f : ℕ → m DigestBytes),
    merkleRootM P d f = merkleRootMWithHash (keccakDigestBytes P) d f
  | 0, _ => rfl
  | d + 1, f => by rw [merkleRootM, merkleRootMWithHash, merkleRootM_eq_withHash d]; rfl

theorem commitCellsM_eq_withHash {r : ℕ} (c : Fin (r * 128) → Cell) :
    commitCellsM P c = commitCellsMWithHash (keccakDigestBytes P) c := by
  simp only [commitCellsM, commitCellsMWithHash, rowRootM, rowRootMWithHash, colRootM,
    colRootMWithHash, merkleRootM_eq_withHash]; rfl

theorem relationM_eq_withHash {r : ℕ} (root : DigestBytes) (c : Fin (r * 128) → Cell) :
    relationM P root c = relationMWithHash (keccakDigestBytes P) P root c := by
  simp only
    [relationM, relationMWithHash, membershipChallengesM_eq_withHash, commitCellsM_eq_withHash]

end Monadic

/-! ## The games and the end statements -/

/-- Keccak-256 over the model's `π` is `keccak256OverPermutation`. -/
theorem keccakDigestBytes_queryPermutation :
    keccakDigestBytes queryPermutation = keccak256OverPermutation := rfl

theorem relationForPermutation_eq_withHash (r : ℕ) :
    relationForPermutation r = relationForPermutationWithHash r := by
  funext π root c
  simp only [relationForPermutation, relationForPermutationWithHash, relationM_eq_withHash]; rfl

variable (r : ℕ) {Crs Proof : Type} (ps : LeanDaArgument r Crs Proof)
  (ext : StraightLineExtractor DigestBytes (Fin (r * 128) → Cell) Crs Proof)

theorem positionBindingGame_eq_withHash (A : PositionBindingAdversary r Crs Proof) :
    positionBindingGame r ps A = positionBindingGameWithHash r ps A := by
  simp only [positionBindingGame, positionBindingGameWithHash, verifyCellM_eq_withHash,
    keccakDigestBytes_queryPermutation]

theorem codeBindingGame_eq_withHash (A : CodeBindingAdversary r Crs Proof) :
    codeBindingGame r ps A = codeBindingGameWithHash r ps A := by
  simp only [codeBindingGame, codeBindingGameWithHash, verifyCellM_eq_withHash,
    keccakDigestBytes_queryPermutation]

theorem knowledgeSoundnessGame_eq_withHash (B : KnowledgeSoundnessAdversary Crs Proof) :
    knowledgeSoundnessGame r ps ext B = knowledgeSoundnessGameWithHash r ps ext B := by
  simp only [knowledgeSoundnessGame, knowledgeSoundnessGameWithHash, relationM_eq_withHash,
    keccakDigestBytes_queryPermutation]

theorem completenessExperiment_eq_withHash (π : Equiv.Perm KeccakState) (msg : Fin r → Payload)
    (p : Fin (r * 128)) :
    completenessExperiment r π ps msg p = completenessExperimentWithHash r π ps msg p := by
  simp only [completenessExperiment, completenessExperimentWithHash, commitCells_eq_withHash,
    openCell_eq_withHash, verifyCellM_eq_withHash]; rfl

/-- **Perfect completeness, from the hash-parameter form.** -/
theorem perfectlyCompleteRpm_of_withHash (h : PerfectlyCompleteRpmWithHash) :
    PerfectlyCompleteRpm := by
  intro r π Crs Proof ps hps msg p
  rw [completenessExperiment_eq_withHash]
  exact h r π ps (relationForPermutation_eq_withHash r ▸ hps) msg p

/-- **Position binding, from the hash-parameter form.** -/
theorem positionBindingRpm_of_withHash (h : PositionBindingRpmWithHash) : PositionBindingRpm := by
  intro r Crs Proof ps A Q hQ
  rw [positionBindingGame_eq_withHash] at hQ ⊢
  exact h r ps A Q hQ

/-- **Code binding, from the hash-parameter form.** -/
theorem codeBindingRpm_of_withHash (h : CodeBindingRpmWithHash) : CodeBindingRpm := by
  intro r Crs Proof ps ext c k hks hr hrmax A Q hQ
  rw [codeBindingGame_eq_withHash] at hQ ⊢
  refine h r ps ext c k (fun B q hq hq' ↦ ?_) hr hrmax A Q hQ
  rw [← knowledgeSoundnessGame_eq_withHash] at hq ⊢
  exact hks B q hq hq'

end LeanDa

end
