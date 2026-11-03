module

public import LeanDa.WithHash
public import Common.Lanes

/-!
# The statement's LeanDA is the hash-parameter form, the hash over the permutation

The statement's LeanDA hashes with Keccak-256 over the permutation it is given
(`keccakDigestBytes`); Benedikt Wagner's framework and its proofs take the hash as a parameter of
its own (`LeanDa.WithHash`). Each statement definition is the hash-parameter one with the hash
Keccak-256 over the permutation (`hashOver π`, `keccakDigestBytes P`), by unfolding, and by
induction for the recursive ones (`merkleRootWith_id`, `walkM_eq_withHash`,
`merkleRootM_eq_withHash`); the statement's membership challenges, drawn with the leanVM verifier's
sponge, are the proofs' duplex's (`membershipChallengesM_eq_withHash`). So the statement's games
are the hash-parameter ones (`positionBindingGame_eq_withHash`, …), and its end statements follow from those
(`positionBindingRpm_of_withHash`, …).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal Common

namespace LeanDa

open LeanVM.Semantics (KeccakState)

/-! ## The commitment over a pure permutation -/

section Pure

variable (π : KeccakState → KeccakState)

/-- `π` as a permutation in `Id`. -/
abbrev pureIn (x : KeccakState) : Id KeccakState := pure (π x)

theorem merkleRootWith_id : ∀ (d : ℕ) (f : ℕ → DigestBytes),
    Id.run (merkleRootWith (pureIn π) d fun i ↦ pure (f i)) = merkleRootWithHash (hashOver π) d f
  | 0, _ => rfl
  | d + 1, f => merkleRootWith_id d (upWithHash (hashOver π) f)

theorem merklePathWith_id : ∀ (d : ℕ) (f : ℕ → DigestBytes) (index : ℕ),
    Id.run (merklePathWith (pureIn π) d (fun i ↦ pure (f i)) index) =
      merklePathWithHash (hashOver π) d f index
  | 0, _, _ => rfl
  | d + 1, f, index => by
    show f (sibling index) ::
        Id.run (merklePathWith (pureIn π) d (fun i ↦ pure (upWithHash (hashOver π) f i))
          (index / 2)) = _
    rw [merklePathWith_id d]
    rfl

theorem rowLeavesWith_id {r : ℕ} (c : Fin (r * 128) → Cell) (i : ℕ) :
    Id.run (rowLeavesWith (pureIn π) c i) = rowLeavesWithHash (hashOver π) c i := by
  simp only [rowLeavesWith, rowLeavesWithHash, Id.run_bind, List.idRun_mapM, List.ofFn_eq_map,
    ← List.map_coe_finRange_eq_range, List.map_map]
  rfl

theorem rowRoot_id {r : ℕ} (c : Fin (r * 128) → Cell) :
    Id.run (rowRootWith (pureIn π) c) = rowRootWithHash (hashOver π) c := by
  have h : rowLeavesWith (pureIn π) c = fun i ↦ pure (rowLeavesWithHash (hashOver π) c i) :=
    funext fun i ↦ rowLeavesWith_id π c i
  rw [rowRootWith, h, merkleRootWith_id]
  rfl

theorem columnRoot_id {r : ℕ} (c : Fin (r * 128) → Cell) :
    Id.run (columnRootWith (pureIn π) c) = colRootWithHash (hashOver π) c :=
  merkleRootWith_id π _ _

theorem commitCells_eq_withHash {r : ℕ} (c : Fin (r * 128) → Cell) :
    commitCells π c = commitCellsWithHash (hashOver π) c := by
  show hashOver π (pairBytes (Id.run (rowRootWith (pureIn π) c))
    (Id.run (columnRootWith (pureIn π) c))) = _
  rw [rowRoot_id, columnRoot_id]
  rfl

theorem openCell_eq_withHash {r : ℕ} (c : Fin (r * 128) → Cell) (p : Fin (r * 128)) :
    openCell π c p = openCellWithHash (hashOver π) c p := by
  show (⟨Id.run (rowRootWith (pureIn π) c), Id.run (merklePathWith (pureIn π)
    (7 + logPaddedRowCount r) (fun l ↦ pure (colLeavesWithHash (hashOver π) c l))
    (columnTreeIndex p))⟩ : CellOpening) = _
  rw [rowRoot_id, merklePathWith_id]
  rfl

theorem commitCodewords_eq_withHash (rows : List (List K)) :
    commitCodewords π rows = commitCodewordsWithHash (hashOver π) rows := rfl

theorem vectorDigest_eq_withHash (vector : List E) :
    vectorDigest π vector = vectorDigestWithHash (hashOver π) vector := rfl

end Pure

/-! ## The challenges' sponge

The statement's sponge (`Field.lean`, tags in `ℕ`) runs as the proofs' (`Sponge`, tags in `K`):
`toCompile` maps the one to the other, and every step commutes with it. -/

open LeanVM.Protocol.Compile (pendingLanes challengeOf seedInput)
open LeanVM.Protocol.KeccakHash (digestHalves)

/-- The statement's sponge of a proofs' sponge: the tags as the numbers of their lanes. -/
def Sponge.toCompile (s : Sponge) : LeanVM.Protocol.Compile.Sponge :=
  ⟨s.state, s.pending.map fun x ↦ (x.1, x.2.lane.toNat)⟩

theorem pendingLanes_toCompile (pending : List (E × K)) :
    pendingLanes (pending.map fun x ↦ (x.1, x.2.lane.toNat)) = (rateWords pending).map K.lane := by
  induction pending with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, pendingLanes, List.flatMap_cons, rateWords, List.map_append] at ih ⊢
    rw [ih]
    simp [limb]

theorem duplexInput_toCompile (s : Sponge) :
    LeanVM.Protocol.Compile.duplexInput s.toCompile = duplexInput s := by
  apply Vector.ext
  intro i hi
  simp only [LeanVM.Protocol.Compile.duplexInput, duplexInput, Vector.getElem_ofFn]
  by_cases h : i < 16
  · simp only [h, ↓reduceIte, show i < rateLanes from h, Sponge.toCompile, pendingLanes_toCompile]
    rw [show (0 : UInt64) = K.lane 0 from rfl, List.getD_map]
  · simp only [h, ↓reduceIte, show ¬ i < rateLanes from h, Sponge.toCompile]
    simp [LeanVM.Semantics.Keccak.lane, hi]

theorem challengeOf_eq (state : KeccakState) :
    challengeOf state = ofLimbs (K.ofLane state[0]) (K.ofLane state[1]) (K.ofLane state[2]) := by
  simp [challengeOf, LeanVM.Semantics.Keccak.lane]
  rfl

theorem digestHalves_digestOfBytes (root : DigestBytes) :
    digestHalves (digestOfBytes root) = (ofLimbs (digestWord root 0) (digestWord root 1) 0,
      ofLimbs (digestWord root 2) (digestWord root 3) 0) := by
  simp only [digestHalves, digestOfBytes, digestWord, Vector.getElem_ofFn]
  rfl

section Monadic

variable {m : Type → Type} [Monad m] (P : KeccakState → m KeccakState)

theorem duplex_toCompile [LawfulMonad m] (s : Sponge) :
    LeanVM.Protocol.Compile.duplex P s.toCompile = Sponge.toCompile <$> Sponge.duplexWith P s := by
  simp only [LeanVM.Protocol.Compile.duplex, Sponge.duplexWith, duplexInput_toCompile,
    map_bind, map_pure]
  rfl

theorem absorb_toCompile [LawfulMonad m] (s : Sponge) (x : E) (tag : K) :
    LeanVM.Protocol.Compile.absorb P s.toCompile x tag.lane.toNat =
      Sponge.toCompile <$> Sponge.absorbWith P s x tag := by
  have hlen : s.toCompile.pending.length = s.pending.length := by simp [Sponge.toCompile]
  simp only [LeanVM.Protocol.Compile.absorb, Sponge.absorbWith, hlen,
    LeanVM.Protocol.Compile.rateScalars, rateScalars, map_bind, map_pure]
  by_cases h : s.pending.length = 4
  · simp only [h, ↓reduceIte, duplex_toCompile, bind_map_left]
    refine bind_congr fun a ↦ ?_
    simp [Sponge.toCompile]
  · simp only [h, ↓reduceIte, pure_bind]
    simp [Sponge.toCompile]

theorem squeezeChallenges_toCompile [LawfulMonad m] : ∀ (n : ℕ) (s : Sponge),
    squeezeChallenges P n s.toCompile = Sponge.samplesWith P n s
  | 0, _ => rfl
  | n + 1, s => by
    simp only [squeezeChallenges, Sponge.samplesWith, LeanVM.Protocol.Compile.squeeze,
      Sponge.sampleWith, duplex_toCompile,
      bind_assoc, pure_bind, map_eq_bind_pure_comp, Function.comp_apply]
    refine bind_congr fun s' ↦ ?_
    rw [show (Sponge.toCompile s').state = s'.state from rfl, squeezeChallenges_toCompile n,
      challengeOf_eq]

/-- The IV's words are the words of its bytes. -/
theorem freshSpongeInput_toBytes (iv : LeanVM.Protocol.Digest) :
    freshSpongeInput iv.toBytes (Vector.replicate 32 0) = seedInput iv (Vector.replicate 4 0) := by
  apply Vector.ext
  intro i hi
  have hiv : iv.toBytes.toList = LeanVM.Rpm.lanesBytes iv.toList := by
    simp [LeanVM.Protocol.Digest.toBytes, LeanVM.Protocol.KeccakHash.digestBytes,
      LeanVM.Rpm.lanesBytes, Vector.toList]
  have hz : (Vector.replicate 32 (0 : UInt8)).toList =
      LeanVM.Rpm.lanesBytes (Vector.replicate 4 (0 : UInt64)).toList := by decide
  simp only [freshSpongeInput, seedInput, Vector.getElem_ofFn, digestWord]
  split_ifs with h1 h2 <;> try rfl
  · rw [hiv, LeanVM.Rpm.leLane_lanesBytes _ _ (by simpa using h1), Vector.getElem_toList]
    rfl
  · rw [hz, LeanVM.Rpm.leLane_lanesBytes _ _ (by simp; omega), Vector.getElem_toList]
    rfl

/-- **The statement's challenges are the proofs' duplex's.** -/
theorem membershipChallengesM_eq_withHash [LawfulMonad m] (root : DigestBytes) :
    membershipChallengesWith P root = membershipChallengesMWithHash (keccakDigestBytes P) P root := by
  simp only [membershipChallengesWith, digestHalves_digestOfBytes, membershipChallengesMWithHash,
    Sponge.fromLabelMWithHash,
    keccakDigestBytes, Sponge.newWith, Sponge.observeWith, map_eq_bind_pure_comp, bind_assoc,
    pure_bind, Function.comp_apply]
  refine bind_congr fun iv ↦ ?_
  rw [freshSpongeInput_toBytes]
  refine bind_congr fun state ↦ ?_
  have h1 : (dsObserve : K).lane.toNat = LeanVM.Protocol.Compile.dsObserve := by decide
  have hs : (⟨state, []⟩ : LeanVM.Protocol.Compile.Sponge) = Sponge.toCompile ⟨state, []⟩ := rfl
  rw [hs, ← h1, absorb_toCompile, bind_map_left]
  refine bind_congr fun s ↦ ?_
  rw [absorb_toCompile, bind_map_left]
  exact bind_congr fun s ↦ squeezeChallenges_toCompile P logK s

theorem walkM_eq_withHash : ∀ (idx : ℕ) (node : DigestBytes) (path : List DigestBytes),
    climbWith P idx node path = walkMWithHash (keccakDigestBytes P) idx node path
  | _, _, [] => rfl
  | idx, node, s :: rest => by
    simp only [climbWith, walkMWithHash, walkM_eq_withHash]

theorem verifyCellM_eq_withHash (r : ℕ) (com : DigestBytes) (p : Fin (r * 128)) (x : Cell)
    (τ : CellOpening) :
    verifyCellWith P r com p x τ = verifyCellMWithHash (keccakDigestBytes P) r com p x τ := by
  simp only [verifyCellWith, verifyCellMWithHash, walkM_eq_withHash]

theorem merkleRootM_eq_withHash : ∀ (d : ℕ) (f : ℕ → m DigestBytes),
    merkleRootWith P d f = merkleRootMWithHash (keccakDigestBytes P) d f
  | 0, _ => rfl
  | d + 1, f => by rw [merkleRootWith, merkleRootMWithHash, merkleRootM_eq_withHash d]; rfl

theorem commitCellsM_eq_withHash {r : ℕ} (c : Fin (r * 128) → Cell) :
    commitCellsWith P c = commitCellsMWithHash (keccakDigestBytes P) c := by
  simp only [commitCellsWith, commitCellsMWithHash, rowRootWith, rowRootMWithHash, columnRootWith,
    colRootMWithHash, merkleRootM_eq_withHash]; rfl

theorem relationM_eq_withHash [LawfulMonad m] {r : ℕ} (root : DigestBytes) (c : Fin (r * 128) → Cell) :
    relationWith P root c = relationMWithHash (keccakDigestBytes P) P root c := by
  simp only
    [relationWith, relationMWithHash, membershipChallengesM_eq_withHash, commitCellsM_eq_withHash]

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
    LeanDaPerfectlyComplete := by
  intro r π Crs Proof ps hps msg p
  rw [completenessExperiment_eq_withHash]
  exact h r π ps (relationForPermutation_eq_withHash r ▸ hps) msg p

/-- **Position binding, from the hash-parameter form.** -/
theorem positionBindingRpm_of_withHash (h : PositionBindingRpmWithHash) :
    LeanDaPositionBinding := by
  intro r Crs Proof ps A Q hQ
  rw [positionBindingGame_eq_withHash] at hQ ⊢
  exact h r ps A Q hQ

/-- **Code binding, from the hash-parameter form.** -/
theorem codeBindingRpm_of_withHash (h : CodeBindingRpmWithHash) : LeanDaCodeBinding := by
  intro r Crs Proof ps ext c k hks hr hrmax A Q hQ
  rw [codeBindingGame_eq_withHash] at hQ ⊢
  refine h r ps ext c k (fun B q hq hq' ↦ ?_) hr hrmax A Q hQ
  rw [← knowledgeSoundnessGame_eq_withHash] at hq ⊢
  exact hks B q hq hq'

end LeanDa

end
