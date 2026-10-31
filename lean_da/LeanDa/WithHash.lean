module

public import Statement.LeanDa
public import Common.WithHash

/-!
# LeanDA with a hash of its own

The statement's LeanDA (`Statement/LeanDa.lean`) hashes with Keccak-256 over the permutation it is
given (`LeanDa.keccakDigestBytes`). Benedikt Wagner's framework and its proofs reason with the hash
a parameter of its own, `H`, beside the sponge's permutation `P`: these are LeanDA's algorithms in
that form, each the statement's definition with the hash a parameter (the commitment, the openings,
the membership challenges' duplex, the vector digest, the relation), and LeanDA's games and end
statements with the hash Keccak-256 over `π` as a call of its own (`keccak256OverPermutation`).
`LeanDa.WithHashBridge` proves the statement's these with the hash Keccak-256 over the permutation.

The framework, the games and the end statements are Benedikt Wagner's
(https://github.com/b-wagn/fv-pq-da, Apache-2.0, `lean_da/NOTICE`), moved to the
random-permutation model.
-/

@[expose] public section

open Polynomial OracleComp OracleSpec ENNReal Common MeasureTheory

set_option linter.unusedSectionVars false

namespace LeanDa

open PqDas
open LeanVM.Semantics (KeccakState)
open LeanVM.Protocol.KeccakHash (keccak256With)

section Pure

variable (H : List UInt8 → DigestBytes)

/-- The digest of a cell (`hash_cells`). -/
def cellDigestWithHash (x : Cell) : DigestBytes := H (cellBytes x)

/-- One level up a Merkle tree: node `i` hashes nodes `2i` and `2i + 1`. -/
def upWithHash (f : ℕ → DigestBytes) (i : ℕ) : DigestBytes :=
  H (pairBytes (f (2 * i)) (f (2 * i + 1)))

/-- The root of the Merkle tree over the leaves `f 0 … f (2^d - 1)` (`tree_from_leaves`). -/
def merkleRootWithHash : ℕ → (ℕ → DigestBytes) → DigestBytes
  | 0, f => f 0
  | d + 1, f => merkleRootWithHash d (upWithHash H f)

/-- The authentication path of leaf `idx`, siblings from the bottom. -/
def merklePathWithHash : ℕ → (ℕ → DigestBytes) → ℕ → List DigestBytes
  | 0, _, _ => []
  | d + 1, f, idx => f (sibling idx) :: merklePathWithHash d (upWithHash H f) (idx / 2)

/-- The row tree's leaves: each padded row's digest of its first `64` cell digests. -/
def rowLeavesWithHash {r : ℕ} (c : Fin (r * 128) → Cell) (i : ℕ) : DigestBytes :=
  H ((List.ofFn fun j : Fin 64 ↦ cellDigestWithHash H (paddedCell c i j)).flatMap Vector.toList)

/-- The column tree's leaves: leaf `j · 2^⌈log₂ r⌉ + i` is cell `j` of padded row `i`. -/
def colLeavesWithHash {r : ℕ} (c : Fin (r * 128) → Cell) (l : ℕ) : DigestBytes :=
  cellDigestWithHash H (paddedCell c (l % nPad r) (l / nPad r))

/-- The row root (`root_row`). -/
def rowRootWithHash {r : ℕ} (c : Fin (r * 128) → Cell) : DigestBytes :=
  merkleRootWithHash H (logPad r) (rowLeavesWithHash H c)

/-- The column root (`root_col`). -/
def colRootWithHash {r : ℕ} (c : Fin (r * 128) → Cell) : DigestBytes :=
  merkleRootWithHash H (7 + logPad r) (colLeavesWithHash H c)

/-- **The root of a matrix** (`commit_codewords`): `H(rowRoot ‖ colRoot)`. -/
def commitCellsWithHash {r : ℕ} (c : Fin (r * 128) → Cell) : DigestBytes :=
  H (pairBytes (rowRootWithHash H c) (colRootWithHash H c))

/-- The honest opening of a position. -/
def openCellWithHash {r : ℕ} (c : Fin (r * 128) → Cell) (p : Fin (r * 128)) : Opening :=
  ⟨rowRootWithHash H c, merklePathWithHash H (7 + logPad r) (colLeavesWithHash H c) (colIndex p)⟩

/-- One level of a Merkle tree: the digests of neighbouring pairs (`tree_from_leaves`). -/
def treeLevelWithHash (nodes : List DigestBytes) : List DigestBytes :=
  (List.range (nodes.length / 2)).map (upWithHash H fun i ↦ nodes.getD i default)

/-- The root of the Merkle tree over a power-of-two number of digests (`tree_from_leaves`; on
other lengths, which `commitCodewords` never passes, the crate panics). -/
def treeRootWithHash (nodes : List DigestBytes) : DigestBytes :=
  if nodes.length ≤ 1 then nodes.headD default else treeRootWithHash (treeLevelWithHash H nodes)
termination_by nodes.length
decreasing_by simp only [treeLevelWithHash, List.length_map, List.length_range]; omega

/-- The digest of cell `j` of a codeword (`hash_cells`). -/
def listCellDigestWithHash (row : List K) (j : ℕ) : DigestBytes :=
  H ((listCell row j).flatMap kBytes)

/-- A row's digest: the hash of its payload cells' digests. -/
def rowDigestWithHash (row : List K) : DigestBytes :=
  H ((List.range payloadCells).flatMap fun j ↦ (listCellDigestWithHash H row j).toList)

/-- The digest of the zero cell, which pads the columns (`padding_digests`). -/
def paddingCellWithHash : DigestBytes := H ((List.replicate cellSymbols 0).flatMap kBytes)

/-- The digest of the zero row, which pads the row tree (`padding_digests`). -/
def paddingRowWithHash : DigestBytes :=
  H ((List.replicate payloadCells (paddingCellWithHash H)).flatMap Vector.toList)

/-- **The root of a matrix of codewords, as the crate computes it** (`commit_codewords`): the
rows padded to a power of two, the hash of the row tree's root and the column tree's. -/
def commitCodewordsWithHash (rows : List (List K)) : DigestBytes :=
  let n := nPad rows.length
  let rowTree := treeRootWithHash H
    (rows.map (rowDigestWithHash H) ++ List.replicate (n - rows.length) (paddingRowWithHash H))
  let columnTree :=
    treeRootWithHash H ((List.range cellsPerRow).flatMap fun j ↦ (List.range n).map fun i ↦
    if h : i < rows.length then listCellDigestWithHash H rows[i] j else paddingCellWithHash H)
  H (pairBytes rowTree columnTree)

end Pure

section Monadic

variable {m : Type → Type} [Monad m] (H : List UInt8 → m DigestBytes)
  (P : KeccakState → m KeccakState)

/-- A sponge with no public input of its own, seeded from the hash of `label`
(`Sponge::from_label`). -/
def Sponge.fromLabelMWithHash (label : List UInt8) : m Sponge := do
  let iv ← H label
  Sponge.newM P iv (Vector.replicate 32 0)

/-- **The challenges `z_0 … z_13` of a root** (`membership_challenges`, `verifier/src/da.rs:15-22`):
a sponge from the label, the root's words observed as two scalars `(w_0, w_1, 0)` and
`(w_2, w_3, 0)`, then `14` samples. -/
def membershipChallengesMWithHash (root : DigestBytes) : m (List E) := do
  let s ← Sponge.fromLabelMWithHash H P label
  let s ← Sponge.observeM P s (ofLimbs (word root 0) (word root 1) 0)
  let s ← Sponge.observeM P s (ofLimbs (word root 2) (word root 3) 0)
  Sponge.samplesM P logK s

/-- Climb from `node` at index `idx` along the siblings `path`. -/
def walkMWithHash : ℕ → DigestBytes → List DigestBytes → m DigestBytes
  | _, node, [] => pure node
  | idx, node, s :: rest => do
    let d ← H (if idx % 2 = 0 then pairBytes node s else pairBytes s node)
    walkMWithHash (idx / 2) d rest

/-- **Verification of a cell opening**: a path of the column tree's height that climbs from the
cell's digest to a column root, which hashed after the row root gives the commitment. -/
def verifyCellMWithHash (r : ℕ) (com : DigestBytes) (p : Fin (r * 128)) (x : Cell) (τ : Opening) :
    m Bool :=
  do
  let d ← H (cellBytes x)
  let w ← walkMWithHash H (colIndex p) d τ.path
  let root ← H (pairBytes τ.rowRoot w)
  pure (decide (τ.path.length = 7 + logPad r) && decide (root = com))

/-- One level up a Merkle tree over an oracle (`up`). -/
def upMWithHash (f : ℕ → m DigestBytes) (i : ℕ) : m DigestBytes := do
  let a ← f (2 * i)
  let b ← f (2 * i + 1)
  H (pairBytes a b)

/-- The root of a Merkle tree over an oracle (`merkleRoot`). -/
def merkleRootMWithHash : ℕ → (ℕ → m DigestBytes) → m DigestBytes
  | 0, f => f 0
  | d + 1, f => merkleRootMWithHash d (upMWithHash H f)

/-- The row tree's leaves over an oracle (`rowLeaves`). -/
def rowLeavesMWithHash {r : ℕ} (c : Fin (r * 128) → Cell) (i : ℕ) : m DigestBytes := do
  let ds ← (List.range 64).mapM fun j ↦ H (cellBytes (paddedCell c i j))
  H (ds.flatMap Vector.toList)

/-- The column tree's leaves over an oracle (`colLeaves`). -/
def colLeavesMWithHash {r : ℕ} (c : Fin (r * 128) → Cell) (l : ℕ) : m DigestBytes :=
  H (cellBytes (paddedCell c (l % nPad r) (l / nPad r)))

/-- The row root over an oracle (`rowRoot`). -/
def rowRootMWithHash {r : ℕ} (c : Fin (r * 128) → Cell) : m DigestBytes :=
  merkleRootMWithHash H (logPad r) (rowLeavesMWithHash H c)

/-- The column root over an oracle (`colRoot`). -/
def colRootMWithHash {r : ℕ} (c : Fin (r * 128) → Cell) : m DigestBytes :=
  merkleRootMWithHash H (7 + logPad r) (colLeavesMWithHash H c)

/-- **The root of a matrix over an oracle** (`commitCells`). -/
def commitCellsMWithHash {r : ℕ} (c : Fin (r * 128) → Cell) : m DigestBytes := do
  let a ← rowRootMWithHash H c
  let b ← colRootMWithHash H c
  H (pairBytes a b)

end Monadic

section VectorDigest

variable (H : List UInt8 → DigestBytes)

/-- The digest of column `j` of a vector, its entries `256 j … 256 j + 255`. -/
def columnDigestWithHash (vector : List E) (j : ℕ) : DigestBytes :=
  H (limbBytes ((vector.drop (j * cellSymbols)).take cellSymbols))

/-- **The digest of a vector** (`vector_digest`, `verifier/src/da.rs:87-96`): the hash of its
`128` columns' digests, in order. The crate takes vectors of `2^15` entries and panics on others. -/
def vectorDigestWithHash (vector : List E) : DigestBytes :=
  H ((List.range cellsPerRow).flatMap fun j ↦ (columnDigestWithHash H vector j).toList)

end VectorDigest

/-- **The relation the argument proves**, with a hash `H` and the sponge's permutation `P` in any
monad: the cells commit to the root and pass the membership test on the root's challenges, drawn
by the deployed duplex (`membershipChallengesM`). In the games `H` is Keccak-256 over `π`
(`keccak256OverPermutation`) and `P` is `π` (`queryPermutation`). -/
noncomputable def relationMWithHash {m : Type → Type} [Monad m] (H : List UInt8 → m DigestBytes)
    (P : KeccakState → m KeccakState) {r : ℕ} (root : DigestBytes) (c : Fin (r * 128) → Cell) :
      m Bool := do
  let zs ← membershipChallengesMWithHash H P root
  let d ← commitCellsMWithHash H c
  pure (decide (d = root) && membershipCheck (toChallenges zs) c)

/-- **Keccak-256 over a permutation `π`** (`keccak256With`), its digest's bytes: the hash `H` of
the games when the permutation is `π` (`runWithRandomPermutation`). -/
def keccak256WithPermutation (π : KeccakState → KeccakState) (a : List UInt8) : DigestBytes :=
  (Id.run (keccak256With (fun x ↦ pure (π x)) a)).toBytes

/-- **LeanDA's relation for a permutation `π`**: `relationM` with Keccak-256 over `π` and `π`. -/
noncomputable def relationForPermutationWithHash (r : ℕ) (π : Equiv.Perm KeccakState)
    (root : DigestBytes)
    (c : Fin (r * 128) → Cell) : Bool :=
  Id.run (relationMWithHash (fun a ↦ pure (keccak256WithPermutation π a))
    (fun x ↦ pure (π x)) root c)

variable (r : ℕ) {Crs Proof : Type} (ps : LeanDaArgument r Crs Proof)
  (ext : StraightLineExtractor DigestBytes (Fin (r * 128) → Cell) Crs Proof)

/-- **The position-binding game**: the argument's setup, the adversary, then the verifications:
the argument's of the root's proof and the two openings'; it wins when all verify, at two
different cells. -/
def positionBindingGameWithHash (A : PositionBindingAdversary r Crs Proof) :
    OracleComp RandomPermutationOracles Bool := do
  let crs ← liftM ps.setup
  let (com, p, x, τ, x', τ') ← A ((), crs)
  let ok ← ps.verify crs com.1 com.2
  let b ← verifyCellMWithHash keccak256OverPermutation r com.1 p x τ
  let b' ← verifyCellMWithHash keccak256OverPermutation r com.1 p x' τ'
  pure (decide (x ≠ x') && ok && b && b')

/-- **The code-binding game**: the argument's setup, the adversary, then the verifications; it wins
when the root's proof and every opening verify and no codeword agrees with the opened cells. -/
noncomputable def codeBindingGameWithHash (A : CodeBindingAdversary r Crs Proof) :
    OracleComp RandomPermutationOracles Bool := do
  let crs ← liftM ps.setup
  let (com, opened) ← A ((), crs)
  let ok ← ps.verify crs com.1 com.2
  let verdicts ← opened.mapM fun o ↦
    verifyCellMWithHash keccak256OverPermutation r com.1 o.1 o.2.1 o.2.2
  pure (ok && verdicts.all id && !decide ((code r).Consistent (opened.map fun o ↦ (o.1, o.2.1))))

/-- **The argument's knowledge-soundness game** (Wagner's, Foundations Definition 18, in the
random-permutation model with a straight-line extractor): the argument's setup, the adversary with
its queries logged, the argument's verification, then the relation's check on the cells the
extractor reads off the proof and the adversary's transcript; it wins when the proof verifies and
the extracted cells do not satisfy the relation (`relationM` over Keccak-256 over `π`, and `π`). -/
noncomputable def knowledgeSoundnessGameWithHash (B : KnowledgeSoundnessAdversary Crs Proof) :
    OracleComp RandomPermutationOracles Bool := do
  let crs ← liftM ps.setup
  let ((root, proof), log) ← (simulateQ loggedOracles (B crs)).run []
  let v ← ps.verify crs root proof
  let ok ← relationMWithHash keccak256OverPermutation queryPermutation root (ext crs root proof log)
  pure (v && !ok)

/-- **The completeness experiment for a permutation `π`** (Wagner's, Foundations Definition 8,
with the hash and the oracles answered by `π`): the argument's setup; the honest commitment to the
message `msg`, the root of its encoding's cells hashed with Keccak-256 over `π`; the argument's
honest proof for the root and its verification, both with the oracles answered by `π`; and the
verification of the encoding's cell at `p` with its honest opening. -/
noncomputable def completenessExperimentWithHash (π : Equiv.Perm KeccakState)
    (ps : LeanDaArgument r Crs Proof)
    (msg : Fin r → Payload) (p : Fin (r * 128)) : ProbComp Bool := do
  let crs ← ps.setup
  let c := (code r).encode msg
  let root := commitCellsWithHash (keccak256WithPermutation π) c
  let ok ← simulateQ (oraclesFromPermutation π) (ps.prove crs root c >>= ps.verify crs root)
  pure (ok && Id.run
    (verifyCellMWithHash (fun a ↦ pure (keccak256WithPermutation π a)) r root p (c p)
    (openCellWithHash (keccak256WithPermutation π) c p)))

/-- **LeanDA is perfectly complete in the random-permutation model, for every permutation.**
For any number `r` of rows, every permutation `π` of the Keccak state, and every argument `ps`
perfectly complete for LeanDA's relation for every permutation (`relationForPermutation`, the hash
Keccak-256 over `π` and the challenges the deployed duplex over `π`; the argument's prover and
verifier answered by `π`): every position `p` of the honest commitment to every message `msg`
opens and verifies with probability one (`completenessExperiment`). Holding for each `π`, it holds
for every outcome of the binding statements' uniformly random permutation. The proof is Wagner's
completeness proof, transferred. Proved by `LeanDa.leanDa_perfectlyComplete_rpm`. -/
abbrev PerfectlyCompleteRpmWithHash : Prop :=
  ∀ (r : ℕ) (π : Equiv.Perm KeccakState) {Crs Proof : Type} (ps : LeanDaArgument r Crs Proof),
    ps.PerfectlyComplete (relationForPermutationWithHash r) →
      ∀ (msg : Fin r → Payload) (p : Fin (r * 128)),
        Pr{let b ← completenessExperimentWithHash r π ps msg p}[b = true] = 1

/-- **LeanDA is position binding in the random-permutation model.** For every argument `ps` (any
prover and verifier) and every adversary whose game, verifications included, makes at most `Q`
calls of `π` and `π⁻¹` on every path (`permutationCallCost`; a hash of `n` bytes, Keccak-256 over
`π`, makes `⌊n / 136⌋ + 1`; the argument's verifier's included), the probability of opening a
position to two different cells is at most `(Q + 1)² · 2^-256`, for every `Q` (past `2^128` the
bound exceeds one). Proved by
`LeanDa.leanDa_positionBinding_rpm`. -/
abbrev PositionBindingRpmWithHash : Prop :=
  ∀ (r : ℕ) {Crs Proof : Type} (ps : LeanDaArgument r Crs Proof)
    (A : PositionBindingAdversary r Crs Proof)
    (Q : ℕ), QueryCostAtMost (positionBindingGameWithHash r ps A) permutationCallCost Q →
      Pr{let b ← runWithRandomPermutation (positionBindingGameWithHash r ps A)}[b = true] ≤
        ((Q : ℝ≥0∞) + 1) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256

/-- **LeanDA is code binding in the random-permutation model, for an argument knowledge sound in
it** (Benedikt Wagner's framework and games, moved to the random-permutation model, with a
straight-line argument in place of his forking lemma). For `1 ≤ r ≤ 1024` rows (`maxRows`, the
crate's bound), every argument `ps` (its prover and verifier querying the model's oracles) and
straight-line extractor `ext` (reading the adversary's transcript): if every adversary whose
knowledge-soundness game (`knowledgeSoundnessGame`, the argument's verifier and the relation's check
included) makes at most `q ≤ 2^128` permutation calls (`permutationCallCost`) wins it with
probability at most `(q + c) · 2^-k`, then every adversary whose code-binding game, verifications
included, makes at most `Q` calls breaks code binding with probability at most

`(Q + c + 2^22) · 2^-k + (Q + 2^22) · 2^-188 + (Q + 2^22)² · 2^-247`.

The first term is the argument's knowledge soundness against the code-binding adversary itself,
its transcript handed to the extractor (at most `Q + 2^22` calls with the relation's check). The
second is the membership test's soundness, `14 / 2^192` for each of at most `Q + 14` roots whose
challenges are drawn. The third gathers the transfer to the two-oracle model and the duplex
lemma, of the two games, and the hash's bad events among at most `2 Q + 2^20` hash and challenge
queries: a collision, or a fresh answer that is a digest an earlier input or a root with drawn
challenges already carries; it exceeds one before `Q = 2^124`.

The argument queries the oracles the adversary does, so its knowledge soundness here is the
usual one of an argument in the random-permutation model, with a straight-line extractor reading
the adversary's queries, as leanVM's (`LeanVM.KnowledgeSoundness`); an argument may satisfy it and
be perfectly complete for every permutation (`PerfectlyCompleteRpm`). Proved by
`LeanDa.leanDa_codeBinding_rpm_bound`. -/
abbrev CodeBindingRpmWithHash : Prop :=
  ∀ (r : ℕ) {Crs Proof : Type} (ps : LeanDaArgument r Crs Proof)
    (ext : StraightLineExtractor DigestBytes (Fin (r * 128) → Cell) Crs Proof) (c k : ℕ),
    (∀ (B : KnowledgeSoundnessAdversary Crs Proof) (q : ℕ),
      QueryCostAtMost (knowledgeSoundnessGameWithHash r ps ext B) permutationCallCost q →
      q ≤ 2 ^ 128 →
        Pr{let b ← runWithRandomPermutation (knowledgeSoundnessGameWithHash r ps ext B)}[b = true] ≤
        ((q : ℝ≥0∞) + c) * (2 : ℝ≥0∞)⁻¹ ^ k) →
    1 ≤ r → r ≤ maxRows →
    ∀ (A : CodeBindingAdversary r Crs Proof) (Q : ℕ),
      QueryCostAtMost (codeBindingGameWithHash r ps A) permutationCallCost Q →
        Pr{let b ← runWithRandomPermutation (codeBindingGameWithHash r ps A)}[b = true] ≤
          ((Q : ℝ≥0∞) + c + 2 ^ 22) * (2 : ℝ≥0∞)⁻¹ ^ k + ((Q : ℝ≥0∞) + 2 ^ 22) *
            (2 : ℝ≥0∞)⁻¹ ^ 188 +
            ((Q : ℝ≥0∞) + 2 ^ 22) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 247

end LeanDa

end
