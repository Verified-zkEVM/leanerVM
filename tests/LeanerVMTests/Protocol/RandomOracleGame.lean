import LeanerVM.Protocol.RandomOracleGame
import LeanerVMTests.Protocol.ListBinding
import LeanerVMTests.Protocol.MerkleBinding
import LeanerVMTests.Protocol.Proof

/-!
# The random-oracle game: tests

* **Lanes.** A stored level-0 row holds lane `u` of `n` at word `n - 1 - u`; the lanes past the
  row read zero.
* **The extraction at the toy.** The toy's honest stack, committed as the Rust commits a level-0
  word (rows reversed, leaves under BLAKE2s), is read back off the honest prover's log: the word
  read off the log is the honest word, and the commitment's pick on it returns the honest stack.
  With one leaf query missing, that row reads zero, the word is no codeword, and the pick
  returns nothing; with the wrong root, every row reads zero.
* **The extractor at leanVM.** `extract` is a definition with no `noncomputable`. It returns
  nothing on a proof with no announcement, inadmissible sizes, no root, or a root with a nonzero
  top limb, before any decoding.
* **Hits.** A verifier's fresh query answered by a root of the proof is a hit, and is none when
  the root is not the proof's; a prover's query answered by the chain's first state is a hit
  through the digests in play; a verifier's query the prover asked first is not fresh. A
  verifier's query answered by a child of the prover's node query is a fresh hit of the Merkle
  binding and a hit of the game; answered by a new digest, neither.
* **The game and the bad challenges** type-check at leanVM: `loggedGame` with any verifier of
  `verifyWith`'s shape, `bad_density` at every admissible announcement.

A plain file, so `#guard` evaluates the compiled definitions.
-/

namespace LeanerVMTests.Protocol.RandomOracleGame

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Protocol LeanerVM.Protocol.Whir
  LeanerVM.Protocol.Toy LeanerVM.Protocol.Blake2sHash OracleComp OracleSpec
open LeanerVMTests.Protocol.ListBinding (lb0 lb1 lbLadder lb_height toyDecoder toyWord badStack)
open LeanerVMTests.Protocol.MerkleBinding (honestLog w)

/-! ## Lanes -/

#guard laneRow 1 [w 5, w 7] = #v[w 7, w 5]
#guard laneRow 2 [w 5] = #v[w 5, 0, 0, 0]
#guard laneRow 1 [] = #v[0, 0]

/-! ## The extraction at the toy -/

/-- The depth of the toy's level-0 tree: `2 ^ 3` positions. -/
abbrev depth : ℕ := Kap lb1 (0 + 1) + lb0.R

/-- The row the Rust stores at position `y` of a level-0 word: its lanes in reverse. -/
def storedRow (x : KWord lb0.ℓ depth lb0.t) (y : Fin (2 ^ depth)) : List K :=
  (List.ofFn fun u : Fin (2 ^ lb0.ℓ) ↦ (x.row y)[u]).reverse

/-- The stored rows of a word, in position order. -/
def storedRows (x : KWord lb0.ℓ depth lb0.t) : List (List K) := List.ofFn (storedRow x)

/-- The root of the tree over a word's stored rows, two words to a leaf. -/
def rootOf (x : KWord lb0.ℓ depth lb0.t) : Digest :=
  merkleRootWith blake2sBytes (Vector.ofFn (n := 2 ^ depth) fun y ↦ leafImage 2 (storedRow x y))

/-- The honest prover's log of the commitment to the toy's honest word. -/
def honestA : hashSpec.QueryLog := honestLog 2 depth (storedRows (toyWord honest))

/-- The word read off a log under the honest root. -/
def readWord (log : hashSpec.QueryLog) : KWord lb0.ℓ depth lb0.t :=
  logWord log (rootOf (toyWord honest)) depth 2 lb0.ℓ lb0.t

/-- Two words agree at every position. -/
def sameWord (x y : KWord lb0.ℓ depth lb0.t) : Bool :=
  (List.finRange (2 ^ depth)).all fun p ↦ x.row p = y.row p

#guard honestA.length = 2 ^ depth + (2 ^ depth - 1)
#guard sameWord (readWord honestA) (toyWord honest)
#guard (commitPick toy toyDecoder lb_height (1 : K) (readWord honestA)).map Column.values =
  some honest.values

/- One leaf query missing: its row reads zero, and the word is no codeword. -/
#guard (readWord (honestA.eraseIdx 5)).row 5 = Vector.replicate _ 0
#guard ¬ sameWord (readWord (honestA.eraseIdx 5)) (toyWord honest)
#guard (commitPick toy toyDecoder lb_height (1 : K) (readWord (honestA.eraseIdx 5))).isNone

/- Under another root, nothing is read. -/
#guard (List.finRange (2 ^ depth)).all fun p ↦
  (logWord honestA (rootOf (toyWord badStack)) depth 2 lb0.ℓ lb0.t).row p = Vector.replicate _ 0

/-! ## The extractor at leanVM -/

/-- The extractor at the deployed Flock specification: a definition, so it computes. -/
def deployedExtract := extract Blake2sFlock.blake2sFlockSpec

open LeanerVMTests.Protocol.Proof (program input sizes e3)

/-- A proof with the given stream and no openings. -/
def proofOf (stream : List E) : Proof PrunedMerklePaths := ⟨stream, []⟩

/-- The two scalars of a digest. -/
def rootScalars (d : Digest) : List E := [(digestScalars d).1, (digestScalars d).2]

#guard (deployedExtract program input (proofOf []) []).isNone
#guard (deployedExtract program input (proofOf (announcement sizes 1)) []).isNone
#guard (deployedExtract program input
  (proofOf (announcement sizes 1 ++ [(digestScalars (rootOf (toyWord honest))).1, e3 0 0 1]))
  []).isNone
#guard (deployedExtract program input
  (proofOf ((announcement sizes 5) ++ rootScalars (rootOf (toyWord honest)))) []).isNone
#guard level0Root (proofOf (announcement sizes 1 ++ rootScalars (rootOf (toyWord honest)))) =
  some (rootOf (toyWord honest))

/-! ## Hits -/

/-- The digest of a byte. -/
def d (b : UInt8) : Digest := blake2sBytes [b]

/-- A run with the given logs and no proof. -/
def runOf (logA logV : hashSpec.QueryLog) : Run := ⟨proofOf [], logA, logV, true⟩

/- The verifier's fresh query answered by a root of the proof. -/
#guard Hit (fun _ ↦ [d 9]) program input (runOf [⟨[1], d 1⟩] [⟨[2], d 9⟩])
#guard ¬ Hit (fun _ ↦ []) program input (runOf [⟨[1], d 1⟩] [⟨[2], d 9⟩])
/- The prover's query answered by the root counts only through the digests in play. -/
#guard ¬ Hit (fun _ ↦ [d 9]) program input (runOf [⟨[2], d 9⟩] [])
/- A query the prover asked first is not fresh for the verifier. -/
#guard ¬ Hit (fun _ ↦ [d 9]) program input (runOf [⟨[2], d 9⟩] [⟨[2], d 9⟩])
/- An answer equal to the chain's first state is in play from the start. -/
#guard Hit (fun _ ↦ []) program input (runOf [⟨[3], (FsState.seed program input).cv⟩] [])

/-- The prover's node query on the children `d 1`, `d 2`. -/
def nodeA : hashSpec.QueryLog := [⟨nodeBytes (d 1) (d 2), d 3⟩]

/-- The verifier's fresh query answered by the node's left child. -/
def nodeV : hashSpec.QueryLog := [⟨[7], d 1⟩]

/- The node's children are its halves, so in play: the verifier's query is a fresh hit for the
Merkle binding and a hit of the game, which `not_freshHit_of_not_hasHit` relates. -/
#guard MerkleTree.queryChildren nodeOfBytes? nodeA[0]!.1 = halves nodeA[0]!.1
#guard decide (MerkleTree.FreshHit nodeOfBytes? [d 1] nodeA nodeV)
#guard decide (QueryLog.HasHit (inPlay (seedDigests program input)) (nodeA ++ nodeV))
/- Answered by a digest known from nowhere, it is neither. -/
#guard !decide (MerkleTree.FreshHit nodeOfBytes? [d 1] nodeA [⟨[7], d 8⟩])
#guard !decide (QueryLog.HasHit (inPlay (seedDigests program input)) (nodeA ++ [⟨[7], d 8⟩]))

/-! ## The game and the bad challenges -/

example (V : VerifierWith) (A : Adversary) : OracleComp hashSpec Run :=
  loggedGame V program input A

example (F : FlockSpec) (prog : Program) (s : LeanIsa.Sizes) (hs : s.Admissible prog) (ρ : ℕ)
    (hρ : LeanIsa.validRate ρ) (st : (leanIsaInstance F prog s).Stmt × ∀ i, NoOracle i)
    (i : (deployedSpec F prog s hs ρ hρ).ChallengeIdx)
    (tr : (deployedSpec F prog s hs ρ hρ).Transcript i.1.castSucc) :
    Pr{let c ← $ᵗ ((deployedSpec F prog s hs ρ hρ).Challenge i)}[
        c ∈ Bad F prog s hs ρ hρ st i tr] ≤
      listBindingError (leanIsaInstance F prog s) (leanIsaChain prog s hs ρ hρ).ladder
        (leanIsaChain prog s hs ρ hρ).pars i :=
  bad_density F prog s hs ρ hρ st i tr

end LeanerVMTests.Protocol.RandomOracleGame
