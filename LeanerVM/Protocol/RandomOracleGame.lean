/-
  LeanerVM.Protocol.RandomOracleGame

  The game of the random-oracle knowledge-soundness theorem: a cheating prover's run and the
  verifier's on the one hash oracle, each logged; the straight-line extractor that reads the
  committed stack off the prover's log; the events the hash must avoid; and the bad challenges of
  the compiled protocol's state function.
-/

module

public import LeanerVM.Protocol.RandomOracle
public import LeanerVM.Protocol.MerkleBinding
public import LeanerVM.Protocol.Proof
public import LeanerVM.Protocol.ListBindingDeployed
public import LeanerVM.Protocol.Verify.Setup
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core

/-!
# The random-oracle game

Category A: the definitions the random-oracle theorems of the compiled verifier are stated with;
they contribute to T4 in the random-oracle model, the Fiat–Shamir compilation of the list-binding
protocol on the one hash oracle. Two layouts are transcribed from the pinned leanVM
(`a386121f84292f6fa663aaa3e570c15bc0240ea2`): the level-0 root is the stream's scalars `8, 9`,
right after the eight announced sizes (`cpu/mod.rs:558-561`, `pcs::commit`, `read_commitment`);
a level-0 row stores the committed lanes in reverse, lane `u` of `n` at word `n - 1 - u`, after a
zero prefix of the leaf image (`pcs/src/whir.rs:330-345, 1305-1316`).

* **The game** (`loggedGame`). A cheating prover is a computation on the hash oracle alone,
  with no coins (`Adversary`). It runs, logged; then the verifier runs on its proof, logged on
  its own (`Run`). The verifier is a parameter of the shape of the executable verifier,
  `verifyWith`, generic in how the hash is answered (`VerifierWith`).
* **The extractor** (`extract`). From the proof: the announced sizes and rate when they pass the
  setup checks, and the level-0 root. From the prover's log: every level-0 row under that root
  (`extractAllRows`), a row no query formed read as zero, as the level-0 word (`logWord`). Then
  the commitment's pick at leanVM (`deployedPick`): the transform's exact path, then brute force,
  and the first member of the list whose stack satisfies `M3Holds`. It is computable.
  `Extracts` says the extraction succeeds with a stack satisfying `M3Holds`, which every stack
  the pick returns does (`extracts_iff_isSome`).
* **The events** (`Hit`, `HashMisbehaves`). A collision on the joint log; a hit, a query
  answered, at its input's first occurrence, by a digest already in play (`inPlay` from the
  chain's first state) or, for the verifier's queries, by one of the proof's roots; or a flip.
  `HitFrom` and `HashMisbehavesFrom` are the same events from any list of roots in play at the
  start.
  The proof's roots and the flip are parameters: both read the verifier's chain walk on the
  proof, which is the transcript decoder's. A log with no hit has no fresh hit on a root in play
  (`not_freshHit_of_not_hasHit`), the condition of the Merkle binding by log replay.
* **The bad challenges** (`Bad`, `bad_density`). At a prefix of the compiled transcript ending
  at a challenge, the challenges that turn the state function of `listBinding_deployed` from
  false to true, the extractor's witness given: the event of `rbrKnowledgeSoundnessWorstCaseWith`.
  Its density is at most the round's error (`listBindingError`), by the security's `rbr`.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics Blake2sHash Whir LeanIsa OracleComp OracleSpec
open scoped NNReal ENNReal

@[expose] public section

/-! ## The game -/

/-- A cheating prover: a computation on the hash oracle, with no coins, that outputs a proof. -/
abbrev Adversary : Type := OracleComp hashSpec (Proof PrunedMerklePaths)

/-- The shape of the executable verifier: the program, the public input and a proof, with every
hash answered by `H` in a monad `m`. -/
abbrev VerifierWith : Type 1 := ∀ {m : Type → Type} [Monad m],
  (List UInt8 → m Digest) → Program → PublicInput → Proof PrunedMerklePaths → m Bool

/-- A run of the game: the proof, the prover's log, the verifier's log and its verdict. -/
structure Run where
  /-- The prover's proof. -/
  proof : Proof PrunedMerklePaths
  /-- The prover's queries, in order. -/
  logA : hashSpec.QueryLog
  /-- The verifier's queries, in order. -/
  logV : hashSpec.QueryLog
  /-- The verdict. -/
  ok : Bool

/-- The joint log: the prover's queries, then the verifier's. -/
def Run.log (g : Run) : hashSpec.QueryLog := g.logA ++ g.logV

/-- **The logged game**: the prover runs with its queries logged, then the verifier `V` runs on
its proof with its own queries logged. -/
def loggedGame (V : VerifierWith) (prog : Program) (input : PublicInput) (A : Adversary) :
    OracleComp hashSpec Run := do
  let (proof, logA) ← A.withQueryLog
  let (ok, logV) ← (V hashQuery prog input proof).withQueryLog
  return ⟨proof, logA, logV, ok⟩

/-! ## The extractor -/

/-- The level-0 root of a proof: its stream's scalars `8` and `9`, after the announced sizes, read
as a digest; `none` if missing or not canonical (`read_commitment`). -/
def level0Root (proof : Proof PrunedMerklePaths) : Option Digest :=
  match proof.stream.drop 8 with
  | x₁ :: x₂ :: _ => digestOfScalars (x₁, x₂)
  | _ => none

/-- The lanes of a stored level-0 row: lane `u` of `n` is word `n - 1 - u`, zero past the row. -/
def laneRow (ℓ : ℕ) (row : List K) : Vector K (2 ^ ℓ) := Vector.ofFn fun u ↦ row.reverse.getD u 0

/-- The level-0 rows under `root` read off a log, `rowWords` words in leaves of `2 ^ ℓ`, a missing
row read as zero, as lanes. -/
def wordRows (log : hashSpec.QueryLog) (root : Digest) (depth rowWords ℓ : ℕ) :
    Vector (Vector K (2 ^ ℓ)) (2 ^ depth) :=
  let rows := (extractAllRows log root depth rowWords (2 ^ ℓ)).toArray
  Vector.ofFn fun y ↦ laneRow ℓ ((rows[y.val]?).bind id |>.getD [])

/-- The level-0 word read off a log. -/
def logWord (log : hashSpec.QueryLog) (root : Digest) (depth rowWords ℓ t : ℕ) : KWord ℓ depth t :=
  ⟨fun y ↦ (wordRows log root depth rowWords ℓ)[y]⟩

/-- The lanes the level-0 rows carry at the sizes `s`, lanes of `2 ^ κ` cells: the committed
columns' cells rounded up to whole lanes, at least one (`StackShape::n_lanes`,
`witness.rs:97-101`). At `κ = deployedHeadKap μ ρ`, which is `μ - initialFold` on the window
(`deployedHeadKap_eq`), it must equal the executable verifier's row width (`Verify.nLanes`). -/
def level0Lanes (prog : Program) (s : Sizes) (κ : ℕ) : ℕ :=
  max 1 (((LeanIsa.blocks prog s).total + 2 ^ κ - 1) / 2 ^ κ)

/-- The executable verifier's row width is the lanes at `μ - initialFold`. -/
theorem nLanes_eq_level0Lanes (prog : Program) (s : Sizes) :
    Verify.nLanes prog s = level0Lanes prog s (leanIsaμ prog s - Parameters.Whir.initialFold) :=
  rfl

/-- Level 0 of every admissible chain leaves `μ - initialFold` variables: one decision on the
window. -/
theorem deployedHeadKap_eq {μ ρ : ℕ} (h : Parameters.Whir.Admissible μ ρ) :
    deployedHeadKap μ ρ = μ - Parameters.Whir.initialFold := by
  have key : ∀ μ < Parameters.Whir.maxLogStack + 1, ∀ r < Parameters.Whir.maxLogInvRate + 1,
      Parameters.Whir.Admissible μ r → deployedHeadKap μ r = μ - Parameters.Whir.initialFold := by
    decide +kernel
  exact key μ (Nat.lt_succ_of_le h.2.1) ρ (Nat.lt_succ_of_le h.2.2.2) h

/-- **The straight-line extractor**: the announced sizes when they pass the setup checks, the
level-0 word read off `log` under the proof's level-0 root, and the stack the commitment's pick
returns, if any. -/
def extract (F : FlockSpec) (prog : Program) (input : PublicInput)
    (proof : Proof PrunedMerklePaths) (log : hashSpec.QueryLog) :
    Option (Σ s : Sizes, Column (leanIsaμ prog s)) :=
  match proof.announced? with
  | none => none
  | some (s, ρ) =>
    if hs : s.Admissible prog ∧ validRate ρ then
      match level0Root proof with
      | none => none
      | some root =>
        let v := wordRows log root
          (deployedHeadKap (leanIsaμ prog s) ρ + (deployedHeadShape (leanIsaμ prog s) ρ).R)
          (level0Lanes prog s (deployedHeadKap (leanIsaμ prog s) ρ))
          (deployedHeadShape (leanIsaμ prog s) ρ).ℓ
        (deployedPick (leanIsaInstance F prog s) (admissible_of_sizes hs.1 hs.2) input
          ⟨fun y ↦ v[y]⟩).map fun q ↦ ⟨s, q⟩
    else none

/-- The extraction succeeds: a stack satisfying `M3Holds` at the announced sizes. -/
def Extracts (F : FlockSpec) (prog : Program) (input : PublicInput)
    (proof : Proof PrunedMerklePaths) (log : hashSpec.QueryLog) : Prop :=
  ∃ s q, extract F prog input proof log = some ⟨s, q⟩ ∧ M3Holds (leanIsaInstance F prog s) input q

/-- Every stack the extractor returns satisfies `M3Holds`. -/
theorem extracts_iff_isSome (F : FlockSpec) (prog : Program) (input : PublicInput)
    (proof : Proof PrunedMerklePaths) (log : hashSpec.QueryLog) :
    Extracts F prog input proof log ↔ (extract F prog input proof log).isSome := by
  refine ⟨fun ⟨s, q, h, _⟩ ↦ by rw [h]; rfl, fun h ↦ ?_⟩
  obtain ⟨⟨s, q⟩, hq⟩ := Option.isSome_iff_exists.mp h
  refine ⟨s, q, hq, ?_⟩
  unfold extract at hq
  split at hq
  · cases hq
  · split at hq
    · split at hq
      · cases hq
      · obtain ⟨q', hq', heq⟩ := Option.map_eq_some_iff.mp hq
        cases heq
        exact commitPick_eq_some hq'
    · cases hq

/-! ## What the hash must avoid -/

/-- The digests in play before any query: the chain's first state. -/
def seedDigests (prog : Program) (input : PublicInput) : List Digest :=
  [(FsState.seed prog input).cv]

/-- The roots a proof carries for the verifier: at most six, a root per level of the deployed
ladders (`ProofRoots.length_rootsOf_le`). -/
def proofDigests : ℕ := 6

/-- **A hit** from the roots `seedRoots`: a query answered, at its input's first occurrence in the
joint log, by a digest in play before it (`inPlay seedRoots`), or, for a verifier's query, by one
of the proof's roots (`rootsOf`). -/
def HitFrom (seedRoots : List Digest) (rootsOf : Proof PrunedMerklePaths → List Digest)
    (g : Run) : Prop :=
  QueryLog.HasHit (inPlay seedRoots) g.log ∨
    ∃ k : Fin g.log.length, g.logA.length ≤ k ∧ QueryLog.Fresh (g.log.take k) g.log[k].1 ∧
      g.log[k].2 ∈ rootsOf g.proof

/-- **A hit** on the statement `(prog, input)`: one from its chain's first state. -/
def Hit (rootsOf : Proof PrunedMerklePaths → List Digest) (prog : Program) (input : PublicInput)
    (g : Run) : Prop :=
  HitFrom (seedDigests prog input) rootsOf g

/-- **The hash misbehaves** on a run, from the roots `seedRoots`: a collision on the joint log, a
hit, or a flip (`Flip`, the proof's own chain choosing a bad challenge). -/
def HashMisbehavesFrom (seedRoots : List Digest) (rootsOf : Proof PrunedMerklePaths → List Digest)
    (Flip : Run → Prop) (g : Run) : Prop :=
  QueryLog.HasCollision g.log ∨ HitFrom seedRoots rootsOf g ∨ Flip g

/-- **The hash misbehaves** on a run of the statement `(prog, input)`: from its chain's first
state. `Flip` and `rootsOf` are parameters, so that the random-oracle bound holds for any reader of
chain histories; `Core.core` and the headline theorems instantiate them at leanVM's, the flip
clause of the deployed reader (`(leanVmReader prog input).Flip`) and the proof's roots
(`ProofRoots.rootsOf prog input`). With `Flip := fun _ ↦ True` the event is trivial, so only that
instance is evidence about the hash. -/
def HashMisbehaves (rootsOf : Proof PrunedMerklePaths → List Digest) (Flip : Run → Prop)
    (prog : Program) (input : PublicInput) (g : Run) : Prop :=
  HashMisbehavesFrom (seedDigests prog input) rootsOf Flip g

instance (seedRoots : List Digest) (rootsOf : Proof PrunedMerklePaths → List Digest) (g : Run) :
    Decidable (HitFrom seedRoots rootsOf g) := by
  letI := Digest.decEq
  unfold HitFrom
  infer_instance

instance (rootsOf : Proof PrunedMerklePaths → List Digest) (prog : Program) (input : PublicInput)
    (g : Run) : Decidable (Hit rootsOf prog input g) := by
  unfold Hit
  infer_instance

/-- The children of a logged query read as a node are in play once it is asked: they are its
halves. -/
theorem queryChildren_mem_inPlay (roots : List Digest) (l : hashSpec.QueryLog)
    (e : (_ : List UInt8) × Digest) :
    ∀ d ∈ MerkleTree.queryChildren nodeOfBytes? e.1, d ∈ inPlay roots (l ++ [e]) := by
  intro d hd
  unfold MerkleTree.queryChildren at hd
  split at hd
  · rename_i lc rc hnode
    obtain ⟨rfl, rfl⟩ := nodeOfBytes?_eq_some hnode
    have hlen : e.1.length = 64 := by
      unfold nodeOfBytes? at hnode
      split at hnode
      · assumption
      · cases hnode
    exact halves_mem_inPlay roots l e d (by simpa [halves, hlen] using hd)
  · cases hd

/-- **No hit, no fresh hit.** In a consistent joint log with no hit on the digests in play, no
query of `logV` fresh with respect to `logA` is answered by a digest known from `logA` and a root
in play after `logA`: the Merkle binding's condition on the log follows from the random-oracle
game's. -/
theorem not_freshHit_of_not_hasHit {roots : List Digest} {logA logV : hashSpec.QueryLog}
    (hcons : QueryLog.Consistent (logA ++ logV))
    (hhit : ¬ QueryLog.HasHit (inPlay roots) (logA ++ logV)) {root : Digest}
    (hroot : root ∈ inPlay roots logA) : ¬ MerkleTree.FreshHit nodeOfBytes? [root] logA logV :=
  MerkleTree.not_freshHit_of_not_hasHit (inPlay_mono roots) (queryChildren_mem_inPlay roots)
    hcons hhit (by simpa using hroot)

/-! ## The bad challenges -/

/-- The shared oracle of the compiled protocol: none, on the unit state. -/
def noSharedOracle : QueryImpl []ₒ (StateT Unit ProbComp) := fun q ↦ PEmpty.elim q

section Bad

variable (F : FlockSpec) (prog : Program) (s : Sizes) (hs : s.Admissible prog) (ρ : ℕ)
  (hρ : validRate ρ)

/-- The schedule of the compiled protocol at leanVM. -/
abbrev deployedSpec :=
  listBindingSpec (leanIsaInstance F prog s) (leanIsaChain prog s hs ρ hρ).sh
    (leanIsaChain prog s hs ρ hρ).κ (leanIsaChain prog s hs ρ hρ).ladder

/-- **The bad challenges** at a prefix `tr` of the compiled transcript ending before the
challenge `i`: those that turn the state function of `listBinding_deployed` from false to true,
the extractor's witness given, on the statement `st`. -/
def Bad (st : (leanIsaInstance F prog s).Stmt × ∀ i, NoOracle i)
    (i : (deployedSpec F prog s hs ρ hρ).ChallengeIdx)
    (tr : (deployedSpec F prog s hs ρ hρ).Transcript i.1.castSucc) :
    Set ((deployedSpec F prog s hs ρ hρ).Challenge i) :=
  {c | ∃ w, ¬ (listBinding_deployed F prog s hs ρ hρ).kSF (pure ()) noSharedOracle i.1.castSucc st
      tr ((listBinding_deployed F prog s hs ρ hρ).extractor.extractMid i.1 st (tr.concat c) w) ∧
    (listBinding_deployed F prog s hs ρ hρ).kSF (pure ()) noSharedOracle i.1.succ st
      (tr.concat c) w}

/-- **The density of the bad challenges** is at most the round's error. -/
theorem bad_density (st : (leanIsaInstance F prog s).Stmt × ∀ i, NoOracle i)
    (i : (deployedSpec F prog s hs ρ hρ).ChallengeIdx)
    (tr : (deployedSpec F prog s hs ρ hρ).Transcript i.1.castSucc) :
    Pr{let c ← $ᵗ ((deployedSpec F prog s hs ρ hρ).Challenge i)}[
        c ∈ Bad F prog s hs ρ hρ st i tr] ≤
      listBindingError (leanIsaInstance F prog s) (leanIsaChain prog s hs ρ hρ).ladder
        (leanIsaChain prog s hs ρ hρ).pars i := by
  have h := (listBinding_deployed F prog s hs ρ hρ).rbr (pure ()) noSharedOracle st i tr
  unfold Bad
  simp only [Set.mem_ofPred_eq]
  convert h using 5

end Bad

end
end LeanerVM.Protocol
