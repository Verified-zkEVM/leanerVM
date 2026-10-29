/-
  LeanerVM.Protocol.Verify.Hom

  The executable verifier transported along a monad morphism of the hash's monads: mapping a run
  of the verifier is running it with the hash's answers mapped. The random-oracle run is the
  verifier with the oracle answering.
-/

module

public import LeanerVM.Protocol.Verify
public import VCVio.OracleComp.SimSemantics.SimulateQ

/-!
# The verifier along a monad morphism

`verifyWith H` is written once over the hash `H : List UInt8 → m Digest`. `verifyWith_hom`: for
a monad morphism `φ : m →ᵐ m'`, `φ (verifyWith H prog input proof)` is
`verifyWith (fun t ↦ φ (H t)) prog input proof`. `verifyWith_simulateQ` is the instance at
VCVio's `simulateQ impl`: the verifier with every hash a query to the oracle
`List UInt8 →ₒ Digest`, simulated by `impl`, is the verifier with `impl` answering, so the
random-oracle run, the BLAKE2s run and a logged run are one function at three hashes;
`verifyWith_pure` makes the BLAKE2s run, answering by `pure (blake2sBytes t)`, `pure` of
`verify`.

Lean has no parametricity theorem, so the transport is proved through the definitions: the
chain's steps, the reader's operations along the lifted morphism `ReadM.mapHom φ`, the Merkle
check (through `MerkleTree.prunedRoot_hom`), every walk along any morphism of its primitives
(`ChainOps.map`, `walkProof_hom`), and the proof reader's primitives mapped (`readerOps_hom`).
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics Blake2sHash LeanIsa

@[expose] public section

/-! ## The chain and the reader -/

section Reader

variable {m m' : Type → Type} [Monad m] [Monad m'] [LawfulMonad m] [LawfulMonad m']
  (φ : m →ᵐ m') (H : List UInt8 → m Digest)

namespace FsState

private theorem observe_hom (s : FsState) (x : E) :
    φ (s.observe H x) = s.observe (fun t ↦ φ (H t)) x := by
  simp [observe]

private theorem sample_hom (s : FsState) : φ (s.sample H) = s.sample (fun t ↦ φ (H t)) := by
  simp [sample]

private theorem checkPow_hom (s : FsState) (bits : ℕ) (nonce : E) :
    φ (s.checkPow H bits nonce) = s.checkPow (fun t ↦ φ (H t)) bits nonce := by
  simp [checkPow, powBase, powOk, absorbNonce]

end FsState

/-- A monad morphism of the hash's monads, lifted to the reader's: the state threaded and a
rejection kept. -/
abbrev ReadM.mapHom {M : Type} : ReadM m M →ᵐ ReadM m' M := StateT.mapHom (ExceptT.mapHom φ)

variable {M : Type}

/-- A reader's run, mapped, is the mapped reader's run. -/
theorem ReadM.run'_mapHom {α : Type} (x : ReadM m M α) (st : ReaderState M) :
    φ ((x.run' st).run) = ((ReadM.mapHom φ x).run' st).run := by
  simp [StateT.run', ReadM.mapHom]
  rfl

private theorem ReadM.mapHom_throw {α : Type} (e : ReadError) :
    ReadM.mapHom φ (throw e : ReadM m M α) = throw e := by
  apply StateT.ext; intro st; apply ExceptT.ext
  simp [ReadM.mapHom]

namespace Reader

private theorem takeRaw_hom : ReadM.mapHom φ (takeRaw : ReadM m M E) = takeRaw := by
  apply StateT.ext; intro st; apply ExceptT.ext
  rcases st with ⟨fs, _ | ⟨x, rest⟩, ms⟩ <;> simp [takeRaw]

private theorem observe_hom (x : E) :
    ReadM.mapHom φ (observe H x : ReadM m M Unit) = observe (fun t ↦ φ (H t)) x := by
  apply StateT.ext; intro st; apply ExceptT.ext
  simp [observe, FsState.observe_hom]

private theorem nextScalar_hom :
    ReadM.mapHom φ (nextScalar H : ReadM m M E) = nextScalar (fun t ↦ φ (H t)) := by
  simp only [nextScalar, MonadHom.mmap_bind, MonadHom.mmap_pure, takeRaw_hom, observe_hom]

private theorem nextRoot_hom :
    ReadM.mapHom φ (nextRoot H : ReadM m M Digest) = nextRoot (fun t ↦ φ (H t)) := by
  simp only [nextRoot, MonadHom.mmap_bind, nextScalar_hom]
  congr 1; funext a; congr 1; funext b
  split <;> simp [ReadM.mapHom_throw]

private theorem sample_hom :
    ReadM.mapHom φ (sample H : ReadM m M E) = sample (fun t ↦ φ (H t)) := by
  apply StateT.ext; intro st; apply ExceptT.ext
  simp [sample, FsState.sample_hom]

private theorem checkPow_hom (bits : ℕ) :
    ReadM.mapHom φ (checkPow H bits : ReadM m M E) = checkPow (fun t ↦ φ (H t)) bits := by
  apply StateT.ext; intro st; apply ExceptT.ext
  rcases st with ⟨fs, _ | ⟨x, rest⟩, ms⟩
  · simp [checkPow, takeRaw]
  · simp [checkPow, takeRaw, FsState.checkPow_hom, ReadM.mapHom_throw]

private theorem nextOpening_hom {α : Type} (auth : M → m (Option α)) :
    ReadM.mapHom φ (nextOpening auth) = nextOpening (fun o ↦ φ (auth o)) := by
  apply StateT.ext; intro st; apply ExceptT.ext
  rcases st with ⟨fs, s, _ | ⟨o, rest⟩⟩
  · simp [nextOpening]
  · simp only [nextOpening, StateT.run_mapHom, ExceptT.run_mapHom, StateT.run_bind,
      ExceptT.run_bind]
    simp
    congr 1; funext x
    cases x <;> simp

private theorem finish_hom : ReadM.mapHom φ (finish : ReadM m M Unit) = finish := by
  apply StateT.ext; intro st; apply ExceptT.ext
  simp [finish, ReadM.mapHom_throw]

end Reader

/-! ## The Merkle check -/

private theorem hashRowsWith_hom (rowWords leafWords : ℕ) (rows : List (List K)) :
    φ (hashRowsWith H rowWords leafWords rows) =
      hashRowsWith (fun t ↦ φ (H t)) rowWords leafWords rows := by
  induction rows with
  | nil => simp [hashRowsWith]
  | cons row rest ih => by_cases h : row.length = rowWords <;> simp [hashRowsWith, h, ih]

private theorem merkleVerifyWith_hom (root : Digest) (depth rowWords leafWords : ℕ)
    (queries : List ℕ) (paths : PrunedMerklePaths) :
    φ (merkleVerifyWith H root depth rowWords leafWords queries paths) =
      merkleVerifyWith (fun t ↦ φ (H t)) root depth rowWords leafWords queries paths := by
  unfold merkleVerifyWith
  dsimp only
  split
  · simp
  · simp only [MonadHom.mmap_bind, hashRowsWith_hom]
    congr 1; funext ls
    cases ls with
    | none => simp
    | some leaves =>
      simp only
      split
      · simp
      · simp only [MonadHom.mmap_bind, MerkleTree.prunedRoot_hom]
        congr 1; funext r
        cases r <;> simp

end Reader

/-! ## The walks along a morphism of their primitives -/

namespace Verify

/-- The primitives carried along a monad morphism. -/
def ChainOps.map {n n' : Type → Type} [Monad n] [Monad n'] (ψ : n →ᵐ n') (ops : ChainOps n) :
    ChainOps n' where
  nextScalar := ψ ops.nextScalar
  sample := ψ ops.sample
  nextRoot := ψ ops.nextRoot
  checkPow bits := ψ (ops.checkPow bits)
  nextOpening root depth rowWords leafWords ps :=
    ψ (ops.nextOpening root depth rowWords leafWords ps)

section Walks

variable {n n' : Type → Type} [Monad n] [Monad n'] [LawfulMonad n] [LawfulMonad n']
  (ψ : n →ᵐ n') (ops : ChainOps n)

private theorem nextScalars_hom (k : ℕ) : ψ (ops.nextScalars k) = (ops.map ψ).nextScalars k := by
  induction k with
  | zero => simp [ChainOps.nextScalars]
  | succ k ih => simp [ChainOps.nextScalars, ih, ChainOps.map]

private theorem samples_hom (k : ℕ) : ψ (samples ops k) = samples (ops.map ψ) k := by
  induction k with
  | zero => simp [samples]
  | succ k ih => simp [samples, ih, ChainOps.map]

private theorem readRounds_hom (d k : ℕ) : ψ (readRounds ops d k) = readRounds (ops.map ψ) d k := by
  induction k with
  | zero => simp [readRounds]
  | succ k ih => simp [readRounds, readRound, ih, nextScalars_hom, ChainOps.map]

private theorem walkLayers_hom (ρs : List ℕ) (j : ℕ) :
    ψ (walkLayers ops ρs j) = walkLayers (ops.map ψ) ρs j := by
  induction ρs generalizing j with
  | nil => simp [walkLayers]
  | cons ρ rest ih =>
    simp [walkLayers, walkLayer, ih, readRounds_hom, nextScalars_hom, samples_hom, ChainOps.map]

private theorem walkFolds_hom (k : ℕ) : ψ (walkFolds ops k) = walkFolds (ops.map ψ) k := by
  induction k with
  | zero => simp [walkFolds]
  | succ k ih => simp [walkFolds, ih, nextScalars_hom, ChainOps.map]

private theorem walkTail_hom (k : ℕ) : ψ (walkTail ops k) = walkTail (ops.map ψ) k := by
  induction k with
  | zero => simp [walkTail]
  | succ k ih => by_cases hk : k = 0 <;> simp [walkTail, ih, hk, nextScalars_hom, ChainOps.map]

private theorem walkPositions_hom (depth fuel need : ℕ) :
    ψ (walkPositions ops depth fuel need) = walkPositions (ops.map ψ) depth fuel need := by
  induction fuel generalizing need with
  | zero => simp [walkPositions]
  | succ fuel ih =>
    cases need with
    | zero => simp [walkPositions]
    | succ need => simp [walkPositions, ih, ChainOps.map]

private theorem walkLevels_hom (shs : List LevelShape) :
    ψ (walkLevels ops shs) = walkLevels (ops.map ψ) shs := by
  induction shs with
  | nil => simp [walkLevels]
  | cons sh shs ih =>
    cases h : sh.final <;>
      simp [walkLevels, walkLevel, h, ih, walkFolds_hom, nextScalars_hom, samples_hom,
        walkPositions_hom, walkTail_hom, ChainOps.map]

private theorem walkOpenings_hom (nLanes : ℕ) (first : Bool) (root : Digest) (shs : List LevelShape)
    (ls : List WhirLevel) :
    ψ (walkOpenings ops nLanes first root shs ls) =
      walkOpenings (ops.map ψ) nLanes first root shs ls := by
  induction shs generalizing first root ls with
  | nil => simp [walkOpenings]
  | cons sh shs ih =>
    cases ls with
    | nil => simp [walkOpenings]
    | cons l ls => simp [walkOpenings, ih, ChainOps.map]

/-- The verifier's reads, mapped along a morphism of their monads, are the reads on the mapped
primitives. -/
theorem walkProof_hom (prog : Program) (s : Sizes) (input : PublicInput)
    (shs : List LevelShape) :
    ψ (walkProof ops prog s input shs) = walkProof (ops.map ψ) prog s input shs := by
  simp [walkProof, walkChain, walkSetup, walkBus, walkTables, walkPub, walkFlock, walkWhir,
    nextScalars_hom, samples_hom, readRounds_hom, walkLayers_hom, walkLevels_hom,
    walkOpenings_hom, ChainOps.map]

end Walks

/-! ## The verifier -/

variable {m m' : Type → Type} [Monad m] [Monad m'] [LawfulMonad m] [LawfulMonad m']
  (φ : m →ᵐ m') (H : List UInt8 → m Digest)

/-- The proof reader's primitives, mapped, are the proof reader's at the mapped hash. -/
theorem readerOps_hom :
    (readerOps H).map (ReadM.mapHom φ) = readerOps (fun t ↦ φ (H t)) := by
  simp only [ChainOps.map, readerOps, Reader.nextScalar_hom, Reader.sample_hom,
    Reader.nextRoot_hom, Reader.checkPow_hom, Reader.nextOpening_hom, merkleVerifyWith_hom]

/-- **The verifier along a monad morphism**: a run of `verifyWith H`, mapped by `φ`, is the run
of `verifyWith` with every hash's answer mapped. -/
theorem verifyWith_hom (prog : Program) (input : PublicInput) (proof : Proof PrunedMerklePaths) :
    φ (verifyWith H prog input proof) = verifyWith (fun t ↦ φ (H t)) prog input proof := by
  unfold verifyWith
  split
  · simp
  · split
    · simp
    · dsimp only
      split
      · simp
      · simp only [MonadHom.mmap_bind, ReadM.run'_mapHom, walkProof_hom, readerOps_hom,
          Reader.finish_hom, MonadHom.mmap_pure]
        congr 1; funext r
        cases r <;> simp

/-- **The deterministic run**: the verifier with every hash answered by `pure (H t)` in a lawful
monad is `pure` of the verifier in `Id`; at `H := blake2sBytes`, of `verify`. -/
theorem verifyWith_pure {m : Type → Type} [Monad m] [LawfulMonad m] (H : List UInt8 → Digest)
    (prog : Program) (input : PublicInput) (proof : Proof PrunedMerklePaths) :
    verifyWith (fun t ↦ (pure (H t) : m Digest)) prog input proof =
      pure (verifyWith (m := Id) H prog input proof) := by
  have h := verifyWith_hom (MonadHom.pure m) (m := Id) H prog input proof
  simp only [MonadHom.pure_apply] at h
  exact h.symm

/-- **The random-oracle run is the verifier at the oracle**: the verifier with every hash a query
to the oracle `List UInt8 →ₒ Digest`, simulated by `impl`, is the verifier with `impl`
answering. -/
theorem verifyWith_simulateQ {r : Type → Type} [Monad r] [LawfulMonad r]
    (impl : QueryImpl (List UInt8 →ₒ Digest) r) (prog : Program) (input : PublicInput)
    (proof : Proof PrunedMerklePaths) :
    simulateQ impl
        (verifyWith (fun t ↦ liftM ((List UInt8 →ₒ Digest).query t)) prog input proof) =
      verifyWith impl prog input proof := by
  have h := verifyWith_hom (simulateQ' impl)
    (fun t ↦ liftM ((List UInt8 →ₒ Digest).query t)) prog input proof
  simp only [simulateQ_spec_query] at h
  exact h

end Verify

end
end LeanerVM.Protocol
