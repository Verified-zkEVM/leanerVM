/-
  LeanerVM.Protocol.Prove.Hom

  The honest prover transported along a monad morphism of the hash's monads: mapping a run of
  the prover is running it with the hash's answers mapped. The random-oracle run is the prover
  with the oracle answering.
-/

module

public import LeanerVM.Protocol.Prove
public import LeanerVM.Protocol.Verify.Hom
public import LeanerVM.Protocol.ToArkLib.RunCodecHom
public import PolyFun.Control.Monad.Hom.Loops

/-!
# The prover along a monad morphism

`proveFrom H seed` is written once over the hash `H : List UInt8 → m Digest` and the start
`seed : m FsState`. For a monad morphism `φ : m →ᵐ m'`, mapping `proveFrom H seed` by `φ` is
`proveFrom (fun t ↦ φ (H t)) (φ seed)`, and `proveWith_hom` is the instance at the statement's
seed. `proveWith_simulateQ` is the instance at VCVio's `simulateQ impl`: the prover with every
hash a query to the oracle `List UInt8 →ₒ Digest`, simulated by `impl`, is the prover with `impl`
answering.

The proof follows the definitions: the writer's primitives along the lifted morphism, the Merkle
commitment (`MerkleTree.buildLevelsM_hom`), the wire of the compiled schedule mapped along any
morphism of its primitives (through `RoundCodec.map`), and the run of the compiled prover against
a mapped wire (`Prover.runWith_hom`).
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization Blake2sHash LeanIsa Whir
open OracleComp OracleSpec ProtocolSpec StepSchedule
open Air.Flat (EnsembleWitness)

@[expose] public section

/-! ## The chain and the Merkle commitment -/

section Chain

variable {m m' : Type → Type} [Monad m] [Monad m'] [LawfulMonad m] [LawfulMonad m']
  (φ : m →ᵐ m') (H : List UInt8 → m Digest)

namespace FsState

omit [LawfulMonad m] [LawfulMonad m'] in
private theorem findNonce_hom (base : Digest) (bits fuel n : ℕ) :
    φ (findNonce H base bits fuel n) = findNonce (fun t ↦ φ (H t)) base bits fuel n := by
  induction fuel generalizing n with
  | zero => simp [findNonce]
  | succ fuel ih =>
    simp only [findNonce, powOk, MonadHom.mmap_bind, MonadHom.mmap_pure]
    congr 1; funext d
    split <;> simp [ih]

private theorem grind_hom (s : FsState) (fuel bits : ℕ) :
    φ (s.grind H fuel bits) = s.grind (fun t ↦ φ (H t)) fuel bits := by
  simp only [grind, powBase, absorbNonce, MonadHom.mmap_bind]
  congr 1; funext base
  split
  · simp
  · simp only [findNonce_hom, MonadHom.mmap_bind]
    congr 1; funext n?
    cases n? <;> simp

end FsState

private theorem merkleCommitWithM_hom (leafWords : ℕ) {k : ℕ} (rows : Vector (List K) (2 ^ k)) :
    φ (merkleCommitWithM H leafWords rows) =
      merkleCommitWithM (fun t ↦ φ (H t)) leafWords rows := by
  simp only [merkleCommitWithM, MonadHom.mmap_bind, MonadHom.mmap_pure, Vector.mapM_hom,
    MerkleTree.buildLevelsM_hom]

end Chain

/-! ## The writer along the lifted morphism -/

namespace Prove

section Writer

variable {m m' : Type → Type} [Monad m] [Monad m'] [LawfulMonad m] [LawfulMonad m']
  (φ : m →ᵐ m') (H : List UInt8 → m Digest) {M : Type}

/-- A monad morphism of the hash's monads, lifted to the writer's: the state threaded and a
failure kept. -/
private abbrev WriteM.mapHom : WriteM m M →ᵐ WriteM m' M := StateT.mapHom (OptionT.mapHom φ)

/-- A monad morphism of the hash's monads, lifted to the prover's. -/
private abbrev liftHom : ProveM m →ᵐ ProveM m' := StateT.mapHom (WriteM.mapHom φ)

private theorem addScalar_hom (x : E) :
    WriteM.mapHom φ (Writer.addScalar (M := M) H x) = Writer.addScalar (fun t ↦ φ (H t)) x := by
  apply StateT.ext; intro st; apply OptionT.ext
  simp [Writer.addScalar, FsState.observe]

private theorem addScalars_hom (xs : List E) :
    WriteM.mapHom φ (Writer.addScalars (M := M) H xs) = Writer.addScalars (fun t ↦ φ (H t)) xs := by
  induction xs with
  | nil => simp [Writer.addScalars]
  | cons x xs ih => simp only [Writer.addScalars, MonadHom.mmap_bind, addScalar_hom, ih]

private theorem sample_hom :
    WriteM.mapHom φ (Writer.sample (M := M) H) = Writer.sample (fun t ↦ φ (H t)) := by
  apply StateT.ext; intro st; apply OptionT.ext
  simp [Writer.sample, FsState.sample]

private theorem grind_hom (fuel bits : ℕ) :
    WriteM.mapHom φ (Writer.grind (M := M) H fuel bits) =
      Writer.grind (fun t ↦ φ (H t)) fuel bits := by
  apply StateT.ext; intro st; apply OptionT.ext
  simp only [Writer.grind, MonadHom.toFun_bind', StateT.run_bind, StateT.run_mapHom,
    StateT.run_get, MonadHom.toFun_pure', StateT.run_monadLift, bind_pure_comp, MonadHom.mmap_map,
    bind_map_left, pure_bind, OptionT.run_bind, OptionT.run_mapHom, OptionT.run_monadLift,
    monadLift_self, Option.elimM_map, Option.elim_some, ← FsState.grind_hom]
  congr 1; funext r
  rcases r with _ | ⟨n, fs⟩ <;> simp

private theorem addRoot_hom (d : Digest) :
    WriteM.mapHom φ (Writer.addRoot (M := M) H d) = Writer.addRoot (fun t ↦ φ (H t)) d :=
  addScalars_hom φ H _

private theorem announce_hom (s : Sizes) (ρ : ℕ) :
    WriteM.mapHom φ (Writer.announce (M := M) H s ρ) = Writer.announce (fun t ↦ φ (H t)) s ρ :=
  addScalars_hom φ H _

omit [LawfulMonad m] [LawfulMonad m'] in
private theorem hintOpening_hom (o : M) :
    WriteM.mapHom φ (Writer.hintOpening (m := m) o) = Writer.hintOpening o := by
  apply StateT.ext; intro st; apply OptionT.ext
  simp [Writer.hintOpening]

omit [LawfulMonad m] [LawfulMonad m'] in
/-- A writer's run, mapped, is the mapped writer's run. -/
private theorem runWrite_hom {α : Type} (x : WriteM m M α) (fs : FsState) :
    φ (runWrite x fs) = runWrite (WriteM.mapHom φ x) fs := by
  simp [runWrite]

end Writer

/-! ## The prover's primitives -/

section Prover

variable {m m' : Type → Type} [Monad m] [Monad m'] [LawfulMonad m] [LawfulMonad m']
  (φ : m →ᵐ m') (H : List UInt8 → m Digest)

private theorem liftHom_lift {α : Type} (x : WriteM m PrunedMerklePaths α) :
    liftHom φ (StateT.lift x : ProveM m α) = StateT.lift (WriteM.mapHom φ x) := by
  apply StateT.ext; intro b
  simp

private theorem liftHom_liftM {α : Type} (x : m α) :
    liftHom φ (liftM x : ProveM m α) = (liftM (φ x) : ProveM m' α) := by
  apply StateT.ext; intro b; apply StateT.ext; intro st; apply OptionT.ext
  simp only [liftM, monadLift, MonadLift.monadLift, OptionT.lift, OptionT.mk,
    StateT.run_mapHom, OptionT.run_mapHom]
  simp only [bind_pure_comp, StateT.run_lift, StateT.run_map, Functor.map_map, OptionT.run_map,
    MonadHom.mmap_map]
  exact congrArg _ (MonadHom.mmap_map φ x some)

omit [LawfulMonad m] [LawfulMonad m'] in
private theorem liftHom_modify (f : Book → Book) :
    liftHom φ (modify f : ProveM m Unit) = modify f := by
  apply StateT.ext; intro b; apply StateT.ext; intro st; apply OptionT.ext
  simp

end Prover

/-! ## The wire along a morphism of its primitives -/

section Wire

variable {w w' : Type → Type} [Monad w] [Monad w'] [LawfulMonad w] [LawfulMonad w']
  (ψ : w →ᵐ w') (ops : WireOps w)

/-- The primitives carried along a monad morphism. -/
private def WireOps.map : WireOps w' where
  send x := ψ (ops.send x)
  sample := ψ ops.sample
  grind := ψ ops.grind
  commit depth leafWords rows := ψ (ops.commit depth leafWords rows)
  record ps := ψ (ops.record ps)

omit [LawfulMonad w] [LawfulMonad w'] in
private theorem sendAll_hom (xs : List E) : ψ (sendAll ops xs) = sendAll (ops.map ψ) xs := by
  induction xs with
  | nil => simp [sendAll]
  | cons x xs ih => simp [sendAll, ih, WireOps.map]

private theorem samples_hom (k : ℕ) : ψ (samples ops k) = samples (ops.map ψ) k := by
  induction k with
  | zero => simp [samples]
  | succ k ih => simp [samples, ih, WireOps.map]

private theorem positions_hom (depth t : ℕ) :
    ψ (positions ops depth t) = positions (ops.map ψ) depth t := by
  simp [positions, Verify.positionsWith_hom, WireOps.map]

omit [LawfulMonad w] [LawfulMonad w'] in
private theorem sendPlain_hom {d : ℕ} (c : Vector E (d + 1)) :
    ψ (sendPlain ops c) = sendPlain (ops.map ψ) c := sendAll_hom ψ ops _

omit [LawfulMonad w] [LawfulMonad w'] in
private theorem sendNormal_hom {d : ℕ} (c : Vector E (d + 1)) :
    ψ (sendNormal ops c) = sendNormal (ops.map ψ) c := sendAll_hom ψ ops _

omit [LawfulMonad w] [LawfulMonad w'] in
private theorem sendTables_hom {k ρ : ℕ} (c : Fin k → Vector E (2 ^ ρ)) :
    ψ (sendTables ops c) = sendTables (ops.map ψ) c := sendAll_hom ψ ops _

/-- Closes the goal `c.map ψ = c'` for two wires of the same shape, leaving the parts. -/
local macro "codec_map" : tactic => `(tactic| repeat' first
  | apply RoundCodec.map_append_of
  | apply RoundCodec.map_empty_of
  | apply RoundCodec.map_sendOne_of
  | apply RoundCodec.map_msg_of
  | apply RoundCodec.map_chal_of
  | apply RoundCodec.map_chals_of
  | apply RoundCodec.map_rounds_of
  | apply RoundCodec.map_odd_of
  | apply RoundCodec.map_steps_of)

omit [LawfulMonad w] [LawfulMonad w'] in
private theorem WireOps.map_send (x : E) : ψ (ops.send x) = (ops.map ψ).send x := rfl
omit [LawfulMonad w] [LawfulMonad w'] in
private theorem WireOps.map_sample : ψ ops.sample = (ops.map ψ).sample := rfl
omit [LawfulMonad w] [LawfulMonad w'] in
private theorem WireOps.map_grind : ψ ops.grind = (ops.map ψ).grind := rfl
omit [LawfulMonad w] [LawfulMonad w'] in
private theorem WireOps.map_commit (depth leafWords : ℕ) (rows : Vector (List K) (2 ^ depth)) :
    ψ (ops.commit depth leafWords rows) = (ops.map ψ).commit depth leafWords rows := rfl

attribute [local simp] WireOps.map_send WireOps.map_sample WireOps.map_grind WireOps.map_commit
  sendAll_hom samples_hom positions_hom sendPlain_hom sendNormal_hom sendTables_hom

omit [LawfulMonad w] [LawfulMonad w'] in
private theorem commitCodec_map (n : ℕ) {ℓ b t : ℕ} :
    (commitCodec ops n (ℓ := ℓ) (b := b) (t := t)).map ψ = commitCodec (ops.map ψ) n :=
  RoundCodec.map_sendOne_of ψ fun _ ↦ rfl

omit [LawfulMonad w] [LawfulMonad w'] in
private theorem pubCodec_map : (pubCodec ops).map ψ = pubCodec (ops.map ψ) :=
  RoundCodec.ext' (fun | ⟨0, _⟩, h, _ => nomatch h | ⟨1, _⟩, _, xs => sendAll_hom ψ ops xs)
    fun | ⟨0, _⟩, _ => rfl | ⟨1, _⟩, h => nomatch h

omit [LawfulMonad w] [LawfulMonad w'] in
private theorem flockCodecOf_map (k : ℕ) :
    (flockCodecOf ops k).map ψ = flockCodecOf (ops.map ψ) k := by
  codec_map
  all_goals first | rfl | (intro x; simp)

omit [LawfulMonad w] [LawfulMonad w'] in
private theorem flockCodecOpt_map (I : M3Instance) (o : Option (FlockRegion I.toShape)) :
    (flockCodecOpt ops I o).map ψ = flockCodecOpt (ops.map ψ) I o := by
  cases o with
  | none => exact RoundCodec.map_empty ψ
  | some r => exact flockCodecOf_map ψ ops r.kBatch

private theorem levelCodec_map (sh sh' : Whir.Shape) (κ' : ℕ) {k : List Step}
    {rest : RoundCodec w (seqSpec k)} {rest' : RoundCodec w' (seqSpec k)}
    (hrest : rest.map ψ = rest') :
    (levelCodec ops sh sh' κ' rest).map ψ = levelCodec (ops.map ψ) sh sh' κ' rest' := by
  codec_map
  all_goals first | exact hrest | rfl | (intro x; simp) | simp

private theorem finalCodec_map (sh : Whir.Shape) (nf : ℕ) :
    (finalCodec ops sh nf).map ψ = finalCodec (ops.map ψ) sh nf := by
  codec_map
  all_goals first | rfl | (intro x; simp) | simp

private theorem ladderCodec_map {sh : Whir.Shape} {κ : ℕ} (L : Ladder sh κ) :
    (ladderCodec ops L).map ψ = ladderCodec (ops.map ψ) L := by
  induction L with
  | last sh nf => exact finalCodec_map ψ ops sh nf
  | cons sh L ih => exact levelCodec_map ψ ops sh _ _ ih

/-- **The wire of the compiled schedule along a morphism of its primitives.** -/
private theorem compiledCodec_map (I : M3Instance) (n : ℕ) {sh : Whir.Shape} {κ : ℕ}
    (L : Ladder sh κ) :
    (compiledCodec ops I n L).map ψ = compiledCodec (ops.map ψ) I n L := by
  codec_map
  all_goals first
    | exact pubCodec_map ψ ops
    | exact flockCodecOpt_map ψ ops I I.flock
    | exact ladderCodec_map ψ ops L
    | rfl | (intro x; simp) | simp

end Wire

/-! ## The prover -/

section Run

variable {m m' : Type → Type} [Monad m] [Monad m'] [LawfulMonad m] [LawfulMonad m']
  (φ : m →ᵐ m') (H : List UInt8 → m Digest)

private theorem proveOps_map (fuel : ℕ) :
    (proveOps H fuel).map (liftHom φ) = proveOps (fun t ↦ φ (H t)) fuel := by
  unfold WireOps.map proveOps
  congr 1
  · funext x
    exact (liftHom_lift φ _).trans (congrArg _ (addScalar_hom φ H x))
  · exact (liftHom_lift φ _).trans (congrArg _ (sample_hom φ H))
  · exact (liftHom_lift φ _).trans (congrArg _ (grind_hom φ H fuel _))
  · funext depth leafWords rows
    simp only [MonadHom.mmap_bind, liftHom_liftM, merkleCommitWithM_hom, liftHom_modify,
      liftHom_lift, addRoot_hom]
  · funext ps
    exact liftHom_modify φ _

omit [LawfulMonad m] [LawfulMonad m'] in
private theorem liftHom_get : liftHom φ (get : ProveM m Book) = get := by
  apply StateT.ext; intro b; apply StateT.ext; intro st; apply OptionT.ext
  simp

omit [LawfulMonad m] [LawfulMonad m'] in
private theorem liftHom_failure {α : Type} : liftHom φ (failure : ProveM m α) = failure := by
  apply StateT.ext; intro b; apply StateT.ext; intro st; apply OptionT.ext
  simp

private theorem hintOpenings_hom : liftHom φ (hintOpenings : ProveM m Unit) = hintOpenings := by
  unfold hintOpenings
  simp only [MonadHom.mmap_bind, liftHom_get, MonadHom.mmap_ite, liftHom_failure,
    MonadHom.mmap_pure, MonadHom.mmap_forIn, liftHom_lift, hintOpening_hom]

private theorem writeProof_hom (ops : WireOps (ProveM m)) (F : FlockSpec) (prog : Program)
    (s : Sizes) (hs : s.Admissible prog) (ρ : ℕ) (hρ : validRate ρ) (input : PublicInput)
    (q : Column (leanIsaμ prog s)) :
    liftHom φ (writeProof H ops F prog s hs ρ hρ input q) =
      writeProof (fun t ↦ φ (H t)) (ops.map (liftHom φ)) F prog s hs ρ hρ input q := by
  simp only [writeProof, MonadHom.mmap_bind, liftHom_lift, announce_hom, Prover.runWith_hom,
    compiledCodec_map, hintOpenings_hom]

private theorem runProofFrom_hom (seed : m FsState) (wr : ProveM m Unit) :
    φ (runProofFrom seed wr) = runProofFrom (φ seed) (liftHom φ wr) := by
  simp only [runProofFrom, MonadHom.mmap_bind, MonadHom.mmap_pure, runWrite_hom]
  congr 1; funext fs; congr 1
  simp [StateT.run'_eq]

/-- **The prover from a computed start along a monad morphism**: a run of `proveFrom H seed`,
mapped by `φ`, is the run of `proveFrom` with every hash's answer and the start mapped. -/
private theorem proveFrom_hom (seed : m FsState) (fuel : ℕ) (F : FlockSpec) (prog : Program)
    (input : PublicInput) {κ : ℕ} (w : EnsembleWitness (leanIsaEnsemble prog κ)) (ρ : ℕ) :
    φ (proveFrom H seed fuel F prog input w ρ) =
      proveFrom (fun t ↦ φ (H t)) (φ seed) fuel F prog input w ρ := by
  unfold proveFrom
  split
  · simp
  · split
    · rw [runProofFrom_hom, writeProof_hom, proveOps_map]
    · simp

/-- **The prover along a monad morphism**: a run of `proveWith H`, mapped by `φ`, is the run of
`proveWith` with every hash's answer mapped. -/
theorem proveWith_hom (fuel : ℕ) (F : FlockSpec) (prog : Program) (input : PublicInput) {κ : ℕ}
    (w : EnsembleWitness (leanIsaEnsemble prog κ)) (ρ : ℕ) :
    φ (proveWith H fuel F prog input w ρ) = proveWith (fun t ↦ φ (H t)) fuel F prog input w ρ := by
  rw [proveWith, proveFrom_hom, FsState.seedWith_hom]
  rfl

end Run

end Prove

/-- **The random-oracle run is the prover at the oracle**: the prover with every hash a query to
the oracle `List UInt8 →ₒ Digest`, simulated by `impl`, is the prover with `impl` answering. -/
theorem proveWith_simulateQ {r : Type → Type} [Monad r] [LawfulMonad r]
    (impl : QueryImpl (List UInt8 →ₒ Digest) r) (fuel : ℕ) (F : FlockSpec) (prog : Program)
    (input : PublicInput) {κ : ℕ} (w : EnsembleWitness (leanIsaEnsemble prog κ)) (ρ : ℕ) :
    simulateQ impl
        (proveWith (fun t ↦ liftM ((List UInt8 →ₒ Digest).query t)) fuel F prog input w ρ) =
      proveWith impl fuel F prog input w ρ := by
  have h := Prove.proveWith_hom (simulateQ' impl)
    (fun t ↦ liftM ((List UInt8 →ₒ Digest).query t)) fuel F prog input w ρ
  simp only [simulateQ_spec_query] at h
  exact h

end
end LeanerVM.Protocol
