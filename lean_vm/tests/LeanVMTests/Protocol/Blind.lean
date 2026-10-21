import LeanVM.Protocol.EndToEnd.Blind.Execution
import LeanVM.Protocol.EndToEnd.Blind.Deferred

/-!
# The Flock-blind verifier V°, locked

Statement locks of `LeanVM/Protocol/EndToEnd/Blind/`: knowledge soundness of V° (the deployed
verifier with the lincheck's terminal check deleted, `LeanVM.Spec.Ideal.Blind`) in the cache
form and in the random-oracle experiment, the execution it extracts under the Flock-blind
semantics, and the refinements by the deferring and the deployed verifiers, with the axioms each
depends on. A mutation shows the deleted check matters: on a proof of zeros the lincheck without
its terminal check accepts and the deployed lincheck rejects.
-/

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol LeanVM
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd.Blind LeanVM.Protocol.Blake2sHash

/-! ## The relation -/

example (F : FlockSpec) (prog : Program) (s : Sizes) (input : PublicInput)
    (q : Column (leanIsaμ prog s)) :
    M3HoldsBlind (leanIsaInstance F prog s) input q ↔
      (leanIsaInstance F prog s).ConstraintsVanish q ∧ (leanIsaInstance F prog s).Balanced q ∧
        (leanIsaInstance F prog s).CountsNonzero q ∧
        (leanIsaInstance F prog s).PublicLinesHold input q :=
  Iff.rfl

example (F : FlockSpec) (prog : Program) (s : Sizes) (input : PublicInput)
    (q : Column (leanIsaμ prog s)) :
    M3Holds (leanIsaWith F prog s none) input q ↔ M3HoldsBlind (leanIsaInstance F prog s) input q :=
  m3Holds_none_iff F prog s input q

/-- The deployed instance is the instance with `BLAKE2s`'s Flock region. -/
example (F : FlockSpec) (prog : Program) (s : Sizes) :
    leanIsaWith F prog s (some (flockRegion prog s F)) = leanIsaInstance F prog s :=
  rfl

/-! ## Knowledge soundness of V° -/

example (prog : Program) (input : PublicInput) (h : List Ev) :
    (2 : ENNReal)⁻¹ ^ min (grindBits h) 64 * (blindCert prog input).ε h ≤ (2 : ENNReal)⁻¹ ^ 128 :=
  blindCert_bound prog input h

example {ℓ : Log} (hf : ¬ Fail LeanVM.Protocol.EndToEnd.Sound.leanVmSeeds ℓ) {x : Statement}
    {π : LeanVM.Proof}
    (hv : verifyBlindWith (look ℓ) (bytecodeWords x.1) (publicDigest x.2) π = some true) :
    1 ≤ pot anyCertBlind.D LeanVM.Protocol.EndToEnd.Sound.leanVmSeeds anyProgramBlind ℓ ∨
      ExtractedBlind x.1 x.2 (LeanVM.Protocol.Rom.cacheOf ℓ) π :=
  blind_knowledge_cache' hf hv

example {A : Adversary} {Q : ℕ} (hA : A.IsTotalQueryBound Q) :
    Pr{let z ← experimentBlind A}[z.1.2 = true ∧ ¬ ExtractedBlind z.1.1.1.1 z.1.1.1.2 z.2 z.1.1.2]
      ≤ soundnessError Q :=
  blindKnowledgeSoundness hA

example {A : Adversary} {Q : ℕ} (hA : A.IsTotalQueryBound Q) :
    Pr{let z ← experimentBlind A}[z.1.2 = true ∧ SentinelSafe z.1.1.1.1 ∧
      ¬ ∃ t, extractBlind z.1.1.1.1 z.1.1.1.2 z.2 z.1.1.2 = some t ∧
        ValidExecutionB blakeFree z.1.1.1.1 z.1.1.1.2 t] ≤ soundnessError Q :=
  blindKnowledgeSoundness_execution hA

/-- The experiment with V° is the deployed experiment with `verifyBlindWith` for `verifyWith`. -/
example (A : Adversary) :
    experimentBlind A = (simulateQ LeanVM.HashSpec.randomOracle
      (A >>= fun z ↦ (z, ·) <$> verifyBlindWith queryH (bytecodeWords z.1.1)
        (publicDigest z.1.2) z.2)).run ∅ :=
  rfl

/-! ## The execution -/

example (F : FlockSpec) {prog : Program} {input : PublicInput} {s : Sizes}
    {q : Column (leanIsaμ prog s)} (hsafe : SentinelSafe prog) (hs : s.Admissible prog)
    (h : M3HoldsBlind (leanIsaInstance F prog s) input q) :
    ∃ t, AssignmentRepresentsB blakeFree (witnessOf F prog s q) t ∧
      ValidExecutionB blakeFree prog input t :=
  execution_of_extractedBlind F hsafe hs h

/-! ## The refinements -/

example {bytecode : List K} {c : FixedClaims} (hc : c.BytecodeHolds bytecode)
    (publicInput : Digest) :
    Prog.Le (deferredProgram c bytecode publicInput) (blindProgram bytecode publicInput) :=
  deferredProgram_le_blind hc publicInput

example {H : Bytes → Option Digest} {bytecode : List K} {publicInput iv : Digest}
    {c : FixedClaims} (hc : multilinearEval (bytecode.map ofK) c.bytecodePoint = c.bytecodeValue)
    (hiv : fiatShamirIvWith H bytecode = some iv) {π : LeanVM.Proof}
    (h : verifyDeferredWith H bytecode iv publicInput c π = some true) :
    verifyBlindWith H bytecode publicInput π = some true :=
  verifyBlindWith_of_verifyDeferredWith hc hiv h

example {H : Bytes → Option Digest} {bytecode : List K} {publicInput : Digest} {π : LeanVM.Proof}
    (h : verifyWith H bytecode publicInput π = some true) :
    verifyBlindWith H bytecode publicInput π = some true :=
  verifyBlindWith_of_verifyWith h

example {bytecode : List K} {publicInput : Digest} {π : LeanVM.Proof}
    (h : Verifier.verify bytecode publicInput π = true) :
    Id.run (verifyBlindWith blake2sBytes bytecode publicInput π) = true :=
  verifyBlind_of_verify h

/-! ## The deleted check matters -/

/-- A zerocheck result with the three claims zero: the lincheck's claim is `α³`. -/
def zc₀ : ZerocheckResult := ⟨1, List.replicate 20 1, 0, 0, 0⟩

/-- A seed. -/
def seed₀ : Digest := blake2sBytes [1, 2, 3]

/-- The lincheck, run from `seed₀` on a stream of `n` zero scalars, accepted. -/
def lincheckAccepts (p : Prog (List E × List E)) (n : ℕ) : Bool :=
  Id.run (runProof blake2sBytes (p >>= fun _ ↦ pure true) seed₀ ⟨List.replicate n 0, []⟩)

-- Eight rounds of two coefficients and the 64 slices: on eighty zeros the lincheck without its
-- terminal check accepts, as it accepts every complete stream.
#guard lincheckAccepts (verifyFlockLincheckBlind zc₀) 80
-- Mutation: the deployed lincheck rejects them, its terminal identity `0 = α³ · Π rᵢ` failing.
#guard !lincheckAccepts (verifyFlockLincheck .computed zc₀) 80

/-! ## Axioms -/

/--
info: 'LeanVM.Protocol.m3Holds_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms m3Holds_none_iff

/--
info: 'LeanVM.Protocol.EndToEnd.Blind.blindCert_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms blindCert_bound

/--
info: 'LeanVM.Protocol.EndToEnd.Blind.blind_knowledge_cache' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms blind_knowledge_cache

/--
info: 'LeanVM.Protocol.EndToEnd.Blind.blind_knowledge_cache'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms blind_knowledge_cache'

/--
info: 'LeanVM.Protocol.EndToEnd.Blind.blindKnowledgeSoundness' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms blindKnowledgeSoundness

/--
info: 'LeanVM.Protocol.EndToEnd.Blind.blindKnowledgeSoundness_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms blindKnowledgeSoundness_execution

/--
info: 'LeanVM.Protocol.EndToEnd.Blind.execution_of_extractedBlind' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms execution_of_extractedBlind

/--
info: 'LeanVM.Protocol.EndToEnd.Blind.constraintSoundnessBlind' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms constraintSoundnessBlind

/--
info: 'LeanVM.Protocol.Verifier.deferredProgram_le_blind' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms deferredProgram_le_blind

/--
info: 'LeanVM.Protocol.Verifier.verifyBlindWith_of_verifyDeferredWith' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms verifyBlindWith_of_verifyDeferredWith

/--
info: 'LeanVM.Protocol.Verifier.verifyBlindWith_of_verifyWith' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms verifyBlindWith_of_verifyWith

/--
info: 'LeanVM.Protocol.Verifier.verifyBlind_of_verify' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms verifyBlind_of_verify
