module

public import Statement.RandomPermutation

/-!
# The SUF-CMA game

Read third: the SUF-CMA game of a hash-based signature scheme in the random-permutation model
(`SufCma`): a scheme over `π`, its signing oracle logged, the forgery game and experiment, and
`bits` bits of security (`StronglyUnforgeable`). leanXMSS and leanSPHINCS are stated with it.
-/

@[expose] public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace Common

/-! ## The SUF-CMA game of a hash-based signature scheme, in the random-permutation model -/

/-- A byte as its residue modulo `256`. -/
def uInt8EquivFin : UInt8 ≃ Fin 256 where
  toFun b := b.toFin
  invFun f := UInt8.ofFin f
  left_inv _ := rfl
  right_inv _ := rfl

namespace SufCma

/-- **The digest bytes as a bit vector**, little endian: byte `i` is bits `8 i … 8 i + 7`
(`digestBitVec_extract`). -/
def digestBytesEquivBitVec : DigestBytes ≃ BitVec 256 :=
  (arrayVectorEquivFin UInt8 32).trans <|
    (Equiv.arrowCongr (Equiv.refl _) uInt8EquivFin).trans <|
      finFunctionFinEquiv.trans <| (finCongr (show 256 ^ 32 = 2 ^ 256 by norm_num)).trans
        ⟨BitVec.ofFin, BitVec.toFin, fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- **A signature scheme** over the model's oracles: a seed sampler, key generation from a seed, the
signer answering a request `SigningRequest` with `SigningResponse`, the verifier of a claimed
forgery `Forgery`, and the winning condition on the signing transcript and the forgery. Key
generation, the signer and the verifier hash with Keccak-256 over `π`
(`keccak256With queryPermutation`). -/
structure Scheme (Seed PublicKey SecretKey SigningRequest SigningResponse Forgery : Type) where
  /-- Sample the secret seed. -/
  sampleSeed : ProbComp Seed
  /-- Generate the keys from the seed. -/
  generateKeys : Seed → OracleComp RandomPermutationOracles (PublicKey × SecretKey)
  /-- Answer a signing request. -/
  sign : SecretKey → SigningRequest → OracleComp RandomPermutationOracles SigningResponse
  /-- Verify a claimed forgery. -/
  verify : PublicKey → Forgery → OracleComp RandomPermutationOracles Bool
  /-- The transcript and the forgery make a win (when the forgery verifies). -/
  winningCondition : QueryLog (SigningRequest →ₒ SigningResponse) → Forgery → Bool

variable {Seed PublicKey SecretKey SigningRequest SigningResponse Forgery : Type}

/-- The signer returned the forgery: some request with the forgery's message (`messageOfRequest`)
was answered with its signature. Any other signature of a signed message is a strong forgery. -/
abbrev SignerReturnedForgery {Message Signature : Type}
    (messageOfRequest : SigningRequest → Message)
    (log : QueryLog (SigningRequest →ₒ Option Signature)) (forgedMessage : Message)
    (forgedSignature : Signature) : Prop :=
  ∃ entry ∈ log, messageOfRequest entry.1 = forgedMessage ∧ entry.2 = some forgedSignature

/-- The signing oracle: the signer's answer, each request and answer recorded. -/
def loggedSigningOracle
    (scheme : Scheme Seed PublicKey SecretKey SigningRequest SigningResponse Forgery)
    (secretKey : SecretKey) :
    QueryImpl (SigningRequest →ₒ SigningResponse)
      (WriterT (QueryLog (SigningRequest →ₒ SigningResponse))
        (OracleComp RandomPermutationOracles)) :=
  QueryImpl.withLogging fun r ↦ scheme.sign secretKey r

/-- **The game**: key generation, then the adversary, which queries coins, `π`, `π⁻¹` and the
signing oracle, then the verification of its forgery. -/
noncomputable def forgeryGame
    (scheme : Scheme Seed PublicKey SecretKey SigningRequest SigningResponse Forgery)
    (adversary : PublicKey →
      OracleComp (RandomPermutationOracles + (SigningRequest →ₒ SigningResponse)) Forgery) :
      OracleComp RandomPermutationOracles Bool := do
  let seed ← liftM scheme.sampleSeed
  let (pk, secretKey) ← scheme.generateKeys seed
  let ((forgery, log) : Forgery × QueryLog (SigningRequest →ₒ SigningResponse)) ←
    (simulateQ
      (QueryImpl.ofLift RandomPermutationOracles
        (WriterT (QueryLog (SigningRequest →ₒ SigningResponse))
          (OracleComp RandomPermutationOracles)) +
      loggedSigningOracle scheme secretKey) (adversary pk)).run
  let verified ← scheme.verify pk forgery
  return scheme.winningCondition log forgery && verified

/-- **The experiment**: the game against the lazily sampled random permutation. -/
noncomputable def forgeryExperiment
    (scheme : Scheme Seed PublicKey SecretKey SigningRequest SigningResponse Forgery)
    (adversary : PublicKey →
      OracleComp (RandomPermutationOracles + (SigningRequest →ₒ SigningResponse)) Forgery) :
    ProbComp Bool :=
  runWithRandomPermutation (forgeryGame scheme adversary)

/-- **`securityBits` bits of SUF-CMA security in the random-permutation model**: every adversary
(coins, `π`, `π⁻¹` and the signing oracle) whose game, key generation, the signer's
answers and the forgery's verification included, makes at most `Q ≥ 1` permutation calls on every
path wins with probability at most `(Q + 1) · 2^-securityBits`. -/
def StronglyUnforgeable
    (scheme : Scheme Seed PublicKey SecretKey SigningRequest SigningResponse Forgery)
    (securityBits : ℕ) : Prop :=
  ∀ Q, 1 ≤ Q → ∀ adversary : PublicKey →
      OracleComp (RandomPermutationOracles + (SigningRequest →ₒ SigningResponse)) Forgery,
    QueryCostAtMost (forgeryGame scheme adversary) permutationCallCost Q →
      Pr{let b ← forgeryExperiment scheme adversary}[b = true] ≤
        ((Q : ℝ≥0∞) + 1) * (2 : ℝ≥0∞)⁻¹ ^ securityBits

end SufCma

end Common

end
