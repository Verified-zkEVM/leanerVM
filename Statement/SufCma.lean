module

public import Statement.RandomPermutation

/-!
# The SUF-CMA game

Read third: the SUF-CMA game of a hash-based signature scheme in the random-permutation model
(`SufCma`): a scheme over `π`, the forgery game, and `bits` bits of security
(`StronglyUnforgeable`). leanXMSS and leanSPHINCS are stated with it. The game has one key; for `k`
keys, guessing the attacked one loses a factor `k` (not proved here).
-/

@[expose] public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace Common

/-! ## The SUF-CMA game of a hash-based signature scheme, in the random-permutation model -/

namespace SufCma

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

/-- **The game**: key generation, then the adversary, which queries coins, `π`, `π⁻¹` and the
signing oracle (each request and answer logged), then the verification of its forgery. -/
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
      QueryImpl.withLogging (spec := SigningRequest →ₒ SigningResponse) (scheme.sign secretKey))
        (adversary pk)).run
  let verified ← scheme.verify pk forgery
  return scheme.winningCondition log forgery && verified

/-- **`securityBits` bits of SUF-CMA security in the random-permutation model**: every adversary
(coins, `π`, `π⁻¹` and the signing oracle) whose game, key generation, the signer's
answers and the forgery's verification included, makes at most `Q ≥ 1` permutation calls on every
path wins, against the lazily sampled random permutation, with probability at most
`(Q + 1) · 2^-securityBits`. -/
def StronglyUnforgeable
    (scheme : Scheme Seed PublicKey SecretKey SigningRequest SigningResponse Forgery)
    (securityBits : ℕ) : Prop :=
  ∀ Q, 1 ≤ Q → ∀ adversary : PublicKey →
      OracleComp (RandomPermutationOracles + (SigningRequest →ₒ SigningResponse)) Forgery,
    QueryCostAtMost (forgeryGame scheme adversary) permutationCallCost Q →
      Pr{let b ← runWithRandomPermutation (forgeryGame scheme adversary)}[b = true] ≤
        ((Q : ℝ≥0∞) + 1) * (2 : ℝ≥0∞)⁻¹ ^ securityBits

end SufCma

end Common

end
