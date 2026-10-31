module

public import Statement.RandomPermutation

/-!
# The SUF-CMA game

Read third: the SUF-CMA game of a hash-based signature scheme in the random-permutation model
(`SufCma`): a scheme over `π`, its signing oracle logged, the forgery game and experiment, and `bits`
bits of security (`StronglyUnforgeable`). leanXMSS and leanSPHINCS are stated with it.
-/

@[expose] public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

set_option linter.unusedSectionVars false

namespace Common

/-! ## The SUF-CMA game of a hash-based signature scheme, in the random-permutation model -/

namespace SufCma

/-- **The digest bytes as a bit vector**, little endian: byte `i` is bits `8 i … 8 i + 7`
(`digestBitVec_extract`). -/
def digestBitVec : DigestBytes ≃ BitVec 256 :=
  (arrayVectorEquivFin UInt8 32).trans <|
    (Equiv.arrowCongr (Equiv.refl _) uInt8EquivFin).trans <|
      finFunctionFinEquiv.trans <| (finCongr (show 256 ^ 32 = 2 ^ 256 by norm_num)).trans
        ⟨BitVec.ofFin, BitVec.toFin, fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- **A signature scheme** over the model's oracles: a seed sampler, key generation from a seed,
the signer answering a request `Req` with `Resp`, the verifier of a claimed forgery `F`, and the
winning condition on the signing transcript and the forgery. Key generation, the signer and the
verifier hash with Keccak-256 over `π` (`keccak256With queryPermutation`). -/
structure Scheme (Seed PK SK Req Resp F : Type) where
  /-- Sample the secret seed. -/
  sample : ProbComp Seed
  /-- Generate the keys from the seed. -/
  keygen : Seed → OracleComp RandomPermutationOracles (PK × SK)
  /-- Answer a signing request. -/
  sign : SK → Req → OracleComp RandomPermutationOracles Resp
  /-- Verify a claimed forgery. -/
  verify : PK → F → OracleComp RandomPermutationOracles Bool
  /-- The transcript and the forgery make a win (when the forgery verifies). -/
  win : QueryLog (Req →ₒ Resp) → F → Bool

variable {Seed PK SK Req Resp F : Type}

/-- The signer returned the forgery: some request with the forgery's message (`message`) was
answered with its signature. Any other signature of a signed message is a strong forgery. -/
abbrev SignerReturned {M S : Type} (message : Req → M) (log : QueryLog (Req →ₒ Option S)) (m : M)
    (s : S) : Prop :=
  ∃ entry ∈ log, message entry.1 = m ∧ entry.2 = some s

/-- The signing oracle: the signer's answer, each request and answer recorded. -/
def loggedSigningOracle (S : Scheme Seed PK SK Req Resp F) (sk : SK) :
    QueryImpl (Req →ₒ Resp)
      (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp RandomPermutationOracles)) :=
  QueryImpl.withLogging fun r ↦ S.sign sk r

/-- **The game**: key generation, then the adversary, which queries coins, `π`, `π⁻¹` and the
signing oracle, then the verification of its forgery. -/
noncomputable def forgeryGame (S : Scheme Seed PK SK Req Resp F)
    (main : PK → OracleComp (RandomPermutationOracles + (Req →ₒ Resp)) F) :
      OracleComp RandomPermutationOracles Bool := do
  let seed ← liftM S.sample
  let (pk, sk) ← S.keygen seed
  let ((forgery, log) : F × QueryLog (Req →ₒ Resp)) ←
    (simulateQ
      (QueryImpl.ofLift RandomPermutationOracles
        (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp RandomPermutationOracles)) +
      loggedSigningOracle S sk) (main pk)).run
  let verified ← S.verify pk forgery
  return S.win log forgery && verified

/-- **The experiment**: the game against the lazily sampled random permutation. -/
noncomputable def forgeryExperiment (S : Scheme Seed PK SK Req Resp F)
    (main : PK → OracleComp (RandomPermutationOracles + (Req →ₒ Resp)) F) : ProbComp Bool :=
  runWithRandomPermutation (forgeryGame S main)

/-- **`bits` bits of SUF-CMA security in the random-permutation model**: every adversary `main`
(coins, `π`, `π⁻¹` and the signing oracle) whose game, key generation, the signer's
answers and the forgery's verification included, makes at most `Q ≥ 1` permutation calls on every
path wins with probability at most `(Q + 1) · 2^-bits`. -/
def StronglyUnforgeable (S : Scheme Seed PK SK Req Resp F) (bits : ℕ) : Prop :=
  ∀ Q, 1 ≤ Q → ∀ main : PK → OracleComp (RandomPermutationOracles + (Req →ₒ Resp)) F,
    QueryCostAtMost (forgeryGame S main) permutationCallCost Q →
      Pr{let b ← forgeryExperiment S main}[b = true] ≤ ((Q : ℝ≥0∞) + 1) * (2 : ℝ≥0∞)⁻¹ ^ bits

end SufCma

end Common

end
