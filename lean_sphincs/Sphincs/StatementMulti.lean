module

public import Sphincs.StatementDet

/-!
# Multi-user SUF-CMA for the deterministic signer

`n` honest keys, each generated from its own uniform 32-byte seed (`Seeded.keygenFromSeed`, in the
order `0, …, n − 1`, after the `n` seeds are drawn), all sharing the one random oracle. The adversary gets the `n` public keys, the
random oracle and one signing oracle per key (`Seeded.sign` of that key; requests are pairs
`(key, message)`). It outputs a key index, a message and a signature, and wins if the final
`Concrete.verify` under that key accepts, the pair is not one that key's signing oracle returned, and
that key's signing oracle answered at most `signatureLimit` requests (repeats included). Every hash
call of the experiment counts: all key generations, all signing calls and the final verification.

The budgeted form of the single-key notion of `StatementDet` (`Det.HasClassicalSecurityBitsDetBudgeted`)
bounds the probability of a win *within* `q` hash calls, for every adversary: no query bound is
assumed. It implies `Det.HasClassicalSecurityBitsDet`, and it is the form a reduction that may
overrun the budget on rare outcomes can use.
-/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security

@[expose] public section

variable [Params]

namespace Det

/-- The probability that the forgery wins and the experiment made at most `q` hash calls. -/
noncomputable def winWithin (adversary : Adversary) (q : Nat) : ℝ≥0∞ :=
  Pr{let result ← experimentDet adversary}[result.1 = true ∧ result.2 ≤ q]

/-- **`bits` classical bits, budgeted**: for every `q ≥ 1` and every adversary, the probability of a
win within `q` hash calls is at most `q / 2^bits`. -/
def HasClassicalSecurityBitsDetBudgeted (bits : Nat) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary, winWithin adversary q ≤ q / ((2 ^ bits : Nat) : ℝ≥0∞)

theorem HasClassicalSecurityBitsDetBudgeted.unbudgeted {bits : Nat}
    (h : HasClassicalSecurityBitsDetBudgeted bits) : HasClassicalSecurityBitsDet bits := by
  intro q hq adversary hbound
  refine le_trans (le_of_eq ?_) (h q hq adversary)
  exact prEvent_congr_of_support _ _ _ fun result hresult => ⟨fun hw => ⟨hw, hbound result hresult⟩, And.left⟩

end Det

namespace Multi

variable (n : Nat)

/-- A forgery for one of the `n` keys. -/
structure Forgery where
  key : Fin n
  message : Message
  signature : Signature

/-- The signing oracles of the `n` keys: a request names the key and the message. -/
abbrev SigningSpec := (Fin n × Message) →ₒ Option Signature

structure Adversary where
  main : (Fin n → PublicKey) → OracleComp (OracleWorld + SigningSpec n) (Forgery n)

variable {n}

/-- The number of requests answered by the signing oracle of key `j`, repeats included. -/
def requests (log : QueryLog (SigningSpec n)) (j : Fin n) : Nat :=
  (log.filter fun entry => decide (entry.1.1 = j)).length

/-- The signing oracle of key `j` answered at most `signatureLimit` requests. -/
def Valid (log : QueryLog (SigningSpec n)) (j : Fin n) : Prop := requests log j ≤ signatureLimit

instance (log : QueryLog (SigningSpec n)) (j : Fin n) : Decidable (Valid log j) :=
  inferInstanceAs (Decidable (requests log j ≤ signatureLimit))

/-- The signing oracle of the forgery's key returned its pair. -/
def Contains (log : QueryLog (SigningSpec n)) (forgery : Forgery n) : Prop :=
  ∃ entry ∈ log, entry.1 = (forgery.key, forgery.message) ∧ entry.2 = some forgery.signature

instance (log : QueryLog (SigningSpec n)) (forgery : Forgery n) : Decidable (Contains log forgery) :=
  inferInstanceAs (Decidable (∃ entry ∈ log, entry.1 = (forgery.key, forgery.message) ∧
    entry.2 = some forgery.signature))

/-- The seeds of the `n` keys: independent uniform 32-byte seeds. -/
noncomputable def sampleSeeds (n : Nat) : ProbComp (Fin n → MasterSeed) :=
  letI := SampleableType.ofFintype (Fin n → MasterSeed)
  $ᵗ (Fin n → MasterSeed)

/-- Key generation of `k` keys from their seeds (`Seeded.keygenFromSeed`), in the order `0, …, k − 1`. -/
def keygenAll : (k : Nat) → (Fin k → MasterSeed) → OracleComp HashSpec (Fin k → PublicKey × Seeded.SecretKey)
  | 0, _ => pure Fin.elim0
  | k + 1, seeds => do
      let keys ← keygenAll k fun i => seeds i.castSucc
      let key ← Seeded.keygenFromSeed (seeds (Fin.last k))
      return Fin.lastCases key keys

/-- The signing oracles: `Seeded.sign` of the requested key, with the log of all requests. -/
noncomputable def signingOracle (keys : Fin n → PublicKey × Seeded.SecretKey) :
    QueryImpl (SigningSpec n) (WriterT (QueryLog (SigningSpec n)) (OracleComp OracleWorld)) :=
  QueryImpl.withLogging fun request =>
    liftM (Seeded.sign (keys request.1).2 request.2 : OracleComp HashSpec (Option Signature))

noncomputable def gameCore (adversary : Adversary n) : OracleComp OracleWorld Bool := do
  let seeds ← liftM (sampleSeeds n)
  let keys ← liftM (keygenAll n seeds)
  let ((forgery, log) : Forgery n × QueryLog (SigningSpec n)) ←
    (simulateQ (QueryImpl.ofLift OracleWorld
      (WriterT (QueryLog (SigningSpec n)) (OracleComp OracleWorld)) + signingOracle keys)
      (adversary.main fun j => (keys j).1)).run
  let verified ← liftM (Concrete.verify (keys forgery.key).1 forgery.message forgery.signature :
    OracleComp HashSpec Bool)
  return decide (Valid log forgery.key ∧ ¬Contains log forgery) && verified

/-- The counted experiment: the result and the number of hash calls. -/
noncomputable def experiment (adversary : Adversary n) : ProbComp (Bool × Nat) :=
  (simulateQ countedOracle (gameCore adversary)).run.run' ∅

noncomputable def forgeAdvantage (adversary : Adversary n) : ℝ≥0∞ :=
  Pr{let result ← experiment adversary}[result.1 = true]

def HasHashQueryBound (adversary : Adversary n) (q : Nat) : Prop :=
  ∀ result ∈ support (experiment adversary), result.2 ≤ q

/-- **Multi-user security with the bound `ε`**: every adversary against `n` keys whose experiment
makes at most `q ≥ 1` hash calls on every outcome wins with probability at most `ε q`. -/
def HasMultiUserBound (n : Nat) (ε : Nat → ℝ≥0∞) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary : Adversary n, HasHashQueryBound adversary q → forgeAdvantage adversary ≤ ε q

end Multi

end

end Sphincs.Security
