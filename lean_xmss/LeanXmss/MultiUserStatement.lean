module

public import LeanXmss.Statement

/-!
# leanXMSS security statements: attributed and multi-user

`Statement.lean` bounds the forgery probability of one key by its adversary's worst-case budget of
hash calls. Here the bound is in the hash calls the attack can direct at the key.

* **Attributed** (`HasAttributedSecurity`): a hash call after key generation is attributable to the
  key when its input starts with the key's public parameter `P`, as every input of the scheme's
  hashes after key generation does. The forgery probability is two units (`2^-128`) per expected
  attributable call, plus a constant, a term of second order in the budget and the guesses of the
  key's two seeds.
* **Multi-user** (`MultiUser.HasMultiUserSecurity`): `n` keys, generated from independent seeds in
  one shared random oracle, each with its own signing oracle; a forgery names a key and wins when it
  verifies under that key, the key never reused a leaf index and never answered a request with that
  message and signature. The budget counts every hash call: all key generations, every signature,
  the adversary's and the final verification's.
-/

open OracleComp OracleSpec ENNReal

namespace LeanXmss

@[expose] public section

namespace Security

/-- A hash call attributable to the key with public key `publicKey`: its input starts with the key's
public parameter. -/
def IsAttributed (publicKey : PublicKey) : OracleWorld.Domain → Prop
  | .inl _ => False
  | .inr input => bytesLE 16 publicKey.parameter <+: input

instance (publicKey : PublicKey) : DecidablePred (IsAttributed publicKey) := fun input =>
  match input with
  | .inl _ => isFalse id
  | .inr input => inferInstanceAs (Decidable (bytesLE 16 publicKey.parameter <+: input))

/-- The game after key generation: the adversary with its signing oracle, then the final
verification, as in `gameCore`. -/
noncomputable def gameRest (adversary : Adversary) (publicKey : PublicKey)
    (secretKey : Seeded.SecretKey) : OracleComp OracleWorld Bool := do
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (QueryImpl.ofLift OracleWorld (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) +
      signingOracle secretKey) (adversary.main publicKey)).run
  let verified ← liftM (Concrete.verify publicKey forgery.message forgery.signature : OracleComp HashSpec Bool)
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

/-- Answer hash queries consistently, forward private sampling, and count one per call
attributable to the key with public key `publicKey`. -/
noncomputable def attributedOracle (publicKey : PublicKey) :=
  (unifFwdImpl HashSpec + (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))).withAddCost
    (fun input => if IsAttributed publicKey input then 1 else (0 : Nat))

/-- Generate the key from a uniform seed in the random oracle, then run the rest of the game,
counting the hash calls attributable to the key. -/
noncomputable def attributedExperiment (adversary : Adversary) : ProbComp (Bool × Nat) := do
  let seed ← sampleMasterSeed
  let keys ← (simulateQ (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
    (Seeded.keygenFromSeed seed)).run ∅
  (simulateQ (attributedOracle keys.1.1) (gameRest adversary keys.1.1 keys.1.2)).run.run' keys.2

/-- The expected number of hash calls after key generation attributable to the key. -/
noncomputable def expectedAttributedQueries (adversary : Adversary) : ℝ≥0∞ :=
  ∑' result, Pr{let x ← attributedExperiment adversary}[x = result] * (result.2 : ℝ≥0∞)

/-- For a budget `q < 2^127`, the forgery probability is at most two units per expected attributable
call, plus `2^10` units, a term of second order `4 q (E + 2^10) / 2^256`, and one guess of each of
the key's two 256-bit seeds per call. -/
def HasAttributedSecurity : Prop :=
  ∀ q, q < 2 ^ 127 → ∀ adversary, HasHashQueryBound adversary q →
    forgeAdvantage adversary ≤
      (2 * expectedAttributedQueries adversary + 2 ^ 10) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
        4 * q * (expectedAttributedQueries adversary + 2 ^ 10) / ((2 ^ 256 : Nat) : ℝ≥0∞) +
        2 * q / ((2 ^ 256 : Nat) : ℝ≥0∞)

end Security

/-- The attributed security claim. -/
abbrev LeanXmssAttributedSecurityStatement : Prop := Security.HasAttributedSecurity

end

end LeanXmss
