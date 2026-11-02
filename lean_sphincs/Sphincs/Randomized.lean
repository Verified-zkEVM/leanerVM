module

public import Sphincs.Scheme
public import Common.WithHash

/-!
The signer variant with a truly uniform randomizer base per signing call (attempt `i` uses
`start + i`). Key derivation and surrogate
derivation still use the master seed and the same shared hash oracle as the reference scheme.
This is distinct from Rust's seed-derived randomizers; no equivalence is assumed.
-/

open OracleComp OracleSpec

namespace SphincsLayered.Randomized

@[expose] public section

open Concrete

variable [Params]

/-- The scan from a start: no randomness. -/
def scanLoop (sk : Seeded.SecretKey) (message : Message) :
    Nat → Randomizer → OracleComp HashSpec (Option Randomizer)
  | 0, _ => pure none
  | attempts + 1, randomness => do
      let result ← Seeded.signAttempt sk message randomness
      match result with
      | some _ => pure (some randomness)
      | none => scanLoop sk message attempts (randomness + 1)

/-- One uniform start, then the scan. -/
noncomputable def signDigestLoop (sk : Seeded.SecretKey) (message : Message) (attempts : Nat) :
    OracleComp OracleWorld (Option Randomizer) := do
  let start ← liftM ($ᵗ Randomizer : ProbComp Randomizer)
  liftM (scanLoop sk message attempts start)

/-- Assemble the signature after a randomizer lands, using the reference hash layouts. -/
def finishSign (sk : Seeded.SecretKey) (message : Message) (randomness : Randomizer) :
    OracleComp HashSpec (Option Signature) := do
  let digest ← messageDigest sk.parameter message randomness
  let index := digestIndex digest
  let opening ← Seeded.forestOpen sk.parameter index (digestMarks digest) sk.schemeSeed
  let some layers ← sequenceLayers (fun lay => Seeded.signLayer sk index lay) | return none
  return some ⟨randomness, opening, layers⟩

/-- The stateless signer with truly random randomizers and an explicit exhaustion result. -/
noncomputable def sign (sk : Seeded.SecretKey) (message : Message) :
    OracleComp OracleWorld (Option Signature) := do
  let some randomness ← signDigestLoop sk message digestAttemptLimit | return none
  liftM (finishSign sk message randomness)

end

end SphincsLayered.Randomized
