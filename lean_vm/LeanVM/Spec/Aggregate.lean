/-
  LeanVM.Spec.Aggregate

  What the outer verifier's acceptance of a proof of the aggregation guest establishes, in the
  random-permutation model of `LeanVM/Spec/Rpm.lean`.
-/

import LeanVM.Spec.Rpm
import LeanVM.Spec.Guest

/-!
# The outer verifier's acceptance, explained

`AggregateSound guest decode`: in the random-permutation experiment of `Rpm.lean`
(`rpmExperiment`), the verifier accepts a proof of `guest` on the digest, under the deployed seed,
of a statement `s` that passes the outer verifier's other checks (`OuterChecks`, `Node.lean`),
while the execution the knowledge extractor `extractorRpm` reads off the proof and the adversary's
transcript is none, or does not explain `s` (`Explains`, `Guest.lean`: decode to the deployed
seed, `s` and a witness holding it, or give a Keccak-256 collision among `collisionCandidates`),
with probability at most the bound of `KnowledgeSoundness`,
`soundnessError Q + rpmError (Q + verifierPermCalls)`, for an adversary of at most `Q` queries to
`π` and `π⁻¹`.

Keccak-256 and Keccak-f[1600] outside the executed program are built from the random permutation;
the statement's digest and the collisions are of the deployed Keccak-256, which the guest
computes. Not a `module`: it imports `Rpm.lean`, which imports `lean_rpm`.
-/

namespace LeanVM.Node

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open scoped ENNReal

/-- **The outer verifier's acceptance, explained.** The adversary, querying `π` and `π⁻¹`,
outputs a proof. The event: the verifier accepts it as a proof of `guest` on the digest, under
the deployed seed, of a statement `s` that passes the outer verifier's other checks, and yet the
execution the knowledge extractor `extractorRpm` reads off the adversary's transcript and the
proof does not explain `s`. Its probability is at most the bound of `KnowledgeSoundness`. -/
def AggregateSound (guest : Program) (decode : Decoder) : Prop :=
  ∀ (A : RpmAdversary) (Q : ℕ), A.IsTotalQueryBound Q →
    Pr{let z ← rpmExperiment A}[∃ s : NodeStatement, z.accepted ∧ z.program = guest ∧
      publicDigest z.input = statementDigest (deployedSeed guest) s ∧ OuterChecks guest s ∧
      ¬ ∃ t, extractorRpm z.program z.input z.transcript z.proof = some t ∧
        Explains guest s (decode t.image)] ≤ soundnessError Q + rpmError (Q + verifierPermCalls)

end LeanVM.Node
