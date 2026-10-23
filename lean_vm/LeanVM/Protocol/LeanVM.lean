/-
  LeanVM.Protocol.LeanVM

  The proof of the two statements of `LeanVM/Spec/Statement.lean`: knowledge soundness of the
  leanVM verifier in the random-oracle model (`LeanVM.Protocol.LeanVMSound`), and completeness.
-/

module

public import LeanVM.Protocol.LeanVMSound
public import LeanVM.Protocol.EndToEnd.Complete.Statement

/-!
# leanVM, end to end

The statements are in `LeanVM/Spec/` (the ISA, the verifier, the extractor and
`Statement.lean`), which imports nothing else from the repository. Knowledge soundness,
`knowledgeSoundness_holds`, and its numbers are proved in `LeanVM.Protocol.LeanVMSound`; this page
proves completeness, `completeness_holds`, with an explicit honest prover.

**Completeness** (`completeness`): for a valid execution whose committed size
(`Trace.committedSize`: the memory, the bytecode and a table per opcode, each at its height) is at
most `2^28`, the most the verifier admits, the honest prover
(`honestProver`), run in the same random-oracle experiment, makes the verifier reject with probability at most
`completenessError fuel`, which is below `2^-128` at a fuel of `2^25` nonces per proof of work
(`completenessError_le`). The honest prover is a specification, not an implementation.

**Scope and trust.**

* Keccak-256 and Keccak-f[1600] are modelled as independent random oracles.
* A proof is the Python verifier's format: the scalar stream and one full Merkle path per query.
  The Rust prover ships pruned paths (shared siblings per batch, `MerkleOpenings::Pruned`), which
  the deployed `leanvm_core::cpu::verify` expands into these paths and checks more strictly; that
  expansion is not formalized.
* That `verifier` is the Python and Rust verifiers is test evidence: it is a transcription of the
  Python, it accepts the Rust prover's proofs, and on mutated proofs it gives the Rust verifier's
  verdict every time (`scripts/fuzz-verifier.py`).
* Every theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.
-/

namespace LeanVM

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.KeccakHash
open Air.Flat (EnsembleWitness)
open LeanVM.Protocol.Rom (cacheOf map_run_simulateQ_loggedRO_nil map_run_simulateQ_loggedRO)
open scoped ENNReal

@[expose] public section

/-! ## Completeness -/

/-- **The honest prover**: the proof of the execution `t` at the commitment's inverse rate `2^ρ`,
every hash a query to the random oracle for Keccak-256 and every permutation one to the random
oracle for Keccak-f[1600], each proof-of-work search trying at most `fuel` nonces (the empty proof
if one fails). A specification: it takes a witness of leanISA's constraint system representing the
execution (a classical choice), pads its tables with the public padding rows, and runs the honest
strategy of every phase through the Fiat-Shamir transform (`Complete.honestProverRom`). -/
noncomputable def honestProver (prog : Program) (input : PublicInput) (t : Trace prog)
    (ρ fuel : ℕ) : Adversary :=
  Complete.honestProverRom prog input t ρ fuel

/-- The statement's completeness error is the random-oracle theorem's,
`(12012 + 48017 · (2^27 + 2·fuel + 2)) · (1 - 2^-17)^fuel`. -/
theorem completenessError_eq (fuel : ℕ) :
    completenessError fuel = Complete.completenessError fuel :=
  Complete.completenessError_eq fuel

/-- **Completeness.** For a valid execution whose committed size is at most `2^28`, at an inverse
rate `2^ρ` with `1 ≤ ρ ≤ 4`: the verifier rejects the honest prover's proof, in the random-oracle
experiment, with probability at most `completenessError fuel`. -/
theorem completeness {prog : Program} {input : PublicInput} {t : Trace prog}
    (hv : ValidExecution prog input t) (hbudget : t.committedSize ≤ 2 ^ 28) {ρ : ℕ}
    (hρ : 1 ≤ ρ ∧ ρ ≤ 4) {fuel : ℕ} (hfuel : fuel ≤ 2 ^ 64) :
    Pr{let z ← experiment (honestProver prog input t ρ fuel)}[z.1.2 = false] ≤
      completenessError fuel :=
  Complete.completeness_le hv hbudget hρ hfuel

/-- **The numbers**: at a fuel of `2^25` nonces per proof of work, the completeness error is
below `2^-128`. -/
theorem completenessError_le : completenessError (2 ^ 25) ≤ (2 : ℝ≥0∞)⁻¹ ^ 128 :=
  Complete.statement_completenessError_le

/-! ## The statement of `LeanVM/Spec/Statement.lean` -/

/-- **Completeness holds**, with the honest prover `honestProver`. -/
theorem completeness_holds : Completeness :=
  Complete.completeness_holds

end
end LeanVM
