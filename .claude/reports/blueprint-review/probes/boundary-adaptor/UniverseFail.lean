/-
  Probe (boundary-adaptor), EXPECTED TO FAIL: ArkLib's knowledge-soundness game and its
  straight-line extractor cannot be stated with the witness of `SatisfiedBy`, which lives in
  `Type 1`. Scratch work for the blueprint review.
  Run from the repository root:
    flock .claude/reports/blueprint-review/logs/lean.lock \
      lake env lean .claude/reports/blueprint-review/probes/boundary-adaptor/UniverseFail.lean
-/
import LeanerVM

open LeanerVM LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization
open LeanerVM.Protocol OracleComp OracleSpec ProtocolSpec
open Air.Flat (Ensemble EnsembleWitness Component)

namespace Probe

/-- Expected failure 1: a straight-line extractor whose output is an `EnsembleWitness`. -/
example (prog : Program) {n : ℕ} (pSpec : ProtocolSpec n) : Type :=
  Extractor.Straightline []ₒ PublicInput (EnsembleWitness (leanIsaEnsemble prog)) Unit pSpec

/-- Expected failure 2: post-composing an extractor of stacks with a map to `EnsembleWitness`. -/
example (prog : Program) {n : ℕ} (pSpec : ProtocolSpec n) (μ : ℕ)
    (witnessOf : PublicInput → Column μ → EnsembleWitness (leanIsaEnsemble prog))
    (E : Extractor.Straightline []ₒ PublicInput (Column μ) Unit pSpec) :=
  Extractor.Straightline.map witnessOf E

end Probe
