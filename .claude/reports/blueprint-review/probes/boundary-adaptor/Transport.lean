/-
  Probe (boundary-adaptor): does the chain
    knowledge of `M3Holds`  →  `SatisfiedBy`  →  `ValidExecution`
  typecheck, with the adaptor's target witness in `Type 1`?
  The instance, the witness map and the two theorems not yet built are hypotheses of each
  `example`; nothing here is an axiom. Scratch work for the blueprint review.
  Run from the repository root:
    flock .claude/reports/blueprint-review/logs/lean.lock \
      lake env lean .claude/reports/blueprint-review/probes/boundary-adaptor/Transport.lean
-/
import LeanerVM

open LeanerVM LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization
open LeanerVM.Protocol
open Air.Flat (Ensemble EnsembleWitness Component)

namespace Probe

/-- A stand-in for `leanIsaInstance prog s`: any instance whose statement type is
`PublicInput`. (The toy's tables, no public line.) -/
abbrev stub : M3Instance :=
  { Toy.toy with Stmt := PublicInput, publicLines := fun _ ↦ [] }

/-- The relation of leanISA in ArkLib's shape, over the statement type of `M3Rel`. Its witness
type is in `Type 1`. -/
def SatRel (prog : Program) :
    Set ((PublicInput × (∀ i, NoOracle i)) × EnsembleWitness (leanIsaEnsemble prog)) :=
  {p | SatisfiedBy prog p.1.1 p.2}

/-- 1. The adaptor is a `Refinement`: the structure accepts a target witness in `Type 1`. -/
example (prog : Program) (witnessOf : Column stub.μ → EnsembleWitness (leanIsaEnsemble prog))
    (satisfiedBy_witnessOf :
      ∀ input q, M3Holds stub input q → SatisfiedBy prog input (witnessOf q)) :
    Refinement (M3Rel stub) (SatRel prog) where
  map := fun _ q ↦ witnessOf q
  map_valid := fun x q hx ↦ satisfiedBy_witnessOf x.1 q hx

/-- 2. The polarity ArkLib's game needs. Its bad event is "no witness in the slot is valid"
(an empty slot is bad); `Refinement.map_option_valid` is stated for "every witness in the slot
is valid" (an empty slot is good). The transport of the bad event is this lemma, which follows
from `map_valid` directly. -/
theorem bad_of_bad {Stmt : Type} {W₁ : Type} {W₂ : Type 1} {R : Set (Stmt × W₁)}
    {S : Set (Stmt × W₂)} (f : Refinement R S) (x : Stmt) (w? : Option W₁)
    (h : ∀ w' ∈ w?.map (f.map x), (x, w') ∉ S) : ∀ w ∈ w?, (x, w) ∉ R := by
  intro w hw hR
  exact h (f.map x w) (Option.mem_map_of_mem _ hw) (f.map_valid x w hR)

/-- 3. The composition of the chain, pointwise, in the form the probability bound consumes:
when `prog` has no valid execution on `input`, whatever the extractor returns is outside
`M3Rel`, so the event of ArkLib's knowledge-soundness game is the event "the verifier accepts".
The conclusion of the chain is therefore a soundness statement for the language
`{(prog, input) | ∃ t, ValidExecution prog input t}`. -/
example (prog : Program) (input : PublicInput)
    (witnessOf : Column stub.μ → EnsembleWitness (leanIsaEnsemble prog))
    (satisfiedBy_witnessOf :
      ∀ q, M3Holds stub input q → SatisfiedBy prog input (witnessOf q))
    (constraintSoundness :
      ∀ w, SatisfiedBy prog input w → ∃ t, ValidExecution prog input t)
    (hno : ¬ ∃ t, ValidExecution prog input t) (o : ∀ i, NoOracle i)
    (q? : Option (Column stub.μ)) :
    ∀ q ∈ q?, ((input, o), q) ∉ M3Rel stub := by
  intro q _ hq
  exact hno (constraintSoundness _ (satisfiedBy_witnessOf q hq))

/-- 4. The same with the hypothesis of `constraintSoundness` the leanISA roadmap states
(`WellFormedBytecode prog`, of which soundness uses the sentinel field, built as
`SentinelSafe prog`): the hypothesis reaches the conclusion of the chain. -/
example (prog : Program) (input : PublicInput)
    (witnessOf : Column stub.μ → EnsembleWitness (leanIsaEnsemble prog))
    (satisfiedBy_witnessOf :
      ∀ q, M3Holds stub input q → SatisfiedBy prog input (witnessOf q))
    (constraintSoundness :
      SentinelSafe prog → ∀ w, SatisfiedBy prog input w → ∃ t, ValidExecution prog input t)
    (hwf : SentinelSafe prog)
    (q : Column stub.μ) (h : M3Holds stub input q) : ∃ t, ValidExecution prog input t :=
  constraintSoundness hwf _ (satisfiedBy_witnessOf q h)

end Probe
