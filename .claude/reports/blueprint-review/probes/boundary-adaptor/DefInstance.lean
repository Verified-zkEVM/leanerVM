/-
  Probe (boundary-adaptor): does the adaptor's statement typecheck when the instance is a `def`
  (not an `abbrev`), and is its relation still decided by evaluation?
  The two `#guard`s on the `def` instance are EXPECTED TO FAIL (no `Decidable` instance is
  found); the same guards on the `abbrev` instance pass.
  Scratch work for the blueprint review.
  Run from the repository root:
    flock .claude/reports/blueprint-review/logs/lean.lock \
      lake env lean .claude/reports/blueprint-review/probes/boundary-adaptor/DefInstance.lean
-/
import LeanerVM.Protocol.Spine.Toy
import LeanerVM.Semantics.Instruction

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Protocol LeanerVM.Protocol.Toy

namespace Probe

/-- A stand-in for `leanIsaInstance prog s`, as a `def` with parameters: the statement type is
`PublicInput`, and the one public line reads lane 0 of the input. -/
def inst (_prog : Program) (_s : ℕ) : M3Instance :=
  { toy with
    Stmt := PublicInput
    publicLines := fun input ↦ [⟨⟨0, 2⟩, input.lanes 0, 0, true, by decide⟩] }

/-- The same, as an `abbrev`. -/
abbrev instA (_prog : Program) (_s : ℕ) : M3Instance :=
  { toy with
    Stmt := PublicInput
    publicLines := fun input ↦ [⟨⟨0, 2⟩, input.lanes 0, 0, true, by decide⟩] }

/-- The statement of `satisfiedBy_witnessOf`'s hypothesis elaborates with `input : PublicInput`
on the `def`: the elaborator unfolds it to see the statement type. -/
example (prog : Program) (s : ℕ) (input : PublicInput) (q : Column (inst prog s).μ) : Prop :=
  M3Holds (inst prog s) input q

/-- A program and an input for the evaluation below. -/
def prog0 : Program := ⟨0, by decide, fun _ ↦ .xor 1 1 1⟩
def input1 : PublicInput := ⟨fun _ ↦ 1⟩
def input0 : PublicInput := ⟨fun _ ↦ 0⟩

-- On the `abbrev`, the relation is decided by evaluation, as the toy's is.
#guard M3Holds (instA prog0 0) input1 honest
#guard ¬ M3Holds (instA prog0 0) input0 honest

-- On the `def`, instance search does not see through the definition (EXPECTED TO FAIL).
#guard M3Holds (inst prog0 0) input1 honest
#guard ¬ M3Holds (inst prog0 0) input0 honest

end Probe
