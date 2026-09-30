/-
  Probe (boundary-adaptor), NEW-PIN VARIANT (CompPoly 572f9973, K.ofBits in place of numerals): the public column of a boundary block is part of the relation, and
  what goes wrong when an instance treats it as committed while the adaptor rebuilds it.
  A model on the spine's toy instance; scratch work for the blueprint review.
  Run from the repository root:
    flock .claude/reports/blueprint-review/logs/lean.lock \
      lake env lean .claude/reports/blueprint-review/probes/boundary-adaptor/KnownColumnNew.lean
-/
import LeanerVM.Protocol.Spine.Toy

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Toy

namespace Probe

/-- The toy instance with the boundary block's public column a parameter: the model of
`leanIsaInstance prog s`, the column `p` standing for the program. -/
abbrev toyOf (p : Column 1) : M3Instance :=
  { toy with
    boundary := [{ κ := 1, side := .pull,
                   coords := Vector.ofFn fun k ↦ if k.val = 0 then .known p else .const 0 }] }

/-- The same instance built wrongly: the block's column is read from the stack (column 1 of the
table), as if the program were committed. -/
abbrev toyCommitted : M3Instance :=
  { toy with
    boundary := [{ κ := 1, side := .pull,
                   coords := Vector.ofFn fun k ↦
                     if k.val = 0 then .committed ⟨0, 1⟩ rfl else .const 0 }] }

/-- The public program of the model. -/
def prog : Column 1 := ⟨#v[1, 1]⟩

/-- Another program. -/
def prog' : Column 1 := ⟨#v[1, K.ofBits 2]⟩

-- 1. The relation is about the program in the instance: the honest stack of `prog` satisfies the
-- relation of `prog`, and not the relation of `prog'`.
#guard M3Holds (toyOf prog) (1 : K) honest
#guard ¬ (toyOf prog').Balanced honest
#guard ¬ M3Holds (toyOf prog') (1 : K) honest

/-- A stack that pushes `[2, 2]` and whose column 1 is `[2, 2]`. -/
def pushesTwo : Column 3 := ⟨#v[K.ofBits 2, K.ofBits 2, K.ofBits 2, K.ofBits 2, 1, 0, 0, 0]⟩

-- 2. The trap. Against the instance that reads the block's column off the stack, the relation
-- holds of a stack that has nothing to do with the public program ...
#guard M3Holds toyCommitted (1 : K) pushesTwo
-- ... while the witness an adaptor would rebuild from it, the table's columns read from the
-- stack and the block's column built from the public program, does not balance.
#guard ¬ (toyOf prog).Balanced pushesTwo
-- The pulled tuples of the two instances on the same stack: the first from the stack, the second
-- from the program.
#guard (toyCommitted.tuples pushesTwo .pull).map (fun t ↦ t.get 0) = [K.ofBits 2, K.ofBits 2]
#guard ((toyOf prog).tuples pushesTwo .pull).map (fun t ↦ t.get 0) = [1, 1]

end Probe
