/-
  LeanVM.E2E.Complete.DecodeFrames

  The frames V_I's decoder is named: a call's frame, by its callee and argument words, that of a
  designated honest instance with those words.
-/

module

public import LeanVM.E2E.Complete.DecodeSplit
public import LeanVM.Guest.B2C.Cells

/-!
# Naming the frames

`DecodeHonest fr t w` decodes the children at the frames `fr` (`Frames`: a callee name and argument
words to a frame pointer). Here `frOf Is` names, for a call, the frame of an instance of `Is` (the
designated honest instances) with the callee's name and those argument words (`instArgs`: its
parameters' values), when there is one: `frOf_eq`, when the designated instances with a name and
argument words share their frame.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- An instance's argument words: its function's parameters' values. -/
noncomputable def instArgs (I : Inst) : List E :=
  match B2C.idxOf I.t.name with
  | some j => (coreOf j).params.map I.t.val
  | none => []

open Classical in
/-- **The frames of the designated instances `Is`**: a call's frame is that of an instance of `Is`
with the callee's name and the call's argument words, if any. -/
noncomputable def frOf (Is : Inst → Prop) : Frames := fun f args =>
  if h : ∃ I, Is I ∧ I.t.name = f ∧ instArgs I = args then some (Classical.choose h).fp else none

/-- **A designated instance's frame is named**, when the designated instances with its name and
argument words share its frame. -/
theorem frOf_eq {Is : Inst → Prop} {I : Inst} (hI : Is I)
    (huniq : ∀ I', Is I' → I'.t.name = I.t.name → instArgs I' = instArgs I → I'.fp = I.fp) :
    frOf Is I.t.name (instArgs I) = some I.fp := by
  classical
  have h : ∃ I', Is I' ∧ I'.t.name = I.t.name ∧ instArgs I' = instArgs I := ⟨I, hI, rfl, rfl⟩
  unfold frOf
  split
  · rename_i h'
    obtain ⟨h1, h2, h3⟩ := Classical.choose_spec h'
    rw [huniq _ h1 h2 h3]
  · rename_i h'
    exact absurd h h'

end
end LeanVM.E2E.Complete
