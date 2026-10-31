/-
  LeanVM.Guest.Memory.GuestCntWD.Range

  Ranges of the guest's core IR whose static weight certificates the kernel checks.
-/

module

public import LeanVM.Guest.Memory.GuestCntWD.Data
public import LeanVM.Guest.Memory.StaticSplit
public import LeanVM.Guest.CoreData

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

/-- The functions left to hand bounds, by index and name. -/
def kudhandJ : List (ℕ × String) := []

/-- **The check of function `j`**: left to a hand bound, or its callees' indices name them and it
passes against its certificate. -/
noncomputable def kudchkIdx (j : ℕ) : Bool :=
  match coreProgram[j]? with
  | none => true
  | some fn => kudhandJ.any (·.1 == j) ||
      ((kudlnkJ j).all (fun q => decide ((coreProgram[q.2]?).map Fn.name = some q.1)) &&
        chkFn (kudlookJ j) (kudomLookJ j) false (kudcertJ j) (kudomegaJ j) fn)

/-- The `n` functions from the `a`-th pass. -/
def kudStaticRange (a n : ℕ) : Prop := (List.range' a n).all kudchkIdx = true

theorem kudStaticRange.get {a n j : ℕ} (h : kudStaticRange a n) (h1 : a ≤ j) (h2 : j < a + n) :
    kudchkIdx j = true := by
  unfold kudStaticRange at h
  rw [List.all_eq_true] at h
  exact h j (List.mem_range'_1.mpr ⟨h1, h2⟩)

end
end LeanVM.Guest
