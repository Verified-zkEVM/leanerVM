/-
  LeanVM.Guest.Memory.GuestCntWK.Range

  Ranges of the guest's core IR whose static weight certificates the kernel checks.
-/

module

public import LeanVM.Guest.Memory.GuestCntWK.Data
public import LeanVM.Guest.Memory.StaticSplit
public import LeanVM.Guest.CoreData

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

/-- The functions left to hand bounds, by index and name. -/
def kukhandJ : List (ℕ × String) := []

/-- **The check of function `j`**: left to a hand bound, or its callees' indices name them and it
passes against its certificate. -/
noncomputable def kukchkIdx (j : ℕ) : Bool :=
  match coreProgram[j]? with
  | none => true
  | some fn => kukhandJ.any (·.1 == j) ||
      ((kuklnkJ j).all (fun q => decide ((coreProgram[q.2]?).map Fn.name = some q.1)) &&
        chkFn (kuklookJ j) (kukomLookJ j) false (kukcertJ j) (kukomegaJ j) fn)

/-- The `n` functions from the `a`-th pass. -/
def kukStaticRange (a n : ℕ) : Prop := (List.range' a n).all kukchkIdx = true

theorem kukStaticRange.get {a n j : ℕ} (h : kukStaticRange a n) (h1 : a ≤ j) (h2 : j < a + n) :
    kukchkIdx j = true := by
  unfold kukStaticRange at h
  rw [List.all_eq_true] at h
  exact h j (List.mem_range'_1.mpr ⟨h1, h2⟩)

end
end LeanVM.Guest
