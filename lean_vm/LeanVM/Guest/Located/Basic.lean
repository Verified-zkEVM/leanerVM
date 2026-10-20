/-
  LeanVM.Guest.Located.Basic

  Frames of the memory and the first one passing a test.
-/

module

public import LeanVM.Guest.CertName

/-!
# Frames, scanned

A located call runs at a frame `g^a` of the memory, `a < 2^κ` (`Check.InMem`), under its
certificate's valuation there (`valAt`). A witness is read off the first frame passing a Boolean
test (`firstFrame`): an explicit function of the memory, found by a scan as long as the memory.
-/

namespace LeanVM.Guest.Located

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Check

@[expose] public section

/-- The valuation of the guest function `f` with the memory's word `a` as its frame. -/
noncomputable def valAt {κ : ℕ} (L : MemImage κ) (f : String) (a : ℕ) : Val :=
  frameVal L certByName f (gpow a)

/-- The first frame `a < 2^κ` passing the test `t`. -/
def firstFrame (κ : ℕ) (t : ℕ → Bool) : Option ℕ := (List.range (2 ^ κ)).find? t

/-- A frame passing the test makes the scan find one. -/
theorem firstFrame_some {κ : ℕ} {t : ℕ → Bool} {a : ℕ} (ha : a < 2 ^ κ) (h : t a = true) :
    ∃ b, firstFrame κ t = some b ∧ t b = true := by
  unfold firstFrame
  rcases hf : (List.range (2 ^ κ)).find? t with _ | b
  · exact absurd h (by simpa using List.find?_eq_none.mp hf a (List.mem_range.mpr ha))
  · exact ⟨b, rfl, List.find?_some hf⟩

end
end LeanVM.Guest.Located
