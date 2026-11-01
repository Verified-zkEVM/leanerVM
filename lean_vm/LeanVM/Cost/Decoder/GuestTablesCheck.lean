module

public import LeanVM.Cost.Decoder.GuestTables
public import LeanVM.Guest.Glob
import all LeanVM.Guest.Glob

/-!
# The guest decoder's tables, checked

The literal tables of `GuestTables.lean` are the guest's, by kernel evaluation: for every
function `j < nFns`, its entry pc, its numbers of arguments and of return words
(`(glob.sig j).entry`, `nargs`, `nret`), and its certificate's frame cells (`(certOf j).locs`).
A module of its own: the evaluation reads the guest's compiled code and certificates.
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Guest

@[expose] public section

theorem guestEntries_eq : ∀ j < nFns, guestEntries.getD j 0 = (glob.sig j).entry := by
  decide +kernel

theorem guestArgCounts_eq : ∀ j < nFns, guestArgCounts.getD j 0 = (glob.sig j).nargs := by
  decide +kernel

theorem guestRetCounts_eq : ∀ j < nFns, guestRetCounts.getD j 0 = (glob.sig j).nret := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- The cells' lists are the certificates', function by function, by unfolding: no list is
evaluated, the certificates' cells being the same constants. -/
theorem guestLocsList_eq : ∀ j < nFns, guestLocsList.getD j [] = (certOf j).locs := by
  intro j hj
  unfold nFns at hj
  interval_cases j <;> rfl

set_option maxRecDepth 100000 in
theorem guestLocsList_length : guestLocsList.length = nFns := by decide +kernel

set_option maxRecDepth 100000 in
theorem guestLocs_eq {j : ℕ} (hj : j < nFns) : (guestLocs.getD j #[]).toList = (certOf j).locs := by
  rw [← guestLocsList_eq j hj, guestLocs]
  have hl : j < guestLocsList.length := guestLocsList_length ▸ hj
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, hl]

end

end LeanVM.Cost.Decoder
