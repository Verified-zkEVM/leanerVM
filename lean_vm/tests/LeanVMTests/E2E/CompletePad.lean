import LeanVM.E2E.Complete.GuestModelBig

/-!
# L2 with the memory padded, locked

Statement locks of `LeanVM/E2E/Complete/{PadHonest,HonestBodiesPad,DecodePad,GuestModelBig}.lean`:
the honest memory's zero padding extends it; D3 holds on every extension; the guest's completeness
over every completeness model gives an execution of committed size above `2^21` whose children
decode; each at Lean's three axioms.
-/

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.E2E.Complete LeanVM.Guest.Memory

example {κ κ' : ℕ} (hκ' : κ' < 64) (hle : κ ≤ κ') (L : MemImage κ) : MemExt L (padImage κ' L) :=
  memExt_padImage hκ' hle L

/-- info: 'LeanVM.E2E.Complete.d3HypOExt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms d3HypOExt

example : GuestCompleteModelBig := guestCompleteModel_big

/-- info: 'LeanVM.E2E.Complete.guestCompleteModel_big' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms guestCompleteModel_big
