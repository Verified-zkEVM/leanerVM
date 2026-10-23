/-
  LeanVM.Guest.B1.Digest.ListsChk

  `da_hash_roots__L{n}`, evaluated: its values defined in order, no store, its `KECCAK` inputs
  canonical from the loaded cells, its only side conditions its loads (by kernel evaluation).
-/

module

public import LeanVM.Guest.B1.Digest.Lists
public import LeanVM.Guest.B1.Fwd.Canon

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- The load of message cell `off < 4n` through the argument. -/
def isLoadHR (n : ℕ) : Atom → Bool
  | .load d p off => decide (p = .n 0) && decide (d = .n (off + 1)) && decide (off < 4 * n)
  | _ => false

/-- `da_hash_roots__L{n}` evaluates: in order, no store, canonical inputs, side conditions in
its loads. -/
def hrcOk (n : ℕ) (f : Fn) : Bool :=
  (chk 1 f.body).isSome && (storesOf 1 f.body).isEmpty &&
  match splitBody f.body with
  | some (atoms, _) => canonChk ((List.range (4 * n)).map (· + 1)) atoms &&
      atoms.all (fun a => !needsSide a || isLoadHR n a)
  | none => false

set_option maxRecDepth 100000 in
theorem hrc_all : ∀ n < 17, hrcOk n (coreProgram.getD (377 + n) default) = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Digest
