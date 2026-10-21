/-
  LeanVM.Guest.B1.Main.RestrictS

  `Restrict.lean` under any semantics of `BLAKE2S` (`S : BlakeSem`).
-/

module

public import LeanVM.Guest.B1.Main.Restrict
public import LeanVM.Guest.Memory.RestrictB
public import LeanVM.Guest.Memory.RegionsB

/-!
# `Restrict.lean` under any `BLAKE2S` semantics

Each definition and lemma of `Restrict.lean` that mentions the semantics, with `S : BlakeSem` a
parameter and a `S` in its name.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

variable {S : BlakeSem}

export LeanVM.Guest.Memory (restrict restrict_supp restrict_of loadHolds_restrict loads_of_supp
  loadsR_of_supp loadsRKids_of_supp relIn_of_rel_supp restrict_supp' atomEqns_read_pure eqns_read_pure
  eqnsKids_read_pure relAtIn_uniform_of_supp)

end
end LeanVM.Guest.B1.Main
