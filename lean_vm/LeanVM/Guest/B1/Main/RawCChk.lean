/-
  LeanVM.Guest.B1.Main.RawCChk

  `main`'s raw-signature loops `__loop3`, `__loop4` as statement lists (by kernel evaluation), and
  the pure sets they call into, for their placed completeness.
-/

module

public import LeanVM.Guest.B1.Main.Loops
public import LeanVM.Guest.Memory.LiftPure
public import LeanVM.Guest.B1.Sig.Interface

/-!
# The raw-signature loops' bodies

`l3Pre`, `l4Pre`: the loops' statements before their `ret []` (`l3_body`, `l4_body`), their
parameters `.n 0 …` (`l3_params`, `l4_params`); `l3_find`, `l4_find`; `raw3_pure`, `raw4_pure`:
each loop with its signature verifier places nothing (kernel evaluation).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Digest

@[expose] public section

/-- `__loop3`'s statements before its `ret []`. -/
def l3Pre : List Stmt :=
  [.atom (.hint (.witness "raw_index" (.stack [.n 5]))),
    .atom (.const (.n 6) (word 9223372036854775821 0 0)), .atom (.mul (.n 7) (.n 2) (.n 6)),
    .atom (.rangeCheck (.n 5) (.n 8) (.n 9) (.n 10) (.n 7)), .atom (.mul (.n 11) (.n 3) (.n 5)),
    .atom (.load (.n 0) (.n 11) 0), .atom (.mul (.n 12) (.n 5) (.n 5)),
    .atom (.mul (.n 13) (.n 12) (.n 12)), .atom (.mul (.n 14) (.n 4) (.n 13)),
    .call "verify_lean_xmss" [.n 14] [], .atom (.const (.n 15) (word 2 0 0)),
    .atom (.mul (.n 16) (.n 0) (.n 15)), .atom (.add (.n 17) (.n 16) (.n 1)),
    .atom (.const (.n 18) (word 2 0 0)), .atom (.mul (.n 19) (.n 0) (.n 18)),
    .callIf (.n 17) "__loop3" [.n 19, .n 1, .n 2, .n 3, .n 4]]

/-- `__loop4`'s statements before its `ret []`. -/
def l4Pre : List Stmt :=
  [.atom (.hint (.witness "sp_raw_index" (.stack [.n 8]))),
    .atom (.const (.n 9) (word 9223372036854775821 0 0)), .atom (.mul (.n 10) (.n 2) (.n 9)),
    .atom (.rangeCheck (.n 8) (.n 11) (.n 12) (.n 13) (.n 10)), .atom (.mul (.n 14) (.n 5) (.n 0)),
    .atom (.mul (.n 15) (.n 4) (.n 8)), .atom (.mul (.n 16) (.n 3) (.n 15)),
    .atom (.load (.n 14) (.n 16) 0), .atom (.mul (.n 17) (.n 8) (.n 8)),
    .atom (.mul (.n 18) (.n 17) (.n 17)), .atom (.mul (.n 19) (.n 6) (.n 18)),
    .call "verify_sig_lean_sphincs" [.n 19, .n 7] [], .atom (.const (.n 20) (word 2 0 0)),
    .atom (.mul (.n 21) (.n 0) (.n 20)), .atom (.add (.n 22) (.n 21) (.n 1)),
    .atom (.const (.n 23) (word 2 0 0)), .atom (.mul (.n 24) (.n 0) (.n 23)),
    .callIf (.n 22) "__loop4" [.n 24, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7]]

set_option maxRecDepth 100000 in
theorem l3_body : Fn.body (coreProgram.getD 35 default) = l3Pre ++ [.ret []] :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem l4_body : Fn.body (coreProgram.getD 36 default) = l4Pre ++ [.ret []] :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem l3_params : (coreProgram.getD 35 default).params = [.n 0, .n 1, .n 2, .n 3, .n 4] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem l4_params : (coreProgram.getD 36 default).params =
    [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem l4_idx' : coreProgram.indexOf? "__loop4" = some 36 := by decide +kernel

theorem l3_find : coreProgram.find? "__loop3" = some (coreProgram.getD 35 default) :=
  find_of_idx l3_idx (by rw [coreProgram_length]; omega)

theorem l4_find : coreProgram.find? "__loop4" = some (coreProgram.getD 36 default) :=
  find_of_idx l4_idx' (by rw [coreProgram_length]; omega)

/-- Every member's body places nothing and calls members only. -/
noncomputable def pureOk (S : List String) : Bool :=
  S.all fun g => match coreProgram.find? g with
    | some fn => Stmt.pureList S fn.body
    | none => true

theorem pureIn_of_ok {S : List String} (h : pureOk S = true) : coreProgram.PureIn S := by
  intro g hg fn hf
  have h := List.all_eq_true.mp h g hg
  rw [hf] at h
  exact h

set_option maxRecDepth 100000 in
theorem raw3_pure : coreProgram.PureIn ["__loop3", "verify_lean_xmss"] :=
  pureIn_of_ok (by decide +kernel)

set_option maxRecDepth 100000 in
theorem raw4_pure : coreProgram.PureIn ["__loop4", "verify_sig_lean_sphincs"] :=
  pureIn_of_ok (by decide +kernel)

end
end LeanVM.Guest.B1.Main
