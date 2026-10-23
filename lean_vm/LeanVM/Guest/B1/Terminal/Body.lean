/-
  LeanVM.Guest.B1.Terminal.Body

  `check_opening_terminal`'s body is the template `termT`, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Terminal.Template

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Guest.Core LeanVM.Guest.B1

@[expose] public section

theorem term_body : Data.core17.body = termT := stmtsEqb_sound (by decide +kernel)

theorem find_term : coreProgram.find? "check_opening_terminal" = some Data.core17 :=
  Program.find?_of_indexOf? (j := 17) (by decide +kernel) rfl

/-- The template's claims end at value `1836`, the sum at `1835`. -/
theorem claimsT_end : (claimsT (List.range 165) 375 16).2 = (1836, 1835) := by decide +kernel

end
end LeanVM.Guest.B1.VerifySub
