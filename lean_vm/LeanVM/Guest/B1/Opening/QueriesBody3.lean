/-
  LeanVM.Guest.B1.Opening.QueriesBody3

  The bodies of a quarter of `opening_queries`' specializations and of their loop helpers are the
  templates (kernel evaluation), and so they are their meaning.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesComplete6

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 100000 in
theorem oqBody_542 : Data.core521.body = oqMainT ⟨1, 64, 12, 7⟩ 0 "__loop383" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_860 : Data.core839.body = oqLoop1T ⟨1, 64, 12, 7⟩ 0 "__loop383" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_468 : Data.core447.body = oqMainT ⟨1, 64, 12, 8⟩ 0 "__loop369" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_843 : Data.core822.body = oqLoop1T ⟨1, 64, 12, 8⟩ 0 "__loop369" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_710 : Data.core689.body = oqMainT ⟨1, 64, 16, 6⟩ 0 "__loop407" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_886 : Data.core865.body = oqLoop1T ⟨1, 64, 16, 6⟩ 0 "__loop407" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_732 : Data.core711.body = oqMainT ⟨1, 64, 18, 6⟩ 0 "__loop409" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_888 : Data.core867.body = oqLoop1T ⟨1, 64, 18, 6⟩ 0 "__loop409" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_614 : Data.core593.body = oqMainT ⟨1, 64, 12, 7⟩ 1 "__loop395" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_873 : Data.core852.body = oqLoop1T ⟨1, 64, 12, 7⟩ 1 "__loop395" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_501 : Data.core480.body = oqMainT ⟨1, 64, 14, 8⟩ 1 "__loop375" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_851 : Data.core830.body = oqLoop1T ⟨1, 64, 14, 8⟩ 1 "__loop375" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_676 : Data.core655.body = oqMainT ⟨1, 64, 18, 7⟩ 1 "__loop401" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_880 : Data.core859.body = oqLoop1T ⟨1, 64, 18, 7⟩ 1 "__loop401" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_439 : Data.core418.body = oqMainT ⟨0, 16, 11, 5⟩ 0 "__loop365" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_837 : Data.core816.body = oqLoop0T ⟨0, 16, 11, 5⟩ "__loop365" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_436 : Data.core415.body = oqMainT ⟨0, 16, 11, 6⟩ 0 "__loop364" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_836 : Data.core815.body = oqLoop0T ⟨0, 16, 11, 6⟩ "__loop364" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_591 : Data.core570.body = oqMainT ⟨0, 16, 15, 4⟩ 0 "__loop390" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_867 : Data.core846.body = oqLoop0T ⟨0, 16, 15, 4⟩ "__loop390" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_505 : Data.core484.body = oqMainT ⟨0, 16, 15, 5⟩ 0 "__loop377" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_853 : Data.core832.body = oqLoop0T ⟨0, 16, 15, 5⟩ "__loop377" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_503 : Data.core482.body = oqMainT ⟨0, 16, 15, 6⟩ 0 "__loop376" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_852 : Data.core831.body = oqLoop0T ⟨0, 16, 15, 6⟩ "__loop376" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_680 : Data.core659.body = oqMainT ⟨0, 16, 18, 5⟩ 0 "__loop403" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_882 : Data.core861.body = oqLoop0T ⟨0, 16, 18, 5⟩ "__loop403" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_757 : Data.core736.body = oqMainT ⟨0, 16, 20, 5⟩ 0 "__loop413" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_893 : Data.core872.body = oqLoop0T ⟨0, 16, 20, 5⟩ "__loop413" :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
