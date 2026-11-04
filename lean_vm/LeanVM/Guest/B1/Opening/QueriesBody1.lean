/-
  LeanVM.Guest.B1.Opening.QueriesBody1

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
theorem oqBody_533 : Data.core524.body = oqMainT ⟨1, 64, 11, 7⟩ 0 "__loop387" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_859 : Data.core848.body = oqLoop1T ⟨1, 64, 11, 7⟩ 0 "__loop387" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_692 : Data.core683.body = oqMainT ⟨1, 64, 14, 6⟩ 0 "__loop410" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_884 : Data.core873.body = oqLoop1T ⟨1, 64, 14, 6⟩ 0 "__loop410" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_563 : Data.core554.body = oqMainT ⟨1, 64, 14, 7⟩ 0 "__loop391" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_863 : Data.core852.body = oqLoop1T ⟨1, 64, 14, 7⟩ 0 "__loop391" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_721 : Data.core712.body = oqMainT ⟨1, 64, 17, 6⟩ 0 "__loop413" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_887 : Data.core876.body = oqLoop1T ⟨1, 64, 17, 6⟩ 0 "__loop413" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_743 : Data.core734.body = oqMainT ⟨1, 64, 19, 6⟩ 0 "__loop415" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_889 : Data.core878.body = oqLoop1T ⟨1, 64, 19, 6⟩ 0 "__loop415" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_632 : Data.core623.body = oqMainT ⟨1, 64, 14, 7⟩ 1 "__loop402" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_875 : Data.core864.body = oqLoop1T ⟨1, 64, 14, 7⟩ 1 "__loop402" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_515 : Data.core506.body = oqMainT ⟨1, 64, 15, 8⟩ 1 "__loop383" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_855 : Data.core844.body = oqLoop1T ⟨1, 64, 15, 8⟩ 1 "__loop383" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_422 : Data.core413.body = oqMainT ⟨0, 16, 10, 5⟩ 0 "__loop366" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_831 : Data.core820.body = oqLoop0T ⟨0, 16, 10, 5⟩ "__loop366" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_568 : Data.core559.body = oqMainT ⟨0, 16, 13, 4⟩ 0 "__loop392" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_864 : Data.core853.body = oqLoop0T ⟨0, 16, 13, 4⟩ "__loop392" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_474 : Data.core465.body = oqMainT ⟨0, 16, 13, 5⟩ 0 "__loop376" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_845 : Data.core834.body = oqLoop0T ⟨0, 16, 13, 5⟩ "__loop376" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_471 : Data.core462.body = oqMainT ⟨0, 16, 13, 6⟩ 0 "__loop375" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_844 : Data.core833.body = oqLoop0T ⟨0, 16, 13, 6⟩ "__loop375" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_683 : Data.core674.body = oqMainT ⟨0, 16, 17, 4⟩ 0 "__loop409" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_883 : Data.core872.body = oqLoop0T ⟨0, 16, 17, 4⟩ "__loop409" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_602 : Data.core593.body = oqMainT ⟨0, 16, 17, 5⟩ 0 "__loop398" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_871 : Data.core860.body = oqLoop0T ⟨0, 16, 17, 5⟩ "__loop398" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_745 : Data.core736.body = oqMainT ⟨0, 16, 19, 5⟩ 0 "__loop416" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_890 : Data.core879.body = oqLoop0T ⟨0, 16, 19, 5⟩ "__loop416" :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
