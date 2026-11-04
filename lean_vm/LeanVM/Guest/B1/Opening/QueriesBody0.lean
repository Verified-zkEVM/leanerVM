/-
  LeanVM.Guest.B1.Opening.QueriesBody0

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
theorem oqBody_413 : Data.core403.body = oqMainT ⟨1, 64, 9, 8⟩ 0 "__loop364" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_827 : Data.core815.body = oqLoop1T ⟨1, 64, 9, 8⟩ 0 "__loop364" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_449 : Data.core439.body = oqMainT ⟨1, 64, 11, 8⟩ 0 "__loop371" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_839 : Data.core827.body = oqLoop1T ⟨1, 64, 11, 8⟩ 0 "__loop371" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_701 : Data.core691.body = oqMainT ⟨1, 64, 15, 6⟩ 0 "__loop411" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_885 : Data.core873.body = oqLoop1T ⟨1, 64, 15, 6⟩ 0 "__loop411" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_575 : Data.core565.body = oqMainT ⟨1, 64, 15, 7⟩ 0 "__loop393" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_865 : Data.core853.body = oqLoop1T ⟨1, 64, 15, 7⟩ 0 "__loop393" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_598 : Data.core588.body = oqMainT ⟨1, 64, 17, 7⟩ 0 "__loop396" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_869 : Data.core857.body = oqLoop1T ⟨1, 64, 17, 7⟩ 0 "__loop396" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_623 : Data.core613.body = oqMainT ⟨1, 64, 13, 7⟩ 1 "__loop401" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_874 : Data.core862.body = oqLoop1T ⟨1, 64, 13, 7⟩ 1 "__loop401" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_654 : Data.core644.body = oqMainT ⟨1, 64, 16, 7⟩ 1 "__loop404" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_877 : Data.core865.body = oqLoop1T ⟨1, 64, 16, 7⟩ 1 "__loop404" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_425 : Data.core415.body = oqMainT ⟨0, 16, 9, 5⟩ 0 "__loop367" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_833 : Data.core821.body = oqLoop0T ⟨0, 16, 9, 5⟩ "__loop367" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_418 : Data.core408.body = oqMainT ⟨0, 16, 10, 6⟩ 0 "__loop365" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_829 : Data.core817.body = oqLoop0T ⟨0, 16, 10, 6⟩ "__loop365" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_524 : Data.core514.body = oqMainT ⟨0, 16, 14, 4⟩ 0 "__loop386" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_858 : Data.core846.body = oqLoop0T ⟨0, 16, 14, 4⟩ "__loop386" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_491 : Data.core481.body = oqMainT ⟨0, 16, 14, 5⟩ 0 "__loop379" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_849 : Data.core837.body = oqLoop0T ⟨0, 16, 14, 5⟩ "__loop379" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_489 : Data.core479.body = oqMainT ⟨0, 16, 14, 6⟩ 0 "__loop378" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_848 : Data.core836.body = oqLoop0T ⟨0, 16, 14, 6⟩ "__loop378" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_761 : Data.core751.body = oqMainT ⟨0, 16, 18, 4⟩ 0 "__loop419" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_894 : Data.core882.body = oqLoop0T ⟨0, 16, 18, 4⟩ "__loop419" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_600 : Data.core590.body = oqMainT ⟨0, 16, 17, 6⟩ 0 "__loop397" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_870 : Data.core858.body = oqLoop0T ⟨0, 16, 17, 6⟩ "__loop397" :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
