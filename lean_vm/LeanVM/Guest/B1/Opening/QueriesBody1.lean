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
theorem oqBody_533 : Data.core512.body = oqMainT ⟨1, 64, 11, 7⟩ 0 "__loop382" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_859 : Data.core838.body = oqLoop1T ⟨1, 64, 11, 7⟩ 0 "__loop382" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_692 : Data.core671.body = oqMainT ⟨1, 64, 14, 6⟩ 0 "__loop405" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_884 : Data.core863.body = oqLoop1T ⟨1, 64, 14, 6⟩ 0 "__loop405" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_563 : Data.core542.body = oqMainT ⟨1, 64, 14, 7⟩ 0 "__loop386" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_863 : Data.core842.body = oqLoop1T ⟨1, 64, 14, 7⟩ 0 "__loop386" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_721 : Data.core700.body = oqMainT ⟨1, 64, 17, 6⟩ 0 "__loop408" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_887 : Data.core866.body = oqLoop1T ⟨1, 64, 17, 6⟩ 0 "__loop408" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_743 : Data.core722.body = oqMainT ⟨1, 64, 19, 6⟩ 0 "__loop410" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_889 : Data.core868.body = oqLoop1T ⟨1, 64, 19, 6⟩ 0 "__loop410" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_632 : Data.core611.body = oqMainT ⟨1, 64, 14, 7⟩ 1 "__loop397" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_875 : Data.core854.body = oqLoop1T ⟨1, 64, 14, 7⟩ 1 "__loop397" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_515 : Data.core494.body = oqMainT ⟨1, 64, 15, 8⟩ 1 "__loop378" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_855 : Data.core834.body = oqLoop1T ⟨1, 64, 15, 8⟩ 1 "__loop378" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_422 : Data.core401.body = oqMainT ⟨0, 16, 10, 5⟩ 0 "__loop361" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_831 : Data.core810.body = oqLoop0T ⟨0, 16, 10, 5⟩ "__loop361" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_568 : Data.core547.body = oqMainT ⟨0, 16, 13, 4⟩ 0 "__loop387" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_864 : Data.core843.body = oqLoop0T ⟨0, 16, 13, 4⟩ "__loop387" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_474 : Data.core453.body = oqMainT ⟨0, 16, 13, 5⟩ 0 "__loop371" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_845 : Data.core824.body = oqLoop0T ⟨0, 16, 13, 5⟩ "__loop371" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_471 : Data.core450.body = oqMainT ⟨0, 16, 13, 6⟩ 0 "__loop370" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_844 : Data.core823.body = oqLoop0T ⟨0, 16, 13, 6⟩ "__loop370" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_683 : Data.core662.body = oqMainT ⟨0, 16, 17, 4⟩ 0 "__loop404" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_883 : Data.core862.body = oqLoop0T ⟨0, 16, 17, 4⟩ "__loop404" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_602 : Data.core581.body = oqMainT ⟨0, 16, 17, 5⟩ 0 "__loop393" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_871 : Data.core850.body = oqLoop0T ⟨0, 16, 17, 5⟩ "__loop393" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_745 : Data.core724.body = oqMainT ⟨0, 16, 19, 5⟩ 0 "__loop411" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_890 : Data.core869.body = oqLoop0T ⟨0, 16, 19, 5⟩ "__loop411" :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
