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
theorem oqBody_533 : Data.core523.body = oqMainT ⟨1, 64, 11, 7⟩ 0 "__loop382" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_859 : Data.core847.body = oqLoop1T ⟨1, 64, 11, 7⟩ 0 "__loop382" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_692 : Data.core682.body = oqMainT ⟨1, 64, 14, 6⟩ 0 "__loop405" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_884 : Data.core872.body = oqLoop1T ⟨1, 64, 14, 6⟩ 0 "__loop405" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_563 : Data.core553.body = oqMainT ⟨1, 64, 14, 7⟩ 0 "__loop386" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_863 : Data.core851.body = oqLoop1T ⟨1, 64, 14, 7⟩ 0 "__loop386" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_721 : Data.core711.body = oqMainT ⟨1, 64, 17, 6⟩ 0 "__loop408" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_887 : Data.core875.body = oqLoop1T ⟨1, 64, 17, 6⟩ 0 "__loop408" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_743 : Data.core733.body = oqMainT ⟨1, 64, 19, 6⟩ 0 "__loop410" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_889 : Data.core877.body = oqLoop1T ⟨1, 64, 19, 6⟩ 0 "__loop410" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_632 : Data.core622.body = oqMainT ⟨1, 64, 14, 7⟩ 1 "__loop397" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_875 : Data.core863.body = oqLoop1T ⟨1, 64, 14, 7⟩ 1 "__loop397" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_515 : Data.core505.body = oqMainT ⟨1, 64, 15, 8⟩ 1 "__loop378" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_855 : Data.core843.body = oqLoop1T ⟨1, 64, 15, 8⟩ 1 "__loop378" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_422 : Data.core412.body = oqMainT ⟨0, 16, 10, 5⟩ 0 "__loop361" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_831 : Data.core819.body = oqLoop0T ⟨0, 16, 10, 5⟩ "__loop361" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_568 : Data.core558.body = oqMainT ⟨0, 16, 13, 4⟩ 0 "__loop387" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_864 : Data.core852.body = oqLoop0T ⟨0, 16, 13, 4⟩ "__loop387" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_474 : Data.core464.body = oqMainT ⟨0, 16, 13, 5⟩ 0 "__loop371" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_845 : Data.core833.body = oqLoop0T ⟨0, 16, 13, 5⟩ "__loop371" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_471 : Data.core461.body = oqMainT ⟨0, 16, 13, 6⟩ 0 "__loop370" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_844 : Data.core832.body = oqLoop0T ⟨0, 16, 13, 6⟩ "__loop370" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_683 : Data.core673.body = oqMainT ⟨0, 16, 17, 4⟩ 0 "__loop404" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_883 : Data.core871.body = oqLoop0T ⟨0, 16, 17, 4⟩ "__loop404" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_602 : Data.core592.body = oqMainT ⟨0, 16, 17, 5⟩ 0 "__loop393" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_871 : Data.core859.body = oqLoop0T ⟨0, 16, 17, 5⟩ "__loop393" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_745 : Data.core735.body = oqMainT ⟨0, 16, 19, 5⟩ 0 "__loop411" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_890 : Data.core878.body = oqLoop0T ⟨0, 16, 19, 5⟩ "__loop411" :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
