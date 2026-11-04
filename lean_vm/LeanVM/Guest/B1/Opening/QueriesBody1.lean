/-
  LeanVM.Guest.B1.Opening.QueriesBody1

  The bodies of a quarter of `opening_queries`' specializations and of their loop helpers are the
  templates (kernel evaluation).
-/

module

public import LeanVM.Guest.B1.Opening.QueriesT

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 100000 in
theorem oqBody_533 : Data.core555.body = oqMainT ⟨1, 64, 11, 7⟩ 0 "__loop391" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_859 : Data.core893.body = oqLoop1T ⟨1, 64, 11, 7⟩ 0 "__loop391" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_692 : Data.core714.body = oqMainT ⟨1, 64, 14, 6⟩ 0 "__loop414" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_884 : Data.core932.body = oqLoop1T ⟨1, 64, 14, 6⟩ 0 "__loop414" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_563 : Data.core585.body = oqMainT ⟨1, 64, 14, 7⟩ 0 "__loop395" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_863 : Data.core901.body = oqLoop1T ⟨1, 64, 14, 7⟩ 0 "__loop395" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_721 : Data.core743.body = oqMainT ⟨1, 64, 17, 6⟩ 0 "__loop417" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_887 : Data.core935.body = oqLoop1T ⟨1, 64, 17, 6⟩ 0 "__loop417" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_743 : Data.core765.body = oqMainT ⟨1, 64, 19, 6⟩ 0 "__loop419" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_889 : Data.core938.body = oqLoop1T ⟨1, 64, 19, 6⟩ 0 "__loop419" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_632 : Data.core654.body = oqMainT ⟨1, 64, 14, 7⟩ 1 "__loop406" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_875 : Data.core920.body = oqLoop1T ⟨1, 64, 14, 7⟩ 1 "__loop406" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_515 : Data.core537.body = oqMainT ⟨1, 64, 15, 8⟩ 1 "__loop387" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_855 : Data.core885.body = oqLoop1T ⟨1, 64, 15, 8⟩ 1 "__loop387" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_422 : Data.core444.body = oqMainT ⟨0, 16, 10, 5⟩ 0 "__loop370" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_831 : Data.core851.body = oqLoop0T ⟨0, 16, 10, 5⟩ "__loop370" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_568 : Data.core590.body = oqMainT ⟨0, 16, 13, 4⟩ 0 "__loop396" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_864 : Data.core903.body = oqLoop0T ⟨0, 16, 13, 4⟩ "__loop396" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_474 : Data.core496.body = oqMainT ⟨0, 16, 13, 5⟩ 0 "__loop380" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_845 : Data.core871.body = oqLoop0T ⟨0, 16, 13, 5⟩ "__loop380" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_471 : Data.core493.body = oqMainT ⟨0, 16, 13, 6⟩ 0 "__loop379" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_844 : Data.core869.body = oqLoop0T ⟨0, 16, 13, 6⟩ "__loop379" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_683 : Data.core705.body = oqMainT ⟨0, 16, 17, 4⟩ 0 "__loop413" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_883 : Data.core931.body = oqLoop0T ⟨0, 16, 17, 4⟩ "__loop413" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_602 : Data.core624.body = oqMainT ⟨0, 16, 17, 5⟩ 0 "__loop402" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_871 : Data.core915.body = oqLoop0T ⟨0, 16, 17, 5⟩ "__loop402" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_745 : Data.core767.body = oqMainT ⟨0, 16, 19, 5⟩ 0 "__loop420" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_890 : Data.core940.body = oqLoop0T ⟨0, 16, 19, 5⟩ "__loop420" :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
