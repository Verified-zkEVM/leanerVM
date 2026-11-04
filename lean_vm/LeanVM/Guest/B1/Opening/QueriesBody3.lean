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
theorem oqBody_542 : Data.core564.body = oqMainT ⟨1, 64, 12, 7⟩ 0 "__loop392" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_860 : Data.core895.body = oqLoop1T ⟨1, 64, 12, 7⟩ 0 "__loop392" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_468 : Data.core490.body = oqMainT ⟨1, 64, 12, 8⟩ 0 "__loop378" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_843 : Data.core867.body = oqLoop1T ⟨1, 64, 12, 8⟩ 0 "__loop378" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_710 : Data.core732.body = oqMainT ⟨1, 64, 16, 6⟩ 0 "__loop416" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_886 : Data.core934.body = oqLoop1T ⟨1, 64, 16, 6⟩ 0 "__loop416" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_732 : Data.core754.body = oqMainT ⟨1, 64, 18, 6⟩ 0 "__loop418" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_888 : Data.core936.body = oqLoop1T ⟨1, 64, 18, 6⟩ 0 "__loop418" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_614 : Data.core636.body = oqMainT ⟨1, 64, 12, 7⟩ 1 "__loop404" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_873 : Data.core918.body = oqLoop1T ⟨1, 64, 12, 7⟩ 1 "__loop404" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_501 : Data.core523.body = oqMainT ⟨1, 64, 14, 8⟩ 1 "__loop384" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_851 : Data.core879.body = oqLoop1T ⟨1, 64, 14, 8⟩ 1 "__loop384" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_676 : Data.core698.body = oqMainT ⟨1, 64, 18, 7⟩ 1 "__loop410" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_880 : Data.core925.body = oqLoop1T ⟨1, 64, 18, 7⟩ 1 "__loop410" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_439 : Data.core461.body = oqMainT ⟨0, 16, 11, 5⟩ 0 "__loop374" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_837 : Data.core859.body = oqLoop0T ⟨0, 16, 11, 5⟩ "__loop374" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_436 : Data.core458.body = oqMainT ⟨0, 16, 11, 6⟩ 0 "__loop373" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_836 : Data.core857.body = oqLoop0T ⟨0, 16, 11, 6⟩ "__loop373" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_591 : Data.core613.body = oqMainT ⟨0, 16, 15, 4⟩ 0 "__loop399" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_867 : Data.core909.body = oqLoop0T ⟨0, 16, 15, 4⟩ "__loop399" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_505 : Data.core527.body = oqMainT ⟨0, 16, 15, 5⟩ 0 "__loop386" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_853 : Data.core883.body = oqLoop0T ⟨0, 16, 15, 5⟩ "__loop386" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_503 : Data.core525.body = oqMainT ⟨0, 16, 15, 6⟩ 0 "__loop385" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_852 : Data.core881.body = oqLoop0T ⟨0, 16, 15, 6⟩ "__loop385" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_680 : Data.core702.body = oqMainT ⟨0, 16, 18, 5⟩ 0 "__loop412" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_882 : Data.core929.body = oqLoop0T ⟨0, 16, 18, 5⟩ "__loop412" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_757 : Data.core779.body = oqMainT ⟨0, 16, 20, 5⟩ 0 "__loop422" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_893 : Data.core944.body = oqLoop0T ⟨0, 16, 20, 5⟩ "__loop422" :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
