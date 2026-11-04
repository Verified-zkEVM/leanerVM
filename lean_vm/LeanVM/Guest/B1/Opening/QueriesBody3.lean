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
theorem oqBody_542 : Data.core533.body = oqMainT ⟨1, 64, 12, 7⟩ 0 "__loop388" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_860 : Data.core849.body = oqLoop1T ⟨1, 64, 12, 7⟩ 0 "__loop388" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_468 : Data.core459.body = oqMainT ⟨1, 64, 12, 8⟩ 0 "__loop374" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_843 : Data.core832.body = oqLoop1T ⟨1, 64, 12, 8⟩ 0 "__loop374" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_710 : Data.core701.body = oqMainT ⟨1, 64, 16, 6⟩ 0 "__loop412" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_886 : Data.core875.body = oqLoop1T ⟨1, 64, 16, 6⟩ 0 "__loop412" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_732 : Data.core723.body = oqMainT ⟨1, 64, 18, 6⟩ 0 "__loop414" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_888 : Data.core877.body = oqLoop1T ⟨1, 64, 18, 6⟩ 0 "__loop414" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_614 : Data.core605.body = oqMainT ⟨1, 64, 12, 7⟩ 1 "__loop400" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_873 : Data.core862.body = oqLoop1T ⟨1, 64, 12, 7⟩ 1 "__loop400" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_501 : Data.core492.body = oqMainT ⟨1, 64, 14, 8⟩ 1 "__loop380" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_851 : Data.core840.body = oqLoop1T ⟨1, 64, 14, 8⟩ 1 "__loop380" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_676 : Data.core667.body = oqMainT ⟨1, 64, 18, 7⟩ 1 "__loop406" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_880 : Data.core869.body = oqLoop1T ⟨1, 64, 18, 7⟩ 1 "__loop406" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_439 : Data.core430.body = oqMainT ⟨0, 16, 11, 5⟩ 0 "__loop370" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_837 : Data.core826.body = oqLoop0T ⟨0, 16, 11, 5⟩ "__loop370" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_436 : Data.core427.body = oqMainT ⟨0, 16, 11, 6⟩ 0 "__loop369" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_836 : Data.core825.body = oqLoop0T ⟨0, 16, 11, 6⟩ "__loop369" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_591 : Data.core582.body = oqMainT ⟨0, 16, 15, 4⟩ 0 "__loop395" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_867 : Data.core856.body = oqLoop0T ⟨0, 16, 15, 4⟩ "__loop395" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_505 : Data.core496.body = oqMainT ⟨0, 16, 15, 5⟩ 0 "__loop382" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_853 : Data.core842.body = oqLoop0T ⟨0, 16, 15, 5⟩ "__loop382" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_503 : Data.core494.body = oqMainT ⟨0, 16, 15, 6⟩ 0 "__loop381" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_852 : Data.core841.body = oqLoop0T ⟨0, 16, 15, 6⟩ "__loop381" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_680 : Data.core671.body = oqMainT ⟨0, 16, 18, 5⟩ 0 "__loop408" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_882 : Data.core871.body = oqLoop0T ⟨0, 16, 18, 5⟩ "__loop408" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_757 : Data.core748.body = oqMainT ⟨0, 16, 20, 5⟩ 0 "__loop418" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_893 : Data.core882.body = oqLoop0T ⟨0, 16, 20, 5⟩ "__loop418" :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
