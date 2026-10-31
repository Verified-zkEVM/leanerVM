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
theorem oqBody_413 : Data.core392.body = oqMainT ⟨1, 64, 9, 8⟩ 0 "__loop359" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_827 : Data.core806.body = oqLoop1T ⟨1, 64, 9, 8⟩ 0 "__loop359" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_449 : Data.core428.body = oqMainT ⟨1, 64, 11, 8⟩ 0 "__loop366" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_839 : Data.core818.body = oqLoop1T ⟨1, 64, 11, 8⟩ 0 "__loop366" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_701 : Data.core680.body = oqMainT ⟨1, 64, 15, 6⟩ 0 "__loop406" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_885 : Data.core864.body = oqLoop1T ⟨1, 64, 15, 6⟩ 0 "__loop406" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_575 : Data.core554.body = oqMainT ⟨1, 64, 15, 7⟩ 0 "__loop388" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_865 : Data.core844.body = oqLoop1T ⟨1, 64, 15, 7⟩ 0 "__loop388" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_598 : Data.core577.body = oqMainT ⟨1, 64, 17, 7⟩ 0 "__loop391" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_869 : Data.core848.body = oqLoop1T ⟨1, 64, 17, 7⟩ 0 "__loop391" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_623 : Data.core602.body = oqMainT ⟨1, 64, 13, 7⟩ 1 "__loop396" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_874 : Data.core853.body = oqLoop1T ⟨1, 64, 13, 7⟩ 1 "__loop396" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_654 : Data.core633.body = oqMainT ⟨1, 64, 16, 7⟩ 1 "__loop399" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_877 : Data.core856.body = oqLoop1T ⟨1, 64, 16, 7⟩ 1 "__loop399" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_425 : Data.core404.body = oqMainT ⟨0, 16, 9, 5⟩ 0 "__loop362" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_833 : Data.core812.body = oqLoop0T ⟨0, 16, 9, 5⟩ "__loop362" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_418 : Data.core397.body = oqMainT ⟨0, 16, 10, 6⟩ 0 "__loop360" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_829 : Data.core808.body = oqLoop0T ⟨0, 16, 10, 6⟩ "__loop360" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_524 : Data.core503.body = oqMainT ⟨0, 16, 14, 4⟩ 0 "__loop381" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_858 : Data.core837.body = oqLoop0T ⟨0, 16, 14, 4⟩ "__loop381" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_491 : Data.core470.body = oqMainT ⟨0, 16, 14, 5⟩ 0 "__loop374" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_849 : Data.core828.body = oqLoop0T ⟨0, 16, 14, 5⟩ "__loop374" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_489 : Data.core468.body = oqMainT ⟨0, 16, 14, 6⟩ 0 "__loop373" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_848 : Data.core827.body = oqLoop0T ⟨0, 16, 14, 6⟩ "__loop373" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_761 : Data.core740.body = oqMainT ⟨0, 16, 18, 4⟩ 0 "__loop414" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_894 : Data.core873.body = oqLoop0T ⟨0, 16, 18, 4⟩ "__loop414" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_600 : Data.core579.body = oqMainT ⟨0, 16, 17, 6⟩ 0 "__loop392" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_870 : Data.core849.body = oqLoop0T ⟨0, 16, 17, 6⟩ "__loop392" :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
