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
theorem oqBody_413 : Data.core435.body = oqMainT ⟨1, 64, 9, 8⟩ 0 "__loop368" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_827 : Data.core847.body = oqLoop1T ⟨1, 64, 9, 8⟩ 0 "__loop368" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_449 : Data.core471.body = oqMainT ⟨1, 64, 11, 8⟩ 0 "__loop375" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_839 : Data.core861.body = oqLoop1T ⟨1, 64, 11, 8⟩ 0 "__loop375" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_701 : Data.core723.body = oqMainT ⟨1, 64, 15, 6⟩ 0 "__loop415" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_885 : Data.core933.body = oqLoop1T ⟨1, 64, 15, 6⟩ 0 "__loop415" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_575 : Data.core597.body = oqMainT ⟨1, 64, 15, 7⟩ 0 "__loop397" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_865 : Data.core905.body = oqLoop1T ⟨1, 64, 15, 7⟩ 0 "__loop397" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_598 : Data.core620.body = oqMainT ⟨1, 64, 17, 7⟩ 0 "__loop400" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_869 : Data.core911.body = oqLoop1T ⟨1, 64, 17, 7⟩ 0 "__loop400" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_623 : Data.core645.body = oqMainT ⟨1, 64, 13, 7⟩ 1 "__loop405" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_874 : Data.core919.body = oqLoop1T ⟨1, 64, 13, 7⟩ 1 "__loop405" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_654 : Data.core676.body = oqMainT ⟨1, 64, 16, 7⟩ 1 "__loop408" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_877 : Data.core922.body = oqLoop1T ⟨1, 64, 16, 7⟩ 1 "__loop408" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_425 : Data.core447.body = oqMainT ⟨0, 16, 9, 5⟩ 0 "__loop371" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_833 : Data.core853.body = oqLoop0T ⟨0, 16, 9, 5⟩ "__loop371" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_418 : Data.core440.body = oqMainT ⟨0, 16, 10, 6⟩ 0 "__loop369" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_829 : Data.core849.body = oqLoop0T ⟨0, 16, 10, 6⟩ "__loop369" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_524 : Data.core546.body = oqMainT ⟨0, 16, 14, 4⟩ 0 "__loop390" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_858 : Data.core891.body = oqLoop0T ⟨0, 16, 14, 4⟩ "__loop390" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_491 : Data.core513.body = oqMainT ⟨0, 16, 14, 5⟩ 0 "__loop383" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_849 : Data.core877.body = oqLoop0T ⟨0, 16, 14, 5⟩ "__loop383" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_489 : Data.core511.body = oqMainT ⟨0, 16, 14, 6⟩ 0 "__loop382" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_848 : Data.core875.body = oqLoop0T ⟨0, 16, 14, 6⟩ "__loop382" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_761 : Data.core783.body = oqMainT ⟨0, 16, 18, 4⟩ 0 "__loop423" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_894 : Data.core946.body = oqLoop0T ⟨0, 16, 18, 4⟩ "__loop423" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_600 : Data.core622.body = oqMainT ⟨0, 16, 17, 6⟩ 0 "__loop401" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_870 : Data.core913.body = oqLoop0T ⟨0, 16, 17, 6⟩ "__loop401" :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
