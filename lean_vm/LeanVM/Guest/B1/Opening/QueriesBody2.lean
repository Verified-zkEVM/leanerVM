/-
  LeanVM.Guest.B1.Opening.QueriesBody2

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
theorem oqBody_433 : Data.core455.body = oqMainT ⟨1, 64, 10, 8⟩ 0 "__loop372" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_835 : Data.core855.body = oqLoop1T ⟨1, 64, 10, 8⟩ 0 "__loop372" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_551 : Data.core573.body = oqMainT ⟨1, 64, 13, 7⟩ 0 "__loop393" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_861 : Data.core897.body = oqLoop1T ⟨1, 64, 13, 7⟩ 0 "__loop393" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_487 : Data.core509.body = oqMainT ⟨1, 64, 13, 8⟩ 0 "__loop381" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_847 : Data.core873.body = oqLoop1T ⟨1, 64, 13, 8⟩ 0 "__loop381" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_586 : Data.core608.body = oqMainT ⟨1, 64, 16, 7⟩ 0 "__loop398" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_866 : Data.core907.body = oqLoop1T ⟨1, 64, 16, 7⟩ 0 "__loop398" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_755 : Data.core777.body = oqMainT ⟨1, 64, 20, 6⟩ 0 "__loop421" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_892 : Data.core942.body = oqLoop1T ⟨1, 64, 20, 6⟩ 0 "__loop421" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_643 : Data.core665.body = oqMainT ⟨1, 64, 15, 7⟩ 1 "__loop407" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_876 : Data.core921.body = oqLoop1T ⟨1, 64, 15, 7⟩ 1 "__loop407" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_665 : Data.core687.body = oqMainT ⟨1, 64, 17, 7⟩ 1 "__loop409" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_878 : Data.core923.body = oqLoop1T ⟨1, 64, 17, 7⟩ 1 "__loop409" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_556 : Data.core578.body = oqMainT ⟨0, 16, 12, 4⟩ 0 "__loop394" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_862 : Data.core899.body = oqLoop0T ⟨0, 16, 12, 4⟩ "__loop394" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_455 : Data.core477.body = oqMainT ⟨0, 16, 12, 5⟩ 0 "__loop377" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_841 : Data.core865.body = oqLoop0T ⟨0, 16, 12, 5⟩ "__loop377" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_452 : Data.core474.body = oqMainT ⟨0, 16, 12, 6⟩ 0 "__loop376" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_840 : Data.core863.body = oqLoop0T ⟨0, 16, 12, 6⟩ "__loop376" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_605 : Data.core627.body = oqMainT ⟨0, 16, 16, 4⟩ 0 "__loop403" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_872 : Data.core917.body = oqLoop0T ⟨0, 16, 16, 4⟩ "__loop403" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_519 : Data.core541.body = oqMainT ⟨0, 16, 16, 5⟩ 0 "__loop389" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_857 : Data.core889.body = oqLoop0T ⟨0, 16, 16, 5⟩ "__loop389" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_517 : Data.core539.body = oqMainT ⟨0, 16, 16, 6⟩ 0 "__loop388" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_856 : Data.core887.body = oqLoop0T ⟨0, 16, 16, 6⟩ "__loop388" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_678 : Data.core700.body = oqMainT ⟨0, 16, 18, 6⟩ 0 "__loop411" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_881 : Data.core927.body = oqLoop0T ⟨0, 16, 18, 6⟩ "__loop411" :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
