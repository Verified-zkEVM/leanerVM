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
theorem oqBody_433 : Data.core424.body = oqMainT ⟨1, 64, 10, 8⟩ 0 "__loop368" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_835 : Data.core824.body = oqLoop1T ⟨1, 64, 10, 8⟩ 0 "__loop368" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_551 : Data.core542.body = oqMainT ⟨1, 64, 13, 7⟩ 0 "__loop389" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_861 : Data.core850.body = oqLoop1T ⟨1, 64, 13, 7⟩ 0 "__loop389" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_487 : Data.core478.body = oqMainT ⟨1, 64, 13, 8⟩ 0 "__loop377" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_847 : Data.core836.body = oqLoop1T ⟨1, 64, 13, 8⟩ 0 "__loop377" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_586 : Data.core577.body = oqMainT ⟨1, 64, 16, 7⟩ 0 "__loop394" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_866 : Data.core855.body = oqLoop1T ⟨1, 64, 16, 7⟩ 0 "__loop394" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_755 : Data.core746.body = oqMainT ⟨1, 64, 20, 6⟩ 0 "__loop417" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_892 : Data.core881.body = oqLoop1T ⟨1, 64, 20, 6⟩ 0 "__loop417" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_643 : Data.core634.body = oqMainT ⟨1, 64, 15, 7⟩ 1 "__loop403" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_876 : Data.core865.body = oqLoop1T ⟨1, 64, 15, 7⟩ 1 "__loop403" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_665 : Data.core656.body = oqMainT ⟨1, 64, 17, 7⟩ 1 "__loop405" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_878 : Data.core867.body = oqLoop1T ⟨1, 64, 17, 7⟩ 1 "__loop405" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_556 : Data.core547.body = oqMainT ⟨0, 16, 12, 4⟩ 0 "__loop390" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_862 : Data.core851.body = oqLoop0T ⟨0, 16, 12, 4⟩ "__loop390" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_455 : Data.core446.body = oqMainT ⟨0, 16, 12, 5⟩ 0 "__loop373" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_841 : Data.core830.body = oqLoop0T ⟨0, 16, 12, 5⟩ "__loop373" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_452 : Data.core443.body = oqMainT ⟨0, 16, 12, 6⟩ 0 "__loop372" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_840 : Data.core829.body = oqLoop0T ⟨0, 16, 12, 6⟩ "__loop372" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_605 : Data.core596.body = oqMainT ⟨0, 16, 16, 4⟩ 0 "__loop399" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_872 : Data.core861.body = oqLoop0T ⟨0, 16, 16, 4⟩ "__loop399" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_519 : Data.core510.body = oqMainT ⟨0, 16, 16, 5⟩ 0 "__loop385" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_857 : Data.core846.body = oqLoop0T ⟨0, 16, 16, 5⟩ "__loop385" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_517 : Data.core508.body = oqMainT ⟨0, 16, 16, 6⟩ 0 "__loop384" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_856 : Data.core845.body = oqLoop0T ⟨0, 16, 16, 6⟩ "__loop384" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_678 : Data.core669.body = oqMainT ⟨0, 16, 18, 6⟩ 0 "__loop407" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_881 : Data.core870.body = oqLoop0T ⟨0, 16, 18, 6⟩ "__loop407" :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
