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
theorem oqBody_433 : Data.core423.body = oqMainT ⟨1, 64, 10, 8⟩ 0 "__loop363" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_835 : Data.core823.body = oqLoop1T ⟨1, 64, 10, 8⟩ 0 "__loop363" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_551 : Data.core541.body = oqMainT ⟨1, 64, 13, 7⟩ 0 "__loop384" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_861 : Data.core849.body = oqLoop1T ⟨1, 64, 13, 7⟩ 0 "__loop384" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_487 : Data.core477.body = oqMainT ⟨1, 64, 13, 8⟩ 0 "__loop372" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_847 : Data.core835.body = oqLoop1T ⟨1, 64, 13, 8⟩ 0 "__loop372" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_586 : Data.core576.body = oqMainT ⟨1, 64, 16, 7⟩ 0 "__loop389" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_866 : Data.core854.body = oqLoop1T ⟨1, 64, 16, 7⟩ 0 "__loop389" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_755 : Data.core745.body = oqMainT ⟨1, 64, 20, 6⟩ 0 "__loop412" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_892 : Data.core880.body = oqLoop1T ⟨1, 64, 20, 6⟩ 0 "__loop412" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_643 : Data.core633.body = oqMainT ⟨1, 64, 15, 7⟩ 1 "__loop398" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_876 : Data.core864.body = oqLoop1T ⟨1, 64, 15, 7⟩ 1 "__loop398" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_665 : Data.core655.body = oqMainT ⟨1, 64, 17, 7⟩ 1 "__loop400" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_878 : Data.core866.body = oqLoop1T ⟨1, 64, 17, 7⟩ 1 "__loop400" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_556 : Data.core546.body = oqMainT ⟨0, 16, 12, 4⟩ 0 "__loop385" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_862 : Data.core850.body = oqLoop0T ⟨0, 16, 12, 4⟩ "__loop385" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_455 : Data.core445.body = oqMainT ⟨0, 16, 12, 5⟩ 0 "__loop368" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_841 : Data.core829.body = oqLoop0T ⟨0, 16, 12, 5⟩ "__loop368" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_452 : Data.core442.body = oqMainT ⟨0, 16, 12, 6⟩ 0 "__loop367" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_840 : Data.core828.body = oqLoop0T ⟨0, 16, 12, 6⟩ "__loop367" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_605 : Data.core595.body = oqMainT ⟨0, 16, 16, 4⟩ 0 "__loop394" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_872 : Data.core860.body = oqLoop0T ⟨0, 16, 16, 4⟩ "__loop394" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_519 : Data.core509.body = oqMainT ⟨0, 16, 16, 5⟩ 0 "__loop380" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_857 : Data.core845.body = oqLoop0T ⟨0, 16, 16, 5⟩ "__loop380" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_517 : Data.core507.body = oqMainT ⟨0, 16, 16, 6⟩ 0 "__loop379" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_856 : Data.core844.body = oqLoop0T ⟨0, 16, 16, 6⟩ "__loop379" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_678 : Data.core668.body = oqMainT ⟨0, 16, 18, 6⟩ 0 "__loop402" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_881 : Data.core869.body = oqLoop0T ⟨0, 16, 18, 6⟩ "__loop402" :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
