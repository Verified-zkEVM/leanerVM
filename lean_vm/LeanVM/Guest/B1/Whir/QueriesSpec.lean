/-
  LeanVM.Guest.B1.Whir.QueriesSpec

  `opening_queries` at its 50 compiled shapes.
-/

module

public import LeanVM.Guest.B1.Whir.Queries

/-!
# The specializations of `opening_queries`

`opening_queries__L{base}_L{I}_L{blocks}_L{depth}_L{cd}` and its loop helper, each body equal to
its template by kernel evaluation (`stmtsEqb_sound`), and the soundness of each at its shape.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

/-- **A specialization of `opening_queries` and its loop helper** at the shape
`(base, I, blocks, pd, cd)`: the shape's facts, and each function's parameters and body the
template's. -/
structure OqSpec (name loop : String) (base I blocks pd cd : ℕ) : Prop where
  shape : OqShape base I blocks pd cd
  fn : ∃ f : Fn, coreProgram.find? name = some f ∧ f.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5] ∧
    f.body = oqBody loop
  loopFn : ∃ lf : Fn, coreProgram.find? loop = some lf ∧
    lf.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7] ∧ lf.body = oqLoopBody base I blocks pd cd loop

/-- `opening_queries_sound` at a specialization. -/
theorem opening_queries_sound_of_spec {name loop : String} {base I blocks pd cd : ℕ}
    (hs : OqSpec name loop base I blocks pd cd) {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n (pd + cd) pos) {rets : List E}
    (h : coreProgram.Rel rd name [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries base I (pd + cd) cd n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n]
      rets := by
  obtain ⟨f, hf, hfp, hfb⟩ := hs.fn
  obtain ⟨lf, hlf, hlp, hlb⟩ := hs.loopFn
  exact opening_queries_sound hs.shape hf hfp hfb hlf hlp hlb hn hpre h


set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L16_L6_L14_L5` and its loop helper `__loop435`, at their shape. -/
theorem oqSpec_L0_L16_L6_L14_L5 : OqSpec "opening_queries__L0_L16_L6_L14_L5" "__loop435" 0 16 6 9 5 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 590) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 981) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L0_L16_L6_L14_L5_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 14 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L14_L5" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 14 5 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L0_L16_L6_L14_L5 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L16_L6_L15_L5` and its loop helper `__loop434`, at their shape. -/
theorem oqSpec_L0_L16_L6_L15_L5 : OqSpec "opening_queries__L0_L16_L6_L15_L5" "__loop434" 0 16 6 10 5 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 587) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 979) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L0_L16_L6_L15_L5_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 15 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L15_L5" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 15 5 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L0_L16_L6_L15_L5 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L16_L6_L16_L4` and its loop helper `__loop460`, at their shape. -/
theorem oqSpec_L0_L16_L6_L16_L4 : OqSpec "opening_queries__L0_L16_L6_L16_L4" "__loop460" 0 16 6 12 4 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 707) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 1012) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L0_L16_L6_L16_L4_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 16 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L16_L4" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 16 4 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L0_L16_L6_L16_L4 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L16_L6_L16_L5` and its loop helper `__loop438`, at their shape. -/
theorem oqSpec_L0_L16_L6_L16_L5 : OqSpec "opening_queries__L0_L16_L6_L16_L5" "__loop438" 0 16 6 11 5 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 601) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 985) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L0_L16_L6_L16_L5_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 16 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L16_L5" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 16 5 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L0_L16_L6_L16_L5 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L16_L6_L16_L6` and its loop helper `__loop432`, at their shape. -/
theorem oqSpec_L0_L16_L6_L16_L6 : OqSpec "opening_queries__L0_L16_L6_L16_L6" "__loop432" 0 16 6 10 6 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 584) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 976) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L0_L16_L6_L16_L6_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 16 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L16_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 16 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L0_L16_L6_L16_L6 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L16_L6_L17_L4` and its loop helper `__loop462`, at their shape. -/
theorem oqSpec_L0_L16_L6_L17_L4 : OqSpec "opening_queries__L0_L16_L6_L17_L4" "__loop462" 0 16 6 13 4 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 719) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 1014) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L0_L16_L6_L17_L4_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 17 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L17_L4" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 17 4 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L0_L16_L6_L17_L4 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L16_L6_L17_L5` and its loop helper `__loop441`, at their shape. -/
theorem oqSpec_L0_L16_L6_L17_L5 : OqSpec "opening_queries__L0_L16_L6_L17_L5" "__loop441" 0 16 6 12 5 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 614) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 989) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L0_L16_L6_L17_L5_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 17 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L17_L5" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 17 5 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L0_L16_L6_L17_L5 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L16_L6_L17_L6` and its loop helper `__loop437`, at their shape. -/
theorem oqSpec_L0_L16_L6_L17_L6 : OqSpec "opening_queries__L0_L16_L6_L17_L6" "__loop437" 0 16 6 11 6 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 599) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 984) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L0_L16_L6_L17_L6_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 17 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L17_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 17 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L0_L16_L6_L17_L6 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L16_L6_L18_L4` and its loop helper `__loop455`, at their shape. -/
theorem oqSpec_L0_L16_L6_L18_L4 : OqSpec "opening_queries__L0_L16_L6_L18_L4" "__loop455" 0 16 6 14 4 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 675) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 1007) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L0_L16_L6_L18_L4_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 18 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L18_L4" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 18 4 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L0_L16_L6_L18_L4 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L16_L6_L18_L5` and its loop helper `__loop444`, at their shape. -/
theorem oqSpec_L0_L16_L6_L18_L5 : OqSpec "opening_queries__L0_L16_L6_L18_L5" "__loop444" 0 16 6 13 5 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 629) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 993) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L0_L16_L6_L18_L5_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 18 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L18_L5" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 18 5 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L0_L16_L6_L18_L5 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L16_L6_L18_L6` and its loop helper `__loop440`, at their shape. -/
theorem oqSpec_L0_L16_L6_L18_L6 : OqSpec "opening_queries__L0_L16_L6_L18_L6" "__loop440" 0 16 6 12 6 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 612) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 988) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L0_L16_L6_L18_L6_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 18 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L18_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 18 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L0_L16_L6_L18_L6 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L16_L6_L19_L4` and its loop helper `__loop465`, at their shape. -/
theorem oqSpec_L0_L16_L6_L19_L4 : OqSpec "opening_queries__L0_L16_L6_L19_L4" "__loop465" 0 16 6 15 4 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 742) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 1017) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L0_L16_L6_L19_L4_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 19 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L19_L4" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 19 4 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L0_L16_L6_L19_L4 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L16_L6_L19_L5` and its loop helper `__loop447`, at their shape. -/
theorem oqSpec_L0_L16_L6_L19_L5 : OqSpec "opening_queries__L0_L16_L6_L19_L5" "__loop447" 0 16 6 14 5 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 644) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 997) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L0_L16_L6_L19_L5_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 19 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L19_L5" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 19 5 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L0_L16_L6_L19_L5 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L16_L6_L19_L6` and its loop helper `__loop443`, at their shape. -/
theorem oqSpec_L0_L16_L6_L19_L6 : OqSpec "opening_queries__L0_L16_L6_L19_L6" "__loop443" 0 16 6 13 6 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 627) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 992) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L0_L16_L6_L19_L6_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 19 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L19_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 19 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L0_L16_L6_L19_L6 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L16_L6_L20_L4` and its loop helper `__loop469`, at their shape. -/
theorem oqSpec_L0_L16_L6_L20_L4 : OqSpec "opening_queries__L0_L16_L6_L20_L4" "__loop469" 0 16 6 16 4 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 756) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 1022) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L0_L16_L6_L20_L4_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 20 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L20_L4" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 20 4 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L0_L16_L6_L20_L4 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L16_L6_L20_L5` and its loop helper `__loop450`, at their shape. -/
theorem oqSpec_L0_L16_L6_L20_L5 : OqSpec "opening_queries__L0_L16_L6_L20_L5" "__loop450" 0 16 6 15 5 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 657) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 1001) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L0_L16_L6_L20_L5_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 20 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L20_L5" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 20 5 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L0_L16_L6_L20_L5 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L16_L6_L20_L6` and its loop helper `__loop446`, at their shape. -/
theorem oqSpec_L0_L16_L6_L20_L6 : OqSpec "opening_queries__L0_L16_L6_L20_L6" "__loop446" 0 16 6 14 6 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 642) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 996) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L0_L16_L6_L20_L6_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 20 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L20_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 20 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L0_L16_L6_L20_L6 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L16_L6_L21_L4` and its loop helper `__loop473`, at their shape. -/
theorem oqSpec_L0_L16_L6_L21_L4 : OqSpec "opening_queries__L0_L16_L6_L21_L4" "__loop473" 0 16 6 17 4 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 828) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 1027) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L0_L16_L6_L21_L4_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 21 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L21_L4" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 21 4 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L0_L16_L6_L21_L4 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L16_L6_L21_L5` and its loop helper `__loop453`, at their shape. -/
theorem oqSpec_L0_L16_L6_L21_L5 : OqSpec "opening_queries__L0_L16_L6_L21_L5" "__loop453" 0 16 6 16 5 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 670) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 1005) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L0_L16_L6_L21_L5_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 21 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L21_L5" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 21 5 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L0_L16_L6_L21_L5 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L16_L6_L21_L6` and its loop helper `__loop449`, at their shape. -/
theorem oqSpec_L0_L16_L6_L21_L6 : OqSpec "opening_queries__L0_L16_L6_L21_L6" "__loop449" 0 16 6 15 6 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 655) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 1000) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L0_L16_L6_L21_L6_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 21 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L21_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 21 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L0_L16_L6_L21_L6 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L16_L6_L22_L4` and its loop helper `__loop483`, at their shape. -/
theorem oqSpec_L0_L16_L6_L22_L4 : OqSpec "opening_queries__L0_L16_L6_L22_L4" "__loop483" 0 16 6 18 4 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 906) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 1038) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L0_L16_L6_L22_L4_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 22 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L22_L4" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 22 4 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L0_L16_L6_L22_L4 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L16_L6_L22_L5` and its loop helper `__loop468`, at their shape. -/
theorem oqSpec_L0_L16_L6_L22_L5 : OqSpec "opening_queries__L0_L16_L6_L22_L5" "__loop468" 0 16 6 17 5 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 753) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 1021) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L0_L16_L6_L22_L5_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 22 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L22_L5" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 22 5 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L0_L16_L6_L22_L5 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L16_L6_L22_L6` and its loop helper `__loop452`, at their shape. -/
theorem oqSpec_L0_L16_L6_L22_L6 : OqSpec "opening_queries__L0_L16_L6_L22_L6" "__loop452" 0 16 6 16 6 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 668) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 1004) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L0_L16_L6_L22_L6_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 22 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L22_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 22 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L0_L16_L6_L22_L6 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L16_L6_L23_L5` and its loop helper `__loop472`, at their shape. -/
theorem oqSpec_L0_L16_L6_L23_L5 : OqSpec "opening_queries__L0_L16_L6_L23_L5" "__loop472" 0 16 6 18 5 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 825) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 1026) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L0_L16_L6_L23_L5_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 23 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L23_L5" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 23 5 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L0_L16_L6_L23_L5 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L16_L6_L23_L6` and its loop helper `__loop467`, at their shape. -/
theorem oqSpec_L0_L16_L6_L23_L6 : OqSpec "opening_queries__L0_L16_L6_L23_L6" "__loop467" 0 16 6 17 6 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 751) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 1020) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L0_L16_L6_L23_L6_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 23 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L23_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 23 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L0_L16_L6_L23_L6 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L16_L6_L24_L5` and its loop helper `__loop480`, at their shape. -/
theorem oqSpec_L0_L16_L6_L24_L5 : OqSpec "opening_queries__L0_L16_L6_L24_L5" "__loop480" 0 16 6 19 5 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 890) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 1034) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L0_L16_L6_L24_L5_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 24 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L24_L5" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 24 5 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L0_L16_L6_L24_L5 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L16_L6_L24_L6` and its loop helper `__loop471`, at their shape. -/
theorem oqSpec_L0_L16_L6_L24_L6 : OqSpec "opening_queries__L0_L16_L6_L24_L6" "__loop471" 0 16 6 18 6 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 823) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 1025) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L0_L16_L6_L24_L6_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 24 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L24_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 24 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L0_L16_L6_L24_L6 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L16_L6_L25_L5` and its loop helper `__loop482`, at their shape. -/
theorem oqSpec_L0_L16_L6_L25_L5 : OqSpec "opening_queries__L0_L16_L6_L25_L5" "__loop482" 0 16 6 20 5 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 902) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 1037) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L0_L16_L6_L25_L5_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 25 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L25_L5" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 25 5 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L0_L16_L6_L25_L5 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L64_L8_L17_L8` and its loop helper `__loop430`, at their shape. -/
theorem oqSpec_L1_L64_L8_L17_L8 : OqSpec "opening_queries__L1_L64_L8_L17_L8" "__loop430" 1 64 8 9 8 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 580) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 973) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L1_L64_L8_L17_L8_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 17 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L17_L8" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 17 8 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L1_L64_L8_L17_L8 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L64_L8_L18_L7` and its loop helper `__loop457`, at their shape. -/
theorem oqSpec_L1_L64_L8_L18_L7 : OqSpec "opening_queries__L1_L64_L8_L18_L7" "__loop457" 1 64 8 11 7 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 684) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 1009) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L1_L64_L8_L18_L7_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 18 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L18_L7" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 18 7 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L1_L64_L8_L18_L7 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L64_L8_L18_L8` and its loop helper `__loop436`, at their shape. -/
theorem oqSpec_L1_L64_L8_L18_L8 : OqSpec "opening_queries__L1_L64_L8_L18_L8" "__loop436" 1 64 8 10 8 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 597) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 983) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L1_L64_L8_L18_L8_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 18 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L18_L8" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 18 8 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L1_L64_L8_L18_L8 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L64_L8_L19_L7` and its loop helper `__loop458`, at their shape. -/
theorem oqSpec_L1_L64_L8_L19_L7 : OqSpec "opening_queries__L1_L64_L8_L19_L7" "__loop458" 1 64 8 12 7 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 693) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 1010) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L1_L64_L8_L19_L7_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 19 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L19_L7" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 19 7 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L1_L64_L8_L19_L7 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L64_L8_L19_L8` and its loop helper `__loop439`, at their shape. -/
theorem oqSpec_L1_L64_L8_L19_L8 : OqSpec "opening_queries__L1_L64_L8_L19_L8" "__loop439" 1 64 8 11 8 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 610) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 987) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L1_L64_L8_L19_L8_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 19 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L19_L8" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 19 8 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L1_L64_L8_L19_L8 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L64_L8_L20_L6` and its loop helper `__loop474`, at their shape. -/
theorem oqSpec_L1_L64_L8_L20_L6 : OqSpec "opening_queries__L1_L64_L8_L20_L6" "__loop474" 1 64 8 14 6 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 837) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 1028) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L1_L64_L8_L20_L6_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 20 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L20_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 20 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L1_L64_L8_L20_L6 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L64_L8_L20_L7` and its loop helper `__loop459`, at their shape. -/
theorem oqSpec_L1_L64_L8_L20_L7 : OqSpec "opening_queries__L1_L64_L8_L20_L7" "__loop459" 1 64 8 13 7 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 702) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 1011) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L1_L64_L8_L20_L7_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 20 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L20_L7" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 20 7 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L1_L64_L8_L20_L7 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L64_L8_L20_L8` and its loop helper `__loop442`, at their shape. -/
theorem oqSpec_L1_L64_L8_L20_L8 : OqSpec "opening_queries__L1_L64_L8_L20_L8" "__loop442" 1 64 8 12 8 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 625) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 991) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L1_L64_L8_L20_L8_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 20 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L20_L8" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 20 8 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L1_L64_L8_L20_L8 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L64_L8_L21_L6` and its loop helper `__loop475`, at their shape. -/
theorem oqSpec_L1_L64_L8_L21_L6 : OqSpec "opening_queries__L1_L64_L8_L21_L6" "__loop475" 1 64 8 15 6 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 846) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 1029) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L1_L64_L8_L21_L6_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 21 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L21_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 21 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L1_L64_L8_L21_L6 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L64_L8_L21_L7` and its loop helper `__loop461`, at their shape. -/
theorem oqSpec_L1_L64_L8_L21_L7 : OqSpec "opening_queries__L1_L64_L8_L21_L7" "__loop461" 1 64 8 14 7 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 714) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 1013) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L1_L64_L8_L21_L7_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 21 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L21_L7" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 21 7 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L1_L64_L8_L21_L7 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L64_L8_L21_L8` and its loop helper `__loop445`, at their shape. -/
theorem oqSpec_L1_L64_L8_L21_L8 : OqSpec "opening_queries__L1_L64_L8_L21_L8" "__loop445" 1 64 8 13 8 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 640) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 995) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L1_L64_L8_L21_L8_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 21 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L21_L8" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 21 8 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L1_L64_L8_L21_L8 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L64_L8_L22_L6` and its loop helper `__loop476`, at their shape. -/
theorem oqSpec_L1_L64_L8_L22_L6 : OqSpec "opening_queries__L1_L64_L8_L22_L6" "__loop476" 1 64 8 16 6 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 855) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 1030) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L1_L64_L8_L22_L6_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 22 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L22_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 22 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L1_L64_L8_L22_L6 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L64_L8_L22_L7` and its loop helper `__loop463`, at their shape. -/
theorem oqSpec_L1_L64_L8_L22_L7 : OqSpec "opening_queries__L1_L64_L8_L22_L7" "__loop463" 1 64 8 15 7 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 726) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 1015) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L1_L64_L8_L22_L7_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 22 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L22_L7" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 22 7 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L1_L64_L8_L22_L7 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L64_L8_L22_L8` and its loop helper `__loop448`, at their shape. -/
theorem oqSpec_L1_L64_L8_L22_L8 : OqSpec "opening_queries__L1_L64_L8_L22_L8" "__loop448" 1 64 8 14 8 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 653) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 999) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L1_L64_L8_L22_L8_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 22 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L22_L8" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 22 8 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L1_L64_L8_L22_L8 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L64_L8_L23_L6` and its loop helper `__loop477`, at their shape. -/
theorem oqSpec_L1_L64_L8_L23_L6 : OqSpec "opening_queries__L1_L64_L8_L23_L6" "__loop477" 1 64 8 17 6 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 866) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 1031) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L1_L64_L8_L23_L6_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 23 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L23_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 23 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L1_L64_L8_L23_L6 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L64_L8_L23_L7` and its loop helper `__loop464`, at their shape. -/
theorem oqSpec_L1_L64_L8_L23_L7 : OqSpec "opening_queries__L1_L64_L8_L23_L7" "__loop464" 1 64 8 16 7 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 737) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 1016) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L1_L64_L8_L23_L7_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 23 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L23_L7" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 23 7 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L1_L64_L8_L23_L7 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L64_L8_L23_L8` and its loop helper `__loop451`, at their shape. -/
theorem oqSpec_L1_L64_L8_L23_L8 : OqSpec "opening_queries__L1_L64_L8_L23_L8" "__loop451" 1 64 8 15 8 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 666) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 1003) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L1_L64_L8_L23_L8_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 23 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L23_L8" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 23 8 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L1_L64_L8_L23_L8 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L64_L8_L24_L6` and its loop helper `__loop478`, at their shape. -/
theorem oqSpec_L1_L64_L8_L24_L6 : OqSpec "opening_queries__L1_L64_L8_L24_L6" "__loop478" 1 64 8 18 6 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 877) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 1032) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L1_L64_L8_L24_L6_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 24 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L24_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 24 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L1_L64_L8_L24_L6 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L64_L8_L24_L7` and its loop helper `__loop466`, at their shape. -/
theorem oqSpec_L1_L64_L8_L24_L7 : OqSpec "opening_queries__L1_L64_L8_L24_L7" "__loop466" 1 64 8 17 7 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 749) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 1019) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L1_L64_L8_L24_L7_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 24 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L24_L7" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 24 7 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L1_L64_L8_L24_L7 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L64_L8_L25_L6` and its loop helper `__loop479`, at their shape. -/
theorem oqSpec_L1_L64_L8_L25_L6 : OqSpec "opening_queries__L1_L64_L8_L25_L6" "__loop479" 1 64 8 19 6 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 888) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 1033) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L1_L64_L8_L25_L6_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 25 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L25_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 25 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L1_L64_L8_L25_L6 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L64_L8_L25_L7` and its loop helper `__loop470`, at their shape. -/
theorem oqSpec_L1_L64_L8_L25_L7 : OqSpec "opening_queries__L1_L64_L8_L25_L7" "__loop470" 1 64 8 18 7 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 821) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 1024) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L1_L64_L8_L25_L7_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 25 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L25_L7" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 25 7 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L1_L64_L8_L25_L7 hn hpre h

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L64_L8_L26_L6` and its loop helper `__loop481`, at their shape. -/
theorem oqSpec_L1_L64_L8_L26_L6 : OqSpec "opening_queries__L1_L64_L8_L26_L6" "__loop481" 1 64 8 20 6 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨_, Program.find?_of_indexOf? (j := 900) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩,
    ⟨_, Program.find?_of_indexOf? (j := 1036) (by decide +kernel) rfl, rfl, stmtsEqb_sound (by decide +kernel)⟩⟩

theorem opening_queries_L1_L64_L8_L26_L6_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 26 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L26_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 26 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound_of_spec oqSpec_L1_L64_L8_L26_L6 hn hpre h

end
end LeanVM.Guest.B1
