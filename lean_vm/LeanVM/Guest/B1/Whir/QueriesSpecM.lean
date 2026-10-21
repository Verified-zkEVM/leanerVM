/-
  LeanVM.Guest.B1.Whir.QueriesSpecM

  `opening_queries` at its 50 compiled shapes, under a hash model.
-/

module

public import LeanVM.Guest.B1.Whir.QueriesM

/-!
# The specializations of `opening_queries` under a hash model

Each specialization's `OqSpec` (`Whir/QueriesSpec.lean`, its body by kernel evaluation) gives
`opening_queries_model` at its shape.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

/-- `opening_queries__L0_L16_L6_L14_L5` under a hash model. -/
theorem opening_queries_L0_L16_L6_L14_L5_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 14 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L0_L16_L6_L14_L5" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 0 16 14 5 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L0_L16_L6_L14_L5 hn hpre h

/-- `opening_queries__L0_L16_L6_L15_L5` under a hash model. -/
theorem opening_queries_L0_L16_L6_L15_L5_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 15 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L0_L16_L6_L15_L5" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 0 16 15 5 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L0_L16_L6_L15_L5 hn hpre h

/-- `opening_queries__L0_L16_L6_L16_L4` under a hash model. -/
theorem opening_queries_L0_L16_L6_L16_L4_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 16 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L0_L16_L6_L16_L4" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 0 16 16 4 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L0_L16_L6_L16_L4 hn hpre h

/-- `opening_queries__L0_L16_L6_L16_L5` under a hash model. -/
theorem opening_queries_L0_L16_L6_L16_L5_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 16 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L0_L16_L6_L16_L5" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 0 16 16 5 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L0_L16_L6_L16_L5 hn hpre h

/-- `opening_queries__L0_L16_L6_L16_L6` under a hash model. -/
theorem opening_queries_L0_L16_L6_L16_L6_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 16 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L0_L16_L6_L16_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 0 16 16 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L0_L16_L6_L16_L6 hn hpre h

/-- `opening_queries__L0_L16_L6_L17_L4` under a hash model. -/
theorem opening_queries_L0_L16_L6_L17_L4_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 17 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L0_L16_L6_L17_L4" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 0 16 17 4 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L0_L16_L6_L17_L4 hn hpre h

/-- `opening_queries__L0_L16_L6_L17_L5` under a hash model. -/
theorem opening_queries_L0_L16_L6_L17_L5_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 17 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L0_L16_L6_L17_L5" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 0 16 17 5 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L0_L16_L6_L17_L5 hn hpre h

/-- `opening_queries__L0_L16_L6_L17_L6` under a hash model. -/
theorem opening_queries_L0_L16_L6_L17_L6_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 17 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L0_L16_L6_L17_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 0 16 17 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L0_L16_L6_L17_L6 hn hpre h

/-- `opening_queries__L0_L16_L6_L18_L4` under a hash model. -/
theorem opening_queries_L0_L16_L6_L18_L4_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 18 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L0_L16_L6_L18_L4" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 0 16 18 4 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L0_L16_L6_L18_L4 hn hpre h

/-- `opening_queries__L0_L16_L6_L18_L5` under a hash model. -/
theorem opening_queries_L0_L16_L6_L18_L5_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 18 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L0_L16_L6_L18_L5" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 0 16 18 5 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L0_L16_L6_L18_L5 hn hpre h

/-- `opening_queries__L0_L16_L6_L18_L6` under a hash model. -/
theorem opening_queries_L0_L16_L6_L18_L6_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 18 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L0_L16_L6_L18_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 0 16 18 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L0_L16_L6_L18_L6 hn hpre h

/-- `opening_queries__L0_L16_L6_L19_L4` under a hash model. -/
theorem opening_queries_L0_L16_L6_L19_L4_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 19 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L0_L16_L6_L19_L4" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 0 16 19 4 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L0_L16_L6_L19_L4 hn hpre h

/-- `opening_queries__L0_L16_L6_L19_L5` under a hash model. -/
theorem opening_queries_L0_L16_L6_L19_L5_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 19 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L0_L16_L6_L19_L5" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 0 16 19 5 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L0_L16_L6_L19_L5 hn hpre h

/-- `opening_queries__L0_L16_L6_L19_L6` under a hash model. -/
theorem opening_queries_L0_L16_L6_L19_L6_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 19 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L0_L16_L6_L19_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 0 16 19 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L0_L16_L6_L19_L6 hn hpre h

/-- `opening_queries__L0_L16_L6_L20_L4` under a hash model. -/
theorem opening_queries_L0_L16_L6_L20_L4_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 20 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L0_L16_L6_L20_L4" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 0 16 20 4 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L0_L16_L6_L20_L4 hn hpre h

/-- `opening_queries__L0_L16_L6_L20_L5` under a hash model. -/
theorem opening_queries_L0_L16_L6_L20_L5_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 20 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L0_L16_L6_L20_L5" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 0 16 20 5 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L0_L16_L6_L20_L5 hn hpre h

/-- `opening_queries__L0_L16_L6_L20_L6` under a hash model. -/
theorem opening_queries_L0_L16_L6_L20_L6_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 20 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L0_L16_L6_L20_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 0 16 20 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L0_L16_L6_L20_L6 hn hpre h

/-- `opening_queries__L0_L16_L6_L21_L4` under a hash model. -/
theorem opening_queries_L0_L16_L6_L21_L4_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 21 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L0_L16_L6_L21_L4" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 0 16 21 4 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L0_L16_L6_L21_L4 hn hpre h

/-- `opening_queries__L0_L16_L6_L21_L5` under a hash model. -/
theorem opening_queries_L0_L16_L6_L21_L5_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 21 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L0_L16_L6_L21_L5" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 0 16 21 5 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L0_L16_L6_L21_L5 hn hpre h

/-- `opening_queries__L0_L16_L6_L21_L6` under a hash model. -/
theorem opening_queries_L0_L16_L6_L21_L6_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 21 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L0_L16_L6_L21_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 0 16 21 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L0_L16_L6_L21_L6 hn hpre h

/-- `opening_queries__L0_L16_L6_L22_L4` under a hash model. -/
theorem opening_queries_L0_L16_L6_L22_L4_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 22 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L0_L16_L6_L22_L4" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 0 16 22 4 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L0_L16_L6_L22_L4 hn hpre h

/-- `opening_queries__L0_L16_L6_L22_L5` under a hash model. -/
theorem opening_queries_L0_L16_L6_L22_L5_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 22 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L0_L16_L6_L22_L5" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 0 16 22 5 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L0_L16_L6_L22_L5 hn hpre h

/-- `opening_queries__L0_L16_L6_L22_L6` under a hash model. -/
theorem opening_queries_L0_L16_L6_L22_L6_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 22 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L0_L16_L6_L22_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 0 16 22 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L0_L16_L6_L22_L6 hn hpre h

/-- `opening_queries__L0_L16_L6_L23_L5` under a hash model. -/
theorem opening_queries_L0_L16_L6_L23_L5_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 23 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L0_L16_L6_L23_L5" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 0 16 23 5 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L0_L16_L6_L23_L5 hn hpre h

/-- `opening_queries__L0_L16_L6_L23_L6` under a hash model. -/
theorem opening_queries_L0_L16_L6_L23_L6_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 23 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L0_L16_L6_L23_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 0 16 23 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L0_L16_L6_L23_L6 hn hpre h

/-- `opening_queries__L0_L16_L6_L24_L5` under a hash model. -/
theorem opening_queries_L0_L16_L6_L24_L5_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 24 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L0_L16_L6_L24_L5" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 0 16 24 5 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L0_L16_L6_L24_L5 hn hpre h

/-- `opening_queries__L0_L16_L6_L24_L6` under a hash model. -/
theorem opening_queries_L0_L16_L6_L24_L6_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 24 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L0_L16_L6_L24_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 0 16 24 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L0_L16_L6_L24_L6 hn hpre h

/-- `opening_queries__L0_L16_L6_L25_L5` under a hash model. -/
theorem opening_queries_L0_L16_L6_L25_L5_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 25 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L0_L16_L6_L25_L5" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 0 16 25 5 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L0_L16_L6_L25_L5 hn hpre h

/-- `opening_queries__L1_L64_L8_L17_L8` under a hash model. -/
theorem opening_queries_L1_L64_L8_L17_L8_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 17 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L1_L64_L8_L17_L8" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 1 64 17 8 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L1_L64_L8_L17_L8 hn hpre h

/-- `opening_queries__L1_L64_L8_L18_L7` under a hash model. -/
theorem opening_queries_L1_L64_L8_L18_L7_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 18 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L1_L64_L8_L18_L7" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 1 64 18 7 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L1_L64_L8_L18_L7 hn hpre h

/-- `opening_queries__L1_L64_L8_L18_L8` under a hash model. -/
theorem opening_queries_L1_L64_L8_L18_L8_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 18 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L1_L64_L8_L18_L8" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 1 64 18 8 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L1_L64_L8_L18_L8 hn hpre h

/-- `opening_queries__L1_L64_L8_L19_L7` under a hash model. -/
theorem opening_queries_L1_L64_L8_L19_L7_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 19 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L1_L64_L8_L19_L7" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 1 64 19 7 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L1_L64_L8_L19_L7 hn hpre h

/-- `opening_queries__L1_L64_L8_L19_L8` under a hash model. -/
theorem opening_queries_L1_L64_L8_L19_L8_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 19 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L1_L64_L8_L19_L8" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 1 64 19 8 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L1_L64_L8_L19_L8 hn hpre h

/-- `opening_queries__L1_L64_L8_L20_L6` under a hash model. -/
theorem opening_queries_L1_L64_L8_L20_L6_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 20 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L1_L64_L8_L20_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 1 64 20 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L1_L64_L8_L20_L6 hn hpre h

/-- `opening_queries__L1_L64_L8_L20_L7` under a hash model. -/
theorem opening_queries_L1_L64_L8_L20_L7_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 20 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L1_L64_L8_L20_L7" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 1 64 20 7 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L1_L64_L8_L20_L7 hn hpre h

/-- `opening_queries__L1_L64_L8_L20_L8` under a hash model. -/
theorem opening_queries_L1_L64_L8_L20_L8_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 20 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L1_L64_L8_L20_L8" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 1 64 20 8 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L1_L64_L8_L20_L8 hn hpre h

/-- `opening_queries__L1_L64_L8_L21_L6` under a hash model. -/
theorem opening_queries_L1_L64_L8_L21_L6_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 21 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L1_L64_L8_L21_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 1 64 21 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L1_L64_L8_L21_L6 hn hpre h

/-- `opening_queries__L1_L64_L8_L21_L7` under a hash model. -/
theorem opening_queries_L1_L64_L8_L21_L7_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 21 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L1_L64_L8_L21_L7" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 1 64 21 7 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L1_L64_L8_L21_L7 hn hpre h

/-- `opening_queries__L1_L64_L8_L21_L8` under a hash model. -/
theorem opening_queries_L1_L64_L8_L21_L8_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 21 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L1_L64_L8_L21_L8" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 1 64 21 8 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L1_L64_L8_L21_L8 hn hpre h

/-- `opening_queries__L1_L64_L8_L22_L6` under a hash model. -/
theorem opening_queries_L1_L64_L8_L22_L6_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 22 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L1_L64_L8_L22_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 1 64 22 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L1_L64_L8_L22_L6 hn hpre h

/-- `opening_queries__L1_L64_L8_L22_L7` under a hash model. -/
theorem opening_queries_L1_L64_L8_L22_L7_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 22 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L1_L64_L8_L22_L7" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 1 64 22 7 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L1_L64_L8_L22_L7 hn hpre h

/-- `opening_queries__L1_L64_L8_L22_L8` under a hash model. -/
theorem opening_queries_L1_L64_L8_L22_L8_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 22 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L1_L64_L8_L22_L8" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 1 64 22 8 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L1_L64_L8_L22_L8 hn hpre h

/-- `opening_queries__L1_L64_L8_L23_L6` under a hash model. -/
theorem opening_queries_L1_L64_L8_L23_L6_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 23 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L1_L64_L8_L23_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 1 64 23 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L1_L64_L8_L23_L6 hn hpre h

/-- `opening_queries__L1_L64_L8_L23_L7` under a hash model. -/
theorem opening_queries_L1_L64_L8_L23_L7_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 23 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L1_L64_L8_L23_L7" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 1 64 23 7 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L1_L64_L8_L23_L7 hn hpre h

/-- `opening_queries__L1_L64_L8_L23_L8` under a hash model. -/
theorem opening_queries_L1_L64_L8_L23_L8_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 23 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L1_L64_L8_L23_L8" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 1 64 23 8 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L1_L64_L8_L23_L8 hn hpre h

/-- `opening_queries__L1_L64_L8_L24_L6` under a hash model. -/
theorem opening_queries_L1_L64_L8_L24_L6_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 24 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L1_L64_L8_L24_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 1 64 24 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L1_L64_L8_L24_L6 hn hpre h

/-- `opening_queries__L1_L64_L8_L24_L7` under a hash model. -/
theorem opening_queries_L1_L64_L8_L24_L7_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 24 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L1_L64_L8_L24_L7" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 1 64 24 7 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L1_L64_L8_L24_L7 hn hpre h

/-- `opening_queries__L1_L64_L8_L25_L6` under a hash model. -/
theorem opening_queries_L1_L64_L8_L25_L6_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 25 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L1_L64_L8_L25_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 1 64 25 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L1_L64_L8_L25_L6 hn hpre h

/-- `opening_queries__L1_L64_L8_L25_L7` under a hash model. -/
theorem opening_queries_L1_L64_L8_L25_L7_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 25 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L1_L64_L8_L25_L7" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 1 64 25 7 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L1_L64_L8_L25_L7 hn hpre h

/-- `opening_queries__L1_L64_L8_L26_L6` under a hash model. -/
theorem opening_queries_L1_L64_L8_L26_L6_model {M : HashModel} {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n 26 pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd "opening_queries__L1_L64_L8_L26_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M 1 64 26 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_model_of_spec oqSpec_L1_L64_L8_L26_L6 hn hpre h

end
end LeanVM.Guest.B1
