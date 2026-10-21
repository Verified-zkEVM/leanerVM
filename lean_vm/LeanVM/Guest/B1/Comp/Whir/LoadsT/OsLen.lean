/-
  LeanVM.Guest.B1.Comp.Whir.LoadsT.OsLen

  The stream words `open_stacked`'s 28 specializations read: their count by the levels'
  positions (`osStreamLen`), equal to the templates' count, bounded; the configurations' body facts
  and final-message callees.
-/

module

public import LeanVM.Guest.B1.Comp.Whir.LoadsT.OsCursorL
public import LeanVM.Guest.Located.VerifySub
public import LeanVM.Guest.B1.Whir.OsInstFacts

/-!
# The stacked opening's stream length

`osStreamLen cfg`: the head's two words, each level's (`osHPEnd`), the tail's `2·(yrLog - 1)`.
Over the 28 configurations it is the templates' count `2 + osLvsCntL cfg 0 cfg.levels +
2·(yrLog - 1)` and below `2^64` (`osStreamLen_eq`); each configuration's body facts
(`osL_bodyFacts`) and final-message callee (`osL_fmOk`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.Located

@[expose] public section

/-- The stream position after the levels `lvl ..` from `p`. -/
def osLvsPos (cfg : OsCfg) : ℕ → List OsLvl → ℕ → ℕ
  | _, [], p => p
  | lvl, _ :: rest, p => osLvsPos cfg (lvl + 1) rest (osHPEnd cfg lvl p)

/-- **The stream words `open_stacked` reads**: the head's two, the levels', the tail rounds'. -/
def osStreamLen (cfg : OsCfg) : ℕ := osLvsPos cfg 0 cfg.levels 2 + 2 * (cfg.yrLog - 1)

set_option maxRecDepth 100000 in
/-- **The two counts agree**, bounded, over the 28 configurations. -/
theorem osStreamLen_eq : ∀ j < 28, osStreamLen (osCfgs.getD j default) =
      2 + osLvsCntL (osCfgs.getD j default) 0 (osCfgs.getD j default).levels +
        2 * ((osCfgs.getD j default).yrLog - 1) ∧
    osStreamLen (osCfgs.getD j default) < 2 ^ 64 := by
  decide +kernel

/-- The final-message callees and their lengths. -/
def osFmNames : List (String × ℕ) :=
  [("opening_final_message__L4", 4), ("opening_final_message__L8", 8),
    ("opening_final_message__L16", 16), ("opening_final_message__L32", 32)]

set_option maxRecDepth 100000 in
theorem osCfgs_fm : ∀ j < 28,
    ((osCfgs.getD j default).finalMsg, (osCfgs.getD j default).yrLen) ∈ osFmNames := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem osL_fm4 : ∃ fn : Fn, coreProgram.find? "opening_final_message__L4" = some fn ∧
    fn.params = [.n 0, .n 1, .n 2, .n 3] ∧ fn.body = ofmBody 4 :=
  ⟨_, Program.find?_of_indexOf? (j := 616) (by decide +kernel) rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem osL_fm8 : ∃ fn : Fn, coreProgram.find? "opening_final_message__L8" = some fn ∧
    fn.params = [.n 0, .n 1, .n 2, .n 3] ∧ fn.body = ofmBody 8 :=
  ⟨_, Program.find?_of_indexOf? (j := 631) (by decide +kernel) rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem osL_fm16 : ∃ fn : Fn, coreProgram.find? "opening_final_message__L16" = some fn ∧
    fn.params = [.n 0, .n 1, .n 2, .n 3] ∧ fn.body = ofmBody 16 :=
  ⟨_, Program.find?_of_indexOf? (j := 588) (by decide +kernel) rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem osL_fm32 : ∃ fn : Fn, coreProgram.find? "opening_final_message__L32" = some fn ∧
    fn.params = [.n 0, .n 1, .n 2, .n 3] ∧ fn.body = ofmBody 32 :=
  ⟨_, Program.find?_of_indexOf? (j := 602) (by decide +kernel) rfl, rfl, rfl⟩

/-- **Each configuration's final-message callee** has body `ofmBody yrLen`. -/
theorem osL_fmOk (j : ℕ) (hj : j < 28) : OsFmOk (osCfgs.getD j default) := by
  have h := osCfgs_fm j hj
  simp only [osFmNames, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨fn, hf, hp, hb⟩ := osL_fm4
    exact ⟨fn, by rw [h1]; exact hf, hp, by rw [h2]; exact hb, by omega⟩
  · obtain ⟨fn, hf, hp, hb⟩ := osL_fm8
    exact ⟨fn, by rw [h1]; exact hf, hp, by rw [h2]; exact hb, by omega⟩
  · obtain ⟨fn, hf, hp, hb⟩ := osL_fm16
    exact ⟨fn, by rw [h1]; exact hf, hp, by rw [h2]; exact hb, by omega⟩
  · obtain ⟨fn, hf, hp, hb⟩ := osL_fm32
    exact ⟨fn, by rw [h1]; exact hf, hp, by rw [h2]; exact hb, by omega⟩

/-- **Each configuration's body facts.** -/
theorem osL_bodyFacts (j : ℕ) (hj : j < 28) : OsBodyFacts (osCfgs.getD j default) := by
  have h := osAllBodyFacts
  interval_cases j
  exacts [h.b0, h.b1, h.b2, h.b3, h.b4, h.b5, h.b6, h.b7, h.b8, h.b9, h.b10, h.b11, h.b12, h.b13,
    h.b14, h.b15, h.b16, h.b17, h.b18, h.b19, h.b20, h.b21, h.b22, h.b23, h.b24, h.b25, h.b26, h.b27]

end
end LeanVM.Guest.B1
