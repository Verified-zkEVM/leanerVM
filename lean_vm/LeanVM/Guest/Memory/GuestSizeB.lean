/-
  LeanVM.Guest.Memory.GuestSizeB

  The words of the guest's self-calling functions (`GuestSize.lean`) under any semantics of
  `BLAKE2S`.
-/

module

public import LeanVM.Guest.Memory.GuestSize
public import LeanVM.Guest.Memory.SizeTotalB
public import LeanVM.Guest.Memory.StaticSoundB

/-!
# Words of the guest's self-calling functions under any `BLAKE2S` semantics

`GuestSize.lean`'s `TotalLe` bounds as `TotalLeB S` (`assertB_canonical_totalLe`,
`loop84B_totalLe`, `loop85B_totalLe`), from the same kernel-checked facts.

Made by `mkB.py` from the generated `GuestSize.lean` (W2-1's pattern, `docs/roadmap/t6-completeness.md` (removed; in git at `6ffa1d1f`)
§4.2): remake it, do not edit it, when that file is regenerated.
-/

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Value Core Memory Data

@[expose] public section

variable {S : BlakeSem}

private theorem j1 : 1 < coreProgram.length := by rw [coreProgram_length]; decide
private theorem j174 : 174 < coreProgram.length := by rw [coreProgram_length]; decide
private theorem j175 : 175 < coreProgram.length := by rw [coreProgram_length]; decide

/-- **`assert_canonical` allocates its frame.** -/
theorem assertB_canonical_totalLe (fs : String → ℕ) :
    TotalLeB S coreProgram fs "assert_canonical" fun _ => fs "assert_canonical" := by
  have hn : (coreProgram[1]'j1).name = "assert_canonical" := by decide +kernel
  obtain ⟨hl, hc⟩ := self_hyps (fs := fs) j1 hn (by decide +kernel) (w := (0, [])) (by decide +kernel)
  have hcf : staticCertOf "assert_canonical" = .stat [] ⟨8, []⟩ [] := by
    rw [certOf_of_idx (j := 1) (by decide +kernel)]; rfl
  have hω : omegaOf "assert_canonical" = 8 := by
    rw [omegaOf_of_idx (j := 1) (by decide +kernel)]; rfl
  intro rd t args rets htn hv hb
  have hw := weightLeB_of_stat coreProgram_checked hcf rd t args rets htn hv hb
  have := totalB_le_self (ω := omegaOf) (n := 1) hl hc htn hv hb (by rw [hω]; decide) (by rw [hω]; simpa using hw)
  simpa [wordsVal_zero] using this

/-- **`__loop84` from `g^a` to its end `g^64`**: `64 - a` instances, each its frame and the
phantom's. -/
theorem loop84B_totalLe (fs : String → ℕ) :
    TotalLeOnB S coreProgram fs "__loop84" (fun args => ∃ a, args.getD 0 0 = ofK (gpow a) ∧ a < 64)
      fun args => (64 - logG (args.getD 0 0)) * (2 * fs "__loop84") := by
  have hn : (coreProgram[174]'j174).name = "__loop84" := by decide +kernel
  obtain ⟨hl, hc⟩ := self_hyps (fs := fs) j174 hn (by decide +kernel) (w := (0, ["__loop84"]))
    (by decide +kernel)
  have hcf : staticCertOf "__loop84" = .loop (some 64) [] ⟨109, []⟩ [] := by
    rw [certOf_of_idx (j := 174) (by decide +kernel)]; rfl
  have hω : omegaOf "__loop84" = 109 := by
    rw [omegaOf_of_idx (j := 174) (by decide +kernel)]; rfl
  intro rd t args rets htn ⟨a, ha, ha64⟩ hv hb
  have hw := weightB_le_of_loop coreProgram_checked hcf htn hv hb ha rfl ha64 (by decide)
    (fun _ h => (List.not_mem_nil h).elim)
  have := totalB_le_self (ω := omegaOf) (n := 64 - a) hl hc htn hv hb (by rw [hω]; decide)
    (by rw [hω]; simpa [Aff.eval] using hw)
  dsimp only
  rw [ha, logG_spec (by omega)]
  simpa [wordsVal_self, two_mul] using this

/-- **`__loop85` from `g^a` to its end `g^e`, its second argument**: `e - a` instances, each its
frame and the phantom's. -/
theorem loop85B_totalLe (fs : String → ℕ) :
    TotalLeOnB S coreProgram fs "__loop85"
      (fun args => ∃ a e, args.getD 0 0 = ofK (gpow a) ∧ args.getD 1 0 = ofK (gpow e) ∧ a < e ∧
        e < 2 ^ 64 - 1)
      fun args => (logG (args.getD 1 0) - logG (args.getD 0 0)) * (2 * fs "__loop85") := by
  have hn : (coreProgram[175]'j175).name = "__loop85" := by decide +kernel
  obtain ⟨hl, hc⟩ := self_hyps (fs := fs) j175 hn (by decide +kernel) (w := (0, ["__loop85"]))
    (by decide +kernel)
  have hcf : staticCertOf "__loop85" = .loop none [] ⟨20, []⟩ [] := by
    rw [certOf_of_idx (j := 175) (by decide +kernel)]; rfl
  have hω : omegaOf "__loop85" = 20 := by
    rw [omegaOf_of_idx (j := 175) (by decide +kernel)]; rfl
  intro rd t args rets htn ⟨a, e, ha, he, hae, heo⟩ hv hb
  have hw := weightB_le_of_loop coreProgram_checked hcf htn hv hb ha he hae heo
    (fun _ h => (List.not_mem_nil h).elim)
  have := totalB_le_self (ω := omegaOf) (n := e - a) hl hc htn hv hb (by rw [hω]; decide)
    (by rw [hω]; simpa [Aff.eval] using hw)
  dsimp only
  rw [ha, he, logG_spec heo, logG_spec (by omega)]
  simpa [wordsVal_self, two_mul] using this

end
end LeanVM.Guest
