/-
  LeanVM.Guest.B1.Comp.Whir.Loc.G1C

  `open_stacked`'s callees from group 1, placed, over a completeness model.
-/

module

public import LeanVM.Guest.B1.Comp.Whir.Loc.OsCallees
public import LeanVM.Guest.B1.Comp.FreeTree
public import LeanVM.Guest.B1.OsCalleesPlaced
public import LeanVM.Guest.B1.G1BoundsAt
public import LeanVM.Guest.Memory.GuestBoundsAtB

/-!
# Group 1's callees of `open_stacked`, placed, over a completeness model

The fields of `OsCalleesAtBC CM` at the bounds of the deployed `osCalleesAtB` (`g1BoundsOf`):

* the callees free of `BLAKE2S` (`assert_canonical`, the row weights, the final folds, the position
  decoders) are the deployed placed lemmas under any semantics (`completeAtBS_of_freeOn`,
  `relAtInB_freeOn`);
* `opening_fold` and the final messages are pure: complete on their meanings over the model
  (`MeaningOpeningFoldComp`, `MeaningOpeningFinalMessageComp`, `opening_fold_comp`,
  `opening_final_message_L*_comp`), by trees within the static bounds under `CM.sem`
  (`GuestBoundsAtB`);
* `opening_ood_point` and `grind_check` (`G1C2.lean`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub
open LeanVM.Guest.B1.Main (MemL RegionL)
open LeanVM.E2E.Complete

@[expose] public section

variable {CM : CompModel}

/-- `CompleteMemB` over the model: `f` complete under `CM.sem` on every precondition holding on
every memory holding the caller's words. -/
def CompleteMemBC (CM : CompModel) (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (f : String)
    (Pre : Reader → List E → List E → Prop) (B : List E → ℕ) : Prop :=
  ∀ (args rets : List E) (Lin : Main.Layout), (∀ rd, MemL rd Lin → Pre rd args rets) →
    CompleteAtBS CM.sem fs cert k f Lin args (Returns rets) (B args)

/-- **A pure function over the model is complete on a meaning that gives its relation**
(`completeMem_of_iffB`). -/
theorem completeMem_of_compBC {fs : String → ℕ} {cert : String → V → ℕ} {Sz : List String}
    (hS : coreProgram.PureIn Sz) {f : String} (hf : f ∈ Sz) {M : Reader → List E → List E → Prop}
    (hrel : ∀ rd args rets, M rd args rets → coreProgram.RelB CM.sem rd f args rets) (k : ℕ)
    {B : List E → ℕ} (hB : TotalLeB CM.sem coreProgram fs f B) : CompleteMemBC CM fs cert k f M B :=
  fun _ _ _ h => completeAtS_of_rel_pureB hS hf (fun rd hL => hrel rd _ _ (h rd hL)) k
    fun rd t a r hn hv hb => hB rd t a r hn hv hb

/-- `completeRel_of_liftB` over the model. -/
theorem completeRel_of_liftBC {fs : String → ℕ} {cert : String → V → ℕ} {k : ℕ} {f : String}
    {Pre : Reader → List E → List E → Prop} {B : List E → ℕ} (h : CompleteMemBC CM fs cert k f Pre B)
    (hlift : ∀ (args rets : List E) (Lin : Main.Layout) (rd1 : Reader), LowDef k rd1 → MemL rd1 Lin →
      (∀ rd, LowDef k rd → MemL rd Lin → Pre rd args rets) → ∀ rd, MemL rd Lin → Pre rd args rets) :
    CompleteRelBAC CM fs cert k f Pre B := by
  intro args rets Lin hpre fp
  classical
  by_cases hex : ∃ rd1, LowDef k rd1 ∧ MemL rd1 Lin
  · obtain ⟨rd1, hl1, hL1⟩ := hex
    exact h args rets Lin (hlift args rets Lin rd1 hl1 hL1 hpre) fp
  · exact ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, Nat.zero_le _, fun rd hl hL =>
      absurd ⟨rd, hl, by simpa using hL⟩ hex⟩

variable (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)

set_option maxRecDepth 100000 in
/-- **`opening_fold`, placed, over the model.** -/
theorem opening_fold_completeRelBC (B : List E → ℕ) (hB : TotalLeB CM.sem coreProgram fs "opening_fold" B) :
    CompleteRelBAC CM fs cert k "opening_fold" (MeaningOpeningFoldComp CM) B := by
  refine completeRel_of_liftBC (completeMem_of_compBC (g1_pure_one find_opening_fold (by decide +kernel))
    (by simp) (fun rd a r h => opening_fold_comp rd a r h) k hB) fun args rets Lin rd1 hl1 hL1 hpre => ?_
  obtain ⟨s0, s1, cur, c0, c1, c2, rfl⟩ : ∃ s0 s1 cur c0 c1 c2, args = [s0, s1, cur, c0, c1, c2] := by
    match args, hpre rd1 hl1 hL1 with
    | [a, b, c, d, e, f], _ => exact ⟨a, b, c, d, e, f, rfl⟩
  have hr : ∀ rd, LowDef k rd → MemL rd Lin → ReadsAt rd cur [rets.getD 4 0, rets.getD 5 0] := by
    intro rd hl hL
    obtain ⟨_, _, _, _, _, _, _, -, hR, -, rfl⟩ := hpre rd hl hL
    exact hR
  have hr' := (readsAt_lift hl1 hL1 hr).2
  intro rd hL
  obtain ⟨cv, d0, d2, r, t, q, cv', hcv, -, hrun, rfl⟩ := hpre rd1 hl1 hL1
  exact ⟨cv, d0, d2, r, t, q, cv', hcv, hr' rd hL, hrun, rfl⟩

set_option maxRecDepth 100000 in
theorem ofm_L4_completeMemBC (B : List E → ℕ) (hB : TotalLeB CM.sem coreProgram fs "opening_final_message__L4" B) :
    OsFinalMsgAtBC CM fs cert k "opening_final_message__L4" 4 B :=
  completeMem_of_compBC (g1_pure_one (Program.find?_of_indexOf? (n := "opening_final_message__L4") (j := 616)
    (by decide +kernel) rfl) (by decide +kernel)) (by simp) (fun rd a r h => opening_final_message_L4_comp rd a r h) k hB

set_option maxRecDepth 100000 in
theorem ofm_L8_completeMemBC (B : List E → ℕ) (hB : TotalLeB CM.sem coreProgram fs "opening_final_message__L8" B) :
    OsFinalMsgAtBC CM fs cert k "opening_final_message__L8" 8 B :=
  completeMem_of_compBC (g1_pure_one (Program.find?_of_indexOf? (n := "opening_final_message__L8") (j := 631)
    (by decide +kernel) rfl) (by decide +kernel)) (by simp) (fun rd a r h => opening_final_message_L8_comp rd a r h) k hB

set_option maxRecDepth 100000 in
theorem ofm_L16_completeMemBC (B : List E → ℕ) (hB : TotalLeB CM.sem coreProgram fs "opening_final_message__L16" B) :
    OsFinalMsgAtBC CM fs cert k "opening_final_message__L16" 16 B :=
  completeMem_of_compBC (g1_pure_one (Program.find?_of_indexOf? (n := "opening_final_message__L16") (j := 588)
    (by decide +kernel) rfl) (by decide +kernel)) (by simp) (fun rd a r h => opening_final_message_L16_comp rd a r h) k hB

set_option maxRecDepth 100000 in
theorem ofm_L32_completeMemBC (B : List E → ℕ) (hB : TotalLeB CM.sem coreProgram fs "opening_final_message__L32" B) :
    OsFinalMsgAtBC CM fs cert k "opening_final_message__L32" 32 B :=
  completeMem_of_compBC (g1_pure_one (Program.find?_of_indexOf? (n := "opening_final_message__L32") (j := 602)
    (by decide +kernel) rfl) (by decide +kernel)) (by simp) (fun rd a r h => opening_final_message_L32_comp rd a r h) k hB

/-- The position decoders are free of `BLAKE2S`. -/
theorem osDq_freeOn : ∀ p ∈ osDqNames, coreProgram.FreeOn [p.2] = true := by
  intro p hp
  simp only [osDqNames, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

/-- **A position decoder, placed, over the model**: the deployed one (`relAtInB_freeOn`). -/
theorem osDecodeAtDC_of {d : ℕ} {name : String} (hfree : coreProgram.FreeOn [name] = true)
    (h : OsDecodeAtD fs cert k d name) : OsDecodeAtDC CM fs cert k d name := by
  intro w pos ptrs Lin fp hpre
  obtain ⟨Lown, hW, hD, hr⟩ := h w pos ptrs Lin fp hpre
  refine ⟨Lown, hW, hD, fun rd hl hm => ?_⟩
  have := hr rd hl hm
  rw [← relAtInB_deployed] at this
  exact (relAtInB_freeOn (S := CM.sem) hfree (List.mem_singleton_self _)).mpr this

end
end LeanVM.Guest.B1
