/-
  LeanVM.Guest.Located.BasicB

  Frames of the memory under any semantics of `BLAKE2S`: the frame a located call ran at, the guest's
  code holding there under `S` (`Located/Basic.lean` over `S`).
-/

module

public import LeanVM.Guest.Located.Basic
public import LeanVM.Guest.CheckSoundB

/-!
# Frames under any semantics

`Basic.lean`'s frame of a call (`frameOf`) is the first frame of the memory at which the callee's
code holds on the call's words under the deployed semantics (`BodyAt`). Under a semantics `S` of
`BLAKE2S` the guest's located calls are `Check.RLB S`, and the frame a decoder reads is the first at
which the callee's code holds under `S` (`BodyAtB S`, `frameOfB S`): the test is the guest's own
semantics, now `S`'s, and the decoder still verifies nothing. At the deployed semantics it is
`frameOf` (`frameOfB_deployed`), so every decoder built on `frameOfB S` is the deployed one at
`blakeDeployed`.
-/

namespace LeanVM.Guest.Located

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Check

@[expose] public section

variable (S : BlakeSem)

/-- **The guest's code for `f` holds under `S` at the memory's frame `a`** on the argument words
`args` and the return words `rets` (`BodyAt` under `S`). -/
def BodyAtB {κ : ℕ} (L : MemImage κ) (f : String) (args rets : List E) (a : ℕ) : Prop :=
  ∃ fn, coreProgram.find? f = some fn ∧ fn.params.map (valAt L f a) = args ∧
    Stmt.HoldsListB S (RLB S coreProgram L certByName) L.read (valAt L f a) fn.body False
      (fun rs ↦ rs = rets)

open Classical in
/-- **The frame of a call under `S`** (`frameOf` under `S`): the first frame of the memory at
which the callee's code holds under `S` on the call's words. -/
noncomputable def frameOfB {κ : ℕ} (L : MemImage κ) (f : String) (args rets : List E) : ℕ :=
  match firstFrame κ (fun a ↦ decide (BodyAtB S L f args rets a)) with
  | some a => a
  | none => 0

variable {S}

/-- A located call's callee holds under `S` at the call's frame. -/
theorem bodyAt_frameOfB {κ : ℕ} {L : MemImage κ} {f : String} {args rets : List E}
    (h : RLB S coreProgram L certByName f args rets) :
    BodyAtB S L f args rets (frameOfB S L f args rets) := by
  classical
  obtain ⟨fn, fp, hf, ⟨a, ha, rfl⟩, hp, hb⟩ := (relLB_iff coreProgram f args rets).mp h
  obtain ⟨b, hb', ht⟩ := firstFrame_some (t := fun a ↦ decide (BodyAtB S L f args rets a)) ha
    (decide_eq_true ⟨fn, hf, hp, hb⟩)
  unfold frameOfB
  rw [hb']
  exact of_decide_eq_true ht

/-- At the call's frame under `S`, the callee's body holds under `S`, the callee being `fn`. -/
theorem body_frameOfB {κ : ℕ} {L : MemImage κ} {f : String} {fn : Fn}
    (hf : coreProgram.find? f = some fn) {args rets : List E}
    (h : RLB S coreProgram L certByName f args rets) :
    fn.params.map (valAt L f (frameOfB S L f args rets)) = args ∧
      Stmt.HoldsListB S (RLB S coreProgram L certByName) L.read
        (valAt L f (frameOfB S L f args rets)) fn.body False (fun rs ↦ rs = rets) := by
  obtain ⟨fn', hf', hp, hb⟩ := bodyAt_frameOfB h
  rw [hf] at hf'
  cases hf'
  exact ⟨hp, hb⟩

/-- At the deployed semantics the located relation under `S` is the deployed one. -/
theorem rlB_deployed {κ : ℕ} (L : MemImage κ) :
    RLB blakeDeployed coreProgram L certByName = RL coreProgram L certByName :=
  relLB_deployed _ _ _ _

/-- At the deployed semantics the test is `BodyAt`. -/
theorem bodyAtB_deployed {κ : ℕ} (L : MemImage κ) (f : String) (args rets : List E) (a : ℕ) :
    BodyAtB blakeDeployed L f args rets a ↔ BodyAt L f args rets a := by
  simp only [BodyAtB, BodyAt, rlB_deployed, holdsListB_deployed]

/-- **At the deployed semantics the frame is `frameOf`.** -/
theorem frameOfB_deployed {κ : ℕ} (L : MemImage κ) (f : String) (args rets : List E) :
    frameOfB blakeDeployed L f args rets = frameOf L f args rets := by
  unfold frameOfB frameOf
  congr 2
  funext a
  exact decide_eq_decide.mpr (bodyAtB_deployed L f args rets a)

end
end LeanVM.Guest.Located
