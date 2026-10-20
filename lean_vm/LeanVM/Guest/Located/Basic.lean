/-
  LeanVM.Guest.Located.Basic

  Frames of the memory and the first one passing a test.
-/

module

public import LeanVM.Guest.CertName

/-!
# Frames

A located call runs at a frame `g^a` of the memory, `a < 2^κ` (`Check.InMem`), under its
certificate's valuation there (`valAt`). A witness is read off the first frame passing a Boolean
test (`firstFrame`). The frame of a call (`frameOf`) is the first at which the callee's code holds
on the call's words (`BodyAt`): the guest's own semantics is the only test, the decoder verifies
nothing.
-/

namespace LeanVM.Guest.Located

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Check

@[expose] public section

/-- The valuation of the guest function `f` with the memory's word `a` as its frame. -/
noncomputable def valAt {κ : ℕ} (L : MemImage κ) (f : String) (a : ℕ) : Val :=
  frameVal L certByName f (gpow a)

/-- The first frame `a < 2^κ` passing the test `t`. -/
def firstFrame (κ : ℕ) (t : ℕ → Bool) : Option ℕ := (List.range (2 ^ κ)).find? t

/-- A frame passing the test makes the scan find one. -/
theorem firstFrame_some {κ : ℕ} {t : ℕ → Bool} {a : ℕ} (ha : a < 2 ^ κ) (h : t a = true) :
    ∃ b, firstFrame κ t = some b ∧ t b = true := by
  unfold firstFrame
  rcases hf : (List.range (2 ^ κ)).find? t with _ | b
  · exact absurd h (by simpa using List.find?_eq_none.mp hf a (List.mem_range.mpr ha))
  · exact ⟨b, rfl, List.find?_some hf⟩

/-! ## The frame the guest's code ran at -/

/-- **The guest's code for `f` holds at the memory's frame `a`** on the argument words `args` and
the return words `rets`: its body, under the frame's valuation, its calls located. -/
def BodyAt {κ : ℕ} (L : MemImage κ) (f : String) (args rets : List E) (a : ℕ) : Prop :=
  ∃ fn, coreProgram.find? f = some fn ∧ fn.params.map (valAt L f a) = args ∧
    Stmt.HoldsList (RL coreProgram L certByName) L.read (valAt L f a) fn.body False
      (fun rs ↦ rs = rets)

open Classical in
/-- **The frame of a call**: the first frame of the memory at which the callee's code holds on the
call's words. It checks nothing itself: the only test is the guest's own semantics. -/
noncomputable def frameOf {κ : ℕ} (L : MemImage κ) (f : String) (args rets : List E) : ℕ :=
  match firstFrame κ (fun a ↦ decide (BodyAt L f args rets a)) with
  | some a => a
  | none => 0

/-- A located call's callee holds at the call's frame. -/
theorem bodyAt_frameOf {κ : ℕ} {L : MemImage κ} {f : String} {args rets : List E}
    (h : RL coreProgram L certByName f args rets) : BodyAt L f args rets (frameOf L f args rets) := by
  classical
  obtain ⟨fn, fp, hf, ⟨a, ha, rfl⟩, hp, hb⟩ := (relL_iff coreProgram f args rets).mp h
  obtain ⟨b, hb', ht⟩ := firstFrame_some (t := fun a ↦ decide (BodyAt L f args rets a)) ha
    (decide_eq_true ⟨fn, hf, hp, hb⟩)
  unfold frameOf
  rw [hb']
  exact of_decide_eq_true ht

/-- At the call's frame, the callee's body holds, the callee being `fn`. -/
theorem body_frameOf {κ : ℕ} {L : MemImage κ} {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    {args rets : List E} (h : RL coreProgram L certByName f args rets) :
    fn.params.map (valAt L f (frameOf L f args rets)) = args ∧
      Stmt.HoldsList (RL coreProgram L certByName) L.read (valAt L f (frameOf L f args rets))
        fn.body False (fun rs ↦ rs = rets) := by
  obtain ⟨fn', hf', hp, hb⟩ := bodyAt_frameOf h
  rw [hf] at hf'
  cases hf'
  exact ⟨hp, hb⟩

end
end LeanVM.Guest.Located
