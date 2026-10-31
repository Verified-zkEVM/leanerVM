/-
  LeanVM.Guest.Located.Basic

  Frames of the memory, the first one passing a test, and witnesses read off a call's frame or a
  loop's frames.
-/

module

public import LeanVM.Guest.CertName

/-!
# Frames

A located call (`Check.RL coreProgram L certByName`, `RLg L` here) runs at a frame `g^a` of the
memory, `a < 2^κ` (`Check.InMem`), under its certificate's valuation there (`valAt`). A witness is
read off the first frame passing a Boolean test (`firstFrame`). The frame of a call (`frameOf`) is
the first at which the callee's code holds on the call's words (`BodyAt`), a classical test of the
guest's own semantics (the callee's core IR body under the located relation, its in-circuit
checks such as `KECCAK`'s `KeccakCellsRelation` included). The decoder computes no hash and runs no
verifier of its own.

* `frameDec L f wit args rets`: the witness `wit` reads off the valuation of the call's frame;
  `frameDec_spec`: whatever the callee's body gives at any of its frames, the decoded witness has.
* `loopDec L f Wf wit args rets`: a `mul_range` loop helper's witnesses, iteration `j` read off
  the frame of the iteration's call `x·g^j :: ps`, for the `loopCount x (Wf ps)` iterations up to
  the loop's end; `loopDec_spec`: a located loop call holds each iteration's outcome at the
  decoded witnesses (`LoopW`).
* `rlg_le_rel`: the located relation lies below `coreProgram.Rel`; it unfolds along the memory's
  frame map (`Located.unfoldsV_RL`, `Located/Interface.lean`).
-/

namespace LeanVM.Guest.Located

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Check
open LeanVM.Protocol.Verifier

@[expose] public section

/-- **The guest's located call relation** on the memory `L`. -/
noncomputable abbrev RLg {κ : ℕ} (L : MemoryImage κ) : CallRel := RL coreProgram L certByName

/-- The valuation of the guest function `f` with the memory's word `a` as its frame. -/
noncomputable def valAt {κ : ℕ} (L : MemoryImage κ) (f : String) (a : ℕ) : Val :=
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

/-! ## The located relation -/

/-- The located relation lies below the relation. -/
theorem rlg_le_rel {κ : ℕ} (L : MemoryImage κ) : CallRel.Le (RLg L) (coreProgram.Rel L.read) :=
  relL_le_rel coreProgram

/-! ## The frame the guest's code ran at -/

/-- **The guest's code for `f` holds at the memory's frame `a`** on the argument words `args` and
the return words `rets`: its body, under the frame's valuation, its calls located. -/
def BodyAt {κ : ℕ} (L : MemoryImage κ) (f : String) (args rets : List E) (a : ℕ) : Prop :=
  ∃ fn, coreProgram.find? f = some fn ∧ fn.params.map (valAt L f a) = args ∧
    Stmt.HoldsList (RLg L) L.read (valAt L f a) fn.body False (fun rs ↦ rs = rets)

open Classical in
/-- **The frame of a call**: the first frame of the memory at which the callee's code holds on the
call's words, decided classically: the test is the guest's own semantics (the callee's core IR
body under the located relation, its in-circuit checks included); it computes no hash and runs no
verifier of its own. -/
noncomputable def frameOf {κ : ℕ} (L : MemoryImage κ) (f : String) (args rets : List E) : ℕ :=
  match firstFrame κ (fun a ↦ decide (BodyAt L f args rets a)) with
  | some a => a
  | none => 0

/-- A located call's callee holds at the call's frame. -/
theorem bodyAt_frameOf {κ : ℕ} {L : MemoryImage κ} {f : String} {args rets : List E}
    (h : RLg L f args rets) : BodyAt L f args rets (frameOf L f args rets) := by
  classical
  obtain ⟨fn, fp, hf, ⟨a, ha, rfl⟩, hp, hb⟩ := (relL_iff coreProgram f args rets).mp h
  obtain ⟨b, hb', ht⟩ := firstFrame_some (t := fun a ↦ decide (BodyAt L f args rets a)) ha
    (decide_eq_true ⟨fn, hf, hp, hb⟩)
  unfold frameOf
  rw [hb']
  exact of_decide_eq_true ht

/-- At the call's frame, the callee's body holds, the callee being `fn`. -/
theorem body_frameOf {κ : ℕ} {L : MemoryImage κ} {f : String} {fn : Fn}
    (hf : coreProgram.find? f = some fn) {args rets : List E} (h : RLg L f args rets) :
    fn.params.map (valAt L f (frameOf L f args rets)) = args ∧
      Stmt.HoldsList (RLg L) L.read (valAt L f (frameOf L f args rets)) fn.body False
        (fun rs ↦ rs = rets) := by
  obtain ⟨fn', hf', hp, hb⟩ := bodyAt_frameOf h
  rw [hf] at hf'
  cases hf'
  exact ⟨hp, hb⟩

/-! ## Decoding a frame -/

/-- **The witness `wit` reads off the frame of a call** (`frameOf`). -/
noncomputable def frameDec {κ : ℕ} {α : Type} (L : MemoryImage κ) (f : String) (wit : Val → α)
    (args rets : List E) : α :=
  wit (valAt L f (frameOf L f args rets))

/-! ## Decoding a loop -/

/-- **The iterations of a `mul_range` loop from `x` to `W`**: the first `m ≥ 1` with `x·g^m = W`
(`0` if none), by a definite search. -/
noncomputable def loopCount (x W : E) : ℕ :=
  open Classical in if h : ∃ m, 0 < m ∧ x * gen ^ m = W then Nat.find h else 0

/-- **A loop's outcome at its iterations' witnesses** `ws`: `m = ws.length ≥ 1` iterations from
`x` to its end `W = x·g^m`, the first such, iteration `j` with the outcome `B (x·g^j) ws[j]`. -/
def LoopW {α : Type} (x W : E) (B : E → α → Prop) (ws : List α) : Prop :=
  0 < ws.length ∧ W = x * gen ^ ws.length ∧ (∀ j, 0 < j → j < ws.length → x * gen ^ j ≠ W) ∧
    ∀ j (hj : j < ws.length), B (x * gen ^ j) ws[j]

/-- **A loop's witnesses, iteration by iteration**: for a call `x :: ps`, iteration
`j < loopCount` at `x·g^j` is the witness of the frame of the iteration's call `x·g^j :: ps`;
`W = Wf ps` is the loop's end. -/
noncomputable def loopDec {κ : ℕ} {α : Type} (L : MemoryImage κ) (f : String)
    (Wf : List E → E) (wit : Val → α) (args _rets : List E) : List α :=
  match args with
  | [] => []
  | x :: ps => (List.range (loopCount x (Wf ps))).map fun j => frameDec L f wit (x * gen ^ j :: ps) []

end
end LeanVM.Guest.Located
