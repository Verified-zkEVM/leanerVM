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

/-- **A located call's frame**: a frame of the memory where the callee's body holds under its
valuation, its own calls located. -/
theorem rl_frame {κ : ℕ} {L : MemoryImage κ} {f : String} {fn : Fn}
    (hf : coreProgram.find? f = some fn) {args rets : List E} (h : RLg L f args rets) :
    ∃ a < 2 ^ κ, fn.params.map (valAt L f a) = args ∧
      Stmt.HoldsList (RLg L) L.read (valAt L f a) fn.body False (fun rs => rs = rets) := by
  obtain ⟨fn', fp, hf', ⟨a, ha, rfl⟩, hp, hb⟩ := (relL_iff coreProgram f args rets).mp h
  rw [hf] at hf'
  cases hf'
  exact ⟨a, ha, hp, hb⟩

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

/-- **What the callee's body gives at any of its frames, the decoded witness has**, for a located
call. -/
theorem frameDec_spec {κ : ℕ} {L : MemoryImage κ} {α : Type} {f : String} {fn : Fn}
    (hf : coreProgram.find? f = some fn) {wit : Val → α} {args rets : List E}
    (h : RLg L f args rets) {t : α → Prop}
    (hT : ∀ a, fn.params.map (valAt L f a) = args →
      Stmt.HoldsList (RLg L) L.read (valAt L f a) fn.body False (fun rs => rs = rets) →
        t (wit (valAt L f a))) :
    t (frameDec L f wit args rets) := by
  obtain ⟨hp, hb⟩ := body_frameOf hf h
  exact hT _ hp hb

/-! ## Decoding a loop -/

/-- **The iterations of a `mul_range` loop from `x` to `W`**: the first `m ≥ 1` with `x·g^m = W`
(`0` if none), by a definite search. -/
noncomputable def loopCount (x W : E) : ℕ :=
  open Classical in if h : ∃ m, 0 < m ∧ x * gen ^ m = W then Nat.find h else 0

theorem loopCount_eq {x W : E} {m : ℕ} (hm : 0 < m) (hW : W = x * gen ^ m)
    (hfirst : ∀ j, 0 < j → j < m → x * gen ^ j ≠ W) : loopCount x W = m := by
  classical
  have h : ∃ m, 0 < m ∧ x * gen ^ m = W := ⟨m, hm, hW.symm⟩
  unfold loopCount
  split
  · rename_i h'
    exact (Nat.find_eq_iff h').mpr ⟨⟨hm, hW.symm⟩, fun n hn ⟨h0, he⟩ => hfirst n h0 hn he⟩
  · contradiction

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

/-- **A located loop's frames**, by induction on the call's depth: given that one frame of the loop
(under any call relation below the located one) has parameters `x :: ps`, its iteration's
outcome and, short of the end, the call on at `x·g`, the loop runs `m ≥ 1` iterations to its end,
each at a frame of the memory. -/
theorem loop_frames {κ : ℕ} {L : MemoryImage κ} {α : Type} {f : String} {fn : Fn}
    (hf : coreProgram.find? f = some fn) {Wf : List E → E} {B : E → List E → α → Prop}
    {wit : Val → α}
    (step : ∀ C : CallRel, CallRel.Le C (RLg L) → ∀ (σ : Val) (args rets : List E),
      fn.params.map σ = args → Stmt.HoldsList C L.read σ fn.body False (fun rs => rs = rets) →
      ∃ x ps, args = x :: ps ∧ rets = [] ∧ B x ps (wit σ) ∧ (x * gen ≠ Wf ps → C f (x * gen :: ps) []))
    (n : ℕ) : ∀ args rets, coreProgram.locN L.read (frameVal L certByName) (InMem κ) n f args rets →
      ∃ x ps, args = x :: ps ∧ rets = [] ∧ ∃ m, 0 < m ∧ Wf ps = x * gen ^ m ∧
        (∀ j, 0 < j → j < m → x * gen ^ j ≠ Wf ps) ∧
        ∀ j < m, RLg L f (x * gen ^ j :: ps) [] := by
  induction n with
  | zero => intro _ _ h; exact h.elim
  | succ n ih =>
    intro args rets h
    have hRL : RLg L f args rets := ⟨n + 1, h⟩
    obtain ⟨fn', fp, hf', ⟨a, ha, rfl⟩, hp, hb⟩ := h
    rw [hf] at hf'
    cases hf'
    obtain ⟨x, ps, rfl, rfl, -, hnext⟩ := step _ (locN_le_relL coreProgram n) _ _ _ hp hb
    refine ⟨x, ps, rfl, rfl, ?_⟩
    by_cases hW : x * gen = Wf ps
    · refine ⟨1, one_pos, by rw [pow_one, hW], fun j h1 h2 => by omega, fun j hj => ?_⟩
      rw [show j = 0 by omega, pow_zero, mul_one]
      exact hRL
    · obtain ⟨x', ps', he, -, m, hm, hWm, hfirst, hall⟩ := ih _ _ (hnext hW)
      simp only [List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      refine ⟨m + 1, by omega, by rw [hWm, pow_succ', mul_assoc], fun j h1 h2 => ?_, fun j hj => ?_⟩
      · rcases Nat.lt_or_ge j 2 with hj | hj
        · rw [show j = 1 by omega, pow_one]; exact hW
        · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
          rw [pow_succ', ← mul_assoc]; exact hfirst i (by omega) (by omega)
      · cases j with
        | zero => rw [pow_zero, mul_one]; exact hRL
        | succ i => rw [pow_succ', ← mul_assoc]; exact hall i (by omega)

/-- **A located loop call holds its loop's outcome at the decoded iterations.** -/
theorem loopDec_spec {κ : ℕ} {L : MemoryImage κ} {α : Type} {f : String} {fn : Fn}
    (hf : coreProgram.find? f = some fn) {Wf : List E → E} {B : E → List E → α → Prop}
    {wit : Val → α}
    (step : ∀ C : CallRel, CallRel.Le C (RLg L) → ∀ (σ : Val) (args rets : List E),
      fn.params.map σ = args → Stmt.HoldsList C L.read σ fn.body False (fun rs => rs = rets) →
      ∃ x ps, args = x :: ps ∧ rets = [] ∧ B x ps (wit σ) ∧ (x * gen ≠ Wf ps → C f (x * gen :: ps) []))
    {args rets : List E} (h : RLg L f args rets) :
    ∃ x ps, args = x :: ps ∧ rets = [] ∧
      LoopW x (Wf ps) (fun y a => B y ps a) (loopDec L f Wf wit args rets) := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨x, ps, rfl, rfl, m, hm, hW, hfirst, hall⟩ := loop_frames hf step n _ _ hn
  refine ⟨x, ps, rfl, rfl, ?_⟩
  show LoopW x (Wf ps) _ ((List.range (loopCount x (Wf ps))).map _)
  rw [loopCount_eq hm hW hfirst]
  refine ⟨by simpa using hm, by simpa using hW, fun j h1 h2 => hfirst j h1 (by simpa using h2),
    fun j hj => ?_⟩
  simp only [List.getElem_map, List.getElem_range]
  refine frameDec_spec hf (hall j (by simpa using hj)) fun a hp hb => ?_
  obtain ⟨x', ps', he, -, hB, -⟩ := step _ (fun _ _ _ h => h) _ _ _ hp hb
  simp only [List.cons.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact hB

end
end LeanVM.Guest.Located
