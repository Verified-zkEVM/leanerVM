/-
  LeanVM.Guest.Located.Da

  The DA check's witnesses decoded from the memory: the frames of `da_verify`'s callees give the
  blob matrix it checks.
-/

module

public import LeanVM.Guest.Located.Basic
public import LeanVM.Guest.B1.Da.Verify

/-!
# The DA check's witnesses, located

`Da.Named` and `da_verify_sound_w` state each function of the DA check with its witness a
function of its valuation and of its callees' witness functions. Here each witness function is a
decoder of the memory `L`, and a located call (`Check.RL`) satisfies its callee's outcome at its
decoder's witness:

* a function called once (`da_verify_cell`, `da_vector_cell__L{final}`, `da_vector_dispatch`,
  `da_verify_column__L{store}`, `da_verify`) is decoded at the call's frame (`frameDec`, at
  `frameOf`: the first frame at which the callee's code holds on the call's words); every such
  frame gives the callee's outcome, so the decoded witness has it;
* a loop (`__loop484`, `__loop486`, `__loop90`, `__loop91`) is decoded iteration by iteration
  (`loopDec`): it has `loopCount x W` iterations, the first `m ≥ 1` with `x·g^m = W`, and
  iteration `j` is read at the frame of the iteration's call `x·g^j :: ps`. `loop_frames` gives
  each iteration's located call by induction on the depth of the first. No decoder calls itself:
  each is defined along the static call graph, and none verifies anything.

`daWit_out`: a located call of `da_verify` holds its DA claim at `wDaL L`.
-/

namespace LeanVM.Guest.Located

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Check
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Guest.Value LeanVM.Guest.B1.Digest

@[expose] public section

/-! ## Decoding a frame -/

/-- **The witness `wit` reads off the frame of a call** (`frameOf`): the first frame at which the
callee's code holds on the call's words. -/
noncomputable def frameDec {κ : ℕ} {α : Type} (L : MemImage κ) (f : String) (wit : Val → α)
    (args rets : List E) : α :=
  wit (valAt L f (frameOf L f args rets))

/-- **What the callee's body gives at any of its frames, the decoded witness has**, for a located
call. -/
theorem frameDec_spec {κ : ℕ} {L : MemImage κ} {α : Type} {f : String} {fn : Fn}
    (hf : coreProgram.find? f = some fn) {wit : Val → α} {args rets : List E}
    (h : RL coreProgram L certByName f args rets) {t : α → Prop}
    (hT : ∀ a, fn.params.map (valAt L f a) = args →
      Stmt.HoldsList (RL coreProgram L certByName) L.read (valAt L f a) fn.body False
        (fun rs => rs = rets) → t (wit (valAt L f a))) :
    t (frameDec L f wit args rets) := by
  obtain ⟨hp, hb⟩ := body_frameOf hf h
  exact hT _ hp hb

/-- **A located call's frame**: a frame of the memory where the callee's body holds under its
valuation, its own calls located. -/
theorem rl_frame {κ : ℕ} {L : MemImage κ} {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    {args rets : List E} (h : RL coreProgram L certByName f args rets) :
    ∃ a < 2 ^ κ, fn.params.map (valAt L f a) = args ∧
      Stmt.HoldsList (RL coreProgram L certByName) L.read (valAt L f a) fn.body False
        (fun rs => rs = rets) := by
  obtain ⟨fn', fp, hf', ⟨a, ha, rfl⟩, hp, hb⟩ := (relL_iff coreProgram f args rets).mp h
  rw [hf] at hf'
  cases hf'
  exact ⟨a, ha, hp, hb⟩

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

/-- **A loop's witnesses, iteration by iteration**: for a call `x :: ps`, iteration `j < loopCount`
at `x·g^j` is the witness of the frame of the iteration's call `x·g^j :: ps`; `W = Wf ps` is the
loop's end. -/
noncomputable def loopDec {κ : ℕ} {α : Type} (L : MemImage κ) (f : String)
    (Wf : List E → E) (wit : Val → α) (args _rets : List E) : List α :=
  match args with
  | [] => []
  | x :: ps => (List.range (loopCount x (Wf ps))).map fun j => frameDec L f wit (x * gen ^ j :: ps) []

/-- **A located loop's frames**, by induction on the call's depth: given that one frame of the loop
(under any call relation below the located one) has parameters `x :: ps`, its iteration's
outcome and, short of the end, the call on at `x·g`, the loop runs `m ≥ 1` iterations to its end,
each at a frame of the memory. -/
theorem loop_frames {κ : ℕ} {L : MemImage κ} {α : Type} {f : String} {fn : Fn}
    (hf : coreProgram.find? f = some fn) {Wf : List E → E} {B : E → List E → α → Prop}
    {wit : Val → α}
    (step : ∀ C : CallRel, CallRel.Le C (RL coreProgram L certByName) → ∀ (σ : Val) (args rets : List E),
      fn.params.map σ = args → Stmt.HoldsList C L.read σ fn.body False (fun rs => rs = rets) →
      ∃ x ps, args = x :: ps ∧ rets = [] ∧ B x ps (wit σ) ∧ (x * gen ≠ Wf ps → C f (x * gen :: ps) []))
    (n : ℕ) : ∀ args rets, coreProgram.locN L.read (frameVal L certByName) (InMem κ) n f args rets →
      ∃ x ps, args = x :: ps ∧ rets = [] ∧ ∃ m, 0 < m ∧ Wf ps = x * gen ^ m ∧
        (∀ j, 0 < j → j < m → x * gen ^ j ≠ Wf ps) ∧
        ∀ j < m, RL coreProgram L certByName f (x * gen ^ j :: ps) [] := by
  induction n with
  | zero => intro _ _ h; exact h.elim
  | succ n ih =>
    intro args rets h
    have hRL : RL coreProgram L certByName f args rets := ⟨n + 1, h⟩
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
theorem loopDec_spec {κ : ℕ} {L : MemImage κ} {α : Type} {f : String} {fn : Fn}
    (hf : coreProgram.find? f = some fn) {Wf : List E → E} {B : E → List E → α → Prop}
    {wit : Val → α}
    (step : ∀ C : CallRel, CallRel.Le C (RL coreProgram L certByName) → ∀ (σ : Val) (args rets : List E),
      fn.params.map σ = args → Stmt.HoldsList C L.read σ fn.body False (fun rs => rs = rets) →
      ∃ x ps, args = x :: ps ∧ rets = [] ∧ B x ps (wit σ) ∧ (x * gen ≠ Wf ps → C f (x * gen :: ps) []))
    {args rets : List E} (h : RL coreProgram L certByName f args rets) :
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

/-! ## The leaves -/

/-- `da_verify_cell`'s symbols, decoded. -/
noncomputable def wCellL {κ : ℕ} (L : MemImage κ) (args rets : List E) : List K :=
  frameDec L "da_verify_cell" vcSyms args rets

theorem wCellL_spec {κ : ℕ} {L : MemImage κ} {args rets : List E}
    (h : RL coreProgram L certByName "da_verify_cell" args rets) :
    CellOut L.read args rets (wCellL L args rets) := by
  exact frameDec_spec find_da_verify_cell h fun _ hp hb => da_verify_cell_out hp hb

/-- `da_vector_cell__L{final}`'s weights, decoded. -/
noncomputable def wVecL {κ : ℕ} (L : MemImage κ) (final : Bool) (args rets : List E) : List E :=
  frameDec L (vxName final) vxWs args rets

theorem wVecL_spec {κ : ℕ} {L : MemImage κ} {final : Bool} {args rets : List E}
    (h : RL coreProgram L certByName (vxName final) args rets) :
    VecOut final L.read args rets (wVecL L final args rets) := by
  exact frameDec_spec (find_vx final) h fun _ hp hb => da_vector_cell_out hp hb

/-- `da_vector_dispatch`'s weights, decoded. -/
noncomputable def wVdL {κ : ℕ} (L : MemImage κ) (args rets : List E) : List E :=
  frameDec L "da_vector_dispatch" (fun σ => vdWit σ (wVecL L)) args rets

theorem wVdL_spec {κ : ℕ} {L : MemImage κ} {args rets : List E}
    (h : RL coreProgram L certByName "da_vector_dispatch" args rets) :
    VdOut L.read args rets (wVdL L args rets) := by
  exact frameDec_spec find_vd h fun _ hp hb => vd_out (fun _ _ _ h => wVecL_spec h) hp hb

/-! ## The rows of a column -/

/-- The row loop's iteration outcome at row `y`, the loop's other words `ps`. -/
def rowB (store : Bool) (rd : Reader) (y : E) (ps : List E) (syms : List K) : Prop :=
  RowCellW store rd (ps.getD 1 0) (ps.getD 2 0) (ps.getD 3 0) (ps.getD 4 0) (ps.getD 5 0) y syms

/-- **The row loop's cells, decoded**: iteration `j`'s cell symbols, `da_verify_cell`'s decoded
at the words of iteration `x·g^j`'s frame. -/
noncomputable def wRowsL {κ : ℕ} (L : MemImage κ) (store : Bool) : List E → List E → List (List K) :=
  loopDec L (rowName store) (fun ps => ps.getD 0 0)
    (fun σ => wCellL L [σ (.n 2)] [σ (.n 7), σ (.n 8), σ (.n 9)])

theorem wRowsL_spec {κ : ℕ} {L : MemImage κ} (store : Bool) {args rets : List E}
    (h : RL coreProgram L certByName (rowName store) args rets) :
    RowsOut store L.read args rets (wRowsL L store args rets) := by
  have hstep : ∀ C : CallRel, CallRel.Le C (RL coreProgram L certByName) → ∀ (σ : Val) (args rets : List E),
      ([.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] : List V).map σ = args →
      Stmt.HoldsList C L.read σ (rowBody store) False (fun rs => rs = rets) →
      ∃ x ps, args = x :: ps ∧ rets = [] ∧
        rowB store L.read x ps (wCellL L [σ (.n 2)] [σ (.n 7), σ (.n 8), σ (.n 9)]) ∧
        (x * gen ≠ ps.getD 0 0 → C (rowName store) (x * gen :: ps) []) := by
    intro C hC σ args rets hp hb
    obtain ⟨rfl, rfl, hcell, ht, hn, hnext⟩ := row_step_w store (fun _ _ h => wCellL_spec (hC _ _ _ h)) hp hb
    refine ⟨_, _, rfl, rfl, hcell, fun hne => ?_⟩
    have h0 : σ (.n (rowTest store)) ≠ 0 := by
      rw [ht]; exact fun h => hne (e_add_eq_zero_iff.mp h)
    have := hnext h0
    rwa [hn] at this
  obtain ⟨a, -, hp, -⟩ := rl_frame (find_row store) h
  obtain ⟨x, ps, rfl, rfl, hl⟩ := loopDec_spec (find_row store) hstep h
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hp
  obtain ⟨-, rfl⟩ := hp
  exact ⟨_, _, _, _, _, _, _, rfl, rfl, hl⟩

/-! ## The columns -/

/-- A column's witness, decoded. -/
noncomputable def wColL {κ : ℕ} (L : MemImage κ) (store : Bool) (args rets : List E) : DaColumn :=
  frameDec L (colName store) (fun σ => colWit σ (wVdL L) (wRowsL L store)) args rets

theorem wColL_spec {κ : ℕ} {L : MemImage κ} (store : Bool) {args rets : List E}
    (h : RL coreProgram L certByName (colName store) args rets) :
    ColOutW store L.read args rets (wColL L store args rets) := by
  exact frameDec_spec (find_col store) h fun _ hp hb => col_out store (relL_le_rel coreProgram)
    (fun _ _ h => wVdL_spec h) (fun _ _ h => wRowsL_spec store h) hp hb

/-- **The column loop's columns, decoded**: iteration `j`'s column, `da_verify_column`'s decoded
at the words of iteration `x·g^j`'s frame. -/
noncomputable def wColsL {κ : ℕ} (L : MemImage κ) (store : Bool) : List E → List E → List DaColumn :=
  loopDec L (colLoopName store) (fun _ => colLoopEnd store)
    (fun σ => wColL L store [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6),
      σ (.n 7), σ (.n 8), σ (.n 9)] [])

theorem wColsL_spec {κ : ℕ} {L : MemImage κ} (store : Bool) {args rets : List E}
    (h : RL coreProgram L certByName (colLoopName store) args rets) :
    ColsOut store L.read args rets (wColsL L store args rets) := by
  have hstep : ∀ C : CallRel, CallRel.Le C (RL coreProgram L certByName) → ∀ (σ : Val) (args rets : List E),
      ([.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9] : List V).map σ = args →
      Stmt.HoldsList C L.read σ (colLoopBody store) False (fun rs => rs = rets) →
      ∃ x ps, args = x :: ps ∧ rets = [] ∧
        ColOutW store L.read (x :: ps) [] (wColL L store [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4),
          σ (.n 5), σ (.n 6), σ (.n 7), σ (.n 8), σ (.n 9)] []) ∧
        (x * gen ≠ colLoopEnd store → C (colLoopName store) (x * gen :: ps) []) := by
    intro C hC σ args rets hp hb
    obtain ⟨rfl, rfl, hcall, ht, hn, hnext⟩ := colLoop_step_w store hp hb
    refine ⟨_, _, rfl, rfl, wColL_spec store (hC _ _ _ hcall), fun hne => ?_⟩
    have h0 : σ (.n 13) ≠ 0 := by
      rw [ht]; exact fun h => hne (e_add_eq_zero_iff.mp h)
    have := hnext h0
    rwa [hn] at this
  obtain ⟨x, ps, rfl, rfl, hl⟩ := loopDec_spec (find_colLoop store) hstep h
  exact ⟨x, ps, rfl, rfl, hl⟩

/-! ## `da_verify` -/

/-- **`da_verify`'s witness, decoded**: the witness of the call's frame, its column loops'
witnesses decoded. -/
noncomputable def wDaL {κ : ℕ} (L : MemImage κ) (args rets : List E) : Da.Witness :=
  frameDec L "da_verify" (fun σ => dvWit σ (wColsL L true) (wColsL L false)) args rets

/-- **A located call of `da_verify` holds its DA claim at the decoded witness**: on a valid
execution's memory and the squares table, the returned words decode to a root and a vector
digest that `wDaL L` opens. -/
theorem daWit_out {κ : ℕ} {L : MemImage κ} (hm : MemOk L.read) {gsq : E} (hT : SquaresAt L.read gsq)
    {r0 r1 v0 v1 : E} (h : RL coreProgram L certByName "da_verify" [gsq] [r0, r1, v0, v1]) :
    DaOut L.read gsq r0 r1 v0 v1 (wDaL L [gsq] [r0, r1, v0, v1]) := by
  exact frameDec_spec find_dv h fun _ hp hb => da_verify_sound_w (relL_le_rel coreProgram) hm hT
    (fun _ _ h => wColsL_spec true h) (fun _ _ h => wColsL_spec false h) hp hb

end
end LeanVM.Guest.Located
