/-
  LeanVM.Guest.Located.DaB

  The DA check's witnesses decoded from the memory under any semantics of `BLAKE2S`, and their
  outcomes over a hash model (`Located/Da.lean` over `S` and a `HashModel`).
-/

module

public import LeanVM.Guest.Located.BasicB
public import LeanVM.Guest.Located.Da
public import LeanVM.Guest.B1.Da.NamedM

/-!
# The DA check's witnesses under any semantics

`Located/Da.lean`'s decoders with the frame of a call under `S` at the named frames `fr`
(`frameOfB S fr`, decision E2E-5 of the removed `e2e-security.md`): `frameDecB S fr`, `loopDecB S fr` and the DA decoders
`wCellLB S fr` … `wDaLB S fr`, each the deployed one at `blakeDeployed` with no frame named
(`wDaLB_deployed`). The outcomes below hold at every `fr`: a decoded frame holds its callee's code
(`frameDecB_spec`). Over a hash model `M` a located call under `M.sem`
(`Check.RLB M.sem`) satisfies its callee's outcome over the model at the decoded witness, by the
model lemmas of `B1/Da/*M.lean` (`da_verify_cell_outM`, `da_vector_cell_outB`, `vd_outB`,
`row_step_wB`, `col_outB`, `colLoop_step_wB`, `da_verify_sound_wM`): `daWit_outM`, the blob
matrix `wDaLB M.sem fr L` opening over the model with the guest's padding digests.
-/

namespace LeanVM.Guest.Located

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Check
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Guest.Value
open LeanVM.Guest.B1.Digest

@[expose] public section

/-! ## Decoding a frame -/

/-- **The witness `wit` reads off the frame of a call under `S`** (`frameDec` over `frameOfB`). -/
noncomputable def frameDecB (S : BlakeSem) (fr : String → List E → Option ℕ) {κ : ℕ} {α : Type}
    (L : MemImage κ) (f : String) (wit : Val → α) (args rets : List E) : α :=
  wit (valAt L f (frameOfB S fr L f args rets))

/-- **What the callee's body gives at any of its frames, the decoded witness has**, for a located
call. -/
theorem frameDecB_spec {S : BlakeSem} {fr : String → List E → Option ℕ} {κ : ℕ} {L : MemImage κ} {α : Type} {f : String} {fn : Fn}
    (hf : coreProgram.find? f = some fn) {wit : Val → α} {args rets : List E}
    (h : RLB S coreProgram L certByName f args rets) {t : α → Prop}
    (hT : ∀ a, fn.params.map (valAt L f a) = args →
      Stmt.HoldsListB S (RLB S coreProgram L certByName) L.read (valAt L f a) fn.body False
        (fun rs => rs = rets) → t (wit (valAt L f a))) :
    t (frameDecB S fr L f wit args rets) := by
  obtain ⟨hp, hb⟩ := body_frameOfB (fr := fr) hf h
  exact hT _ hp hb

/-- **A located call's frame**: a frame of the memory where the callee's body holds under its
valuation, its own calls located. -/
theorem rl_frameB {S : BlakeSem} {κ : ℕ} {L : MemImage κ} {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    {args rets : List E} (h : RLB S coreProgram L certByName f args rets) :
    ∃ a < 2 ^ κ, fn.params.map (valAt L f a) = args ∧
      Stmt.HoldsListB S (RLB S coreProgram L certByName) L.read (valAt L f a) fn.body False
        (fun rs => rs = rets) := by
  obtain ⟨fn', fp, hf', ⟨a, ha, rfl⟩, hp, hb⟩ := (relLB_iff coreProgram f args rets).mp h
  rw [hf] at hf'
  cases hf'
  exact ⟨a, ha, hp, hb⟩

/-! ## Decoding a loop -/

/-- **A loop's witnesses, iteration by iteration**: for a call `x :: ps`, iteration `j < loopCount`
at `x·g^j` is the witness of the frame of the iteration's call `x·g^j :: ps`; `W = Wf ps` is the
loop's end. -/
noncomputable def loopDecB (S : BlakeSem) (fr : String → List E → Option ℕ) {κ : ℕ} {α : Type}
    (L : MemImage κ) (f : String) (Wf : List E → E) (wit : Val → α) (args _rets : List E) :
    List α :=
  match args with
  | [] => []
  | x :: ps =>
    (List.range (loopCount x (Wf ps))).map fun j => frameDecB S fr L f wit (x * gen ^ j :: ps) []

/-- **A located loop's frames**, by induction on the call's depth: given that one frame of the loop
(under any call relation below the located one) has parameters `x :: ps`, its iteration's
outcome and, short of the end, the call on at `x·g`, the loop runs `m ≥ 1` iterations to its end,
each at a frame of the memory. -/
theorem loop_framesB {S : BlakeSem} {κ : ℕ} {L : MemImage κ} {α : Type} {f : String} {fn : Fn}
    (hf : coreProgram.find? f = some fn) {Wf : List E → E} {B : E → List E → α → Prop}
    {wit : Val → α}
    (step : ∀ C : CallRel, CallRel.Le C (RLB S coreProgram L certByName) → ∀ (σ : Val) (args rets : List E),
      fn.params.map σ = args → Stmt.HoldsListB S C L.read σ fn.body False (fun rs => rs = rets) →
      ∃ x ps, args = x :: ps ∧ rets = [] ∧ B x ps (wit σ) ∧ (x * gen ≠ Wf ps → C f (x * gen :: ps) []))
    (n : ℕ) : ∀ args rets, coreProgram.locNB S L.read (frameVal L certByName) (InMem κ) n f args rets →
      ∃ x ps, args = x :: ps ∧ rets = [] ∧ ∃ m, 0 < m ∧ Wf ps = x * gen ^ m ∧
        (∀ j, 0 < j → j < m → x * gen ^ j ≠ Wf ps) ∧
        ∀ j < m, RLB S coreProgram L certByName f (x * gen ^ j :: ps) [] := by
  induction n with
  | zero => intro _ _ h; exact h.elim
  | succ n ih =>
    intro args rets h
    have hRL : RLB S coreProgram L certByName f args rets := ⟨n + 1, h⟩
    obtain ⟨fn', fp, hf', ⟨a, ha, rfl⟩, hp, hb⟩ := h
    rw [hf] at hf'
    cases hf'
    obtain ⟨x, ps, rfl, rfl, -, hnext⟩ := step _ (locNB_le_relL coreProgram n) _ _ _ hp hb
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
theorem loopDecB_spec {S : BlakeSem} {fr : String → List E → Option ℕ} {κ : ℕ} {L : MemImage κ} {α : Type} {f : String} {fn : Fn}
    (hf : coreProgram.find? f = some fn) {Wf : List E → E} {B : E → List E → α → Prop}
    {wit : Val → α}
    (step : ∀ C : CallRel, CallRel.Le C (RLB S coreProgram L certByName) → ∀ (σ : Val) (args rets : List E),
      fn.params.map σ = args → Stmt.HoldsListB S C L.read σ fn.body False (fun rs => rs = rets) →
      ∃ x ps, args = x :: ps ∧ rets = [] ∧ B x ps (wit σ) ∧ (x * gen ≠ Wf ps → C f (x * gen :: ps) []))
    {args rets : List E} (h : RLB S coreProgram L certByName f args rets) :
    ∃ x ps, args = x :: ps ∧ rets = [] ∧
      LoopW x (Wf ps) (fun y a => B y ps a) (loopDecB S fr L f Wf wit args rets) := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨x, ps, rfl, rfl, m, hm, hW, hfirst, hall⟩ := loop_framesB hf step n _ _ hn
  refine ⟨x, ps, rfl, rfl, ?_⟩
  show LoopW x (Wf ps) _ ((List.range (loopCount x (Wf ps))).map _)
  rw [loopCount_eq hm hW hfirst]
  refine ⟨by simpa using hm, by simpa using hW, fun j h1 h2 => hfirst j h1 (by simpa using h2),
    fun j hj => ?_⟩
  simp only [List.getElem_map, List.getElem_range]
  refine frameDecB_spec hf (hall j (by simpa using hj)) fun a hp hb => ?_
  obtain ⟨x', ps', he, -, hB, -⟩ := step _ (fun _ _ _ h => h) _ _ _ hp hb
  simp only [List.cons.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact hB

/-! ## At the deployed semantics -/

theorem frameDecB_deployed {κ : ℕ} {α : Type} (L : MemImage κ) (f : String) (wit : Val → α) :
    frameDecB blakeDeployed (fun _ _ ↦ none) L f wit = frameDec L f wit := by
  funext args rets
  simp only [frameDecB, frameDec, frameOfB_deployed]

theorem loopDecB_deployed {κ : ℕ} {α : Type} (L : MemImage κ) (f : String) (Wf : List E → E)
    (wit : Val → α) : loopDecB blakeDeployed (fun _ _ ↦ none) L f Wf wit = loopDec L f Wf wit := by
  funext args rets
  cases args <;> simp only [loopDecB, loopDec, frameDecB_deployed]

/-- **At the deployed semantics, at any named frames**, what the callee's body gives under the
deployed relation at any of its frames, the decoded witness has, for a located call. -/
theorem frameDecB_spec_deployed {fr : String → List E → Option ℕ} {κ : ℕ} {L : MemImage κ}
    {α : Type} {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn) {wit : Val → α}
    {args rets : List E} (h : RL coreProgram L certByName f args rets) {t : α → Prop}
    (hT : ∀ a, fn.params.map (valAt L f a) = args →
      Stmt.HoldsList (RL coreProgram L certByName) L.read (valAt L f a) fn.body False
        (fun rs => rs = rets) → t (wit (valAt L f a))) :
    t (frameDecB blakeDeployed fr L f wit args rets) :=
  frameDecB_spec hf (by rw [rlB_deployed]; exact h) fun a hp hb ↦
    hT a hp (by rwa [rlB_deployed, holdsListB_deployed] at hb)

/-- **At the deployed semantics, at any named frames**, a located loop call holds its loop's
outcome at the decoded iterations. -/
theorem loopDecB_spec_deployed {fr : String → List E → Option ℕ} {κ : ℕ} {L : MemImage κ}
    {α : Type} {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn) {Wf : List E → E}
    {B : E → List E → α → Prop} {wit : Val → α}
    (step : ∀ C : CallRel, CallRel.Le C (RL coreProgram L certByName) → ∀ (σ : Val) (args rets : List E),
      fn.params.map σ = args → Stmt.HoldsList C L.read σ fn.body False (fun rs => rs = rets) →
      ∃ x ps, args = x :: ps ∧ rets = [] ∧ B x ps (wit σ) ∧ (x * gen ≠ Wf ps → C f (x * gen :: ps) []))
    {args rets : List E} (h : RL coreProgram L certByName f args rets) :
    ∃ x ps, args = x :: ps ∧ rets = [] ∧
      LoopW x (Wf ps) (fun y a => B y ps a) (loopDecB blakeDeployed fr L f Wf wit args rets) :=
  loopDecB_spec hf (fun C hC σ args rets hp hb ↦
      step C (by rwa [rlB_deployed] at hC) σ args rets hp (by rwa [holdsListB_deployed] at hb))
    (by rw [rlB_deployed]; exact h)

/-! ## The leaves -/

variable (S : BlakeSem) (fr : String → List E → Option ℕ)

/-- `da_verify_cell`'s symbols, decoded under `S`. -/
noncomputable def wCellLB {κ : ℕ} (L : MemImage κ) (args rets : List E) : List K :=
  frameDecB S fr L "da_verify_cell" vcSyms args rets

/-- `da_vector_cell__L{final}`'s weights, decoded under `S`. -/
noncomputable def wVecLB {κ : ℕ} (L : MemImage κ) (final : Bool) (args rets : List E) : List E :=
  frameDecB S fr L (vxName final) vxWs args rets

/-- `da_vector_dispatch`'s weights, decoded under `S`. -/
noncomputable def wVdLB {κ : ℕ} (L : MemImage κ) (args rets : List E) : List E :=
  frameDecB S fr L "da_vector_dispatch" (fun σ => vdWit σ (wVecLB S fr L)) args rets

/-- The row loop's cells, decoded under `S`. -/
noncomputable def wRowsLB {κ : ℕ} (L : MemImage κ) (store : Bool) : List E → List E → List (List K) :=
  loopDecB S fr L (rowName store) (fun ps => ps.getD 0 0)
    (fun σ => wCellLB S fr L [σ (.n 2)] [σ (.n 7), σ (.n 8), σ (.n 9)])

/-- A column's witness, decoded under `S`. -/
noncomputable def wColLB {κ : ℕ} (L : MemImage κ) (store : Bool) (args rets : List E) : DaColumn :=
  frameDecB S fr L (colName store) (fun σ => colWit σ (wVdLB S fr L) (wRowsLB S fr L store)) args rets

/-- The column loop's columns, decoded under `S`. -/
noncomputable def wColsLB {κ : ℕ} (L : MemImage κ) (store : Bool) : List E → List E → List DaColumn :=
  loopDecB S fr L (colLoopName store) (fun _ => colLoopEnd store)
    (fun σ => wColLB S fr L store [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6),
      σ (.n 7), σ (.n 8), σ (.n 9)] [])

/-- **`da_verify`'s witness, decoded under `S`** (`wDaL`). -/
noncomputable def wDaLB {κ : ℕ} (L : MemImage κ) (args rets : List E) : Da.Witness :=
  frameDecB S fr L "da_verify" (fun σ => dvWit σ (wColsLB S fr L true) (wColsLB S fr L false)) args rets

variable {S fr}

/-- **At the deployed semantics, no frame named, the DA decoder is `wDaL`.** -/
theorem wDaLB_deployed {κ : ℕ} (L : MemImage κ) : wDaLB blakeDeployed (fun _ _ ↦ none) L = wDaL L := by
  have hc : wCellLB blakeDeployed (fun _ _ ↦ none) L = wCellL L := by
    funext a r; simp only [wCellLB, wCellL, frameDecB_deployed]
  have hv : wVecLB blakeDeployed (fun _ _ ↦ none) L = wVecL L := by
    funext f a r; simp only [wVecLB, wVecL, frameDecB_deployed]
  have hd : wVdLB blakeDeployed (fun _ _ ↦ none) L = wVdL L := by
    funext a r; simp only [wVdLB, wVdL, frameDecB_deployed, hv]
  have hr : wRowsLB blakeDeployed (fun _ _ ↦ none) L = wRowsL L := by
    funext st; simp only [wRowsLB, wRowsL, loopDecB_deployed, hc]
  have hcol : wColLB blakeDeployed (fun _ _ ↦ none) L = wColL L := by
    funext st a r; simp only [wColLB, wColL, frameDecB_deployed, hd, hr]
  have hcols : wColsLB blakeDeployed (fun _ _ ↦ none) L = wColsL L := by
    funext st; simp only [wColsLB, wColsL, loopDecB_deployed, hcol]
  funext a r
  simp only [wDaLB, wDaL, frameDecB_deployed, hcols]

/-! ## The outcomes over a hash model -/

variable {M : HashModel}

theorem wCellLB_spec {κ : ℕ} {L : MemImage κ} {args rets : List E}
    (h : RLB M.sem coreProgram L certByName "da_verify_cell" args rets) :
    CellOutM M L.read args rets (wCellLB M.sem fr L args rets) :=
  frameDecB_spec find_da_verify_cell h fun _ hp hb => da_verify_cell_outM hp hb

theorem wVecLB_spec {κ : ℕ} {L : MemImage κ} {final : Bool} {args rets : List E}
    (h : RLB M.sem coreProgram L certByName (vxName final) args rets) :
    VecOutB M.sem final L.read args rets (wVecLB M.sem fr L final args rets) :=
  frameDecB_spec (find_vx final) h fun _ hp hb => da_vector_cell_outB hp hb

theorem wVdLB_spec {κ : ℕ} {L : MemImage κ} {args rets : List E}
    (h : RLB M.sem coreProgram L certByName "da_vector_dispatch" args rets) :
    VdOutB M.sem L.read args rets (wVdLB M.sem fr L args rets) :=
  frameDecB_spec find_vd h fun _ hp hb => vd_outB (fun _ _ _ h => wVecLB_spec h) hp hb

theorem wRowsLB_spec {κ : ℕ} {L : MemImage κ} (store : Bool) {args rets : List E}
    (h : RLB M.sem coreProgram L certByName (rowName store) args rets) :
    RowsOutM M store L.read args rets (wRowsLB M.sem fr L store args rets) := by
  have hstep : ∀ C : CallRel, CallRel.Le C (RLB M.sem coreProgram L certByName) →
      ∀ (σ : Val) (args rets : List E),
      ([.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] : List V).map σ = args →
      Stmt.HoldsListB M.sem C L.read σ (rowBody store) False (fun rs => rs = rets) →
      ∃ x ps, args = x :: ps ∧ rets = [] ∧
        RowCellWM M store L.read (ps.getD 1 0) (ps.getD 2 0) (ps.getD 3 0) (ps.getD 4 0)
          (ps.getD 5 0) x (wCellLB M.sem fr L [σ (.n 2)] [σ (.n 7), σ (.n 8), σ (.n 9)]) ∧
        (x * gen ≠ ps.getD 0 0 → C (rowName store) (x * gen :: ps) []) := by
    intro C hC σ args rets hp hb
    obtain ⟨rfl, rfl, hcell, ht, hn, hnext⟩ :=
      row_step_wB store (fun _ _ h => wCellLB_spec (hC _ _ _ h)) hp hb
    refine ⟨_, _, rfl, rfl, hcell, fun hne => ?_⟩
    have h0 : σ (.n (rowTest store)) ≠ 0 := by
      rw [ht]; exact fun h => hne (e_add_eq_zero_iff.mp h)
    have := hnext h0
    rwa [hn] at this
  obtain ⟨a, -, hp, -⟩ := rl_frameB (find_row store) h
  obtain ⟨x, ps, rfl, rfl, hl⟩ := loopDecB_spec (find_row store) hstep h
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hp
  obtain ⟨-, rfl⟩ := hp
  exact ⟨_, _, _, _, _, _, _, rfl, rfl, hl⟩

theorem wColLB_spec {κ : ℕ} {L : MemImage κ} (store : Bool) {args rets : List E}
    (h : RLB M.sem coreProgram L certByName (colName store) args rets) :
    ColOutWM M store L.read args rets (wColLB M.sem fr L store args rets) :=
  frameDecB_spec (find_col store) h fun _ hp hb => col_outB store (relLB_le_rel coreProgram)
    (fun _ _ h => wVdLB_spec h) (fun _ _ h => wRowsLB_spec store h) hp hb

theorem wColsLB_spec {κ : ℕ} {L : MemImage κ} (store : Bool) {args rets : List E}
    (h : RLB M.sem coreProgram L certByName (colLoopName store) args rets) :
    ColsOutM M store L.read args rets (wColsLB M.sem fr L store args rets) := by
  have hstep : ∀ C : CallRel, CallRel.Le C (RLB M.sem coreProgram L certByName) →
      ∀ (σ : Val) (args rets : List E),
      ([.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9] : List V).map σ = args →
      Stmt.HoldsListB M.sem C L.read σ (colLoopBody store) False (fun rs => rs = rets) →
      ∃ x ps, args = x :: ps ∧ rets = [] ∧
        ColOutWM M store L.read (x :: ps) [] (wColLB M.sem fr L store [σ (.n 0), σ (.n 1), σ (.n 2),
          σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7), σ (.n 8), σ (.n 9)] []) ∧
        (x * gen ≠ colLoopEnd store → C (colLoopName store) (x * gen :: ps) []) := by
    intro C hC σ args rets hp hb
    obtain ⟨rfl, rfl, hcall, ht, hn, hnext⟩ := colLoop_step_wB store hp hb
    refine ⟨_, _, rfl, rfl, wColLB_spec store (hC _ _ _ hcall), fun hne => ?_⟩
    have h0 : σ (.n 13) ≠ 0 := by
      rw [ht]; exact fun h => hne (e_add_eq_zero_iff.mp h)
    have := hnext h0
    rwa [hn] at this
  obtain ⟨x, ps, rfl, rfl, hl⟩ := loopDecB_spec (find_colLoop store) hstep h
  exact ⟨x, ps, rfl, rfl, hl⟩

/-- **A located call of `da_verify` under the model's semantics holds its DA claim over the model
at the decoded witness** (`daWit_out`): on a valid execution's memory and the squares table, the
returned words decode to a root and a vector digest that `wDaLB M.sem fr L` opens over the model,
the padding digests the guest's. -/
theorem daWit_outM {κ : ℕ} {L : MemImage κ} (hm : MemOk L.read) {gsq : E}
    (hT : SquaresAt L.read gsq) {r0 r1 v0 v1 : E}
    (h : RLB M.sem coreProgram L certByName "da_verify" [gsq] [r0, r1, v0, v1]) :
    DaOutM M L.read gsq r0 r1 v0 v1 (wDaLB M.sem fr L [gsq] [r0, r1, v0, v1]) :=
  frameDecB_spec find_dv h fun _ hp hb => da_verify_sound_wM (relLB_le_rel coreProgram) hm hT
    (fun _ _ h => wColsLB_spec true h) (fun _ _ h => wColsLB_spec false h) hp hb

end
end LeanVM.Guest.Located
