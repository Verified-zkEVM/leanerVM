/-
  LeanerVM.Arithmetization.Steps

  In a witness of the constraint statement, every row of the six opcode tables is a step of the
  machine from the state it pulls to the state it pushes, and no row pulls the sentinel counter.
-/

module

public import LeanerVM.Arithmetization.Bus

@[expose] public section

/-!
# Rows are steps

The per-row half of constraint soundness (specification §5, "an instance is accepted exactly
when every table's constraints hold and the bus balances"; §6.1, §7), at leanVM pin
`a386121f84292f6fa663aaa3e570c15bc0240ea2`, over Clean `9dd71e82`. Category A: the argument
composes this repository's components; nothing is transcribed. Artifact: the accept relation
`SatisfiedBy`. Direction: soundness.

**Guarantees.** `fullGuarantees_of_satisfiedBy`: in a witness of `SatisfiedBy`, every pull of
every row carries its channel's guarantee (Clean's `Interaction.Guarantees` binds pulls only).
Every interaction is on one of the ensemble's three channels: the state channel, which
guarantees nothing, and the two lookup channels, whose guarantees are `mem_channel_sound` and
the decoding half of `bytecode_channel_sound` (`decode_entry`).

**Specifications.** `spec_of_satisfiedBy`: then Clean's per-row soundness
(`Air.Flat.Component.weakSoundness`) gives every row its component's `Spec`, the constraints
being `SatisfiedBy`'s and the row's circuit assumptions Clean derives
(`Table.circuitAssumptions_of_assumptions`) from the fixed columns, the derived data and the
BLAKE2s validity (`assumptions_of_blake2sRowsValid`). A table's `Spec` is its row's `*Refines`
relation over the image the data names, at the successor the row returns, which is the state it
pushes (`xor_rowOutput` and its five siblings).

**Steps.** `rowSteps_of_satisfiedBy`: a row's `Spec` executes the instruction its own columns
name, and the bytecode lookup makes that instruction the program's at the pulled counter
(`bytecode_channel_sound`, `entry_injective`, `Program.fetch_gpow`), so the row's pull steps to
its push: `step prog (imageOf w.data).2 r = some r'`. The two blocks send nothing on the state
channel, so the statement is over every table of the witness.

**The sentinel.** `no_row_at_sentinel`: no row of a table pulls the sentinel counter
`g^(N_prog - 1)` when the program's sentinel slot is not a `JUMP` (`SentinelSafe`). Such a row
reads the sentinel's entry, so it is not a `JUMP` row and pushes `g^N_prog`; the state pair
balances, and neither the verifier, which pulls `g^(N_prog - 1)`, nor a row, whose pulled
counter is a bytecode address `g^k` with `k < N_prog`, pulls `g^N_prog`. The statement is over
the tables' rows: over all of `w.interactions` it is false, since the verifier pulls
`(g^(N_prog - 1), 1)`.

## Wrong readings excluded

* A row's `Spec` is not a step: it executes the instruction the row names, and only the
  bytecode lookup makes that the program's instruction at the row's counter.
* The `JUMP` row's successor is the state it pushes and returns, which reads its indicator, a
  local witness the residuals force; it is never read off the typed row alone.
* `no_row_at_sentinel` needs `SentinelSafe`: a `JUMP` at the sentinel slot lets a row pull the
  sentinel counter and jump on.
-/

namespace LeanerVM.Arithmetization

open LeanerVM.Parameters LeanerVM.Semantics
open Air.Flat (Component EnsembleWitness)

variable {prog : Program} {κ : ℕ} {input : PublicInput}

/-! ## The state each row returns -/

/-- Evaluates a row circuit's output at its typed row. -/
local macro "row_output" circuit:ident sends:ident : tactic => `(tactic|
  (rw [← eval_varFromOffset_valueFromOffset]
   simp only [circuit_norm, $circuit:ident, instructionStep, memRead, bytecodeRead,
     $sends:ident]))

-- Each statement below is first proved of the row circuit's output, whose evaluation carries the
-- row type's own `ProvableType` instance, which `circuit_norm` evaluates; the component's
-- `rowOutput` carries the component's instance, definitionally the same.

/-- An `XOR` row returns the state it pushes. -/
theorem xor_rowOutput (env : Environment K) :
    xorComponent.rowOutput env = (xorSends (valueFromOffset XorRow 0 env)).push := by
  have h : eval env ((xorTable.main (varFromOffset XorRow 0)).output (size XorRow)) =
      (xorSends (valueFromOffset XorRow 0 env)).push := by row_output xorTable xorSends
  exact h

/-- A `MUL_NATIVE` row returns the state it pushes. -/
theorem mul_rowOutput (env : Environment K) :
    mulComponent.rowOutput env = (mulSends (valueFromOffset MulRow 0 env)).push := by
  have h : eval env ((mulTable.main (varFromOffset MulRow 0)).output (size MulRow)) =
      (mulSends (valueFromOffset MulRow 0 env)).push := by row_output mulTable mulSends
  exact h

/-- A `SET_CONSTANT` row returns the state it pushes. -/
theorem set_rowOutput (env : Environment K) :
    setComponent.rowOutput env = (setSends (valueFromOffset SetRow 0 env)).push := by
  have h : eval env ((setTable.main (varFromOffset SetRow 0)).output (size SetRow)) =
      (setSends (valueFromOffset SetRow 0 env)).push := by row_output setTable setSends
  exact h

/-- A `DEREF` row returns the state it pushes. -/
theorem deref_rowOutput (env : Environment K) :
    derefComponent.rowOutput env = (derefSends (valueFromOffset DerefRow 0 env)).push := by
  have h : eval env ((derefTable.main (varFromOffset DerefRow 0)).output (size DerefRow)) =
      (derefSends (valueFromOffset DerefRow 0 env)).push := by row_output derefTable derefSends
  exact h

/-- A `JUMP` row returns the state it pushes, which reads its indicator. -/
theorem jump_rowOutput (env : Environment K) :
    jumpComponent.rowOutput env =
      (jumpSends (valueFromOffset JumpRow 0 env) (env.get (size JumpRow + 1))).push := by
  have h : eval env ((jumpTable.main (varFromOffset JumpRow 0)).output (size JumpRow)) =
      (jumpSends (valueFromOffset JumpRow 0 env) (env.get (size JumpRow + 1))).push := by
    row_output jumpTable jumpSends
  exact h

/-- A `BLAKE2S` row returns the state it pushes. -/
theorem blake2s_rowOutput (env : Environment K) :
    blake2sComponent.rowOutput env = (blake2sSends (valueFromOffset Blake2sRow 0 env)).push := by
  have h : eval env ((blake2sTable.main (varFromOffset Blake2sRow 0)).output (size Blake2sRow)) =
      (blake2sSends (valueFromOffset Blake2sRow 0 env)).push := by
    row_output blake2sTable blake2sSends
  exact h

/-! ## Proof helpers -/

/-- A row's interaction is an interaction of the witness. -/
private theorem mem_interactions {w : EnsembleWitness (leanIsaEnsemble prog κ)}
    {t : Air.Flat.Table K} (ht : t ∈ w.tables) {row : Array K} (hrow : row ∈ t.table)
    {i : AbstractInteraction K} (hi : i ∈ t.component.operations.interactions) :
    i.eval (t.environment row) ∈ w.interactions :=
  List.mem_append_right _
    (List.mem_flatMap.mpr ⟨t, ht, List.mem_flatMap.mpr ⟨row, hrow, List.mem_map_of_mem hi⟩⟩)

private theorem stateChannel_mem : StateChannel.toRaw ∈ (leanIsaEnsemble prog κ).channels :=
  List.mem_cons_self

/-! ## Guarantees and specifications -/

/-- In a witness of the statement, every pull of every row carries its channel's guarantee: the
memory and bytecode lookups' (`mem_channel_sound`, `bytecode_channel_sound`), the state pull's
being `True`. -/
theorem fullGuarantees_of_satisfiedBy {w : EnsembleWitness (leanIsaEnsemble prog κ)}
    (h : SatisfiedBy prog input w) :
    ∀ t ∈ w.tables, ∀ row ∈ t.table,
      t.component.operations.FullGuarantees (t.environment row) := by
  intro t ht row hrow i hi _
  have hmem := mem_interactions ht hrow hi
  have hch := EnsembleWitness.channel_mem_of_mem_interactions hmem
  have hdata : (t.environment row).data = w.data := table_data w ht
  obtain ⟨ch, dir, mult, msg⟩ := i
  simp only [AbstractInteraction.eval_channel, leanIsaEnsemble, List.mem_cons, List.not_mem_nil,
    or_false] at hch
  dsimp only at hmem ⊢
  rcases hch with rfl | rfl | rfl
  · exact fun _ ↦ trivial
  · intro _
    rw [hdata]
    exact mem_channel_sound h _ hmem rfl _ (by
      show (msg.map _).toArray = (toElements (fromElements (msg.map _))).toArray
      rw [ProvableType.toElements_fromElements])
  · intro _
    obtain ⟨k, -, hk⟩ := bytecode_channel_sound h _ hmem rfl
      (fromElements (msg.map (t.environment row))) (by
        show (msg.map _).toArray = (toElements (fromElements (msg.map _))).toArray
        rw [ProvableType.toElements_fromElements])
    exact ⟨_, hk ▸ decode_entry _⟩

/-- In a witness of the statement, every row satisfies its component's specification: Clean's
per-row soundness, from the row's circuit assumptions (the fixed columns, the derived data and
the BLAKE2s validity), the constraints and the guarantees. -/
theorem spec_of_satisfiedBy {w : EnsembleWitness (leanIsaEnsemble prog κ)}
    (h : SatisfiedBy prog input w) :
    ∀ t ∈ w.tables, ∀ row ∈ t.table, t.component.Spec (t.environment row) :=
  fun t ht row hrow ↦ (Component.weakSoundness
    (t.circuitAssumptions_of_assumptions
      (assumptions_of_blake2sRowsValid h.caps.le_maxLogMem h.blake2s_valid t ht) row hrow)
    (h.constraints t ht row hrow) (fullGuarantees_of_satisfiedBy h t ht row hrow)).1

/-! ## Rows are steps -/

/-- Two arrays of two coordinates are equal exactly when their coordinates are. -/
private theorem pair_eq {a b c d : K} (h : #[a, b] = #[c, d]) : a = c ∧ b = d := by
  simpa using h

/-- Two states with the same message are equal. -/
private theorem regs_eq_of_pair {r r' : Regs K} (h : #[r.pc, r.fp] = #[r'.pc, r'.fp]) :
    r = r' := by
  obtain ⟨hpc, hfp⟩ := pair_eq h
  cases r
  cases r'
  cases hpc
  cases hfp
  rfl

/-- A row's bytecode read is the program's entry at its counter. -/
private theorem bytecode_of_row {w : EnsembleWitness (leanIsaEnsemble prog κ)}
    (h : SatisfiedBy prog input w) {t : Air.Flat.Table K} (ht : t ∈ w.tables) {row : Array K}
    (hrow : row ∈ t.table) {s : OpcodeSends} (hs : SendsOpcode t row s) :
    ∃ k : Fin (2 ^ prog.logSize), s.bc.pc = gpow k ∧
      #v[s.bc.opcode] ++ s.bc.op = entry (prog.code k) := by
  obtain ⟨i, hi, hname, -, hmsg⟩ := exists_interaction_of_mem_messagesOn
    (mem_messagesOn_of_mem_rowMessagesOn ht hrow (a := (toElements s.bc).toArray)
      (by rw [hs.bytecode_pull]; exact List.mem_singleton_self _))
  exact bytecode_channel_sound h i hi hname s.bc hmsg

/-- A row that executes the instruction its bytecode read names, at its pulled counter, steps. -/
private theorem step_of_row {w : EnsembleWitness (leanIsaEnsemble prog κ)}
    (h : SatisfiedBy prog input w) {t : Air.Flat.Table K} (ht : t ∈ w.tables) {row : Array K}
    (hrow : row ∈ t.table) {s : OpcodeSends} (hs : SendsOpcode t row s) {ins : Instr}
    (hins : #v[s.bc.opcode] ++ s.bc.op = entry ins) (hpc : s.bc.pc = s.pull.pc)
    (hexec : execute (imageOf w.data).2 s.pull ins = some s.push) :
    step prog (imageOf w.data).2 s.pull = some s.push := by
  obtain ⟨k, hk, he⟩ := bytecode_of_row h ht hrow hs
  have hcode : prog.code k = ins := entry_injective (he.symm.trans hins)
  rw [step_of_fetch_eq_some (ins := ins) (by rw [← hpc, hk, Program.fetch_gpow, hcode])]
  exact hexec

/-- A row of a table satisfies its circuit's `Spec`, over the witness's data. -/
private theorem spec_row {w : EnsembleWitness (leanIsaEnsemble prog κ)}
    (h : SatisfiedBy prog input w) {t : Air.Flat.Table K} (ht : t ∈ w.tables) {c : Component K}
    (htc : t.component = c) {row : Array K} (hrow : row ∈ t.table) :
    c.circuit.Spec (c.rowInput (t.environment row)) (c.rowOutput (t.environment row)) w.data := by
  have hspec := spec_of_satisfiedBy h t ht row hrow
  have hd : (t.environment row).data = w.data := table_data w ht
  rw [htc] at hspec
  unfold Component.Spec at hspec
  rw [hd] at hspec
  exact hspec

private theorem xor_step {w : EnsembleWitness (leanIsaEnsemble prog κ)}
    (h : SatisfiedBy prog input w) {t : Air.Flat.Table K} (ht : t ∈ w.tables)
    (htc : t.component = xorComponent) {row : Array K} (hrow : row ∈ t.table) :
    step prog (imageOf w.data).2 (xorSends (valueFromOffset XorRow 0 (t.environment row))).pull =
      some (xorSends (valueFromOffset XorRow 0 (t.environment row))).push := by
  have hexec := (show XorSpec _ _ _ from spec_row h ht htc hrow).exec_eq
  rw [xor_rowOutput] at hexec
  exact step_of_row h ht hrow (xor_sendsOpcode htc row)
    (Vector.toList_inj.mp (by rw [Vector.toList_append]; rfl)) rfl hexec

private theorem mul_step {w : EnsembleWitness (leanIsaEnsemble prog κ)}
    (h : SatisfiedBy prog input w) {t : Air.Flat.Table K} (ht : t ∈ w.tables)
    (htc : t.component = mulComponent) {row : Array K} (hrow : row ∈ t.table) :
    step prog (imageOf w.data).2 (mulSends (valueFromOffset MulRow 0 (t.environment row))).pull =
      some (mulSends (valueFromOffset MulRow 0 (t.environment row))).push := by
  have hexec := (show MulSpec _ _ _ from spec_row h ht htc hrow).exec_eq
  rw [mul_rowOutput] at hexec
  exact step_of_row h ht hrow (mul_sendsOpcode htc row)
    (Vector.toList_inj.mp (by rw [Vector.toList_append]; rfl)) rfl hexec

private theorem set_step {w : EnsembleWitness (leanIsaEnsemble prog κ)}
    (h : SatisfiedBy prog input w) {t : Air.Flat.Table K} (ht : t ∈ w.tables)
    (htc : t.component = setComponent) {row : Array K} (hrow : row ∈ t.table) :
    step prog (imageOf w.data).2 (setSends (valueFromOffset SetRow 0 (t.environment row))).pull =
      some (setSends (valueFromOffset SetRow 0 (t.environment row))).push := by
  have hexec := (show SetSpec _ _ _ from spec_row h ht htc hrow).exec_eq
  rw [set_rowOutput] at hexec
  exact step_of_row h ht hrow (set_sendsOpcode htc row)
    (Vector.toList_inj.mp (by
      rw [Vector.toList_append]
      simp [entry, setSends]
      exact ⟨rfl, rfl, rfl, rfl⟩)) rfl hexec

private theorem deref_step {w : EnsembleWitness (leanIsaEnsemble prog κ)}
    (h : SatisfiedBy prog input w) {t : Air.Flat.Table K} (ht : t ∈ w.tables)
    (htc : t.component = derefComponent) {row : Array K} (hrow : row ∈ t.table) :
    step prog (imageOf w.data).2
        (derefSends (valueFromOffset DerefRow 0 (t.environment row))).pull =
      some (derefSends (valueFromOffset DerefRow 0 (t.environment row))).push := by
  obtain ⟨mode, hb, hexec⟩ := (show DerefSpec _ _ _ from spec_row h ht htc hrow)
  rw [deref_rowOutput] at hexec
  exact step_of_row h ht hrow (deref_sendsOpcode htc row)
    (Vector.toList_inj.mp (by
      rw [Vector.toList_append]
      simp [entry, derefSends, hb.flags_eq]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩)) rfl hexec

private theorem jump_step {w : EnsembleWitness (leanIsaEnsemble prog κ)}
    (h : SatisfiedBy prog input w) {t : Air.Flat.Table K} (ht : t ∈ w.tables)
    (htc : t.component = jumpComponent) {row : Array K} (hrow : row ∈ t.table) :
    step prog (imageOf w.data).2
        (jumpSends (valueFromOffset JumpRow 0 (t.environment row))
          (row[size JumpRow + 1]?.getD 0)).pull =
      some (jumpSends (valueFromOffset JumpRow 0 (t.environment row))
        (row[size JumpRow + 1]?.getD 0)).push := by
  have hexec := (show JumpSpec _ _ _ from spec_row h ht htc hrow).exec_eq
  rw [jump_rowOutput] at hexec
  exact step_of_row h ht hrow (jump_sendsOpcode htc row)
    (Vector.toList_inj.mp (by rw [Vector.toList_append]; rfl)) rfl hexec

private theorem blake2s_step {w : EnsembleWitness (leanIsaEnsemble prog κ)}
    (h : SatisfiedBy prog input w) {t : Air.Flat.Table K} (ht : t ∈ w.tables)
    (htc : t.component = blake2sComponent) {row : Array K} (hrow : row ∈ t.table) :
    step prog (imageOf w.data).2
        (blake2sSends (valueFromOffset Blake2sRow 0 (t.environment row))).pull =
      some (blake2sSends (valueFromOffset Blake2sRow 0 (t.environment row))).push := by
  have hexec := (show Blake2sSpec _ _ _ from spec_row h ht htc hrow).exec_eq
  rw [blake2s_rowOutput] at hexec
  exact step_of_row h ht hrow (blake2s_sendsOpcode htc row)
    (Vector.toList_inj.mp (by rw [Vector.toList_append]; rfl)) rfl hexec

/-- A row of a table of the witness either pulls no state (a block) or is an opcode row: it
steps, it reads the bytecode at the counter it pulls, and it falls through unless it reads a
`JUMP`. -/
private theorem row_cases {w : EnsembleWitness (leanIsaEnsemble prog κ)}
    (h : SatisfiedBy prog input w) {t : Air.Flat.Table K} (ht : t ∈ w.tables) {row : Array K}
    (hrow : row ∈ t.table) :
    rowMessagesOn t row StateChannel.toRaw .pull = [] ∨
      ∃ s, SendsOpcode t row s ∧ step prog (imageOf w.data).2 s.pull = some s.push ∧
        s.bc.pc = s.pull.pc ∧
        (s.bc.opcode = Opcode.jump.code ∨ s.push = ⟨g * s.pull.pc, s.pull.fp⟩) := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ht
  have h8 : j < 8 := by rw [← w.same_length] at hj; exact hj
  have hc : (w.tables[j]'hj).component = (leanIsaEnsemble prog κ).tables[j]'h8 :=
    (w.same_circuits j h8).symm
  interval_cases j
  · exact Or.inr ⟨_, xor_sendsOpcode hc row, xor_step h ht hc hrow, rfl, Or.inr rfl⟩
  · exact Or.inr ⟨_, mul_sendsOpcode hc row, mul_step h ht hc hrow, rfl, Or.inr rfl⟩
  · exact Or.inr ⟨_, set_sendsOpcode hc row, set_step h ht hc hrow, rfl, Or.inr rfl⟩
  · exact Or.inr ⟨_, deref_sendsOpcode hc row, deref_step h ht hc hrow, rfl, Or.inr rfl⟩
  · exact Or.inr ⟨_, jump_sendsOpcode hc row, jump_step h ht hc hrow, rfl, Or.inl rfl⟩
  · exact Or.inr ⟨_, blake2s_sendsOpcode hc row, blake2s_step h ht hc hrow, rfl, Or.inr rfl⟩
  · left
    rw [memBlock_rowMessagesOn hc row rfl, ite_eq_right (by decide)]
  · left
    rw [bytecodeBlock_rowMessagesOn hc row rfl, ite_eq_right (by decide)]

/-- In a witness of the constraint statement, every row is a step of the machine from the state
it pulls to the state it pushes. -/
theorem rowSteps_of_satisfiedBy {w : EnsembleWitness (leanIsaEnsemble prog κ)}
    (h : SatisfiedBy prog input w) :
    ∀ t ∈ w.tables, ∀ row ∈ t.table, ∀ r r' : Regs K,
      rowMessagesOn t row StateChannel.toRaw .pull = [#[r.pc, r.fp]] →
      rowMessagesOn t row StateChannel.toRaw .push = [#[r'.pc, r'.fp]] →
        step prog (imageOf w.data).2 r = some r' := by
  intro t ht row hrow r r' hpull hpush
  rcases row_cases h ht hrow with hnil | ⟨s, hs, hstep, -, -⟩
  · rw [hnil] at hpull
    exact absurd hpull.symm (List.cons_ne_nil _ _)
  · obtain rfl := regs_eq_of_pair (List.cons.inj (hs.state_pull.symm.trans hpull)).1
    obtain rfl := regs_eq_of_pair (List.cons.inj (hs.state_push.symm.trans hpush)).1
    exact hstep

/-! ## The sentinel -/

/-- The bytecode has at most `2^32` slots, far below the order of `g`. -/
private theorem two_pow_logSize_lt (prog : Program) : 2 ^ prog.logSize < 2 ^ 64 - 1 :=
  lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) prog.logSize_le) (by decide)

/-- The successor counter of the sentinel's is `g^N_prog`. -/
private theorem g_mul_finalPc (prog : Program) : g * prog.finalPc = gpow (2 ^ prog.logSize) := by
  rw [Program.finalPc, ← gpow_succ, Nat.sub_add_cancel Nat.one_le_two_pow]

/-- No row of a table of the witness pulls the sentinel counter, when the sentinel slot is not
a `JUMP`: such a row would push `(g^N_prog, fp)`, which neither the verifier nor a row pulls. -/
theorem no_row_at_sentinel (hsafe : SentinelSafe prog)
    {w : EnsembleWitness (leanIsaEnsemble prog κ)} (h : SatisfiedBy prog input w) :
    ∀ t ∈ w.tables, ∀ row ∈ t.table, ∀ pc fp : K,
      #[pc, fp] ∈ rowMessagesOn t row StateChannel.toRaw .pull → pc ≠ prog.finalPc := by
  intro t ht row hrow pc fp hmem hpc
  have hN := two_pow_logSize_lt prog
  rcases row_cases h ht hrow with hnil | ⟨s, hs, -, hbcpc, hcase⟩
  · rw [hnil] at hmem
    exact List.not_mem_nil hmem
  rw [hs.state_pull, List.mem_singleton] at hmem
  obtain ⟨rfl, rfl⟩ := pair_eq hmem
  obtain ⟨k, hk, he⟩ := bytecode_of_row h ht hrow hs
  have hkN : (k : ℕ) = 2 ^ prog.logSize - 1 :=
    gpow_injOn (lt_trans k.isLt hN) (lt_of_le_of_lt (Nat.sub_le _ _) hN)
      (hk.symm.trans (hbcpc.trans hpc))
  rcases hcase with hjump | hpush
  · -- The row reads the sentinel's entry, which is no `JUMP`'s.
    apply hsafe
    have h0 : s.bc.opcode = (prog.code k).opcode.code := by
      rw [← entry_getElem_zero, ← he, Vector.getElem_append_left (by decide)]
      rfl
    have hop : (prog.code k).opcode = .jump := Opcode.code_injective (h0.symm.trans hjump)
    rwa [show k = ⟨2 ^ prog.logSize - 1, Nat.sub_lt (Nat.two_pow_pos _) (by decide)⟩ from
      Fin.ext hkN] at hop
  · -- The row pushes `(g^N_prog, fp)`, and someone pulls it.
    have hpushed : #[gpow (2 ^ prog.logSize), s.pull.fp] ∈
        messagesOn w StateChannel.toRaw .push :=
      mem_messagesOn_of_mem_rowMessagesOn ht hrow (by
        rw [hs.state_push, hpush, hpc, g_mul_finalPc]
        exact List.mem_singleton_self _)
    have hpulled := (h.perm stateChannel_mem).mem_iff.mp hpushed
    rw [messagesOn_eq_flatMap, List.mem_append] at hpulled
    rcases hpulled with hv | hpulled
    · -- The verifier pulls `g^(N_prog - 1)`.
      rw [verifier_messagesOn, ite_eq_left (show StateChannel.toRaw.name = StateChannel.name
        from rfl), ite_eq_right (by decide), List.mem_singleton] at hv
      have := gpow_injOn hN (lt_of_le_of_lt (Nat.sub_le _ _) hN) (pair_eq hv).1
      have := Nat.one_le_two_pow (n := prog.logSize)
      omega
    · -- A row pulls only a bytecode address.
      obtain ⟨t', ht', hm'⟩ := List.mem_flatMap.mp hpulled
      obtain ⟨row', hrow', hm'⟩ := List.mem_flatMap.mp hm'
      rcases row_cases h ht' hrow' with hnil' | ⟨s', hs', -, hbcpc', -⟩
      · rw [hnil'] at hm'
        exact List.not_mem_nil hm'
      rw [hs'.state_pull, List.mem_singleton] at hm'
      obtain ⟨k', hk', -⟩ := bytecode_of_row h ht' hrow' hs'
      have := gpow_injOn hN (lt_trans k'.isLt hN) ((pair_eq hm').1.trans (hbcpc'.symm.trans hk'))
      have := k'.isLt
      omega

end LeanerVM.Arithmetization
