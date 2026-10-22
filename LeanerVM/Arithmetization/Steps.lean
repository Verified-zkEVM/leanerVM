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
`a386121f84292f6fa663aaa3e570c15bc0240ea2`. Category A: the argument composes this
repository's components; nothing is transcribed. Artifact: the accept relation `SatisfiedBy`.
Direction: soundness.

**Guarantees.** `fullGuarantees_of_satisfiedBy`: in a witness of `SatisfiedBy`, every pull of
every row carries its channel's guarantee. A component's interactions are on a channel that
assumes guarantees only when they are pulls (Clean's `Component.inChannelsOrGuarantees`), and
the components of the ensemble pull only on the state channel, which guarantees nothing, and
on the two lookup channels, whose guarantees are `mem_channel_sound` and the decoding half of
`bytecode_channel_sound` (`decode_entry`).

**Specifications.** `spec_of_satisfiedBy`: then Clean's per-row soundness
(`Air.Flat.Component.weakSoundness`) gives every row its component's `Spec`, the constraints
being `SatisfiedBy`'s and the assumptions the BLAKE2s validity
(`assumptions_of_blake2sRowsValid`). A table's `Spec` is its row's `*Refines` relation over the
image the data names, at the successor the row returns, which is the state it pushes
(`xor_rowOutput` and its five siblings).

**Steps.** `rowSteps_of_satisfiedBy`: a row's `Spec` executes the instruction its own columns
name, and the bytecode lookup makes that instruction the program's at the pulled counter
(`bytecode_channel_sound`, `entry_injective`, `Program.fetch_gpow`), so the row's pull steps to
its push: `step prog (imageOf w.data).2 r = some r'`. The two blocks send nothing on the state
channels, so the statement is over every table of the witness.

**The sentinel.** `no_row_at_sentinel`: no row of a table pulls the sentinel counter
`g^(N_prog - 1)` when the program's sentinel slot is not a `JUMP` (`SentinelSafe`). Such a row
reads the sentinel's entry, so it is not a `JUMP` row and pushes `g^N_prog`; the state pair
balances, and neither the verifier, which pulls `g^(N_prog - 1)`, nor a row, whose pulled
counter is a bytecode address `g^k` with `k < N_prog`, pulls `g^N_prog`. The statement is over
the tables' rows: over all of `w.interactions` it is false, since the verifier's own row pulls
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

variable {prog : Program} {input : PublicInput}

/-! ## The state each row returns -/

/-- An `XOR` row returns the state it pushes. -/
theorem xor_rowOutput (env : Environment K) :
    (⟨xorTable⟩ : Component K).rowOutput env = (xorSends (valueFromOffset XorRow 0 env)).push := by
  rw [← eval_varFromOffset_valueFromOffset]
  simp only [Component.rowOutput, circuit_norm, xorTable, instructionStep, memRead, bytecodeRead,
    xorSends]

/-- A `MUL_NATIVE` row returns the state it pushes. -/
theorem mul_rowOutput (env : Environment K) :
    (⟨mulTable⟩ : Component K).rowOutput env = (mulSends (valueFromOffset MulRow 0 env)).push := by
  rw [← eval_varFromOffset_valueFromOffset]
  simp only [Component.rowOutput, circuit_norm, mulTable, instructionStep, memRead, bytecodeRead,
    mulSends]

/-- A `SET_CONSTANT` row returns the state it pushes. -/
theorem set_rowOutput (env : Environment K) :
    (⟨setTable⟩ : Component K).rowOutput env = (setSends (valueFromOffset SetRow 0 env)).push := by
  rw [← eval_varFromOffset_valueFromOffset]
  simp only [Component.rowOutput, circuit_norm, setTable, instructionStep, memRead, bytecodeRead,
    setSends]

/-- A `DEREF` row returns the state it pushes. -/
theorem deref_rowOutput (env : Environment K) :
    (⟨derefTable⟩ : Component K).rowOutput env =
      (derefSends (valueFromOffset DerefRow 0 env)).push := by
  rw [← eval_varFromOffset_valueFromOffset]
  simp only [Component.rowOutput, circuit_norm, derefTable, instructionStep, memRead, bytecodeRead,
    derefSends]

/-- A `JUMP` row returns the state it pushes, which reads its indicator. -/
theorem jump_rowOutput (env : Environment K) :
    (⟨jumpTable⟩ : Component K).rowOutput env =
      (jumpSends (valueFromOffset JumpRow 0 env) (env.get (size JumpRow + 1))).push := by
  rw [← eval_varFromOffset_valueFromOffset]
  simp only [Component.rowOutput, circuit_norm, jumpTable, instructionStep, memRead, bytecodeRead,
    jumpSends]

/-- A `BLAKE2S` row returns the state it pushes. -/
theorem blake2s_rowOutput (env : Environment K) :
    (⟨blake2sTable⟩ : Component K).rowOutput env =
      (blake2sSends (valueFromOffset Blake2sRow 0 env)).push := by
  rw [← eval_varFromOffset_valueFromOffset]
  simp only [Component.rowOutput, circuit_norm, blake2sTable, instructionStep, memRead,
    bytecodeRead, blake2sSends]

/-! ## Proof helpers -/

/-- A row's interaction is an interaction of the witness. -/
private theorem mem_interactions {w : EnsembleWitness (leanIsaEnsemble prog)}
    {t : Air.Flat.Table K} (ht : t ∈ w.allTables) {row : Array K} (hrow : row ∈ t.table)
    {i : AbstractInteraction K} (hi : i ∈ t.component.operations.interactions) :
    i.eval (t.environment row) ∈ w.interactions :=
  List.mem_flatMap.mpr ⟨t, ht, List.mem_flatMap.mpr ⟨row, hrow, List.mem_map_of_mem hi⟩⟩

/-- A message a row sends is the message of one of the witness's interactions on a channel of
that name. -/
private theorem exists_interaction {w : EnsembleWitness (leanIsaEnsemble prog)}
    {t : Air.Flat.Table K} (ht : t ∈ w.allTables) {row : Array K} (hrow : row ∈ t.table)
    {c : RawChannel K} {a : Array K} (ha : a ∈ rowMessagesOn t row c) :
    ∃ i ∈ w.interactions, i.channel.name = c.name ∧ i.msg = a := by
  rw [rowMessagesOn, List.mem_map] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  rw [List.mem_filter] at hi
  obtain ⟨hi, hname⟩ := hi
  rw [Operations.interactionValues, List.mem_map] at hi
  obtain ⟨j, hj, rfl⟩ := hi
  exact ⟨_, mem_interactions ht hrow hj, of_decide_eq_true hname, rfl⟩

/-- The components of the ensemble pull only on the state channel and the two lookup channels. -/
private theorem channelsWithGuarantees_cases {c : Component K}
    (hc : c ∈ (leanIsaEnsemble prog).allTables) :
    ∀ ch ∈ c.circuit.channelsWithGuarantees,
      ch = StatePull.toRaw ∨ ch = MemPull.toRaw ∨ ch = BytecodePull.toRaw := by
  simp only [Air.Flat.Ensemble.allTables, Air.Flat.Ensemble.verifierTable, leanIsaEnsemble,
    List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp only [circuit_norm, leanIsaVerifier, xorTable, mulTable, setTable, derefTable, jumpTable,
      blake2sTable, memTable, bytecodeTable, instructionStep, memRead, bytecodeRead,
      List.mem_cons, List.not_mem_nil, or_false]
    try (intro ch hch; rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp)

/-! ## Guarantees and specifications -/

/-- In a witness of the statement, every pull of every row carries its channel's guarantee: the
memory and bytecode lookups' (`mem_channel_sound`, `bytecode_channel_sound`), the state pull's
being `True`. -/
theorem fullGuarantees_of_satisfiedBy {w : EnsembleWitness (leanIsaEnsemble prog)}
    (h : SatisfiedBy prog input w) :
    ∀ t ∈ w.allTables, ∀ row ∈ t.table,
      t.component.operations.FullGuarantees (t.environment row) := by
  intro t ht row hrow i hi
  rcases t.component.inChannelsOrGuarantees (t.environment row) i hi with hch | hg
  · have hcases := channelsWithGuarantees_cases
      (EnsembleWitness.mem_allTables_component_of_mem_allTables ht) _ hch
    have hmem := mem_interactions ht hrow hi
    have hdata : (t.environment row).data = w.data := w.data_eq_of_mem_allTables t ht
    obtain ⟨ch, mult, msg, assume⟩ := i
    dsimp only at hcases hmem ⊢
    rcases hcases with rfl | rfl | rfl
    · exact fun _ _ ↦ trivial
    · intro _ _
      rw [hdata]
      exact mem_channel_sound h _ hmem rfl _ (by
        show (msg.map _).toArray = (toElements (fromElements (msg.map _))).toArray
        rw [ProvableType.toElements_fromElements])
    · intro _ _
      obtain ⟨k, -, hk⟩ := bytecode_channel_sound h _ hmem rfl
        (fromElements (msg.map (t.environment row))) (by
          show (msg.map _).toArray = (toElements (fromElements (msg.map _))).toArray
          rw [ProvableType.toElements_fromElements])
      exact ⟨_, hk ▸ decode_entry _⟩
  · exact hg

/-- In a witness of the statement, every row satisfies its component's specification: Clean's
per-row soundness, from the constraints, the BLAKE2s validity and the guarantees. -/
theorem spec_of_satisfiedBy {w : EnsembleWitness (leanIsaEnsemble prog)}
    (h : SatisfiedBy prog input w) :
    ∀ t ∈ w.allTables, ∀ row ∈ t.table, t.component.Spec (t.environment row) :=
  fun t ht row hrow ↦ (Component.weakSoundness
    (assumptions_of_blake2sRowsValid h.blake2s_valid t ht row hrow) (h.constraints t ht row hrow)
    (fullGuarantees_of_satisfiedBy h t ht row hrow)).1

/-! ## Rows are steps -/

/-- Two arrays of two coordinates are equal exactly when their coordinates are. -/
private theorem pair_eq {a b c d : K} (h : #[a, b] = #[c, d]) : a = c ∧ b = d := by
  have h' := congrArg Array.toList h
  simp only [List.cons.injEq, and_true] at h'
  exact h'

/-- A row's bytecode read is the program's entry at its counter. -/
private theorem bytecode_of_row {w : EnsembleWitness (leanIsaEnsemble prog)}
    (h : SatisfiedBy prog input w) {t : Air.Flat.Table K} (ht : t ∈ w.tables) {row : Array K}
    (hrow : row ∈ t.table) {s : OpcodeSends} (hs : SendsOpcode t row s) :
    ∃ k : Fin (2 ^ prog.logSize), s.bc.pc = gpow k ∧
      #v[s.bc.opcode] ++ s.bc.op = entry (prog.code k) := by
  obtain ⟨i, hi, hname, hmsg⟩ := exists_interaction (w.mem_allTables_of_mem_tables ht) hrow
    (a := (toElements s.bc).toArray) (by rw [hs.bytecode_pull]; exact List.mem_singleton_self _)
  exact bytecode_channel_sound h i hi hname s.bc hmsg

/-- A row that executes the instruction its bytecode read names, at its pulled counter, steps. -/
private theorem step_of_row {w : EnsembleWitness (leanIsaEnsemble prog)}
    (h : SatisfiedBy prog input w) {t : Air.Flat.Table K} (ht : t ∈ w.tables) {row : Array K}
    (hrow : row ∈ t.table) {s : OpcodeSends} (hs : SendsOpcode t row s) {ins : Instr}
    (hins : #v[s.bc.opcode] ++ s.bc.op = entry ins) (hpc : s.bc.pc = s.pull.pc)
    (hexec : execute (imageOf w.data).2 s.pull ins = some s.push) :
    step prog (imageOf w.data).2 s.pull = some s.push := by
  obtain ⟨k, hk, he⟩ := bytecode_of_row h ht hrow hs
  have hcode : prog.code k = ins := entry_injective (he.symm.trans hins)
  rw [step_of_fetch_eq_some (ins := ins) (by rw [← hpc, hk, Program.fetch_gpow, hcode])]
  exact hexec

/-- The data a row's specification reads is the witness's. -/
private theorem environment_data {w : EnsembleWitness (leanIsaEnsemble prog)}
    {t : Air.Flat.Table K} (ht : t ∈ w.tables) (row : Array K) :
    (t.environment row).data = w.data :=
  w.same_data t ht

private theorem xor_step {w : EnsembleWitness (leanIsaEnsemble prog)}
    (h : SatisfiedBy prog input w) {t : Air.Flat.Table K} (ht : t ∈ w.tables)
    (htc : t.component = ⟨xorTable⟩) {row : Array K} (hrow : row ∈ t.table) :
    step prog (imageOf w.data).2 (xorSends (valueFromOffset XorRow 0 (t.environment row))).pull =
      some (xorSends (valueFromOffset XorRow 0 (t.environment row))).push := by
  have hspec := spec_of_satisfiedBy h t (w.mem_allTables_of_mem_tables ht) row hrow
  rw [htc] at hspec
  have hexec := (show XorSpec (valueFromOffset XorRow 0 (t.environment row))
    ((⟨xorTable⟩ : Component K).rowOutput (t.environment row)) (t.environment row).data
    from hspec).exec_eq
  rw [xor_rowOutput, environment_data ht] at hexec
  exact step_of_row h ht hrow (xor_sendsOpcode htc row)
    (Vector.toList_inj.mp (by rw [Vector.toList_append]; rfl)) rfl hexec

private theorem mul_step {w : EnsembleWitness (leanIsaEnsemble prog)}
    (h : SatisfiedBy prog input w) {t : Air.Flat.Table K} (ht : t ∈ w.tables)
    (htc : t.component = ⟨mulTable⟩) {row : Array K} (hrow : row ∈ t.table) :
    step prog (imageOf w.data).2 (mulSends (valueFromOffset MulRow 0 (t.environment row))).pull =
      some (mulSends (valueFromOffset MulRow 0 (t.environment row))).push := by
  have hspec := spec_of_satisfiedBy h t (w.mem_allTables_of_mem_tables ht) row hrow
  rw [htc] at hspec
  have hexec := (show MulSpec (valueFromOffset MulRow 0 (t.environment row))
    ((⟨mulTable⟩ : Component K).rowOutput (t.environment row)) (t.environment row).data
    from hspec).exec_eq
  rw [mul_rowOutput, environment_data ht] at hexec
  exact step_of_row h ht hrow (mul_sendsOpcode htc row)
    (Vector.toList_inj.mp (by rw [Vector.toList_append]; rfl)) rfl hexec

private theorem set_step {w : EnsembleWitness (leanIsaEnsemble prog)}
    (h : SatisfiedBy prog input w) {t : Air.Flat.Table K} (ht : t ∈ w.tables)
    (htc : t.component = ⟨setTable⟩) {row : Array K} (hrow : row ∈ t.table) :
    step prog (imageOf w.data).2 (setSends (valueFromOffset SetRow 0 (t.environment row))).pull =
      some (setSends (valueFromOffset SetRow 0 (t.environment row))).push := by
  have hspec := spec_of_satisfiedBy h t (w.mem_allTables_of_mem_tables ht) row hrow
  rw [htc] at hspec
  have hexec := (show SetSpec (valueFromOffset SetRow 0 (t.environment row))
    ((⟨setTable⟩ : Component K).rowOutput (t.environment row)) (t.environment row).data
    from hspec).exec_eq
  rw [set_rowOutput, environment_data ht] at hexec
  exact step_of_row h ht hrow (set_sendsOpcode htc row)
    (Vector.toList_inj.mp (by rw [Vector.toList_append]; simp [entry, setSends])) rfl hexec

private theorem deref_step {w : EnsembleWitness (leanIsaEnsemble prog)}
    (h : SatisfiedBy prog input w) {t : Air.Flat.Table K} (ht : t ∈ w.tables)
    (htc : t.component = ⟨derefTable⟩) {row : Array K} (hrow : row ∈ t.table) :
    step prog (imageOf w.data).2
        (derefSends (valueFromOffset DerefRow 0 (t.environment row))).pull =
      some (derefSends (valueFromOffset DerefRow 0 (t.environment row))).push := by
  have hspec := spec_of_satisfiedBy h t (w.mem_allTables_of_mem_tables ht) row hrow
  rw [htc] at hspec
  obtain ⟨mode, hb, hexec⟩ := (show DerefSpec (valueFromOffset DerefRow 0 (t.environment row))
    ((⟨derefTable⟩ : Component K).rowOutput (t.environment row)) (t.environment row).data
    from hspec)
  rw [deref_rowOutput, environment_data ht] at hexec
  exact step_of_row h ht hrow (deref_sendsOpcode htc row)
    (Vector.toList_inj.mp (by rw [Vector.toList_append]; simp [entry, derefSends, hb.flags_eq]))
    rfl hexec

private theorem jump_step {w : EnsembleWitness (leanIsaEnsemble prog)}
    (h : SatisfiedBy prog input w) {t : Air.Flat.Table K} (ht : t ∈ w.tables)
    (htc : t.component = ⟨jumpTable⟩) {row : Array K} (hrow : row ∈ t.table) :
    step prog (imageOf w.data).2
        (jumpSends (valueFromOffset JumpRow 0 (t.environment row))
          (row[size JumpRow + 1]?.getD 0)).pull =
      some (jumpSends (valueFromOffset JumpRow 0 (t.environment row))
        (row[size JumpRow + 1]?.getD 0)).push := by
  have hspec := spec_of_satisfiedBy h t (w.mem_allTables_of_mem_tables ht) row hrow
  rw [htc] at hspec
  have hexec := (show JumpSpec (valueFromOffset JumpRow 0 (t.environment row))
    ((⟨jumpTable⟩ : Component K).rowOutput (t.environment row)) (t.environment row).data
    from hspec).exec_eq
  rw [jump_rowOutput, environment_data ht] at hexec
  exact step_of_row h ht hrow (jump_sendsOpcode htc row)
    (Vector.toList_inj.mp (by rw [Vector.toList_append]; rfl)) rfl hexec

private theorem blake2s_step {w : EnsembleWitness (leanIsaEnsemble prog)}
    (h : SatisfiedBy prog input w) {t : Air.Flat.Table K} (ht : t ∈ w.tables)
    (htc : t.component = ⟨blake2sTable⟩) {row : Array K} (hrow : row ∈ t.table) :
    step prog (imageOf w.data).2
        (blake2sSends (valueFromOffset Blake2sRow 0 (t.environment row))).pull =
      some (blake2sSends (valueFromOffset Blake2sRow 0 (t.environment row))).push := by
  have hspec := spec_of_satisfiedBy h t (w.mem_allTables_of_mem_tables ht) row hrow
  rw [htc] at hspec
  have hexec := (show Blake2sSpec (valueFromOffset Blake2sRow 0 (t.environment row))
    ((⟨blake2sTable⟩ : Component K).rowOutput (t.environment row)) (t.environment row).data
    from hspec).exec_eq
  rw [blake2s_rowOutput, environment_data ht] at hexec
  exact step_of_row h ht hrow (blake2s_sendsOpcode htc row)
    (Vector.toList_inj.mp (by rw [Vector.toList_append]; rfl)) rfl hexec

/-- A row of a table of the witness either sends nothing on the state pull (a block) or is an
opcode row: it steps, it reads the bytecode at the counter it pulls, and it falls through
unless it reads a `JUMP`. -/
private theorem row_cases {w : EnsembleWitness (leanIsaEnsemble prog)}
    (h : SatisfiedBy prog input w) {t : Air.Flat.Table K} (ht : t ∈ w.tables) {row : Array K}
    (hrow : row ∈ t.table) :
    rowMessagesOn t row StatePull.toRaw = [] ∨
      ∃ s, SendsOpcode t row s ∧ step prog (imageOf w.data).2 s.pull = some s.push ∧
        s.bc.pc = s.pull.pc ∧
        (s.bc.opcode = Opcode.jump.code ∨ s.push = ⟨g * s.pull.pc, s.pull.fp⟩) := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ht
  have h8 : j < 8 := by rw [← w.same_length] at hj; exact hj
  have hc : (w.tables[j]'hj).component = (leanIsaEnsemble prog).tables[j]'h8 :=
    (w.same_circuits j h8).symm
  interval_cases j
  · exact Or.inr ⟨_, xor_sendsOpcode hc row, xor_step h ht hc hrow, rfl, Or.inr rfl⟩
  · exact Or.inr ⟨_, mul_sendsOpcode hc row, mul_step h ht hc hrow, rfl, Or.inr rfl⟩
  · exact Or.inr ⟨_, set_sendsOpcode hc row, set_step h ht hc hrow, rfl, Or.inr rfl⟩
  · exact Or.inr ⟨_, deref_sendsOpcode hc row, deref_step h ht hc hrow, rfl, Or.inr rfl⟩
  · exact Or.inr ⟨_, jump_sendsOpcode hc row, jump_step h ht hc hrow, rfl, Or.inl rfl⟩
  · exact Or.inr ⟨_, blake2s_sendsOpcode hc row, blake2s_step h ht hc hrow, rfl, Or.inr rfl⟩
  · left
    rw [memBlock_rowMessagesOn hc row rfl, ite_eq_right (by decide), ite_eq_right (by decide)]
  · left
    rw [bytecodeBlock_rowMessagesOn hc row rfl, ite_eq_right (by decide),
      ite_eq_right (by decide)]

/-- In a witness of the constraint statement, every row is a step of the machine from the state
it pulls to the state it pushes. -/
theorem rowSteps_of_satisfiedBy {w : EnsembleWitness (leanIsaEnsemble prog)}
    (h : SatisfiedBy prog input w) :
    ∀ t ∈ w.tables, ∀ row ∈ t.table, ∀ r r' : Regs K,
      rowMessagesOn t row StatePull.toRaw = [#[r.pc, r.fp]] →
      rowMessagesOn t row StatePush.toRaw = [#[r'.pc, r'.fp]] →
        step prog (imageOf w.data).2 r = some r' := by
  intro t ht row hrow r r' hpull hpush
  rcases row_cases h ht hrow with hnil | ⟨s, hs, hstep, -, -⟩
  · rw [hnil] at hpull
    exact absurd hpull.symm (List.cons_ne_nil _ _)
  · rw [hs.state_pull, List.cons.injEq] at hpull
    rw [hs.state_push, List.cons.injEq] at hpush
    obtain ⟨hpc, hfp⟩ := pair_eq hpull.1
    obtain ⟨hpc', hfp'⟩ := pair_eq hpush.1
    obtain ⟨pc, fp⟩ := r
    obtain ⟨pc', fp'⟩ := r'
    dsimp only at hpc hfp hpc' hfp'
    subst hpc hfp hpc' hfp'
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
    {w : EnsembleWitness (leanIsaEnsemble prog)} (h : SatisfiedBy prog input w) :
    ∀ t ∈ w.tables, ∀ row ∈ t.table, ∀ pc fp : K,
      #[pc, fp] ∈ rowMessagesOn t row StatePull.toRaw → pc ≠ prog.finalPc := by
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
    have hpushed : #[gpow (2 ^ prog.logSize), s.pull.fp] ∈ messagesOn w StatePush.toRaw := by
      rw [messagesOn_eq_flatMap, List.mem_flatMap]
      refine ⟨t, w.mem_allTables_of_mem_tables ht, List.mem_flatMap.mpr ⟨row, hrow, ?_⟩⟩
      rw [hs.state_push, hpush, hpc, g_mul_finalPc]
      exact List.mem_singleton_self _
    have hpulled := h.state_balanced.mem_iff.mp hpushed
    rw [messagesOn_eq_flatMap, List.mem_flatMap] at hpulled
    obtain ⟨t', ht', hm'⟩ := hpulled
    obtain ⟨row', hrow', hm'⟩ := List.mem_flatMap.mp hm'
    rcases List.mem_cons.mp ht' with rfl | ht''
    · -- The verifier pulls `g^(N_prog - 1)`.
      rw [verifier_rowMessagesOn (prog := prog) rfl, ite_eq_right (by decide),
        ite_eq_left (show StatePull.toRaw.name = StatePull.name from rfl),
        List.mem_singleton] at hm'
      have := gpow_injOn hN (lt_of_le_of_lt (Nat.sub_le _ _) hN) (pair_eq hm').1
      have := Nat.one_le_two_pow (n := prog.logSize)
      omega
    · -- A row pulls only a bytecode address.
      rcases row_cases h ht'' hrow' with hnil' | ⟨s', hs', -, hbcpc', -⟩
      · rw [hnil'] at hm'
        exact List.not_mem_nil hm'
      rw [hs'.state_pull, List.mem_singleton] at hm'
      obtain ⟨k', hk', -⟩ := bytecode_of_row h ht'' hrow' hs'
      have := gpow_injOn hN (lt_trans k'.isLt hN) ((pair_eq hm').1.trans (hbcpc'.symm.trans hk'))
      have := k'.isLt
      omega

end LeanerVM.Arithmetization
