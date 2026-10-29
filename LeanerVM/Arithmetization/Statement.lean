/-
  LeanerVM.Arithmetization.Statement

  The constraint statement of leanISA: the ensemble of the six opcode tables, the two seed
  blocks and the verifier; Clean's multiset balance; the checks the verifier makes on the
  announced instance; the relation `SatisfiedBy` the two T1 theorems connect to
  `ValidExecution`; and what it means for a witness to represent a trace.
-/

module

public import LeanerVM.Arithmetization.Boundary
public import LeanerVM.Arithmetization.Tables.Xor
public import LeanerVM.Arithmetization.Tables.MulNative
public import LeanerVM.Arithmetization.Tables.SetConstant
public import LeanerVM.Arithmetization.Tables.Deref
public import LeanerVM.Arithmetization.Tables.Jump
public import LeanerVM.Arithmetization.Tables.Blake2s
public import Clean.Air.FlatEnsemble

@[expose] public section

/-!
# The constraint statement

leanISA roadmap Layer 8 (`docs/roadmap/leanisa-blueprint.md`), at leanVM pin
`a386121f84292f6fa663aaa3e570c15bc0240ea2` and Clean pin `9dd71e82`. Category A for the
statement itself, which is what the M3 model means by an accepted instance (specification §5,
`doc/leanvm/body/05-arithmetization.tex:4`: "an instance is accepted exactly when every
table's constraints hold and the bus balances", the balance being the multiset equality of
`:14`), and Category B for what the verifier checks of an announced instance: the caps
(`crates/lean_vm/src/cpu/mod.rs:130-178`, `read_public`; §6.2 "Instance caps",
`06-bus-interactions.tex:80`), the nonzero count product (§6.2 "The count product", `:78`;
`cpu/layout.rs:73`, the count channel of the six tables' read-count columns, `:397-413`), the
public words against the committed memory (§8.2, `08-end-to-end-protocol.tex:27-33`), and the
BLAKE2s validity Flock proves (§8.5 "BLAKE2s validity"; `cpu/mod.rs:759-768`). The public parts
of the bus the verifier forms itself, the index column and the program's share of the bytecode
block (§8.5, `:70`; §6.5, `06-bus-interactions.tex:95`), are the fixed columns of the two blocks
(Layer 7). Artifact: the accept relation of the M3 constraint system and its ensemble. Direction:
a statement, no soundness or completeness theorem. Boundary: leanVM at the pin above, Clean
`9dd71e82`. Contribution: the statement surface of T1 (both directions); no target of
`docs/architecture.md` is claimed.

**The ensemble.** `leanIsaEnsemble prog κ` is Clean's `Ensemble`: the six opcode tables of Layer
6 as demand components, program-free as leanVM's AIRs are, the two blocks of Layer 7 as
preallocated components, the memory block of height `2^κ` for the announced memory log-size `κ`
and the bytecode block of the program with its fixed entry columns, the three channels of Layer
5, and the verifier `leanIsaVerifier prog`, as leanVM's `layout(prog, log_mem, taus, pi)` is a
function of the program and the memory size. A witness `w : EnsembleWitness (leanIsaEnsemble
prog κ)` is Clean's: one `Air.Flat.Table` of raw rows per component, each agreeing with its
component's fixed cells, and the public input; its prover data `w.data` is derived from the
tables (Clean's `deriveProverData`), so its `"mem"` table is the memory block's rows. The
constraints `w.Constraints` ("every component's constraints hold on every row") are Clean's,
consumed unchanged.

**Reading a witness.** Tables are read by position in the ensemble's `tables` (`tableAt`), and
messages by channel name and direction (`messagesOn`, `rowMessagesOn`, Clean's
`activeMessages`): Clean's `RawChannel` carries propositions and has no decidable equality, and
the channels have distinct names. A raw row is read as its typed row exactly as the component's
constraints read it (`memRowAt`, `blake2sRowAt`: Clean's `Component.rowInput`).

**Balance** is Clean's multiset balance on each of the three channels, `w.Balanced
.multiset`: every multiplicity is `0` or `1`, fewer than `2^64` interactions per channel, and
the messages of the active pushes are a permutation of those of the active pulls (§5.1
"Balance", `05-arithmetization.tex:14`), counted in `ℕ`, never a field sum (acceptance test 14).
`SatisfiedBy.perm` reads it as a permutation of `messagesOn`.

**The verifier's checks.** `CountsNonzero w` is the nonzero count product: every read pull of
the six tables carries a nonzero count, message index `1` (bus coordinate 2) of a memory or
bytecode tuple (§6.2 "The count product"; `layout.rs:73` and `:397-413`, the count channel
stacks the read-count columns of the six tables and nothing else, so the finalize counts of the
two blocks are outside it, as §6.2 "Nothing checks the finalize counts" says). `Caps w` is the
M3 part of `read_public` (`cpu/mod.rs:130-178`), which makes eight checks: (1) the announced
sizes have zero upper limbs (`:133`) and (2) the two public words have a zero third limb
(`:141-143`), both by type here; (3) the bytecode length is a power of two at most
`2^MAX_LOG_BYTECODE` (`:158-159`), `Program`'s by type; (4) the memory log-size is within
`[MIN_LOG_MEM, MAX_LOG_MEM]` (`:160`), a condition on the ensemble's `κ`; (5) every table height
is a power of two at most `2^MAX_LOG_ROWS` (`:161`); (6) the `BLAKE2S` table has at least
`2^n_blocks_log(1) = 2^3` rows (`:166`); (7) the WHIR rate (`:167`) and (8) the stacked size
`mu ∈ [MIN_MU, MAX_MU]` (`:174-176`) are parameters of the commitment, left to the protocol
layer. `Caps` transcribes (4), (5) and (6). These caps keep the total read count below
`2^64 - 1`, the bound Layer 9's bus argument needs (Lemma 6.3).

**The BLAKE2s validity.** `Blake2sRowsValid w`, every row of the `BLAKE2S` table satisfies
`Blake2sRelation` (Layer 6, the table's `Assumptions` field), is the one conjunct the verifier
enforces outside the bus: the table has no constraint on its eighteen limbs, and the
compression is proved by Flock on the region the limb columns are routed to (§8.5 "BLAKE2s
validity", Opening step 4; `cpu/mod.rs:759-768`). Clean's `EnsembleWitness.Constraints` does
not include a component's `Assumptions`, so the fact is a conjunct of the statement, and
`assumptions_of_blake2sRowsValid` turns it, with the caps, into the `w.Assumptions` Clean's
per-table soundness takes. The proof system's adaptor discharges it from the Flock region.

**The statement.** `SatisfiedBy prog input w` is the relation the proof system proves and
extracts (issue #13), a structure with named fields so that Layers 9 and 10 project the
conjunct they consume by name. Its `constraints` field is Clean's; only the `JUMP` table emits
an assertion (`tables.rs:724-731`), so the field reduces to the `JUMP` residuals. The
`public_input_eq` field is read by no component: the lanes bind the run through `word0_eq` and
`word1_eq`, the two public words at `g^0` and `g^1` of the image the data names (§8.2).

**The trace.** `AssignmentRepresents w t` says what a witness of `SatisfiedBy` is a witness
of: the image the data names is the trace's (`κ_eq`, `image_eq`; `assignmentRepresents_image`
reads the two as one equality of dependent pairs), and each consecutive pair `(r_k, r_{k+1})`
of the trace's register sequence (Layer 3's `Trace.regs`) occurs as the state pull and the state
push of some row of some table (`RowSteps`). Occurrence, not an injection of steps into rows.
The remaining rows are the closed walks of §8.3, about which nothing is claimed.

## Wrong readings excluded

* Balance is a permutation, not a field sum (acceptance test 14): `Balance.multiset`, never
  Clean's `Balance.logUp`, whose characteristic bound admits one interaction over `K`.
* A direction is an interaction's tag, never the sign of a multiplicity (acceptance test 13).
* The count product covers the six tables' read counts and nothing else: `CountsNonzero`
  quantifies over the pulls of `w.tables.take 6`, and a finalize count of `0` is rejected by
  balance alone (§6.2).
* The compression is not a constraint of the table and not a bus fact: `Blake2sRowsValid` is a
  conjunct of its own, discharged by Flock.
* No guarantee reads the program off the prover data (acceptance test 22): it is the bytecode
  block's fixed columns, which the verifier forms (decision 14); the derived `"bytecode"` rows
  are those columns, read by no channel.
* The public words are not on the bus (§8.2): `word0_eq` and `word1_eq` read the image the data
  names, as `HasPublicBoundary` reads the trace's.
* The state pull carries no guarantee (acceptance test 21): `AssignmentRepresents` claims the
  run's steps are rows, and nothing about the rows that are not.
-/

namespace LeanerVM.Arithmetization

open LeanerVM.Parameters LeanerVM.Semantics
open Air.Flat (Ensemble EnsembleWitness Component)

/-! ## The components -/

/-- The `XOR` component (Layer 6), a demand component on the state channel. -/
def xorComponent : Component K := { circuit := xorTable, generation := opcodeGeneration XorRow }

/-- The `MUL_NATIVE` component. -/
def mulComponent : Component K := { circuit := mulTable, generation := opcodeGeneration MulRow }

/-- The `SET_CONSTANT` component. -/
def setComponent : Component K := { circuit := setTable, generation := opcodeGeneration SetRow }

/-- The `DEREF` component. -/
def derefComponent : Component K :=
  { circuit := derefTable, generation := opcodeGeneration DerefRow }

/-- The `JUMP` component. -/
def jumpComponent : Component K := { circuit := jumpTable, generation := opcodeGeneration JumpRow }

/-- The `BLAKE2S` component: its rows assume the compression relation, which the ensemble
supplies from Flock (`Blake2sRowsValid`). -/
def blake2sComponent : Component K where
  circuit := blake2sTable
  generation := opcodeGeneration Blake2sRow
  Assumptions r _ := Blake2sRelation r
  circuit_assumptions_of_assumptions _ _ _ _ _ h := h

/-! ## Proof helpers -/

/-- The three channels of the ensemble. -/
private abbrev threeChannels : List (RawChannel K) :=
  [StateChannel.toRaw, MemChannel.toRaw, BytecodeChannel.toRaw]

private theorem xorTable_channels : xorTable.channels ⊆ threeChannels := by
  change [StateChannel.toRaw, BytecodeChannel.toRaw, MemChannel.toRaw, MemChannel.toRaw, MemChannel.toRaw] ++ [StateChannel.toRaw, MemChannel.toRaw, BytecodeChannel.toRaw] ⊆ _
  simp

private theorem mulTable_channels : mulTable.channels ⊆ threeChannels := by
  change [StateChannel.toRaw, BytecodeChannel.toRaw, MemChannel.toRaw, MemChannel.toRaw, MemChannel.toRaw] ++ [StateChannel.toRaw, MemChannel.toRaw, BytecodeChannel.toRaw] ⊆ _
  simp

private theorem setTable_channels : setTable.channels ⊆ threeChannels := by
  change [StateChannel.toRaw, BytecodeChannel.toRaw, MemChannel.toRaw] ++ [StateChannel.toRaw, MemChannel.toRaw, BytecodeChannel.toRaw] ⊆ _
  simp

private theorem derefTable_channels : derefTable.channels ⊆ threeChannels := by
  change [StateChannel.toRaw, BytecodeChannel.toRaw, MemChannel.toRaw, MemChannel.toRaw, MemChannel.toRaw] ++ [StateChannel.toRaw, MemChannel.toRaw, BytecodeChannel.toRaw] ⊆ _
  simp

private theorem jumpTable_channels : jumpTable.channels ⊆ threeChannels := by
  change [StateChannel.toRaw, BytecodeChannel.toRaw, MemChannel.toRaw, MemChannel.toRaw, MemChannel.toRaw] ++ [StateChannel.toRaw, MemChannel.toRaw, BytecodeChannel.toRaw] ⊆ _
  simp

private theorem blake2sTable_channels : blake2sTable.channels ⊆ threeChannels := by
  change [StateChannel.toRaw, BytecodeChannel.toRaw, MemChannel.toRaw, MemChannel.toRaw, MemChannel.toRaw, MemChannel.toRaw, MemChannel.toRaw, MemChannel.toRaw, MemChannel.toRaw, MemChannel.toRaw, MemChannel.toRaw] ++ [StateChannel.toRaw, MemChannel.toRaw, BytecodeChannel.toRaw] ⊆ _
  simp

private theorem memTable_channels : memTable.channels ⊆ threeChannels := by
  change [MemChannel.toRaw] ++ [MemChannel.toRaw] ⊆ _
  simp

private theorem bytecodeTable_channels : bytecodeTable.channels ⊆ threeChannels := by
  change [BytecodeChannel.toRaw] ++ [BytecodeChannel.toRaw] ⊆ _
  simp

/-! ## The ensemble -/

/-- The leanISA ensemble of the public program `prog` at memory log-size `κ`: the six opcode
tables (Layer 6), the memory and bytecode blocks (Layer 7), the three channels (Layer 5), and
the verifier `leanIsaVerifier prog` (`layout.rs:352-395`; decision 14). -/
def leanIsaEnsemble (prog : Program) (κ : ℕ) : Ensemble K PublicIO where
  tables := [xorComponent, mulComponent, setComponent, derefComponent, jumpComponent,
    blake2sComponent, memComponent κ, bytecodeComponent prog]
  unique_names := by
    show ["xor", "mul_native", "set_constant", "deref", "jump", "blake2s", "mem",
      "bytecode"].Nodup
    decide
  channels := [StateChannel.toRaw, MemChannel.toRaw, BytecodeChannel.toRaw]
  unique_channel_names := by
    show ["state", "memory", "bytecode"].Nodup
    decide
  verifier := leanIsaVerifier prog
  tables_channels := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨xorTable_channels, mulTable_channels, setTable_channels, derefTable_channels,
      jumpTable_channels, blake2sTable_channels, memTable_channels, bytecodeTable_channels⟩
  verifier_channels := by
    simp [circuit_norm, leanIsaVerifier]

/-! ## Reading a witness -/

variable {prog : Program} {κ : ℕ}

/-- The witness's table of component `j`, in the order of the ensemble's `tables`: `XOR`,
`MUL_NATIVE`, `SET_CONSTANT`, `DEREF`, `JUMP`, `BLAKE2S`, then the memory block and the
bytecode block. -/
def tableAt (w : EnsembleWitness (leanIsaEnsemble prog κ)) (j : Fin 8) : Air.Flat.Table K :=
  w.tables[(j : ℕ)]'(by rw [← w.same_length]; exact j.isLt)

/-- The rows of the `BLAKE2S` table. -/
abbrev blake2sRows (w : EnsembleWitness (leanIsaEnsemble prog κ)) : List (Array K) :=
  (tableAt w 5).table

/-- The rows of the memory block. -/
abbrev memBlockRows (w : EnsembleWitness (leanIsaEnsemble prog κ)) : List (Array K) :=
  (tableAt w 6).table

/-- The rows of the bytecode block. -/
abbrev bytecodeBlockRows (w : EnsembleWitness (leanIsaEnsemble prog κ)) : List (Array K) :=
  (tableAt w 7).table

/-- The messages the witness sends on the channel `c` in the direction `d`, in the order of its
interactions (the verifier's first, then table by table and row by row): Clean's
`activeMessages` of its interactions on the channel of that name. -/
def messagesOn (w : EnsembleWitness (leanIsaEnsemble prog κ)) (c : RawChannel K) (d : BusDir) :
    List (Array K) :=
  activeMessages (w.interactions.filter (·.channel.name = c.name)) d

/-- The messages one row of a table sends on the channel `c` in the direction `d`. -/
def rowMessagesOn (t : Air.Flat.Table K) (row : Array K) (c : RawChannel K) (d : BusDir) :
    List (Array K) :=
  activeMessages
    ((t.component.operations.interactionValues (t.environment row)).filter
      (·.channel.name = c.name)) d

/-- A raw row of the memory block, read as its typed row: the first `size MemRow` cells, a
missing cell `0`, as the block's constraints read it (Clean's `Component.rowInput`). -/
def memRowAt (w : EnsembleWitness (leanIsaEnsemble prog κ)) (row : Array K) : MemRow K :=
  valueFromOffset MemRow 0 (Environment.fromArray row w.data)

/-- A raw row of the bytecode block, read as its typed row, likewise. -/
def bytecodeRowAt (w : EnsembleWitness (leanIsaEnsemble prog κ)) (row : Array K) :
    BytecodeRow K :=
  valueFromOffset BytecodeRow 0 (Environment.fromArray row w.data)

/-- A raw row of the `BLAKE2S` table, read as its typed row, likewise. -/
def blake2sRowAt (w : EnsembleWitness (leanIsaEnsemble prog κ)) (row : Array K) : Blake2sRow K :=
  valueFromOffset Blake2sRow 0 (Environment.fromArray row w.data)

/-! ## The verifier's checks -/

/-- Every read pull of the six tables carries a nonzero count, message index `1` (bus
coordinate 2) of the memory and bytecode tuples: the nonzero count product (§6.2 "The count
product"; `layout.rs:73`, `:397-413`). The finalize counts of the two blocks are outside it
(§6.2). Both tuples have at least two coordinates (Layer 5's `MemMsg`, `BytecodeMsg`), so the
bound is never the reason the conjunct holds. -/
def CountsNonzero (w : EnsembleWitness (leanIsaEnsemble prog κ)) : Prop :=
  ∀ t ∈ w.tables.take 6, ∀ i ∈ t.interactions,
    (i.channel.name = MemChannel.name ∨ i.channel.name = BytecodeChannel.name) →
      i.direction = .pull → ∀ h : 1 < i.msg.size, i.msg[1] ≠ 0

/-- The M3 checks of the announced instance, three of `read_public`'s eight
(`cpu/mod.rs:130-178`; §6.2 "Instance caps"): the memory log-size window, the height cap and the
`BLAKE2S` floor. The bytecode length and the public words' third limbs are checked by type
(`Program`, `PublicInput`); the WHIR rate and the stacked size are the protocol layer's (see
the module docstring). -/
structure Caps (w : EnsembleWitness (leanIsaEnsemble prog κ)) : Prop where
  /-- `MIN_LOG_MEM ≤ log_mem` (`:160`). -/
  minLogMem_le : minLogMem ≤ κ
  /-- `log_mem ≤ MAX_LOG_MEM` (`:160`). -/
  le_maxLogMem : κ ≤ maxLogMem
  /-- Every table's height is a power of two at most `2^MAX_LOG_ROWS`. Rust caps the six
  opcode tables' announced log-heights (`:161`, `:114-117`); the memory block's height is
  `2^log_mem`, within the bound by `:160`, and the bytecode block's `2^prog.logSize`, within it
  by `:158-159`, since `maxLogMem = maxLogBytecode = maxLogRows`. -/
  heights : ∀ t ∈ w.tables, ∃ τ ≤ maxLogRows, t.table.length = 2 ^ τ
  /-- The `BLAKE2S` table has at least `2^n_blocks_log(1)` rows (`:166`; Layer 2's
  `minLogRowsBlake2s`). -/
  blake2s_height : 2 ^ minLogRowsBlake2s ≤ (blake2sRows w).length

/-! ## The BLAKE2s validity -/

/-- Every row of the `BLAKE2S` table satisfies the compression relation on its eighteen limbs
(Layer 6's `Blake2sRelation`, the component's `Assumptions`): what Flock proves of the region
the limb columns are routed to (§8.5 "BLAKE2s validity"; `cpu/mod.rs:759-768`). The one
conjunct enforced outside the bus; the proof system discharges it from the Flock region. -/
def Blake2sRowsValid (w : EnsembleWitness (leanIsaEnsemble prog κ)) : Prop :=
  ∀ row ∈ blake2sRows w, Blake2sRelation (blake2sRowAt w row)

/-! ## The statement -/

/-- The witness `w` satisfies the constraint system of `prog` on `input`: the relation the
proof system proves and extracts (issue #13). `constraints` and `balanced` are Clean's;
`counts_nonzero` and `caps` are the verifier's checks; `blake2s_valid` is Flock's; the two
words are §8.2's evaluation claim against the committed memory. -/
structure SatisfiedBy (prog : Program) (input : PublicInput)
    (w : EnsembleWitness (leanIsaEnsemble prog κ)) : Prop where
  /-- The public input is the run's: the four lanes (Layer 7). No component reads them; the
  run is bound to them by `word0_eq` and `word1_eq`. -/
  public_input_eq : w.publicInput = PublicIO.ofInput input
  /-- Every component's constraints hold on every row (Clean): the `JUMP` residuals, the
  other components having none. -/
  constraints : w.Constraints
  /-- The three channels balance as multisets (§5.1; Clean's `Balance.multiset`). -/
  balanced : w.Balanced .multiset
  /-- Every read count is nonzero (§6.2). -/
  counts_nonzero : CountsNonzero w
  /-- The announced sizes are within the caps (§6.2). -/
  caps : Caps w
  /-- Every `BLAKE2S` row compresses (§8.5). -/
  blake2s_valid : Blake2sRowsValid w
  /-- The first word of the image is `input₀ + input₁·y` (§8.2). -/
  word0_eq : (imageOf w.data).2.read (gpow 0) = some input.word0
  /-- The second word of the image is `input₂ + input₃·y` (§8.2). -/
  word1_eq : (imageOf w.data).2.read (gpow 1) = some input.word1

/-! ## The trace a witness represents -/

/-- Some row of some table steps from `r` to `r'`: its one state pull is `r` and its one state
push is `r'` (§6.1). -/
def RowSteps (w : EnsembleWitness (leanIsaEnsemble prog κ)) (r r' : Regs K) : Prop :=
  ∃ t ∈ w.tables, ∃ row ∈ t.table,
    rowMessagesOn t row StateChannel.toRaw .pull = [#[r.pc, r.fp]] ∧
      rowMessagesOn t row StateChannel.toRaw .push = [#[r'.pc, r'.fp]]

/-- The witness `w` represents the trace `t`: the image the data names is the trace's, and
each consecutive pair of the trace's register sequence `r_0, …, r_steps` (Layer 3's
`Trace.regs`) occurs as the state pull and push of some row (occurrence, not an injection of
steps into rows). The remaining rows are the closed walks of §8.3. -/
structure AssignmentRepresents (w : EnsembleWitness (leanIsaEnsemble prog κ)) (t : Trace prog) :
    Prop where
  /-- The memory log-size is the trace's. -/
  κ_eq : (imageOf w.data).1 = t.κ
  /-- Every word of the image is the trace's. -/
  image_eq : ∀ i (hi : i < 2 ^ t.κ), (imageOf w.data).2 ⟨i, κ_eq ▸ hi⟩ = t.image ⟨i, hi⟩
  /-- Each step of the register sequence occurs as some row's state pull and push. -/
  regs_embed : ∀ k (hk : k + 1 < t.regs.length), RowSteps w t.regs[k] t.regs[k + 1]

/-! ## The trace interface -/

/-- A computable execution of every satisfying witness: `traceOf` returns, on every witness of
the constraint statement at any memory log-size, a trace the witness represents and that is a
valid execution of the program on the input. The interface the proof system's execution-level
headline takes; it is inhabited, for a program whose sentinel slot is not a `JUMP`, by
`leanIsaTraceExtraction` (`LeanerVM.Arithmetization.Soundness`). -/
structure TraceExtraction (prog : Program) where
  /-- The trace of a witness, if one is found. -/
  traceOf : PublicInput → (κ : ℕ) → EnsembleWitness (leanIsaEnsemble prog κ) → Option (Trace prog)
  /-- On a satisfying witness, a trace is found, the witness represents it, and it is a valid
  execution. -/
  valid : ∀ input κ (w : EnsembleWitness (leanIsaEnsemble prog κ)), SatisfiedBy prog input w →
    ∃ t, traceOf input κ w = some t ∧ AssignmentRepresents w t ∧ ValidExecution prog input t

/-! ## Building a witness -/

/-- A table of rows of the component `c`, carrying its own input rows as its prover data; a
witness replaces that data by the ensemble's (`witnessOfTables`). -/
def tableOf (c : Component K) (rows : List (Array K)) (hw : ∀ row ∈ rows, row.size = c.width)
    (hl : rows.length ≤ UInt64.size) (hf : c.FixedRowsMatch rows) : Air.Flat.Table K where
  component := c
  table := rows
  data name n := if c.circuit.name = name then (rows.map (Air.Flat.rowPrefix n)).toArray else #[]
  uniform_width := hw
  length_le := hl
  fixed_rows_match := hf
  data_consistent := by simp

/-- Tables whose components are the ensemble's have distinct component names. -/
theorem names_nodup {ts : List (Air.Flat.Table K)}
    (hc : ts.map (·.component) = (leanIsaEnsemble prog κ).tables) :
    (ts.map fun t ↦ t.component.circuit.name).Nodup := by
  have h := (leanIsaEnsemble prog κ).unique_names
  rw [← hc, List.map_map] at h
  exact h

/-- The witness of tables `ts` whose components are the ensemble's, in order, with the public
input `pi`: Clean's `withDerivedData` gives every table the prover data derived from all of
them. -/
def witnessOfTables (prog : Program) (κ : ℕ) (pi : PublicIO K) (ts : List (Air.Flat.Table K))
    (hc : ts.map (·.component) = (leanIsaEnsemble prog κ).tables) :
    EnsembleWitness (leanIsaEnsemble prog κ) where
  tables := Air.Flat.withDerivedData ts (names_nodup hc)
  publicInput := pi
  same_length := by
    have h := (Air.Flat.withDerivedData_map_component ts (names_nodup hc)).trans hc
    simpa using (congrArg List.length h).symm
  same_circuits i hi := by
    have h := (Air.Flat.withDerivedData_map_component ts (names_nodup hc)).trans hc
    rw [List.getElem_of_eq h.symm hi]
    exact List.getElem_map _
  same_data := Air.Flat.withDerivedData_data ts (names_nodup hc)

/-- The tables of `witnessOfTables` are `ts`, up to their prover data. -/
theorem witnessOfTables_map {pi : PublicIO K} {ts : List (Air.Flat.Table K)}
    {hc : ts.map (·.component) = (leanIsaEnsemble prog κ).tables} :
    (witnessOfTables prog κ pi ts hc).tables.map (fun t ↦ (t.component, t.table)) =
      ts.map fun t ↦ (t.component, t.table) :=
  Air.Flat.withDerivedData_map ts (names_nodup hc)

/-- The prover data of `witnessOfTables` is the data derived from `ts`. -/
theorem witnessOfTables_data {pi : PublicIO K} {ts : List (Air.Flat.Table K)}
    {hc : ts.map (·.component) = (leanIsaEnsemble prog κ).tables} :
    (witnessOfTables prog κ pi ts hc).data = Air.Flat.deriveProverData ts :=
  Air.Flat.deriveProverData_congr witnessOfTables_map

/-! ## Load-bearing lemmas -/

/-- A raw row written from a typed row reads back as it: reading at offset `0` inverts
`toElements`, for any row type and any data. -/
theorem rowAt_toElements {Row : TypeMap} [ProvableType Row] (data : ProverData K) (r : Row K) :
    valueFromOffset Row 0 (Environment.fromArray (toElements r).toArray data) = r := by
  unfold valueFromOffset
  convert ProvableType.fromElements_toElements r
  refine Vector.ext fun i hi ↦ ?_
  rw [Vector.getElem_mapRange]
  show ((toElements r).toArray[0 + i]?).getD 0 = _
  rw [Nat.zero_add, Array.getElem?_eq_getElem (by simpa using hi), Option.getD_some,
    Vector.getElem_toArray]

/-- `memRowAt` inverts `toElements`. -/
theorem memRowAt_toElements (w : EnsembleWitness (leanIsaEnsemble prog κ)) (r : MemRow K) :
    memRowAt w (toElements r).toArray = r :=
  rowAt_toElements w.data r

/-- `blake2sRowAt` inverts `toElements`. -/
theorem blake2sRowAt_toElements (w : EnsembleWitness (leanIsaEnsemble prog κ))
    (r : Blake2sRow K) : blake2sRowAt w (toElements r).toArray = r :=
  rowAt_toElements w.data r

/-- A table of the witness is `tableAt w j` for some `j`. -/
theorem mem_tables_iff {w : EnsembleWitness (leanIsaEnsemble prog κ)} {t : Air.Flat.Table K} :
    t ∈ w.tables ↔ ∃ j : Fin 8, tableAt w j = t := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, by rwa [← w.same_length] at hi⟩, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j, _, rfl⟩

/-- The component of `tableAt w j` is the ensemble's `j`-th. -/
theorem tableAt_component (w : EnsembleWitness (leanIsaEnsemble prog κ)) (j : Fin 8) :
    (tableAt w j).component = (leanIsaEnsemble prog κ).tables[(j : ℕ)] :=
  (w.same_circuits j j.isLt).symm

/-- Every table of a witness carries the witness's data. -/
theorem table_data (w : EnsembleWitness (leanIsaEnsemble prog κ)) {t : Air.Flat.Table K}
    (ht : t ∈ w.tables) : t.data = w.data :=
  w.same_data t ht

/-- The table at a position carries the witness's data. -/
theorem tableAt_data (w : EnsembleWitness (leanIsaEnsemble prog κ)) (j : Fin 8) :
    (tableAt w j).data = w.data :=
  w.same_data _ (List.getElem_mem _)

/-- The `"mem"` table of a witness's data has the memory block's `2^κ` rows. -/
theorem memRows_size (w : EnsembleWitness (leanIsaEnsemble prog κ)) (hκ : κ ≤ maxLogMem) :
    (memRows w.data).size = 2 ^ κ := by
  have h := w.getRows_size_of_preallocated (component := memComponent κ)
    (by simp [leanIsaEnsemble]) (mode := memMode κ) rfl
  rw [memRows, Array.size_map]
  refine h.trans ?_
  show (UInt64.ofNat (2 ^ κ)).toNat = 2 ^ κ
  have hκ64 : κ < 64 := lt_of_le_of_lt hκ (by decide)
  exact UInt64.toNat_ofNat_of_lt' (Nat.pow_lt_pow_right (by norm_num) hκ64)

/-- The memory block of a witness within the cap: `2^κ` rows, row `i` at the address `g^i` (the
fixed column) and holding row `i` of the data's `"mem"` table (the derived data). -/
theorem memBlock_rows (w : EnsembleWitness (leanIsaEnsemble prog κ)) (hκ : κ ≤ maxLogMem) :
    (memBlockRows w).length = 2 ^ κ ∧ ∀ i (hi : i < (memBlockRows w).length),
      (memRowAt w (memBlockRows w)[i]).idx = gpow i ∧
        (memRows w.data)[i]? = some (memRowAt w (memBlockRows w)[i]).m := by
  have hκ64 : κ < 64 := lt_of_le_of_lt hκ (by decide)
  have h64 : 2 ^ κ < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) hκ64
  have hm := (tableAt w 6).fixed_rows_match
  rw [tableAt_component] at hm
  obtain ⟨hlen, hfix⟩ := hm
  have hlen' : (memBlockRows w).length = 2 ^ κ := by
    rw [memBlockRows, hlen]
    exact UInt64.toNat_ofNat_of_lt' h64
  refine ⟨hlen', fun i hi ↦ ⟨?_, ?_⟩⟩
  · have h := (memMode_fixedAt_iff (hlen' ▸ hi) hκ64 _).mp (hfix i hi)
    rw [memRowAt, Air.Flat.valueFromOffset_fromArray]
    exact h
  · have hd : w.data memDataName (size MemRow) =
        ((memBlockRows w).map (Air.Flat.rowPrefix (size MemRow))).toArray := by
      have h := (tableAt w 6).data_consistent
      rw [tableAt_data, tableAt_component] at h
      exact h
    rw [memRows, ProverData.getRows, hd, Array.getElem?_map, Array.getElem?_map,
      List.getElem?_toArray, List.getElem?_map, List.getElem?_eq_getElem hi]
    simp only [Option.map_some, memRowAt, Air.Flat.valueFromOffset_fromArray]

/-- The bytecode block of a witness: `2^prog.logSize` rows, row `i` at the counter `g^i` and
holding the program's entry at slot `i` (the fixed columns). -/
theorem bytecodeBlock_rows (w : EnsembleWitness (leanIsaEnsemble prog κ)) :
    (bytecodeBlockRows w).length = 2 ^ prog.logSize ∧ ∀ i (hi : i < (bytecodeBlockRows w).length),
      ∃ k : Fin (2 ^ prog.logSize), (k : ℕ) = i ∧
        (bytecodeRowAt w (bytecodeBlockRows w)[i]).idx = gpow i ∧
        #v[(bytecodeRowAt w (bytecodeBlockRows w)[i]).opcode] ++
          (bytecodeRowAt w (bytecodeBlockRows w)[i]).op = entry (prog.code k) := by
  have h64 : 2 ^ prog.logSize < 2 ^ 64 :=
    Nat.pow_lt_pow_right (by norm_num) (lt_of_le_of_lt prog.logSize_le (by decide))
  have hm := (tableAt w 7).fixed_rows_match
  rw [tableAt_component] at hm
  obtain ⟨hlen, hfix⟩ := hm
  have hlen' : (bytecodeBlockRows w).length = 2 ^ prog.logSize := by
    rw [bytecodeBlockRows, hlen]
    exact UInt64.toNat_ofNat_of_lt' h64
  refine ⟨hlen', fun i hi ↦ ⟨⟨i, hlen' ▸ hi⟩, rfl, ?_⟩⟩
  have h := (bytecodeMode_fixedAt_iff prog (hlen' ▸ hi) _).mp (hfix i hi)
  rw [bytecodeRowAt, Air.Flat.valueFromOffset_fromArray]
  exact h

/-- Within the cap, the image a witness's data names has log-size `κ`. -/
theorem imageOf_data_fst {w : EnsembleWitness (leanIsaEnsemble prog κ)} (hκ : κ ≤ maxLogMem) :
    (imageOf w.data).1 = κ :=
  imageOf_fst hκ (memRows_size w hκ)

/-- The messages of a witness on a channel of the ensemble balance: Clean's multiset balance
read as a permutation of `messagesOn`. -/
theorem SatisfiedBy.perm {input : PublicInput} {w : EnsembleWitness (leanIsaEnsemble prog κ)}
    (h : SatisfiedBy prog input w) {c : RawChannel K}
    (hc : c ∈ (leanIsaEnsemble prog κ).channels) :
    (messagesOn w c .push).Perm (messagesOn w c .pull) := by
  have hb := (h.balanced c hc).2.2
  rw [EnsembleWitness.interactionsWith_eq_filter_name hc] at hb
  unfold messagesOn
  convert hb using 3

/-- The BLAKE2s validity and the memory cap make Clean's `w.Assumptions`: the `BLAKE2S`
component's `Assumptions` is `Blake2sRelation`, the memory block's the derived data's shape,
and every other component's is `True`. This is the form Clean's per-table soundness takes
(Layer 10). -/
theorem assumptions_of_blake2sRowsValid {w : EnsembleWitness (leanIsaEnsemble prog κ)}
    (hκ : κ ≤ maxLogMem) (h : Blake2sRowsValid w) : w.Assumptions := by
  intro t ht
  have hd : t.data = w.data := w.same_data t ht
  obtain ⟨j, rfl⟩ := mem_tables_iff.mp ht
  intro row hrow
  rw [Air.Flat.Component.RowAssumptions, tableAt_component, Air.Flat.Table.environment, hd]
  fin_cases j
  · exact trivial
  · exact trivial
  · exact trivial
  · exact trivial
  · exact trivial
  · exact h row hrow
  · exact ⟨hκ, memRows_size w hκ⟩
  · exact trivial

/-- The image a representing witness names is the trace's, as one equality of dependent
pairs. -/
theorem assignmentRepresents_image {w : EnsembleWitness (leanIsaEnsemble prog κ)}
    {t : Trace prog} (h : AssignmentRepresents w t) : imageOf w.data = ⟨t.κ, t.image⟩ := by
  obtain ⟨κ', image, steps⟩ := t
  obtain ⟨hκ, himage, -⟩ := h
  revert hκ himage
  generalize imageOf w.data = s
  obtain ⟨κ'', image'⟩ := s
  intro hκ himage
  dsimp only at hκ
  subst hκ
  congr 1
  funext ⟨i, hi⟩
  exact himage i hi

end LeanerVM.Arithmetization
