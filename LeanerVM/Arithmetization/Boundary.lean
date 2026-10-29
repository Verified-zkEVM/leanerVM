/-
  LeanerVM.Arithmetization.Boundary

  The three bus blocks owned by no table: the memory seed/finalize block, the bytecode
  seed/finalize block, each a preallocated Clean component with fixed columns, and the
  verifier's state boundary.
-/

module

public import LeanerVM.Arithmetization.Tables.Basic
public import LeanerVM.Semantics.Execution
public import Clean.Air.FlatComponent
public import Clean.Air.Verifier
public import Clean.Utils.Tactics.CircuitProofStart

@[expose] public section

/-!
# The boundary blocks

leanISA roadmap Layer 7 (`docs/roadmap/leanisa-blueprint.md`), at leanVM pin
`a386121f84292f6fa663aaa3e570c15bc0240ea2` and Clean pin `9dd71e82`. Category B: the three
blocks are `crates/lean_vm/src/cpu/layout.rs:352-395` (the "shared blocks" of `layout`), matching
specification §6.1 (`doc/leanvm/body/06-bus-interactions.tex:8`, the state boundary), §6.2
"Flush rules" (`:44-46`, seed and finalize), §6.4 (the bytecode array), §6.5 (`:95`, the index
column), and §8.5 (`08-end-to-end-protocol.tex:70`: "three blocks per side belong to no
table"). The committed columns are `MEM_LO, MEM_HI, MEM_TOP, MFCNT` and `BFCNT`
(`layout.rs:13-17`); the address column is `Coord::Index`, which the verifier evaluates itself
(`crates/primitives/src/field/mod.rs:105-113`, `index_mle(ζ) = ∏_k (1 + ζ_k (1 + g^{2^k}))`,
`leaf.rs:444`); the bytecode entry rides eight *public* columns (`bytecode_columns`,
`layout.rs:229-290`, Layer 4's `entry`); the sentinel counter `g^(N_prog - 1)` is derived from
the public program's length and written into the state block as a constant (`layout.rs:335`,
`final_pc`; `:357`, `Const(g_pow(final_pc))`).

**The three blocks.** Every table row of Layer 6 pulls its state and pushes its successor,
and reads its cells and its instruction through the counted lookup of §6.2. What closes the
three channels are the boundary blocks: the *memory block* pushes each word of the image
once, as `(g^i, 1, mem[i])`, and pulls it back with its final count, `(g^i, g^(A[i]), mem[i])`;
the *bytecode block* does the same for each slot of the public program; the *verifier* pushes
the initial state `(1, 1)` and pulls the final state `(g^(N_prog - 1), 1)`. None has a
constraint: each is its two flushes.

**Fixed columns.** The two blocks are *preallocated* Clean components (`Air.Flat.Component`
with `generation := .preallocated`): their heights are part of the component, `2^κ` for the
memory block of log-size `κ` (`memComponent κ`) and `2^prog.logSize` for the bytecode block of
the program (`bytecodeComponent prog`), and their fixed cells are verifier-known columns that
Clean checks of every row (`Table.fixed_rows_match`). The memory block's address column is
`gpowCell`, `g^i` at row `i` as the product of `g^(2^k)` over the set bits of `i`, leanVM's
`index_mle` read at a hypercube point; the bytecode block's counter is the same column, and its
eight entry columns are the program's entries (`entryCell`). The prover commits only the
finalize counts and, for memory, the words, whose rows Clean derives into the prover data's
`"mem"` table (Layer 5).

**The specifications.** A block's `Spec` is what its pull guarantees (Layer 5): `MemSpec r
data` says the row is bound to the image the data names, `MemBindings (imageOf data).2 r`;
`BytecodeDecodes r` says the row's entry decodes to an instruction (Layer 4), the program-free
guarantee of the bytecode channel. The two circuits are program- and size-free, as the opcode
tables are: what a block row may assume is its circuit's `Assumptions`, which the component
supplies from its fixed cells and the derived data (`circuit_assumptions_of_assumptions`):
`MemSeed r data`, the row being row `i` of the `"mem"` table at address `g^i` for an index `i`
of the image, and `BytecodeDecodes r`, which the program's entry columns satisfy. From them the
block's seed push discharges what it owes (`MemChannel.Guarantees`, `BytecodeChannel.Guarantees`).
`BytecodeBindings prog r`, the program fetching at `idx` the instruction the row's entry decodes
to, is what the fixed columns say of a row (`bytecodeMode_fixedAt_iff`); Layer 9 reads it off
every row. The verifier is a Clean `Verifier.Program`, and its `Spec` is `True`: the state pull
carries no guarantee, since a pulled state need not be reachable (roadmap acceptance test 21,
decision 7), and what the state boundary yields, a run from `(1, 1)` to `(g^(N_prog - 1), 1)`
inside a balanced bus, is Layer 9's, stated once, from balance. Access counts are outside every
specification: nothing checks a finalize count (§6.2), and a wrong one can only unbalance the
bus (Layer 8).

**Soundness and completeness.** The honest-prover premise of a block is its `Spec`, and nothing
above this file assumes it: `memRowOf mem i cntFin` is the seed row of word `i` of an image and
`bytecodeRowOf prog i cntFin` the seed row of slot `i` of a program, `memRowOf_bindings` proves
the word's row bound and `bytecodeRowOf_decodes` the slot's row decodable, with any finalize
count, and `mem_word_complete` and `bytecode_entry_complete` push them through `completeness`
over the prover data. `memMode_fixedAt_iff` and `bytecodeMode_fixedAt_iff` say that these rows
are the ones the fixed columns allow. `verifier_push_eval` and `verifier_pull_eval` read the
verifier's two states as Layer 3's `Regs.initial` and `Regs.final prog`.

**Generation.** Each component carries Clean's witness-generation metadata (`generation`); no
theorem uses Clean's generator, and the cells only fixed columns constrain are placeholders.

## Wrong readings excluded

* The seed count is the literal `1 = g^0` and the finalize count a column: a block whose seed
  carried the finalize count, or whose finalize pulled `1`, would let a read go unbalanced;
  `main` transcribes `Const(one)` on the push and `Col(MFCNT)`/`Col(BFCNT)` on the pull.
* The verifier pulls `fp = 1` as a literal (§6.1, the final frame pointer is `g^0`; acceptance
  test 4), never a public coordinate: a run ending with `fp ≠ 1` cannot balance the state
  channel.
* The counter it pulls is the program's constant, never a public coordinate or a column
  (status finding F9); `verifier_pull_eval` says the pulled state is `Regs.final prog` in every
  environment.
* `idx` is a fixed column, not a committed one: a prover cannot shift the memory block's
  addresses, and the block's words are the data's `"mem"` table by derivation, not by a
  hypothesis of the statement (tests).
* The bytecode circuit names no program: one read off the prover data is the prover's (status
  finding F10). The program enters as the component's fixed columns (decision 14).
* The bytecode entry carries all seven operand slots, spare slots as literal zeros, so that the
  seed of a slot and a table's read of it are the same tuple (status finding R24); Layer 4's
  `decode` rejects a nonzero spare slot, and so does `BytecodeDecodes` (tests).
* The public words are not on the bus: §8.2 checks them against the committed memory by an
  evaluation claim, which Layer 8 states as a conjunct of `SatisfiedBy` over `imageOf w.data`,
  and the verifier reads `lanes` for nothing.
-/

namespace LeanerVM.Arithmetization

open LeanerVM.Parameters LeanerVM.Semantics
open Air.Flat (Component)
open Air.Flat.WitnessGeneration (Cell)

/-! ## The public input of the constraint system -/

/-- What the verifier reads off the public data: the four lanes of the public input
(specification §2, §8.2). The sentinel counter is not here: it is a constant of the public
program (`leanIsaVerifier`). -/
structure PublicIO (F : Type) where
  /-- `input₀, …, input₃`. -/
  lanes : Vector F 4
  deriving ProvableStruct

/-- The public input of a run on `input`: its four lanes. -/
def PublicIO.ofInput (input : PublicInput) : PublicIO K :=
  ⟨#v[input.lanes 0, input.lanes 1, input.lanes 2, input.lanes 3]⟩

/-! ## Fixed columns -/

/-- The index column at the row index `i`, over its low `n` bits: the product of `g^(2^k)` over
the set bits `k < n` of `i`, which is `g^i` for `i < 2^n` (`gpowCell_eval`). leanVM's verifier
evaluates the same product as the multilinear `index_mle` (§6.5). -/
def gpowCell (i : Witgen.U64Expr K) : ℕ → Witgen.FExpr K
  | 0 => .const 1
  | n + 1 => .mul (gpowCell i n) (.ite (.bit (.ofU64 i) n) (.const (gpow (2 ^ n))) (.const 1))

/-- Column `j` of the program's entries at the row index `i`: `(entry (prog.code i))[j]`, `0`
past the program. -/
def entryCell (prog : Program) (j : Fin 8) (i : Witgen.U64Expr K) : Witgen.FExpr K :=
  .listGet (List.ofFn fun k : Fin (2 ^ prog.logSize) ↦ .const (entry (prog.code k))[j]) i

/-- The index column is `g^i` at every row `i` below `2^n`. -/
theorem gpowCell_eval (ctx : Witgen.Ctx K) (n : ℕ) {i : Witgen.U64Expr K}
    (hi : (i.eval ctx).toNat < 2 ^ n) : (gpowCell i n).eval ctx = gpow (i.eval ctx).toNat := by
  suffices h : ∀ n, (gpowCell i n).eval ctx = gpow ((i.eval ctx).toNat % 2 ^ n) by
    rw [h, Nat.mod_eq_of_lt hi]
  intro n
  induction n with
  | zero => rw [pow_zero, Nat.mod_one]; rfl
  | succ n ih =>
    have hbit : (FiniteField.val ((Witgen.FExpr.ofU64 i).eval ctx)).testBit n =
        (i.eval ctx).toNat.testBit n := by
      show (FiniteField.val (FiniteField.fromNat (i.eval ctx).toNat : K)).testBit n = _
      rw [FiniteField.val_fromNat _ (UInt64.toNat_lt _)]
    show (gpowCell i n).eval ctx *
        (if Witgen.BExpr.eval ctx (.bit (.ofU64 i) n) then gpow (2 ^ n) else 1) = _
    rw [ih, Nat.mod_pow_succ, gpow, gpow, gpow, pow_add, pow_mul]
    simp only [Witgen.BExpr.eval, hbit, Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one ((i.eval ctx).toNat / 2 ^ n) with h | h <;>
      simp [h]

/-- The index column is `g^i` at a row `i` below `2^n`, read in the context a fixed cell is
evaluated in. -/
theorem gpowCell_idx_eval {n i : ℕ} (hi : i < 2 ^ n) (hn : n ≤ 64) (env : ProverEnvironment K)
    (locals : Array (K ⊕ UInt64)) :
    (gpowCell .idx n).eval ⟨env, locals, i⟩ = gpow i := by
  have h64 : i < 2 ^ 64 := lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hn)
  have h : (Witgen.U64Expr.idx.eval (⟨env, locals, i⟩ : Witgen.Ctx K)).toNat = i := by
    show (UInt64.ofNat i).toNat = i
    rw [UInt64.toNat_ofNat_of_lt' h64]
  rw [gpowCell_eval _ n (by rw [h]; exact hi), h]

/-- The row index a fixed cell reads is the row's. -/
private theorem idx_eval_toNat (ctx : Witgen.Ctx K) (h : ctx.idx < 2 ^ 64) :
    (Witgen.U64Expr.idx.eval ctx).toNat = ctx.idx := by
  show (UInt64.ofNat ctx.idx).toNat = ctx.idx
  rw [UInt64.toNat_ofNat_of_lt' h]

/-- Entry column `j` is the program's entry at every row `i` below `2^prog.logSize`. -/
theorem entryCell_eval (prog : Program) (j : Fin 8) (ctx : Witgen.Ctx K) {i : Witgen.U64Expr K}
    (hi : (i.eval ctx).toNat < 2 ^ prog.logSize) :
    (entryCell prog j i).eval ctx = (entry (prog.code ⟨_, hi⟩))[j] := by
  suffices h : ∀ (l : List (Witgen.FExpr K)) (k : ℕ) (hk : k < l.length),
      Witgen.FExpr.evalList ctx k l = l[k].eval ctx by
    show Witgen.FExpr.evalList ctx (i.eval ctx).toNat _ = _
    rw [h _ _ (by rwa [List.length_ofFn]), List.getElem_ofFn]
    rfl
  intro l
  induction l with
  | nil => intro k hk; exact absurd hk (Nat.not_lt_zero _)
  | cons x l ih =>
    intro k hk
    cases k with
    | zero => rfl
    | succ k => exact ih k (Nat.lt_of_succ_lt_succ hk)

/-- Entry column `j` is the program's entry at a row `i` below `2^prog.logSize`, read in the
context a fixed cell is evaluated in. -/
theorem entryCell_idx_eval (prog : Program) {i : ℕ} (hi : i < 2 ^ prog.logSize) (j : Fin 8)
    (env : ProverEnvironment K) (locals : Array (K ⊕ UInt64)) :
    (entryCell prog j .idx).eval ⟨env, locals, i⟩ = (entry (prog.code ⟨i, hi⟩))[j] := by
  have h64 : i < 2 ^ 64 := lt_of_lt_of_le hi
    (Nat.pow_le_pow_right (by norm_num) (prog.logSize_le.trans (by decide)))
  have h := idx_eval_toNat (⟨env, locals, i⟩ : Witgen.Ctx K) h64
  rw [entryCell_eval prog j (⟨env, locals, i⟩ : Witgen.Ctx K) (by rw [h]; exact hi)]
  simp only [h]

/-- An eight-coordinate entry is its opcode followed by its seven operand slots. -/
private theorem cons_append_ops (e : Vector K 8) :
    #v[e[0]] ++ #v[e[1], e[2], e[3], e[4], e[5], e[6], e[7]] = e := by
  ext j hj
  interval_cases j <;> rfl

/-! ## The memory block -/

/-- The row's binding to an image: the cell at its address holds its word. -/
structure MemBindings {κ : ℕ} (mem : MemImage κ) (r : MemRow K) : Prop where
  /-- The cell `idx` holds the row's word `m`. -/
  word_eq : mem.read r.idx = some (E.ofLimbs r.m[0] r.m[1] r.m[2])

/-- The memory block's `Spec`: the row is bound to the image the prover data names (Layer 5's
`imageOf`). -/
def MemSpec (r : MemRow K) (data : ProverData K) : Prop :=
  MemBindings (imageOf data).2 r

/-- What a memory block row may assume, from its fixed address column and the derived data: it
is row `i` of the `"mem"` table, at address `g^i`, for an index `i` of the image. -/
structure MemSeed (r : MemRow K) (data : ProverData K) : Prop where
  /-- The row is row `i` of the `"mem"` table at address `g^i`. -/
  row_eq : ∃ i : Fin (2 ^ (imageOf data).1), r.idx = gpow i ∧ (memRows data)[(i : ℕ)]? = some r.m

/-- A seed row is bound to the image the data names. -/
theorem MemSeed.spec {r : MemRow K} {data : ProverData K} (h : MemSeed r data) : MemSpec r data := by
  obtain ⟨i, hidx, hrow⟩ := h.row_eq
  refine ⟨?_⟩
  rw [hidx, MemImage.read_gpow (imageOf_fst_lt data), imageOf_apply i hrow]

/-- The memory block circuit (specification §6.2, seed and finalize; `layout.rs:359-382`): push
`(idx, 1, m)`, pull `(idx, cntFin, m)`. Its name is the prover data's `"mem"` table. -/
def memTable : GeneralFormalCircuit K MemRow unit where
  name := memDataName
  main r := do
    MemChannel.push ⟨r.idx, 1, r.m⟩
    MemChannel.pull ⟨r.idx, r.cntFin, r.m⟩
  -- The seed push owes the channel's guarantee.
  channelsWithRequirements := [MemChannel.toRaw]
  Assumptions := MemSeed
  Spec r _ data := MemSpec r data
  -- The honest prover's row: a word of the image. Proved of the row of every word by
  -- `memRowOf_bindings`; see `mem_word_complete`.
  ProverAssumptions r data _ := MemSpec r data
  soundness := by
    circuit_proof_start [MemChannel]
    obtain ⟨_, _, hm⟩ := h_input
    subst hm
    refine ⟨⟨by simpa only [Vector.getElem_map] using h_holds⟩, fun _ ↦ ?_⟩
    simpa only [Vector.getElem_map] using (MemSeed.spec h_assumptions).word_eq
  completeness := by
    circuit_proof_start [MemChannel]
    obtain ⟨_, _, hm⟩ := h_input
    subst hm
    simpa only [Vector.getElem_map] using h_assumptions.word_eq

/-- The rows of the memory block of log-size `κ`: `2^κ` of them, the address column fixed to
`g^i` at row `i` (`gpowCell`), the words from the prover's hint, the finalize count the
generator's multiplicity cell. -/
def memMode (κ : ℕ) : Air.Flat.WitnessGeneration.PreallocatedMode K MemRow where
  channel := MemChannel
  trigger := .pull
  height := UInt64.ofNat (2 ^ κ)
  input i := pure ⟨.fixed (gpowCell i κ), .multiplicity,
    #v[.witness (.hintGet memDataName 3 i 0), .witness (.hintGet memDataName 3 i 1),
      .witness (.hintGet memDataName 3 i 2)]⟩
  rowOf _ := .const (UInt64.ofNat (2 ^ κ))

/-- Row `i` of the memory block agrees with its fixed cells exactly when its address is `g^i`. -/
theorem memMode_fixedAt_iff {κ : ℕ} {i : ℕ} (hi : i < 2 ^ κ) (hκ : κ < 64) (r : MemRow K) :
    (memMode κ).FixedAt (UInt64.ofNat i) r ↔ r.idx = gpow i := by
  have hi64 : i < 2 ^ 64 := lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hκ.le)
  obtain ⟨idx, cntFin, m⟩ := r
  obtain ⟨m0, m1, m2, rfl⟩ : ∃ a b c, m = #v[a, b, c] :=
    ⟨m[0], m[1], m[2], by ext j hj; interval_cases j <;> rfl⟩
  simp only [Air.Flat.WitnessGeneration.PreallocatedMode.FixedAt, memMode,
    Witgen.M.pure_def, circuit_norm, explicit_provable_type, ProvableStruct.toComponents]
  simp [Cell.FixedMatches]
  rw [gpowCell_idx_eval hi hκ.le]

/-- The memory block of log-size `κ`: `memTable` preallocated at height `2^κ` (`memMode`). The
component's own assumption is the derived data's shape, which holds in every witness of the
ensemble within the cap (Layer 8). -/
def memComponent (κ : ℕ) : Component K where
  circuit := memTable
  generation := .preallocated (memMode κ)
  Assumptions _ data := κ ≤ maxLogMem ∧ (memRows data).size = 2 ^ κ
  circuit_assumptions_of_assumptions i input data hfixed hdata hshape := by
    obtain ⟨hlt, hfix⟩ := hfixed
    have hκ : κ < 64 := lt_of_le_of_lt hshape.1 (by decide)
    have h64 : 2 ^ κ < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) hκ
    have hi : i.toNat < 2 ^ κ := by
      rw [UInt64.lt_iff_toNat_lt, memMode, UInt64.toNat_ofNat_of_lt' h64] at hlt
      exact hlt
    rw [show i = UInt64.ofNat i.toNat from UInt64.ofNat_toNat.symm,
      memMode_fixedAt_iff hi hκ] at hfix
    have hfst := imageOf_fst hshape.1 hshape.2
    refine ⟨⟨⟨i.toNat, by rw [hfst]; exact hi⟩, hfix, ?_⟩⟩
    simp only [Air.Flat.DataInputAt, ProverData.getRows, Array.getElem?_map] at hdata
    simp only [memRows, ProverData.getRows, Array.getElem?_map]
    exact congrArg (Option.map (·.m)) hdata

/-! ## The bytecode block -/

/-- A row of the bytecode block: the counter `g^i` (the index column), the finalize count
`g^(A[i])` (`BFCNT`, `layout.rs:17`), and the entry of Layer 4 at that slot, the opcode and the
seven operand slots (the eight public columns of `bytecode_columns`, `layout.rs:229-290`). -/
structure BytecodeRow (F : Type) where
  /-- The counter, `g^i` for row `i`. -/
  idx : F
  /-- The finalize count, `g^(A[i])` for a slot executed `A[i]` times. -/
  cntFin : F
  /-- The opcode, coordinate 3 of the tuple. -/
  opcode : F
  /-- The seven operand slots. -/
  op : Vector F 7
  deriving ProvableStruct

/-- The row's entry decodes to an instruction (Layer 4; `decode_eq_some_iff` reads it as the
entry): the bytecode channel's guarantee (Layer 5), the block circuit's `Assumptions` and
`Spec`. -/
structure BytecodeDecodes (r : BytecodeRow K) : Prop where
  /-- The row's entry is an instruction's. -/
  entry_eq : ∃ ins, decode (#v[r.opcode] ++ r.op) = some ins

/-- The row's binding to a program: the program fetches an instruction at the row's counter,
and the row's entry decodes to it. What the bytecode block's fixed columns say of each row
(`bytecodeMode_fixedAt_iff`). -/
structure BytecodeBindings (prog : Program) (r : BytecodeRow K) : Prop where
  /-- The program fetches at `idx` the instruction the row's entry decodes to. -/
  entry_eq : ∃ ins, prog.fetch r.idx = some ins ∧ decode (#v[r.opcode] ++ r.op) = some ins

/-- The bytecode block circuit (specification §6.2 and §6.4, seed and finalize;
`layout.rs:383-395`): push `(idx, 1, opcode, op)`, pull `(idx, cntFin, opcode, op)`.
Program-free: the program is the component's fixed columns (`bytecodeComponent`). -/
def bytecodeTable : GeneralFormalCircuit K BytecodeRow unit where
  name := "bytecode"
  main r := do
    BytecodeChannel.push ⟨r.idx, 1, r.opcode, r.op⟩
    BytecodeChannel.pull ⟨r.idx, r.cntFin, r.opcode, r.op⟩
  -- The seed push owes the channel's guarantee.
  channelsWithRequirements := [BytecodeChannel.toRaw]
  Assumptions r _ := BytecodeDecodes r
  Spec r _ _ := BytecodeDecodes r
  -- The honest prover's row: a slot of the program, whose entry decodes. Proved of the row of
  -- every slot by `bytecodeRowOf_decodes`; see `bytecode_entry_complete`.
  ProverAssumptions r _ _ := BytecodeDecodes r
  soundness := by
    circuit_proof_start [BytecodeChannel]
    obtain ⟨_, _, _, hop⟩ := h_input
    subst hop
    exact ⟨h_assumptions, fun _ ↦ h_assumptions.entry_eq⟩
  completeness := by
    circuit_proof_start [BytecodeChannel]
    obtain ⟨_, _, _, hop⟩ := h_input
    subst hop
    exact h_assumptions.entry_eq

/-- The rows of the bytecode block of `prog`: `2^prog.logSize` of them, the counter fixed to
`g^i` and the entry columns to the program's entry at row `i` (`Coord::Public`; §8.5, Bus 4),
the finalize count the generator's multiplicity cell. -/
def bytecodeMode (prog : Program) : Air.Flat.WitnessGeneration.PreallocatedMode K BytecodeRow where
  channel := BytecodeChannel
  trigger := .pull
  height := UInt64.ofNat (2 ^ prog.logSize)
  input i := pure ⟨.fixed (gpowCell i prog.logSize), .multiplicity, .fixed (entryCell prog 0 i),
    #v[.fixed (entryCell prog 1 i), .fixed (entryCell prog 2 i), .fixed (entryCell prog 3 i),
      .fixed (entryCell prog 4 i), .fixed (entryCell prog 5 i), .fixed (entryCell prog 6 i),
      .fixed (entryCell prog 7 i)]⟩
  rowOf _ := .const (UInt64.ofNat (2 ^ prog.logSize))

/-- Row `i` of the bytecode block agrees with its fixed cells exactly when its counter is `g^i`
and its entry is the program's at slot `i`. -/
theorem bytecodeMode_fixedAt_iff (prog : Program) {i : ℕ} (hi : i < 2 ^ prog.logSize)
    (r : BytecodeRow K) :
    (bytecodeMode prog).FixedAt (UInt64.ofNat i) r ↔
      r.idx = gpow i ∧ #v[r.opcode] ++ r.op = entry (prog.code ⟨i, hi⟩) := by
  obtain ⟨idx, cntFin, opcode, op⟩ := r
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, rfl⟩ : ∃ a b c d e f h, op = #v[a, b, c, d, e, f, h] :=
    ⟨op[0], op[1], op[2], op[3], op[4], op[5], op[6], by ext j hj; interval_cases j <;> rfl⟩
  simp only [Air.Flat.WitnessGeneration.PreallocatedMode.FixedAt, bytecodeMode,
    Witgen.M.pure_def, circuit_norm, explicit_provable_type, ProvableStruct.toComponents]
  have hlog : prog.logSize ≤ 64 := prog.logSize_le.trans (by decide)
  have h64 : i < 2 ^ 64 := lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hlog)
  have h64' : i < 18446744073709551616 := h64
  simp [Cell.FixedMatches, Nat.mod_eq_of_lt h64']
  simp only [gpowCell_idx_eval hi hlog, entryCell_idx_eval prog hi]
  constructor
  · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    exact ⟨rfl, cons_append_ops _⟩
  · rintro ⟨rfl, he⟩
    have h := fun (k : ℕ) (hk : k < 8) ↦ congrArg (fun v : Vector K 8 ↦ v[k]'hk) he
    exact ⟨rfl, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide),
      h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)⟩

/-- The bytecode block of the program `prog`: `bytecodeTable` preallocated at height
`2^prog.logSize` (`bytecodeMode`). -/
def bytecodeComponent (prog : Program) : Component K where
  circuit := bytecodeTable
  generation := .preallocated (bytecodeMode prog)
  circuit_assumptions_of_assumptions i input data hfixed _ _ := by
    obtain ⟨hlt, hfix⟩ := hfixed
    have h64 : 2 ^ prog.logSize < 2 ^ 64 :=
      Nat.pow_lt_pow_right (by norm_num) (lt_of_le_of_lt prog.logSize_le (by decide))
    have hi : i.toNat < 2 ^ prog.logSize := by
      rw [UInt64.lt_iff_toNat_lt, bytecodeMode, UInt64.toNat_ofNat_of_lt' h64] at hlt
      exact hlt
    rw [show i = UInt64.ofNat i.toNat from UInt64.ofNat_toNat.symm,
      bytecodeMode_fixedAt_iff prog hi] at hfix
    exact ⟨_, hfix.2 ▸ decode_entry _⟩

/-! ## Rows from images and programs -/

/-- The seed row of word `i` of the image `mem`, with finalize count `cntFin`: the address `g^i`
and the word's limbs. -/
def memRowOf {κ : ℕ} (mem : MemImage κ) (i : Fin (2 ^ κ)) (cntFin : K) : MemRow K :=
  ⟨gpow i, cntFin, #v[(mem i).limb 0, (mem i).limb 1, (mem i).limb 2]⟩

/-- On an image within the address space `gLog?_spec` covers, `memRowOf` is bound, with any
finalize count. -/
theorem memRowOf_bindings {κ : ℕ} (hκ : κ < 64) (mem : MemImage κ) (i : Fin (2 ^ κ))
    (cntFin : K) : MemBindings mem (memRowOf mem i cntFin) :=
  ⟨by
    show mem.read (gpow i) = some (E.ofLimbs ((mem i).limb 0) ((mem i).limb 1) ((mem i).limb 2))
    rw [MemImage.read_gpow hκ, ofLimbs_limb]⟩

/-- Every word of the image named by the data has a satisfying seed row, from the image alone:
the constraints of `main` hold of `memRowOf` in the row environment over the data. -/
theorem mem_word_complete {data : ProverData K} (i : Fin (2 ^ (imageOf data).1)) (cntFin : K) :
    ConstraintsHold.Completeness (rowEnv data)
      ((memTable.main (const (memRowOf (imageOf data).2 i cntFin))).operations 0) :=
  (memTable.completeness 0 (rowEnv data) (const _)
    -- No witness slot: the row environment uses the local witnesses vacuously.
    (by simp only [circuit_norm, memTable, -BitVec.reduceNeg]) _
    ProvableType.eval_const_prover
    (memRowOf_bindings (imageOf_fst_lt data) _ _ _)).1

/-- The seed row of slot `i` of the program `prog`, with finalize count `cntFin`: the counter
`g^i` and the slot's entry (Layer 4) as the opcode and the seven operand slots. -/
def bytecodeRowOf (prog : Program) (i : Fin (2 ^ prog.logSize)) (cntFin : K) : BytecodeRow K :=
  let e := entry (prog.code i)
  ⟨gpow i, cntFin, e[0], #v[e[1], e[2], e[3], e[4], e[5], e[6], e[7]]⟩

/-- `bytecodeRowOf` is bound to its program, with any finalize count. -/
theorem bytecodeRowOf_bindings (prog : Program) (i : Fin (2 ^ prog.logSize)) (cntFin : K) :
    BytecodeBindings prog (bytecodeRowOf prog i cntFin) :=
  ⟨_, prog.fetch_gpow i, by
    show decode (#v[(entry (prog.code i))[0]] ++ #v[(entry (prog.code i))[1],
      (entry (prog.code i))[2], (entry (prog.code i))[3], (entry (prog.code i))[4],
      (entry (prog.code i))[5], (entry (prog.code i))[6], (entry (prog.code i))[7]]) = some _
    rw [cons_append_ops]
    exact decode_entry _⟩

/-- `bytecodeRowOf` decodes, with any finalize count: the block's `Spec` of every row the
builder writes. -/
theorem bytecodeRowOf_decodes (prog : Program) (i : Fin (2 ^ prog.logSize)) (cntFin : K) :
    BytecodeDecodes (bytecodeRowOf prog i cntFin) :=
  ⟨(bytecodeRowOf_bindings prog i cntFin).entry_eq.imp fun _ h ↦ h.2⟩

/-- Every slot of a program has a satisfying seed row, from the program alone and over any
data: the constraints of `main` hold of `bytecodeRowOf` in the row environment. -/
theorem bytecode_entry_complete {data : ProverData K} (prog : Program)
    (i : Fin (2 ^ prog.logSize)) (cntFin : K) :
    ConstraintsHold.Completeness (rowEnv data)
      ((bytecodeTable.main (const (bytecodeRowOf prog i cntFin))).operations 0) :=
  (bytecodeTable.completeness 0 (rowEnv data) (const _)
    (by simp only [circuit_norm, bytecodeTable, -BitVec.reduceNeg]) _
    ProvableType.eval_const_prover (bytecodeRowOf_decodes _ _ _)).1

/-! ## The verifier -/

/-- The verifier's state boundary for the public program `prog` (specification §6.1;
`layout.rs:352-358`): push the initial state `(1, 1)`, pull the final state
`(g^(N_prog - 1), 1)`, the counter a constant of the program as `Const(g_pow(final_pc))` is
(`layout.rs:335`, `:357`). `Spec` is `True`: the state pull carries no guarantee (acceptance
test 21), and the run the boundary closes is Layer 9's. -/
def leanIsaVerifier (prog : Program) : Verifier.Program K PublicIO where
  main _ := do
    Verifier.push StateChannel ⟨1, 1⟩
    Verifier.pull StateChannel ⟨Expression.const prog.finalPc, 1⟩
  Spec _ _ := True
  soundness _ _ := trivial

/-! ## Load-bearing lemmas -/

/-- The state the verifier pushes is Layer 3's `Regs.initial`, in every environment. -/
theorem verifier_push_eval (env : Environment K) :
    eval env (⟨1, 1⟩ : Regs (Expression K)) = Regs.initial := by
  simp only [circuit_norm]; rfl

/-- The state the verifier pulls is Layer 3's `Regs.final prog`, in every environment: the
counter is a constant of the component, not a column or a public coordinate. -/
theorem verifier_pull_eval (prog : Program) (env : Environment K) :
    eval env (⟨Expression.const prog.finalPc, 1⟩ : Regs (Expression K)) = Regs.final prog := by
  simp only [circuit_norm]; rfl

end LeanerVM.Arithmetization
