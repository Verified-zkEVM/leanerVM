import LeanerVM.Arithmetization.Soundness
import LeanerVMTests.Arithmetization.Statement

/-!
# Tests: the sentinel hypothesis is load-bearing

A classic test for kernel evaluation. Constraint soundness needs `SentinelSafe prog`: a `JUMP`
in the sentinel slot lets a row at the sentinel counter jump on, so a satisfying witness can
reach the final registers through a state at which the machine halts.

**The program** `sentProg` is the statement tests' fixture rearranged: the run's `JUMP` (slot `3`)
jumps to `(g^31, g^5)` instead of `(g^31, 1)`, reading its frame word from cell `11`; the `XOR` and
`DEREF` fill blocks share one closing `JUMP` (slots `4`, `5`, `6`), so that the `JUMP` table keeps
four rows; and the sentinel slot `31` holds a `JUMP` in frame `g^5` to `(g^31, 1)`. The image and
the data are the fixture's, the `BLAKE2S` fill rows too, so `Caps` holds.

**The witness** `sentW` satisfies `SatisfiedBy sentProg mulInput` (`sent_satisfiedBy`): its rows
are steps, the sentinel row among them, and the state pair balances with the walk
`(1, 1) → (g, 1) → (g^2, 1) → (g^3, 1) → (g^31, g^5) → (g^31, 1)`. But the machine halts at
`(g^31, g^5)`, the sentinel counter with the wrong frame: no run reaches the final registers
(`sent_no_run`), so no trace the witness represents is a valid execution
(`sent_not_sound`): `constraintSoundness` fails without `SentinelSafe`. `traceOf` still walks the
rows' states to the final registers in five steps (the `#guard`), a trace whose run is refuted.
-/

namespace LeanerVMTests.Arithmetization.Sentinel

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization
open LeanerVMTests.Arithmetization.Statement
open Air.Flat (Component EnsembleWitness)

/-! ## The program -/

/-- The fixture's program with a `JUMP` in its sentinel slot. -/
def sentProg : Program :=
  ⟨5, by decide, fun i ↦
    match (i : ℕ) with
    | 0 => .setConstant (gpow 2) mulX
    | 1 => .setConstant (gpow 3) mulY
    | 2 => .mulNative (gpow 2) (gpow 3) (gpow 4)
    | 3 => .jump (gpow 26) (gpow 27) (gpow 11)
    | 4 => .xor 1 1 1
    | 5 => .deref (gpow 6) 1 1 .cell
    | 6 => .jump g (gpow 2) (gpow 6)
    | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 =>
      .blake2s ![gpow 2, gpow 3, gpow 4, gpow 5] 1 (gpow 6) (gpow 8)
    | 16 => .jump (gpow 9) (gpow 10) (gpow 11)
    | 31 => .jump g (gpow 22) g
    | _ => .xor 1 1 1⟩

/-- Its sentinel slot is a `JUMP`. -/
theorem sent_not_safe : ¬ SentinelSafe sentProg := by decide

/-! ## The rows -/

/-- A typed row as the raw row a table holds. -/
def asRow {Row : TypeMap} [ProvableType Row] (r : Row K) : Array K := (toElements r).toArray

/-- A `JUMP` row with its two local witnesses `w = b = 1`. -/
def asJumpRow (r : JumpRow K) : Array K := asRow r ++ #[1, 1]

/-- Slot `3`, the run's `JUMP` to `(g^31, g^5)`: the condition at `g^26`, the destination at
`g^27`, the frame word `g^5` at `g^11` (its third read). -/
def jumpRowA : JumpRow K :=
  ⟨gpow 3, 1, gpow 26, gpow 27, gpow 11, 1, gpow 31, gpow 5, 1, 1, g ^ 2, 1⟩

/-- Slot `5`, the fixture's `DEREF` fill row one slot earlier. -/
def derefRowS : DerefRow K :=
  ⟨gpow 5, gpow 5, gpow 6, 1, 1, 0, 0, gpow 5, #v[0, 0, 0], g, g ^ 4, g ^ 3, 1⟩

/-- Slot `6`, the `JUMP` back to slot `4` closing both fill blocks. -/
def jumpRowB : JumpRow K :=
  ⟨gpow 6, gpow 5, g, gpow 2, gpow 6, 1, gpow 4, gpow 5, 1, 1, 1, 1⟩

/-- Slot `31`, the sentinel's `JUMP` in frame `g^5` to `(g^31, 1)`: the condition and the frame
word `1` at `g^6`, the destination `g^31` at `g^27`. -/
def jumpRowS : JumpRow K :=
  ⟨gpow 31, gpow 5, g, gpow 22, g, 1, gpow 31, 1, g, g, g ^ 2, 1⟩

/-- The finalize counts: cell `6` read three times, cell `27` twice, cells `8` and `28` never;
the rest as in the fixture. -/
def sentCnt (i : ℕ) : K :=
  if i = 6 then g ^ 3 else if i = 27 then g ^ 2 else if i = 8 ∨ i = 28 then 1 else memCnt i

theorem sentCnt_of_ge {i : ℕ} (h : touched ≤ i) : sentCnt i = 1 := by
  have h29 : 29 ≤ i := h
  unfold sentCnt
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), memCnt_of_ge h]

/-- The bytecode finalize counts: slots `0` to `6`, `8` to `16` and `31` executed once. -/
def sentBcCnt (i : Fin (2 ^ sentProg.logSize)) : K :=
  if (i : ℕ) = 7 then 1 else if (i : ℕ) = 31 then g else bcCnt i

/-! ## The witness -/

def derefTS : Air.Flat.Table K :=
  mkT derefTable (size DerefRow) [asRow derefRowS] fun r hr ↦ by
    rw [List.mem_singleton] at hr
    subst hr
    exact Vector.size_toArray _

def jumpTS : Air.Flat.Table K :=
  mkT jumpTable (size JumpRow + 2) ([jumpRowA, jumpRowB, jumpRow16, jumpRowS].map asJumpRow)
    fun r hr ↦ by
      rw [List.mem_map] at hr
      obtain ⟨_, -, rfl⟩ := hr
      rw [asJumpRow, Array.size_append, asRow, Vector.size_toArray]
      rfl

def bcTS : Air.Flat.Table K :=
  mkT bytecodeTable (size BytecodeRow)
    (List.ofFn fun i ↦ (toElements (bytecodeRowOf sentProg i (sentBcCnt i))).toArray)
    fun r hr ↦ by
      rw [List.mem_ofFn] at hr
      obtain ⟨i, rfl⟩ := hr
      exact Vector.size_toArray _

/-- A witness of the ensemble of `sentProg` over the fixture's data and input. -/
def mkWS (ts : List (Air.Flat.Table K))
    (hlen : (leanIsaEnsemble sentProg).tables.length = ts.length := by rfl)
    (hc : ∀ i (hi : i < (leanIsaEnsemble sentProg).tables.length),
      (leanIsaEnsemble sentProg).tables[i] = (ts[i]'(hlen ▸ hi)).component := by
        intro i hi
        have hi' : i < 8 := hi
        interval_cases i <;> rfl)
    (hd : ∀ t ∈ ts, t.data = fillData := by
      intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) :
    EnsembleWitness (leanIsaEnsemble sentProg) :=
  ⟨ts, fillData, PublicIO.ofInput mulInput, hlen, hc, hd⟩

def sentW : EnsembleWitness (leanIsaEnsemble sentProg) :=
  mkWS [xorT, mulT g, setT 1, derefTS, jumpTS, blakeT, memT sentCnt, bcTS]

/-! ## Proof helpers -/

theorem bcTS_table :
    bcTS.table =
      List.ofFn fun i ↦ (toElements (bytecodeRowOf sentProg i (sentBcCnt i))).toArray := by
  dsimp only [bcTS, mkT]

/-- The bytecode block sends nothing on a channel that is not its pair. -/
theorem bcTS_filter (c : RawChannel K) (hc : c.name ≠ BytecodePush.name)
    (hc' : c.name ≠ BytecodePull.name) :
    bcTS.interactions.filter (·.channel.name = c.name) = [] :=
  filter_eq_nil_of_rowOps _ c (by
    rw [show bcTS.component = ⟨bytecodeTable⟩ from rfl, bytecodeTable_rowOps]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro i (rfl | rfl)
    · exact fun h ↦ hc (h.symm.trans rfl)
    · exact fun h ↦ hc' (h.symm.trans rfl))

theorem verifierS_constraints (env : Environment K) :
    (⟨leanIsaVerifier sentProg⟩ : Component K).operations.ConstraintsHold env := by
  rw [Component.constraintsHold_iff]
  simp only [circuit_norm, leanIsaVerifier, -BitVec.reduceNeg]

theorem jumpTS_constraints : jumpTS.Constraints := by
  intro r hr
  simp only [jumpTS, mkT, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;>
  · rw [Component.constraintsHold_iff]
    simp only [jumpTS, mkT, circuit_norm, jumpTable, instructionStep, memRead, bytecodeRead,
      -BitVec.reduceNeg]
    rintro e (rfl | rfl) <;> decide +kernel

/-! ## The witness satisfies the statement -/

theorem sent_constraints : sentW.Constraints := by
  intro t ht
  simp only [EnsembleWitness.allTables, sentW, mkWS, List.mem_cons, List.not_mem_nil,
    or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun _ _ ↦ verifierS_constraints _
  · exact fun _ _ ↦ xor_constraints _
  · exact fun _ _ ↦ mul_constraints _
  · exact fun _ _ ↦ set_constraints _
  · exact fun _ _ ↦ deref_constraints _
  · exact jumpTS_constraints
  · exact fun _ _ ↦ blake2s_constraints _
  · exact fun _ _ ↦ mem_constraints _
  · exact fun _ _ ↦ bytecode_constraints _

theorem sent_state_balanced : BalancedPair sentW StatePull.toRaw StatePush.toRaw := by
  unfold BalancedPair messagesOn
  simp only [EnsembleWitness.interactions, EnsembleWitness.allTables, sentW, mkWS,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.filter_append, List.map_append,
    memT_filter sentCnt StatePush.toRaw (by decide) (by decide),
    memT_filter sentCnt StatePull.toRaw (by decide) (by decide),
    bcTS_filter StatePush.toRaw (by decide) (by decide),
    bcTS_filter StatePull.toRaw (by decide) (by decide)]
  simp only [table_interactions_eq]
  decide +kernel

theorem sent_bytecode_balanced : BalancedPair sentW BytecodePull.toRaw BytecodePush.toRaw := by
  unfold BalancedPair messagesOn
  simp only [EnsembleWitness.interactions, EnsembleWitness.allTables, sentW, mkWS,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.filter_append, List.map_append,
    memT_filter sentCnt BytecodePush.toRaw (by decide) (by decide),
    memT_filter sentCnt BytecodePull.toRaw (by decide) (by decide)]
  simp only [table_interactions_eq]
  decide +kernel

theorem sent_mem_balanced : BalancedPair sentW MemPull.toRaw MemPush.toRaw := by
  unfold BalancedPair messagesOn
  rw [EnsembleWitness.interactions]
  simp only [EnsembleWitness.allTables, sentW, mkWS, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.filter_append, List.map_append,
    bcTS_filter MemPush.toRaw (by decide) (by decide),
    bcTS_filter MemPull.toRaw (by decide) (by decide), memT_pushes, memT_pulls,
    seeds_split, fins_split sentCnt fun _ ↦ sentCnt_of_ge, ← List.append_assoc]
  refine List.perm_append_right_iff _ |>.mpr ?_
  simp only [table_interactions_eq]
  decide +kernel

theorem sent_countsNonzero : CountsNonzero sentW := by
  unfold CountsNonzero
  simp only [sentW, mkWS, table_interactions_eq]
  decide +kernel

theorem sent_caps : Caps sentW where
  minLogMem_le := by rw [show sentW.data = fillData from rfl, fill_logSize]
  le_maxLogMem := by rw [show sentW.data = fillData from rfl, fill_logSize]; decide
  heights := by
    intro t ht
    simp only [sentW, mkWS, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by decide, rfl⟩
    · exact ⟨0, by decide, rfl⟩
    · exact ⟨1, by decide, rfl⟩
    · exact ⟨0, by decide, rfl⟩
    · exact ⟨2, by decide, rfl⟩
    · exact ⟨3, by decide, by rw [blakeT_table, List.length_map, List.length_ofFn]; rfl⟩
    · exact ⟨minLogMem, by decide, by rw [memT_table, List.length_ofFn]⟩
    · exact ⟨5, by decide, by rw [bcTS_table, List.length_ofFn]; rfl⟩
  blake2s_height := by
    rw [blake2sRows, show tableAt sentW 5 = blakeT from rfl, blakeT_table, List.length_map,
      List.length_ofFn]
    decide
  well_shaped := fill_wellShaped

theorem sent_memBlockRows : memBlockRows sentW = List.ofFn (memRowArr sentCnt) := by
  rw [memBlockRows, show tableAt sentW 6 = memT sentCnt from rfl, memT_table]

theorem sent_indexColumns : IndexColumnsAreRowIndices sentW := by
  intro i hi
  simp only [sent_memBlockRows]
  rw [List.getElem_ofFn, memRowArr, memRowAt_toElements]

/-- The seed-rows conjunct for a destructured witness over the fixture's data, the image
substituted before anything is compared. -/
theorem seedRowsS_of {tables : List (Air.Flat.Table K)} {pi : PublicIO K} {h1 h2 h3}
    (hrows : memBlockRows (⟨tables, fillData, pi, h1, h2, h3⟩ :
      EnsembleWitness (leanIsaEnsemble sentProg)) = List.ofFn (memRowArr sentCnt)) :
    SeedRowsAreTheImage (⟨tables, fillData, pi, h1, h2, h3⟩ :
      EnsembleWitness (leanIsaEnsemble sentProg)) := by
  unfold SeedRowsAreTheImage
  dsimp only
  have key : ∀ s : (κ : ℕ) × MemImage κ, s = ⟨minLogMem, fillImage⟩ →
      ∃ idx cntFin : Fin (2 ^ s.1) → K,
        memBlockRows (⟨tables, fillData, pi, h1, h2, h3⟩ :
          EnsembleWitness (leanIsaEnsemble sentProg)) = List.ofFn fun i ↦
            (toElements (⟨idx i, cntFin i, #v[(s.2 i).limb 0, (s.2 i).limb 1, (s.2 i).limb 2]⟩ :
              MemRow K)).toArray := by
    rintro s rfl
    exact ⟨fun i ↦ gpow i, fun i ↦ sentCnt i, hrows⟩
  exact key (imageOf fillData) fill_imageOf

theorem sent_satisfiedBy : SatisfiedBy sentProg mulInput sentW where
  public_input_eq := rfl
  constraints := sent_constraints
  state_balanced := sent_state_balanced
  mem_balanced := sent_mem_balanced
  bytecode_balanced := sent_bytecode_balanced
  counts_nonzero := sent_countsNonzero
  caps := sent_caps
  index_columns := sent_indexColumns
  seed_rows := seedRowsS_of sent_memBlockRows
  bytecode_rows := ⟨sentBcCnt, by rw [bytecodeBlockRows, show tableAt sentW 7 = bcTS from rfl,
    bcTS_table]⟩
  blake2s_valid := by
    intro r hr
    rw [blake2sRows, show tableAt sentW 5 = blakeT from rfl, blakeT_table, List.mem_map] at hr
    obtain ⟨rj, hrj, rfl⟩ := hr
    rw [List.mem_ofFn] at hrj
    obtain ⟨j, rfl⟩ := hrj
    show Blake2sRelation (blake2sRowAt sentW (toElements (blakeRow j)).toArray)
    rw [blake2sRowAt_toElements]
    exact blakeRow_relation j
  word0_eq := by
    rw [show sentW.data = fillData from rfl, fill_imageOf]
    exact read_at 0 mulInput.word0
  word1_eq := by
    rw [show sentW.data = fillData from rfl, fill_imageOf]
    exact read_at 1 mulInput.word1

/-! ## The machine halts at the wrong frame -/

/-- The instruction at `g^i`. -/
theorem sent_fetch_at (i : ℕ) (ins : Instr) (hi : i < 2 ^ sentProg.logSize := by decide)
    (hd : sentProg.code ⟨i, hi⟩ = ins := by rfl) : sentProg.fetch (gpow i) = some ins := by
  rw [show gpow i = gpow ((⟨i, hi⟩ : Fin (2 ^ sentProg.logSize)) : ℕ) from rfl,
    Program.fetch_gpow, hd]

theorem sent_step0 : step sentProg fillImage ⟨1, 1⟩ = some ⟨gpow 1, 1⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨1, 1⟩)
    (by simpa using sent_fetch_at 0 (.setConstant (gpow 2) mulX))]
  show execute fillImage ⟨1, 1⟩ (.setConstant (gpow 2) mulX) = _
  simp only [execute, executeWith, one_mul, read_at 2 mulX]
  decide +kernel

theorem sent_step1 : step sentProg fillImage ⟨gpow 1, 1⟩ = some ⟨gpow 2, 1⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨gpow 1, 1⟩) (sent_fetch_at 1 (.setConstant (gpow 3) mulY))]
  show execute fillImage ⟨gpow 1, 1⟩ (.setConstant (gpow 3) mulY) = _
  simp only [execute, executeWith, one_mul, read_at 3 mulY]
  decide +kernel

theorem sent_step2 : step sentProg fillImage ⟨gpow 2, 1⟩ = some ⟨gpow 3, 1⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨gpow 2, 1⟩)
    (sent_fetch_at 2 (.mulNative (gpow 2) (gpow 3) (gpow 4)))]
  show execute fillImage ⟨gpow 2, 1⟩ (.mulNative (gpow 2) (gpow 3) (gpow 4)) = _
  simp only [execute, executeWith, one_mul, read_at 2 mulX, read_at 3 mulY, read_at 4 mulXY]
  decide +kernel

theorem sent_step3 : step sentProg fillImage ⟨gpow 3, 1⟩ = some ⟨gpow 31, gpow 5⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨gpow 3, 1⟩)
    (sent_fetch_at 3 (.jump (gpow 26) (gpow 27) (gpow 11)))]
  show execute fillImage ⟨gpow 3, 1⟩ (.jump (gpow 26) (gpow 27) (gpow 11)) = _
  simp only [execute, executeWith, one_mul, read_at 26 (cellK 1), read_at 27 (cellK (gpow 31)),
    read_at 11 (cellK (gpow 5))]
  decide +kernel

/-- The run from `(1, 1)`: four steps to `(g^31, g^5)`, where it halts. -/
theorem sent_run4 : run sentProg fillImage 4 Regs.initial = some ⟨gpow 31, gpow 5⟩ := by
  simp (disch := decide +kernel) only [Regs.initial, run_succ_of_ne, sent_step0, sent_step1,
    sent_step2, sent_step3, Option.bind_eq_bind, Option.bind_some, run_zero]

/-- The sentinel counter is `g^31`. -/
theorem sent_finalPc : sentProg.finalPc = gpow 31 := congrArg gpow (by decide)

/-- Past four steps the run has halted. -/
theorem sent_run_halt (k : ℕ) (r : Regs K) :
    run sentProg fillImage (4 + (k + 1)) Regs.initial ≠ some r := by
  intro h
  obtain ⟨r', h1, h2⟩ := run_prefix h
  rw [sent_run4, Option.some.injEq] at h1
  subst h1
  rw [run_succ_of_eq (r := ⟨gpow 31, gpow 5⟩) sent_finalPc.symm] at h2
  cases h2

/-- No run reaches the final registers. -/
theorem sent_no_run (n : ℕ) :
    run sentProg fillImage n Regs.initial ≠ some (Regs.final sentProg) := by
  intro h
  rcases Nat.lt_or_ge n 5 with hn | hn
  · interval_cases n
    · exact absurd (Option.some.inj h) (by decide +kernel)
    · simp (disch := decide +kernel) only [Regs.initial, run_succ_of_ne, sent_step0,
        Option.bind_eq_bind, Option.bind_some, run_zero, Option.some.injEq] at h
      revert h
      decide +kernel
    · simp (disch := decide +kernel) only [Regs.initial, run_succ_of_ne, sent_step0, sent_step1,
        Option.bind_eq_bind, Option.bind_some, run_zero, Option.some.injEq] at h
      revert h
      decide +kernel
    · simp (disch := decide +kernel) only [Regs.initial, run_succ_of_ne, sent_step0, sent_step1,
        sent_step2, Option.bind_eq_bind, Option.bind_some, run_zero, Option.some.injEq] at h
      revert h
      decide +kernel
    · rw [sent_run4, Option.some.injEq] at h
      revert h
      decide +kernel
  · obtain ⟨m, rfl⟩ : ∃ m, n = 4 + (m + 1) := ⟨n - 5, by omega⟩
    exact sent_run_halt m _ h

/-- Constraint soundness fails without `SentinelSafe`: the witness satisfies the statement and
represents no valid execution. -/
theorem sent_not_sound :
    SatisfiedBy sentProg mulInput sentW ∧
      ¬ ∃ t, AssignmentRepresents sentW t ∧ ValidExecution sentProg mulInput t := by
  refine ⟨sent_satisfiedBy, ?_⟩
  rintro ⟨⟨κ, image, steps⟩, hrep, -, hrun⟩
  have himg := assignmentRepresents_image hrep
  rw [show sentW.data = fillData from rfl, fill_imageOf] at himg
  obtain ⟨rfl, himg⟩ := Sigma.mk.inj himg
  obtain rfl := eq_of_heq himg
  exact sent_no_run steps hrun

/-! ## The computable walk still finds the final registers -/

-- `traceOf` walks the rows' states, the sentinel row among them, to the final registers in
-- five steps; the empty memory block keeps the interpreter off the `2^16` rows.
def sentLightW : EnsembleWitness (leanIsaEnsemble sentProg) :=
  mkWS [xorT, mulT g, setT 1, derefTS, jumpTS, blakeT,
    mkT memTable (size MemRow) [] (fun _ h ↦ absurd h List.not_mem_nil), bcTS]

#guard (traceOf sentProg sentLightW).map (·.steps) = some 5

end LeanerVMTests.Arithmetization.Sentinel
