import LeanerVM.Arithmetization.Soundness
import LeanerVMTests.Arithmetization.SentinelFixture

/-!
# Tests: the sentinel hypothesis is load-bearing

A classic test for kernel evaluation. Constraint soundness needs `SentinelSafe prog`: a `JUMP`
in the sentinel slot lets a row at the sentinel counter jump on, so a satisfying witness can
reach the final registers through a state at which the machine halts.

**The program and the witness** are `sentProg` and `sentW` of
`LeanerVMTests.Arithmetization.SentinelFixture`. The witness satisfies `SatisfiedBy sentProg
mulInput` (`sent_satisfiedBy`): its rows are steps, the sentinel row among them, and the state
pair balances with the walk `(1, 1) → (g, 1) → (g^2, 1) → (g^3, 1) → (g^31, g^5) → (g^31, 1)`.

**No execution at all.** The run's first two instructions pin, by `SET_CONSTANT`, the cells the
run's `JUMP` reads its destination and frame from, and the `JUMP`'s condition is the public word
`input₀ = 1`. So over every image whose first word is the public input's, a run either faults or
reaches `(g^31, g^5)`, the sentinel counter with the wrong frame, where the machine halts
(`sent_no_run`, generic in the image: each step lemma learns the cell its step pins). No trace of
`sentProg` is a valid execution on `mulInput` (`sent_no_execution`), whatever memory it names, so
no extractor of any kind can find one: `exists_satisfiedBy_without_execution`. The weaker
`sent_not_sound`, that no trace the witness represents is a valid execution, is its corollary.
`traceOf` still walks the rows' states to the final registers in five steps (the `#guard`), a
trace whose run is refuted.
-/

namespace LeanerVMTests.Arithmetization.Sentinel

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization
open LeanerVMTests.Arithmetization.Statement
open Air.Flat (Component EnsembleWitness)

/-- Its sentinel slot is a `JUMP`. -/
theorem sent_not_safe : ¬ SentinelSafe sentProg := by decide

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

/-- A message as a numeral, injectively, so that the kernel decides a permutation of messages
by comparing numerals. -/
def msgCode (a : Array K) : ℕ := Encodable.encode (a.toList.map fun x ↦ x.toBitVec.toNat)

/-- Distinct messages have distinct codes. -/
theorem msgCode_injective : Function.Injective msgCode := fun _ _ h ↦
  Array.toList_inj.mp <| List.map_injective_iff.mpr
    (fun _ _ h' ↦ BF64.toBitVec_injective (BitVec.eq_of_toNat_eq h')) (Encodable.encode_injective h)

/-- The three pairs balance: one kernel evaluation, which evaluates each row's messages once,
decides the three permutations on the messages' codes. The memory pair is reduced to the touched
cells, the untouched seeds and finalizes cancelling. -/
theorem sent_balanced : BalancedPair sentW StatePull.toRaw StatePush.toRaw ∧
    BalancedPair sentW BytecodePull.toRaw BytecodePush.toRaw ∧
    BalancedPair sentW MemPull.toRaw MemPush.toRaw := by
  unfold BalancedPair messagesOn
  simp only [EnsembleWitness.interactions, EnsembleWitness.allTables, sentW, mkWS,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.filter_append, List.map_append,
    memT_filter sentCnt StatePush.toRaw (by decide) (by decide),
    memT_filter sentCnt StatePull.toRaw (by decide) (by decide),
    memT_filter sentCnt BytecodePush.toRaw (by decide) (by decide),
    memT_filter sentCnt BytecodePull.toRaw (by decide) (by decide),
    bcTS_filter StatePush.toRaw (by decide) (by decide),
    bcTS_filter StatePull.toRaw (by decide) (by decide),
    bcTS_filter MemPush.toRaw (by decide) (by decide),
    bcTS_filter MemPull.toRaw (by decide) (by decide), memT_pushes, memT_pulls, seeds_split,
    fins_split sentCnt fun _ ↦ sentCnt_of_ge, ← List.append_assoc, List.perm_append_right_iff,
    ← List.map_perm_map_iff msgCode_injective]
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
  state_balanced := sent_balanced.1
  mem_balanced := sent_balanced.2.2
  bytecode_balanced := sent_balanced.2.1
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
    rw [rawRow, blake2sRowAt_toElements]
    exact blakeRow_relation j
  word0_eq := by
    rw [show sentW.data = fillData from rfl, fill_imageOf]
    exact read_at 0 mulInput.word0
  word1_eq := by
    rw [show sentW.data = fillData from rfl, fill_imageOf]
    exact read_at 1 mulInput.word1

/-! ## No run reaches the final registers, over any image -/

/-- The instruction at `g^i`. -/
theorem sent_fetch_at (i : ℕ) (ins : Instr) (hi : i < 2 ^ sentProg.logSize := by decide)
    (hd : sentProg.code ⟨i, hi⟩ = ins := by rfl) : sentProg.fetch (gpow i) = some ins := by
  rw [show gpow i = gpow ((⟨i, hi⟩ : Fin (2 ^ sentProg.logSize)) : ℕ) from rfl,
    Program.fetch_gpow, hd]

/-- The sentinel counter is `g^31`. -/
theorem sent_finalPc : sentProg.finalPc = gpow 31 := congrArg gpow (by decide)

/-- A run of `n + 1` steps takes a first step. -/
theorem run_succ_eq_some {κ : ℕ} {prog : Program} {L : MemImage κ} {n : ℕ} {r r'' : Regs K}
    (h : run prog L (n + 1) r = some r'') :
    ∃ r', step prog L r = some r' ∧ run prog L n r' = some r'' := by
  rw [run_succ_of_ne (pc_ne_finalPc_of_run_succ h)] at h
  exact Option.bind_eq_some_iff.mp h

/-- A `SET_CONSTANT` step pins its cell to the constant and moves to the next slot. -/
theorem execute_setConstant_eq_some {κ : ℕ} {L : MemImage κ} {r r' : Regs K} {o : K} {k : E}
    (h : execute L r (.setConstant o k) = some r') :
    L.read (r.fp * o) = some k ∧ r' = r.next := by
  simp only [execute, executeWith, Option.bind_eq_bind] at h
  obtain ⟨v, hv, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hk, h'⟩ := (guard_bind_eq_some_iff _ _ _).mp h
  exact ⟨hk ▸ hv, by simpa [eq_comm] using h'⟩

/-- A `MUL_NATIVE` step moves to the next slot. -/
theorem execute_mulNative_eq_some {κ : ℕ} {L : MemImage κ} {r r' : Regs K} {oA oB oC : K}
    (h : execute L r (.mulNative oA oB oC) = some r') : r' = r.next := by
  simp only [execute, executeWith, Option.bind_eq_bind] at h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨-, h'⟩ := (guard_bind_eq_some_iff _ _ _).mp h
  simpa [eq_comm] using h'

variable {κ : ℕ} {L : MemImage κ}

theorem sent_step0 {r : Regs K} (h : step sentProg L ⟨1, 1⟩ = some r) :
    L.read (gpow 11) = some (cellK (gpow 5)) ∧ r = ⟨gpow 1, 1⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨1, 1⟩)
    (by simpa using sent_fetch_at 0 (.setConstant (gpow 11) (cellK (gpow 5))))] at h
  obtain ⟨h1, rfl⟩ := execute_setConstant_eq_some h
  exact ⟨by simpa using h1, by simp [Regs.next]⟩

theorem sent_step1 {r : Regs K} (h : step sentProg L ⟨gpow 1, 1⟩ = some r) :
    L.read (gpow 27) = some (cellK (gpow 31)) ∧ r = ⟨gpow 2, 1⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨gpow 1, 1⟩)
    (sent_fetch_at 1 (.setConstant (gpow 27) (cellK (gpow 31))))] at h
  obtain ⟨h1, rfl⟩ := execute_setConstant_eq_some h
  exact ⟨by simpa using h1, by simp [Regs.next, pow_succ, mul_comm]⟩

theorem sent_step2 {r : Regs K} (h : step sentProg L ⟨gpow 2, 1⟩ = some r) :
    r = ⟨gpow 3, 1⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨gpow 2, 1⟩)
    (sent_fetch_at 2 (.mulNative (gpow 2) (gpow 3) (gpow 4)))] at h
  rw [execute_mulNative_eq_some h]
  simp [Regs.next, pow_succ, mul_comm]

theorem sent_step3 (h0 : L.read (gpow 0) = some mulInput.word0)
    (h27 : L.read (gpow 27) = some (cellK (gpow 31)))
    (h11 : L.read (gpow 11) = some (cellK (gpow 5))) :
    step sentProg L ⟨gpow 3, 1⟩ = some ⟨gpow 31, gpow 5⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨gpow 3, 1⟩) (sent_fetch_at 3 (.jump 1 (gpow 27) (gpow 11)))]
  have h0' : L.read 1 = some mulInput.word0 := by simpa using h0
  simp only [execute, executeWith, one_mul, h0', h27, h11]
  decide +kernel

/-- From the sentinel at frame `g^5` nothing reaches the final registers: the machine halts. -/
theorem sent_from4 (n : ℕ) : run sentProg L n ⟨gpow 31, gpow 5⟩ ≠ some (Regs.final sentProg) := by
  intro h
  cases n with
  | zero => exact absurd (Option.some.inj h) (by decide +kernel)
  | succ n => rw [run_succ_of_eq (by rw [sent_finalPc])] at h; cases h

theorem sent_from3 (h0 : L.read (gpow 0) = some mulInput.word0)
    (h27 : L.read (gpow 27) = some (cellK (gpow 31)))
    (h11 : L.read (gpow 11) = some (cellK (gpow 5))) (n : ℕ) :
    run sentProg L n ⟨gpow 3, 1⟩ ≠ some (Regs.final sentProg) := by
  intro h
  cases n with
  | zero => exact absurd (Option.some.inj h) (by decide +kernel)
  | succ n =>
    obtain ⟨r', hs, hr⟩ := run_succ_eq_some h
    rw [sent_step3 h0 h27 h11, Option.some.injEq] at hs
    exact sent_from4 n (hs ▸ hr)

theorem sent_from2 (h0 : L.read (gpow 0) = some mulInput.word0)
    (h27 : L.read (gpow 27) = some (cellK (gpow 31)))
    (h11 : L.read (gpow 11) = some (cellK (gpow 5))) (n : ℕ) :
    run sentProg L n ⟨gpow 2, 1⟩ ≠ some (Regs.final sentProg) := by
  intro h
  cases n with
  | zero => exact absurd (Option.some.inj h) (by decide +kernel)
  | succ n =>
    obtain ⟨r', hs, hr⟩ := run_succ_eq_some h
    exact sent_from3 h0 h27 h11 n (sent_step2 hs ▸ hr)

theorem sent_from1 (h0 : L.read (gpow 0) = some mulInput.word0)
    (h11 : L.read (gpow 11) = some (cellK (gpow 5))) (n : ℕ) :
    run sentProg L n ⟨gpow 1, 1⟩ ≠ some (Regs.final sentProg) := by
  intro h
  cases n with
  | zero => exact absurd (Option.some.inj h) (by decide +kernel)
  | succ n =>
    obtain ⟨r', hs, hr⟩ := run_succ_eq_some h
    obtain ⟨h27, rfl⟩ := sent_step1 hs
    exact sent_from2 h0 h27 h11 n hr

/-- **No run reaches the final registers**, over any image whose first word is the public
input's: every run faults or halts at the sentinel at frame `g^5`. -/
theorem sent_no_run (h0 : L.read (gpow 0) = some mulInput.word0) (n : ℕ) :
    run sentProg L n Regs.initial ≠ some (Regs.final sentProg) := by
  intro h
  cases n with
  | zero => exact absurd (Option.some.inj h) (by decide +kernel)
  | succ n =>
    obtain ⟨r', hs, hr⟩ := run_succ_eq_some h
    obtain ⟨h11, rfl⟩ := sent_step0 hs
    exact sent_from1 h0 h11 n hr

/-- **No valid execution**: no trace of `sentProg`, over any memory, is a valid execution on the
public input. -/
theorem sent_no_execution (t : Trace sentProg) : ¬ ValidExecution sentProg mulInput t :=
  fun ⟨⟨_, _, h0, _⟩, hrun⟩ ↦ sent_no_run h0 t.steps hrun

/-! ## Constraint soundness fails, for every extractor -/

/-- Constraint soundness fails without `SentinelSafe`: the witness satisfies the statement and
represents no valid execution. -/
theorem sent_not_sound :
    SatisfiedBy sentProg mulInput sentW ∧
      ¬ ∃ t, AssignmentRepresents sentW t ∧ ValidExecution sentProg mulInput t :=
  ⟨sent_satisfiedBy, fun ⟨t, _, ht⟩ ↦ sent_no_execution t ht⟩

/-- **A witness of the constraint statement with no execution**: some program whose sentinel slot
is a `JUMP` has a witness of the constraint statement on a public input on which it has no valid
execution, over any memory. -/
theorem exists_satisfiedBy_without_execution :
    ∃ (prog : Program) (input : PublicInput) (w : EnsembleWitness (leanIsaEnsemble prog)),
      ¬ SentinelSafe prog ∧ SatisfiedBy prog input w ∧
        ∀ t : Trace prog, ¬ ValidExecution prog input t :=
  ⟨sentProg, mulInput, sentW, sent_not_safe, sent_satisfiedBy, sent_no_execution⟩

/-! ## The computable walk still finds the final registers -/

-- `traceOf` walks the rows' states, the sentinel row among them, to the final registers in
-- five steps; the empty memory block keeps the interpreter off the `2^16` rows.
def sentLightW : EnsembleWitness (leanIsaEnsemble sentProg) :=
  mkWS [xorT, mulTS, setTS, derefTS, jumpTS, blakeT,
    mkT memTable (size MemRow) [] (fun _ h ↦ absurd h List.not_mem_nil), bcTS]

#guard (traceOf sentProg sentLightW).map (·.steps) = some 5

end LeanerVMTests.Arithmetization.Sentinel
