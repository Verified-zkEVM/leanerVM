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
`traceOf` still walks the rows' states to the final registers in five steps (the `#guard`, on the
witness's opcode tables with a one-row memory block), a trace whose run is refuted.
-/

namespace LeanerVMTests.Arithmetization.Sentinel

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization
open LeanerVMTests.Arithmetization.Statement
open Air.Flat (Component EnsembleWitness)

/-- Its sentinel slot is a `JUMP`. -/
theorem sent_not_safe : ¬ SentinelSafe sentProg := by decide

/-! ## Proof helpers: the tables and the image -/

theorem bcTS_table : bcTS.table = bcRowsS := by
  dsimp only [bcTS, mkT, tableOf]

theorem sentW_data : sentW.data = Air.Flat.deriveProverData sentTables :=
  witnessOfTables_data (hc := rfl)

/-- A table of the witness has the component and rows of one of `sentTables`. -/
theorem mem_sentW {t : Air.Flat.Table K} (ht : t ∈ sentW.tables) :
    ∃ t₀ ∈ sentTables, t.component = t₀.component ∧ t.table = t₀.table := by
  have hm : sentW.tables.map (fun t ↦ (t.component, t.table)) =
      sentTables.map fun t ↦ (t.component, t.table) := witnessOfTables_map (hc := rfl)
  have h : (t.component, t.table) ∈ sentTables.map fun t ↦ (t.component, t.table) :=
    hm ▸ List.mem_map_of_mem ht
  obtain ⟨t₀, h₀, he⟩ := List.mem_map.mp h
  exact ⟨t₀, h₀, (Prod.mk.inj he).1.symm, (Prod.mk.inj he).2.symm⟩

theorem sent_tableAt_five : (tableAt sentW 5).table = blakeT.table := by
  simp only [tableAt, sentW, witnessOfTables, Air.Flat.withDerivedData, List.getElem_map,
    List.getElem_attach]
  rfl

/-- Row `k` of the data's `"mem"` table: the fixture's word `k` (finding E8: through
`getElem?`). -/
theorem sent_memRows_get? (k : ℕ) (hk : k < 2 ^ minLogMem) :
    (memRows sentW.data)[k]? = some #v[(fillImage ⟨k, hk⟩).limb 0,
      (fillImage ⟨k, hk⟩).limb 1, (fillImage ⟨k, hk⟩).limb 2] := by
  have hmem : memT sentCnt ∈ sentTables := by
    simp only [sentTables, List.mem_cons, true_or, or_true]
  rw [memRows, ProverData.getRows, sentW_data,
    show memDataName = (memT sentCnt).component.circuit.name from rfl,
    Air.Flat.deriveProverData_eq_of_mem _ (names_nodup rfl) hmem, Air.Flat.Table.rowPrefixes,
    memT_table, Array.getElem?_map, Array.getElem?_map, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_ofFn, dite_eq_left hk, Option.map_some, Option.map_some]
  exact congrArg (fun r : MemRow K ↦ some r.m) (fromElements_rawRow _)

theorem sent_logSize : (imageOf sentW.data).1 = minLogMem := imageOf_data_fst (by decide)

theorem sent_pow_eq : 2 ^ (imageOf sentW.data).1 = 2 ^ minLogMem := by rw [sent_logSize]

theorem sent_image_apply' (k : ℕ) (hk : k < 2 ^ (imageOf sentW.data).1) :
    (imageOf sentW.data).2 ⟨k, hk⟩ = fillImage ⟨k, by rw [← sent_pow_eq]; exact hk⟩ := by
  conv_rhs => rw [← ofLimbs_limb (fillImage ⟨k, _⟩)]
  exact imageOf_apply ⟨k, hk⟩ (v := #v[(fillImage ⟨k, _⟩).limb 0, (fillImage ⟨k, _⟩).limb 1,
    (fillImage ⟨k, _⟩).limb 2]) (sent_memRows_get? k _)

/-- The image the data names is the fixture's, as one equality of dependent pairs (finding
E8). -/
theorem sent_imageOf : imageOf sentW.data = ⟨minLogMem, fillImage⟩ := by
  have hκ : (imageOf sentW.data).1 = minLogMem := sent_logSize
  have hpow : 2 ^ (imageOf sentW.data).1 = 2 ^ minLogMem := sent_pow_eq
  have hf : ∀ i, (imageOf sentW.data).2 i = fillImage (Fin.cast hpow i) :=
    fun i ↦ sent_image_apply' i i.isLt
  revert hκ hpow hf
  generalize imageOf sentW.data = s
  obtain ⟨κ, img⟩ := s
  intro hκ hpow hf
  dsimp only at hκ hpow hf
  subst hκ
  exact congrArg _ (funext fun i ↦ (hf i).trans (congrArg fillImage (Fin.ext rfl)))

/-! ## Proof helpers: interactions -/

/-- A built witness's interactions: the verifier's, then each table's over the derived
data. -/
theorem witnessOfTables_interactions (ts : List (Air.Flat.Table K)) (hc) :
    (witnessOfTables sentProg minLogMem (PublicIO.ofInput mulInput) ts hc).interactions =
      (leanIsaEnsemble sentProg minLogMem).verifierOperations.interactionValues
          (.fromInput (PublicIO.ofInput mulInput)
            (witnessOfTables sentProg minLogMem (PublicIO.ofInput mulInput) ts hc).data) ++
        ts.flatMap (intsOver
          (witnessOfTables sentProg minLogMem (PublicIO.ofInput mulInput) ts hc).data) := by
  rw [EnsembleWitness.interactions]
  congr 1
  show (List.map _ ts.attach).flatMap _ = _
  rw [List.flatMap_map, List.flatMap_subtype (g := intsOver _) (fun t _ ↦ ?_),
    List.unattach_attach]
  rw [table_interactions_eq, witnessOfTables_data]
  rfl

/-- The witness's interactions: the verifier's, then the eight tables' over its data. -/
theorem sentW_interactions :
    sentW.interactions =
      (leanIsaEnsemble sentProg minLogMem).verifierOperations.interactionValues
          (.fromInput (PublicIO.ofInput mulInput) sentW.data) ++
        sentTables.flatMap (intsOver sentW.data) :=
  witnessOfTables_interactions _ _

/-- The bytecode block sends nothing on another channel. -/
theorem bcTS_filter (c : RawChannel K) (hc : c.name ≠ BytecodeChannel.name) (D : ProverData K) :
    (intsOver D bcTS).filter (·.channel.name = c.name) = [] :=
  intsOver_filter_nil D _ c (by
    rw [show bcTS.component = bytecodeComponent sentProg from rfl, bytecodeComponent_rowOps]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro i (rfl | rfl) <;> exact fun h ↦ hc (h.symm.trans rfl))

/-- Fewer interactions than `2^64`. -/
theorem sent_length : sentW.interactions.length < FiniteField.size K := by
  rw [sentW_interactions]
  simp only [sentTables, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.length_append, intsOver_length, Operations.interactionValues, List.length_map,
    show mulTS.table.length = 1 from rfl, show setTS.table.length = 2 from rfl,
    show mulTS.component = mulComponent from rfl,
    show setTS.component = setComponent from rfl,
    show (memT sentCnt).component = memComponent minLogMem from rfl, memT_table,
    List.length_ofFn]
  decide +kernel

/-- Rewrites the messages of the verifier, the six opcode tables and the bytecode block over the
witness's data to their closed forms (`intsOver_messages`). -/
local macro "rw_sent_msgs" loc:(ppSpace Lean.Parser.Tactic.location)? : tactic => `(tactic|
  simp only [verifier_msgs,
    intsOver_messages sentW.data xorT (rows := [xorRow]) rfl (opComponent_mults .xor)
      (fun r ↦ xor_sends_gen (varFromOffset XorRow 0) _ (size XorRow) _
        (eval_rowVar r sentW.data)),
    intsOver_messages sentW.data mulTS (rows := [mulRowS]) rfl (opComponent_mults .mulNative)
      (fun r ↦ mul_sends_gen (varFromOffset MulRow 0) _ (size MulRow) _
        (eval_rowVar r sentW.data)),
    intsOver_messages sentW.data setTS (rows := [setRowS0, setRowS1]) rfl
      (opComponent_mults .setConstant)
      (fun r ↦ set_sends_gen (varFromOffset SetRow 0) _ (size SetRow) _
        (eval_rowVar r sentW.data)),
    intsOver_messages sentW.data derefTS (rows := [derefRowS]) rfl (opComponent_mults .deref)
      (fun r ↦ deref_sends_gen (varFromOffset DerefRow 0) _ (size DerefRow) _
        (eval_rowVar r sentW.data)),
    intsOver_messages sentW.data jumpTS (rows := [jumpRowA, jumpRowB, jumpRow16, jumpRowS])
      (raw := fun r ↦ LeanerVM.Arithmetization.jumpRaw r 1 1) rfl (opComponent_mults .jump)
      (fun r ↦ jumpRaw_sends r 1 1 sentW.data),
    intsOver_messages sentW.data blakeT (rows := List.ofFn blakeRow) blakeT_table
      (opComponent_mults .blake2s)
      (fun r ↦ blake2s_sends_gen (varFromOffset Blake2sRow 0) _ (size Blake2sRow) _
        (eval_rowVar r sentW.data)),
    intsOver_messages sentW.data bcTS
      (rows := List.ofFn fun i ↦ bytecodeRowOf sentProg i (sentBcCnt i))
      (by dsimp only [bcTS, mkT, tableOf]; rw [bcRowsS, List.map_ofFn]; rfl)
      (bytecode_mults sentProg)
      (fun r ↦ bytecode_sends_gen (varFromOffset BytecodeRow 0) _ (size BytecodeRow) _
        (eval_rowVar r sentW.data))] $(loc)?)

/-- The memory messages of the verifier and the six opcode tables. -/
def sentMemSmall : List (Interaction K) :=
  ((leanIsaEnsemble sentProg minLogMem).verifierOperations.interactionValues
      (.fromInput (PublicIO.ofInput mulInput) sentW.data) ++
    [xorT, mulTS, setTS, derefTS, jumpTS, blakeT].flatMap (intsOver sentW.data)).filter
      (·.channel.name = MemChannel.toRaw.name)

/-- The memory channel, reduced to the touched cells. -/
theorem sent_mem_perm_iff :
    (messagesOn sentW MemChannel.toRaw .push).Perm (messagesOn sentW MemChannel.toRaw .pull) ↔
      (activeMessages sentMemSmall .push ++
        List.ofFn fun i : Fin touched ↦ seedMsg (Fin.castAdd untouched i)).Perm
      (activeMessages sentMemSmall .pull ++
        List.ofFn fun i : Fin touched ↦ finMsg sentCnt (Fin.castAdd untouched i)) := by
  unfold messagesOn
  rw [sentW_interactions,
    show sentTables.flatMap (intsOver sentW.data) =
      [xorT, mulTS, setTS, derefTS, jumpTS, blakeT].flatMap (intsOver sentW.data) ++
        (intsOver sentW.data (memT sentCnt) ++ intsOver sentW.data bcTS) by
      simp only [sentTables, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.append_assoc],
    ← List.append_assoc, ← List.append_assoc, List.filter_append, List.filter_append,
    bcTS_filter MemChannel.toRaw (by decide), List.append_nil, activeMessages_append,
    activeMessages_append, memT_pushes, memT_pulls, seeds_split,
    fins_split sentCnt fun _ ↦ sentCnt_of_ge, ← List.append_assoc, ← List.append_assoc]
  exact List.perm_append_right_iff _

/-! ## Proof helpers: constraints -/

theorem jumpTS_constraints (D : ProverData K) :
    ∀ row ∈ jumpTS.table,
      jumpComponent.operations.ConstraintsHold (Environment.fromArray row D) := by
  intro r hr
  simp only [jumpTS, mkT, tableOf, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;>
  · rw [Component.constraintsHold_iff]
    simp only [circuit_norm, jumpComponent, jumpTable, instructionStep, memRead, bytecodeRead,
      -BitVec.reduceNeg]
    rintro e (rfl | rfl) <;> rw [eval_fromArray _ D fun _ _ ↦ #[]] <;> decide +kernel

/-! ## The witness satisfies the statement -/

theorem sent_constraints : sentW.Constraints := by
  intro t ht row hrow
  have hd : t.data = sentW.data := sentW.same_data t ht
  obtain ⟨t₀, h₀, hcomp, hr⟩ := mem_sentW ht
  rw [Air.Flat.Table.environment, hd, hcomp]
  have hrow₀ : row ∈ t₀.table := hr ▸ hrow
  simp only [sentTables, List.mem_cons, List.not_mem_nil, or_false] at h₀
  rcases h₀ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact xor_constraints _
  · exact mul_constraints _
  · exact set_constraints _
  · exact deref_constraints _
  · exact jumpTS_constraints _ _ hrow₀
  · exact blake2s_constraints _
  · exact mem_constraints _ _
  · exact bytecode_constraints _ _

theorem sent_state_perm : (messagesOn sentW StateChannel.toRaw .push).Perm
    (messagesOn sentW StateChannel.toRaw .pull) := by
  unfold messagesOn
  rw [sentW_interactions]
  simp only [sentTables, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.filter_append,
    activeMessages_append, memT_filter sentCnt StateChannel.toRaw (by decide),
    bcTS_filter StateChannel.toRaw (by decide)]
  rw_sent_msgs
  decide +kernel

theorem sent_bytecode_perm : (messagesOn sentW BytecodeChannel.toRaw .push).Perm
    (messagesOn sentW BytecodeChannel.toRaw .pull) := by
  unfold messagesOn
  rw [sentW_interactions]
  simp only [sentTables, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.filter_append,
    activeMessages_append, memT_filter sentCnt BytecodeChannel.toRaw (by decide)]
  rw_sent_msgs
  decide +kernel

theorem sent_mem_perm : (messagesOn sentW MemChannel.toRaw .push).Perm
    (messagesOn sentW MemChannel.toRaw .pull) := by
  rw [sent_mem_perm_iff]
  simp only [sentMemSmall, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.filter_append, activeMessages_append]
  rw_sent_msgs
  decide +kernel

/-- The three channels balance as multisets. -/
theorem sent_balanced : sentW.Balanced .multiset := by
  intro c hc
  rw [EnsembleWitness.interactionsWith_eq_filter_name hc]
  refine ⟨lt_of_le_of_lt (List.length_filter_le _ _) sent_length,
    fun i hi ↦ Or.inr (interactions_mult_eq_one _ i (List.mem_of_mem_filter hi)), ?_⟩
  have hp : (messagesOn sentW c .push).Perm (messagesOn sentW c .pull) := by
    simp only [leanIsaEnsemble, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact sent_state_perm
    · exact sent_mem_perm
    · exact sent_bytecode_perm
  unfold messagesOn at hp
  convert hp using 3

theorem sent_countsNonzero : CountsNonzero sentW := by
  unfold CountsNonzero
  simp only [table_interactions_eq]
  decide +kernel

theorem sent_caps : Caps sentW where
  minLogMem_le := le_rfl
  le_maxLogMem := by decide
  heights := by
    intro t ht
    obtain ⟨t₀, h₀, -, hr⟩ := mem_sentW ht
    rw [hr]
    simp only [sentTables, List.mem_cons, List.not_mem_nil, or_false] at h₀
    rcases h₀ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by decide, rfl⟩
    · exact ⟨0, by decide, rfl⟩
    · exact ⟨1, by decide, rfl⟩
    · exact ⟨0, by decide, rfl⟩
    · exact ⟨2, by decide, rfl⟩
    · exact ⟨3, by decide, by rw [blakeT_table, List.length_map, List.length_ofFn]; rfl⟩
    · exact ⟨minLogMem, by decide, by rw [memT_table, List.length_ofFn]⟩
    · exact ⟨5, by decide, by rw [bcTS_table, bcRowsS, List.length_ofFn]; rfl⟩
  blake2s_height := by
    rw [blake2sRows, sent_tableAt_five, blakeT_table, List.length_map, List.length_ofFn]
    decide

theorem sent_satisfiedBy : SatisfiedBy sentProg mulInput sentW where
  public_input_eq := rfl
  constraints := sent_constraints
  balanced := sent_balanced
  counts_nonzero := sent_countsNonzero
  caps := sent_caps
  blake2s_valid := by
    intro r hr
    rw [blake2sRows, sent_tableAt_five, blakeT_table, List.mem_map] at hr
    obtain ⟨rj, hrj, rfl⟩ := hr
    rw [List.mem_ofFn] at hrj
    obtain ⟨j, rfl⟩ := hrj
    rw [rawRow, blake2sRowAt_toElements]
    exact blakeRow_relation j
  word0_eq := by
    rw [sent_imageOf]
    exact read_at 0 mulInput.word0
  word1_eq := by
    rw [sent_imageOf]
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
    ∃ (prog : Program) (input : PublicInput) (κ : ℕ) (w : EnsembleWitness (leanIsaEnsemble prog κ)),
      ¬ SentinelSafe prog ∧ SatisfiedBy prog input w ∧
        ∀ t : Trace prog, ¬ ValidExecution prog input t :=
  ⟨sentProg, mulInput, minLogMem, sentW, sent_not_safe, sent_satisfiedBy, sent_no_execution⟩

/-! ## The computable walk still finds the final registers -/

-- `traceOf` walks the rows' states, the sentinel row among them, to the final registers in
-- five steps; a one-row memory block at `κ = 0` keeps the interpreter off the `2^16` rows.

/-- A one-row memory block at `κ = 0`: cell `g^0`, the zero word. -/
def memT0 : Air.Flat.Table K :=
  mkT (memComponent 0) ([(⟨1, 1, #v[0, 0, 0]⟩ : MemRow K)].map rawRow)
    (rawRows_size [(⟨1, 1, #v[0, 0, 0]⟩ : MemRow K)]) (by decide)
    ⟨rfl, fun i hi ↦ by
      obtain rfl : i = 0 := by simpa using hi
      refine (memMode_fixedAt_iff (κ := 0) hi (by decide) _).mpr ?_
      show (fromElements (Air.Flat.rowPrefix (size MemRow)
        (rawRow (⟨1, 1, #v[0, 0, 0]⟩ : MemRow K))) : MemRow K).idx = gpow 0
      rw [fromElements_rawRow]
      exact (pow_zero g).symm⟩

/-- The witness's opcode tables with the one-row memory block. -/
def sentLightW : EnsembleWitness (leanIsaEnsemble sentProg 0) :=
  witnessOfTables sentProg 0 (PublicIO.ofInput mulInput)
    [xorT, mulTS, setTS, derefTS, jumpTS, blakeT, memT0, bcTS] rfl

#guard (traceOf sentProg sentLightW).map (·.steps) = some 5

end LeanerVMTests.Arithmetization.Sentinel
