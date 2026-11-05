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
the image is the fixture's, the `BLAKE2S` fill rows too, so `Caps` holds.

**The witness** `sentW` satisfies `SatisfiedBy sentProg mulInput` (`sent_satisfiedBy`): its rows
are steps, the sentinel row among them, and the state channel balances with the walk
`(1, 1) → (g, 1) → (g^2, 1) → (g^3, 1) → (g^31, g^5) → (g^31, 1)`. But the machine halts at
`(g^31, g^5)`, the sentinel counter with the wrong frame: no run reaches the final registers
(`sent_no_run`), so no trace the witness represents is a valid execution
(`sent_not_sound`): `constraintSoundness` fails without `SentinelSafe`. `traceOf` still walks the
rows' states to the final registers in five steps (the `#guard`, on the witness's opcode tables
with a one-row memory block), a trace whose run is refuted.
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
  mkT derefComponent ([derefRowS].map rawRow) (rawRows_size [derefRowS])

def jumpTS : Air.Flat.Table K :=
  mkT jumpComponent ([jumpRowA, jumpRowB, jumpRow16, jumpRowS].map jumpRaw)
    (jumpRaw_size [jumpRowA, jumpRowB, jumpRow16, jumpRowS])

/-- The bytecode block's rows: the program's. -/
def bcRowsS : List (Array K) :=
  List.ofFn fun i ↦ rawRow (bytecodeRowOf sentProg i (sentBcCnt i))

/-- They agree with the block's fixed columns. -/
theorem bcRowsS_fixed : (bytecodeComponent sentProg).FixedRowsMatch bcRowsS := by
  unfold bcRowsS
  refine ⟨?_, fun i hi ↦ ?_⟩
  · rw [List.length_ofFn]
    exact (UInt64.toNat_ofNat_of_lt' (by decide)).symm
  · have hi' : i < 2 ^ sentProg.logSize := by rwa [List.length_ofFn] at hi
    rw [List.getElem_ofFn]
    show (bytecodeMode sentProg).FixedAt (UInt64.ofNat i) (fromElements (Air.Flat.rowPrefix
      (size BytecodeRow) (rawRow (bytecodeRowOf sentProg ⟨i, hi'⟩ (sentBcCnt ⟨i, hi'⟩)))))
    rw [fromElements_rawRow, bytecodeMode_fixedAt_iff sentProg hi']
    exact ⟨rfl, cons_append_ops _⟩

def bcTS : Air.Flat.Table K :=
  mkT (bytecodeComponent sentProg) bcRowsS (by
      intro r hr
      rw [bcRowsS, List.mem_ofFn] at hr
      obtain ⟨i, rfl⟩ := hr
      exact rawRow_size _) (by rw [bcRowsS, List.length_ofFn]; decide) bcRowsS_fixed

/-- The tables of the witness. -/
def sentTables : List (Air.Flat.Table K) :=
  [xorT, mulT g, setT 1, derefTS, jumpTS, blakeT, memT sentCnt, bcTS]

/-- A witness of the ensemble of `sentProg` at the minimum memory size, over the fixture's
input. -/
def sentW : EnsembleWitness (leanIsaEnsemble sentProg minLogMem) :=
  witnessOfTables sentProg minLogMem (PublicIO.ofInput mulInput) sentTables rfl

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
    show (mulT g).table.length = 1 from rfl, show (setT 1).table.length = 2 from rfl,
    show (mulT g).component = mulComponent from rfl,
    show (setT 1).component = setComponent from rfl,
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
    intsOver_messages sentW.data (mulT g) (rows := [mulRow g]) rfl (opComponent_mults .mulNative)
      (fun r ↦ mul_sends_gen (varFromOffset MulRow 0) _ (size MulRow) _
        (eval_rowVar r sentW.data)),
    intsOver_messages sentW.data (setT 1) (rows := [setRow0 1, setRow1]) rfl
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
    [xorT, mulT g, setT 1, derefTS, jumpTS, blakeT].flatMap (intsOver sentW.data)).filter
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
      [xorT, mulT g, setT 1, derefTS, jumpTS, blakeT].flatMap (intsOver sentW.data) ++
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
  rw [sent_imageOf] at himg
  obtain ⟨rfl, himg⟩ := Sigma.mk.inj himg
  obtain rfl := eq_of_heq himg
  exact sent_no_run steps hrun

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
    [xorT, mulT g, setT 1, derefTS, jumpTS, blakeT, memT0, bcTS] rfl

#guard (traceOf sentProg sentLightW).map (·.steps) = some 5

end LeanerVMTests.Arithmetization.Sentinel
