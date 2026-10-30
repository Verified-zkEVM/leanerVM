/-
  LeanerVM.Arithmetization.Completeness.Satisfied

  The witness of a padded execution satisfies the constraint statement: the three balances, the
  caps, the compression, and the public words.
-/

module

public import LeanerVM.Arithmetization.Completeness.Witness
public import LeanerVM.Arithmetization.Rows

@[expose] public section

/-!
# The witness satisfies the statement

leanISA roadmap Layer 10 (`docs/roadmap/leanisa-blueprint.md`), at Clean pin `ce2eee63`.
Category A. `padWitness prog input img S hκ hS` satisfies every conjunct of `SatisfiedBy prog
input` (`padWitness_satisfiedBy`) when the skeletons `S` are sound for the program and the image
(`SkelOk`: fetched, and they execute), the state channel balances (the hypothesis `hstate`,
proved from the run and the fill in `Completeness`), every table's height is a power of two
within the cap and the `BLAKE2S` table has at least eight rows, and the image has the public
words.

The proof is the bus computation. Every interaction of a witness of the ensemble has multiplicity
`1` (`interactions_mult_eq_one`), so Clean's active messages are the sends (`messagesOn_eq_sends`)
and every multiplicity is boolean. `padWitness_sends` says what the witness sends: the verifier's
two messages, then the rows of each table, then the blocks'. For the memory and the bytecode channel
the rows are the reads of one list of skeletons, numbered by the chain (`Completeness.Bus`), so
`chain_balance` (`Completeness.Balance`) balances them against the blocks' seeds and finalizes; the
six tables hold the rows in another order than the list, which is a permutation (`regroup_perm`).
The state channel is the hypothesis `hstate` regrouped the same way. Fewer than `2^64` interactions:
at most `22` per row of at most `6·2^32` skeletons, and two per row of the blocks
(`padSends_length_lt`). The `JUMP` table is the one component with constraints, and its two
residuals hold of the honest witnesses (`flags_complete`).

## Wrong readings excluded

* The balance is of the messages the rows send, never of the rows: a row that does not execute
  sends a message the image does not hold, and the chain lemma needs every read to be a message of
  the image (`readAddrs_valid`).
* The finalize count of a cell is `g^(reads of the cell)`, which is `1` for a cell nobody reads:
  the finalize pull of an unread cell is its seed push, and the two cancel.
* The pull and the push of a read are told apart by their direction, never by a multiplicity:
  every multiplicity is `1`.
-/

open scoped List

namespace LeanerVM.Arithmetization

open LeanerVM.Parameters LeanerVM.Semantics
open Air.Flat (Component EnsembleWitness)

/-! ## What the bus carries -/

/-- The sends of rows of a component over the data `data`. -/
def rowsSends (c : Component K) (rows : List (Array K)) (data : ProverData K) :
    List (String × BusDir × Array K) :=
  rows.flatMap fun row ↦ rowSends c (Environment.fromArray row data)

/-- A table's interactions, as sends, are its rows' sends. -/
private theorem table_sends (t : Air.Flat.Table K) :
    t.interactions.map (fun i ↦ (i.channel.name, i.direction, i.msg)) =
      rowsSends t.component t.table t.data := by
  rw [table_interactions_eq, List.map_flatMap]
  rfl

/-- Everything a witness sends: the verifier's two messages, then each table's rows, over the
witness's data. -/
private theorem witness_sends {prog : Program} {κ : ℕ}
    (w : EnsembleWitness (leanIsaEnsemble prog κ)) :
    w.interactions.map (fun i ↦ (i.channel.name, i.direction, i.msg)) =
      [(StateChannel.name, .push, #[1, 1]), (StateChannel.name, .pull, #[prog.finalPc, 1])] ++
        w.tables.flatMap fun t ↦ rowsSends t.component t.table w.data := by
  unfold EnsembleWitness.interactions
  rw [List.map_append, verifier_sends, List.map_flatMap]
  congr 1
  refine List.flatMap_congr fun t ht ↦ ?_
  rw [table_sends, w.same_data t ht]
  rfl

/-- The messages a witness sends on a channel in a direction: those of its sends. -/
private theorem messagesOn_eq_sends {prog : Program} {κ : ℕ}
    (w : EnsembleWitness (leanIsaEnsemble prog κ)) (c : RawChannel K) (d : BusDir) :
    messagesOn w c d =
      chanOf c.name d (w.interactions.map fun i ↦ (i.channel.name, i.direction, i.msg)) :=
  activeMessages_filter_name _
    (fun i hi ↦ by rw [interactions_mult_eq_one w i hi]; exact one_ne_zero) _ _

/-- The sends of an opcode's table are those of its rows, when their instructions execute. -/
private theorem opTable_sends {κ : ℕ} (img : MemImage κ) (R : List PRow)
    (hR : R.length ≤ UInt64.size) (op : Opcode)
    (hRx : ∀ r ∈ R, ∃ next, execute img r.sk.regs r.sk.ins = some next)
    (data : ProverData K) :
    rowsSends (opTable img R hR op).component (opTable img R hR op).table data =
      (R.filter fun r ↦ r.sk.ins.opcode = op).flatMap (PRow.sends img) := by
  show ((R.filter fun r ↦ r.sk.ins.opcode = op).map (PRow.raw img)).flatMap
    (fun row ↦ rowSends (opComponent op) (Environment.fromArray row data)) = _
  rw [List.flatMap_map]
  refine List.flatMap_congr fun r hr ↦ ?_
  obtain ⟨hr1, hr2⟩ := List.mem_filter.mp hr
  simp only [decide_eq_true_eq] at hr2
  subst hr2
  exact PRow.rowSends_raw (hRx r hr1) data

/-- The sends of the memory block: per cell, the seed push and the finalize pull. -/
def memBlockSends {κ : ℕ} (img : MemImage κ) (fin : K → ℕ) :
    List (String × BusDir × Array K) :=
  (List.finRange (2 ^ κ)).flatMap fun i : Fin (2 ^ κ) ↦
    [(MemChannel.name, .push, #[gpow i, 1, (img i).limb 0, (img i).limb 1, (img i).limb 2]),
      (MemChannel.name, .pull,
        #[gpow i, g ^ fin (gpow i), (img i).limb 0, (img i).limb 1, (img i).limb 2])]

/-- The sends of the memory block's rows are `memBlockSends`. -/
private theorem memBlock_sends {κ : ℕ} (hκ : κ ≤ maxLogMem) (img : MemImage κ) (fin : K → ℕ)
    (data : ProverData K) :
    rowsSends (memBlock hκ img fin).component (memBlock hκ img fin).table data =
      memBlockSends img fin := by
  show (List.ofFn fun i : Fin (2 ^ κ) ↦ rawRow (memRowOf img i (g ^ fin (gpow i)))).flatMap
    (fun row ↦ rowSends (memComponent κ) (Environment.fromArray row data)) = _
  rw [List.ofFn_eq_map, List.flatMap_map]
  refine List.flatMap_congr fun i _ ↦ ?_
  rw [show rowSends (memComponent κ) _ = _ from
    mem_sends_gen (varFromOffset MemRow 0) _ (size MemRow) _ (eval_rowVar _ data)]
  rfl

/-- The sends of the bytecode block: per slot, the seed push and the finalize pull. -/
def bcBlockSends (prog : Program) (fin : K → ℕ) : List (String × BusDir × Array K) :=
  (List.finRange (2 ^ prog.logSize)).flatMap fun i : Fin (2 ^ prog.logSize) ↦
    [(BytecodeChannel.name, .push, bcMsgOf (gpow i) 1 (entry (prog.code i))),
      (BytecodeChannel.name, .pull, bcMsgOf (gpow i) (g ^ fin (gpow i)) (entry (prog.code i)))]

/-- The sends of the bytecode block's rows are `bcBlockSends`. -/
private theorem bcBlock_sends (prog : Program) (fin : K → ℕ) (data : ProverData K) :
    rowsSends (bcBlock prog fin).component (bcBlock prog fin).table data =
      bcBlockSends prog fin := by
  show (List.ofFn fun i : Fin (2 ^ prog.logSize) ↦
      rawRow (bytecodeRowOf prog i (g ^ fin (gpow i)))).flatMap
    (fun row ↦ rowSends (bytecodeComponent prog) (Environment.fromArray row data)) = _
  rw [List.ofFn_eq_map, List.flatMap_map]
  refine List.flatMap_congr fun i _ ↦ ?_
  rw [show rowSends (bytecodeComponent prog) _ = _ from
    bytecode_sends_gen (varFromOffset BytecodeRow 0) _ (size BytecodeRow) _ (eval_rowVar _ data)]
  simp [bytecodeRowOf, bcMsgOf]

/-! ## What each channel carries -/

/-- Everything the padded witness sends, in the ensemble's order: the verifier's two messages, the
rows of the six tables, the memory block, the bytecode block. -/
noncomputable def padSends (prog : Program) {κ : ℕ} (img : MemImage κ) (S : List Skel) :
    List (String × BusDir × Array K) :=
  [(StateChannel.name, .push, #[1, 1]), (StateChannel.name, .pull, #[prog.finalPc, 1])] ++
    (fillTables.flatMap fun op ↦
      ((padRows img S).filter fun r ↦ r.sk.ins.opcode = op).flatMap (PRow.sends img)) ++
    memBlockSends img (padMemFin img S) ++ bcBlockSends prog (padBcFin S)

/-- **The sends of the padded witness.** -/
theorem padWitness_sends (prog : Program) (input : PublicInput) {κ : ℕ} (img : MemImage κ)
    (S : List Skel) (hκ : κ ≤ maxLogMem) (hS : S.length ≤ UInt64.size)
    (hSx : ∀ sk ∈ S, ∃ next, execute img sk.regs sk.ins = some next) :
    (padWitness prog input img S hκ hS).interactions.map
        (fun i ↦ (i.channel.name, i.direction, i.msg)) = padSends prog img S := by
  have hR : ∀ r ∈ padRows img S, ∃ next, execute img r.sk.regs r.sk.ins = some next :=
    fun r hr ↦ hSx _ (mem_mkRows_sk hr)
  rw [witness_sends, ← List.flatMap_map (f := fun t : Air.Flat.Table K ↦ (t.component, t.table))
    (g := fun p ↦ rowsSends p.1 p.2 (padWitness prog input img S hκ hS).data), padWitness_map,
    List.flatMap_map]
  simp only [padTables, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    opTable_sends _ _ _ _ hR, memBlock_sends, bcBlock_sends, padSends, fillTables,
    List.append_assoc]

/-- The messages the padded witness sends on a channel in a direction. -/
private theorem messagesOn_padWitness (prog : Program) (input : PublicInput) {κ : ℕ}
    (img : MemImage κ)
    (S : List Skel) (hκ : κ ≤ maxLogMem) (hS : S.length ≤ UInt64.size)
    (hSx : ∀ sk ∈ S, ∃ next, execute img sk.regs sk.ins = some next) (c : RawChannel K)
    (d : BusDir) :
    messagesOn (padWitness prog input img S hκ hS) c d = chanOf c.name d (padSends prog img S) := by
  rw [messagesOn_eq_sends, padWitness_sends prog input img S hκ hS hSx]

/-- Every opcode has a table. -/
private theorem opcode_mem_fillTables (o : Opcode) : o ∈ fillTables := by
  cases o <;> decide

/-- **The six tables hold the rows of `R` regrouped by opcode**: their sends are a permutation of
those of the rows in order. -/
theorem tables_sends_perm {κ : ℕ} (img : MemImage κ) (R : List PRow) :
    (fillTables.flatMap fun op ↦
      (R.filter fun r ↦ r.sk.ins.opcode = op).flatMap (PRow.sends img)).Perm
      (R.flatMap (PRow.sends img)) := by
  rw [← List.flatMap_assoc]
  exact (regroup_perm fillTables (fun r : PRow ↦ r.sk.ins.opcode) R (by decide)
    fun r _ ↦ opcode_mem_fillTables _).flatMap_right _

/-- Permuted sends carry permuted messages on every channel and direction. -/
private theorem chanOf_perm {n : String} {d : BusDir} {l₁ l₂ : List (String × BusDir × Array K)}
    (h : l₁.Perm l₂) : (chanOf n d l₁).Perm (chanOf n d l₂) :=
  (h.filter _).map _

/-- On every channel and direction, the six tables carry the messages of the rows of `R`. -/
private theorem chanOf_tables_perm {κ : ℕ} (img : MemImage κ) (n : String) (d : BusDir)
    (R : List PRow) :
    (chanOf n d (fillTables.flatMap fun op ↦
      (R.filter fun r ↦ r.sk.ins.opcode = op).flatMap (PRow.sends img))).Perm
      (R.flatMap fun r ↦ chanOf n d (r.sends img)) := by
  rw [← chanOf_flatMap]
  exact chanOf_perm (tables_sends_perm img R)

/-- The padded witness's messages on a channel: the verifier's, the rows' of the six tables in
order, the memory block's, the bytecode block's, up to the regrouping of the rows. -/
private theorem chanOf_padSends_perm (prog : Program) {κ : ℕ} (img : MemImage κ) (S : List Skel)
    (n : String) (d : BusDir) :
    (chanOf n d (padSends prog img S)).Perm
      (chanOf n d [(StateChannel.name, .push, #[1, 1]),
          (StateChannel.name, .pull, #[prog.finalPc, 1])] ++
        (padRows img S).flatMap (fun r ↦ chanOf n d (r.sends img)) ++
        chanOf n d (memBlockSends img (padMemFin img S)) ++
        chanOf n d (bcBlockSends prog (padBcFin S))) := by
  unfold padSends
  simp only [chanOf_append]
  exact (((chanOf_tables_perm img n d (padRows img S)).append_left _).append_right _).append_right _

/-! ### The blocks' channels -/

/-- The word at the address of an index, as a memory message. -/
private theorem memMsg_gpow {κ : ℕ} (hκ : κ < 64) (img : MemImage κ) (i : Fin (2 ^ κ)) (e : ℕ) :
    memMsg img (gpow i) e =
      #[gpow i, g ^ e, (img i).limb 0, (img i).limb 1, (img i).limb 2] := by
  have h := MemImage.limbsAt_eq_of_read (MemImage.read_gpow hκ img i)
  simp [memMsg, memMsgOf, h]

/-- The memory block sends only on the memory channel. -/
private theorem memBlockSends_names {κ : ℕ} (img : MemImage κ) (fin : K → ℕ) :
    ∀ x ∈ memBlockSends img fin, x.1 = MemChannel.name := by
  intro x hx
  simp only [memBlockSends, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hx
  obtain ⟨i, -, rfl | rfl⟩ := hx <;> rfl

/-- The bytecode block sends only on the bytecode channel. -/
private theorem bcBlockSends_names (prog : Program) (fin : K → ℕ) :
    ∀ x ∈ bcBlockSends prog fin, x.1 = BytecodeChannel.name := by
  intro x hx
  simp only [bcBlockSends, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hx
  obtain ⟨i, -, rfl | rfl⟩ := hx <;> rfl

/-- The memory block's seed pushes: the word of each cell with the count `g^0`. -/
private theorem memBlock_push {κ : ℕ} (hκ : κ < 64) (img : MemImage κ) (fin : K → ℕ) :
    chanOf MemChannel.name .push (memBlockSends img fin) =
      (List.finRange (2 ^ κ)).map fun i : Fin (2 ^ κ) ↦ memMsg img (gpow i) 0 := by
  unfold memBlockSends
  rw [chanOf_flatMap, ← flatMap_singleton_eq_map]
  refine List.flatMap_congr fun i _ ↦ ?_
  simp [chanOf, memMsg_gpow hκ]

/-- The memory block's finalize pulls: the word of each cell with the count its row holds. -/
private theorem memBlock_pull {κ : ℕ} (hκ : κ < 64) (img : MemImage κ) (fin : K → ℕ) :
    chanOf MemChannel.name .pull (memBlockSends img fin) =
      (List.finRange (2 ^ κ)).map fun i : Fin (2 ^ κ) ↦ memMsg img (gpow i) (fin (gpow i)) := by
  unfold memBlockSends
  rw [chanOf_flatMap, ← flatMap_singleton_eq_map]
  refine List.flatMap_congr fun i _ ↦ ?_
  simp [chanOf, memMsg_gpow hκ]

/-- The bytecode block's seed pushes. -/
private theorem bcBlock_push (prog : Program) (fin : K → ℕ) :
    chanOf BytecodeChannel.name .push (bcBlockSends prog fin) =
      (List.finRange (2 ^ prog.logSize)).map fun i : Fin (2 ^ prog.logSize) ↦
        bcMsg prog (gpow i) 0 := by
  unfold bcBlockSends
  rw [chanOf_flatMap, ← flatMap_singleton_eq_map]
  refine List.flatMap_congr fun i _ ↦ ?_
  simp [chanOf, bcMsg, entryAt, Program.fetch_gpow]

/-- The bytecode block's finalize pulls. -/
private theorem bcBlock_pull (prog : Program) (fin : K → ℕ) :
    chanOf BytecodeChannel.name .pull (bcBlockSends prog fin) =
      (List.finRange (2 ^ prog.logSize)).map fun i : Fin (2 ^ prog.logSize) ↦
        bcMsg prog (gpow i) (fin (gpow i)) := by
  unfold bcBlockSends
  rw [chanOf_flatMap, ← flatMap_singleton_eq_map]
  refine List.flatMap_congr fun i _ ↦ ?_
  simp [chanOf, bcMsg, entryAt, Program.fetch_gpow]

/-- A list of sends all on one channel carries nothing on another. -/
private theorem chanOf_eq_nil_of_names {n m : String} {d : BusDir}
    {l : List (String × BusDir × Array K)} (h : ∀ x ∈ l, x.1 = m) (hnm : m ≠ n) :
    chanOf n d l = [] :=
  chanOf_eq_nil fun x hx h' ↦ hnm ((h x hx).symm.trans h'.1)

/-! ## The three balances -/

/-- The addresses of the `2^k` rows of a block are distinct, for `k ≤ 32`. -/
private theorem gpow_keys_nodup (k : ℕ) (hk : k ≤ 32) :
    ((List.finRange (2 ^ k)).map fun i : Fin (2 ^ k) ↦ gpow (i : ℕ)).Nodup := by
  refine List.Nodup.map_on (fun x _ y _ h ↦ ?_) (List.nodup_finRange _)
  have h32 : 2 ^ k ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) hk
  have hx : (x : ℕ) ∈ Set.Iio (2 ^ 64 - 1) := by
    simp only [Set.mem_Iio]; have := x.isLt; omega
  have hy : (y : ℕ) ∈ Set.Iio (2 ^ 64 - 1) := by
    simp only [Set.mem_Iio]; have := y.isLt; omega
  exact Fin.ext (gpow_injOn hx hy h)

/-- A block's seeds and finalizes against the reads of the rows, for any messages indexed by the
address and the number. -/
private theorem block_balance {ι α : Type} [DecidableEq ι] (keys : List ι) (hnd : keys.Nodup)
    (mk : ι → ℕ → α) (L : List ι) (hL : ∀ a ∈ L, a ∈ keys) :
    (List.zipWith (fun a e ↦ mk a (e + 1)) L (readExps (fun _ ↦ 0) L) ++
        keys.map fun a ↦ mk a 0).Perm
      (List.zipWith (fun a e ↦ mk a e) L (readExps (fun _ ↦ 0) L) ++
        keys.map fun a ↦ mk a (readBump (fun _ ↦ 0) L a)) :=
  List.perm_append_comm.trans
    ((chain_balance keys hnd mk L hL fun _ ↦ 0).trans List.perm_append_comm)

/-- The channel names are distinct. -/
private theorem state_ne_mem : StateChannel.name ≠ MemChannel.name := by decide

/-- The channel names are distinct. -/
private theorem state_ne_bytecode : StateChannel.name ≠ BytecodeChannel.name := by decide

/-- The channel names are distinct. -/
private theorem mem_ne_bytecode : MemChannel.name ≠ BytecodeChannel.name := by decide

/-- **The memory channel balances**: the rows' reads, numbered by the chain, against the block's
seeds and finalizes. -/
theorem mem_pair_perm (prog : Program) {κ : ℕ} (hκ : κ ≤ maxLogMem) (img : MemImage κ)
    (S : List Skel) (hS : ∀ sk ∈ S, ∃ next, execute img sk.regs sk.ins = some next) :
    (chanOf MemChannel.name .push (padSends prog img S)).Perm
      (chanOf MemChannel.name .pull (padSends prog img S)) := by
  have hκ64 : κ < 64 := by unfold maxLogMem at hκ; omega
  have hmem : ∀ a ∈ S.flatMap (fun sk ↦ readAddrs img sk.fp sk.ins),
      a ∈ (List.finRange (2 ^ κ)).map fun i : Fin (2 ^ κ) ↦ gpow (i : ℕ) := by
    intro a ha
    obtain ⟨sk, hsk, ha⟩ := List.mem_flatMap.mp ha
    obtain ⟨next, hn⟩ := hS sk hsk
    obtain ⟨w, hw⟩ := readAddrs_valid (pc := sk.pc) (fp := sk.fp) hn a ha
    obtain ⟨i, rfl, -⟩ := (MemImage.read_eq_some_iff hκ64 img).mp hw
    exact List.mem_map.mpr ⟨i, List.mem_finRange _, rfl⟩
  have hb := block_balance _ (gpow_keys_nodup κ hκ) (memMsg img) _ hmem
  have h1 : (padRows img S).flatMap (fun r ↦ chanOf MemChannel.name .push (r.sends img)) =
      List.zipWith (fun a e ↦ memMsg img a (e + 1))
        (S.flatMap fun sk ↦ readAddrs img sk.fp sk.ins)
        (readExps (fun _ ↦ 0) (S.flatMap fun sk ↦ readAddrs img sk.fp sk.ins)) :=
    mkRows_memPushes img (fun _ ↦ 0) (fun _ ↦ 0) S
  have h2 : (padRows img S).flatMap (fun r ↦ chanOf MemChannel.name .pull (r.sends img)) =
      List.zipWith (fun a e ↦ memMsg img a e)
        (S.flatMap fun sk ↦ readAddrs img sk.fp sk.ins)
        (readExps (fun _ ↦ 0) (S.flatMap fun sk ↦ readAddrs img sk.fp sk.ins)) :=
    mkRows_memPulls img (fun _ ↦ 0) (fun _ ↦ 0) S
  have hv : ∀ d, chanOf MemChannel.name d
      [(StateChannel.name, .push, #[1, 1]), (StateChannel.name, .pull, #[prog.finalPc, 1])] =
      [] := fun d ↦ chanOf_eq_nil_of_names (by simp) state_ne_mem
  have hc : ∀ d, chanOf MemChannel.name d (bcBlockSends prog (padBcFin S)) = [] := fun d ↦
    chanOf_eq_nil_of_names (bcBlockSends_names prog _) mem_ne_bytecode.symm
  refine (chanOf_padSends_perm prog img S _ _).trans
    (List.Perm.trans ?_ (chanOf_padSends_perm prog img S _ _).symm)
  rw [hv, hv, hc, hc, h1, h2, memBlock_push hκ64, memBlock_pull hκ64]
  simp only [List.nil_append, List.append_nil]
  simpa only [List.map_map, Function.comp_def, padMemFin] using hb

/-- **The bytecode channel balances**: the rows' fetches, numbered by the chain, against the
block's seeds and finalizes. -/
theorem bc_pair_perm (prog : Program) {κ : ℕ} (img : MemImage κ) (S : List Skel)
    (hS : ∀ sk ∈ S, SkelOk prog img sk) :
    (chanOf BytecodeChannel.name .push (padSends prog img S)).Perm
      (chanOf BytecodeChannel.name .pull (padSends prog img S)) := by
  have hmem : ∀ a ∈ S.map (·.pc),
      a ∈ (List.finRange (2 ^ prog.logSize)).map fun i : Fin (2 ^ prog.logSize) ↦
        gpow (i : ℕ) := by
    intro a ha
    obtain ⟨sk, hsk, rfl⟩ := List.mem_map.mp ha
    obtain ⟨i, hi, -⟩ := Program.fetch_eq_some_iff prog |>.mp (hS sk hsk).1
    exact List.mem_map.mpr ⟨i, List.mem_finRange _, hi.symm⟩
  have hb := block_balance _ (gpow_keys_nodup prog.logSize prog.logSize_le) (bcMsg prog) _ hmem
  have hF : ∀ sk ∈ S, prog.fetch sk.pc = some sk.ins := fun sk h ↦ (hS sk h).1
  have h1 : (padRows img S).flatMap
      (fun r ↦ chanOf BytecodeChannel.name .push (r.sends img)) =
      List.zipWith (fun pc e ↦ bcMsg prog pc (e + 1)) (S.map (·.pc))
        (readExps (fun _ ↦ 0) (S.map (·.pc))) :=
    mkRows_bcPushes img (fun _ ↦ 0) (fun _ ↦ 0) S hF
  have h2 : (padRows img S).flatMap
      (fun r ↦ chanOf BytecodeChannel.name .pull (r.sends img)) =
      List.zipWith (fun pc e ↦ bcMsg prog pc e) (S.map (·.pc))
        (readExps (fun _ ↦ 0) (S.map (·.pc))) :=
    mkRows_bcPulls img (fun _ ↦ 0) (fun _ ↦ 0) S hF
  have hv : ∀ d, chanOf BytecodeChannel.name d
      [(StateChannel.name, .push, #[1, 1]), (StateChannel.name, .pull, #[prog.finalPc, 1])] =
      [] := fun d ↦ chanOf_eq_nil_of_names (by simp) state_ne_bytecode
  have hc : ∀ d, chanOf BytecodeChannel.name d (memBlockSends img (padMemFin img S)) = [] :=
    fun d ↦ chanOf_eq_nil_of_names (memBlockSends_names img _) mem_ne_bytecode
  refine (chanOf_padSends_perm prog img S _ _).trans
    (List.Perm.trans ?_ (chanOf_padSends_perm prog img S _ _).symm)
  rw [hv, hv, hc, hc, h1, h2, bcBlock_push, bcBlock_pull]
  simp only [List.nil_append, List.append_nil]
  simpa only [List.map_map, Function.comp_def, padBcFin] using hb

/-- **The state channel balances**, from the hypothesis that the skeletons' states and successors
balance with the initial and final states: the rows' pulls and pushes are those states,
regrouped by the six tables. -/
theorem state_pair_perm (prog : Program) {κ : ℕ} (img : MemImage κ) (S : List Skel)
    (hstate : (#[1, 1] :: S.map fun sk ↦ #[(nextOf img sk).pc, (nextOf img sk).fp]).Perm
      (#[prog.finalPc, 1] :: S.map fun sk ↦ #[sk.pc, sk.fp])) :
    (chanOf StateChannel.name .push (padSends prog img S)).Perm
      (chanOf StateChannel.name .pull (padSends prog img S)) := by
  have h1 : (padRows img S).flatMap (fun r ↦ chanOf StateChannel.name .push (r.sends img)) =
      S.map fun sk ↦ #[(nextOf img sk).pc, (nextOf img sk).fp] :=
    mkRows_statePushes img (fun _ ↦ 0) (fun _ ↦ 0) S
  have h2 : (padRows img S).flatMap (fun r ↦ chanOf StateChannel.name .pull (r.sends img)) =
      S.map fun sk ↦ #[sk.pc, sk.fp] :=
    mkRows_statePulls img (fun _ ↦ 0) (fun _ ↦ 0) S
  have hv1 : chanOf StateChannel.name .push
      [(StateChannel.name, .push, #[1, 1]), (StateChannel.name, .pull, #[prog.finalPc, 1])] =
      [#[1, 1]] := by
    simp [chanOf]
  have hv2 : chanOf StateChannel.name .pull
      [(StateChannel.name, .push, #[1, 1]), (StateChannel.name, .pull, #[prog.finalPc, 1])] =
      [#[prog.finalPc, 1]] := by
    simp [chanOf]
  have hm : ∀ d, chanOf StateChannel.name d (memBlockSends img (padMemFin img S)) = [] :=
    fun d ↦ chanOf_eq_nil_of_names (memBlockSends_names img _) state_ne_mem.symm
  have hb : ∀ d, chanOf StateChannel.name d (bcBlockSends prog (padBcFin S)) = [] :=
    fun d ↦ chanOf_eq_nil_of_names (bcBlockSends_names prog _) state_ne_bytecode.symm
  refine (chanOf_padSends_perm prog img S _ _).trans
    (List.Perm.trans ?_ (chanOf_padSends_perm prog img S _ _).symm)
  rw [hv1, hv2, hm, hm, hb, hb, h1, h2]
  simpa only [List.append_nil, List.singleton_append] using hstate

/-! ### The number of interactions -/

/-- Two sends per entry. -/
private theorem length_flatMap_pair {α β : Type} (l : List α) (f h : α → β) :
    (l.flatMap fun x ↦ [f x, h x]).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.flatMap_cons, List.length_append, ih, List.length_cons]
    simp only [List.length_cons, List.length_nil]
    omega

/-- At most `k` sends per entry. -/
private theorem length_flatMap_le {α β : Type} (l : List α) (F : α → List β) (k : ℕ)
    (h : ∀ a ∈ l, (F a).length ≤ k) : (l.flatMap F).length ≤ k * l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_succ]
    have h1 := h x List.mem_cons_self
    have h2 := ih fun a ha ↦ h a (List.mem_cons_of_mem _ ha)
    omega

/-- An instruction reads at most nine cells. -/
private theorem readAddrs_length_le {κ : ℕ} (mem : MemImage κ) (fp : K) (ins : Instr) :
    (readAddrs mem fp ins).length ≤ 9 := by
  cases ins <;> simp [readAddrs]

/-- A row sends at most twenty-two messages. -/
private theorem PRow.sends_length_le {κ : ℕ} (img : MemImage κ) (r : PRow) :
    (r.sends img).length ≤ 22 := by
  rw [PRow.sends, sendsOf, List.length_append, length_flatMap_pair, readsOf, List.length_mapIdx]
  have := readAddrs_length_le img r.sk.fp r.sk.ins
  simp only [List.length_cons, List.length_nil]
  omega

/-- The skeletons are the rows of the six tables: at most `6 · 2^32` of them when every table's
height is a power of two within the cap. -/
theorem skels_length_le {S : List Skel}
    (hheights : ∀ op, ∃ σ ≤ maxLogRows, Skel.count op S = 2 ^ σ) : S.length ≤ 6 * 2 ^ 32 := by
  have hp := regroup_perm fillTables (fun sk : Skel ↦ sk.ins.opcode) S (by decide)
    fun sk _ ↦ opcode_mem_fillTables _
  have hc : ∀ op, Skel.count op S ≤ 2 ^ 32 := fun op ↦ by
    obtain ⟨σ, hσ, h⟩ := hheights op
    rw [h]
    exact Nat.pow_le_pow_right (by norm_num) hσ
  have h1 := hc .xor
  have h2 := hc .mulNative
  have h3 := hc .setConstant
  have h4 := hc .deref
  have h5 := hc .jump
  have h6 := hc .blake2s
  unfold Skel.count Skel.onTable at h1 h2 h3 h4 h5 h6
  rw [← hp.length_eq]
  simp only [fillTables, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.length_append]
  omega

/-- **Fewer than `2^64` interactions**: at most twenty-two per skeleton and two per row of each
block. -/
theorem padSends_length_lt (prog : Program) {κ : ℕ} (hκ : κ ≤ maxLogMem) (img : MemImage κ)
    (S : List Skel) (hlen : S.length ≤ 6 * 2 ^ 32) : (padSends prog img S).length < 2 ^ 64 := by
  have h1 : (fillTables.flatMap fun op ↦
      ((padRows img S).filter fun r ↦ r.sk.ins.opcode = op).flatMap (PRow.sends img)).length ≤
      22 * S.length := by
    rw [(tables_sends_perm img (padRows img S)).length_eq, ← padRows_length img S]
    exact length_flatMap_le _ _ 22 fun r _ ↦ PRow.sends_length_le img r
  have h2 : (memBlockSends img (padMemFin img S)).length = 2 * 2 ^ κ := by
    rw [memBlockSends, length_flatMap_pair, List.length_finRange]
  have h3 : (bcBlockSends prog (padBcFin S)).length = 2 * 2 ^ prog.logSize := by
    rw [bcBlockSends, length_flatMap_pair, List.length_finRange]
  have h4 : 2 ^ κ ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) hκ
  have h5 : 2 ^ prog.logSize ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) prog.logSize_le
  have e32 : (2 : ℕ) ^ 32 = 4294967296 := by norm_num
  have e64 : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
  simp only [padSends, List.length_append, List.length_cons, List.length_nil, h2, h3]
  omega

/-! ## The constraints -/

/-- The `JUMP` row circuit's constraints, generically: they are exactly the two residuals of the
local witnesses `w` and `b`, at slots `n` and `n + 1`. -/
private theorem jump_constraints_iff (x : Var JumpRow K) (env : Environment K) (n : ℕ)
    (r : JumpRow K) (hx : eval env x = r) (w b : K) (hw : env.get n = w)
    (hb : env.get (n + 1) = b) :
    ((jumpTable.main x).operations n).ConstraintsHold env ↔
      b + r.vcond * w = 0 ∧ r.vcond * (b + 1) = 0 := by
  subst hx
  obtain ⟨pc, fp, oc, od, of, vcond, vpc, vfp, rc, rd, rf, rbc⟩ := x
  dsimp only [jumpTable]
  simp only [circuit_norm, instructionStep, memRead, bytecodeRead, -BitVec.reduceNeg]
  constructor
  · intro h
    have h1 := h _ (Or.inl rfl)
    have h2 := h _ (Or.inr rfl)
    simp only [Expression.eval, hw, hb] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩ e (rfl | rfl)
    · simp only [Expression.eval, hw, hb, h1]
    · simp only [Expression.eval, hb, h2]

/-- The witness slot of a `JUMP` raw row is its first witness. -/
private theorem jumpRaw_get_witness (r : JumpRow K) (w b : K) (data : ProverData K) :
    (Environment.fromArray (jumpRaw r w b) data).get (size JumpRow) = w := by
  show ((rawRow r ++ #[w, b])[size JumpRow]?).getD 0 = w
  rw [Array.getElem?_append_right (by rw [rawRow_size]), rawRow_size]
  simp

/-- A `JUMP` raw row satisfies the table's constraints exactly when its witnesses satisfy the two
residuals. -/
theorem jumpRaw_constraints_iff (r : JumpRow K) (w b : K) (data : ProverData K) :
    jumpComponent.operations.ConstraintsHold (Environment.fromArray (jumpRaw r w b) data) ↔
      b + r.vcond * w = 0 ∧ r.vcond * (b + 1) = 0 := by
  rw [Component.constraintsHold_iff]
  exact jump_constraints_iff (varFromOffset JumpRow 0) _ (size JumpRow) r
    (eval_rowVar_append r #[w, b] data) w b (jumpRaw_get_witness r w b data)
    (jumpRaw_get_indicator r w b data)

/-- A `JUMP` raw row whose witnesses satisfy the two residuals satisfies the table's
constraints. -/
theorem jumpRaw_constraints (r : JumpRow K) (w b : K) (h1 : b + r.vcond * w = 0)
    (h2 : r.vcond * (b + 1) = 0) (data : ProverData K) :
    jumpComponent.operations.ConstraintsHold (Environment.fromArray (jumpRaw r w b) data) :=
  (jumpRaw_constraints_iff r w b data).mpr ⟨h1, h2⟩

/-- **Every table of the padded witness satisfies its constraints**: only the `JUMP` table
asserts anything, and its rows carry the honest inverse and indicator. -/
theorem padWitness_constraints (prog : Program) (input : PublicInput) {κ : ℕ} (img : MemImage κ)
    (S : List Skel) (hκ : κ ≤ maxLogMem) (hS : S.length ≤ UInt64.size) :
    (padWitness prog input img S hκ hS).Constraints := by
  intro t ht row hrow
  obtain ⟨t₀, h₀, hc, htab⟩ := mem_padWitness_tables ht
  rw [← htab] at hrow
  show t.component.operations.ConstraintsHold (Environment.fromArray row t.data)
  rw [← hc]
  simp only [padTables, List.mem_cons, List.not_mem_nil, or_false] at h₀
  rcases h₀ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact xor_constraints _
  · exact mul_constraints _
  · exact set_constraints _
  · exact deref_constraints _
  · have hrow' : row ∈ ((padRows img S).filter fun r ↦ r.sk.ins.opcode = .jump).map
        (PRow.raw img) := hrow
    obtain ⟨⟨⟨pc, fp, ins⟩, exps, bc⟩, hr, rfl⟩ := List.mem_map.mp hrow'
    have h := (List.mem_filter.mp hr).2
    simp only [decide_eq_true_eq] at h
    cases ins with
    | jump oc od of =>
      obtain ⟨h1, h2⟩ := flags_complete ((img.limbsAt (fp * oc))[0])
      exact jumpRaw_constraints (jumpRowOf img pc fp oc od of _ _ _ _)
        (if (img.limbsAt (fp * oc))[0] = 0 then 0 else ((img.limbsAt (fp * oc))[0])⁻¹)
        (if (img.limbsAt (fp * oc))[0] = 0 then 0 else 1) h1 h2 _
    | xor _ _ _ => simp [Instr.opcode] at h
    | mulNative _ _ _ => simp [Instr.opcode] at h
    | setConstant _ _ => simp [Instr.opcode] at h
    | deref _ _ _ _ => simp [Instr.opcode] at h
    | blake2s _ _ _ _ => simp [Instr.opcode] at h
  · exact blake2s_constraints _
  · exact mem_constraints κ _
  · exact bytecode_constraints prog _

/-! ## The verifier's checks -/

/-- Every pull of a row's read carries a nonzero count, when the row's counts are nonzero. -/
private theorem sendsOf_counts_ne_zero {pc fp : K} {next : Regs K} {rbc : K} {e : Vector K 8}
    {reads : List (K × K × Vector K 3)} (hb : rbc ≠ 0) (hr : ∀ x ∈ reads, x.2.1 ≠ 0) :
    ∀ y ∈ sendsOf pc fp next rbc e reads,
      (y.1 = MemChannel.name ∨ y.1 = BytecodeChannel.name) → y.2.1 = .pull →
        ∃ h : 1 < y.2.2.size, y.2.2[1] ≠ 0 := by
  intro y hy hn hd
  simp only [sendsOf, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap] at hy
  rcases hy with (rfl | rfl | rfl | rfl) | ⟨x, hx, rfl | rfl⟩
  · simp [StateChannel, MemChannel, BytecodeChannel] at hn
  · simp [StateChannel, MemChannel, BytecodeChannel] at hn
  · exact ⟨by simp [bcMsgOf], by simpa [bcMsgOf] using hb⟩
  · simp at hd
  · exact ⟨by simp [memMsgOf], by simpa [memMsgOf] using hr x hx⟩
  · simp at hd

/-- A row of the witness has nonzero counts: they are powers of `g`. -/
private theorem PRow.sends_counts_ne_zero {κ : ℕ} (img : MemImage κ) (r : PRow) :
    ∀ y ∈ r.sends img,
      (y.1 = MemChannel.name ∨ y.1 = BytecodeChannel.name) → y.2.1 = .pull →
        ∃ h : 1 < y.2.2.size, y.2.2[1] ≠ 0 := by
  refine sendsOf_counts_ne_zero (pow_ne_zero _ g_ne_zero) fun x hx ↦ ?_
  simp only [readsOf, List.mem_mapIdx] at hx
  obtain ⟨j, -, rfl⟩ := hx
  exact pow_ne_zero _ g_ne_zero

/-- **Every read pull of the six tables carries a nonzero count.** -/
theorem padWitness_counts_nonzero (prog : Program) (input : PublicInput) {κ : ℕ}
    (img : MemImage κ) (S : List Skel) (hκ : κ ≤ maxLogMem) (hS : S.length ≤ UInt64.size)
    (hSx : ∀ sk ∈ S, ∃ next, execute img sk.regs sk.ins = some next) :
    CountsNonzero (padWitness prog input img S hκ hS) := by
  have hR : ∀ r ∈ padRows img S, ∃ next, execute img r.sk.regs r.sk.ins = some next :=
    fun r hr ↦ hSx _ (mem_mkRows_sk hr)
  intro t ht i hi hn hd h
  have hpair : (t.component, t.table) ∈ ((padTables prog img S hκ hS).take 6).map
      fun t ↦ (t.component, t.table) := by
    rw [List.map_take, ← padWitness_map (input := input), ← List.map_take]
    exact List.mem_map_of_mem ht
  obtain ⟨t₀, h₀, he⟩ := List.mem_map.mp hpair
  have h6 : (padTables prog img S hκ hS).take 6 =
      fillTables.map (opTable img (padRows img S) ((padRows_length img S).trans_le hS)) := rfl
  rw [h6, List.mem_map] at h₀
  obtain ⟨op, -, rfl⟩ := h₀
  have hmem := List.mem_map_of_mem (f := fun i : Interaction K ↦ (i.channel.name, i.direction,
    i.msg)) hi
  obtain ⟨hc, htab⟩ := Prod.mk.inj he
  rw [table_sends, ← hc, ← htab, opTable_sends img _ _ op hR] at hmem
  obtain ⟨r, -, hr⟩ := List.mem_flatMap.mp hmem
  obtain ⟨_, hne⟩ := PRow.sends_counts_ne_zero img _ _ hr hn hd
  exact hne

/-! ## The compression and the words -/

/-- **Every `BLAKE2S` row compresses**: the row of an executing instruction satisfies the
relation its execution checks. -/
theorem padWitness_blake2s_valid (prog : Program) (input : PublicInput) {κ : ℕ}
    (img : MemImage κ) (S : List Skel) (hκ : κ ≤ maxLogMem) (hS : S.length ≤ UInt64.size)
    (hSx : ∀ sk ∈ S, ∃ next, execute img sk.regs sk.ins = some next) :
    Blake2sRowsValid (padWitness prog input img S hκ hS) := by
  intro row hrow
  have hrow' : row ∈ ((padRows img S).filter fun r ↦ r.sk.ins.opcode = .blake2s).map
      (PRow.raw img) := by
    rw [blake2sRows, (padWitness_tableAt 5).2] at hrow
    exact hrow
  obtain ⟨⟨⟨pc, fp, ins⟩, exps, bc⟩, hr, rfl⟩ := List.mem_map.mp hrow'
  obtain ⟨hr1, hr2⟩ := List.mem_filter.mp hr
  simp only [decide_eq_true_eq] at hr2
  obtain ⟨next, hn⟩ := hSx _ (mem_mkRows_sk hr1)
  cases ins with
  | blake2s om ocv oout omd =>
    have hom : om = ![om 0, om 1, om 2, om 3] := by funext i; fin_cases i <;> rfl
    have hn' : execute img ⟨pc, fp⟩ (.blake2s ![om 0, om 1, om 2, om 3] ocv oout omd) =
        some next := hom ▸ hn
    simp only [PRow.raw, rowOf, rawRow]
    rw [blake2sRowAt_toElements]
    exact ((blake2s_refines_iff _ _ _).mp (blake2sRowOf_refines hn' _ _ _ _ _ _ _ _ _ _)).2.1
  | xor _ _ _ => simp [Instr.opcode] at hr2
  | mulNative _ _ _ => simp [Instr.opcode] at hr2
  | setConstant _ _ => simp [Instr.opcode] at hr2
  | deref _ _ _ _ => simp [Instr.opcode] at hr2
  | jump _ _ _ => simp [Instr.opcode] at hr2

/-! ## The caps -/

/-- The rows of a table of the padded witness are the skeletons of its opcode. -/
private theorem length_filter_mkRows {κ : ℕ} (img : MemImage κ) (sm sb : K → ℕ) (S : List Skel)
    (op : Opcode) :
    ((mkRows img sm sb S).filter fun r ↦ r.sk.ins.opcode = op).length = Skel.count op S := by
  unfold Skel.count Skel.onTable
  conv_rhs => rw [← mkRows_sk img sm sb S]
  rw [List.filter_map, List.length_map]
  rfl

/-- An opcode's table of the padded rows has a row per skeleton of the opcode. -/
private theorem opRows_length {κ : ℕ} (img : MemImage κ) (S : List Skel) (op : Opcode) :
    (opRows img (padRows img S) op).length = Skel.count op S := by
  rw [opRows, List.length_map, padRows, length_filter_mkRows]

/-- **The announced sizes are within the caps**: the memory window, every table's height a power
of two within the cap, and the `BLAKE2S` floor. -/
theorem padWitness_caps (prog : Program) (input : PublicInput) {κ : ℕ} (img : MemImage κ)
    (S : List Skel) (hκmin : minLogMem ≤ κ) (hκ : κ ≤ maxLogMem) (hS : S.length ≤ UInt64.size)
    (hheights : ∀ op, ∃ σ ≤ maxLogRows, Skel.count op S = 2 ^ σ)
    (hblake : 2 ^ minLogRowsBlake2s ≤ Skel.count .blake2s S) :
    Caps (padWitness prog input img S hκ hS) where
  minLogMem_le := hκmin
  le_maxLogMem := hκ
  heights := by
    intro t ht
    obtain ⟨t₀, h₀, -, htab⟩ := mem_padWitness_tables ht
    rw [← htab]
    simp only [padTables, List.mem_cons, List.not_mem_nil, or_false] at h₀
    have hop : ∀ op, ∃ σ ≤ maxLogRows, (opRows img (padRows img S) op).length = 2 ^ σ := by
      intro op
      obtain ⟨σ, hσ, h⟩ := hheights op
      exact ⟨σ, hσ, by rw [opRows_length, h]⟩
    rcases h₀ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hop _
    · exact hop _
    · exact hop _
    · exact hop _
    · exact hop _
    · exact hop _
    · exact ⟨κ, hκ, memRowsOf_length img _⟩
    · exact ⟨prog.logSize, prog.logSize_le, bcRowsOf_length prog _⟩
  blake2s_height := by
    rw [blake2sRows, (padWitness_tableAt 5).2]
    show 2 ^ minLogRowsBlake2s ≤ (opRows img (padRows img S) .blake2s).length
    rw [opRows_length]
    exact hblake

/-! ## The witness satisfies the statement -/

/-- **The padded witness balances** on each of the three channels: fewer than `2^64`
interactions, every multiplicity `1`, and the messages of the pushes a permutation of those of
the pulls. -/
theorem padWitness_balanced (prog : Program) (input : PublicInput) {κ : ℕ} (img : MemImage κ)
    (S : List Skel) (hκ : κ ≤ maxLogMem) (hS : S.length ≤ UInt64.size)
    (hSok : ∀ sk ∈ S, SkelOk prog img sk)
    (hstate : (#[1, 1] :: S.map fun sk ↦ #[(nextOf img sk).pc, (nextOf img sk).fp]).Perm
      (#[prog.finalPc, 1] :: S.map fun sk ↦ #[sk.pc, sk.fp]))
    (hlen : S.length ≤ 6 * 2 ^ 32) :
    (padWitness prog input img S hκ hS).Balanced .multiset := by
  have hSx : ∀ sk ∈ S, ∃ next, execute img sk.regs sk.ins = some next := fun sk h ↦ (hSok sk h).2
  intro c hc
  rw [EnsembleWitness.interactionsWith_eq_filter_name hc]
  refine ⟨?_, fun i hi ↦ Or.inr (interactions_mult_eq_one _ i (List.mem_of_mem_filter hi)), ?_⟩
  · refine lt_of_le_of_lt (List.length_filter_le _ _) ?_
    rw [← List.length_map (f := fun i : Interaction K ↦ (i.channel.name, i.direction, i.msg)),
      padWitness_sends prog input img S hκ hS hSx]
    exact padSends_length_lt prog hκ img S hlen
  · have hperm : (messagesOn (padWitness prog input img S hκ hS) c .push).Perm
        (messagesOn (padWitness prog input img S hκ hS) c .pull) := by
      rw [messagesOn_padWitness prog input img S hκ hS hSx,
        messagesOn_padWitness prog input img S hκ hS hSx]
      simp only [leanIsaEnsemble, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact state_pair_perm prog img S hstate
      · exact mem_pair_perm prog hκ img S hSx
      · exact bc_pair_perm prog img S hSok
    unfold messagesOn at hperm
    convert hperm using 3

/-- **The witness of a padded execution satisfies the constraint statement.** When the skeletons
`S` are sound for the program and the image, their state pulls and pushes balance with the
initial and final states, every table's height is a power of two within the cap and the `BLAKE2S`
table has at least eight rows, the memory log-size is in the window and the image has the two
public words, `padWitness prog input img S hκ hS` satisfies every conjunct of `SatisfiedBy`. -/
theorem padWitness_satisfiedBy (prog : Program) (input : PublicInput) {κ : ℕ} (img : MemImage κ)
    (S : List Skel) (hκmin : minLogMem ≤ κ) (hκ : κ ≤ maxLogMem) (hS : S.length ≤ UInt64.size)
    (hSok : ∀ sk ∈ S, SkelOk prog img sk)
    (hstate : (#[1, 1] :: S.map fun sk ↦ #[(nextOf img sk).pc, (nextOf img sk).fp]).Perm
      (#[prog.finalPc, 1] :: S.map fun sk ↦ #[sk.pc, sk.fp]))
    (hheights : ∀ op, ∃ σ ≤ maxLogRows, Skel.count op S = 2 ^ σ)
    (hblake : 2 ^ minLogRowsBlake2s ≤ Skel.count .blake2s S)
    (hw0 : img.read (gpow 0) = some input.word0) (hw1 : img.read (gpow 1) = some input.word1) :
    SatisfiedBy prog input (padWitness prog input img S hκ hS) := by
  have hSx : ∀ sk ∈ S, ∃ next, execute img sk.regs sk.ins = some next := fun sk h ↦ (hSok sk h).2
  exact
    { public_input_eq := rfl
      constraints := padWitness_constraints prog input img S hκ hS
      balanced := padWitness_balanced prog input img S hκ hS hSok hstate
        (skels_length_le hheights)
      counts_nonzero := padWitness_counts_nonzero prog input img S hκ hS hSx
      caps := padWitness_caps prog input img S hκmin hκ hS hheights hblake
      blake2s_valid := padWitness_blake2s_valid prog input img S hκ hS hSx
      word0_eq := by rw [imageOf_padWitness]; exact hw0
      word1_eq := by rw [imageOf_padWitness]; exact hw1 }

end LeanerVM.Arithmetization
