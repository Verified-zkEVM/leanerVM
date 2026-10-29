/-
  LeanerVM.Arithmetization.Completeness.Witness

  The witness of a padded execution: the eight tables, the prover data they derive, and the image
  it names.
-/

module

public import LeanerVM.Arithmetization.Completeness.Bus

@[expose] public section

/-!
# The witness of a padded execution

leanISA roadmap Layer 10 (`docs/roadmap/leanisa-blueprint.md`), at Clean pin `9dd71e82`.
Category A. Given the program, the public input, the image `img` and a list of skeletons `S`
(the states stepped from and the instructions fetched there: the run and the fill),
`padWitness prog input img S hκ hS` is Clean's `EnsembleWitness` of `leanIsaEnsemble prog κ`,
built from the eight tables `padTables` by `witnessOfTables`:

* the six opcode tables hold the rows of the skeletons of their opcode (`opTable`): `padRows img
  S` are the rows of `S` with their counts, threaded through `S` (`Completeness.Bus`), and a table
  holds those whose instruction has its opcode;
* the memory block holds one row per cell, `(g^i, g^(finalizes of i), the word at i)`, and the
  bytecode block one row per slot of the program, with the finalize counts the reads leave; both
  agree with their components' fixed columns (`memRowsOf_fixed`, `bcRowsOf_fixed`).

The prover data is not chosen: Clean derives it from the tables, and its `"mem"` table is the
memory block's rows (`memRows_padWitness`), so the image it names is `img` within the cap
(`imageOf_padWitness`). The two hypotheses of `padWitness` are what Clean's tables need: the
memory log-size within the cap (`hκ`, the block's height `2^κ` is a `u64`) and at most `2^64`
skeletons (`hS`, every table's row indices are `u64` values).

The witness is never evaluated: the memory block has `2^κ` rows, and every statement about it is
about its rows generically, through `getElem?` and equation lemmas (status finding E8).

## Wrong readings excluded

* The tables are filtered from one list of rows, not built one at a time: the numbers of a cell's
  reads run across all six tables, so that the memory channel balances (`Completeness.Balance`).
* The memory block's finalize count of a cell is `g` to the number of reads of it, never the
  number: `cntFin = g^(readBump …)`, the count a read of the cell would carry next.
* The prover data is not an input of the witness: it is derived from the memory block's rows,
  and the program is in no table of it (the bytecode block's entries are fixed columns).
-/

namespace LeanerVM.Arithmetization

open LeanerVM.Parameters LeanerVM.Semantics
open Air.Flat (Component EnsembleWitness)

/-! ## The rows of a list of skeletons -/

/-- The rows of a list of skeletons over the image `img`, numbered from zero. -/
noncomputable def padRows {κ : ℕ} (img : MemImage κ) (S : List Skel) : List PRow :=
  mkRows img (fun _ ↦ 0) (fun _ ↦ 0) S

/-- How many times each memory cell is read by the rows of `S`: the exponent of its finalize
count. -/
noncomputable def padMemFin {κ : ℕ} (img : MemImage κ) (S : List Skel) : K → ℕ :=
  readBump (fun _ ↦ 0) (S.flatMap fun sk ↦ readAddrs img sk.fp sk.ins)

/-- How many times each bytecode slot is read by the rows of `S`. -/
noncomputable def padBcFin (S : List Skel) : K → ℕ :=
  readBump (fun _ ↦ 0) (S.map (·.pc))

/-- A row of the rows of `S` is a row of a skeleton of `S`. -/
theorem mem_mkRows_sk {κ : ℕ} {img : MemImage κ} {sm sb : K → ℕ} {S : List Skel} {r : PRow}
    (h : r ∈ mkRows img sm sb S) : r.sk ∈ S := by
  rw [← mkRows_sk img sm sb S]
  exact List.mem_map_of_mem h

/-- There is a row per skeleton. -/
theorem padRows_length {κ : ℕ} (img : MemImage κ) (S : List Skel) :
    (padRows img S).length = S.length := by
  conv_rhs => rw [← mkRows_sk img (fun _ ↦ 0) (fun _ ↦ 0) S]
  rw [List.length_map]
  rfl

/-! ## Proof helpers -/

/-- An eight-coordinate entry is its opcode followed by its seven operand slots. -/
private theorem cons_append_ops (e : Vector K 8) :
    #v[e[0]] ++ #v[e[1], e[2], e[3], e[4], e[5], e[6], e[7]] = e := by
  ext j hj
  interval_cases j <;> rfl

/-- A typed row written as a raw row reads back from its prefix of the row type's width. -/
private theorem fromElements_rowPrefix_rawRow {Row : TypeMap} [ProvableType Row] (r : Row K) :
    fromElements (Air.Flat.rowPrefix (size Row) (rawRow r)) = r := by
  rw [← Air.Flat.valueFromOffset_fromArray (Input := Row) (rawRow r) (fun _ _ ↦ #[])]
  exact rowAt_toElements _ r

/-! ## The tables -/

/-- The rows of the table of an opcode: the raw rows of the rows of `R` whose instruction has the
opcode. -/
noncomputable def opRows {κ : ℕ} (img : MemImage κ) (R : List PRow) (op : Opcode) :
    List (Array K) :=
  (R.filter fun r ↦ r.sk.ins.opcode = op).map (PRow.raw img)

/-- The rows of an opcode's table have its width. -/
theorem opRows_width {κ : ℕ} (img : MemImage κ) (R : List PRow) (op : Opcode) :
    ∀ row ∈ opRows img R op, row.size = (opComponent op).width := by
  intro row hrow
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hrow
  have h := (List.mem_filter.mp hr).2
  simp only [decide_eq_true_eq] at h
  rw [opComponent_width, PRow.raw, rowOf_size, h]

/-- An opcode's table has at most as many rows as `R`. -/
theorem opRows_length_le {κ : ℕ} (img : MemImage κ) (R : List PRow) (op : Opcode) :
    (opRows img R op).length ≤ R.length := by
  rw [opRows, List.length_map]
  exact List.length_filter_le _ _

/-- The table of an opcode: the raw rows of the rows of `R` whose instruction has the opcode, a
demand component with no fixed cell. -/
noncomputable def opTable {κ : ℕ} (img : MemImage κ) (R : List PRow)
    (hR : R.length ≤ UInt64.size) (op : Opcode) : Air.Flat.Table K :=
  tableOf (opComponent op) (opRows img R op) (opRows_width img R op)
    ((opRows_length_le img R op).trans hR) (by cases op <;> exact trivial)

/-- The rows of the memory block: one per cell, `(g^i, g^(fin (g^i)), the word at i)`. -/
noncomputable def memRowsOf {κ : ℕ} (img : MemImage κ) (fin : K → ℕ) : List (Array K) :=
  List.ofFn fun i : Fin (2 ^ κ) ↦ rawRow (memRowOf img i (g ^ fin (gpow i)))

/-- The memory block has `2^κ` rows. -/
theorem memRowsOf_length {κ : ℕ} (img : MemImage κ) (fin : K → ℕ) :
    (memRowsOf img fin).length = 2 ^ κ :=
  List.length_ofFn

/-- The memory block's rows have its width. -/
theorem memRowsOf_width {κ : ℕ} (img : MemImage κ) (fin : K → ℕ) :
    ∀ row ∈ memRowsOf img fin, row.size = (memComponent κ).width := by
  intro row hrow
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrow
  exact rawRow_size _

/-- The memory block agrees with the fixed address column. -/
theorem memRowsOf_fixed {κ : ℕ} (hκ : κ ≤ maxLogMem) (img : MemImage κ) (fin : K → ℕ) :
    (memComponent κ).FixedRowsMatch (memRowsOf img fin) := by
  have hκ64 : κ < 64 := lt_of_le_of_lt hκ (by decide)
  have h64 : 2 ^ κ < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) hκ64
  refine ⟨?_, fun i hi ↦ ?_⟩
  · show (memRowsOf img fin).length = (UInt64.ofNat (2 ^ κ)).toNat
    rw [memRowsOf_length, UInt64.toNat_ofNat_of_lt' h64]
  · have hi' : i < 2 ^ κ := memRowsOf_length img fin ▸ hi
    show (memMode κ).FixedAt (UInt64.ofNat i)
      (fromElements (Air.Flat.rowPrefix (size MemRow) (memRowsOf img fin)[i]))
    rw [memMode_fixedAt_iff hi' hκ64]
    simp only [memRowsOf, List.getElem_ofFn, fromElements_rowPrefix_rawRow]
    rfl

/-- The memory block: `memComponent κ` with one row per cell. -/
noncomputable def memBlock {κ : ℕ} (hκ : κ ≤ maxLogMem) (img : MemImage κ) (fin : K → ℕ) :
    Air.Flat.Table K :=
  tableOf (memComponent κ) (memRowsOf img fin) (memRowsOf_width img fin)
    ((memRowsOf_length img fin).trans_le
      ((Nat.pow_le_pow_right (by norm_num) (hκ.trans (by decide) : κ ≤ 64)).trans (by decide)))
    (memRowsOf_fixed hκ img fin)

/-- The rows of the bytecode block: one per slot of the program. -/
noncomputable def bcRowsOf (prog : Program) (fin : K → ℕ) : List (Array K) :=
  List.ofFn fun i : Fin (2 ^ prog.logSize) ↦ rawRow (bytecodeRowOf prog i (g ^ fin (gpow i)))

/-- The bytecode block has `2^prog.logSize` rows. -/
theorem bcRowsOf_length (prog : Program) (fin : K → ℕ) :
    (bcRowsOf prog fin).length = 2 ^ prog.logSize :=
  List.length_ofFn

/-- The bytecode block's rows have its width. -/
theorem bcRowsOf_width (prog : Program) (fin : K → ℕ) :
    ∀ row ∈ bcRowsOf prog fin, row.size = (bytecodeComponent prog).width := by
  intro row hrow
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrow
  exact rawRow_size _

/-- The bytecode block agrees with the fixed counter and entry columns. -/
theorem bcRowsOf_fixed (prog : Program) (fin : K → ℕ) :
    (bytecodeComponent prog).FixedRowsMatch (bcRowsOf prog fin) := by
  have h64 : 2 ^ prog.logSize < 2 ^ 64 :=
    Nat.pow_lt_pow_right (by norm_num) (lt_of_le_of_lt prog.logSize_le (by decide))
  refine ⟨?_, fun i hi ↦ ?_⟩
  · show (bcRowsOf prog fin).length = (UInt64.ofNat (2 ^ prog.logSize)).toNat
    rw [bcRowsOf_length, UInt64.toNat_ofNat_of_lt' h64]
  · have hi' : i < 2 ^ prog.logSize := bcRowsOf_length prog fin ▸ hi
    show (bytecodeMode prog).FixedAt (UInt64.ofNat i)
      (fromElements (Air.Flat.rowPrefix (size BytecodeRow) (bcRowsOf prog fin)[i]))
    rw [bytecodeMode_fixedAt_iff prog hi']
    simp only [bcRowsOf, List.getElem_ofFn, fromElements_rowPrefix_rawRow]
    exact ⟨rfl, cons_append_ops _⟩

/-- The bytecode block: `bytecodeComponent prog` with one row per slot. -/
noncomputable def bcBlock (prog : Program) (fin : K → ℕ) : Air.Flat.Table K :=
  tableOf (bytecodeComponent prog) (bcRowsOf prog fin) (bcRowsOf_width prog fin)
    ((bcRowsOf_length prog fin).trans_le
      ((Nat.pow_le_pow_right (by norm_num)
        (prog.logSize_le.trans (by decide) : prog.logSize ≤ 64)).trans (by decide)))
    (bcRowsOf_fixed prog fin)

/-- The eight tables of a padded execution, in the ensemble's order. -/
noncomputable def padTables (prog : Program) {κ : ℕ} (img : MemImage κ) (S : List Skel)
    (hκ : κ ≤ maxLogMem) (hS : S.length ≤ UInt64.size) : List (Air.Flat.Table K) :=
  [opTable img (padRows img S) ((padRows_length img S).trans_le hS) .xor,
    opTable img (padRows img S) ((padRows_length img S).trans_le hS) .mulNative,
    opTable img (padRows img S) ((padRows_length img S).trans_le hS) .setConstant,
    opTable img (padRows img S) ((padRows_length img S).trans_le hS) .deref,
    opTable img (padRows img S) ((padRows_length img S).trans_le hS) .jump,
    opTable img (padRows img S) ((padRows_length img S).trans_le hS) .blake2s,
    memBlock hκ img (padMemFin img S), bcBlock prog (padBcFin S)]

/-- The components of `padTables` are the ensemble's. -/
theorem padTables_components (prog : Program) {κ : ℕ} (img : MemImage κ) (S : List Skel)
    (hκ : κ ≤ maxLogMem) (hS : S.length ≤ UInt64.size) :
    (padTables prog img S hκ hS).map (·.component) = (leanIsaEnsemble prog κ).tables := by
  unfold padTables opTable memBlock bcBlock tableOf
  rfl

/-- **The witness of a padded execution.** -/
noncomputable def padWitness (prog : Program) (input : PublicInput) {κ : ℕ} (img : MemImage κ)
    (S : List Skel) (hκ : κ ≤ maxLogMem) (hS : S.length ≤ UInt64.size) :
    EnsembleWitness (leanIsaEnsemble prog κ) :=
  witnessOfTables prog κ (PublicIO.ofInput input) (padTables prog img S hκ hS)
    (padTables_components prog img S hκ hS)

/-! ## The tables of the witness -/

section Tables

variable {prog : Program} {input : PublicInput} {κ : ℕ} {img : MemImage κ} {S : List Skel}
  {hκ : κ ≤ maxLogMem} {hS : S.length ≤ UInt64.size}

/-- The tables of the padded witness are `padTables`, up to their prover data. -/
theorem padWitness_map :
    (padWitness prog input img S hκ hS).tables.map (fun t ↦ (t.component, t.table)) =
      (padTables prog img S hκ hS).map fun t ↦ (t.component, t.table) := by
  unfold padWitness
  exact witnessOfTables_map

/-- A table of the padded witness is one of `padTables` with the witness's data. -/
theorem mem_padWitness_tables {t : Air.Flat.Table K}
    (ht : t ∈ (padWitness prog input img S hκ hS).tables) :
    ∃ t₀ ∈ padTables prog img S hκ hS, t₀.component = t.component ∧ t₀.table = t.table := by
  have h := List.mem_map_of_mem (f := fun t : Air.Flat.Table K ↦ (t.component, t.table)) ht
  rw [padWitness_map, List.mem_map] at h
  obtain ⟨t₀, h₀, he⟩ := h
  exact ⟨t₀, h₀, (Prod.ext_iff.mp he).1, (Prod.ext_iff.mp he).2⟩

/-- Each of `padTables` is, up to its data, a table of the padded witness. -/
theorem exists_padWitness_table {t₀ : Air.Flat.Table K} (h₀ : t₀ ∈ padTables prog img S hκ hS) :
    ∃ t ∈ (padWitness prog input img S hκ hS).tables,
      t.component = t₀.component ∧ t.table = t₀.table := by
  have h := List.mem_map_of_mem (f := fun t : Air.Flat.Table K ↦ (t.component, t.table)) h₀
  rw [← padWitness_map (input := input), List.mem_map] at h
  obtain ⟨t, ht, he⟩ := h
  exact ⟨t, ht, (Prod.ext_iff.mp he).1, (Prod.ext_iff.mp he).2⟩

/-- The table at a position of the padded witness is that of `padTables`, up to its data. -/
theorem padWitness_tableAt (j : Fin 8) :
    (tableAt (padWitness prog input img S hκ hS) j).component =
        ((padTables prog img S hκ hS)[(j : ℕ)]'(by exact j.isLt)).component ∧
      (tableAt (padWitness prog input img S hκ hS) j).table =
        ((padTables prog img S hκ hS)[(j : ℕ)]'(by exact j.isLt)).table := by
  have hl : (j : ℕ) < ((padWitness prog input img S hκ hS).tables.map
      fun t ↦ (t.component, t.table)).length := by
    rw [List.length_map, ← (padWitness prog input img S hκ hS).same_length]
    exact j.isLt
  have h := List.getElem_of_eq padWitness_map hl
  rw [List.getElem_map, List.getElem_map] at h
  exact Prod.mk.inj h

end Tables

/-! ## The prover data -/

section Data

variable {prog : Program} {input : PublicInput} {κ : ℕ} {img : MemImage κ} {S : List Skel}
  {hκ : κ ≤ maxLogMem} {hS : S.length ≤ UInt64.size}

/-- The `"mem"` table of the padded witness's data is the memory block's rows, as typed rows. -/
private theorem memRows_padWitness :
    memRows (padWitness prog input img S hκ hS).data =
      (((memRowsOf img (padMemFin img S)).map (Air.Flat.rowPrefix (size MemRow))).toArray.map
        (fromElements (M := MemRow))).map (·.m) := by
  rw [padWitness, witnessOfTables_data]
  have h := Air.Flat.deriveProverData_eq_of_mem (padTables prog img S hκ hS)
    (names_nodup (padTables_components prog img S hκ hS))
    (table := memBlock hκ img (padMemFin img S)) (by simp [padTables]) (size MemRow)
  unfold memRows ProverData.getRows
  exact congrArg (fun a ↦ (a.map fromElements).map (·.m)) h

/-- Row `k` of the `"mem"` table is the word at `k`, through `getElem?` (finding E8). -/
theorem memRows_padWitness_get (k : ℕ) (hk : k < 2 ^ κ) :
    (memRows (padWitness prog input img S hκ hS).data)[k]? =
      some #v[(img ⟨k, hk⟩).limb 0, (img ⟨k, hk⟩).limb 1, (img ⟨k, hk⟩).limb 2] := by
  rw [memRows_padWitness, Array.getElem?_map, Array.getElem?_map, List.getElem?_toArray,
    List.getElem?_map, memRowsOf, List.getElem?_ofFn]
  simp only [hk, ↓reduceDIte, Option.map_some, fromElements_rowPrefix_rawRow]
  rfl

/-- **The image the padded witness's data names is `img`**, as one equality of dependent pairs:
what every conjunct over `imageOf w.data` is rewritten with, so that nothing compares the data's
log-size against `κ` definitionally (finding E8). -/
theorem imageOf_padWitness :
    imageOf (padWitness prog input img S hκ hS).data = ⟨κ, img⟩ := by
  have hκ' : (imageOf (padWitness prog input img S hκ hS).data).1 = κ := imageOf_data_fst hκ
  have hpow : 2 ^ (imageOf (padWitness prog input img S hκ hS).data).1 = 2 ^ κ := by rw [hκ']
  have hf : ∀ i, (imageOf (padWitness prog input img S hκ hS).data).2 i =
      img (Fin.cast hpow i) := fun i ↦ by
    have hi : (i : ℕ) < 2 ^ κ := hpow ▸ i.isLt
    rw [imageOf_apply i (memRows_padWitness_get i hi)]
    show E.ofLimbs ((img ⟨i, hi⟩).limb 0) ((img ⟨i, hi⟩).limb 1) ((img ⟨i, hi⟩).limb 2) = _
    rw [ofLimbs_limb]
    rfl
  revert hκ' hpow hf
  generalize imageOf (padWitness prog input img S hκ hS).data = s
  obtain ⟨κ', img'⟩ := s
  intro hκ' hpow hf
  dsimp only at hκ' hpow hf
  subst hκ'
  exact congrArg _ (funext fun i ↦ (hf i).trans (congrArg img (Fin.ext rfl)))

end Data

end LeanerVM.Arithmetization
