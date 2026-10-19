/-
  LeanerVM.Protocol.LeanIsa.Complete

  The adaptor's completeness direction: a witness satisfying leanISA's constraint system stacks
  into a column satisfying the leanISA instance's relation, and is read back off it.
-/

module

public import LeanerVM.Protocol.LeanIsa.Sound
public import LeanerVM.Protocol.ToArkLib.Refinement

/-!
# The adaptor, completeness

`m3Holds_stackOf`: a witness `w` satisfying `SatisfiedBy prog input w` stacks, at the sizes it
carries (`Sizes.ofWitness`, which `sizes_of_satisfiedBy` shows it has), into a column satisfying
`M3Holds` of the leanISA instance. `witnessOf_stackOf`: reading a witness back off that stack
gives `w`'s opcode tables within their widths, its two blocks, its public input and its image.

The stack agrees with the witness (`agrees_stackOf`): its committed columns are the witness's
cells (`column_stackOf`), and its limb columns are the cells the honest Flock column carries at
the specification's slots (`column_limb_stackOf`), which are the witness's limbs by
`FlockSpec.slots_gen`, since every `BLAKE2S` row compresses (`limbsCompress_of_satisfiedBy`).
Then the constraint, bus and count clauses follow from the equivalences of
`LeanIsa/Relation.lean`; the public lines from the two public words of the image
(`image_words`), which the seed rows put in the memory columns (`memLimb_stackOf`); and the Flock
clause from `FlockSpec.holds_gen`, the region being the honest column of the limbs
(`flockColumn_stackOf`).

`leanIsaRefinement` packages the soundness direction as the spine's `Refinement` from `M3Rel` to
`SatisfiedBy`, the witness map the knowledge transport needs.

A witness's rows may carry cells past their component's width, which no constraint reads and
the stack drops: the read-back is cell for cell within the width.
-/

namespace LeanerVM.Protocol.LeanIsa

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization CompPoly CMlPolynomialEval
open Air.Flat (Component EnsembleWitness)

@[expose] public section

variable (F : FlockSpec) (prog : Program) (s : Sizes) (w : EnsembleWitness (leanIsaEnsemble prog))

/-! ## Reading the stack of a witness -/

/-- A cell of a stack inside a block's window is the block's cell. -/
private theorem stackColumn_get (t : (blocks prog s).Tables K) (b : Fin (blocks prog s).n)
    (x : Fin (2 ^ (blocks prog s).size b)) :
    ((blocks prog s).stackColumn t (leanIsaμ prog s)).values[x.val + (blocks prog s).offset b]'(by
      have := (blocks prog s).offset_add_pow_le_total b
      have := blocks_fits prog s
      have := x.isLt
      omega) = (t b)[x] := by
  rw [← (blocks prog s).unstack_getElem (blocks_fits prog s) _ b x.isLt]
  exact congrArg (·[x]) ((blocks prog s).unstack_stackAt t (blocks_fits prog s) 0 b)

/-- A witness's column, transported along an equality of columns. -/
private theorem witnessColumn_congr {c c' : Col} (h : c' = c) (x : Fin (2 ^ kappa prog s c')) :
    (witnessColumn F prog s w c')[x] =
      (witnessColumn F prog s w c)[(Fin.cast (by rw [h]) x : Fin (2 ^ kappa prog s c))] := by
  subst h
  rfl

/-- A committed column of the stack of a witness is the witness's column. -/
theorem column_stackOf (c : Col) (h : ¬ IsLimb c) (x : Fin (2 ^ kappa prog s c)) :
    ((leanIsaInstance F prog s).column (stackOf F prog s w) c).values.get x =
      (witnessColumn F prog s w c)[x] := by
  refine (column_committed F prog s _ c h x).trans ?_
  have hsz := size_blockOf prog s c h
  have hx : x.val < 2 ^ (blocks prog s).size (blockOf c h) := by rw [hsz]; exact x.isLt
  refine (stackColumn_get prog s _ (blockOf c h) ⟨x.val, hx⟩).trans ?_
  exact witnessColumn_congr F prog s w (stackOrder_blockOf prog s c h) _

/-- Limb `k` of row `x` of the stack of a witness is the limb the honest Flock column carries at
slot `k` of block `x`. -/
theorem column_limb_stackOf (k : Fin 18) (x : Fin (2 ^ s.τ 5)) :
    ((leanIsaInstance F prog s).column (stackOf F prog s w) (limbCol k)).values.get x =
      slotLimbs F.slot (F.gen (blake2sLimbs prog s w)) x k :=
  (column_limb F prog s _ k x).trans
    ((column_committed F prog s _ flockCol not_isLimb_flockCol (cubeIndex (F.slot k) x)).symm.trans
      (column_stackOf F prog s w flockCol not_isLimb_flockCol (cubeIndex (F.slot k) x)))

/-- A raw `BLAKE2S` row is a compression exactly when its limbs, cells `9 … 26`, are. -/
private theorem blake2sRelation_array (row : Array K) (data : ProverData K) :
    Blake2sRelation (valueFromOffset Blake2sRow 0 (Environment.fromArray row data)) ↔
      LimbsCompress fun k ↦ row[9 + (k : ℕ)]?.getD 0 := by
  unfold Blake2sRelation LimbsCompress
  simp [valueFromOffset, explicit_provable_type, circuit_norm]

/-! ## Rows of the two blocks -/

/-- The cells of a memory-block row: the finalize count at `1`, the limbs at `2, 3, 4`. -/
private theorem memRow_cells (idx cnt : K) (m : Vector K 3) :
    (toElements (⟨idx, cnt, m⟩ : MemRow K)).toArray[1]?.getD 0 = cnt ∧
    (toElements (⟨idx, cnt, m⟩ : MemRow K)).toArray[2]?.getD 0 = m[0] ∧
    (toElements (⟨idx, cnt, m⟩ : MemRow K)).toArray[3]?.getD 0 = m[1] ∧
    (toElements (⟨idx, cnt, m⟩ : MemRow K)).toArray[4]?.getD 0 = m[2] := by
  simp [explicit_provable_type, ProvableStruct.componentsToElements, ProvableStruct.toComponents,
    toComponents, circuit_norm]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [Vector.getElem_append] <;> simp <;>
    rw [Vector.getElem_append] <;> simp

/-- Cell `memRowCell k` of a memory-block row is its column `k`: a limb, or the finalize count. -/
private theorem memRow_cell (idx cnt : K) (m : Vector K 3) (k : Fin 4) :
    (toElements (⟨idx, cnt, m⟩ : MemRow K)).toArray[memRowCell k]?.getD 0 =
      ![m[0], m[1], m[2], cnt] k := by
  obtain ⟨c1, c2, c3, c4⟩ := memRow_cells idx cnt m
  fin_cases k
  exacts [c2, c3, c4, c1]

/-- The finalize count of a bytecode-block row is its cell `1`. -/
private theorem bytecodeRow_cell (i : Fin (2 ^ prog.logSize)) (c : K) :
    (toElements (bytecodeRowOf prog i c)).toArray[1]?.getD 0 = c := by
  simp [bytecodeRowOf, explicit_provable_type, ProvableStruct.componentsToElements,
    ProvableStruct.toComponents, toComponents, circuit_norm]
  rw [Vector.getElem_append]
  simp
  rw [Vector.getElem_append]
  simp

/-! ## The sizes of a witness -/

variable {F prog s w}

/-- The sizes a witness carries: its memory size and its tables' log-heights. -/
def witnessSizes (w : EnsembleWitness (leanIsaEnsemble prog)) (h : 0 < (imageOf w.data).1) :
    Sizes :=
  ⟨(imageOf w.data).1, h, fun j ↦ Nat.log 2 (opTable w j).table.length⟩

/-- `Sizes.ofWitness` returns the sizes the witness carries. -/
theorem eq_of_ofWitness (hs : Sizes.ofWitness w = some s) :
    ∃ h, s = witnessSizes w h := by
  unfold Sizes.ofWitness at hs
  split_ifs at hs with h
  exact ⟨h, (Option.some.inj hs).symm⟩

/-- A witness satisfying the constraint system has its sizes. -/
theorem sizes_of_satisfiedBy {input : PublicInput} (h : SatisfiedBy prog input w) :
    ∃ s, Sizes.ofWitness w = some s := by
  unfold Sizes.ofWitness
  have hp : 0 < (imageOf w.data).1 := lt_of_lt_of_le (by decide) h.caps.minLogMem_le
  simp only [hp, dite_true]
  exact ⟨_, rfl⟩

/-- An opcode table of a witness within the caps has `2 ^ τ` rows at its log-height `τ`. -/
private theorem opTable_length {input : PublicInput} (h : SatisfiedBy prog input w) (j : Fin 6) :
    (opTable w j).table.length = 2 ^ Nat.log 2 (opTable w j).table.length := by
  have hmem : opTable w j ∈ w.tables :=
    mem_tables_iff.mpr ⟨⟨j, by omega⟩, rfl⟩
  obtain ⟨τ, -, hτ⟩ := h.caps.heights _ hmem
  rw [hτ, Nat.log_pow (by norm_num)]

/-! ## The stack of a witness agrees with it -/

/-- A cell of a table, as a row's cell. -/
private theorem cellOf_eq (t : Air.Flat.Table K) {x : ℕ} (hx : x < t.table.length) (i : ℕ) :
    cellOf t x i = (t.table[x]'hx)[i]?.getD 0 := by
  rw [cellOf, List.getElem?_eq_getElem hx]
  rfl

/-- Every `BLAKE2S` row of a witness satisfying the constraint system has compressing limbs. -/
theorem limbsCompress_of_satisfiedBy {input : PublicInput} (h : SatisfiedBy prog input w)
    (hs : Sizes.ofWitness w = some s) (x : Fin (2 ^ s.τ 5)) :
    LimbsCompress (blake2sLimbs prog s w)[x] := by
  obtain ⟨hp, rfl⟩ := eq_of_ofWitness hs
  have hx : x.val < (tableAt w 5).table.length :=
    lt_of_lt_of_eq x.isLt (opTable_length h 5).symm
  have hv := h.blake2s_valid _ (List.getElem_mem hx)
  rw [blake2sRowAt, blake2sRelation_array] at hv
  have hl : (blake2sLimbs prog _ w)[x] = fun k : Fin 18 ↦ cellOf (tableAt w 5) x (9 + k) :=
    Vector.getElem_ofFn _
  rw [hl]
  simp only [cellOf_eq _ hx]
  exact hv

/-- Within its width, an opcode table of a witness satisfying the constraint system is the
stack's rows. -/
private theorem cells_stackOf {input : PublicInput} (h : SatisfiedBy prog input w)
    (hp : 0 < (imageOf w.data).1) (j : Fin 6) (x : Fin (2 ^ (witnessSizes w hp).τ j))
    (i : Fin (opcodeComponent j).width) :
    cellOf (opTable w j) x i =
      (leanIsaInstance F prog (witnessSizes w hp)).row
        (stackOf F prog (witnessSizes w hp) w) (opIdx j) x i := by
  have hs : Sizes.ofWitness w = some (witnessSizes w hp) := by
    unfold Sizes.ofWitness
    simp only [hp, dite_true]
    rfl
  have hLC := limbsCompress_of_satisfiedBy h hs
  have hx : x.val < (opTable w j).table.length :=
    lt_of_lt_of_eq x.isLt (opTable_length h j).symm
  by_cases hl : IsLimb ⟨opIdx j, i⟩
  · have hj : j = 5 := Fin.ext (by have := congrArg Fin.val hl.1; simp [opIdx] at this; omega)
    subst hj
    have h1 : 9 ≤ i.val := hl.2.1
    have h2 : i.val < 27 := hl.2.2
    have hk : i.val - 9 < 18 := by omega
    have hi : i = ⟨9 + (i.val - 9), by rw [Nat.add_sub_cancel' h1]; exact i.isLt⟩ :=
      Fin.ext (by simp only; omega)
    rw [hi]
    refine Eq.symm ((column_limb_stackOf F prog _ w ⟨i.val - 9, hk⟩ x).trans ?_)
    rw [F.slots_gen _ x (hLC x)]
    have hl' : (blake2sLimbs prog _ w)[x] = fun k : Fin 18 ↦ cellOf (tableAt w 5) x (9 + k) :=
      Vector.getElem_ofFn _
    rw [hl']
    rfl
  · refine Eq.symm ((column_stackOf F prog _ w ⟨opIdx j, i⟩ hl x).trans ?_)
    exact Vector.getElem_ofFn _

/-- The memory block of a witness satisfying the constraint system is the stack's. -/
private theorem memRows_stackOf {input : PublicInput} (h : SatisfiedBy prog input w)
    (hp : 0 < (imageOf w.data).1) :
    memBlockRows w = memBlockRowsOf F prog (witnessSizes w hp)
      (stackOf F prog (witnessSizes w hp) w) := by
  obtain ⟨idx, cnt, hrows⟩ := h.seed_rows
  have hlen : (memBlockRows w).length = 2 ^ (imageOf w.data).1 := by
    rw [hrows, List.length_ofFn]
  have hrow : ∀ x : Fin (2 ^ (imageOf w.data).1),
      (memBlockRows w)[x.val]'(by rw [hlen]; exact x.isLt) =
        (toElements (⟨idx x, cnt x, #v[((imageOf w.data).2 x).limb 0,
          ((imageOf w.data).2 x).limb 1, ((imageOf w.data).2 x).limb 2]⟩ : MemRow K)).toArray :=
    fun x ↦ by simp only [hrows, List.getElem_ofFn]
  have hidx : ∀ x : Fin (2 ^ (imageOf w.data).1), idx x = gpow x := fun x ↦ by
    have := h.index_columns x.val (by rw [hlen]; exact x.isLt)
    rw [hrow, memRowAt_toElements] at this
    exact this
  have hcell : ∀ (k : Fin 4) (x : Fin (2 ^ (imageOf w.data).1)),
      cell F prog (witnessSizes w hp) (stackOf F prog (witnessSizes w hp) w) (memCol k) x =
        ((memBlockRows w)[x.val]'(by rw [hlen]; exact x.isLt))[memRowCell k]?.getD 0 :=
    fun k x ↦ (column_stackOf F prog (witnessSizes w hp) w (memCol k) (fun hk ↦ by
      have := congrArg Fin.val hk.1; simp [memCol, opIdx] at this) x).trans
        ((Vector.getElem_ofFn _).trans (cellOf_eq _ _ _))
  rw [hrows, memBlockRowsOf]
  refine congrArg List.ofFn (funext fun x ↦ ?_)
  simp only [hcell, hrow x, hidx x, memRow_cell]
  rfl

/-- The bytecode block of a witness satisfying the constraint system is the stack's. -/
private theorem bytecodeRows_stackOf {input : PublicInput} (h : SatisfiedBy prog input w)
    (hp : 0 < (imageOf w.data).1) :
    bytecodeBlockRows w = bytecodeBlockRowsOf F prog (witnessSizes w hp)
      (stackOf F prog (witnessSizes w hp) w) := by
  obtain ⟨cntFin, hrows⟩ := h.bytecode_rows
  have hlen : (bytecodeBlockRows w).length = 2 ^ prog.logSize := by
    rw [hrows, List.length_ofFn]
  have hrow : ∀ i : Fin (2 ^ prog.logSize),
      (bytecodeBlockRows w)[i.val]'(by rw [hlen]; exact i.isLt) =
        (toElements (bytecodeRowOf prog i (cntFin i))).toArray :=
    fun i ↦ by simp only [hrows, List.getElem_ofFn]
  have hcell : ∀ i : Fin (2 ^ prog.logSize),
      cell F prog (witnessSizes w hp) (stackOf F prog (witnessSizes w hp) w) bfcntCol i =
        ((bytecodeBlockRows w)[i.val]'(by rw [hlen]; exact i.isLt))[1]?.getD 0 :=
    fun i ↦ (column_stackOf F prog (witnessSizes w hp) w bfcntCol (by decide) i).trans
      ((Vector.getElem_ofFn _).trans (cellOf_eq _ _ _))
  rw [hrows, bytecodeBlockRowsOf]
  refine congrArg List.ofFn (funext fun i ↦ ?_)
  simp only [hcell, hrow i, bytecodeRow_cell]

/-- The stack of a witness satisfying the constraint system agrees with it. -/
theorem agrees_stackOf {input : PublicInput} (h : SatisfiedBy prog input w)
    (hs : Sizes.ofWitness w = some s) : Agrees F s (stackOf F prog s w) w := by
  obtain ⟨hp, rfl⟩ := eq_of_ofWitness hs
  exact ⟨fun j ↦ opTable_length h j, cells_stackOf h hp, memRows_stackOf h hp,
    bytecodeRows_stackOf h hp⟩

/-! ## The relation of the stack -/

/-- A limb column of the memory on the stack of a witness satisfying the constraint system is
that limb of the image the data names. -/
private theorem memLimb_stackOf {input : PublicInput} (h : SatisfiedBy prog input w)
    (hp : 0 < (imageOf w.data).1) (k : Fin 3) (x : Fin (2 ^ (imageOf w.data).1)) :
    cell F prog (witnessSizes w hp) (stackOf F prog (witnessSizes w hp) w) (memCol k.castSucc) x =
      ((imageOf w.data).2 x).limb k := by
  obtain ⟨idx, cnt, hrows⟩ := h.seed_rows
  have hlen : (memBlockRows w).length = 2 ^ (imageOf w.data).1 := by
    rw [hrows, List.length_ofFn]
  refine (column_stackOf F prog (witnessSizes w hp) w (memCol k.castSucc) (fun hk ↦ by
    have := congrArg Fin.val hk.1; simp [memCol, opIdx] at this) x).trans
      ((Vector.getElem_ofFn _).trans ((cellOf_eq _ (by rw [hlen]; exact x.isLt) _).trans ?_))
  have hrow : (memBlockRows w)[x.val]'(by rw [hlen]; exact x.isLt) =
      (toElements (⟨idx x, cnt x, #v[((imageOf w.data).2 x).limb 0,
        ((imageOf w.data).2 x).limb 1, ((imageOf w.data).2 x).limb 2]⟩ : MemRow K)).toArray := by
    simp only [hrows, List.getElem_ofFn]
  simp only [hrow, memRow_cell]
  fin_cases k <;> rfl

/-- The image a witness satisfying the constraint system names holds the public words at
`g^0` and `g^1`. -/
private theorem image_words {input : PublicInput} (h : SatisfiedBy prog input w)
    (h0 : 0 < 2 ^ (imageOf w.data).1) (h1 : 1 < 2 ^ (imageOf w.data).1) :
    (imageOf w.data).2 ⟨0, h0⟩ = input.word0 ∧ (imageOf w.data).2 ⟨1, h1⟩ = input.word1 := by
  have hκ : (imageOf w.data).1 < 64 := lt_of_le_of_lt h.caps.le_maxLogMem (by decide)
  have e0 := (MemImage.read_gpow hκ (imageOf w.data).2 ⟨0, h0⟩).symm.trans h.word0_eq
  have e1 := (MemImage.read_gpow hκ (imageOf w.data).2 ⟨1, h1⟩).symm.trans h.word1_eq
  exact ⟨Option.some.inj e0, Option.some.inj e1⟩

/-- The Flock region of the stack of a witness is the honest column of its `BLAKE2S` limbs. -/
private theorem flockColumn_stackOf :
    (leanIsaInstance F prog s).flockColumn (flockRegion prog s F) (stackOf F prog s w) =
      F.gen (blake2sLimbs prog s w) := by
  suffices hv : ((leanIsaInstance F prog s).flockColumn (flockRegion prog s F)
      (stackOf F prog s w)).values = (F.gen (blake2sLimbs prog s w)).values by
    revert hv
    generalize F.gen (blake2sLimbs prog s w) = c
    intro hv
    cases c
    exact congrArg Column.mk hv
  refine Vector.ext fun y hy ↦ ?_
  simp only [M3Instance.flockColumn, Vector.getElem_cast]
  exact column_stackOf F prog s w flockCol not_isLimb_flockCol ⟨y, hy⟩

/-- The stack of a witness satisfying the constraint system holds the public lines: its memory
columns' first two cells are the public words' limbs. -/
private theorem publicLinesHold_stackOf {input : PublicInput} (h : SatisfiedBy prog input w)
    (hs : Sizes.ofWitness w = some s) :
    (leanIsaInstance F prog s).PublicLinesHold input (stackOf F prog s w) := by
  obtain ⟨hp, rfl⟩ := eq_of_ofWitness hs
  have h0 : 0 < 2 ^ (imageOf w.data).1 := Nat.two_pow_pos _
  have h1 : 1 < 2 ^ (imageOf w.data).1 := Nat.one_lt_two_pow hp.ne'
  obtain ⟨w0, w1⟩ := image_words h h0 h1
  have hl : ∀ k : Fin 3,
      cell F prog (witnessSizes w hp) (stackOf F prog (witnessSizes w hp) w) (memCol k.castSucc)
        ⟨0, h0⟩ = input.word0.limb k ∧
      cell F prog (witnessSizes w hp) (stackOf F prog (witnessSizes w hp) w) (memCol k.castSucc)
        ⟨1, h1⟩ = input.word1.limb k := fun k ↦
    ⟨(memLimb_stackOf h hp k _).trans (congrArg (·.limb k) w0),
      (memLimb_stackOf h hp k _).trans (congrArg (·.limb k) w1)⟩
  intro l hl'
  have hls : (publicLines prog (witnessSizes w hp) input).toList =
      [⟨memCol 0, input.lanes 0, input.lanes 2, true, hp⟩,
        ⟨memCol 1, input.lanes 1, input.lanes 3, true, hp⟩, ⟨memCol 2, 0, 0, false, hp⟩] := rfl
  change l ∈ (publicLines prog (witnessSizes w hp) input).toList at hl'
  rw [hls] at hl'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl'
  rcases hl' with rfl | rfl | rfl
  · exact ⟨(hl 0).1.trans (by simp [PublicInput.word0]),
      (hl 0).2.trans (by simp [PublicInput.word1])⟩
  · exact ⟨(hl 1).1.trans (by simp [PublicInput.word0]),
      (hl 1).2.trans (by simp [PublicInput.word1])⟩
  · exact ⟨(hl 2).1.trans (by simp [PublicInput.word0]),
      (hl 2).2.trans (by simp [PublicInput.word1])⟩

/-- **The adaptor, completeness.** A witness satisfying leanISA's constraint system on the input
stacks, at the sizes it carries, into a column satisfying the leanISA instance's relation. -/
theorem m3Holds_stackOf {input : PublicInput} (h : SatisfiedBy prog input w)
    (hs : Sizes.ofWitness w = some s) :
    M3Holds (leanIsaInstance F prog s) input (stackOf F prog s w) := by
  have hA := agrees_stackOf (F := F) h hs
  refine ⟨?_, (balanced_iff_pairs hA).mpr fun k ↦ ?_, (countsNonzero_iff hA).mp h.counts_nonzero,
    ?_, ?_⟩
  · intro j' C hC x
    rcases j' with ⟨_ | _ | _ | j, hj⟩
    · exact absurd hC List.not_mem_nil
    · exact absurd hC List.not_mem_nil
    · exact absurd hC List.not_mem_nil
    · have h9 : (leanIsaInstance F prog s).ntab = 9 := rfl
      have hmem : opTable w ⟨j, by omega⟩ ∈ w.allTables :=
        EnsembleWitness.mem_allTables_of_mem_tables _ (mem_tables_iff.mpr ⟨⟨j, by omega⟩, rfl⟩)
      exact (opcode_constraints_iff hA ⟨j, by omega⟩).mp (h.constraints _ hmem) x C hC
  · fin_cases k
    exacts [h.state_balanced, h.mem_balanced, h.bytecode_balanced]
  · exact publicLinesHold_stackOf h hs
  · intro r hr
    obtain rfl := Option.mem_def.mp hr |> Option.some.inj |>.symm
    rw [flockColumn_stackOf]
    exact F.region_holds_gen _ rfl rfl _

/-- **The witness read back.** Reading a witness back off the stack of a witness satisfying the
constraint system gives the witness's opcode tables within their widths, its memory and bytecode
blocks, its public input and the image its data names. -/
theorem witnessOf_stackOf {input : PublicInput} (h : SatisfiedBy prog input w)
    (hs : Sizes.ofWitness w = some s) :
    (∀ (j : Fin 6) (x : Fin (2 ^ s.τ j)) (i : Fin (opcodeComponent j).width),
      cellOf (opTable (witnessOf F prog s (stackOf F prog s w)) j) x i = cellOf (opTable w j) x i) ∧
    memBlockRows (witnessOf F prog s (stackOf F prog s w)) = memBlockRows w ∧
    bytecodeBlockRows (witnessOf F prog s (stackOf F prog s w)) = bytecodeBlockRows w ∧
    (witnessOf F prog s (stackOf F prog s w)).publicInput = w.publicInput ∧
    imageOf (witnessOf F prog s (stackOf F prog s w)).data = imageOf w.data := by
  have hA := agrees_stackOf (F := F) h hs
  have hB := agrees_witnessOf F prog s (stackOf F prog s w)
  refine ⟨fun j x i ↦ (hB.cells j x i).trans (hA.cells j x i).symm,
    hB.memRows.trans hA.memRows.symm, hB.bytecodeRows.trans hA.bytecodeRows.symm, ?_, ?_⟩
  · obtain ⟨c00, c01, c10, c11, -, -⟩ := publicLines_cells F prog s _ (publicLinesHold_stackOf h hs)
    show publicInputOf F prog s (stackOf F prog s w) = _
    rw [h.public_input_eq, publicInputOf, PublicIO.ofInput, c00, c01, c10, c11]
  · obtain ⟨hp, rfl⟩ := eq_of_ofWitness hs
    rw [imageOf_witnessOf F prog _ _ h.caps.le_maxLogMem]
    refine image_sigma_eq rfl _ _ fun x ↦ ?_
    exact (congr (congr (congrArg E.ofLimbs (memLimb_stackOf h hp 0 x))
      (memLimb_stackOf h hp 1 x)) (memLimb_stackOf h hp 2 x)).trans (ofLimbs_limb _)

/-! ## The refinement -/

/-- `SatisfiedBy` as a relation on the protocol's statements: the public input, no oracle. -/
def satisfiedByRel (prog : Program) :
    Set ((PublicInput × ∀ i, NoOracle i) × EnsembleWitness (leanIsaEnsemble prog)) :=
  {p | SatisfiedBy prog p.1.1 p.2}

/-- The adaptor as a refinement: on admissible sizes, reading the witness off the stack maps the
protocol's relation into leanISA's. -/
def leanIsaRefinement (F : FlockSpec) (prog : Program) (s : Sizes) (hs : s.Admissible prog) :
    Refinement (M3Rel (leanIsaInstance F prog s)) (satisfiedByRel prog) where
  map _ q := witnessOf F prog s q
  map_valid _ q h := satisfiedBy_witnessOf F prog s q hs h

end

end LeanerVM.Protocol.LeanIsa
