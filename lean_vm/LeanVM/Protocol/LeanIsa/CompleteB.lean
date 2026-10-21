/-
  LeanVM.Protocol.LeanIsa.CompleteB

  The adaptor's completeness without Flock: a witness satisfying leanISA's constraint system
  without the compression stacks, with a Flock region that writes every row's limbs at their
  slots, into a column satisfying the leanISA relation without Flock, with honest padding, and is
  read back off it.
-/

module

public import LeanVM.Protocol.LeanIsa.Complete
public import LeanVM.Protocol.EndToEnd.Blind.Relation
public import LeanVM.Arithmetization.Soundness.Bus

/-!
# The adaptor without Flock, completeness

`LeanIsa/Complete.lean` for executions whose `BLAKE2S` rows are not compressions. The deployed
stack writes the Flock region with `F.gen`, which places each row's input limbs and runs the
BLAKE2s circuit: it carries a row's limbs at their slots only when the row compresses
(`FlockSpec.slots_gen`). Here the region is any generator `gen` carrying every row's limbs at
their slots (`SlotsOK F gen`, the unconditional `slots_gen°` of `docs/roadmap/t6-completeness.md`
L4); the Flock clause (`aux`) is dropped. `genFree` is one: the eighteen limbs at their slots,
zero elsewhere (`slotsOK_genFree`).

* `stackOfG gen prog s w`: the stack, the region `gen` of the witness's `BLAKE2S` limbs;
* `m3HonestBlind_stackOfG`: from `SatisfiedByB` (the constraint statement without the
  compression), the stack satisfies `M3HoldsBlind` and its padding is honest;
* `witnessOf_stackOfG`: the witness read back off it, its image the witness's.
-/

namespace LeanVM.Protocol.LeanIsa

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization CompPoly CMlPolynomialEval
open Air.Flat (Component EnsembleWitness)

@[expose] public section

/-! ## The stack with a generator -/

/-- **A generator carries every row's limbs at the slots of `F`.** -/
def SlotsOK (F : FlockSpec) (gen : ∀ {κ : ℕ}, Vector (Fin 18 → K) (2 ^ κ) → Column (8 + κ)) :
    Prop :=
  ∀ {κ : ℕ} (rows : Vector (Fin 18 → K) (2 ^ κ)) (t : Fin (2 ^ κ)),
    slotLimbs F.slot (gen rows) t = rows[t]

section Gen

variable (gen : ∀ {κ : ℕ}, Vector (Fin 18 → K) (2 ^ κ) → Column (8 + κ)) (F : FlockSpec)
  (prog : Program) (s : Sizes)

/-- The column `c` a witness carries, the Flock region `gen` of its `BLAKE2S` limbs
(`witnessColumn`). -/
def witnessColumnG (w : EnsembleWitness (leanIsaEnsemble prog)) :
    (c : Col) → Vector K (2 ^ kappa prog s c)
  | ⟨⟨0, _⟩, i⟩ => Vector.ofFn fun x ↦ cellOf (tableAt w 6) x (memRowCell i)
  | ⟨⟨1, _⟩, _⟩ => Vector.ofFn fun x ↦ cellOf (tableAt w 7) x 1
  | ⟨⟨2, _⟩, _⟩ => (gen (blake2sLimbs prog s w)).values
  | ⟨⟨j + 3, h⟩, i⟩ => Vector.ofFn fun x ↦ cellOf (tableAt w ⟨j, by omega⟩) x i

/-- The stack of a witness, the Flock region `gen` of its limbs (`stackOf`). -/
def stackOfG (w : EnsembleWitness (leanIsaEnsemble prog)) : Column (leanIsaμ prog s) :=
  (blocks prog s).stackColumn (fun b ↦ witnessColumnG gen prog s w (stackOrder prog s)[b])
    (leanIsaμ prog s)

end Gen

/-- The limb a slot of `slot` carries, `0` at a cell no limb has. -/
def limbAtSlot (slot : Fin 18 → Fin 256) (l : Fin 18 → K) (c : Fin 256) : K :=
  ((List.finRange 18).find? fun k ↦ decide (slot k = c)).elim 0 l

/-- **The free Flock region**: block `t` carries row `t`'s eighteen limbs at their slots and zero
elsewhere. -/
def genFree (slot : Fin 18 → Fin 256) {κ : ℕ} (rows : Vector (Fin 18 → K) (2 ^ κ)) :
    Column (8 + κ) :=
  ⟨Vector.ofFn fun u ↦ limbAtSlot slot rows[((cubeSplit 8 κ).symm u).2] ((cubeSplit 8 κ).symm u).1⟩

/-- A slot carries its limb, for injective slots. -/
theorem limbAtSlot_slot {slot : Fin 18 → Fin 256} (hinj : Function.Injective slot)
    (l : Fin 18 → K) (k : Fin 18) : limbAtSlot slot l (slot k) = l k := by
  unfold limbAtSlot
  cases hf : (List.finRange 18).find? (fun k' ↦ decide (slot k' = slot k)) with
  | none =>
    have := List.find?_eq_none.mp hf k (List.mem_finRange k)
    simp at this
  | some k' =>
    have hp := List.find?_some hf
    simp only [decide_eq_true_eq] at hp
    rw [hinj hp]
    rfl

/-- **The free region carries every row's limbs at the slots** (`slots_gen°`, unconditional). -/
theorem slotsOK_genFree (F : FlockSpec) (hinj : Function.Injective F.slot) :
    SlotsOK F (genFree F.slot) := by
  intro κ rows t
  funext k
  have h : (cubeSplit 8 κ).symm (cubeIndex (F.slot k) t) = (F.slot k, t) := by
    rw [← cubeSplit_apply, Equiv.symm_apply_apply]
  simp only [slotLimbs, blockCell, genFree, Fin.getElem_fin, Vector.getElem_ofFn, h]
  exact limbAtSlot_slot hinj _ k

/-! ## The adaptor -/

variable (F : FlockSpec) (gen : ∀ {κ : ℕ}, Vector (Fin 18 → K) (2 ^ κ) → Column (8 + κ))
  (prog : Program) (s : Sizes) (w : EnsembleWitness (leanIsaEnsemble prog))

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
private theorem witnessColumnG_congr {c c' : Col} (h : c' = c) (x : Fin (2 ^ kappa prog s c')) :
    (witnessColumnG gen prog s w c')[x] =
      (witnessColumnG gen prog s w c)[(Fin.cast (by rw [h]) x : Fin (2 ^ kappa prog s c))] := by
  subst h
  rfl

/-- A committed column of the stack of a witness is the witness's column. -/
theorem column_stackOfG (c : Col) (h : ¬ IsLimb c) (x : Fin (2 ^ kappa prog s c)) :
    ((leanIsaInstance F prog s).column (stackOfG gen prog s w) c).values.get x =
      (witnessColumnG gen prog s w c)[x] := by
  refine (column_committed F prog s _ c h x).trans ?_
  have hsz := size_blockOf prog s c h
  have hx : x.val < 2 ^ (blocks prog s).size (blockOf c h) := by rw [hsz]; exact x.isLt
  refine (stackColumn_get prog s _ (blockOf c h) ⟨x.val, hx⟩).trans ?_
  exact witnessColumnG_congr gen prog s w (stackOrder_blockOf prog s c h) _

/-- Limb `k` of row `x` of the stack of a witness is the limb the honest Flock column carries at
slot `k` of block `x`. -/
theorem column_limb_stackOfG (k : Fin 18) (x : Fin (2 ^ s.τ 5)) :
    ((leanIsaInstance F prog s).column (stackOfG gen prog s w) (limbCol k)).values.get x =
      slotLimbs F.slot (gen (blake2sLimbs prog s w)) x k :=
  (column_limb F prog s _ k x).trans
    ((column_committed F prog s _ flockCol not_isLimb_flockCol (cubeIndex (F.slot k) x)).symm.trans
      (column_stackOfG F gen prog s w flockCol not_isLimb_flockCol (cubeIndex (F.slot k) x)))

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

variable {F gen prog s w} [hgen : Fact (SlotsOK F @gen)]

/-- A witness satisfying the constraint system has its sizes. -/
theorem sizes_of_satisfiedByG {input : PublicInput} (h : SatisfiedByB prog input w) :
    ∃ s, Sizes.ofWitness w = some s := by
  unfold Sizes.ofWitness
  have hp : 0 < (imageOf w.data).1 := lt_of_lt_of_le (by decide) h.caps.minLogMem_le
  simp only [hp, dite_true]
  exact ⟨_, rfl⟩

/-! ## The stack of a witness agrees with it -/

/-- A cell of a table, as a row's cell. -/
private theorem cellOf_eq (t : Air.Flat.Table K) {x : ℕ} (hx : x < t.table.length) (i : ℕ) :
    cellOf t x i = (t.table[x]'hx)[i]?.getD 0 := by
  rw [cellOf, List.getElem?_eq_getElem hx]
  rfl

/-- Within its width, an opcode table of a witness satisfying the constraint system is the
stack's executed rows. -/
private theorem cells_stackOf {input : PublicInput} (_h : SatisfiedByB prog input w)
    (hp : 0 < (imageOf w.data).1) (j : Fin 6) (x : Fin ((witnessSizes w hp).rows j))
    (i : Fin (opcodeComponent j).width) :
    cellOf (opTable w j) x i =
      (leanIsaInstance F prog (witnessSizes w hp)).row
        (stackOfG gen prog (witnessSizes w hp) w) (opIdx j)
          (Fin.castLE ((witnessSizes w hp).rows_le j) x) i := by
  have hs : Sizes.ofWitness w = some (witnessSizes w hp) := by
    unfold Sizes.ofWitness
    simp only [hp, dite_true]
    rfl
  by_cases hl : IsLimb ⟨opIdx j, i⟩
  · have hj : j = 5 := Fin.ext (by have := congrArg Fin.val hl.1; simp [opIdx] at this; omega)
    subst hj
    have h1 : 9 ≤ i.val := hl.2.1
    have h2 : i.val < 27 := hl.2.2
    have hk : i.val - 9 < 18 := by omega
    have hi : i = ⟨9 + (i.val - 9), by rw [Nat.add_sub_cancel' h1]; exact i.isLt⟩ :=
      Fin.ext (by simp only; omega)
    have hx : (Fin.castLE ((witnessSizes w hp).rows_le 5) x).val < (witnessSizes w hp).rows 5 :=
      x.isLt
    rw [hi]
    refine Eq.symm ((column_limb_stackOfG F gen prog _ w ⟨i.val - 9, hk⟩ _).trans ?_)
    refine (congrFun (hgen.out _ _) _).trans ?_
    refine (congrFun (Vector.getElem_ofFn _) _).trans ?_
    split
    · rfl
    · exact absurd hx ‹_›
  · refine Eq.symm ((column_stackOfG F gen prog _ w ⟨opIdx j, i⟩ hl _).trans ?_)
    exact Vector.getElem_ofFn _

omit hgen in
/-- The memory block of a witness satisfying the constraint system is the stack's. -/
private theorem memRows_stackOf {input : PublicInput} (h : SatisfiedByB prog input w)
    (hp : 0 < (imageOf w.data).1) :
    memBlockRows w = memBlockRowsOf F prog (witnessSizes w hp)
      (stackOfG gen prog (witnessSizes w hp) w) := by
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
      cell F prog (witnessSizes w hp) (stackOfG gen prog (witnessSizes w hp) w) (memCol k) x =
        ((memBlockRows w)[x.val]'(by rw [hlen]; exact x.isLt))[memRowCell k]?.getD 0 :=
    fun k x ↦ (column_stackOfG F gen prog (witnessSizes w hp) w (memCol k) (fun hk ↦ by
      have := congrArg Fin.val hk.1; simp [memCol, opIdx] at this) x).trans
        ((Vector.getElem_ofFn _).trans (cellOf_eq _ _ _))
  rw [hrows, memBlockRowsOf]
  refine congrArg List.ofFn (funext fun x ↦ ?_)
  simp only [hcell, hrow x, hidx x, memRow_cell]
  rfl

omit hgen in
/-- The bytecode block of a witness satisfying the constraint system is the stack's. -/
private theorem bytecodeRows_stackOf {input : PublicInput} (h : SatisfiedByB prog input w)
    (hp : 0 < (imageOf w.data).1) :
    bytecodeBlockRows w = bytecodeBlockRowsOf F prog (witnessSizes w hp)
      (stackOfG gen prog (witnessSizes w hp) w) := by
  obtain ⟨cntFin, hrows⟩ := h.bytecode_rows
  have hlen : (bytecodeBlockRows w).length = 2 ^ prog.logSize := by
    rw [hrows, List.length_ofFn]
  have hrow : ∀ i : Fin (2 ^ prog.logSize),
      (bytecodeBlockRows w)[i.val]'(by rw [hlen]; exact i.isLt) =
        (toElements (bytecodeRowOf prog i (cntFin i))).toArray :=
    fun i ↦ by simp only [hrows, List.getElem_ofFn]
  have hcell : ∀ i : Fin (2 ^ prog.logSize),
      cell F prog (witnessSizes w hp) (stackOfG gen prog (witnessSizes w hp) w) bfcntCol i =
        ((bytecodeBlockRows w)[i.val]'(by rw [hlen]; exact i.isLt))[1]?.getD 0 :=
    fun i ↦ (column_stackOfG F gen prog (witnessSizes w hp) w bfcntCol (by decide) i).trans
      ((Vector.getElem_ofFn _).trans (cellOf_eq _ _ _))
  rw [hrows, bytecodeBlockRowsOf]
  refine congrArg List.ofFn (funext fun i ↦ ?_)
  simp only [hcell, hrow i, bytecodeRow_cell]

/-- The stack of a witness satisfying the constraint system agrees with it. -/
theorem agrees_stackOfG {input : PublicInput} (h : SatisfiedByB prog input w)
    (hs : Sizes.ofWitness w = some s) : Agrees F s (stackOfG gen prog s w) w := by
  obtain ⟨hp, rfl⟩ := eq_of_ofWitness hs
  exact ⟨fun j ↦ rfl, cells_stackOf h hp, memRows_stackOf h hp, bytecodeRows_stackOf h hp⟩

/-! ## The relation of the stack -/

omit hgen in
/-- A limb column of the memory on the stack of a witness satisfying the constraint system is
that limb of the image the data names. -/
private theorem memLimb_stackOf {input : PublicInput} (h : SatisfiedByB prog input w)
    (hp : 0 < (imageOf w.data).1) (k : Fin 3) (x : Fin (2 ^ (imageOf w.data).1)) :
    cell F prog (witnessSizes w hp) (stackOfG gen prog (witnessSizes w hp) w) (memCol k.castSucc) x =
      ((imageOf w.data).2 x).limb k := by
  obtain ⟨idx, cnt, hrows⟩ := h.seed_rows
  have hlen : (memBlockRows w).length = 2 ^ (imageOf w.data).1 := by
    rw [hrows, List.length_ofFn]
  refine (column_stackOfG F gen prog (witnessSizes w hp) w (memCol k.castSucc) (fun hk ↦ by
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
private theorem image_words {input : PublicInput} (h : SatisfiedByB prog input w)
    (h0 : 0 < 2 ^ (imageOf w.data).1) (h1 : 1 < 2 ^ (imageOf w.data).1) :
    (imageOf w.data).2 ⟨0, h0⟩ = input.word0 ∧ (imageOf w.data).2 ⟨1, h1⟩ = input.word1 := by
  have hκ : (imageOf w.data).1 < 64 := lt_of_le_of_lt h.caps.le_maxLogMem (by decide)
  have e0 := (MemImage.read_gpow hκ (imageOf w.data).2 ⟨0, h0⟩).symm.trans h.word0_eq
  have e1 := (MemImage.read_gpow hκ (imageOf w.data).2 ⟨1, h1⟩).symm.trans h.word1_eq
  exact ⟨Option.some.inj e0, Option.some.inj e1⟩

omit hgen in
/-- The stack of a witness satisfying the constraint system holds the public lines: its memory
columns' first two cells are the public words' limbs. -/
private theorem publicLinesHold_stackOf {input : PublicInput} (h : SatisfiedByB prog input w)
    (hs : Sizes.ofWitness w = some s) :
    (leanIsaInstance F prog s).PublicLinesHold input (stackOfG gen prog s w) := by
  obtain ⟨hp, rfl⟩ := eq_of_ofWitness hs
  have h0 : 0 < 2 ^ (imageOf w.data).1 := Nat.two_pow_pos _
  have h1 : 1 < 2 ^ (imageOf w.data).1 := Nat.one_lt_two_pow hp.ne'
  obtain ⟨w0, w1⟩ := image_words h h0 h1
  have hl : ∀ k : Fin 3,
      cell F prog (witnessSizes w hp) (stackOfG gen prog (witnessSizes w hp) w) (memCol k.castSucc)
        ⟨0, h0⟩ = input.word0.limb k ∧
      cell F prog (witnessSizes w hp) (stackOfG gen prog (witnessSizes w hp) w) (memCol k.castSucc)
        ⟨1, h1⟩ = input.word1.limb k := fun k ↦
    ⟨(memLimb_stackOf h hp k _).trans (congrArg (·.limb k) w0),
      (memLimb_stackOf h hp k _).trans (congrArg (·.limb k) w1)⟩
  intro l hl'
  have hls : (publicLines prog (witnessSizes w hp) input).toList =
      [⟨memCol 0, input.lanes 0, input.lanes 2, false, hp⟩,
        ⟨memCol 1, input.lanes 1, input.lanes 3, false, hp⟩, ⟨memCol 2, 0, 0, false, hp⟩] := rfl
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

/-! ## Honest padding -/

/-- **The padding is honest.** On the stack of any witness, at the sizes it carries, every padding row holds its table's public padding row: the committed cells are
zero past the table's rows, and the limbs the Flock region carries at a padding block are the
padding instance, when it compresses. -/
theorem paddingHonest_stackOfG (hs : Sizes.ofWitness w = some s) :
    (leanIsaInstance F prog s).PaddingHonest (stackOfG gen prog s w) := by
  obtain ⟨hp, rfl⟩ := eq_of_ofWitness hs
  rintro ⟨j, hj⟩ x hx
  funext i
  have h9 : j < 9 := hj
  match j, hj, h9, x, hx, i with
  | 0, _, _, x, hx, _ => exact absurd (lt_of_lt_of_le x.isLt hx) (lt_irrefl _)
  | 1, _, _, x, hx, _ => exact absurd (lt_of_lt_of_le x.isLt hx) (lt_irrefl _)
  | 2, _, _, x, hx, _ => exact absurd (lt_of_lt_of_le x.isLt hx) (lt_irrefl _)
  | j + 3, hj, h9, x, hx, i =>
    have hrows : (opTable w ⟨j, by omega⟩).table.length ≤ x.val := hx
    by_cases hl : IsLimb ⟨⟨j + 3, hj⟩, i⟩
    · have hj5 : j = 5 := by have := congrArg Fin.val hl.1; simp [opIdx] at this; omega
      subst hj5
      have h1 : 9 ≤ i.val := hl.2.1
      have h2 : i.val < 27 := hl.2.2
      have hw : (leanIsaInstance F prog (witnessSizes w hp)).width ⟨5 + 3, hj⟩ = 37 :=
        width_blake2s
      obtain ⟨k, rfl⟩ : ∃ k : Fin 18,
          i = ⟨9 + k.val, by clear hl h1 h2; have := k.isLt; rw [hw]; omega⟩ :=
        ⟨⟨i.val - 9, by omega⟩, Fin.ext (by simp only; omega)⟩
      let x' : Fin (2 ^ (witnessSizes w hp).τ 5) := x
      have hx' : (witnessSizes w hp).rows 5 ≤ x'.val := hx
      have hrow : (blake2sLimbs prog (witnessSizes w hp) w)[x'] = padLimbs := by
        refine (Vector.getElem_ofFn _).trans (funext fun k ↦ ?_)
        simp only [padLimbs, show ¬ x'.val < (witnessSizes w hp).rows 5 from Nat.not_lt.mpr hx',
          ↓reduceIte]
      refine (column_limb_stackOfG F gen prog (witnessSizes w hp) w k x').trans ?_
      refine (congrFun (hgen.out _ x') k).trans ?_
      exact congrFun hrow k
    · refine (column_stackOfG F gen prog (witnessSizes w hp) w ⟨⟨j + 3, hj⟩, i⟩ hl x).trans ?_
      refine Eq.trans ?_ (padRow_of_not_isLimb ⟨j, by omega⟩ i hl).symm
      refine (Vector.getElem_ofFn _).trans ?_
      simp [cellOf, List.getElem?_eq_none hrows]

/-- **The adaptor without Flock, completeness.** A witness satisfying leanISA's constraint
system without the compression stacks, with a generator writing every row's limbs at their slots,
into a column satisfying the leanISA relation without Flock whose padding rows hold the public
padding row (`m3Honest_stackOf` without the Flock clause and without the compression). -/
theorem m3HonestBlind_stackOfG {input : PublicInput} (h : SatisfiedByB prog input w)
    (hs : Sizes.ofWitness w = some s) :
    M3HoldsBlind (leanIsaInstance F prog s) input (stackOfG gen prog s w) ∧
      (leanIsaInstance F prog s).PaddingHonest (stackOfG gen prog s w) := by
  have hA := agrees_stackOfG (F := F) (gen := gen) h hs
  have hP := paddingHonest_stackOfG (F := F) (gen := gen) (w := w) hs
  refine ⟨⟨?_, (balanced_iff_pairs hA).mpr fun k ↦ ?_, (countsNonzero_iff hA).mp h.counts_nonzero,
    ?_⟩, hP⟩
  · intro j' C hC x
    rcases j' with ⟨_ | _ | _ | j, hj⟩
    · exact absurd hC List.not_mem_nil
    · exact absurd hC List.not_mem_nil
    · exact absurd hC List.not_mem_nil
    · have h9 : (leanIsaInstance F prog s).ntab = 9 := rfl
      by_cases hx : x.val < s.rows ⟨j, by omega⟩
      · have hmem : opTable w ⟨j, by omega⟩ ∈ w.allTables :=
          EnsembleWitness.mem_allTables_of_mem_tables _ (mem_tables_iff.mpr ⟨⟨j, by omega⟩, rfl⟩)
        exact (opcode_constraints_iff hA ⟨j, by omega⟩).mp (h.constraints _ hmem) ⟨x.val, hx⟩ C hC
      · rw [hP ⟨j + 3, hj⟩ x (Nat.not_lt.mp hx)]
        exact padRow_constraints ⟨j, by omega⟩ C hC
  · fin_cases k
    exacts [h.state_balanced, h.mem_balanced, h.bytecode_balanced]
  · exact publicLinesHold_stackOf h hs

/-- **The witness read back.** Reading a witness back off the stack of a witness satisfying the
constraint system gives the witness's opcode tables within their widths, its memory and bytecode
blocks, its public input and the image its data names. -/
theorem witnessOf_stackOfG {input : PublicInput} (h : SatisfiedByB prog input w)
    (hs : Sizes.ofWitness w = some s) :
    (∀ (j : Fin 6) (x : Fin (s.rows j)) (i : Fin (opcodeComponent j).width),
      cellOf (opTable (witnessOf F prog s (stackOfG gen prog s w)) j) x i = cellOf (opTable w j) x i) ∧
    memBlockRows (witnessOf F prog s (stackOfG gen prog s w)) = memBlockRows w ∧
    bytecodeBlockRows (witnessOf F prog s (stackOfG gen prog s w)) = bytecodeBlockRows w ∧
    (witnessOf F prog s (stackOfG gen prog s w)).publicInput = w.publicInput ∧
    imageOf (witnessOf F prog s (stackOfG gen prog s w)).data = imageOf w.data := by
  have hA := agrees_stackOfG (F := F) (gen := gen) h hs
  have hB := agrees_witnessOf F prog s (stackOfG gen prog s w)
  refine ⟨fun j x i ↦ (hB.cells j x i).trans (hA.cells j x i).symm,
    hB.memRows.trans hA.memRows.symm, hB.bytecodeRows.trans hA.bytecodeRows.symm, ?_, ?_⟩
  · obtain ⟨c00, c01, c10, c11, -, -⟩ := publicLines_cells F prog s _ (publicLinesHold_stackOf h hs)
    show publicInputOf F prog s (stackOfG gen prog s w) = _
    rw [h.public_input_eq, publicInputOf, PublicIO.ofInput, c00, c01, c10, c11]
  · obtain ⟨hp, rfl⟩ := eq_of_ofWitness hs
    rw [imageOf_witnessOf F prog _ _ h.caps.le_maxLogMem]
    refine image_sigma_eq rfl _ _ fun x ↦ ?_
    exact (congr (congr (congrArg E.ofLimbs (memLimb_stackOf h hp 0 x))
      (memLimb_stackOf h hp 1 x)) (memLimb_stackOf h hp 2 x)).trans (ofLimbs_limb _)


end

end LeanVM.Protocol.LeanIsa
