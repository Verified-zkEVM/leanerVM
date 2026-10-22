import LeanerVM.Arithmetization.Bus
import LeanerVMTests.Arithmetization.Statement

/-!
# Tests: lookup soundness

A classic test for kernel evaluation, on the hand-built witness of the constraint-statement
tests (`LeanerVMTests.Arithmetization.Statement`).

**The theorems applied.** On the honest witness, `mem_channel_sound` makes the product row's
three reads correct reads of the image, and `bytecode_channel_sound` makes the `XOR` fill row's
bytecode read the program's entry at its counter.

**Lemma 6.3 concludes that every count is `0`.** The list `[0, 0]` is invariant under
multiplication by `g` and is not empty.

**A zero-count read balances itself.** For any key, a read `(a, 0)` pulls and pushes the same
tuple: with the count hypothesis removed, `lookup_sound` is false on the one read `(1, 0)` with no
seed and no finalize and no good key. The witness-level form is the statement tests'
`zero_count_witness`, which satisfies every conjunct of `SatisfiedBy` but the count product.

**A wrong index column.** `badW` is the honest witness with one memory block row changed: the
first untouched cell, `29`, which holds `0` and is never read, carries the address `g^2` of `x`,
so its seed and finalize are both `(g^2, 1, 0)` and cancel. The witness satisfies every conjunct
`mem_channel_sound` consumes, the memory balance (from the honest witness's), the count product,
the caps and the seed rows, and fails `IndexColumnsAreRowIndices`; and the conclusion of
`mem_channel_sound` fails on it: the pulled finalize `(g^2, 1, 0)` is not a read of the image,
which holds `x` at `g^2`. The index column the verifier computes is load-bearing.
-/

namespace LeanerVMTests.Arithmetization.Bus

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization
open LeanerVMTests.Arithmetization.Statement
open Air.Flat (Component EnsembleWitness)

/-! ## Helpers -/

/-- A message on a channel is the message of an interaction on a channel of that name. -/
theorem exists_interaction_of_mem {w : EnsembleWitness (leanIsaEnsemble fillProg)}
    {c : RawChannel K} {a : Array K} (ha : a ∈ messagesOn w c) :
    ∃ i ∈ w.interactions, i.channel.name = c.name ∧ i.msg = a := by
  rw [messagesOn, List.mem_map] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  rw [List.mem_filter] at hi
  exact ⟨i, hi.1, of_decide_eq_true hi.2, rfl⟩

/-- A row's message is a message of the witness. -/
theorem mem_messagesOn {w : EnsembleWitness (leanIsaEnsemble fillProg)} {t : Air.Flat.Table K}
    (ht : t ∈ w.tables) {row : Array K} (hrow : row ∈ t.table) {c : RawChannel K} {a : Array K}
    (ha : a ∈ rowMessagesOn t row c) : a ∈ messagesOn w c := by
  rw [messagesOn_eq_flatMap, List.mem_flatMap]
  exact ⟨t, w.mem_allTables_of_mem_tables ht, List.mem_flatMap.mpr ⟨row, hrow, ha⟩⟩

/-! ## The theorems applied to the honest witness -/

/-- The product row's three memory reads are correct reads of the image. -/
example : ∀ m ∈ (mulSends (mulRow g)).mem, MemPull.Guarantees m fillData := by
  intro m hm
  have hrow := (mul_sendsOpcode (t := mulT g) rfl (rawRow (mulRow g))).mem_pull
  rw [show valueFromOffset MulRow 0 ((mulT g).environment (rawRow (mulRow g))) = mulRow g from
    rowAt_toElements fillData (mulRow g)] at hrow
  have hmem : (toElements m).toArray ∈ messagesOn (fillW 1 g memCnt) MemPull.toRaw :=
    mem_messagesOn (t := mulT g) (List.mem_cons_of_mem _ List.mem_cons_self) List.mem_cons_self
      (by rw [hrow]; exact List.mem_map_of_mem hm)
  obtain ⟨i, hi, hname, hmsg⟩ := exists_interaction_of_mem hmem
  exact mem_channel_sound fill_satisfiedBy i hi hname m hmsg

/-- The `XOR` fill row's bytecode read is the program's entry at its counter. -/
example : ∃ k : Fin (2 ^ fillProg.logSize), (xorSends xorRow).bc.pc = gpow k ∧
    #v[(xorSends xorRow).bc.opcode] ++ (xorSends xorRow).bc.op = entry (fillProg.code k) := by
  have hrow := (xor_sendsOpcode (t := xorT) rfl (rawRow xorRow)).bytecode_pull
  rw [show valueFromOffset XorRow 0 (xorT.environment (rawRow xorRow)) = xorRow from
    rowAt_toElements fillData xorRow] at hrow
  have hmem : (toElements (xorSends xorRow).bc).toArray ∈
      messagesOn (fillW 1 g memCnt) BytecodePull.toRaw :=
    mem_messagesOn (t := xorT) List.mem_cons_self List.mem_cons_self
      (by rw [hrow]; exact List.mem_singleton_self _)
  obtain ⟨i, hi, hname, hmsg⟩ := exists_interaction_of_mem hmem
  exact bytecode_channel_sound fill_satisfiedBy i hi hname _ hmsg

/-! ## Lemma 6.3 and the count hypothesis -/

/-- `[0, 0]` is invariant under multiplication by `g`: Lemma 6.3 concludes its counts are `0`,
and it is not empty. -/
example : ∀ c ∈ ([0, 0] : List K), c = 0 :=
  eq_zero_of_perm_map_mul_g (by simp) (by decide)

/-- Without the count hypothesis, `lookup_sound` is false: the read `(1, 0)` pulls and pushes the
same tuple, balancing itself with no seed and no finalize, though no key is good. -/
example : ¬ ∀ (reads seeds fins : List (K × K)) (Good : K → Prop),
    ((reads.map fun m ↦ (m.1, g * m.2)) ++ seeds).Perm (reads ++ fins) →
    (∀ m ∈ seeds, Good m.1) → (∀ m ∈ fins, Good m.1) → reads.length < 2 ^ 64 - 1 →
    ∀ m ∈ reads, Good m.1 := fun h ↦
  h [(1, 0)] [] [] (fun _ ↦ False) (by simp) (by simp) (by simp) (by decide) _ List.mem_cons_self

/-! ## A wrong index column -/

/-- The index column of the bad memory block: `g^i`, except at the first untouched cell, which
carries the address `g^2` of `x`. -/
def idxBad (i : ℕ) : K := if i = touched then gpow 2 else gpow i

/-- Row `i` of the bad memory block. -/
def memRowArrBad (i : Fin (2 ^ minLogMem)) : Array K :=
  (toElements (⟨idxBad i, memCnt i,
    #v[(fillImage i).limb 0, (fillImage i).limb 1, (fillImage i).limb 2]⟩ : MemRow K)).toArray

theorem memRowArrBad_eq (i : Fin (2 ^ minLogMem)) :
    memRowArrBad i =
      #[idxBad i, memCnt i, (fillImage i).limb 0, (fillImage i).limb 1, (fillImage i).limb 2] := by
  with_unfolding_all rfl

/-- The bad memory block. -/
def memTBad : Air.Flat.Table K :=
  mkT memTable (size MemRow) (List.ofFn memRowArrBad) (by
    intro r hr
    rw [List.mem_ofFn] at hr
    obtain ⟨i, rfl⟩ := hr
    exact Vector.size_toArray _)

theorem memTBad_table : memTBad.table = List.ofFn memRowArrBad := by
  dsimp only [memTBad, mkT]

/-- The honest witness with the bad memory block. -/
def badW : EnsembleWitness (leanIsaEnsemble fillProg) :=
  mkW [xorT, mulT g, setT 1, derefT, jumpT, blakeT, memTBad, bcT]

/-- The bad block's seed of cell `i`. -/
def seedBad (i : Fin (2 ^ minLogMem)) : Array K :=
  #[idxBad i, 1, (fillImage i).limb 0, (fillImage i).limb 1, (fillImage i).limb 2]

/-- The bad block's finalize of cell `i`. -/
def finBad (i : Fin (2 ^ minLogMem)) : Array K :=
  #[idxBad i, memCnt i, (fillImage i).limb 0, (fillImage i).limb 1, (fillImage i).limb 2]

theorem memTBad_pushes :
    (memTBad.interactions.filter (·.channel.name = MemPush.toRaw.name)).map (·.msg) =
      List.ofFn seedBad := by
  rw [table_interactions_eq, List.filter_flatMap, List.map_flatMap]
  simp only [memTBad, mkT, Air.Flat.Table.environment, memRow_push, ← List.map_eq_flatMap,
    List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  dsimp only [Function.comp_apply]
  rw [memRowArrBad_eq]
  rfl

theorem memTBad_pulls :
    (memTBad.interactions.filter (·.channel.name = MemPull.toRaw.name)).map (·.msg) =
      List.ofFn finBad := by
  rw [table_interactions_eq, List.filter_flatMap, List.map_flatMap]
  simp only [memTBad, mkT, Air.Flat.Table.environment, memRow_pull, ← List.map_eq_flatMap,
    List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  dsimp only [Function.comp_apply]
  rw [memRowArrBad_eq]
  rfl

/-- Below the first untouched cell the bad block is the honest one. -/
theorem idxBad_of_lt {i : ℕ} (h : i < touched) : idxBad i = gpow i :=
  ite_eq_right (by omega)

/-- The bad seeds, split at the touched cells: the touched ones are the honest seeds. -/
theorem seedsBad_split : List.ofFn seedBad =
    (List.ofFn fun i : Fin touched ↦ seedMsg (Fin.castAdd untouched i)) ++
      List.ofFn fun j : Fin untouched ↦ seedBad (Fin.natAdd touched j) := by
  rw [show List.ofFn seedBad = List.ofFn fun i : Fin (touched + untouched) ↦ seedBad i from rfl,
    List.ofFn_add]
  refine congrArg₂ _ (congrArg _ (funext fun i ↦ ?_)) rfl
  show #[idxBad i, 1, _, _, _] = #[gpow i, 1, _, _, _]
  rw [idxBad_of_lt i.isLt]
  rfl

/-- The bad finalizes, split the same way: past the touched cells they are the bad seeds. -/
theorem finsBad_split : List.ofFn finBad =
    (List.ofFn fun i : Fin touched ↦ finMsg memCnt (Fin.castAdd untouched i)) ++
      List.ofFn fun j : Fin untouched ↦ seedBad (Fin.natAdd touched j) := by
  rw [show List.ofFn finBad = List.ofFn fun i : Fin (touched + untouched) ↦ finBad i from rfl,
    List.ofFn_add]
  refine congrArg₂ _ (congrArg _ (funext fun i ↦ ?_)) (congrArg _ (funext fun j ↦ ?_))
  · show #[idxBad i, _, _, _, _] = #[gpow i, _, _, _, _]
    rw [idxBad_of_lt i.isLt]
    rfl
  · show #[_, memCnt (touched + j), _, _, _] = #[_, 1, _, _, _]
    rw [memCnt_of_ge (Nat.le_add_right touched j)]

/-- The bad witness's memory balance is the honest witness's touched permutation. -/
theorem badW_mem_balanced_iff :
    BalancedPair badW MemPull.toRaw MemPush.toRaw ↔
      (List.map (·.msg) (List.filter (·.channel.name = MemPush.toRaw.name)
        ((fillW 1 g memCnt).verifierTable.interactions ++ xorT.interactions ++
          (mulT g).interactions ++ (setT 1).interactions ++ derefT.interactions ++
          jumpT.interactions ++ blakeT.interactions)) ++
        List.ofFn fun i : Fin touched ↦ seedMsg (Fin.castAdd untouched i)).Perm
      (List.map (·.msg) (List.filter (·.channel.name = MemPull.toRaw.name)
        ((fillW 1 g memCnt).verifierTable.interactions ++ xorT.interactions ++
          (mulT g).interactions ++ (setT 1).interactions ++ derefT.interactions ++
          jumpT.interactions ++ blakeT.interactions)) ++
        List.ofFn fun i : Fin touched ↦ finMsg memCnt (Fin.castAdd untouched i)) := by
  unfold BalancedPair messagesOn
  rw [EnsembleWitness.interactions]
  simp only [EnsembleWitness.allTables, EnsembleWitness.verifierTable, badW, fillW, mkW,
    List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.filter_append, List.map_append,
    bcT_filter MemPush.toRaw (by decide) (by decide),
    bcT_filter MemPull.toRaw (by decide) (by decide), memTBad_pushes, memTBad_pulls,
    seedsBad_split, finsBad_split, ← List.append_assoc]
  exact List.perm_append_right_iff _

/-- The memory pair of the bad witness balances. -/
theorem badW_mem_balanced : BalancedPair badW MemPull.toRaw MemPush.toRaw :=
  badW_mem_balanced_iff.mpr ((mem_balanced_iff 1 g memCnt fun _ ↦ memCnt_of_ge).mp
    fill_mem_balanced)

/-- Its count product holds: its six opcode tables are the honest ones. -/
theorem badW_countsNonzero : CountsNonzero badW := by
  have h := fill_countsNonzero
  have h1 : badW.tables.take 6 = [xorT, mulT g, setT 1, derefT, jumpT, blakeT] := rfl
  have h2 : (fillW 1 g memCnt).tables.take 6 = [xorT, mulT g, setT 1, derefT, jumpT, blakeT] :=
    rfl
  unfold CountsNonzero at h ⊢
  rw [h1]
  rw [h2] at h
  exact h

/-- Its caps hold. -/
theorem badW_caps : Caps badW where
  minLogMem_le := by rw [show badW.data = fillData from rfl, fill_logSize]
  le_maxLogMem := by rw [show badW.data = fillData from rfl, fill_logSize]; decide
  heights := by
    intro t ht
    simp only [badW, mkW, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by decide, rfl⟩
    · exact ⟨0, by decide, rfl⟩
    · exact ⟨1, by decide, rfl⟩
    · exact ⟨0, by decide, rfl⟩
    · exact ⟨2, by decide, rfl⟩
    · exact ⟨3, by decide, by rw [blakeT_table, List.length_map, List.length_ofFn]; rfl⟩
    · exact ⟨minLogMem, by decide, by rw [memTBad_table, List.length_ofFn]⟩
    · exact ⟨5, by decide, by rw [bcT_table, List.length_ofFn]; rfl⟩
  blake2s_height := by
    rw [blake2sRows, show tableAt badW 5 = blakeT from rfl, blakeT_table, List.length_map,
      List.length_ofFn]
    decide
  well_shaped := fill_wellShaped

/-- The seed-rows conjunct over the bad block, for any image equal to the fixture's: the image
is substituted before anything is compared. -/
theorem seedRowsBad_of {tables : List (Air.Flat.Table K)} {pi : PublicIO K} {h1 h2 h3}
    (hrows : memBlockRows (⟨tables, fillData, pi, h1, h2, h3⟩ :
      EnsembleWitness (leanIsaEnsemble fillProg)) = List.ofFn memRowArrBad) :
    SeedRowsAreTheImage (⟨tables, fillData, pi, h1, h2, h3⟩ :
      EnsembleWitness (leanIsaEnsemble fillProg)) := by
  unfold SeedRowsAreTheImage
  dsimp only
  have key : ∀ s : (κ : ℕ) × MemImage κ, s = ⟨minLogMem, fillImage⟩ →
      ∃ idx cntFin : Fin (2 ^ s.1) → K,
        memBlockRows (⟨tables, fillData, pi, h1, h2, h3⟩ :
          EnsembleWitness (leanIsaEnsemble fillProg)) = List.ofFn fun i ↦
            (toElements (⟨idx i, cntFin i, #v[(s.2 i).limb 0, (s.2 i).limb 1, (s.2 i).limb 2]⟩ :
              MemRow K)).toArray := by
    rintro s rfl
    exact ⟨fun i ↦ idxBad i, fun i ↦ memCnt i, hrows⟩
  exact key (imageOf fillData) fill_imageOf

theorem badW_memBlockRows : memBlockRows badW = List.ofFn memRowArrBad := by
  rw [memBlockRows, show tableAt badW 6 = memTBad from rfl, memTBad_table]

/-- Its memory block's rows are the image, with the bad index column. -/
theorem badW_seedRows : SeedRowsAreTheImage badW := seedRowsBad_of badW_memBlockRows

/-- Its index column is wrong at cell `29`. -/
theorem badW_not_indexColumns : ¬ IndexColumnsAreRowIndices badW := fun h ↦ by
  have h29 := h touched (by rw [badW_memBlockRows, List.length_ofFn]; decide)
  simp only [badW_memBlockRows, List.getElem_ofFn, memRowArrBad, memRowAt_toElements, idxBad,
    ↓reduceIte] at h29
  revert h29
  decide +kernel

/-- The bad witness pulls the finalize `(g^2, 1, 0)` of cell `29`, and it is not a read of the
image: the conclusion of `mem_channel_sound` fails. -/
theorem badW_not_sound : ¬ ∀ i ∈ badW.interactions, i.channel.name = MemPull.name →
    ∀ m : MemMsg K, i.msg = (toElements m).toArray → MemPull.Guarantees m badW.data := by
  intro h
  let m : MemMsg K := ⟨gpow 2, 1, #v[0, 0, 0]⟩
  have hrow : memRowArrBad ⟨touched, by decide⟩ ∈ memTBad.table := by
    rw [memTBad_table]
    exact List.mem_ofFn.mpr ⟨_, rfl⟩
  have hmsgs : rowMessagesOn memTBad (memRowArrBad ⟨touched, by decide⟩) MemPull.toRaw =
      [(toElements m).toArray] := by
    rw [memBlock_rowMessagesOn (t := memTBad) rfl (memRowArrBad ⟨touched, by decide⟩)
      (rowAt_toElements fillData _)]
    decide +kernel
  have hmem : (toElements m).toArray ∈ messagesOn badW MemPull.toRaw :=
    mem_messagesOn (t := memTBad)
      (List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <|
        List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_of_mem _
          List.mem_cons_self)
      hrow (by rw [hmsgs]; exact List.mem_singleton_self _)
  obtain ⟨i, hi, hname, hmsg⟩ := exists_interaction_of_mem hmem
  have hg : (imageOf fillData).2.read (gpow 2) = some (E.ofLimbs 0 0 0) := h i hi hname m hmsg
  have hread : (imageOf fillData).2.read (gpow 2) = some mulX := by
    rw [fill_imageOf]
    exact read_at 2 mulX
  have hne : mulX ≠ E.ofLimbs 0 0 0 := by decide +kernel
  exact hne (Option.some.inj (hread.symm.trans hg))

end LeanerVMTests.Arithmetization.Bus
