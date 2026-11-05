import LeanerVM.Arithmetization.Bus
import LeanerVMTests.Arithmetization.Statement

/-!
# Tests: lookup soundness

A classic test for kernel evaluation, on the hand-built witness of the constraint-statement
tests (`LeanerVMTests.Arithmetization.Statement`).

**The theorems applied.** On the honest witness, `mem_channel_sound` makes the product row's
three reads, their pulls and their pushes, correct reads of the image, and
`bytecode_channel_sound` makes the `XOR` fill row's bytecode read the program's entry at its
counter.

**Lemma 6.3 concludes that every count is `0`.** The list `[0, 0]` is invariant under
multiplication by `g` and is not empty.

**A zero-count read balances itself.** For any key, a read `(a, 0)` pulls and pushes the same
tuple: with the count hypothesis removed, `lookup_sound` is false on the one read `(1, 0)` with no
seed and no finalize and no good key, the test that isolates the hypothesis. The statement
tests' `zero_count_witness` shows the count product independent of the other conjuncts; its
zero-count read is a correct read, so it does not falsify `mem_channel_sound`'s conclusion.

**A wrong index column is no memory block.** A memory block whose first untouched cell, `29`,
carries the address `g^2` of `x` would seed and finalize `(g^2, 1, 0)`, which cancel, and its
pull would be a wrong read. The address column is a fixed column: those rows fail the block's
`FixedRowsMatch`, which every table of a witness carries, so no witness has them.
-/

namespace LeanerVMTests.Arithmetization.Bus

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization
open LeanerVMTests.Arithmetization.Statement
open Air.Flat (Component EnsembleWitness)

/-! ## Helpers -/

/-- The `XOR` table of the witness has the fixture's row. -/
theorem tableAt_zero : (tableAt (fillW 1 g memCnt) 0).table = xorT.table := by
  simp only [tableAt, fillW, mkW, witnessOfTables, Air.Flat.withDerivedData, List.getElem_map,
    List.getElem_attach]
  rfl

/-- The `MUL_NATIVE` table of the witness has the fixture's row. -/
theorem tableAt_one : (tableAt (fillW 1 g memCnt) 1).table = (mulT g).table := by
  simp only [tableAt, fillW, mkW, witnessOfTables, Air.Flat.withDerivedData, List.getElem_map,
    List.getElem_attach]
  rfl

/-! ## The theorems applied to the honest witness -/

/-- The product row's three memory reads, pulled and pushed, are correct reads of the image. -/
example : ∀ m ∈ (mulSends (mulRow g)).mem, MemChannel.Guarantees m (fillW 1 g memCnt).data ∧
    MemChannel.Guarantees m.bump (fillW 1 g memCnt).data := by
  intro m hm
  have hs := mul_sendsOpcode (t := tableAt (fillW 1 g memCnt) 1)
    (tableAt_component _ 1) (rawRow (mulRow g))
  rw [show valueFromOffset MulRow 0 ((tableAt (fillW 1 g memCnt) 1).environment
    (rawRow (mulRow g))) = mulRow g from rowAt_toElements _ (mulRow g)] at hs
  have hrow : rawRow (mulRow g) ∈ (tableAt (fillW 1 g memCnt) 1).table := by
    rw [tableAt_one]
    exact List.mem_cons_self
  have hpull := mem_messagesOn_of_mem_rowMessagesOn
    (t := tableAt (fillW 1 g memCnt) 1) (List.getElem_mem _) hrow (c := MemChannel.toRaw)
    (d := .pull) (a := (toElements m).toArray)
    (by rw [hs.mem_pull]; exact List.mem_map_of_mem hm)
  have hpush := mem_messagesOn_of_mem_rowMessagesOn
    (t := tableAt (fillW 1 g memCnt) 1) (List.getElem_mem _) hrow (c := MemChannel.toRaw)
    (d := .push) (a := (toElements m.bump).toArray)
    (by rw [hs.mem_push]; exact List.mem_map_of_mem hm)
  obtain ⟨i, hi, hname, -, hmsg⟩ := exists_interaction_of_mem_messagesOn hpull
  obtain ⟨i', hi', hname', -, hmsg'⟩ := exists_interaction_of_mem_messagesOn hpush
  exact ⟨mem_channel_sound fill_satisfiedBy i hi hname m hmsg,
    mem_channel_sound fill_satisfiedBy i' hi' hname' m.bump hmsg'⟩

/-- The `XOR` fill row's bytecode read is the program's entry at its counter. -/
example : ∃ k : Fin (2 ^ fillProg.logSize), (xorSends xorRow).bc.pc = gpow k ∧
    #v[(xorSends xorRow).bc.opcode] ++ (xorSends xorRow).bc.op = entry (fillProg.code k) := by
  have hs := xor_sendsOpcode (t := tableAt (fillW 1 g memCnt) 0)
    (tableAt_component _ 0) (rawRow xorRow)
  rw [show valueFromOffset XorRow 0 ((tableAt (fillW 1 g memCnt) 0).environment
    (rawRow xorRow)) = xorRow from rowAt_toElements _ xorRow] at hs
  have hrow : rawRow xorRow ∈ (tableAt (fillW 1 g memCnt) 0).table := by
    rw [tableAt_zero]
    exact List.mem_cons_self
  have hmem := mem_messagesOn_of_mem_rowMessagesOn
    (t := tableAt (fillW 1 g memCnt) 0) (List.getElem_mem _) hrow (c := BytecodeChannel.toRaw)
    (d := .pull) (a := (toElements (xorSends xorRow).bc).toArray)
    (by rw [hs.bytecode_pull]; exact List.mem_singleton_self _)
  obtain ⟨i, hi, hname, -, hmsg⟩ := exists_interaction_of_mem_messagesOn hmem
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

/-- The index column of a bad memory block: `g^i`, except at the first untouched cell, which
carries the address `g^2` of `x`. -/
def idxBad (i : ℕ) : K := if i = touched then gpow 2 else gpow i

/-- Row `i` of the bad memory block. -/
def memRowBad (i : Fin (2 ^ minLogMem)) : MemRow K :=
  ⟨idxBad i, memCnt i, #v[(fillImage i).limb 0, (fillImage i).limb 1, (fillImage i).limb 2]⟩

/-- The bad rows fail the memory block's fixed address column at cell `29`: no table of a
witness has them. -/
example : ¬ (memComponent minLogMem).FixedRowsMatch (List.ofFn fun i ↦ rawRow (memRowBad i)) := by
  rintro ⟨-, hfix⟩
  have h := hfix touched (by rw [List.length_ofFn]; decide)
  rw [List.getElem_ofFn] at h
  have h' := (memMode_fixedAt_iff (show touched < 2 ^ minLogMem by decide) (by decide) _).mp h
  have hidx : idxBad touched = gpow touched :=
    (congrArg MemRow.idx (fromElements_rawRow (memRowBad ⟨touched, by decide⟩))).symm.trans h'
  rw [idxBad, ite_eq_left (rfl : touched = touched)] at hidx
  exact absurd hidx (by decide +kernel)

end LeanerVMTests.Arithmetization.Bus
