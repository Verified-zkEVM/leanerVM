/-
  LeanVM.Protocol.LeanIsa.Sound

  The adaptor's soundness direction: a stack satisfying the leanISA instance's relation carries a
  witness satisfying leanISA's constraint system.
-/

module

public import LeanVM.Protocol.LeanIsa.Relation
public import LeanVM.Arithmetization.Soundness.Bus

/-!
# The adaptor, soundness

`satisfiedBy_witnessOf`: if the announced sizes are admissible and the stack `q` satisfies
`M3Holds` of the leanISA instance on the input, then the witness read off `q` (`witnessOf`)
satisfies `SatisfiedBy` on it. Every conjunct of `SatisfiedBy` comes from one clause of `M3Holds`,
from admissibility, or from how the witness is read:

* the Clean constraints, the three channel pairs' balances and the nonzero read counts from the
  constraints, the bus and the count clauses, through the witness agreeing with its stack
  (`agrees_witnessOf`, with the equivalences of `LeanIsa/Relation.lean`);
* the public input and the two public words from the three public lines, which fix the first two
  cells of the memory columns (`publicLines_cells`), and the image the data names, which is the
  memory columns at the announced size (`imageOf_witnessOf`);
* the caps from admissibility; the index column, the seed rows and the bytecode rows by
  construction;
* **the `KECCAK` validity** (`keccakRowsValid_witnessOf`) from the Keccak clause. leanISA's
  `KeccakRowsValid` asks every `KECCAK` row's output lanes to be Keccak-f[1600] of its input lanes.
  The instance commits neither: an input lane is read off `QKECCAK` at its slot, and an output lane
  is derived, the second segment of the middle state `QKECCAK` commits for the row
  (`column_outCol`). The Keccak clause says every middle state is the first segment of its input
  state, so an output lane is the permutation of the input lanes (`column_outCol_of_aux`,
  `keccakF_eq_segments`). The permutation is proved, not assumed.

`satisfiedByB_witnessOf` gives every conjunct but the `KECCAK` validity; `satisfiedBy_witnessOf`
adds it.

Admissibility is a hypothesis because `Caps` does not follow from `M3Holds`: the compiled
verifier checks the announced sizes before the protocol starts.
-/

namespace LeanVM.Protocol.LeanIsa

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization CompPoly CMlPolynomialEval
open Air.Flat (Component EnsembleWitness)

@[expose] public section

set_option maxHeartbeats 2000000 in
/-- Input lane `l` of a raw `KECCAK` row is its cell `13 + l`. -/
theorem keccakRowAt_lin {prog : Program} (w : EnsembleWitness (leanIsaEnsemble prog)) (row : Array K)
    (l : Fin 25) : (keccakRowAt w row).lin[l] = row[13 + l.val]?.getD 0 := by
  simp [keccakRowAt, valueFromOffset, explicit_provable_type, circuit_norm]
  fin_cases l <;> simp

set_option maxHeartbeats 2000000 in
/-- Output lane `l` of a raw `KECCAK` row is its cell `38 + l`. -/
theorem keccakRowAt_lout {prog : Program} (w : EnsembleWitness (leanIsaEnsemble prog)) (row : Array K)
    (l : Fin 25) : (keccakRowAt w row).lout[l] = row[38 + l.val]?.getD 0 := by
  simp [keccakRowAt, valueFromOffset, explicit_provable_type, circuit_norm]
  fin_cases l <;> simp

variable (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s))

/-- The `KECCAK` rows of the witness read off a stack are the rows of opcode table `5`. -/
private theorem keccakRows_witnessOf :
    keccakRows (witnessOf prog s q) = opcodeRows prog s q 5 := rfl

/-- **The `KECCAK` validity.** On a stack whose Keccak region satisfies the Keccak predicate, every
`KECCAK` row of the witness read off it permutes: its output lanes are the derived columns, the
second segment of the committed middle state, which the predicate makes Keccak-f[1600] of the
input lanes the region holds at the row (`column_outCol_of_aux`, `column_inCol`). -/
theorem keccakRowsValid_witnessOf (h : (leanIsaInstance prog s).aux q) :
    KeccakRowsValid (witnessOf prog s q) := by
  intro row hrow
  rw [keccakRows_witnessOf, opcodeRows, List.mem_ofFn] at hrow
  obtain ⟨x, rfl⟩ := hrow
  have hw : (90 : ℕ) ≤ (leanIsaInstance prog s).width (opIdx 5) := width_keccak.ge
  unfold KeccakRelation KeccakRow.outLanes KeccakRow.inLanes
  funext l
  rw [keccakRowAt_lout, getElem?_pos _ _ (by rw [Array.size_ofFn]; omega), Array.getElem_ofFn,
    Option.getD_some]
  have hin : (fun l' : Fin 25 ↦ (keccakRowAt (witnessOf prog s q) (Array.ofFn
      ((leanIsaInstance prog s).row q (opIdx 5) (Fin.castLE (s.rows_le 5) x)))).lin[l']) =
      fun l' ↦ ((leanIsaInstance prog s).column q (inCol l')).values.get
        (Fin.castLE (s.rows_le 5) x) := by
    funext l'
    rw [keccakRowAt_lin, getElem?_pos _ _ (by rw [Array.size_ofFn]; omega), Array.getElem_ofFn,
      Option.getD_some]
    rfl
  rw [hin]
  refine (column_outCol_of_aux prog s q h l (Fin.castLE (s.rows_le 5) x)).trans ?_
  simp only [KeccakRegion.state, Nat.zero_add]
  congr 3
  funext l'
  exact (column_inCol prog s q l' _).symm

/-! ## The witness agrees with its stack -/

/-- The opcode tables of the witness read off a stack are the stack's rows. -/
private theorem opTable_witnessOf (j : Fin 6) :
    (opTable (witnessOf prog s q) j).table = opcodeRows prog s q j := by
  fin_cases j <;> rfl

/-- The witness read off a stack agrees with it. -/
theorem agrees_witnessOf : Agrees s q (witnessOf prog s q) where
  length j := by rw [opTable_witnessOf, opcodeRows, List.length_ofFn]
  cells j x i := by
    rw [cellOf, opTable_witnessOf, opcodeRows]
    have hlt : (i : ℕ) < (shape prog s).width (opIdx j) := i.isLt
    simp only [List.getElem?_ofFn, Array.getElem?_ofFn, Option.bind_some, Fin.is_lt, dite_true,
      hlt, Option.getD_some]
    rfl
  memRows := rfl
  bytecodeRows := rfl

/-! ## The image and the public input -/

/-- The prover data's `"mem"` table is the image read off the memory columns. -/
private theorem memRows_witnessOf : memRows (witnessOf prog s q).data = imageRows prog s q := by
  simp [memRows, witnessOf, dataOf]

/-- Two images are equal when their sizes are and their words agree. -/
theorem image_sigma_eq {κ κ' : ℕ} (h : κ = κ') (f : MemImage κ) (g : MemImage κ')
    (hfg : ∀ i : Fin (2 ^ κ), f i = g (Fin.cast (by rw [h]) i)) :
    (⟨κ, f⟩ : (κ : ℕ) × MemImage κ) = ⟨κ', g⟩ := by
  subst h
  congr
  funext i
  exact hfg i

/-- The word of the image at index `x`: the three memory columns' cells. -/
abbrev imageWord (x : Fin (2 ^ s.logMem)) : E :=
  E.ofLimbs (cell prog s q (memCol 0) x) (cell prog s q (memCol 1) x)
    (cell prog s q (memCol 2) x)

/-- Within the memory cap, the image the witness's data names is the memory columns, word by
word, at the announced memory size. -/
theorem imageOf_witnessOf (h : s.logMem ≤ maxLogMem) :
    imageOf (witnessOf prog s q).data = ⟨s.logMem, imageWord prog s q⟩ := by
  unfold imageOf
  rw [memRows_witnessOf]
  have hsz : (imageRows prog s q).size = 2 ^ s.logMem := Array.size_ofFn
  refine image_sigma_eq (by rw [hsz, Nat.log_pow (by norm_num), Nat.min_eq_left h]) _ _
    fun i ↦ ?_
  have hi : (i : ℕ) < 2 ^ s.logMem := hsz ▸ (i.isLt.trans_le (by
    rw [hsz, Nat.log_pow (by norm_num), Nat.min_eq_left h]))
  simp [imageRows, hi]
  rfl

/-- The three public lines fix the first two cells of the three memory columns. -/
theorem publicLines_cells {input : PublicInput}
    (hp : (leanIsaInstance prog s).PublicLinesHold input q) :
    cell0 prog s q 0 = input.lanes 0 ∧ cell1 prog s q 0 = input.lanes 2 ∧
      cell0 prog s q 1 = input.lanes 1 ∧ cell1 prog s q 1 = input.lanes 3 ∧
      cell0 prog s q 2 = 0 ∧ cell1 prog s q 2 = 0 := by
  have h0 := hp _ (List.mem_cons_self (l := [_, _]))
  have h1 := hp _ (List.mem_cons_of_mem _ (List.mem_cons_self (l := [_])))
  have h2 := hp _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self (l := []))))
  exact ⟨h0.1, h0.2, h1.1, h1.2, h2.1, h2.2⟩

/-! ## The constraints and the caps -/

/-- A component with neither constraints nor lookups holds on every row. -/
private theorem constraintsHold_of_nil (c : Component K) (h₁ : c.rowOperations.constraints = [])
    (h₂ : c.rowOperations.lookups = []) (env : Environment K) :
    c.operations.ConstraintsHold env := by
  rw [Air.Flat.Component.constraintsHold_iff, Operations.ConstraintsHold, h₁, h₂]
  simp

/-- On a stack whose constraint polynomials vanish, every table of the witness read off it
satisfies its Clean constraints. -/
theorem constraints_witnessOf (hcv : (leanIsaInstance prog s).ConstraintsVanish q) :
    (witnessOf prog s q).Constraints := by
  intro t ht
  rcases List.mem_cons.mp ht with rfl | ht
  · exact fun _ _ ↦ constraintsHold_of_nil _ rfl rfl _
  · obtain ⟨⟨j, hj⟩, rfl⟩ := mem_tables_iff.mp ht
    by_cases h6 : j < 6
    · exact (opcode_constraints_iff (agrees_witnessOf prog s q) ⟨j, h6⟩).mpr
        fun x C hC ↦ hcv (opIdx ⟨j, h6⟩) C hC _
    · have : j = 6 ∨ j = 7 := by omega
      rcases this with rfl | rfl
      · intro row _
        rw [tableAt_component]
        exact constraintsHold_of_nil _ rfl rfl _
      · intro row _
        rw [tableAt_component]
        exact constraintsHold_of_nil _ rfl rfl _

/-- The tables of the witness read off a stack have the announced row counts. -/
private theorem table_length_witnessOf (j : Fin 8) :
    (tableAt (witnessOf prog s q) j).table.length =
      ![s.rows 0, s.rows 1, s.rows 2, s.rows 3, s.rows 4, s.rows 5, 2 ^ s.logMem,
        2 ^ prog.logSize] j := by
  fin_cases j <;> exact List.length_ofFn

/-- On admissible sizes, the witness read off a stack is within the caps. -/
theorem caps_witnessOf (hs : s.Admissible prog) : Caps (witnessOf prog s q) := by
  obtain ⟨hmin, hmax, hrows, -⟩ := hs
  have himg := imageOf_witnessOf prog s q hmax
  refine ⟨?_, ?_, ?_, ⟨?_⟩⟩
  · rw [himg]
    exact hmin
  · rw [himg]
    exact hmax
  · intro t ht
    obtain ⟨j, rfl⟩ := mem_tables_iff.mp ht
    rw [table_length_witnessOf prog s q j]
    fin_cases j
    exacts [hrows 0, hrows 1, hrows 2, hrows 3, hrows 4, hrows 5,
      Nat.pow_le_pow_right (by norm_num) hmax,
      Nat.pow_le_pow_right (by norm_num) prog.logSize_le]
  · rw [memRows_witnessOf, himg]
    exact Array.size_ofFn

/-- The seed rows are the image, for an image given as a dependent pair. -/
private def SeedRowsAre {prog : Program} (w : EnsembleWitness (leanIsaEnsemble prog))
    (d : (κ : ℕ) × MemImage κ) : Prop :=
  ∃ idx cntFin : Fin (2 ^ d.1) → K, memBlockRows w = List.ofFn fun i ↦
    (toElements (⟨idx i, cntFin i, #v[(d.2 i).limb 0, (d.2 i).limb 1, (d.2 i).limb 2]⟩ :
      MemRow K)).toArray

/-- `SeedRowsAreTheImage` is `SeedRowsAre` of the image the data names. -/
private theorem seedRows_iff {prog : Program} (w : EnsembleWitness (leanIsaEnsemble prog)) :
    SeedRowsAreTheImage w ↔ SeedRowsAre w (imageOf w.data) := Iff.rfl

/-! ## The adaptor -/

/-- **The adaptor, soundness, without the `KECCAK` validity.** If the announced sizes are admissible
and the stack `q` satisfies the leanISA instance's constraints, bus, counts and public lines on
the input, then the witness read off `q` satisfies leanISA's constraint system on it but for the
`KECCAK` validity (`SatisfiedByB`). -/
theorem satisfiedByB_witnessOf {input : PublicInput} (hs : s.Admissible prog)
    (hcv : (leanIsaInstance prog s).ConstraintsVanish q)
    (hbal : (leanIsaInstance prog s).Balanced q)
    (hcnt : (leanIsaInstance prog s).CountsNonzero q)
    (hpl : (leanIsaInstance prog s).PublicLinesHold input q) :
    SatisfiedByB prog input (witnessOf prog s q) := by
  have hmax : s.logMem ≤ maxLogMem := hs.2.1
  have hA := agrees_witnessOf prog s q
  have hpairs := (balanced_iff_pairs hA).mp hbal
  have himg := imageOf_witnessOf prog s q hmax
  obtain ⟨c00, c01, c10, c11, c20, c21⟩ := publicLines_cells prog s q hpl
  have hκ : s.logMem < 64 := lt_of_le_of_lt hmax (by decide)
  refine ⟨?_, constraints_witnessOf prog s q hcv, hpairs 0, hpairs 1, hpairs 2,
    (countsNonzero_iff hA).mpr hcnt, caps_witnessOf prog s q hs, ?_, ?_, ⟨_, rfl⟩, ?_, ?_⟩
  · show publicInputOf prog s q = PublicIO.ofInput input
    rw [publicInputOf, PublicIO.ofInput, c00, c01, c10, c11]
  · intro i hi
    show (memRowAt _ ((memBlockRowsOf prog s q)[i]'hi)).idx = gpow i
    simp only [memBlockRowsOf, List.getElem_ofFn, memRowAt_toElements]
  · rw [seedRows_iff, himg]
    refine ⟨fun x ↦ gpow x, fun x ↦ cell prog s q (memCol 3) x, ?_⟩
    show memBlockRowsOf prog s q = _
    simp only [memBlockRowsOf, imageWord, limb_ofLimbs]
    rfl
  · rw [himg]
    have := MemImage.read_gpow hκ (imageWord prog s q) ⟨0, Nat.two_pow_pos _⟩
    refine this.trans ?_
    show some (E.ofLimbs (cell0 prog s q 0) (cell0 prog s q 1) (cell0 prog s q 2)) = _
    rw [c00, c10, c20]
    rfl
  · rw [himg]
    have := MemImage.read_gpow hκ (imageWord prog s q)
      ⟨1, Nat.one_lt_two_pow s.logMem_pos.ne'⟩
    refine this.trans ?_
    show some (E.ofLimbs (cell1 prog s q 0) (cell1 prog s q 1) (cell1 prog s q 2)) = _
    rw [c01, c11, c21]
    rfl

/-- **The adaptor, soundness.** If the announced sizes are admissible and the stack `q`
satisfies the leanISA instance's relation on the input, then the witness read off `q` satisfies
leanISA's constraint system on it. -/
theorem satisfiedBy_witnessOf {input : PublicInput} (hs : s.Admissible prog)
    (h : M3Holds (leanIsaInstance prog s) input q) :
    SatisfiedBy prog input (witnessOf prog s q) :=
  (satisfiedByB_witnessOf prog s q hs h.1 h.2.1 h.2.2.1 h.2.2.2.1).toSatisfiedBy
    (keccakRowsValid_witnessOf prog s q h.2.2.2.2)

end

end LeanVM.Protocol.LeanIsa
