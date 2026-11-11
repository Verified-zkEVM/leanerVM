/-
  LeanerVM.Protocol.LeanIsa.Sound

  The adaptor's soundness direction: a stack satisfying the leanISA instance's relation carries a
  witness satisfying leanISA's constraint system.
-/

module

public import LeanerVM.Protocol.LeanIsa.Relation

/-!
# The adaptor, soundness

`satisfiedBy_witnessOf`: if the announced sizes are admissible and the stack `q` satisfies
`M3Holds` of the leanISA instance on the input, then the witness read off `q` (`witnessOf`)
satisfies `SatisfiedBy` on it. Every conjunct of `SatisfiedBy` comes from one clause of `M3Holds`,
from admissibility, or from how the witness is read:

* the Clean constraints, the three channels' balances and the nonzero read counts from the
  constraints, the bus and the count clauses, through the witness agreeing with its stack
  (`agrees_witnessOf`, with the equivalences of `LeanIsa/Relation.lean`); Clean's multiset
  balance also bounds each channel's interactions, which the caps do
  (`interactionsWith_length_lt`);
* the public input and the two public words from the three public lines, which fix the first two
  cells of the memory columns (`publicLines_cells`), and the image the data names, derived from
  the memory block, which is the memory columns at the announced size (`imageOf_witnessOf`);
* the caps from admissibility, which also make every table fit Clean's 64-bit row indices
  (`Sizes.Fits`); the fixed index and program columns by construction (`witnessOf`);
* **the BLAKE2s validity** (`blake2sRowsValid_witnessOf`) from the Flock clause. leanISA's
  `Blake2sRowsValid` asks every `BLAKE2S` row to satisfy `Blake2sRelation`, the compression on its
  eighteen limbs. The instance never commits the limbs: it reads them off the Flock region at the
  specification's slots, so the limbs of row `x` are the cells block `x` of the region carries
  there (`slotLimbs_flockColumn`). The Flock clause says every block satisfies the R1CS with the
  constant pinned, and `FlockSpec.compress_of_holds` turns that into the compression at the slots.
  No hypothesis beyond `M3Holds` is needed: the compression is proved, not assumed.

Admissibility is a hypothesis because `Caps` does not follow from `M3Holds`: the compiled
verifier checks the announced sizes before the protocol starts.
-/

namespace LeanerVM.Protocol.LeanIsa

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization CompPoly CMlPolynomialEval
open Air.Flat (Component EnsembleWitness)

@[expose] public section

/-- A raw `BLAKE2S` row of at least twenty-seven cells is a compression exactly when its limbs,
cells `9 … 26`, are. -/
theorem blake2sRelation_ofFn {n : ℕ} (r : Fin n → K) (hn : 27 ≤ n) (data : ProverData K) :
    Blake2sRelation (valueFromOffset Blake2sRow 0 (Environment.fromArray (Array.ofFn r) data)) ↔
      LimbsCompress fun k ↦ r ⟨9 + k, by omega⟩ := by
  unfold Blake2sRelation LimbsCompress
  simp [valueFromOffset, explicit_provable_type, circuit_norm, Array.getElem?_ofFn,
    show 9 < n by omega, show 10 < n by omega, show 11 < n by omega, show 12 < n by omega,
    show 13 < n by omega, show 14 < n by omega, show 15 < n by omega, show 16 < n by omega,
    show 17 < n by omega, show 18 < n by omega, show 19 < n by omega, show 20 < n by omega,
    show 21 < n by omega, show 22 < n by omega, show 23 < n by omega, show 24 < n by omega,
    show 25 < n by omega, show 26 < n by omega]

variable (F : FlockSpec) (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s))

/-- The tables of the witness read off a stack are the tables read off it, up to their data. -/
private theorem tableAt_witnessOf (j : Fin 8) :
    (tableAt (witnessOf F prog s q) j).table =
      ((tablesOf F prog s q)[(j : ℕ)]'(by simp [tablesOf])).table := by
  have h := witnessOfTables_map (prog := prog) (κ := s.logMem) (pi := publicInputOf F prog s q)
    (ts := tablesOf F prog s q) (hc := tablesOf_components F prog s q)
  have hl := congrArg List.length h
  simp only [List.length_map] at hl
  have := List.getElem_of_eq h (i := (j : ℕ)) (by rw [List.length_map, hl]; simp [tablesOf])
  simp only [List.getElem_map] at this
  exact congrArg Prod.snd this

/-- Opcode table `j` read off a stack is the stack's rows, or none. -/
private theorem opTableOf_table (j : Fin 6) :
    (opTableOf F prog s q j).table = if s.τ j ≤ 64 then opcodeRows F prog s q j else [] := by
  unfold opTableOf
  split <;> simp_all [tableOf]

/-- The table at opcode position `j` of the witness read off a stack is opcode table `j` read
off it. -/
private theorem opTable_witnessOf_eq (j : Fin 6) :
    (opTable (witnessOf F prog s q) j).table = (opTableOf F prog s q j).table := by
  refine (tableAt_witnessOf F prog s q ⟨j, by omega⟩).trans ?_
  fin_cases j <;> rfl

/-- The opcode tables of the witness read off a stack are the stack's rows, within `2^64`. -/
private theorem opTable_witnessOf (j : Fin 6) (h : s.τ j ≤ 64) :
    (opTable (witnessOf F prog s q) j).table = opcodeRows F prog s q j := by
  simp only [opTable_witnessOf_eq, opTableOf_table, h, ↓reduceIte]

/-- The memory block of the witness read off a stack is the stack's, below `2^64` rows. -/
private theorem memBlockRows_witnessOf (h : s.logMem < 64) :
    memBlockRows (witnessOf F prog s q) = memBlockRowsOf F prog s q := by
  refine (tableAt_witnessOf F prog s q 6).trans ?_
  show (memTableOf F prog s q).table = _
  simp only [memTableOf, h, ↓reduceDIte]
  rfl

/-- **The BLAKE2s validity.** On a stack whose Flock region satisfies the region predicate, every
`BLAKE2S` row of the witness read off it is a compression: its limbs are the cells the region's
block carries at the specification's slots, and the specification's soundness makes them a
compression. -/
theorem blake2sRowsValid_witnessOf (h : (leanIsaInstance F prog s).aux q) :
    Blake2sRowsValid (witnessOf F prog s q) := by
  intro row hrow
  rw [blake2sRows, show (tableAt (witnessOf F prog s q) 5).table =
    (opTable (witnessOf F prog s q) 5).table from rfl, opTable_witnessOf_eq, opTableOf_table]
    at hrow
  split_ifs at hrow
  swap
  · exact absurd hrow List.not_mem_nil
  rw [opcodeRows, List.mem_ofFn] at hrow
  obtain ⟨x, rfl⟩ := hrow
  refine (blake2sRelation_ofFn _ (le_trans (by decide : 27 ≤ 37) width_blake2s.ge) _).mpr ?_
  have hc := F.compress_of_holds _ (h (flockRegion prog s F) rfl) x
  rw [slotLimbs_flockColumn] at hc
  exact hc

/-! ## The witness agrees with its stack -/

/-- The witness read off a stack whose sizes fit Clean's tables agrees with it. -/
theorem agrees_witnessOf (hs : s.Fits) : Agrees F s q (witnessOf F prog s q) where
  length j := by rw [opTable_witnessOf F prog s q j (hs.2 j), opcodeRows, List.length_ofFn]
  cells j x i := by
    rw [cellOf, opTable_witnessOf F prog s q j (hs.2 j), opcodeRows]
    have hlt : (i : ℕ) < (shape prog s).width (opIdx j) := i.isLt
    simp only [List.getElem?_ofFn, Array.getElem?_ofFn, Option.bind_some, Fin.is_lt, dite_true,
      hlt, Option.getD_some]
    rfl
  memRows := memBlockRows_witnessOf F prog s q hs.1
  bytecodeRows := tableAt_witnessOf F prog s q 7

/-! ## The image and the public input -/

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
  E.ofLimbs (cell F prog s q (memCol 0) x) (cell F prog s q (memCol 1) x)
    (cell F prog s q (memCol 2) x)

/-- Within the memory cap, the image the witness's data names is the memory columns, word by
word, at the announced memory size: the data's `"mem"` table is the memory block's rows. -/
theorem imageOf_witnessOf (h : s.logMem ≤ maxLogMem) :
    imageOf (witnessOf F prog s q).data = ⟨s.logMem, imageWord F prog s q⟩ := by
  have hκ : s.logMem < 64 := lt_of_le_of_lt h (by decide)
  obtain ⟨hlen, hrows⟩ := memBlock_rows (witnessOf F prog s q) h
  have hm := memBlockRows_witnessOf F prog s q hκ
  refine image_sigma_eq (imageOf_data_fst h) _ _ fun i ↦ ?_
  have hi : (i : ℕ) < 2 ^ s.logMem := lt_of_lt_of_eq i.isLt (by rw [imageOf_data_fst h])
  have hi' : (i : ℕ) < (memBlockRows (witnessOf F prog s q)).length := hlen ▸ hi
  refine (imageOf_apply i (hrows i hi').2).trans ?_
  simp only [hm, memBlockRowsOf, List.getElem_ofFn, memRowAt_toElements]
  rfl

/-- The three public lines fix the first two cells of the three memory columns. -/
theorem publicLines_cells {input : PublicInput}
    (hp : (leanIsaInstance F prog s).PublicLinesHold input q) :
    cell0 F prog s q 0 = input.lanes 0 ∧ cell1 F prog s q 0 = input.lanes 2 ∧
      cell0 F prog s q 1 = input.lanes 1 ∧ cell1 F prog s q 1 = input.lanes 3 ∧
      cell0 F prog s q 2 = 0 ∧ cell1 F prog s q 2 = 0 := by
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

/-- On a stack whose sizes fit and whose constraint polynomials vanish, every table of the
witness read off it satisfies its Clean constraints. -/
private theorem constraints_witnessOf (hs : s.Fits)
    (hcv : (leanIsaInstance F prog s).ConstraintsVanish q) :
    (witnessOf F prog s q).Constraints := by
  intro t ht
  obtain ⟨⟨j, hj⟩, rfl⟩ := mem_tables_iff.mp ht
  by_cases h6 : j < 6
  · exact (opcode_constraints_iff (agrees_witnessOf F prog s q hs) ⟨j, h6⟩).mpr
      fun x C hC ↦ hcv (opIdx ⟨j, h6⟩) C hC x
  · have : j = 6 ∨ j = 7 := by omega
    rcases this with rfl | rfl
    · intro row _
      rw [tableAt_component]
      exact constraintsHold_of_nil _ rfl rfl _
    · intro row _
      rw [tableAt_component]
      exact constraintsHold_of_nil _ rfl rfl _

/-- The tables of the witness read off a stack whose sizes fit have the announced heights. -/
private theorem table_length_witnessOf (hs : s.Fits) (j : Fin 8) :
    (tableAt (witnessOf F prog s q) j).table.length =
      2 ^ (![s.τ 0, s.τ 1, s.τ 2, s.τ 3, s.τ 4, s.τ 5, s.logMem, prog.logSize] j) := by
  have hA := agrees_witnessOf F prog s q hs
  fin_cases j
  · exact hA.length 0
  · exact hA.length 1
  · exact hA.length 2
  · exact hA.length 3
  · exact hA.length 4
  · exact hA.length 5
  · exact (congrArg List.length hA.memRows).trans List.length_ofFn
  · exact (congrArg List.length hA.bytecodeRows).trans List.length_ofFn

/-- On admissible sizes, the witness read off a stack is within the caps. -/
theorem caps_witnessOf (hs : s.Admissible prog) : Caps (witnessOf F prog s q) := by
  have hf := hs.fits
  obtain ⟨hmin, hmax, hτ, hb2, -⟩ := hs
  refine ⟨hmin, hmax, ?_, ?_⟩
  · intro t ht
    obtain ⟨j, rfl⟩ := mem_tables_iff.mp ht
    refine ⟨_, ?_, table_length_witnessOf F prog s q hf j⟩
    fin_cases j
    exacts [hτ 0, hτ 1, hτ 2, hτ 3, hτ 4, hτ 5, hmax, prog.logSize_le]
  · rw [blake2sRows, table_length_witnessOf F prog s q hf 5]
    exact Nat.pow_le_pow_right (by norm_num) hb2

/-! ## The adaptor -/

/-- **The adaptor, soundness.** If the announced sizes are admissible and the stack `q`
satisfies the leanISA instance's relation on the input, then the witness read off `q` satisfies
leanISA's constraint system on it. -/
theorem satisfiedBy_witnessOf {input : PublicInput} (hs : s.Admissible prog)
    (h : M3Holds (leanIsaInstance F prog s) input q) :
    SatisfiedBy prog input (witnessOf F prog s q) := by
  obtain ⟨hcv, hbal, hcnt, hpl, haux⟩ := h
  have hA := agrees_witnessOf F prog s q hs.fits
  have hcaps := caps_witnessOf F prog s q hs
  have himg := imageOf_witnessOf F prog s q hs.2.1
  obtain ⟨c00, c01, c10, c11, c20, c21⟩ := publicLines_cells F prog s q hpl
  have hκ : s.logMem < 64 := hs.fits.1
  refine ⟨?_, constraints_witnessOf F prog s q hs.fits hcv,
    (balanced_multiset_iff _).mpr ⟨interactionsWith_length_lt hcaps,
      (balanced_iff_channels hA).mp hbal⟩,
    (countsNonzero_iff hA).mpr hcnt, hcaps, blake2sRowsValid_witnessOf F prog s q haux, ?_, ?_⟩
  · show publicInputOf F prog s q = PublicIO.ofInput input
    rw [publicInputOf, PublicIO.ofInput, c00, c01, c10, c11]
  · rw [himg]
    have := MemImage.read_gpow hκ (imageWord F prog s q) ⟨0, Nat.two_pow_pos _⟩
    refine this.trans ?_
    show some (E.ofLimbs (cell0 F prog s q 0) (cell0 F prog s q 1) (cell0 F prog s q 2)) = _
    rw [c00, c10, c20]
    rfl
  · rw [himg]
    have := MemImage.read_gpow hκ (imageWord F prog s q)
      ⟨1, Nat.one_lt_two_pow s.logMem_pos.ne'⟩
    refine this.trans ?_
    show some (E.ofLimbs (cell1 F prog s q 0) (cell1 F prog s q 1) (cell1 F prog s q 2)) = _
    rw [c01, c11, c21]
    rfl

end

end LeanerVM.Protocol.LeanIsa
