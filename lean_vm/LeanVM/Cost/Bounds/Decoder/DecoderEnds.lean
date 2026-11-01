module

public import LeanVM.Cost.Bounds.Runner
public import LeanVM.Cost.DecoderProgram

/-!
# Bound: the decoder top's two ends and its entry, compiled

The prices of `Cost/Decoder/Ends.lean`'s functions and of the entry (`Cost/DecoderProgram.lean`):

* **`decoderTables_cost`**: the two address tables (`decoderTablesC`, the extractor's `powTable`
  twice), at most `(70κ + 374)·2^κ + (70ℓ + 374)·2^ℓ + 48`; at `κ, ℓ ≤ 32`
  (`decoderTables_cost_deployed`), at most `2614·2^33 + 48` (≈ `2^44.35`);
* **`memReader_cost`**: one memory read (`memReaderC`, the binary search in the table and the
  vector's entry), at most `123 + 42·log₂|memT|`; on the table `powTable κ`, `κ ≤ 32`, at most
  `123 + 42κ ≤ 1467` (`memReader_cost_deployed`), the price `R` of the reader closure
  (`memReaderClosure_cost`) the readers and the precondition's test take;
* `decodedOf_cost`: `7`;
* **`decoderOutput_cost`**: the seed (`decSeedC`, at most `A`) and the statement (`decStmtC`, at
  most `S`, the bounds of the chain `Log … Witness`), then `decodedOf`: at most `A + S + 14`;
* **`decoderEntry_output`**: the entry (`decoderEntryBody`) costs `8` past the top: a top whose
  price is at most `C` gives the program's output within the budget `C + 8`.
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Decoder LeanVM.Parameters LeanVM.Semantics LeanVM.Extraction.Fast

public section

variable (P : LeanVM.Cost.MachineProgram)

/-! ## The input side -/

open Auto.LeanVM.Extraction.Fast in
/-- **The address tables** (`decoderTablesC`): the memory's `2^κ` addresses and the bytecode's
`2^ℓ`, each sorted. -/
theorem decoderTables_cost (hP : Includes P decoderTablesC.costDeps) (prog : Program) (κ : ℕ)
    (hκ : κ ≤ 62) :
    machineCost P decoderTablesC.costIdx [encodeValue prog, encodeValue κ] ≤
      (70 * κ + 374) * 2 ^ κ + (70 * prog.logSize + 374) * 2 ^ prog.logSize + 48 := by
  have hls : prog.logSize ≤ 32 := prog.logSize_le
  rw [decoderTablesC.costEq P hP]
  have h1 := powTable_cost P (by includes) κ hκ
  have h2 := powTable_cost P (by includes) prog.logSize (by omega)
  omega

/-- `(70κ + 374)·2^κ` at `κ ≤ 32`: at most `2614·2^32`. -/
theorem powTablePrice_le {κ : ℕ} (hκ : κ ≤ 32) : (70 * κ + 374) * 2 ^ κ ≤ 2614 * 2 ^ 32 :=
  Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by norm_num) hκ)

/-- **The address tables at the deployed shape** (`κ, ℓ ≤ 32`): at most `2614·2^33 + 48`. -/
theorem decoderTables_cost_deployed (hP : Includes P decoderTablesC.costDeps) (prog : Program)
    (κ : ℕ) (hκ : κ ≤ 32) :
    machineCost P decoderTablesC.costIdx [encodeValue prog, encodeValue κ] ≤
      2614 * 2 ^ 33 + 48 := by
  have := decoderTables_cost P hP prog κ (by omega)
  have h1 := powTablePrice_le hκ
  have h2 := powTablePrice_le prog.logSize_le
  rw [show 2614 * 2 ^ 33 = 2614 * 2 ^ 32 + 2614 * 2 ^ 32 by norm_num]
  omega

open Auto.LeanVM.Extraction.Fast in
/-- **One memory read** (`memReaderC`): the binary search in the address table and the vector's
entry, at most `123 + 42·log₂|memT|`. -/
theorem memReader_cost (hP : Includes P memReaderC.costDeps) (memT : Array (ℕ × ℕ))
    (ht : WordTable memT) {κ : ℕ} (hκ : κ < 64) (mem : Vector E (2 ^ κ)) (a : K) :
    machineCost P memReaderC.costIdx [encodeValue memT, encodeValue κ, encodeValue mem,
      encodeValue a] ≤ 123 + 42 * Nat.log2 memT.size := by
  rw [memReaderC.costEq P hP]
  have := gLogTable_cost P (by includes) memT ht κ hκ a
  have := optionMap_cost P (by includes) _
    (.closure stepVec.c388.lam0.lam0.lam0.costIdx [encodeValue κ, encodeValue mem])
    (fun i ↦ RunsApp.of_spec (stepVec.c388.lam0.lam0.lam0.costSpec P (by includes) mem i)) 12
    (gLogTable memT κ a) (fun i _ ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [stepVec.c388.lam0.lam0.lam0.costEq P (by includes), limbs_shift hκ,
        limbs_of_lt (by omega : κ < 2 ^ 64), Auto.Vector.get.c442.costEq P (by includes)])
  omega

/-- **One memory read at the deployed shape** (the table `powTable κ`, `κ ≤ 32`): at most
`123 + 42κ ≤ 1467`. -/
theorem memReader_cost_deployed (hP : Includes P memReaderC.costDeps) {κ : ℕ} (hκ : κ ≤ 32)
    (mem : Vector E (2 ^ κ)) (a : K) :
    machineCost P memReaderC.costIdx [encodeValue (powTable κ), encodeValue κ, encodeValue mem,
      encodeValue a] ≤ 123 + 42 * κ := by
  have := memReader_cost P hP (powTable κ) (wordTable_powTable (by omega)) (by omega) mem a
  rwa [powTable_size, Nat.log2_two_pow] at this

/-- **The reader closure** (`memReader memT mem`, partially applied): each read at most
`123 + 42κ ≤ 1467` on the table `powTable κ`, `κ ≤ 32`: the price `R` of a read. -/
theorem memReaderClosure_cost (hP : Includes P memReaderC.costDeps) {κ : ℕ} (hκ : κ ≤ 32)
    (mem : Vector E (2 ^ κ)) (a : K) :
    appCost P (.closure memReaderC.costIdx [encodeValue (powTable κ), encodeValue κ,
      encodeValue mem]) [encodeValue a] ≤ 1467 := by
  simp only [appCost_fn, List.cons_append, List.nil_append]
  have := memReader_cost_deployed P hP hκ mem a
  omega

/-! ## The output side -/

/-- A decoding of its fields (`decodedOfC`): `7`. -/
theorem decodedOf_cost (hP : Includes P decodedOfC.costDeps) (s : LeanVM.Protocol.Digest)
    (st : LeanVM.Node.NodeStatement) (w : LeanVM.Node.NodeWitness) :
    machineCost P decodedOfC.costIdx [encodeValue s, encodeValue st, encodeValue w] = 7 := by
  rw [decodedOfC.costEq P hP]

/-- **The decoding** (`decoderOutputC`): the seed (at most `A`), the statement (at most `S`) and
`14`. -/
theorem decoderOutput_cost (hP : Includes P decoderOutputC.costDeps) (σ : LeanVM.Guest.Core.Val)
    (σVal : MachineValue) (hσ : ∀ a, RunsApp P σVal [encodeValue a] (encodeValue (σ a)))
    (rd : LeanVM.Guest.Core.Reader) (rdVal : MachineValue)
    (hrd : ∀ a, RunsApp P rdVal [encodeValue a] (encodeValue (rd a))) (w : LeanVM.Node.NodeWitness)
    (A S : ℕ) (hA : machineCost P decSeedC.costIdx [σVal] ≤ A)
    (hS : machineCost P decStmtC.costIdx [σVal, rdVal] ≤ S) :
    machineCost P decoderOutputC.costIdx [σVal, rdVal, encodeValue w] ≤ A + S + 14 := by
  rw [decoderOutputC.costEq P hP σ σVal hσ rd rdVal hrd, decodedOf_cost P (by includes)]
  omega

/-! ## The entry -/

/-- **The program's output within the top's price and the entry's `8`**: in a program whose
function `0` is `decoderEntryBody j`, a top `j` computing `v` on the input's fields at its
machine price, at most `C`, gives `v` within the budget `C + 8`. -/
theorem decoderEntry_output {j : ℕ} (hentry : P[0]? = some (decoderEntryBody j)) (prog : Program)
    (t : Execution prog) {v : MachineValue}
    (h : RunsBody P j [encodeValue prog, encodeValue t.logMemorySize,
      encodeValue (memoryVector t.memory)] v (machineCost P j [encodeValue prog,
        encodeValue t.logMemorySize, encodeValue (memoryVector t.memory)]))
    {C : ℕ} (hC : machineCost P j [encodeValue prog, encodeValue t.logMemorySize,
      encodeValue (memoryVector t.memory)] ≤ C) :
    outputWithin P (encodeDecoderInput prog t) (C + 8) = some v :=
  outputWithin_decoderEntry hentry prog t h (by omega)

end

end LeanVM.Cost.Bounds
