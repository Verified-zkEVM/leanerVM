module

public import LeanVM.Cost.Bounds.Guest.Readers
public import LeanVM.Cost.Decoder.Da

/-!
# Bounds on the guest decoder's prices: the DA matrix

`da_verify`'s witness off its callees' frames (`Cost/Decoder/Da.lean`: each column's frame looked
up once, its two words kept in an array of the `128` columns; each cell's row frame looked up
once; the powers of `g` in `K`), in the price `S` of an application of `da_verify`'s valuation `σ`
and the price `F` of an application of the frame map `Vn` (a frame's valuation at a variable), the
matrix's rows `r ≤ 2^k`, `k ≤ 34` (`r < 2^34`, `gLogD_lt`):

* a column's valuation (`dvColVN_cost`: `F + 8·S + 33261`), its two words (`dvColWords_cost`:
  `2·F + 16·S + 66561`), **the `128` columns' words** (`dvCols_cost`: `256·F + 2048·S + 8524051`);
* a row's valuation (`dvRowVW_cost`: `F + 3·S + 535·k + 3842`), a cell's `256` symbols at a row's
  valuation (`cellSymsAt_cost`: `3·Rw + 256·F + 12096`, `Rw` the row's price), a cell
  (`dvSymsCell_cost`: `259·F + 9·S + 1605·k + 23658`), a cell of the padded matrix
  (`dvSymsCols_cost`: `259·F + 9·S + 1605·k + 23693`);
* a column's weights (`dvWsCols_cost`: `256·F + S + 16916`), the rows (`daRows_cost`, any
  symbols);
* the witness, its columns' words given (`dvWitNCols_cost`), and built (`dvWitNAt_cost`: at most
  `dvWitNRowsPrice k F S = (33152·F + 1152·S + 205440·k + 3333810)·2^k + 33024·F + 2176·S +
  10989648`);
* **`dvWitN_cost`**: one logarithm (`GLogBound P D G`), the rows below `2^34`: at most
  `S + G + dvWitNAtPrice F S + 14`, `dvWitNAtPrice F S = dvWitNRowsPrice 34 F S ≈
  2^34·(33152·F + 1152·S) + 2^57.30` (`2^49.02·F + 2^44.17·S + 2^57.30`);
  `dvWitN_cost_of_le`: at rows `≤ 2^k`, `S + G + dvWitNRowsPrice k F S + 14`; at `r ≤ 32`
  (`k = 5`, the deployed DA), `1093888·F + 39041·S + G + 150541982` (`2^20.06·F + 2^15.25·S +
  G + 2^27.17`).
-/

namespace LeanVM.Cost.Bounds.Guest

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Main LeanVM.Guest.Fast

public section

variable (P : MachineProgram) {G : ℕ}

/-- Column `j`'s function (`colNumC`): `6`. -/
theorem colNum_cost (hP : Includes P Decoder.colNumC.costDeps) (j : ℕ) (hj : j < 2 ^ 64) :
    machineCost P Decoder.colNumC.costIdx [encodeValue j] ≤ 6 := by
  rw [Decoder.colNumC.costEq P hP, limbs_of_lt hj]; split_ifs <;> omega

/-- Column `j`'s row loop (`rowNumC`): `6`. -/
theorem rowNum_cost (hP : Includes P Decoder.rowNumC.costDeps) (j : ℕ) (hj : j < 2 ^ 64) :
    machineCost P Decoder.rowNumC.costIdx [encodeValue j] ≤ 6 := by
  rw [Decoder.rowNumC.costEq P hP, limbs_of_lt hj]; split_ifs <;> omega

theorem length_dvSymsCols (r : ℕ) (σ : Val) (Vn : NFrames) (cols : Array (E × E)) (i j : ℕ) :
    (Decoder.dvSymsCols r σ Vn cols i j).length = 256 := by
  unfold Decoder.dvSymsCols Decoder.dvSymsCell Decoder.cellSymsAt Da.cellSymsOf
  split_ifs
  · rw [List.length_map, List.length_range]
  · rw [List.length_replicate]

theorem length_dvWsCols (σ : Val) (Vn : NFrames) (cols : Array (E × E)) (j : ℕ) :
    (Decoder.dvWsCols σ Vn cols j).length = 256 := by
  unfold Decoder.dvWsCols Da.vecWsOf
  split_ifs
  · rw [List.length_map, List.length_range]
  · rw [List.length_replicate]

/-- **The rows** (`daRowsC`), any symbols: `r ≤ M` rows of `128` cells, each cell's price at
most `D` and its symbols at most `256`: at most `((D + 32)·128 + 296114)·M + 16`. -/
theorem daRows_cost (hP : Includes P Decoder.daRowsC.costDeps)
    (syms : ℕ → ℕ → List K) (symsV : MachineValue)
    (hsyms : ∀ a b, RunsApp P symsV [encodeValue a, encodeValue b] (encodeValue (syms a b)))
    (D r M : ℕ) (hr : r ≤ M) (hM : M < 2 ^ 64)
    (hD : ∀ i < r, ∀ j < 128, appCost P symsV [encodeValue i, encodeValue j] ≤ D)
    (hlen : ∀ i j, (syms i j).length ≤ 256) :
    machineCost P Decoder.daRowsC.costIdx [encodeValue r, symsV] ≤
      ((D + 32) * 128 + 296114) * M + 16 := by
  rw [Decoder.daRowsC.costEq P hP r syms symsV hsyms]
  have m := rangeMap_le P (by includes) (by includes) _
    (.closure Decoder.daRowsC.lam0.costIdx [symsV])
    (fun i ↦ RunsApp.of_spec (Decoder.daRowsC.lam0.costSpec P (by includes)
      syms symsV hsyms i))
    ((D + 32) * 128 + 296086) r M hr hM (fun i hi ↦ by
      rw [appCost_fn, List.cons_append, List.nil_append,
        Decoder.daRowsC.lam0.costEq P (by includes) syms symsV hsyms]
      have m' := rangeMap_le P (by includes) (by includes) _
        (.closure Decoder.daRowsC.lam0.lam0.costIdx [symsV, encodeValue i])
        (fun j ↦ RunsApp.of_spec (Decoder.daRowsC.lam0.lam0.costSpec P
          (by includes) syms symsV hsyms i j))
        (D + 4) 128 128 le_rfl (by norm_num) (fun j hj ↦ by
          rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
            Decoder.daRowsC.lam0.lam0.costEq P (by includes) syms symsV hsyms]
          have := hD i hi j hj
          omega)
      have hf := flatten_map_cost P (by includes) 256 (syms i) (List.range 128)
        (fun j _ ↦ hlen i j)
      simp only [List.length_range] at hf
      omega)
  nlinarith

section Frames

variable {Vn : NFrames} {VnV : MachineValue}
  (hVn : ∀ (k : ℕ) (a r : List E) (v : V),
    RunsApp P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v]
      (encodeValue (Vn k a r v)))
  {F : ℕ} (hF : ∀ (k : ℕ) (a r : List E) (v : V), k < 2 ^ 64 → a.length + r.length ≤ 16 →
    appCost P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v] ≤ F)
include hVn hF

/-- **A cell's `256` symbols at a row's valuation** (`cellSymsAtC`), the row's valuation a closure
`rowV` of price at most `Rw`: `3·Rw + 256·F + 12096`. -/
theorem cellSymsAt_cost (hP : Includes P Decoder.cellSymsAtC.costDeps) (c11 : E) {row : Val}
    {rowV : MachineValue} (hrow : ∀ v : V, RunsApp P rowV [encodeValue v] (encodeValue (row v)))
    {Rw : ℕ} (hRw : ∀ v : V, appCost P rowV [encodeValue v] ≤ Rw) :
    machineCost P Decoder.cellSymsAtC.costIdx [VnV, encodeValue c11, rowV] ≤
      3 * Rw + 256 * F + 12096 := by
  rw [Decoder.cellSymsAtC.costEq P hP Vn VnV hVn c11 row rowV hrow]
  set a := [row (.n 7), row (.n 8), row (.n 9)]
  have hσ : ∀ v : V, RunsApp P (.closure Decoder.cellSymsAtC.lam0.costIdx
      [VnV, encodeValue a, encodeValue [c11]]) [encodeValue v] (encodeValue (Vn 28 [c11] a v)) :=
    fun v ↦ RunsApp.of_spec (Decoder.cellSymsAtC.lam0.costSpec P (by includes) Vn VnV hVn a [c11] v)
  rw [Decoder.cellSymsOfC.costEq P (by includes) _ _ hσ]
  have m := rangeMap_le P (by includes) (by includes) _
    (.closure Decoder.cellSymsOfC.lam0.costIdx
      [.closure Decoder.cellSymsAtC.lam0.costIdx [VnV, encodeValue a, encodeValue [c11]]])
    (fun j ↦ RunsApp.of_spec (Decoder.cellSymsOfC.lam0.costSpec P
      (by includes) _ _ hσ j))
    (F + 19) 256 256 le_rfl (by norm_num) (fun j hj ↦ by
      rw [appCost_fn, List.cons_append, List.nil_append,
        Decoder.cellSymsOfC.lam0.costEq P (by includes) _ _ hσ,
        limbs_of_lt (by omega : j < 2 ^ 64), appCost_fn, List.cons_append, List.cons_append,
        List.cons_append, List.nil_append,
        Decoder.cellSymsAtC.lam0.costEq P (by includes) Vn VnV hVn]
      have := hF 28 [c11] a (.n (j + 1)) (by norm_num) (by simp [a])
      omega)
  have := hRw (.n 7); have := hRw (.n 8); have := hRw (.n 9)
  omega

/-- A column's `256` weights (`vecWsOfC`) at the valuation `dvWsColsC.lam0`:
`256·F + 11792`. -/
theorem vecWsOf_cost (hP : Includes P Decoder.vecWsOfC.costDeps)
    (hL : Includes P Decoder.dvWsColsC.lam0.costDeps) (a r : List E)
    (hlen : r.length + a.length ≤ 16) :
    machineCost P Decoder.vecWsOfC.costIdx
      [.closure Decoder.dvWsColsC.lam0.costIdx [VnV, encodeValue a, encodeValue r]] ≤
        256 * F + 11792 := by
  have hσ : ∀ v : V, RunsApp P (.closure Decoder.dvWsColsC.lam0.costIdx
      [VnV, encodeValue a, encodeValue r]) [encodeValue v] (encodeValue (Vn 29 r a v)) :=
    fun v ↦ RunsApp.of_spec (Decoder.dvWsColsC.lam0.costSpec P hL Vn VnV hVn a r v)
  rw [Decoder.vecWsOfC.costEq P hP _ _ hσ]
  have m := rangeMap_le P (by includes) (by includes) _
    (.closure Decoder.vecWsOfC.lam0.costIdx
      [.closure Decoder.dvWsColsC.lam0.costIdx [VnV, encodeValue a, encodeValue r]])
    (fun j ↦ RunsApp.of_spec (Decoder.vecWsOfC.lam0.costSpec P
      (by includes) _ _ hσ j))
    (F + 18) 256 256 le_rfl (by norm_num) (fun j hj ↦ by
      rw [appCost_fn, List.cons_append, List.nil_append,
        Decoder.vecWsOfC.lam0.costEq P (by includes) _ _ hσ,
        limbs_of_lt (by omega : j < 2 ^ 64), appCost_fn, List.cons_append, List.cons_append,
        List.cons_append, List.nil_append, Decoder.dvWsColsC.lam0.costEq P hL Vn VnV hVn]
      have := hF 29 r a (.n (j + 1)) (by norm_num) hlen
      omega)
  omega

section Val

variable {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, appCost P σV [encodeValue v] ≤ S)
include hσ hS

omit hVn hF in
/-- Column `j`'s arguments (`dvColArgsC`), `j < 128`: `8·S + 33246`. -/
theorem dvColArgs_cost (hP : Includes P Decoder.dvColArgsC.costDeps) (j : ℕ)
    (hj : j < 128) :
    machineCost P Decoder.dvColArgsC.costIdx [σV, encodeValue j] ≤
      8 * S + 33246 := by
  rw [Decoder.dvColArgsC.costEq P hP σ σV hσ]
  have := powSqE_cost_lt P (by includes) LeanVM.Protocol.Verifier.gen j 7 (by norm_num)
    (by norm_num) (by omega)
  have := hS (.n 1); have := hS (.n 3); have := hS (.n 4); have := hS (.n 2)
  have := hS (.n 13); have := hS (.n 31); have := hS (.n 27); have := hS (.n 17)
  omega

/-- **Column `j`'s valuation** (`dvColVNC`) at `a`, `j < 128`: `F + 8·S + 33261`. -/
theorem dvColVN_cost (hP : Includes P Decoder.dvColVNC.costDeps) (j : ℕ) (hj : j < 128) (a : V) :
    machineCost P Decoder.dvColVNC.costIdx [σV, VnV, encodeValue j, encodeValue a] ≤
      F + 8 * S + 33261 := by
  rw [Decoder.dvColVNC.costEq P hP σ σV hσ Vn VnV hVn]
  have := colNum_cost P (by includes) j (by omega)
  have := dvColArgs_cost P hσ hS (by includes) j hj
  have := hF (colNum j) (Da.dvColArgs σ j) [] a (by unfold colNum; split <;> norm_num)
    (by simp [Da.dvColArgs])
  omega

/-- **Column `j`'s two words** (`dvColWordsC`), its frame looked up once per word, `j < 128`:
`2·F + 16·S + 66561`. -/
theorem dvColWords_cost (hP : Includes P Decoder.dvColWordsC.costDeps) (j : ℕ) (hj : j < 128) :
    machineCost P Decoder.dvColWordsC.costIdx [σV, VnV, encodeValue j] ≤
      2 * F + 16 * S + 66561 := by
  have hv : ∀ v : V, RunsApp P (.closure Decoder.dvColWordsC.lam0.costIdx
      [σV, VnV, encodeValue j]) [encodeValue v] (encodeValue (dvColVN σ Vn j v)) :=
    fun v ↦ RunsApp.of_spec (Decoder.dvColWordsC.lam0.costSpec P (by includes) σ σV hσ Vn VnV hVn
      j v)
  rw [Decoder.dvColWordsC.costEq P hP σ σV hσ Vn VnV hVn,
    Decoder.colWordsOfC.costEq P (by includes) _ _ hv]
  have h : ∀ v : V, appCost P (.closure Decoder.dvColWordsC.lam0.costIdx
      [σV, VnV, encodeValue j]) [encodeValue v] ≤ F + 8 * S + 33266 := fun v ↦ by
    rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
      Decoder.dvColWordsC.lam0.costEq P (by includes) σ σV hσ Vn VnV hVn]
    have := dvColVN_cost P hVn hF hσ hS (by includes) j hj v
    omega
  have := h (.n 11); have := h (.n 14)
  omega

/-- **The `128` columns' words** (`dvColsC`), each column's frame looked up once:
`256·F + 2048·S + 8524051`. -/
theorem dvCols_cost (hP : Includes P Decoder.dvColsC.costDeps) :
    machineCost P Decoder.dvColsC.costIdx [σV, VnV] ≤ 256 * F + 2048 * S + 8524051 := by
  rw [Decoder.dvColsC.costEq P hP σ σV hσ Vn VnV hVn, List.length_map, List.length_range]
  have m := rangeMap_le P (by includes) (by includes) _
    (.closure Decoder.dvColsC.lam0.costIdx [σV, VnV])
    (fun j ↦ RunsApp.of_spec (Decoder.dvColsC.lam0.costSpec P (by includes) σ σV hσ Vn VnV hVn j))
    (2 * F + 16 * S + 66565) 128 128 le_rfl (by norm_num) (fun j hj ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        Decoder.dvColsC.lam0.costEq P (by includes) σ σV hσ Vn VnV hVn]
      have := dvColWords_cost P hVn hF hσ hS (by includes) j hj
      omega)
  omega

/-- **Row `i`'s valuation in column `j`** (`dvRowVWC`) at `a`, the column's words `cw` given,
`i < 2^k`, `k ≤ 34`, `j < 128`: `F + 3·S + 535·k + 3842`. -/
theorem dvRowVW_cost (hP : Includes P Decoder.dvRowVWC.costDeps) (cw : E × E) (k i j : ℕ)
    (hk0 : 0 < k) (hk : k ≤ 34) (hi : i < 2 ^ k) (hj : j < 128) (a : V) :
    machineCost P Decoder.dvRowVWC.costIdx
      [σV, VnV, encodeValue cw, encodeValue i, encodeValue j, encodeValue a] ≤
        F + 3 * S + 535 * k + 3842 := by
  rw [Decoder.dvRowVWC.costEq P hP σ σV hσ Vn VnV hVn]
  have := rowNum_cost P (by includes) j (by omega)
  have := powSqK_cost_lt P (by includes) Parameters.g i k hk0 (by omega) hi
  have := powSqK_cost_lt P (by includes) Parameters.g j 7 (by norm_num) (by norm_num) (by omega)
  have := hS (.n 1); have := hS (.n 27); have := hS (.n 13)
  have := hF (rowNum j) [ofK (Parameters.g ^ i), σ (.n 1), cw.1, σ (.n 27), ofK (Parameters.g ^ j),
    cw.2, σ (.n 13)] [] a (by unfold rowNum; split <;> norm_num) (by simp)
  omega

/-- **Cell `(i, j)`'s symbols** (`dvSymsCellC`), the column's words given, its row's frame looked
up once, `i < 2^k`, `k ≤ 34`, `j < 128`: `259·F + 9·S + 1605·k + 23658`. -/
theorem dvSymsCell_cost (hP : Includes P Decoder.dvSymsCellC.costDeps) (cw : E × E) (k i j : ℕ)
    (hk0 : 0 < k) (hk : k ≤ 34) (hi : i < 2 ^ k) (hj : j < 128) :
    machineCost P Decoder.dvSymsCellC.costIdx
      [σV, VnV, encodeValue cw, encodeValue i, encodeValue j] ≤
        259 * F + 9 * S + 1605 * k + 23658 := by
  rw [Decoder.dvSymsCellC.costEq P hP σ σV hσ Vn VnV hVn]
  have hrow : ∀ v : V, RunsApp P (.closure Decoder.dvSymsCellC.lam0.costIdx
      [σV, VnV, encodeValue cw, encodeValue i, encodeValue j]) [encodeValue v]
      (encodeValue (Decoder.dvRowVW σ Vn cw i j v)) :=
    fun v ↦ RunsApp.of_spec (Decoder.dvSymsCellC.lam0.costSpec P (by includes) σ σV hσ Vn VnV hVn
      cw i j v)
  have hRw : ∀ v : V, appCost P (.closure Decoder.dvSymsCellC.lam0.costIdx
      [σV, VnV, encodeValue cw, encodeValue i, encodeValue j]) [encodeValue v] ≤
        F + 3 * S + 535 * k + 3849 := fun v ↦ by
    rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
      List.cons_append, List.nil_append,
      Decoder.dvSymsCellC.lam0.costEq P (by includes) σ σV hσ Vn VnV hVn]
    have := dvRowVW_cost P hVn hF hσ hS (by includes) cw k i j hk0 hk hi hj v
    omega
  have := cellSymsAt_cost P hVn hF (by includes) cw.1 hrow hRw
  omega

/-- **A cell of the padded matrix** of `r ≤ 2^k` rows (`dvSymsColsC`), `k ≤ 34`, any columns'
words: at most `259·F + 9·S + 1605·k + 23693`. -/
theorem dvSymsCols_cost (hP : Includes P Decoder.dvSymsColsC.costDeps) (cols : Array (E × E))
    (k r i j : ℕ) (hk0 : 0 < k) (hk : k ≤ 34) (hr : r ≤ 2 ^ k) (hi : i < 2 ^ 64)
    (hj : j < 2 ^ 64) :
    machineCost P Decoder.dvSymsColsC.costIdx
      [encodeValue r, σV, VnV, encodeValue cols, encodeValue i, encodeValue j] ≤
        259 * F + 9 * S + 1605 * k + 23693 := by
  have h2 : 2 ^ k ≤ 2 ^ 34 := Nat.pow_le_pow_right (by norm_num) hk
  rw [Decoder.dvSymsColsC.costEq P hP r σ σV hσ Vn VnV hVn,
    limbs_of_lt (by omega : r < 2 ^ 64), limbs_of_lt hi, limbs_of_lt hj]
  have := replicate_cost P (by includes) (0 : K) 256 (by norm_num)
  split_ifs with h1 h2'
  · have := dvSymsCell_cost P hVn hF hσ hS (by includes) (cols.getD j (0, 0)) k i j hk0 hk
      (by omega) h2'.2
    omega
  · omega
  · omega
  · omega

/-- **A column's weights** (`dvWsColsC`), the columns' words given: at most
`256·F + S + 16916`. -/
theorem dvWsCols_cost (hP : Includes P Decoder.dvWsColsC.costDeps) (cols : Array (E × E)) (j : ℕ)
    (hj : j < 2 ^ 64) :
    machineCost P Decoder.dvWsColsC.costIdx [σV, VnV, encodeValue cols, encodeValue j] ≤
      256 * F + S + 16916 := by
  rw [Decoder.dvWsColsC.costEq P hP σ σV hσ Vn VnV hVn, limbs_of_lt hj,
    Decoder.mulKC.costEq P (by includes)]
  have := replicate_cost P (by includes) (0 : E) 256 (by norm_num)
  split_ifs with h
  · have := powSqK_cost_lt P (by includes) Parameters.g (2 * j) 8 (by norm_num) (by norm_num)
      (by omega)
    have := vecWsOf_cost P hVn hF (by includes) (by includes) [(cols.getD j (0, 0)).1]
      [Decoder.mulK (σ (.n 17)) (Parameters.g ^ (2 * j))] (by simp)
    have := hS (.n 17)
    omega
  · omega

/-- The witness's price, its columns' words given, at `r ≤ 2^k` rows. -/
@[expose] def dvWitNColsPrice (k F S : ℕ) : ℕ :=
  (33152 * F + 1152 * S + 205440 * k + 3333810) * 2 ^ k + 32768 * F + 128 * S + 2465590

/-- **`da_verify`'s witness, its columns' words given** (`dvWitNColsC`), `r ≤ 2^k` rows,
`0 < k ≤ 34`: at most `dvWitNColsPrice k F S`. -/
theorem dvWitNCols_cost (hP : Includes P Decoder.dvWitNColsC.costDeps) (cols : Array (E × E))
    (k r : ℕ) (hk0 : 0 < k) (hk : k ≤ 34) (hr : r ≤ 2 ^ k) :
    machineCost P Decoder.dvWitNColsC.costIdx [encodeValue r, σV, VnV, encodeValue cols] ≤
      dvWitNColsPrice k F S := by
  have h2 : 2 ^ k ≤ 2 ^ 34 := Nat.pow_le_pow_right (by norm_num) hk
  rw [Decoder.dvWitNColsC.costEq P hP r σ σV hσ Vn VnV hVn]
  have hrows := daRows_cost P (by includes) (Decoder.dvSymsCols r σ Vn cols)
    (.closure Decoder.dvWitNColsC.lam0.costIdx [encodeValue r, σV, VnV, encodeValue cols])
    (fun i j ↦ RunsApp.of_spec (Decoder.dvWitNColsC.lam0.costSpec P (by includes) r σ σV hσ Vn
      VnV hVn cols i j))
    (259 * F + 9 * S + 1605 * k + 23700) r (2 ^ k) hr (by omega)
    (fun i hi j hj ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.nil_append, Decoder.dvWitNColsC.lam0.costEq P (by includes) r σ σV hσ Vn VnV hVn]
      have := dvSymsCols_cost P hVn hF hσ hS (by includes) cols k r i j hk0 hk hr (by omega)
        (by omega)
      omega)
    (fun i j ↦ (length_dvSymsCols r σ Vn cols i j).le)
  have hws := rangeMap_le P (by includes) (by includes) _
    (.closure Decoder.dvWitNColsC.lam1.costIdx [σV, VnV, encodeValue cols])
    (fun j ↦ RunsApp.of_spec (Decoder.dvWitNColsC.lam1.costSpec P (by includes) σ σV hσ Vn VnV
      hVn cols j))
    (256 * F + S + 16921) 128 128 le_rfl (by norm_num) (fun j hj ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
        Decoder.dvWitNColsC.lam1.costEq P (by includes) σ σV hσ Vn VnV hVn]
      have := dvWsCols_cost P hVn hF hσ hS (by includes) cols j (by omega)
      omega)
  have hf := flatten_map_cost P (by includes) 256 (Decoder.dvWsCols σ Vn cols) (List.range 128)
    (fun j _ ↦ (length_dvWsCols σ Vn cols j).le)
  simp only [List.length_range] at hf
  have e : ((259 * F + 9 * S + 1605 * k + 23700 + 32) * 128 + 296114) * 2 ^ k =
      (33152 * F + 1152 * S + 205440 * k + 3333810) * 2 ^ k := by ring
  unfold dvWitNColsPrice
  omega

/-- The witness's price at `r ≤ 2^k` rows. -/
@[expose] def dvWitNRowsPrice (k F S : ℕ) : ℕ :=
  (33152 * F + 1152 * S + 205440 * k + 3333810) * 2 ^ k + 33024 * F + 2176 * S + 10989648

/-- The witness's price at `r ≤ 2^34` rows. -/
@[expose] def dvWitNAtPrice (F S : ℕ) : ℕ := dvWitNRowsPrice 34 F S

/-- **`da_verify`'s witness at `r ≤ 2^k` rows** (`dvWitNAtC`), `0 < k ≤ 34`: the columns' words
built once, then the witness: at most `dvWitNRowsPrice k F S`. -/
theorem dvWitNAt_cost (hP : Includes P Decoder.dvWitNAtC.costDeps) (k r : ℕ) (hk0 : 0 < k)
    (hk : k ≤ 34) (hr : r ≤ 2 ^ k) :
    machineCost P Decoder.dvWitNAtC.costIdx [encodeValue r, σV, VnV] ≤ dvWitNRowsPrice k F S := by
  rw [Decoder.dvWitNAtC.costEq P hP r σ σV hσ Vn VnV hVn]
  have := dvCols_cost P hVn hF hσ hS (by includes)
  have := dvWitNCols_cost P hVn hF hσ hS (by includes) (Decoder.dvCols σ Vn) k r hk0 hk hr
  unfold dvWitNColsPrice at this
  unfold dvWitNRowsPrice
  omega

/-- **`da_verify`'s witness at `r ≤ 2^k` rows** (`dvWitNC`), the logarithm's tables `D` given:
one logarithm, then the rows: at most `S + G + dvWitNRowsPrice k F S + 14`. -/
theorem dvWitN_cost_of_le (D : LeanVM.Extraction.Fast.DiscreteLogTables)
    (hP : Includes P Decoder.dvWitNC.costDeps) (hG : GLogBound P D G) (k : ℕ) (hk0 : 0 < k)
    (hk : k ≤ 34) (hr : Decoder.gLogD D (σ (.n 1)) ≤ 2 ^ k) :
    machineCost P Decoder.dvWitNC.costIdx [encodeValue D, σV, VnV] ≤
      S + G + dvWitNRowsPrice k F S + 14 := by
  rw [Decoder.dvWitNC.costEq P hP D σ σV hσ Vn VnV hVn]
  have := hG (σ (.n 1))
  have := hS (.n 1)
  have := dvWitNAt_cost P hVn hF hσ hS (by includes) k _ hk0 hk hr
  omega

/-- **`da_verify`'s witness** (`dvWitNC`), the logarithm's tables `D` given: one logarithm, the
rows below `2^34` (`gLogD_lt`): at most `S + G + dvWitNAtPrice F S + 14`. -/
theorem dvWitN_cost (D : LeanVM.Extraction.Fast.DiscreteLogTables)
    (hP : Includes P Decoder.dvWitNC.costDeps) (hG : GLogBound P D G) :
    machineCost P Decoder.dvWitNC.costIdx [encodeValue D, σV, VnV] ≤
      S + G + dvWitNAtPrice F S + 14 :=
  dvWitN_cost_of_le P hVn hF hσ hS D hP hG 34 (by norm_num) le_rfl (gLogD_lt D _).le

/-- At `r ≤ 32` rows (`k = 5`): `1093888·F + 39041·S + G + 150541982`. -/
theorem dvWitN_cost_32 (D : LeanVM.Extraction.Fast.DiscreteLogTables)
    (hP : Includes P Decoder.dvWitNC.costDeps) (hG : GLogBound P D G)
    (hr : Decoder.gLogD D (σ (.n 1)) ≤ 32) :
    machineCost P Decoder.dvWitNC.costIdx [encodeValue D, σV, VnV] ≤
      1093888 * F + 39041 * S + G + 150541982 := by
  have := dvWitN_cost_of_le P hVn hF hσ hS D hP hG 5 (by norm_num) (by norm_num) hr
  have e : dvWitNRowsPrice 5 F S = 1093888 * F + 39040 * S + 150541968 := by
    unfold dvWitNRowsPrice; ring
  omega

end Val

end Frames

end

end LeanVM.Cost.Bounds.Guest
