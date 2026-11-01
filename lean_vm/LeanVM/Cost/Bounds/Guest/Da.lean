module

public import LeanVM.Cost.Bounds.Guest.Stmt
public import LeanVM.Cost.Decoder.Da

/-!
# Bounds on the guest decoder's prices: the DA matrix

`da_verify`'s witness off its callees' frames (`Cost/Decoder/Da.lean`), in the price `S` of an
application of `da_verify`'s valuation `σ` and the price `F` of an application of the frame map
`Vn` (a frame's valuation at a variable), the matrix's rows at most `2^34` (`gLogD_lt`):

* a column's and a row's valuation (`dvColVN_cost`: `F + 8·S + 33261`; `dvRowVN_cost`:
  `3·F + 19·S + 260661`), a cell's `256` symbols (`cellSymsOf_cost`), a column's `256` weights
  (`vecWsOf_cost`);
* a cell of the padded matrix (`dvSymsPN_cost`: `266·F + 66·S + G + 827379`), a column's
  weights (`dvWsPN_cost`: `257·F + 11·S + 175334`), the rows (`daRows_cost`, any symbols);
* **`dvWitN_cost`**: at most `dvWitNPrice G F S ≈ 2^41·(266·F + 66·S) + 2^67.7`: `2^34` rows of
  `128` cells, each a logarithm (`gLog (σ 1)`, recomputed per cell) and `266` frame reads.
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

theorem length_dvSymsPNAt (r : ℕ) (σ : Val) (Vn : NFrames) (i j : ℕ) :
    (Decoder.dvSymsPNAt r σ Vn i j).length = 256 := by
  unfold Decoder.dvSymsPNAt Da.cellSymsOf
  split_ifs
  · rw [List.length_map, List.length_range]
  · rw [List.length_replicate]

theorem length_dvWsPN (σ : Val) (Vn : NFrames) (j : ℕ) : (dvWsPN σ Vn j).length = 256 := by
  unfold dvWsPN Da.vecWsOf
  split_ifs
  · rw [List.length_map, List.length_range]
  · rw [List.length_replicate]

/-! ## The frames -/

section Frames

variable {Vn : NFrames} {VnV : MachineValue}
  (hVn : ∀ (k : ℕ) (a r : List E) (v : V),
    RunsApp P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v]
      (encodeValue (Vn k a r v)))
  {F : ℕ} (hF : ∀ (k : ℕ) (a r : List E) (v : V),
    appCost P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v] ≤ F)
include hVn hF

/-- A cell's `256` symbols (`cellSymsOf.c560`) at the valuation `dvSymsPNC.lam0`: `256·F + 12048`. -/
theorem cellSymsOf_cost (hP : Includes P Auto.LeanVM.Guest.B1.Da.cellSymsOf.c560.costDeps)
    (hL : Includes P Decoder.dvSymsPNC.lam0.costDeps) (a r : List E) :
    machineCost P Auto.LeanVM.Guest.B1.Da.cellSymsOf.c560.costIdx
      [.closure Decoder.dvSymsPNC.lam0.costIdx [VnV, encodeValue a, encodeValue r]] ≤
        256 * F + 12048 := by
  have hσ : ∀ v : V, RunsApp P (.closure Decoder.dvSymsPNC.lam0.costIdx
      [VnV, encodeValue a, encodeValue r]) [encodeValue v] (encodeValue (Vn 28 r a v)) :=
    fun v ↦ RunsApp.of_spec (Decoder.dvSymsPNC.lam0.costSpec P hL Vn VnV hVn a r v)
  rw [Auto.LeanVM.Guest.B1.Da.cellSymsOf.c560.costEq P hP _ _ hσ]
  have m := rangeMap_le P (by includes) (by includes) _
    (.closure Auto.LeanVM.Guest.B1.Da.cellSymsOf.c560.lam0.costIdx
      [.closure Decoder.dvSymsPNC.lam0.costIdx [VnV, encodeValue a, encodeValue r]])
    (fun j ↦ RunsApp.of_spec (Auto.LeanVM.Guest.B1.Da.cellSymsOf.c560.lam0.costSpec P
      (by includes) _ _ hσ j))
    (F + 19) 256 256 le_rfl (by norm_num) (fun j hj ↦ by
      rw [appCost_fn, List.cons_append, List.nil_append,
        Auto.LeanVM.Guest.B1.Da.cellSymsOf.c560.lam0.costEq P (by includes) _ _ hσ,
        limbs_of_lt (by omega : j < 2 ^ 64), appCost_fn, List.cons_append, List.cons_append,
        List.cons_append, List.nil_append, Decoder.dvSymsPNC.lam0.costEq P hL Vn VnV hVn]
      have := hF 28 r a (.n (j + 1))
      omega)
  omega

/-- A column's `256` weights (`vecWsOf.c564`) at the valuation `dvWsPNC.lam0`: `256·F + 11792`. -/
theorem vecWsOf_cost (hP : Includes P Auto.LeanVM.Guest.B1.Da.vecWsOf.c564.costDeps)
    (hL : Includes P Decoder.dvWsPNC.lam0.costDeps) (a r : List E) :
    machineCost P Auto.LeanVM.Guest.B1.Da.vecWsOf.c564.costIdx
      [.closure Decoder.dvWsPNC.lam0.costIdx [VnV, encodeValue a, encodeValue r]] ≤
        256 * F + 11792 := by
  have hσ : ∀ v : V, RunsApp P (.closure Decoder.dvWsPNC.lam0.costIdx
      [VnV, encodeValue a, encodeValue r]) [encodeValue v] (encodeValue (Vn 29 a r v)) :=
    fun v ↦ RunsApp.of_spec (Decoder.dvWsPNC.lam0.costSpec P hL Vn VnV hVn a r v)
  rw [Auto.LeanVM.Guest.B1.Da.vecWsOf.c564.costEq P hP _ _ hσ]
  have m := rangeMap_le P (by includes) (by includes) _
    (.closure Auto.LeanVM.Guest.B1.Da.vecWsOf.c564.lam0.costIdx
      [.closure Decoder.dvWsPNC.lam0.costIdx [VnV, encodeValue a, encodeValue r]])
    (fun j ↦ RunsApp.of_spec (Auto.LeanVM.Guest.B1.Da.vecWsOf.c564.lam0.costSpec P
      (by includes) _ _ hσ j))
    (F + 18) 256 256 le_rfl (by norm_num) (fun j hj ↦ by
      rw [appCost_fn, List.cons_append, List.nil_append,
        Auto.LeanVM.Guest.B1.Da.vecWsOf.c564.lam0.costEq P (by includes) _ _ hσ,
        limbs_of_lt (by omega : j < 2 ^ 64), appCost_fn, List.cons_append, List.cons_append,
        List.cons_append, List.nil_append, Decoder.dvWsPNC.lam0.costEq P hL Vn VnV hVn]
      have := hF 29 a r (.n (j + 1))
      omega)
  omega

section Val

variable {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, appCost P σV [encodeValue v] ≤ S)
include hσ hS

omit hVn hF in
/-- Column `j`'s arguments (`dvColArgs.c557`), `j < 128`: `8·S + 33246`. -/
theorem dvColArgs_cost (hP : Includes P Auto.LeanVM.Guest.B1.Da.dvColArgs.c557.costDeps) (j : ℕ)
    (hj : j < 128) :
    machineCost P Auto.LeanVM.Guest.B1.Da.dvColArgs.c557.costIdx [σV, encodeValue j] ≤
      8 * S + 33246 := by
  rw [Auto.LeanVM.Guest.B1.Da.dvColArgs.c557.costEq P hP σ σV hσ]
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
  have := hF (colNum j) (Da.dvColArgs σ j) [] a
  omega

/-- **Row `i`'s valuation in column `j`** (`dvRowVNC`) at `a`, `i < 2^34`, `j < 128`:
`3·F + 19·S + 260661`. -/
theorem dvRowVN_cost (hP : Includes P Decoder.dvRowVNC.costDeps) (i j : ℕ) (hi : i < 2 ^ 34)
    (hj : j < 128) (a : V) :
    machineCost P Decoder.dvRowVNC.costIdx [σV, VnV, encodeValue i, encodeValue j, encodeValue a] ≤
      3 * F + 19 * S + 260661 := by
  rw [Decoder.dvRowVNC.costEq P hP σ σV hσ Vn VnV hVn]
  have := rowNum_cost P (by includes) j (by omega)
  have := powSqE_cost_lt P (by includes) LeanVM.Protocol.Verifier.gen i 34 (by norm_num)
    (by norm_num) hi
  have := powSqE_cost_lt P (by includes) LeanVM.Protocol.Verifier.gen j 7 (by norm_num)
    (by norm_num) (by omega)
  have := dvColVN_cost P hVn hF hσ hS (by includes) j hj (.n 11)
  have := dvColVN_cost P hVn hF hσ hS (by includes) j hj (.n 14)
  have := hS (.n 1); have := hS (.n 27); have := hS (.n 13)
  have := hF (rowNum j) [LeanVM.Protocol.Verifier.gen ^ i, σ (.n 1), dvColVN σ Vn j (.n 11),
    σ (.n 27), LeanVM.Protocol.Verifier.gen ^ j, dvColVN σ Vn j (.n 14), σ (.n 13)] [] a
  omega

/-- **A cell of the padded matrix** of `r ≤ 2^34` rows (`dvSymsPNC`): at most
`266·F + 65·S + 827369`. -/
theorem dvSymsPN_cost (hP : Includes P Decoder.dvSymsPNC.costDeps) (r i j : ℕ) (hr : r ≤ 2 ^ 34)
    (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) :
    machineCost P Decoder.dvSymsPNC.costIdx [encodeValue r, σV, VnV, encodeValue i, encodeValue j] ≤
      266 * F + 65 * S + 827369 := by
  rw [Decoder.dvSymsPNC.costEq P hP r σ σV hσ Vn VnV hVn]
  rw [limbs_of_lt (by omega : r < 2 ^ 64), limbs_of_lt hi]
  split_ifs with h1 h2 h2
  · rw [limbs_of_lt (by omega : j < 2 ^ 64)]
    have := dvRowVN_cost P hVn hF hσ hS (by includes) i j (by omega) h2.2 (.n 7)
    have := dvRowVN_cost P hVn hF hσ hS (by includes) i j (by omega) h2.2 (.n 8)
    have := dvRowVN_cost P hVn hF hσ hS (by includes) i j (by omega) h2.2 (.n 9)
    have := dvColVN_cost P hVn hF hσ hS (by includes) j h2.2 (.n 11)
    have := cellSymsOf_cost P hVn hF (by includes) (by includes)
      [dvRowVN σ Vn i j (.n 7), dvRowVN σ Vn i j (.n 8), dvRowVN σ Vn i j (.n 9)]
      [dvColVN σ Vn j (.n 11)]
    omega
  · have := replicate_cost P (by includes) (0 : K) 256 (by norm_num)
    rw [limbs_of_lt (by omega : j < 2 ^ 64)]
    omega
  · omega
  · have := replicate_cost P (by includes) (0 : K) 256 (by norm_num)
    omega

/-- **A column's weights** (`dvWsPNC`): at most `257·F + 11·S + 175334`. -/
theorem dvWsPN_cost (hP : Includes P Decoder.dvWsPNC.costDeps) (j : ℕ) (hj : j < 2 ^ 64) :
    machineCost P Decoder.dvWsPNC.costIdx [σV, VnV, encodeValue j] ≤ 257 * F + 11 * S + 175334 := by
  rw [Decoder.dvWsPNC.costEq P hP σ σV hσ Vn VnV hVn, limbs_of_lt hj]
  split_ifs with h
  · have := powSqE_cost_lt P (by includes) LeanVM.Protocol.Verifier.gen j 7 (by norm_num)
      (by norm_num) (by omega)
    have := powSqE_cost_lt P (by includes) (LeanVM.Protocol.Verifier.gen ^ j) 2 2 (by norm_num)
      (by norm_num) (by norm_num)
    have := dvColVN_cost P hVn hF hσ hS (by includes) j h (.n 11)
    have := vecWsOf_cost P hVn hF (by includes) (by includes)
      [σ (.n 17) * (LeanVM.Protocol.Verifier.gen ^ j) ^ 2] [dvColVN σ Vn j (.n 11)]
    have := hS (.n 17)
    omega
  · have := replicate_cost P (by includes) (0 : E) 256 (by norm_num)
    omega

end Val

end Frames

/-- **The rows** (`daRows.c568`), any symbols: `r ≤ M` rows of `128` cells, each cell's price at
most `D` and its symbols at most `256`: at most `((D + 32)·128 + 296114)·M + 16`. -/
theorem daRows_cost (hP : Includes P Auto.LeanVM.Guest.B1.Da.daRows.c568.costDeps)
    (syms : ℕ → ℕ → List K) (symsV : MachineValue)
    (hsyms : ∀ a b, RunsApp P symsV [encodeValue a, encodeValue b] (encodeValue (syms a b)))
    (D r M : ℕ) (hr : r ≤ M) (hM : M < 2 ^ 64)
    (hD : ∀ i < r, ∀ j < 128, appCost P symsV [encodeValue i, encodeValue j] ≤ D)
    (hlen : ∀ i j, (syms i j).length ≤ 256) :
    machineCost P Auto.LeanVM.Guest.B1.Da.daRows.c568.costIdx [encodeValue r, symsV] ≤
      ((D + 32) * 128 + 296114) * M + 16 := by
  rw [Auto.LeanVM.Guest.B1.Da.daRows.c568.costEq P hP r syms symsV hsyms]
  have m := rangeMap_le P (by includes) (by includes) _
    (.closure Auto.LeanVM.Guest.B1.Da.daRows.c568.lam0.costIdx [symsV])
    (fun i ↦ RunsApp.of_spec (Auto.LeanVM.Guest.B1.Da.daRows.c568.lam0.costSpec P (by includes)
      syms symsV hsyms i))
    ((D + 32) * 128 + 296086) r M hr hM (fun i hi ↦ by
      rw [appCost_fn, List.cons_append, List.nil_append,
        Auto.LeanVM.Guest.B1.Da.daRows.c568.lam0.costEq P (by includes) syms symsV hsyms]
      have m' := rangeMap_le P (by includes) (by includes) _
        (.closure Auto.LeanVM.Guest.B1.Da.daRows.c568.lam0.lam0.costIdx [symsV, encodeValue i])
        (fun j ↦ RunsApp.of_spec (Auto.LeanVM.Guest.B1.Da.daRows.c568.lam0.lam0.costSpec P
          (by includes) syms symsV hsyms i j))
        (D + 4) 128 128 le_rfl (by norm_num) (fun j hj ↦ by
          rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
            Auto.LeanVM.Guest.B1.Da.daRows.c568.lam0.lam0.costEq P (by includes) syms symsV hsyms]
          have := hD i hi j hj
          omega)
      have hf := flatten_map_cost P (by includes) 256 (syms i) (List.range 128)
        (fun j _ ↦ hlen i j)
      simp only [List.length_range] at hf
      omega)
  nlinarith

section Witness

variable {Vn : NFrames} {VnV : MachineValue}
  (hVn : ∀ (k : ℕ) (a r : List E) (v : V),
    RunsApp P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v]
      (encodeValue (Vn k a r v)))
  {F : ℕ} (hF : ∀ (k : ℕ) (a r : List E) (v : V),
    appCost P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v] ≤ F)
  {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, appCost P σV [encodeValue v] ≤ S)
include hVn hF hσ hS

/-- The witness's price at `r ≤ 2^34` rows. -/
@[expose] def dvWitNAtPrice (F S : ℕ) : ℕ :=
  ((266 * F + 65 * S + 827375 + 32) * 128 + 296114) * 2 ^ 34 + 16 +
    ((257 * F + 11 * S + 175338 + 28) * 128 + 9) + 296067 + 22

/-- **`da_verify`'s witness at `r ≤ 2^34` rows** (`dvWitNAtC`): at most `dvWitNAtPrice F S`. -/
theorem dvWitNAt_cost (hP : Includes P Decoder.dvWitNAtC.costDeps) (r : ℕ) (hr : r ≤ 2 ^ 34) :
    machineCost P Decoder.dvWitNAtC.costIdx [encodeValue r, σV, VnV] ≤ dvWitNAtPrice F S := by
  rw [Decoder.dvWitNAtC.costEq P hP r σ σV hσ Vn VnV hVn]
  have hrows := daRows_cost P (by includes) (Decoder.dvSymsPNAt r σ Vn)
    (.closure Decoder.dvWitNAtC.lam0.costIdx [encodeValue r, σV, VnV])
    (fun i j ↦ RunsApp.of_spec (Decoder.dvWitNAtC.lam0.costSpec P (by includes) r σ σV hσ Vn VnV
      hVn i j))
    (266 * F + 65 * S + 827375) r (2 ^ 34) hr (by norm_num)
    (fun i hi j _ ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
        Decoder.dvWitNAtC.lam0.costEq P (by includes) r σ σV hσ Vn VnV hVn]
      have := dvSymsPN_cost P hVn hF hσ hS (by includes) r i j hr (by omega) (by omega)
      omega)
    (fun i j ↦ (length_dvSymsPNAt r σ Vn i j).le)
  have hws := rangeMap_le P (by includes) (by includes) _
    (.closure Decoder.dvWitNAtC.lam1.costIdx [σV, VnV])
    (fun j ↦ RunsApp.of_spec (Decoder.dvWitNAtC.lam1.costSpec P (by includes) σ σV hσ Vn VnV hVn j))
    (257 * F + 11 * S + 175338) 128 128 le_rfl (by norm_num) (fun j hj ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        Decoder.dvWitNAtC.lam1.costEq P (by includes) σ σV hσ Vn VnV hVn]
      have := dvWsPN_cost P hVn hF hσ hS (by includes) j (by omega)
      omega)
  have hf := flatten_map_cost P (by includes) 256 (dvWsPN σ Vn) (List.range 128)
    (fun j _ ↦ (length_dvWsPN σ Vn j).le)
  simp only [List.length_range] at hf
  unfold dvWitNAtPrice
  omega

/-- **`da_verify`'s witness** (`dvWitNC`), the logarithm's tables `D` given: one logarithm, the
rows (at most `2^34`): at most `S + G + dvWitNAtPrice F S + 14`. -/
theorem dvWitN_cost (D : LeanVM.Extraction.Fast.DiscreteLogTables)
    (hP : Includes P Decoder.dvWitNC.costDeps) (hG : GLogBound P D G) :
    machineCost P Decoder.dvWitNC.costIdx [encodeValue D, σV, VnV] ≤
      S + G + dvWitNAtPrice F S + 14 := by
  rw [Decoder.dvWitNC.costEq P hP D σ σV hσ Vn VnV hVn]
  have := hG (σ (.n 1))
  have := hS (.n 1)
  have := dvWitNAt_cost P hVn hF hσ hS (by includes) (Decoder.gLogD D (σ (.n 1)))
    (gLogD_lt D _).le
  omega

end Witness

end

end LeanVM.Cost.Bounds.Guest
