module

public import LeanVM.Cost.Bounds.Guest.Readers

/-!
# Bounds on the guest decoder's prices: the seed, the statement, the batching's hints

In the price `R` of an application of the memory's reader `rd` and the price `S` of an
application of `main`'s valuation `σ`, the declared claims at most `2^34` of each kind
(`gLog_lt`):

* **`decSeed_cost`**: `2·S + 45`;
* **`decStmt_cost`**: at most `decStmtPrice G R S = 8·S + (2^37 + 26)·R + 3·G +
  2^35·657464 + 565399 ≈ 2^37·R + 2^54.33`: the declared claims, each a slot's four cells and
  their exponentiation `gen^(4s)` in `E` (three times, the compiler not sharing it);
* `aggRounds_cost`, **`aggHints_cost`**: `47·S + 46·R + 998693`.
-/

namespace LeanVM.Cost.Bounds.Guest

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Main

public section

variable (P : MachineProgram) {G : ℕ}

section Val

variable {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, appCost P σV [encodeValue v] ≤ S)
include hσ hS

/-- **The seed** (`decSeedC`): `2·S + 45` at most. -/
theorem decSeed_cost (hP : Includes P Decoder.decSeedC.costDeps) :
    machineCost P Decoder.decSeedC.costIdx [σV] ≤ 2 * S + 45 := by
  rw [Decoder.decSeedC.costEq P hP σ σV hσ, digestOfCells_cost P (by includes)]
  have := hS (.n 47)
  have := hS (.n 48)
  omega

section Reader

variable {rd : Reader} {rdV : MachineValue}
  (hrd : ∀ a : K, RunsApp P rdV [encodeValue a] (encodeValue (rd a)))
  {R : ℕ} (hR : ∀ a : K, appCost P rdV [encodeValue a] ≤ R)
include hrd hR

/-- The statement's price. -/
@[expose] def decStmtPrice (G R S : ℕ) : ℕ :=
  8 * S + (2 ^ 37 + 26) * R + 3 * G + 2 ^ 35 * 657464 + 565399

/-- **The statement** (`decStmtC`): at most `decStmtPrice G R S`. -/
theorem decStmt_cost (hP : Includes P Decoder.decStmtC.costDeps) (hG : GLogBound P G) :
    machineCost P Decoder.decStmtC.costIdx [σV, rdV] ≤ decStmtPrice G R S := by
  rw [Decoder.decStmtC.costEq P hP σ σV hσ rd rdV hrd]
  have g0 := hG (σ (.n 0))
  have g3 := hG (σ (.n 3))
  have g387 := hG (σ (.n 387))
  have n0 := gLog_lt (σ (.n 0))
  have n3 := gLog_lt (σ (.n 3))
  have n387 := gLog_lt (σ (.n 387))
  have m0 := rangeMap_le P (by includes) (by includes) (xmssAt rd (σ (.n 53)))
    (.closure Decoder.decStmtC.lam0.costIdx [rdV, encodeValue (σ (.n 53))])
    (fun s ↦ RunsApp.of_spec (Decoder.decStmtC.lam0.costSpec P (by includes) rd rdV hrd _ s))
    (4 * R + 657436) (gLog (σ (.n 0))) (2 ^ 34) n0.le (by norm_num) (fun k hk ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        Decoder.decStmtC.lam0.costEq P (by includes) rd rdV hrd]
      have := xmssAt_cost P hrd hR (by includes) (σ (.n 53)) k (by omega)
      omega)
  have m3 := rangeMap_le P (by includes) (by includes) (sphincsAt rd (σ (.n 56)))
    (.closure Decoder.decStmtC.lam2.costIdx [rdV, encodeValue (σ (.n 56))])
    (fun s ↦ RunsApp.of_spec (Decoder.decStmtC.lam2.costSpec P (by includes) rd rdV hrd _ s))
    (4 * R + 657436) (gLog (σ (.n 3))) (2 ^ 34) n3.le (by norm_num) (fun k hk ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        Decoder.decStmtC.lam2.costEq P (by includes) rd rdV hrd]
      have := sphincsAt_cost P hrd hR (by includes) (σ (.n 56)) k (by omega)
      omega)
  have hd := daDigestAt_cost P hrd hR hσ hS (by includes) (gLog (σ (.n 387))) (by omega)
  have hc := readCells_cost P hrd hR (by includes) (σ (.n 402)) 24 (by norm_num)
  have hf := deferOfCells_cost P (by includes) (readCells rd (σ (.n 402)) 24)
  have := hS (.n 0)
  have := hS (.n 3)
  have := hS (.n 53)
  have := hS (.n 56)
  have := hS (.n 387)
  have := hS (.n 402)
  unfold decStmtPrice
  omega

/-- The sumcheck's rounds the batching hints (`aggRoundsC`): at most `46·S + 46·R + 998678`. -/
theorem aggRounds_cost (hP : Includes P Decoder.aggRoundsC.costDeps) :
    machineCost P Decoder.aggRoundsC.costIdx [rdV, σV] ≤ 46 * S + 46 * R + 998678 := by
  rw [Decoder.aggRoundsC.costEq P hP rd rdV hrd σ σV hσ]
  have m := rangeMap_le P (by includes) (by includes) _
    (.closure Decoder.aggRoundsC.lam0.costIdx [rdV, σV])
    (fun k ↦ RunsApp.of_spec (Decoder.aggRoundsC.lam0.costSpec P (by includes) rd rdV hrd σ σV hσ k))
    (2 * S + 2 * R + 43392) 23 23 le_rfl (by norm_num) (fun k hk ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        Decoder.aggRoundsC.lam0.costEq P (by includes) rd rdV hrd σ σV hσ]
      have := memAt_cost P hrd hR (by includes) (σ (.n 5)) (2 * k) (by omega)
      have := memAt_cost P hrd hR (by includes) (σ (.n 5)) (2 * k + 1) (by omega)
      have := hS (.n 5)
      limbs_one
      omega)
  omega

/-- **The batching's hints** (`aggHintsC`): at most `47·S + 46·R + 998693`. -/
theorem aggHints_cost (hP : Includes P Decoder.aggHintsC.costDeps) :
    machineCost P Decoder.aggHintsC.costIdx [rdV, σV] ≤ 47 * S + 46 * R + 998693 := by
  rw [Decoder.aggHintsC.costEq P hP rd rdV hrd σ σV hσ]
  have := aggRounds_cost P hσ hS hrd hR (by includes)
  have := hS (.n 6)
  omega

end Reader

end Val

end

end LeanVM.Cost.Bounds.Guest
