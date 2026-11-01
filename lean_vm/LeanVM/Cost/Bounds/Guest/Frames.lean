module

public import LeanVM.Cost.Bounds.Guest.Whir
public import LeanVM.Cost.Bounds.Guest.Da
public import LeanVM.Cost.Decoder.Witness

/-!
# Bounds on the guest decoder's prices: each callee's witness off its frame

`Cost/Decoder/Frames.lean`: a callee's witness at its call's frame `Vn k args rets`, a closure of
the frame map whose application costs at most `F + 6` (`F` the frame map's price), and the closures
`decWitNC` hands to `decWitC` (`decWitNC.lam0 … lam4`), the callees' witness functions:

* `xmssAtFrame_cost` (`458·F + 717182`), `sphincsAtFrame_cost` (`S + 450·F + 1663653`),
  `daAtFrame_cost`, `proofAtFrame_cost`, `hintsAtFrame_cost`;
* `wX_cost` … `wA_cost`: the five closures' prices, `xmssW F`, …, the bounds `decWitC`'s takes.
-/

namespace LeanVM.Cost.Bounds.Guest

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.Fast

public section

variable (P : MachineProgram) {G : ℕ}

section Frames

variable {Vn : NFrames} {VnV : MachineValue}
  (hVn : ∀ (k : ℕ) (a r : List E) (v : V),
    RunsApp P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v]
      (encodeValue (Vn k a r v)))
  {F : ℕ} (hF : ∀ (k : ℕ) (a r : List E) (v : V),
    appCost P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v] ≤ F)
include hVn hF

/-- **A leanXMSS signature off its check's frame** (`xmssAtFrameC`): `458·F + 717182`. -/
theorem xmssAtFrame_cost (hP : Includes P Decoder.xmssAtFrameC.costDeps) (p : E) :
    machineCost P Decoder.xmssAtFrameC.costIdx [VnV, encodeValue p] ≤ 458 * F + 717182 := by
  rw [Decoder.xmssAtFrameC.costEq P hP Vn VnV hVn]
  have hσ : ∀ v : V, RunsApp P (.closure Decoder.xmssAtFrameC.lam0.costIdx
      [VnV, encodeValue [p], encodeValue ([] : List E)]) [encodeValue v]
      (encodeValue (Vn 20 [p] [] v)) :=
    fun v ↦ RunsApp.of_spec (Decoder.xmssAtFrameC.lam0.costSpec P (by includes) Vn VnV hVn _ _ v)
  have hS : ∀ v : V, appCost P (.closure Decoder.xmssAtFrameC.lam0.costIdx
      [VnV, encodeValue [p], encodeValue ([] : List E)]) [encodeValue v] ≤ F + 6 := fun v ↦ by
    rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
      Decoder.xmssAtFrameC.lam0.costEq P (by includes) Vn VnV hVn]
    have := hF 20 [p] [] v; omega
  have := xmssSigOfN_cost P hσ hS (by includes)
  omega

/-- **A leanSPHINCS signature off its check's frame** (`sphincsAtFrameC`), at `main`'s valuation
of price `S`: `S + 450·F + 1663653`. -/
theorem sphincsAtFrame_cost (hP : Includes P Decoder.sphincsAtFrameC.costDeps) {σ : Val}
    {σV : MachineValue} (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
    {S : ℕ} (hS : ∀ v : V, appCost P σV [encodeValue v] ≤ S) (p : E) :
    machineCost P Decoder.sphincsAtFrameC.costIdx [σV, VnV, encodeValue p] ≤
      S + 450 * F + 1663653 := by
  rw [Decoder.sphincsAtFrameC.costEq P hP σ σV hσ Vn VnV hVn]
  have hσ' : ∀ v : V, RunsApp P (.closure Decoder.sphincsAtFrameC.lam0.costIdx
      [VnV, encodeValue [p, σ (.n 68)], encodeValue ([] : List E)]) [encodeValue v]
      (encodeValue (Vn 21 [p, σ (.n 68)] [] v)) :=
    fun v ↦ RunsApp.of_spec (Decoder.sphincsAtFrameC.lam0.costSpec P (by includes) Vn VnV hVn _ _ v)
  have hS' : ∀ v : V, appCost P (.closure Decoder.sphincsAtFrameC.lam0.costIdx
      [VnV, encodeValue [p, σ (.n 68)], encodeValue ([] : List E)]) [encodeValue v] ≤ F + 6 :=
    fun v ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
        Decoder.sphincsAtFrameC.lam0.costEq P (by includes) Vn VnV hVn]
      have := hF 21 [p, σ (.n 68)] [] v; omega
  have := sphincsSigOfN_cost P hσ' hS' (by includes)
  have := hS (.n 68)
  omega

/-- **The DA matrix off `da_verify`'s frame** (`daAtFrameC`), the logarithm's tables `D` given:
`F + 6 + G + dvWitNAtPrice F (F + 6) + 24`. -/
theorem daAtFrame_cost (D : LeanVM.Extraction.Fast.DiscreteLogTables)
    (hP : Includes P Decoder.daAtFrameC.costDeps) (hG : GLogBound P D G) (args rets : List E) :
    machineCost P Decoder.daAtFrameC.costIdx [encodeValue D, VnV, encodeValue args, encodeValue rets] ≤
      F + 6 + G + dvWitNAtPrice F (F + 6) + 24 := by
  rw [Decoder.daAtFrameC.costEq P hP D Vn VnV hVn]
  have hσ : ∀ v : V, RunsApp P (.closure Decoder.daAtFrameC.lam0.costIdx
      [VnV, encodeValue args, encodeValue rets]) [encodeValue v]
      (encodeValue (Vn 26 args rets v)) :=
    fun v ↦ RunsApp.of_spec (Decoder.daAtFrameC.lam0.costSpec P (by includes) Vn VnV hVn _ _ v)
  have hS : ∀ v : V, appCost P (.closure Decoder.daAtFrameC.lam0.costIdx
      [VnV, encodeValue args, encodeValue rets]) [encodeValue v] ≤ F + 6 := fun v ↦ by
    rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
      Decoder.daAtFrameC.lam0.costEq P (by includes) Vn VnV hVn]
    have := hF 26 args rets v; omega
  have := dvWitN_cost P hVn hF hσ hS D (by includes) hG
  omega

/-- **A child's proof off its `verify_sub` frame** (`proofAtFrameC`): `vsPiPrice R (F + 6) F C L
+ 11`. -/
theorem proofAtFrame_cost (hP : Includes P Decoder.proofAtFrameC.costDeps) {rd : Reader}
    {rdV : MachineValue} (hrd : ∀ a : K, RunsApp P rdV [encodeValue a] (encodeValue (rd a)))
    {R : ℕ} (hR : ∀ a : K, appCost P rdV [encodeValue a] ≤ R) {cl : E → E → ℕ} {clV : MachineValue}
    (hcl : ∀ a b : E, RunsApp P clV [encodeValue a, encodeValue b] (encodeValue (cl a b)))
    {C : ℕ} (hC : ∀ a b : E, appCost P clV [encodeValue a, encodeValue b] ≤ C)
    {L : ℕ} (hL : ∀ a b : E, cl a b ≤ L) (hL32 : L ≤ 2 ^ 32) (args : List E) :
    machineCost P Decoder.proofAtFrameC.costIdx [rdV, VnV, clV, encodeValue args] ≤
      vsPiPrice R (F + 6) F C L + 11 := by
  rw [Decoder.proofAtFrameC.costEq P hP rd rdV hrd Vn VnV hVn cl clV hcl]
  have hσ : ∀ v : V, RunsApp P (.closure Decoder.proofAtFrameC.lam0.costIdx
      [VnV, encodeValue args, encodeValue ([] : List E)]) [encodeValue v]
      (encodeValue (Vn 19 args [] v)) :=
    fun v ↦ RunsApp.of_spec (Decoder.proofAtFrameC.lam0.costSpec P (by includes) Vn VnV hVn _ _ v)
  have hS : ∀ v : V, appCost P (.closure Decoder.proofAtFrameC.lam0.costIdx
      [VnV, encodeValue args, encodeValue ([] : List E)]) [encodeValue v] ≤ F + 6 := fun v ↦ by
    rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
      Decoder.proofAtFrameC.lam0.costEq P (by includes) Vn VnV hVn]
    have := hF 19 args [] v; omega
  have := vsPiOfN_cost P hrd hR hσ hS hVn hF hcl hC hL hL32 (by includes)
  omega

/-- **The batching's hints off `aggregate_claims`' frame** (`hintsAtFrameC`):
`47·F + 46·R + 998984`. -/
theorem hintsAtFrame_cost (hP : Includes P Decoder.hintsAtFrameC.costDeps) {rd : Reader}
    {rdV : MachineValue} (hrd : ∀ a : K, RunsApp P rdV [encodeValue a] (encodeValue (rd a)))
    {R : ℕ} (hR : ∀ a : K, appCost P rdV [encodeValue a] ≤ R) (args : List E) :
    machineCost P Decoder.hintsAtFrameC.costIdx [rdV, VnV, encodeValue args] ≤
      47 * F + 46 * R + 998984 := by
  rw [Decoder.hintsAtFrameC.costEq P hP rd rdV hrd Vn VnV hVn]
  have hσ : ∀ v : V, RunsApp P (.closure Decoder.hintsAtFrameC.lam0.costIdx
      [VnV, encodeValue args, encodeValue ([] : List E)]) [encodeValue v]
      (encodeValue (Vn 30 args [] v)) :=
    fun v ↦ RunsApp.of_spec (Decoder.hintsAtFrameC.lam0.costSpec P (by includes) Vn VnV hVn _ _ v)
  have hS : ∀ v : V, appCost P (.closure Decoder.hintsAtFrameC.lam0.costIdx
      [VnV, encodeValue args, encodeValue ([] : List E)]) [encodeValue v] ≤ F + 6 := fun v ↦ by
    rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
      Decoder.hintsAtFrameC.lam0.costEq P (by includes) Vn VnV hVn]
    have := hF 30 args [] v; omega
  have := aggHints_cost P hσ hS hrd hR (by includes)
  omega

end Frames

end

end LeanVM.Cost.Bounds.Guest
