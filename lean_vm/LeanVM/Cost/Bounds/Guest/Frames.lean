module

public import LeanVM.Cost.Bounds.Guest.Whir
public import LeanVM.Cost.Bounds.Guest.Stmt
public import LeanVM.Cost.Decoder.Witness

/-!
# Bounds on the guest decoder's prices: each callee's witness off its frame

`Cost/Decoder/Frames.lean`: a callee's witness at its call's frame `Vn k args rets`, a closure of
the frame map whose application costs at most `F + 6` (`F` the frame map's price), and the closures
`decWitNC` hands to `decWitC` (`decWitNC.lam0 … lam4`), the callees' witness functions:

* `xmssAtFrame_cost` (`458·F + 214100`), `sphincsAtFrame_cost` (`S + 450·F + 244100`), the
  readers' tables `Tb` given (`ReaderTabsOK`, `readerTabs_ok`),
  `daAtFrame_cost` (`dvWitNC`'s price `DW` at the frame a parameter, `daFrame_runs`, `daFrame_cost`:
  the frame's spec and price for `Da.lean`'s bound), `proofAtFrame_cost`, `hintsAtFrame_cost`;
* `wX_cost` … `wA_cost`: the five closures `decWitNC` passes to `decWitC`, their prices.
-/

namespace LeanVM.Cost.Bounds.Guest

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.Fast

public section

variable (P : MachineProgram) {G : ℕ}

/-- The readers' tables, their entries small (`readerTabs_ok`). -/
structure ReaderTabsOK (Tb : ReaderTabs) : Prop where
  xmss : XmssTabsOK Tb.xmss
  sphincs : SphincsTabsOK Tb.sphincs
  whir : WhirTabsOK Tb.whir

theorem readerTabs_ok : ReaderTabsOK readerTabs := ⟨xmssTabs_ok, sphincsTabs_ok, whirTabs_ok⟩

/-- **The readers' tables, built once per decoding** (`readerTabsC`): at most `44537`. -/
theorem readerTabs_cost (hP : Includes P Decoder.readerTabsC.costDeps) :
    machineCost P Decoder.readerTabsC.costIdx [] ≤ 44537 := by
  rw [Decoder.readerTabsC.costEq P hP]
  have := xmssTabs_cost P (by includes)
  have := sphincsTabs_cost P (by includes)
  have := whirTabs_cost P (by includes)
  omega

section Frames

variable {Vn : NFrames} {VnV : MachineValue}
  (hVn : ∀ (k : ℕ) (a r : List E) (v : V),
    RunsApp P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v]
      (encodeValue (Vn k a r v)))
  {F : ℕ} (hF : ∀ (k : ℕ) (a r : List E) (v : V),
    appCost P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v] ≤ F)
include hVn hF

/-- **A leanXMSS signature off its check's frame** (`xmssAtFrameC`), the readers' tables `Tb`
given: `458·F + 214100`. -/
theorem xmssAtFrame_cost (hP : Includes P Decoder.xmssAtFrameC.costDeps) (Tb : ReaderTabs)
    (hTb : ReaderTabsOK Tb) (p : E) :
    machineCost P Decoder.xmssAtFrameC.costIdx [encodeValue Tb, VnV, encodeValue p] ≤
      458 * F + 214100 := by
  rw [Decoder.xmssAtFrameC.costEq P hP Tb Vn VnV hVn]
  have hσ : ∀ v : V, RunsApp P (.closure Decoder.xmssAtFrameC.lam0.costIdx
      [VnV, encodeValue [p], encodeValue ([] : List E)]) [encodeValue v]
      (encodeValue (Vn 20 [p] [] v)) :=
    fun v ↦ RunsApp.of_spec (Decoder.xmssAtFrameC.lam0.costSpec P (by includes) Vn VnV hVn _ _ v)
  have hS : ∀ v : V, appCost P (.closure Decoder.xmssAtFrameC.lam0.costIdx
      [VnV, encodeValue [p], encodeValue ([] : List E)]) [encodeValue v] ≤ F + 6 := fun v ↦ by
    rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
      Decoder.xmssAtFrameC.lam0.costEq P (by includes) Vn VnV hVn]
    have := hF 20 [p] [] v; omega
  have := xmssSigOfN_cost P hσ hS (by includes) Tb.xmss hTb.xmss
  omega

/-- **A leanSPHINCS signature off its check's frame** (`sphincsAtFrameC`), the readers' tables
`Tb` given, at `main`'s valuation of price `S`: `S + 450·F + 244100`. -/
theorem sphincsAtFrame_cost (hP : Includes P Decoder.sphincsAtFrameC.costDeps) (Tb : ReaderTabs)
    (hTb : ReaderTabsOK Tb) {σ : Val}
    {σV : MachineValue} (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
    {S : ℕ} (hS : ∀ v : V, appCost P σV [encodeValue v] ≤ S) (p : E) :
    machineCost P Decoder.sphincsAtFrameC.costIdx [encodeValue Tb, σV, VnV, encodeValue p] ≤
      S + 450 * F + 244100 := by
  rw [Decoder.sphincsAtFrameC.costEq P hP Tb σ σV hσ Vn VnV hVn]
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
  have := sphincsSigOfN_cost P hσ' hS' (by includes) Tb.sphincs hTb.sphincs
  have := hS (.n 68)
  omega

omit hF in
/-- **The DA matrix off `da_verify`'s frame** (`daAtFrameC`), the logarithm's tables `D` given,
`da_verify`'s witness (`dvWitNC`) at that frame at most `DW` (`Bounds/Guest/Da.lean`): `DW + 10`. -/
theorem daAtFrame_cost (D : LeanVM.Extraction.Fast.DiscreteLogTables)
    (hP : Includes P Decoder.daAtFrameC.costDeps) (DW : ℕ)
    (hDW : ∀ args rets : List E, machineCost P Decoder.dvWitNC.costIdx
      [encodeValue D, .closure Decoder.daAtFrameC.lam0.costIdx [VnV, encodeValue args, encodeValue rets],
        VnV] ≤ DW) (args rets : List E) :
    machineCost P Decoder.daAtFrameC.costIdx [encodeValue D, VnV, encodeValue args, encodeValue rets] ≤
      DW + 10 := by
  rw [Decoder.daAtFrameC.costEq P hP D Vn VnV hVn]
  have := hDW args rets
  omega

omit hF in
/-- `da_verify`'s frame (`daAtFrameC.lam0`), the valuation `dvWitNC` takes: its spec. -/
theorem daFrame_runs (hP : Includes P Decoder.daAtFrameC.lam0.costDeps) (args rets : List E) (v : V) :
    RunsApp P (.closure Decoder.daAtFrameC.lam0.costIdx [VnV, encodeValue args, encodeValue rets])
      [encodeValue v] (encodeValue (Vn 26 args rets v)) :=
  RunsApp.of_spec (Decoder.daAtFrameC.lam0.costSpec P hP Vn VnV hVn _ _ v)

/-- `da_verify`'s frame (`daAtFrameC.lam0`): its price `F + 6`. -/
theorem daFrame_cost (hP : Includes P Decoder.daAtFrameC.lam0.costDeps) (args rets : List E) (v : V) :
    appCost P (.closure Decoder.daAtFrameC.lam0.costIdx [VnV, encodeValue args, encodeValue rets])
      [encodeValue v] ≤ F + 6 := by
  rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
    Decoder.daAtFrameC.lam0.costEq P hP Vn VnV hVn]
  have := hF 26 args rets v; omega

/-- **A child's proof off its `verify_sub` frame** (`proofAtFrameC`), the readers' tables `Tb`
given: `vsPiPrice R (F + 6) F C L + 20`. -/
theorem proofAtFrame_cost (hP : Includes P Decoder.proofAtFrameC.costDeps) (Tb : ReaderTabs)
    (hTb : ReaderTabsOK Tb) {rd : Reader}
    {rdV : MachineValue} (hrd : ∀ a : K, RunsApp P rdV [encodeValue a] (encodeValue (rd a)))
    {R : ℕ} (hR : ∀ a : K, appCost P rdV [encodeValue a] ≤ R) {cl : E → E → ℕ} {clV : MachineValue}
    (hcl : ∀ a b : E, RunsApp P clV [encodeValue a, encodeValue b] (encodeValue (cl a b)))
    {C : ℕ} (hC : ∀ a b : E, appCost P clV [encodeValue a, encodeValue b] ≤ C)
    {L : ℕ} (hL : ∀ a b : E, cl a b ≤ L) (hL32 : L ≤ 2 ^ 32) (args : List E) :
    machineCost P Decoder.proofAtFrameC.costIdx [encodeValue Tb, rdV, VnV, clV, encodeValue args] ≤
      vsPiPrice R (F + 6) F C L + 20 := by
  rw [Decoder.proofAtFrameC.costEq P hP Tb rd rdV hrd Vn VnV hVn cl clV hcl]
  have hσ : ∀ v : V, RunsApp P (.closure Decoder.proofAtFrameC.lam0.costIdx
      [VnV, encodeValue args, encodeValue ([] : List E)]) [encodeValue v]
      (encodeValue (Vn 19 args [] v)) :=
    fun v ↦ RunsApp.of_spec (Decoder.proofAtFrameC.lam0.costSpec P (by includes) Vn VnV hVn _ _ v)
  have hS : ∀ v : V, appCost P (.closure Decoder.proofAtFrameC.lam0.costIdx
      [VnV, encodeValue args, encodeValue ([] : List E)]) [encodeValue v] ≤ F + 6 := fun v ↦ by
    rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
      Decoder.proofAtFrameC.lam0.costEq P (by includes) Vn VnV hVn]
    have := hF 19 args [] v; omega
  have := vsPiOfN_cost P hrd hR hσ hS hVn hF hcl hC hL hL32 (by includes) Tb.whir hTb.whir
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

/-! ## The callees' witness functions `decWitNC` passes -/

section Closures

variable {Vn : NFrames} {VnV : MachineValue}
  (hVn : ∀ (k : ℕ) (a r : List E) (v : V),
    RunsApp P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v]
      (encodeValue (Vn k a r v)))
  {F : ℕ} (hF : ∀ (k : ℕ) (a r : List E) (v : V),
    appCost P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v] ≤ F)
  {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, appCost P σV [encodeValue v] ≤ S)
  {rd : Reader} {rdV : MachineValue}
  (hrd : ∀ a : K, RunsApp P rdV [encodeValue a] (encodeValue (rd a)))
  {R : ℕ} (hR : ∀ a : K, appCost P rdV [encodeValue a] ≤ R)
  {cl : E → E → ℕ} {clV : MachineValue}
  (hcl : ∀ a b : E, RunsApp P clV [encodeValue a, encodeValue b] (encodeValue (cl a b)))
  {C : ℕ} (hC : ∀ a b : E, appCost P clV [encodeValue a, encodeValue b] ≤ C)
  {L : ℕ} (hL : ∀ a b : E, cl a b ≤ L) (hL32 : L ≤ 2 ^ 32)

include hVn hF in
/-- The leanXMSS witness function (`decWitNC.lam0`), the readers' tables `Tb` given:
`458·F + 214110`. -/
theorem wX_cost (hP : Includes P Decoder.decWitNC.lam0.costDeps) (Tb : ReaderTabs)
    (hTb : ReaderTabsOK Tb) (p : E) :
    appCost P (.closure Decoder.decWitNC.lam0.costIdx [encodeValue Tb, VnV]) [encodeValue p] ≤
      458 * F + 214110 := by
  rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
    Decoder.decWitNC.lam0.costEq P hP Tb Vn VnV hVn]
  have := xmssAtFrame_cost P hVn hF (by includes) Tb hTb p
  omega

include hVn hF hσ hS in
/-- The leanSPHINCS witness function (`decWitNC.lam1`), the readers' tables `Tb` given:
`S + 450·F + 244110`. -/
theorem wS_cost (hP : Includes P Decoder.decWitNC.lam1.costDeps) (Tb : ReaderTabs)
    (hTb : ReaderTabsOK Tb) (p : E) :
    appCost P (.closure Decoder.decWitNC.lam1.costIdx [encodeValue Tb, σV, VnV]) [encodeValue p] ≤
      S + 450 * F + 244110 := by
  rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
    Decoder.decWitNC.lam1.costEq P hP Tb σ σV hσ Vn VnV hVn]
  have := sphincsAtFrame_cost P hVn hF (by includes) Tb hTb hσ hS p
  omega

include hVn in
/-- The DA witness function (`decWitNC.lam2`), the logarithm's tables `D` given, `dvWitNC` at
`da_verify`'s frame at most `DW`: `DW + 15`. -/
theorem wD_cost (D : LeanVM.Extraction.Fast.DiscreteLogTables)
    (hP : Includes P Decoder.decWitNC.lam2.costDeps) (DW : ℕ)
    (hDW : ∀ args rets : List E, machineCost P Decoder.dvWitNC.costIdx
      [encodeValue D, .closure Decoder.daAtFrameC.lam0.costIdx [VnV, encodeValue args, encodeValue rets],
        VnV] ≤ DW) (args rets : List E) :
    appCost P (.closure Decoder.decWitNC.lam2.costIdx [encodeValue D, VnV])
      [encodeValue args, encodeValue rets] ≤ DW + 15 := by
  rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
    Decoder.decWitNC.lam2.costEq P hP D Vn VnV hVn]
  have := daAtFrame_cost P hVn D (by includes) DW hDW args rets
  omega

include hVn hF hrd hR hcl hC hL hL32 in
/-- The child proofs' witness function (`decWitNC.lam3`), the readers' tables `Tb` given:
`vsPiPrice R (F + 6) F C L + 30`. -/
theorem wV_cost (hP : Includes P Decoder.decWitNC.lam3.costDeps) (Tb : ReaderTabs)
    (hTb : ReaderTabsOK Tb) (args : List E) :
    appCost P (.closure Decoder.decWitNC.lam3.costIdx [encodeValue Tb, rdV, VnV, clV])
      [encodeValue args] ≤ vsPiPrice R (F + 6) F C L + 30 := by
  rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
    List.nil_append, Decoder.decWitNC.lam3.costEq P hP Tb rd rdV hrd Vn VnV hVn cl clV hcl]
  have := proofAtFrame_cost P hVn hF (by includes) Tb hTb hrd hR hcl hC hL hL32 args
  omega

include hVn hF hrd hR in
/-- The batching hints' witness function (`decWitNC.lam4`): `47·F + 46·R + 998988`. -/
theorem wA_cost (hP : Includes P Decoder.decWitNC.lam4.costDeps) (args : List E) :
    appCost P (.closure Decoder.decWitNC.lam4.costIdx [rdV, VnV]) [encodeValue args] ≤
      47 * F + 46 * R + 998988 := by
  rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
    Decoder.decWitNC.lam4.costEq P hP rd rdV hrd Vn VnV hVn]
  have := hintsAtFrame_cost P hVn hF (by includes) hrd hR args
  omega

end Closures

end

end LeanVM.Cost.Bounds.Guest
