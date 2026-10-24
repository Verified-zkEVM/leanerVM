/-
  LeanVM.Guest.B1.Terminal.SelComplete

  `column_selector`, placed, on `selector_tables`' buffers and the point: complete from B1-c's
  `column_selector_complete_holds`, its tables from `selector_tables`' soundness on a memory holding
  its honest buffers.
-/

module

public import LeanVM.Guest.B1.Selectors.SelectorTablesAt
public import LeanVM.Guest.B1.Selectors.ColumnSelectorComplete
public import LeanVM.Guest.B1.Tables.VtC.Kids
public import LeanVM.Guest.B1.Terminal.Template

/-!
# The column selectors, placed

`selector_tables` returns its buffers `stOwn` (B1-c's `selector_tables_completeAt`). On a memory
holding them and the point's words `stLin`, `selector_tables`' statements hold (`st_holds`), so its
soundness puts the opening point's tables there (`selTabs_of_memL`); `column_selector__L{κ}`, pure
and without range checks (`cs_pure`), is then complete by B1-c's `column_selector_complete_holds`
and `completeAt_of_rel_pureD` (`cs_completeAt`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol.Verifier hiding gpow
open LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

theorem cs_pure : coreProgram.PureIn colSelNames := Tables.pureIn_of_pureInB (by decide +kernel)

theorem colSelNames_mem {κ : ℕ} (hκ : κ < 29) : Tables.lName "column_selector" κ ∈ colSelNames :=
  List.mem_map.mpr ⟨κ, List.mem_range.mpr hκ, rfl⟩

/-- **`selector_tables`' honest buffers hold the opening point's tables**, on every memory holding
them and the point. -/
theorem selTabs_of_memL {ept ept1 ese esg : ℕ} {p p1 : List E} (hl : p.length = 28)
    (hl1 : p1.length = 28) {rd : Reader}
    (hm : MemL rd (Tables.stOwn ept ept1 ese esg p p1 ++ Tables.stLin ept ept1 p p1)) :
    Tables.SelTabsAt rd (ofK (gpow ese)) (ofK (gpow esg)) p p1 :=
  Tables.selector_tables_sound (Tables.st_holds ept ept1 ese esg p p1 hl hl1 rd hm) p p1 hl hl1
    (hm (ept, p) (by simp [Tables.stLin])) (hm (ept1, p1) (by simp [Tables.stLin]))

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **`column_selector__L{κ}` is complete, placed**, on `selector_tables`' buffers and the point:
it returns the eq weight of the offset's bits above `κ`. -/
theorem cs_completeAt (k : ℕ) {κ : ℕ} (hκ : κ < 29) {o : ℕ} (ho : o < 2 ^ 28) (hd : 2 ^ κ ∣ o)
    {ept ept1 ese esg : ℕ} {p p1 : List E} (hl : p.length = 28) (hl1 : p1.length = 28) :
    CompleteAtD fs cert k (Tables.lName "column_selector" κ)
      (Tables.stOwn ept ept1 ese esg p p1 ++ Tables.stLin ept ept1 p p1)
      [gen ^ o, ofK (gpow ese), ofK (gpow esg)]
      (Returns [Tables.bitsEq ((List.range (28 - κ)).map fun i ↦ o.testBit (κ + i)) (p.drop κ)
        (p1.drop κ)]) :=
  completeAt_of_rel_pureD cs_pure (colSelNames_mem hκ) (fun rd hm ↦
    have ht := selTabs_of_memL hl hl1 hm
    Tables.column_selector_complete_holds κ hκ rd o _ _ p p1 ho hd hl hl1 ht.1 ht.2) k

end
end LeanVM.Guest.B1.VerifySub
