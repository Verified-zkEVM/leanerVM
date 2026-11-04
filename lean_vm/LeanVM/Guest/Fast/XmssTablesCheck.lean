module

public import LeanVM.Guest.Fast.XmssTables
public import LeanVM.Guest.Fast.Numbers
public import LeanVM.Guest.B1.Sig.XmssT
public import LeanVM.Guest.B1.Sig.Merkle

/-!
# leanXMSS's tables, checked

The literal tables of `Fast/XmssTables.lean` are the template generators' numbers, by kernel
evaluation: the bottom layer ends at `12622` (`xLayer0_end`), the layers' selector cells
(`selN`, `Fast/Numbers.lean`) and path bases (`mBase` over `xLeafK`), the chain starts' tables
(`offTab 1`).
-/

namespace LeanVM.Guest.Fast

open LeanVM.Guest.Core LeanVM.Guest.B1.Sig

@[expose] public section

theorem xLayer0_end : (xLayer 0 196 (.n 0)).2.1 = 12622 := by decide +kernel

theorem xSel0_eq : xSel0 = (List.range 20).map (selN 1 230) := by decide +kernel

theorem xSel1_eq : xSel1 = (List.range 20).map (selN 1 12647) := by decide +kernel

theorem xPath0_eq :
    xPath0 = (List.range 16).map fun l ↦ mBase (xNodeOf 0) 0 l (xLeafK 0 196).2.1 := by
  decide +kernel

theorem xPath1_eq :
    xPath1 = (List.range 16).map fun l ↦ mBase (xNodeOf 1) 0 l (xLeafK 1 12622).2.1 := by
  decide +kernel

theorem xTabs : WotsTabs 1 xFirst xRest xLast :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

end
end LeanVM.Guest.Fast
