/-
  LeanVM.Guest.Count.VsOs18

  `open_stacked`'s words at candidate 18, by the kernel.
-/

module

public import LeanVM.Guest.Count.VsBoundBase

namespace LeanVM.Guest.Count

@[expose] public section

set_option maxRecDepth 100000 in
theorem osC_18 : osC 18 = 190581 := by
  rw [osC_eq_fast]; decide +kernel

end
end LeanVM.Guest.Count
