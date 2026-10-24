/-
  LeanVM.Guest.Count.VsOs12

  `open_stacked`'s words at candidate 12, by the kernel.
-/

module

public import LeanVM.Guest.Count.VsBoundBase

namespace LeanVM.Guest.Count

@[expose] public section

set_option maxRecDepth 100000 in
theorem osC_12 : osC 12 = 243802 := by
  rw [osC_eq_fast]; decide +kernel

end
end LeanVM.Guest.Count
