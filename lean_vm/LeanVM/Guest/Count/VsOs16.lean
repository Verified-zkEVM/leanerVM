/-
  LeanVM.Guest.Count.VsOs16

  `open_stacked`'s words at candidate 16, by the kernel.
-/

module

public import LeanVM.Guest.Count.VsBoundBase

namespace LeanVM.Guest.Count

@[expose] public section

set_option maxRecDepth 100000 in
theorem osC_16 : osC 16 = 179059 := by
  rw [osC_eq_fast]; decide +kernel

end
end LeanVM.Guest.Count
