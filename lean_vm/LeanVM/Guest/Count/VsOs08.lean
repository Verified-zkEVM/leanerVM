/-
  LeanVM.Guest.Count.VsOs08

  `open_stacked`'s words at candidate 8, by the kernel.
-/

module

public import LeanVM.Guest.Count.VsBoundBase

namespace LeanVM.Guest.Count

@[expose] public section

set_option maxRecDepth 100000 in
theorem osC_8 : osC 8 = 201647 := by
  rw [osC_eq_fast]; decide +kernel

end
end LeanVM.Guest.Count
