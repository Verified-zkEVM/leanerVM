/-
  LeanVM.Guest.Count.VsOs13

  `open_stacked`'s words at candidate 13, by the kernel.
-/

module

public import LeanVM.Guest.Count.VsBoundBase

namespace LeanVM.Guest.Count

@[expose] public section

set_option maxRecDepth 100000 in
theorem osC_13 : osC 13 = 262375 := by
  rw [osC_eq_fast]; decide +kernel

end
end LeanVM.Guest.Count
