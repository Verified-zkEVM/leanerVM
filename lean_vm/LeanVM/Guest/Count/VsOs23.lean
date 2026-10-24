/-
  LeanVM.Guest.Count.VsOs23

  `open_stacked`'s words at candidate 23, by the kernel.
-/

module

public import LeanVM.Guest.Count.VsBoundBase

namespace LeanVM.Guest.Count

@[expose] public section

set_option maxRecDepth 100000 in
theorem osC_23 : osC 23 = 152498 := by
  rw [osC_eq_fast]; decide +kernel

end
end LeanVM.Guest.Count
