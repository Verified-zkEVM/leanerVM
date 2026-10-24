/-
  LeanVM.Guest.Count.VsOs24

  `open_stacked`'s words at candidate 24, by the kernel.
-/

module

public import LeanVM.Guest.Count.VsBoundBase

namespace LeanVM.Guest.Count

@[expose] public section

set_option maxRecDepth 100000 in
theorem osC_24 : osC 24 = 156694 := by
  rw [osC_eq_fast]; decide +kernel

end
end LeanVM.Guest.Count
