/-
  LeanVM.Guest.Count.VsOs25

  `open_stacked`'s words at candidate 25, by the kernel.
-/

module

public import LeanVM.Guest.Count.VsBoundBase

namespace LeanVM.Guest.Count

@[expose] public section

set_option maxRecDepth 100000 in
theorem osC_25 : osC 25 = 160946 := by
  rw [osC_eq_fast]; decide +kernel

end
end LeanVM.Guest.Count
