/-
  LeanVM.Guest.Count.VsOs10

  `open_stacked`'s words at candidate 10, by the kernel.
-/

module

public import LeanVM.Guest.Count.VsBoundBase

namespace LeanVM.Guest.Count

@[expose] public section

set_option maxRecDepth 100000 in
theorem osC_10 : osC 10 = 228805 := by
  rw [osC_eq_fast]; decide +kernel

end
end LeanVM.Guest.Count
