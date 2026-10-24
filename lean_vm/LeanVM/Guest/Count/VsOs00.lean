/-
  LeanVM.Guest.Count.VsOs00

  `open_stacked`'s words at candidate 0, by the kernel.
-/

module

public import LeanVM.Guest.Count.VsBoundBase

namespace LeanVM.Guest.Count

@[expose] public section

set_option maxRecDepth 100000 in
theorem osC_0 : osC 0 = 305139 := by
  rw [osC_eq_fast]; decide +kernel

end
end LeanVM.Guest.Count
