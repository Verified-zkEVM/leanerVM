/-
  LeanVM.Guest.Count.VsOs14

  `open_stacked`'s words at candidate 14, by the kernel.
-/

module

public import LeanVM.Guest.Count.VsBoundBase

namespace LeanVM.Guest.Count

@[expose] public section

set_option maxRecDepth 100000 in
theorem osC_14 : osC 14 = 155194 := by
  rw [osC_eq_fast]; decide +kernel

end
end LeanVM.Guest.Count
