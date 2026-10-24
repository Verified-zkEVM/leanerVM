/-
  LeanVM.Guest.Count.VsOs22

  `open_stacked`'s words at candidate 22, by the kernel.
-/

module

public import LeanVM.Guest.Count.VsBoundBase

namespace LeanVM.Guest.Count

@[expose] public section

set_option maxRecDepth 100000 in
theorem osC_22 : osC 22 = 135951 := by
  rw [osC_eq_fast]; decide +kernel

end
end LeanVM.Guest.Count
