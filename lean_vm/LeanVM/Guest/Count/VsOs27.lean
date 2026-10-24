/-
  LeanVM.Guest.Count.VsOs27

  `open_stacked`'s words at candidate 27, by the kernel.
-/

module

public import LeanVM.Guest.Count.VsBoundBase

namespace LeanVM.Guest.Count

@[expose] public section

set_option maxRecDepth 100000 in
theorem osC_27 : osC 27 = 184655 := by
  rw [osC_eq_fast]; decide +kernel

end
end LeanVM.Guest.Count
