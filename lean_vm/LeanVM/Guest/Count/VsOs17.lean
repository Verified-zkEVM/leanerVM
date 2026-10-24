/-
  LeanVM.Guest.Count.VsOs17

  `open_stacked`'s words at candidate 17, by the kernel.
-/

module

public import LeanVM.Guest.Count.VsBoundBase

namespace LeanVM.Guest.Count

@[expose] public section

set_option maxRecDepth 100000 in
theorem osC_17 : osC 17 = 184847 := by
  rw [osC_eq_fast]; decide +kernel

end
end LeanVM.Guest.Count
