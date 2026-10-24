/-
  LeanVM.Guest.Count.VsOs19

  `open_stacked`'s words at candidate 19, by the kernel.
-/

module

public import LeanVM.Guest.Count.VsBoundBase

namespace LeanVM.Guest.Count

@[expose] public section

set_option maxRecDepth 100000 in
theorem osC_19 : osC 19 = 196413 := by
  rw [osC_eq_fast]; decide +kernel

end
end LeanVM.Guest.Count
