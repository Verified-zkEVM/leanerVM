/-
  LeanVM.Guest.Count.VsOs21

  `open_stacked`'s words at candidate 21, by the kernel.
-/

module

public import LeanVM.Guest.Count.VsBoundBase

namespace LeanVM.Guest.Count

@[expose] public section

set_option maxRecDepth 100000 in
theorem osC_21 : osC 21 = 131990 := by
  rw [osC_eq_fast]; decide +kernel

end
end LeanVM.Guest.Count
