/-
  LeanVM.Guest.Count.VsOs09

  `open_stacked`'s words at candidate 9, by the kernel.
-/

module

public import LeanVM.Guest.Count.VsBoundBase

namespace LeanVM.Guest.Count

@[expose] public section

set_option maxRecDepth 100000 in
theorem osC_9 : osC 9 = 221871 := by
  rw [osC_eq_fast]; decide +kernel

end
end LeanVM.Guest.Count
