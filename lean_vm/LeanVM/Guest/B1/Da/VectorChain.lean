/-
  LeanVM.Guest.B1.Da.VectorChain

  `da_vector_cell`'s tail, checked by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Da.Vector

namespace LeanVM.Guest.B1.Da

@[expose] public section

set_option maxRecDepth 100000 in
theorem vec_tail_ok : vecTailOk = true := by decide +kernel

end
end LeanVM.Guest.B1.Da
