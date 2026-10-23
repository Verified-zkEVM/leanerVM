/-
  LeanVM.Guest.B1.Da.VectorChain0

  `da_vector_cell`'s chain blocks 0 to 9, checked by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Da.Vector

namespace LeanVM.Guest.B1.Da

@[expose] public section

set_option maxRecDepth 100000 in
theorem vec_chain0_ok : (vecSpec vecTail).partOk vecTail 0 10 = true := by decide +kernel

end
end LeanVM.Guest.B1.Da
