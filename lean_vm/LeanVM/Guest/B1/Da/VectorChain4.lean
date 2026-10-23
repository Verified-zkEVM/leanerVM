/-
  LeanVM.Guest.B1.Da.VectorChain4

  `da_vector_cell`'s chain blocks 38 to 45, checked by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Da.Vector

namespace LeanVM.Guest.B1.Da

@[expose] public section

set_option maxRecDepth 100000 in
theorem vec_chain4_ok : (vecSpec vecTail).partOk vecTail 38 46 = true := by decide +kernel

end
end LeanVM.Guest.B1.Da
