/-
  LeanVM.Guest.B1.Da.VectorChain2

  `da_vector_cell`'s chain blocks 20 to 29, checked by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Da.Vector

namespace LeanVM.Guest.B1.Da

@[expose] public section

set_option maxRecDepth 100000 in
theorem vec_chain2_ok : (vecSpec vecTail).partOk vecTail 20 30 = true := by decide +kernel

end
end LeanVM.Guest.B1.Da
