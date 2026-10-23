/-
  LeanVM.Guest.B1.Da.VectorChain3

  `da_vector_cell`'s chain blocks 30 to 37, checked by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Da.Vector

namespace LeanVM.Guest.B1.Da

@[expose] public section

set_option maxRecDepth 100000 in
theorem vec_chain3_ok : (vecSpec vecTail).partOk vecTail 30 38 = true := by decide +kernel

end
end LeanVM.Guest.B1.Da
