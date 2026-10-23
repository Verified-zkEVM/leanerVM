/-
  LeanVM.Guest.B1.Da.VectorChain1

  `da_vector_cell`'s chain blocks 10 to 19, checked by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Da.Vector

namespace LeanVM.Guest.B1.Da

@[expose] public section

set_option maxRecDepth 100000 in
theorem vec_chain1_ok : (vecSpec vecTail).partOk vecTail 10 20 = true := by decide +kernel

end
end LeanVM.Guest.B1.Da
