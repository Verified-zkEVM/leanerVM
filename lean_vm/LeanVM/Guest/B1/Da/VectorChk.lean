/-
  LeanVM.Guest.B1.Da.VectorChk

  `da_vector_cell`'s template, checked by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Da.Vector

namespace LeanVM.Guest.B1.Da

@[expose] public section

set_option maxRecDepth 100000 in
theorem vec_tmpl_ok : vecTmplOk Data.core28 = true := by decide +kernel

end
end LeanVM.Guest.B1.Da
