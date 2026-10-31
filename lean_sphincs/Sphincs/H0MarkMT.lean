import Sphincs.H0Mark
import Sphincs.H0Moments

/-! **Marks as tuples.** A digest's mark of one tree (`CoordMark`) is the tuple `MT` of
`H0Moments.lean`, and the uniform field values are the uniform tuples (`fieldMT`). Apart from
`H0Moments.lean`, so that its moments, which the kernel-checked tables read, do not depend on the
scheme. -/

namespace SphincsLayered.Security.H0

open Concrete

set_option linter.unusedSectionVars false

def toMT (m : CoordMark) : MT := (m.super, fun j => (m.child j, m.word j))

def ofMT (x : MT) : CoordMark := ⟨x.1, fun j => (x.2 j).1, fun j => (x.2 j).2⟩

/-- Fields are uniform tuples. -/
def fieldMT : FieldVal ≃ MT where
  toFun v := toMT (markEquiv v)
  invFun x := markEquiv.symm (ofMT x)
  left_inv v := by
    simp only [toMT, ofMT]
    rw [show (⟨(markEquiv v).super, fun j => (markEquiv v).child j, fun j => (markEquiv v).word j⟩ : CoordMark) =
      markEquiv v from rfl, Equiv.symm_apply_apply]
  right_inv x := by
    simp only [Equiv.apply_symm_apply, toMT, ofMT]

end SphincsLayered.Security.H0
