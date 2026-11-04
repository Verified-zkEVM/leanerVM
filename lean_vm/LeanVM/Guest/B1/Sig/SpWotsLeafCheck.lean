/-
  LeanVM.Guest.B1.Sig.SpWotsLeafCheck

  The leaf's `keccak_cells` of `sp_wots`, for completeness, checked by the kernel: with its padding
  run at the last group's digit cells and moved by `padRen`, it is the template's, its run moved
  by `padShift`; and where its numbers are.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsCheck
public import LeanVM.Guest.B1.Sig.SpWotsPadComplete
import LeanVM.Guest.B1.Sig.Decide

/-!
# The leaf's message, checked

* `spLeafB`: the last group's base, whose digit cells `spLeafB ..< spLeafB + 5` the leaf does not
  read: its message is evaluated with its padding run there;
* `spLeafP`: where the compiler allocates the leaf's padding run;
* `spLeaf_check`: the leaf's message with its run at `spLeafB`, moved by `padRen`, is the
  template's moved by `padShift`; it ends where the template's does; its run goes after the
  checks and before its end; the codeword's product and encoding lie before the checks.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Parameters

@[expose] public section

/-- The last group's base. -/
def spLeafB : Nat := (spState 21).2.2

/-- Where the leaf's padding run goes. -/
def spLeafP : Nat := padBase isKeccak spLeafM.1

/-- The leaf's message with its padding run at `spLeafB`. -/
def spLeafMb : List Stmt × Nat × Nat := kMsg spLeafB (spLeafCells.map KC.cell) 1056 false none (spC + 3)

open scoped Dec in
/-- **The leaf's message, checked.** -/
theorem spLeaf_check :
    Stmt.renameList (padShift spVPad spLeafP) spLeafM.1 = Stmt.renameList (padRen spLeafB spLeafP) spLeafMb.1 ∧
      spLeafMb.2.1 = spLeafM.2.1 ∧ spLeafMb.2.2 = spLeafM.2.2 ∧ spLeafB + 5 ≤ spC + 3 ∧
      spC + 3 ≤ spLeafP ∧ spLeafP ≤ spLeafM.2.1 ∧ spLeafM.2.2 < spLeafM.2.1 ∧
      spEnc false 1 spLeafB < spC ∧ spProd false 1 spLeafB < spC := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
