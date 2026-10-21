/-
  LeanVM.Guest.B1.Comp.Whir.Loc.Support

  Small facts over a total hash the located layer of `open_stacked` uses.
-/

module

public import LeanVM.Guest.B1.Comp.Whir.OsCapC
public import LeanVM.Guest.B1.Comp.Whir.OsBody
public import LeanVM.Guest.B1.Comp.Whir.OsDataC
public import LeanVM.Guest.B1.Comp.Whir.OpenAns
public import LeanVM.Guest.B1.Comp.Whir.CapAgreesW

/-!
# Support for the located layer over a total hash

`length_sqAllW`: `n` squeezes over `Ht` give `n` challenges (`length_sqAll`); `sqAll_succ_sndW`:
the state after `j + 1` squeezes is one squeeze of the state after `j` (`sqAll_succ_snd`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

theorem length_sqAllW (Ht : Bytes → Digest) (j : ℕ) (cv : Digest) : (sqAllW Ht j cv).1.length = j := by
  induction j generalizing cv with
  | zero => rfl
  | succ j ih => simp [sqAllW, ih]

theorem sqAll_succ_sndW (Ht : Bytes → Digest) (j : ℕ) (cv : Digest) :
    (sqAllW Ht (j + 1) cv).2 = sqCvW Ht (sqAllW Ht j cv).2 := by
  induction j generalizing cv with
  | zero => rfl
  | succ j ih => exact ih (sqCvW Ht cv)

end
end LeanVM.Guest.B1
