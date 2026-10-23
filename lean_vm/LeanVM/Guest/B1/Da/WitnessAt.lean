/-
  LeanVM.Guest.B1.Da.WitnessAt

  `da_verify` in the uniform placed form on a LeanDA witness: a witness opening `(root, vd)` gives
  `CompleteAtD`, returning the cells of `root` and `vd`.

  The witness and `Da.Witness.Opens` are Benedikt Wagner's LeanDA formalization, as ported here.
-/

module

public import LeanVM.Guest.B1.Da.VerifyAt
public import LeanVM.Guest.B1.Da.WitnessComplete

/-!
# `da_verify` on a witness, placed

`da_verify_completeAt_w`: for a witness opening `(root, vd)` (`Da.Witness.Opens`), `da_verify` is
`CompleteAtD` at `g_squares = g^s`, reading `g^(2^L)` at `g^(s + L)` (`L = wLog w`), returning the
cells of `root` and `vd`, when the certificate's weights run fits `da_vector_cell`'s frame.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest
open LeanVM.Guest.B1 (CompleteAtD Returns)

@[expose] public section

/-- **`da_verify` is complete, placed, on a witness.** -/
theorem da_verify_completeAt_w (fs : String → ℕ) (cert : String → V → ℕ)
    (hcv : cert "da_vector_cell" (.n 1) + 256 ≤ fs "da_vector_cell") {w : LeanVM.Da.Witness}
    {root vd : Digest} (hw : w.Opens root vd) (s : ℕ) :
    CompleteAtD fs cert 16 "da_verify" [(s + wLog w, [gen ^ 2 ^ wLog w])] [gen ^ s]
      (Returns (digestCells root ++ digestCells vd)) := by
  obtain ⟨e1, e2⟩ := opens_eq hw
  rw [e1, e2]
  exact da_verify_completeAt fs cert hcv hw.1 hw.2.1 rfl (wSyms_len hw) (wWs_len hw)
    (fun i hi => wDot hw i hi) s

end
end LeanVM.Guest.B1.Da
