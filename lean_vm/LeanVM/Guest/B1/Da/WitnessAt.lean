/-
  LeanVM.Guest.B1.Da.WitnessAt

  `da_verify` in the uniform placed form on a LeanDA witness: a witness opening `(root, vd)` gives
  `CompleteAtD`, returning the cells of `root` and `vd`.

  The witness and `Da.MatrixWitness.Opens` are Benedikt Wagner's LeanDA formalization, as ported here.
-/

module

public import LeanVM.Guest.B1.Da.VerifyAt
public import LeanVM.Guest.B1.Da.WitnessComplete
public import LeanVM.Guest.Memory.LiftPure

/-!
# `da_verify` on a witness, placed

`da_verify_completeAt_w`: for a witness opening `(root, vd)` (`Da.MatrixWitness.Opens`), `da_verify` is
`CompleteAtD` at `g_squares = g^s`, reading `g^(2^L)` at `g^(s + L)` (`L = wLog w`), returning the
cells of `root` and `vd`, when the certificate's weights run fits `da_vector_cell`'s frame;
`da_verify_completeAt_runs`, when every certificate's frame runs fit their frames (G7's
`Lift.RunsFit`).
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest
open LeanVM.Guest.B1 (CompleteAtD Returns)

@[expose] public section

/-- **`da_verify` is complete, placed, on a witness.** -/
theorem da_verify_completeAt_w (fs : String → ℕ) (cert : String → V → ℕ)
    (hcv : cert "da_vector_cell" (.n 1) + 256 ≤ fs "da_vector_cell") {w : LeanVM.Da.MatrixWitness}
    {root vd : Digest} (hw : w.Opens root vd) (s : ℕ) :
    CompleteAtD fs cert 16 "da_verify" [(s + wLog w, [gen ^ 2 ^ wLog w])] [gen ^ s]
      (Returns (digestCells root ++ digestCells vd)) := by
  obtain ⟨e1, e2⟩ := opens_eq hw
  rw [e1, e2]
  exact da_verify_completeAt fs cert hcv hw.1 hw.2.1 rfl (wSyms_len hw) (wWs_len hw)
    (fun i hi => wDot hw i hi) s

set_option maxRecDepth 100000 in
theorem vec_run_mem : Atom.frameAddr (.n 4461) (.n 1 :: (List.range 255).map fun k => .n (k + 2)) ∈
    Lift.blockAtoms (Fn.body Data.core28) := by
  decide +kernel

/-- The weights' run fits `da_vector_cell`'s frame, when every run fits its frame. -/
theorem vec_runFits {fs : String → ℕ} {cert : String → V → ℕ} (hrf : Lift.RunsFit fs cert) :
    cert "da_vector_cell" (.n 1) + 256 ≤ fs "da_vector_cell" := by
  have := hrf "da_vector_cell" Data.core28 find_da_vector_cell (.n 4461) (.n 1)
    ((List.range 255).map fun k => .n (k + 2)) vec_run_mem
  simpa using this

/-- **`da_verify` is complete, placed, on a witness**, when the certificate's frame runs fit. -/
theorem da_verify_completeAt_runs (fs : String → ℕ) (cert : String → V → ℕ)
    (hrf : Lift.RunsFit fs cert) {w : LeanVM.Da.MatrixWitness} {root vd : Digest} (hw : w.Opens root vd)
    (s : ℕ) :
    CompleteAtD fs cert 16 "da_verify" [(s + wLog w, [gen ^ 2 ^ wLog w])] [gen ^ s]
      (Returns (digestCells root ++ digestCells vd)) :=
  da_verify_completeAt_w fs cert (vec_runFits hrf) hw s

end
end LeanVM.Guest.B1.Da
