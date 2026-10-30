/-
  LeanVM.Guest.B1.Da.WitnessAtT

  `da_verify` placed on a LeanDA witness, by a tree of its honest shape (`dvNH`) at the witness's
  row count and padded log.

  The witness and `Da.MatrixWitness.Opens` are Benedikt Wagner's LeanDA formalization, as ported here.
-/

module

public import LeanVM.Guest.B1.Da.VerifyAtT
public import LeanVM.Guest.B1.Da.WitnessAt

/-!
# `da_verify` on a witness, its honest shape

`da_verify_completeAtT_w`, `da_verify_completeAtT`: `da_verify_completeAt_w`,
`da_verify_completeAt_runs` by a tree of `dvNH w.rows.length (wLog w)`.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest
open LeanVM.Guest.B1 (CompleteAtDT Returns)

@[expose] public section

/-- **`da_verify` is complete, placed, on a witness, by a tree of its honest shape.** -/
theorem da_verify_completeAtT_w (fs : String → ℕ) (cert : String → V → ℕ)
    (hcv : cert "da_vector_cell" (.n 1) + 256 ≤ fs "da_vector_cell") {w : LeanVM.Da.MatrixWitness}
    {root vd : Digest} (hw : w.Opens root vd) (s : ℕ) :
    CompleteAtDT fs cert 16 "da_verify" [(s + wLog w, [gen ^ 2 ^ wLog w])] [gen ^ s]
      (Returns (digestCells root ++ digestCells vd)) (dvNH w.rows.length (wLog w)) := by
  obtain ⟨e1, e2⟩ := opens_eq hw
  rw [e1, e2]
  exact dvT_completeAt fs cert hcv hw.1 hw.2.1 rfl (wSyms_len hw) (wWs_len hw)
    (fun i hi => wDot hw i hi) s

/-- **`da_verify` is complete, placed, on a witness, by a tree of its honest shape**, when the
certificate's frame runs fit. -/
theorem da_verify_completeAtT (fs : String → ℕ) (cert : String → V → ℕ)
    (hrf : Lift.RunsFit fs cert) {w : LeanVM.Da.MatrixWitness} {root vd : Digest} (hw : w.Opens root vd)
    (s : ℕ) :
    CompleteAtDT fs cert 16 "da_verify" [(s + wLog w, [gen ^ 2 ^ wLog w])] [gen ^ s]
      (Returns (digestCells root ++ digestCells vd)) (dvNH w.rows.length (wLog w)) :=
  da_verify_completeAtT_w fs cert (vec_runFits hrf) hw s

end
end LeanVM.Guest.B1.Da
