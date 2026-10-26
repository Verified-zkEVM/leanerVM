module

public import Statement.Prover.Script

/-!
# Ring switching

The honest prover of ring switching (`ringSwitch`, `verifier.py:1408-1444` at leanVM
`4af2cdddd7cd41b9df2cc7e123e314a91b0b4462`) sends nothing: it receives the six coefficients of the
staged map `Φ` and computes the target `Σ_i x^i Φ(s_i)` of the claim it opens on the stack.
`ringFast` returns, besides the target, the data the opening needs to build the claim's weight on
the stack: the Keccak reduction's point and the six coefficients. The weight
`u ↦ ringWeight point u (ringCoefficients challenges)` is never evaluated as a closure: on the
cube it is `Φ` applied to the equality kernel of the point (`Statement/Prover/Whir.lean`).
-/

@[expose] public section

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Protocol.Verifier

/-- What ring switching leaves for the opening: the target, the point and the coefficients of
`Φ`. -/
structure RingOut where
  /-- The target `Σ_i x^i Φ(s_i)`. -/
  target : E
  /-- The Keccak reduction's point on `q_keccak`. -/
  point : List E
  /-- The six coefficients of the staged map `Φ`. -/
  challenges : List E

/-- **The honest prover of ring switching**: receive the six coefficients, return the target with
the point and the coefficients. -/
def ringFast (point slices : List E) : Script RingOut := do
  let challenges ← Script.sampleN ringMapShifts.length
  return ⟨polyEval (slices.map (phiMap · challenges)) gen, point, challenges⟩

end LeanVM.Prover

end
