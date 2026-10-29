/-
  LeanerVM.Protocol.Verify.Blake2sWalk

  The forward walk of the BLAKE2s circuit at a vector of column weights: the products `A w` and
  `B w` of the circuit's two matrices, by the circuit's builder run on the weights, and its
  equality with the circuit's block R1CS.
-/

module

public import LeanerVM.Protocol.Blake2sCircuit

/-!
# The forward walk of the BLAKE2s circuit

The lincheck's terminal reads the two matrices of the BLAKE2s circuit only through `A w` and
`B w` for one vector `w` of column weights (`Flock.linTerminal`); the circuit's own block R1CS
(`blake2sCircuit.toBlockR1CS`) evaluates them entry by entry, `2^28` terms a matrix, which no
verifier can run. `blake2sRows w` runs the circuit's builder (`Blake2sCircuit.blake2sGates`) on
the carrier of the weights (`weightLin w`): a position is its weight, XOR is addition, and a
gate's row is its two values, a few additions a row; a position without a gate has `restRow`'s
row, `(w_c, w_c)` at the constant, `(w_j, w_c)` at an input, zero elsewhere.

`blake2sRows_eq`: the walk is the forward walk of the circuit's block R1CS at every `w`. In
characteristic two, evaluating a form at the weights maps forms to weights (`evalAt_hom`), the
builder commutes with such maps (`blake2sGates_map`), and the block R1CS's forward walk is the
rows at the weights of the gates' forms evaluated (`toBlockR1CS_rows`).

Nothing here transcribes a source: the circuit is `LeanerVM.Protocol.Blake2sCircuit`'s, and its
rows are checked against the pinned leanVM's there.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly ProductCircuit Blake2sCircuit

@[expose] public section

/-- The forward walk of the BLAKE2s circuit at the column weights `w`: `A w` and `B w`, from the
circuit's gates built on the weights. -/
def blake2sRows (w : CMlPolynomialEval E (Flock.kSkip + Flock.kIn)) :
    CMlPolynomialEval E (Flock.kSkip + Flock.kIn) × CMlPolynomialEval E (Flock.kSkip + Flock.kIn) :=
  let r := rowsAt (weightLin w) Flock.constPos Blake2sCircuit.inputs (blake2sGates (weightLin w))
  (r.map (·.a), r.map (·.b))

/-- The walk is the forward walk of the BLAKE2s circuit's block R1CS. -/
theorem blake2sRows_eq (w : CMlPolynomialEval E (Flock.kSkip + Flock.kIn)) :
    blake2sRows w = (blake2sCircuit.toBlockR1CS E).rows w := by
  have hg : blake2sCircuit.gates.map (mapGate (evalAt w)) = blake2sGates (weightLin w) := by
    rw [blake2sGates_map (evalAt_hom w), blake2sCircuit_gates, blake2sGates]
  rw [toBlockR1CS_rows, hg, blake2sCircuit_cpos, blake2sCircuit_inputs]
  rfl

end
end LeanerVM.Protocol
