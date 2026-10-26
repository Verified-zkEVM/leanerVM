module

public import Statement.Prover.Script

/-!
# A stateful sumcheck prover

`sumcheckBy round fold modes st`: in each round, the round polynomial's coefficients (constant
first), computed from the prover's state `st`, go on the wire in the round's mode (all but the
linear coefficient in plain mode, all but the constant one in equality mode, as the verifier's
`sumcheckRoundPoly` rebuilds them); then the challenge is folded into the state. It returns the
challenges, in order, and the last state.
-/

@[expose] public section

namespace LeanVM.Prover

open LeanVM.Parameters

/-- The coefficients the wire carries: all but the linear one in plain mode (`none`), all but the
constant one in equality mode (`some r`). -/
def wire : Option E → List E → List E
  | none, c => c.headD 0 :: c.drop 2
  | some _, c => c.drop 1

/-- **A stateful sumcheck prover**: per round the coefficients `round st` on the wire, then the
challenge `c`, the state becoming `fold st c`. -/
def sumcheckBy {σ : Type} (round : σ → List E) (fold : σ → E → σ) :
    List (Option E) → σ → Script (List E × σ)
  | [], st => .ret ([], st)
  | mode :: modes, st =>
    (Script.sendList (wire mode (round st))).bind fun _ ↦ Script.sampleE.bind fun c ↦
      (sumcheckBy round fold modes (fold st c)).bind fun r ↦ .ret (c :: r.1, r.2)

end LeanVM.Prover

end
