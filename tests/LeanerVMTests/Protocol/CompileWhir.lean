import LeanerVM.Protocol.Compile.Whir
import LeanerVMTests.Protocol.WhirOpen

/-!
# WHIR's opening on the wire, on a toy

The opening of `LeanerVMTests.Protocol.WhirOpen` (a level of two folds at rate `2⁻¹` with two
queries, then a last level of one fold and one query) run through the guarded form the compiled
verifier composes (`whirOpenGuarded`), and the executable's algebra (`Verify.whirCheck`) on the
transcript's wire (`DecodeChain.whirWireOf`) and the rows its openings carry (`whirCheck_of_run`).

* On the honest transcript the guarded run accepts, and the algebra accepts its wire.
* With the linear coefficient of the opening claim's polynomial changed, the guarded run
  rejects. The wire drops that coefficient, so it is the honest one and the algebra accepts it.
  The algebra's verdict on a transcript's wire is the oracle verifier's only for a transcript whose
  polynomials pass their checks.
-/

namespace LeanerVMTests.Protocol.CompileWhir

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Whir LeanerVM.Protocol.StepSchedule
  LeanerVM.Protocol.DecodeChain LeanerVM.Protocol.Compile LeanerVMTests.Protocol.WhirOpenToy
  ProtocolSpec

/-- The toy's transcript of the prover's messages. -/
def trOf (m : Msgs) :
    (seqSpec (.skip :: .msg (SumcheckRound.Message E 2) :: ladder.steps)).FullTranscript :=
  seqTr _ m.vals

/-- The level-0 word's leaves: each row's lanes in reverse, as base-field values. -/
def leaf0 (p : Fin (2 ^ (κ0 + sh0.R))) : List K :=
  ((oracle0 0).row p).toList.reverse.map (·.limb 0)

/-- Whether the guarded run of the opening accepts the messages, on the toy's statement and word. -/
def runs (m : Msgs) : Bool :=
  ((whirOpenGuarded sh0 κ0 ladder).run (stmt0, oracle0) (trOf m)).isSome

/-- The executable's algebra on the messages' wire and the rows their openings carry. -/
def algebra (m : Msgs) : Bool :=
  Verify.whirCheck (κ0 + sh0.ℓ) ladder.shapes stackW stackC (whirWireOf ladder (trOf m)).1
    (whirWireOf ladder (trOf m)).2 (Prove.ladderRows ladder leaf0 (seqTail (seqTail (trOf m))))

/-- The opening claim's polynomial with its linear coefficient, the one its wire drops, changed. -/
def flipped : Msgs := { honest with first := bump honest.first }

/-- The checks, each named. -/
def checks : List (String × Bool) := [
  ("the leaves read back as the level-0 word's rows",
    (List.finRange _).all fun p ↦
      Verify.laneRow true sh0.ℓ (leaf0 p) == some ((oracle0 0).row p)),
  ("honest: the guarded run accepts", runs honest),
  ("honest: the algebra accepts its wire", algebra honest),
  ("a dropped coefficient changed: the guarded run rejects", !runs flipped),
  ("its wire is the honest one",
    (whirWireOf ladder (trOf flipped)).1 == (whirWireOf ladder (trOf honest)).1),
  ("and the algebra accepts it", algebra flipped)]

#guard (checks.filter (!·.2)).map (·.1) == []

end LeanerVMTests.Protocol.CompileWhir
