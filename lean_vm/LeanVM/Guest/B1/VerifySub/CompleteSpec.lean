/-
  LeanVM.Guest.B1.VerifySub.CompleteSpec

  `verify_sub`'s completeness statement (G7's target, 2026-10-23): one honest child at a time,
  in the placed form `CompleteAtD`.
-/

module

public import LeanVM.Guest.B1.VerifySub.Interface
public import LeanVM.Guest.Limits
public import LeanVM.Guest.Hints
public import LeanVM.Guest.Memory.LiftPure

/-!
# `verify_sub` is complete

`verify_sub_complete_Spec bytecode`: for every honest child `c` of a node under the seed `seed` —
its deferred claim shaped for the bytecode, its stack at least `2^muMin`, its stream at most
`streamCap` words, the deferring verifier accepting it while refusing a zero challenge where the
guest divides (`Limits.verifyDeferredNZ`), and its openings agreeing per batch over the run's query
steps (`Limits.queriesOf`) — and every caller's words `Lin` holding the exponent tables at `lp`, `sq`
and the child's fixed cells at `out = g^outE` (write-once: `verify_sub` writes them there),
`verify_sub` on the statement's and the seed's cells, `lp`, `sq`, `out` is complete at every frame
pointer (`CompleteAtD`), returning nothing. Its own buffers hold `Hints.childHints bytecode seed c`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.B1.Main

@[expose] public section

/-- **`verify_sub` is complete on every honest child** (G7's target). -/
def verify_sub_complete_Spec (bytecode : List K) : Prop :=
  ∀ (fs : String → ℕ) (cert : String → V → ℕ), Lift.RunsFit fs cert →
  ∀ (seed : Digest) (c : Child) (lp sq : E) (outE : ℕ) (Lin : Main.Layout) (κ : ℕ), 16 ≤ κ →
    c.statement.defer.Shaped bytecode →
    (∀ layout r, Verifier.announced bytecode c.proof.stream = some (layout, r) →
      Hints.muMin ≤ layout.stackLog) →
    c.proof.stream.length ≤ Hints.streamCap →
    Limits.verifyDeferredNZ bytecode seed (statementDigest seed c.statement) c.fresh c.proof = true →
    (∀ b ∈ Limits.queriesOf (deferredProgram c.fresh bytecode (statementDigest seed c.statement))
      (Hints.childStart seed c), Limits.BatchAgrees b.1 b.2) →
    (∀ rd, LowDef κ rd → MemL rd Lin → ExpTables rd lp sq) →
    (outE, fixedCells c.fresh) ∈ Lin →
    CompleteAtD fs cert κ "verify_sub" Lin
      [(digestScalars (statementDigest seed c.statement)).1,
        (digestScalars (statementDigest seed c.statement)).2, (digestScalars seed).1,
        (digestScalars seed).2, lp, sq, ofK (gpow outE)] (Returns [])

end
end LeanVM.Guest.B1.VerifySub
