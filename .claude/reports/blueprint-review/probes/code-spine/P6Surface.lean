import LeanerVM.Protocol.ToArkLib.Component
import LeanerVM.Protocol.ToArkLib.Refinement

/-!
Probe P6 (code-spine): three facts behind section B's proposals and section C.7.

1. The field `Component.Complete.outputPure` holds of every component: the shared oracle is
   empty, so the prover's output makes no query. (ArkLib has this at the pin as the instance
   `Prover.instOutputIsPureEmpty`, `Composition/Sequential/NoAmbient.lean:39-42`, in a module
   leanerVM does not import and whose `.olean` is not built; it is restated here.)
2. The universes of `Refinement`: whether its two witness types may live in different
   universes (`Column μ : Type`, Clean's `EnsembleWitness : Type 1`). The last `example` of that
   section is the one that decides it.
3. Knowledge transports along a refinement at the same error, with the map applied in the
   event and the game, the provers and the extractor left alone.
-/

open OracleComp OracleSpec ProtocolSpec LeanerVM.Protocol
open scoped NNReal

namespace Probe

/-! ## 1. `outputPure` is automatic -/

/-- The result of a computation that has no possible oracle query (ArkLib
`NoAmbient.lean:25-27` at `dca90385`, restated). -/
def runEmpty {α : Type} : OracleComp []ₒ α → α
  | .pure a => a
  | .liftBind t _ => isEmptyElim t

/-- Every computation over the empty specification is its pure result (`NoAmbient.lean:30-35`,
restated). -/
theorem eq_pure_runEmpty {α : Type} (oa : OracleComp []ₒ α) : oa = pure (runEmpty oa) := by
  cases oa with
  | pure a => rfl
  | queryBind t _ => exact isEmptyElim t

/-- The field `outputPure`, for every component, from its definition alone. -/
theorem outputPure_of_def {StmtIn : Type} {ιi : Type} {OStmtIn : ιi → Type} {WitIn : Type}
    {StmtOut : Type} {ιo : Type} {OStmtOut : ιo → Type} {WitOut : Type}
    [∀ i, OracleInterface (OStmtIn i)] [∀ i, OracleInterface (OStmtOut i)]
    (D : Component.Def StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut) :
    D.red.prover.OutputIsPure :=
  ⟨fun st ↦ runEmpty (D.red.prover.output st),
    fun st ↦ eq_pure_runEmpty (D.red.prover.output st)⟩

#print axioms outputPure_of_def

/-! ## 3. Knowledge transports along a refinement, in the event -/

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ}
  {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- If `E` extracts a witness of `R` except with probability `ε`, then the same extractor
followed by the map of a refinement from `R` to `S` yields a witness of `S` except with
probability `ε`. -/
theorem knowledge_transport {R : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {W₂ : Type} {S : Set (StmtIn × W₂)} (f : Refinement R S)
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {E : Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec} {ε : ℝ≥0}
    (h : verifier.knowledgeSoundnessWith init impl R relOut E ε)
    (stmtIn : StmtIn) (witIn : WitIn)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    let pImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
      impl.addLift challengeQueryImpl
    let exec := do
      let ⟨⟨⟨transcript, ⟨_, witOut⟩⟩, stmtOut⟩, proveQueryLog, verifyQueryLog⟩
        ← (Reduction.mk prover verifier).runWithLog stmtIn witIn
      let extractedWitIn? ←
        liftM (E stmtIn witOut transcript proveQueryLog.fst verifyQueryLog).run
      return (stmtIn, extractedWitIn?, stmtOut, witOut)
    Pr[fun ⟨stmtIn, extractedWitIn?, stmtOut, witOut⟩ =>
        (∀ w ∈ extractedWitIn?, (stmtIn, f.map stmtIn w) ∉ S) ∧ (stmtOut, witOut) ∈ relOut
      | OptionT.mk do (simulateQ pImpl exec.run).run' (← init)] ≤ ε :=
  le_trans (probEvent_mono fun _ _ hx ↦
    ⟨fun w hw hR ↦ hx.1 w hw (f.map_valid _ _ hR), hx.2⟩) (h stmtIn witIn prover)

#print axioms knowledge_transport

/-! ## 2. The universes of `Refinement` -/

#check @Refinement

/-- A witness type in `Type 1`, as Clean's `EnsembleWitness` is. -/
structure Big : Type 1 where
  carrier : Type

/-- Decides the question: a refinement from a relation whose witness is in `Type` to one whose
witness is in `Type 1`. Accepted if the two witness universes of `Refinement` are independent,
rejected if `{W₁ W₂ : Type _}` gave them one universe. -/
example : Refinement (Stmt := Unit) {p : Unit × ℕ | True} {p : Unit × Big | True} where
  map := fun _ n ↦ ⟨Fin n⟩
  map_valid := fun _ _ _ ↦ trivial

end Probe
