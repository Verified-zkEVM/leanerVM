/-
  LeanerVM.Protocol.ToArkLib.MapWitness

  The component with no round that maps the statement and the witness and leaves the oracles
  alone, with its completeness. Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.PassThrough

/-!
# The map-witness component

`Component.mapWitness OStmt f g` sends nothing: the verifier outputs `f` of the statement and the
oracles it was given, and the prover outputs the witness `g` makes from its input (the statement,
the oracles' contents and the witness). It is `Component.passThrough` with a witness that
changes: the step in which the prover replaces the table it holds by the table it folded.

Completeness (`mapWitnessComplete`): whenever `f` and `g` carry the input relation into the
output relation. Security (`mapWitnessSecurity`, at the empty error): the witness is read back by a
function the consumer gives, and the output relation at the mapped statement implies the input
relation at the witness read back.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec

@[expose] public section

namespace Component

variable {ι : Type} (OStmt : ι → Type) [∀ i, OracleInterface (OStmt i)]
  {StmtIn StmtOut W W' : Type} (f : StmtIn → StmtOut) (g : (StmtIn × ∀ i, OStmt i) × W → W')

/-- The prover: no message, the statement mapped, the witness `g` makes, the oracles kept. -/
def mapWitnessProver : OracleProver []ₒ StmtIn OStmt W StmtOut OStmt W' !p[] where
  PrvState := fun _ ↦ (StmtIn × ∀ i, OStmt i) × W
  input := _root_.id
  sendMessage := fun i ↦ Fin.elim0 i.1
  receiveChallenge := fun i ↦ Fin.elim0 i.1
  output := fun p ↦ pure ((f p.1.1, p.1.2), g p)

/-- The map-witness component: the pass-through verifier, the witness-mapping prover. -/
def mapWitness : Def StmtIn OStmt W StmtOut OStmt W' !p[] where
  red := ⟨mapWitnessProver OStmt f g, passThroughVerifier OStmt f⟩

/-- Completeness, for any two relations `f` and `g` carry one into the other. -/
def mapWitnessComplete
    {relIn : Set ((StmtIn × ∀ i, OStmt i) × W)}
    {relOut : Set ((StmtOut × ∀ i, OStmt i) × W')}
    (h : ∀ s o w, ((s, o), w) ∈ relIn → ((f s, o), g ((s, o), w)) ∈ relOut) :
    Complete (mapWitness OStmt f g) relIn relOut where
  guarded := (passThroughPure OStmt f).toGuardedForm
  complete := fun init impl ↦ by
    apply Reduction.perfectCompleteness_of_run_support
    intro stmtIn witIn hIn x hx
    obtain ⟨s, o⟩ := stmtIn
    have hrun : ((mapWitness OStmt f g).red.toReduction.run (s, o) witIn).run =
        pure (some (((show (!p[] : ProtocolSpec 0).FullTranscript from
          fun i ↦ Fin.elim0 i), (f s, o), g ((s, o), witIn)), (f s, o))) := rfl
    rw [hrun, support_pure, Set.mem_singleton_iff] at hx
    exact ⟨_, hx, h s o witIn hIn, rfl⟩


/-! ## Security -/

section Security

variable (back : W' → W) {relIn : Set ((StmtIn × ∀ i, OStmt i) × W)}
  {relOut : Set ((StmtOut × ∀ i, OStmt i) × W')}
  (h : ∀ s o w', ((f s, o), w') ∈ relOut → ((s, o), back w') ∈ relIn)
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-- The extractor of the map-witness component: the output witness goes back to an input witness
by `back`. -/
def backExtractor (S : Type) {n : ℕ} (pSpec : ProtocolSpec n) :
    Extractor.RoundByRound (OracleSpec.emptySpec.{0, 0}) S W W' pSpec (fun _ ↦ W) where
  eqIn := rfl
  extractMid := fun _ _ _ w ↦ w
  extractOut := fun _ _ w' ↦ back w'

/-- The knowledge state function of the map-witness component: the input relation, at the
witness that `back` extracts. -/
def mapWitnessStateFunction :
    (passThroughVerifier OStmt f).toVerifier.KnowledgeStateFunction init impl relIn relOut
      (backExtractor back (StmtIn × ∀ i, OStmt i) !p[]) where
  toFun := fun _ stmt _ w ↦ (stmt, w) ∈ relIn
  toFun_empty := fun _ _ ↦ Iff.rfl
  toFun_next := fun m ↦ Fin.elim0 m
  toFun_full := fun stmt tr w' hpos ↦
    h stmt.1 stmt.2 w' (Verifier.GuardedForm.of_probEvent_pos
      (passThroughPure OStmt f).toGuardedForm init impl stmt tr _ hpos).2

/-- The security half of the map-witness component, at the empty error, with the extractor that
sends the output witness back by `back`: the output relation, at the statement mapped, implies the
input relation at the witness sent back. -/
def mapWitnessSecurity :
    Security (mapWitness OStmt f g) relIn relOut (fun i ↦ Fin.elim0 i.1) where
  guarded := (passThroughPure OStmt f).toGuardedForm
  witMid := fun _ ↦ W
  extractor := backExtractor back (StmtIn × ∀ i, OStmt i) !p[]
  kSF := mapWitnessStateFunction OStmt f back h
  rbr := fun _ _ _ i ↦ Fin.elim0 i.1

end Security

end Component

end
end LeanerVM.Protocol
