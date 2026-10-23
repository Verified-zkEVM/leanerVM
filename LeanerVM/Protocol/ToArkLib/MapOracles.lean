/-
  LeanerVM.Protocol.ToArkLib.MapOracles

  The component with no round that maps the statement, the witness and the oracles: the output
  oracles are a function of the input oracles, each query to them answered by one query to an
  input oracle. Completeness and knowledge soundness. Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.MapWitness
public import LeanerVM.Protocol.ToArkLib.QueryCheck

/-!
# Mapping the oracles

An `OracleMap O O'` reads oracles `O'` off oracles `O`: a function `map` from the values of `O` to
the values of `O'`, and for each query to `O'` one query to `O` and a way to turn its answer into
the answer of `map`. `Component.mapOracles O O' f g M` has no round: the verifier maps the
statement by `f` and exposes `M.map` of its input oracles as its output oracles, each query to
them answered by the one query to the input oracles (ArkLib's virtual output oracles); the prover
maps the witness by `g`. It is the step between two components that read the same data through
two types: the codeword of a word with values in a subfield, read in the field, for instance.

Completeness (`mapOraclesComplete`): whenever `f`, `M.map` and `g` carry the input relation into
the output relation. Security (`mapOraclesSecurity`, at the empty error): the witness is read back
by a function the consumer gives, and the output relation at the mapped statement and oracles
implies the input relation at the witness read back.

Nothing here transcribes a source.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec

@[expose] public section

namespace Component

/-- Oracles `O'` read off oracles `O`, each query answered by one query. -/
structure OracleMap {ι ι' : Type} (O : ι → Type) (O' : ι' → Type) [∀ i, OracleInterface (O i)]
    [∀ i, OracleInterface (O' i)] where
  /-- The values of the oracles `O'`. -/
  map : (∀ i, O i) → ∀ j, O' j
  /-- The query to `O` that answers a query to `O'`. -/
  query : [O']ₒ.Domain → [O]ₒ.Domain
  /-- The answer to the query to `O'`, from the answer to that query. -/
  answer : (q : [O']ₒ.Domain) → [O]ₒ.Range (query q) → [O']ₒ.Range q
  /-- It is the answer of the mapped oracles. -/
  answer_eq : ∀ o q, answer q (answerOf O o (query q)) = answerOf O' (map o) q

variable {ι ι' : Type} (O : ι → Type) (O' : ι' → Type) [∀ i, OracleInterface (O i)]
  [∀ i, OracleInterface (O' i)] {StmtIn StmtOut W W' : Type} (f : StmtIn → StmtOut)
  (g : W → W') (M : OracleMap O O')

/-- The output oracles of the verifier, as virtual oracles: their values `M.map`, each query
answered by its query to the input oracles. -/
def OracleMap.simulation : OracleOutputSimulation []ₒ O O' !p[] where
  materializeOutput := fun _ o _ ↦ M.map o
  simulateOutputQuery := fun _ q ↦
    M.answer q <$> (liftM (askInput O (M.query q)) :
      OracleComp ([]ₒ + ([O]ₒ + [(!p[] : ProtocolSpec 0).Message]ₒ)) _)
  simulateOutputQuery_eq := fun _ o _ q ↦ by
    rw [simulateQ_map]
    exact congrArg (fun a ↦ (pure a : OracleComp []ₒ _)) (M.answer_eq o q)

/-- The verifier: maps the statement, exposes the mapped oracles. -/
def mapOraclesVerifier : OracleVerifier []ₒ StmtIn O StmtOut O' !p[] where
  verify := fun s _ ↦ pure (f s)
  outputOracle := .inr (M.simulation O O')

/-- The prover: no message, the statement, the oracles and the witness mapped. -/
def mapOraclesProver : OracleProver []ₒ StmtIn O W StmtOut O' W' !p[] where
  PrvState := fun _ ↦ (StmtIn × ∀ i, O i) × W
  input := _root_.id
  sendMessage := fun i ↦ Fin.elim0 i.1
  receiveChallenge := fun i ↦ Fin.elim0 i.1
  output := fun p ↦ pure ((f p.1.1, M.map p.1.2), g p.2)

/-- The map-oracles component: no round. -/
def mapOracles : Def StmtIn O W StmtOut O' W' !p[] where
  red := ⟨mapOraclesProver O O' f g M, mapOraclesVerifier O O' f M⟩

/-- As an ordinary verifier, it returns the mapped statement and the mapped oracles. -/
theorem mapOraclesVerifier_toVerifier_run (s : StmtIn) (o : ∀ i, O i)
    (tr : (!p[]).FullTranscript) :
    (mapOraclesVerifier O O' f M).toVerifier.run (s, o) tr = pure (f s, M.map o) :=
  rfl

/-- The map-oracles verifier is pure, as data. -/
def mapOraclesPure : (mapOraclesVerifier O O' f M).toVerifier.PureForm where
  verify := fun p _ ↦ (f p.1, M.map p.2)
  verify_eq := fun ⟨s, o⟩ tr ↦ mapOraclesVerifier_toVerifier_run O O' f M s o tr

/-- Completeness, whenever `f`, `M.map` and `g` carry the input relation into the output
relation. -/
def mapOraclesComplete {relIn : Set ((StmtIn × ∀ i, O i) × W)}
    {relOut : Set ((StmtOut × ∀ i, O' i) × W')}
    (h : ∀ s o w, ((s, o), w) ∈ relIn → ((f s, M.map o), g w) ∈ relOut) :
    Complete (mapOracles O O' f g M) relIn relOut where
  guarded := (mapOraclesPure O O' f M).toGuardedForm
  complete := fun init impl ↦ by
    apply Reduction.perfectCompleteness_of_run_support
    intro stmtIn witIn hIn x hx
    obtain ⟨s, o⟩ := stmtIn
    have hrun : ((mapOracles O O' f g M).red.toReduction.run (s, o) witIn).run =
        pure (some (((show (!p[] : ProtocolSpec 0).FullTranscript from
          fun i ↦ Fin.elim0 i), (f s, M.map o), g witIn), (f s, M.map o))) := rfl
    rw [hrun, support_pure, Set.mem_singleton_iff] at hx
    exact ⟨_, hx, h s o witIn hIn, rfl⟩

/-! ## Security -/

section Security

variable (back : W' → W) {relIn : Set ((StmtIn × ∀ i, O i) × W)}
  {relOut : Set ((StmtOut × ∀ i, O' i) × W')}
  (h : ∀ s o w', ((f s, M.map o), w') ∈ relOut → ((s, o), back w') ∈ relIn)
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-- The knowledge state function: the input relation, at the witness that `back` extracts. -/
def mapOraclesStateFunction :
    (mapOraclesVerifier O O' f M).toVerifier.KnowledgeStateFunction init impl relIn relOut
      (backExtractor back (StmtIn × ∀ i, O i) !p[]) where
  toFun := fun _ stmt _ w ↦ (stmt, w) ∈ relIn
  toFun_empty := fun _ _ ↦ Iff.rfl
  toFun_next := fun m ↦ Fin.elim0 m
  toFun_full := fun stmt tr w' hpos ↦
    h stmt.1 stmt.2 w' (Verifier.GuardedForm.of_probEvent_pos
      (mapOraclesPure O O' f M).toGuardedForm init impl stmt tr _ hpos).2

/-- The security half, at the empty error, with the extractor that sends the output witness back
by `back`. -/
def mapOraclesSecurity :
    Security (mapOracles O O' f g M) relIn relOut (fun i ↦ Fin.elim0 i.1) where
  guarded := (mapOraclesPure O O' f M).toGuardedForm
  witMid := fun _ ↦ W
  extractor := backExtractor back (StmtIn × ∀ i, O i) !p[]
  kSF := mapOraclesStateFunction O O' f M back h
  rbr := fun _ _ _ i ↦ Fin.elim0 i.1

end Security

end Component

end
end LeanerVM.Protocol
