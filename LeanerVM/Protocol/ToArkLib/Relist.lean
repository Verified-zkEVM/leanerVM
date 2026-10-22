/-
  LeanerVM.Protocol.ToArkLib.Relist

  A component whose verifier never reads its oracles, run over other oracles that stand for a
  list of candidates: its knowledge soundness carries over at the list's length times the error.
  Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.Component
public import LeanerVM.Protocol.ToArkLib.FrontVerifier
public import LeanerVM.Protocol.ToArkLib.Refutation
public import VCVio.EvalDist.ProbabilityBounds

/-!
# Relisting a front component

A front component (`Component.Front`) has a verifier that is a check and a verdict on the
statement and the transcript, and hands its oracles on. Such a verifier makes sense over any
oracles: `Front.frontVerifier` answers the verifier's queries to its oracles with fixed values,
which it never reads, and so is a verifier typed without access to them, and `Front.over` is the
component with that verifier over other oracles `O'` and a given prover.

Over the oracles `O'` a value `o'` stands for a list `list o'` of values of the old oracles, and a
relation on the old oracles becomes `relistRel list rel`: some value in the list is related, with
some witness. `Front.relist` is the step this makes possible: if a front component is round by
round knowledge sound over `O` from `relIn` to `relOut` at errors `ε`, then any front component
over `O'` with the same check and verdict is round by round knowledge sound from
`relistRel list relIn` to `relistRel list relOut` at `L · ε`, when every list has at most `L`
values. The extractor keeps the witness, and the state function is "some value in the list
satisfies the old state function, with some intermediate witness of the old extractor". A
challenge can turn it from false to true only by turning the old state function from false to
true at one of the values, so the union bound over the list gives the error.

`proverVia` is the honest prover that goes with it: the old prover run on the oracles read off
the new witness, the new oracles and the new witness handed on; each of its rounds is the old
prover's (`runToRound_proverVia`). Completeness carries over the same way (`Front.overComplete`),
at the relations read through the witness (`viaRel`): the new oracles and the witness are related
as the consumer says, and the statement is related to the oracles read off the witness.

Nothing here transcribes a source.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal

@[expose] public section

namespace Component

/-! ## Relations through a list -/

/-- A relation over the oracles `O` read through a list: a statement and a value `o'` of the
oracles `O'` are related when some value in `list o'` is related to the statement, with some
witness. -/
def relistRel {S W W' : Type} {ι ι' : Type} {O : ι → Type} {O' : ι' → Type}
    (list : (∀ i, O' i) → List (∀ i, O i)) (rel : Set ((S × ∀ i, O i) × W)) :
    Set ((S × ∀ i, O' i) × W') :=
  {p | ∃ q ∈ list p.1.2, ∃ w, ((p.1.1, q), w) ∈ rel}

/-! ## A front verifier over other oracles -/

section Over

variable {StmtIn StmtOut WitIn WitOut : Type} {ι : Type} {O : ι → Type}
  [∀ i, OracleInterface (O i)] {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, OracleInterface (pSpec.Message i)] [∀ i, SampleableType (pSpec.Challenge i)]

/-- The queries of a verifier over the oracles `O`, those to the oracles answered by fixed values
`o₀` and those to the messages passed on. -/
def answerOracles (o₀ : ∀ i, O i) :
    QueryImpl ([]ₒ + ([O]ₒ + [pSpec.Message]ₒ)) (OracleComp ([]ₒ + [pSpec.Message]ₒ))
  | .inl t => PEmpty.elim t
  | .inr (.inl t) => pure (OracleInterface.answer (o₀ t.1) t.2)
  | .inr (.inr t) => liftM (([]ₒ + [pSpec.Message]ₒ).query (.inr t))

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- Answering the oracles with `o₀`, then the messages, is answering both. -/
theorem simulateQ_answerOracles (o₀ : ∀ i, O i) (msgs : pSpec.Messages) {α : Type}
    (mx : OracleComp ([]ₒ + ([O]ₒ + [pSpec.Message]ₒ)) α) :
    simulateQ (OracleInterface.simOracle []ₒ msgs) (simulateQ (answerOracles o₀) mx) =
      simulateQ (OracleInterface.simOracle2 []ₒ o₀ msgs) mx := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  funext t
  rcases t with t | t | t
  · exact PEmpty.elim t
  · simp only [QueryImpl.apply_compose, answerOracles]
    rfl
  · simp only [QueryImpl.apply_compose, answerOracles, simulateQ_spec_query]
    rfl

/-- The verifier of a front component, its queries to the oracles answered by `o₀`: a verifier
typed without access to the oracles. -/
def Front.frontVerifier {D : Def StmtIn O WitIn StmtOut O WitOut pSpec} (_F : Front D)
    (o₀ : ∀ i, O i) : FrontVerifier []ₒ StmtIn StmtOut pSpec where
  verify := fun s c ↦ OptionT.mk (simulateQ (answerOracles o₀) (D.red.verifier.verify s c).run)

/-- Simulated with the messages, it is the front component's check and verdict. -/
theorem Front.frontVerifier_spec {D : Def StmtIn O WitIn StmtOut O WitOut pSpec} (F : Front D)
    (o₀ : ∀ i, O i) (s : StmtIn) (tr : pSpec.FullTranscript) :
    OptionT.mk (simulateQ (OracleInterface.simOracle []ₒ tr.messages)
        ((F.frontVerifier o₀).verify s tr.challenges).run) =
      if F.check s tr then pure (F.out s tr) else failure := by
  have h := congrArg (fun v : OptionT (OracleComp []ₒ) (StmtOut × ∀ i, O i) ↦
    (Prod.fst <$> v : OptionT (OracleComp []ₒ) StmtOut)) (F.verify_eq (s, o₀) tr)
  simp only [OracleVerifier.toVerifier] at h
  have hl : (Prod.fst <$> (OptionT.mk (Option.map (fun t ↦ (t,
      D.red.verifier.materializeOutput tr.challenges o₀ tr.messages)) <$>
        simulateQ (OracleInterface.simOracle2 []ₒ o₀ tr.messages)
          (D.red.verifier.verify s tr.challenges).run) :
        OptionT (OracleComp []ₒ) (StmtOut × ∀ i, O i)) : OptionT (OracleComp []ₒ) StmtOut) =
      OptionT.mk (simulateQ (OracleInterface.simOracle2 []ₒ o₀ tr.messages)
        (D.red.verifier.verify s tr.challenges).run) := by
    apply OptionT.ext
    simp only [OptionT.run_map, OptionT.run_mk, Functor.map_map]
    conv_rhs => rw [← id_map (simulateQ _ _)]
    congr 1
    funext o
    cases o <;> rfl
  rw [hl] at h
  refine Eq.trans ?_ (h.trans ?_)
  · simp only [Front.frontVerifier, OptionT.run_mk]
    rw [simulateQ_answerOracles]
  · by_cases hc : F.check s tr = true
    · rw [ite_eq_left hc, ite_eq_left hc]
      rfl
    · rw [ite_eq_right hc, ite_eq_right hc]
      rfl

variable {ι' : Type} {O' : ι' → Type} [∀ i, OracleInterface (O' i)] {W' : Type}

/-- The front component's verifier over the oracles `O'`, with a prover over them: the same check
and verdict, the oracles `O'` handed on. -/
def Front.over {D : Def StmtIn O WitIn StmtOut O WitOut pSpec} (F : Front D) (o₀ : ∀ i, O i)
    (prover : OracleProver []ₒ StmtIn O' W' StmtOut O' W' pSpec) :
    Def StmtIn O' W' StmtOut O' W' pSpec where
  red := ⟨prover, (F.frontVerifier o₀).toOracleVerifier O'⟩

/-- It is front, with the same check and verdict. -/
def Front.overFront {D : Def StmtIn O WitIn StmtOut O WitOut pSpec} (F : Front D)
    (o₀ : ∀ i, O i) (prover : OracleProver []ₒ StmtIn O' W' StmtOut O' W' pSpec) :
    Front (F.over o₀ prover) where
  check := F.check
  out := F.out
  verify_eq := fun ⟨s, o⟩ tr ↦ FrontVerifier.toVerifier_verify_of_check _ F.check F.out
    (F.frontVerifier_spec o₀) s o tr

/-- The honest prover over the oracles `O'`: the prover over `O` run on the oracles and the
witness read off the new witness, the new oracles and the new witness handed on. -/
def proverVia (P : OracleProver []ₒ StmtIn O WitIn StmtOut O WitOut pSpec)
    (read : W' → (∀ i, O i) × WitIn) : OracleProver []ₒ StmtIn O' W' StmtOut O' W' pSpec where
  PrvState := fun i ↦ P.PrvState i × ((∀ j, O' j) × W')
  input := fun p ↦ (P.input ((p.1.1, (read p.2).1), (read p.2).2), (p.1.2, p.2))
  sendMessage := fun i st ↦ (fun r ↦ (r.1, (r.2, st.2))) <$> P.sendMessage i st.1
  receiveChallenge := fun i st ↦ (fun f c ↦ (f c, st.2)) <$> P.receiveChallenge i st.1
  output := fun st ↦ (fun r ↦ ((r.1.1, st.2.1), st.2.2)) <$> P.output st.1

omit [∀ i, OracleInterface (O i)] [∀ i, OracleInterface (pSpec.Message i)]
  [∀ i, SampleableType (pSpec.Challenge i)] [∀ i, OracleInterface (O' i)] in
/-- Every round of `proverVia` is the round of the prover it wraps, the new oracles and witness
beside it. -/
theorem runToRound_proverVia (P : OracleProver []ₒ StmtIn O WitIn StmtOut O WitOut pSpec)
    (read : W' → (∀ i, O i) × WitIn) (s : StmtIn) (o' : ∀ i, O' i) (w : W') (i : Fin (n + 1)) :
    (proverVia (O' := O') P read).runToRound i (s, o') w =
      (fun r ↦ (r.1, (r.2, (o', w)))) <$> P.runToRound i (s, (read w).1) (read w).2 := by
  induction i using Fin.induction with
  | zero => simp [Prover.runToRound, proverVia]
  | succ j ih =>
    simp only [Prover.runToRound, Fin.induction_succ] at ih ⊢
    rw [ih]
    unfold Prover.processRound
    split <;> simp [proverVia, map_bind, bind_map_left]

omit [∀ i, OracleInterface (O i)] [∀ i, OracleInterface (pSpec.Message i)]
  [∀ i, SampleableType (pSpec.Challenge i)] [∀ i, OracleInterface (O' i)] in
/-- The run of `proverVia`, for a prover with the trivial witness: the wrapped prover's run on the
oracles read off the witness, its output statement with the new oracles and the new witness. -/
theorem run_proverVia (P : OracleProver []ₒ StmtIn O Unit StmtOut O Unit pSpec)
    (read : W' → ∀ i, O i) (s : StmtIn) (o' : ∀ i, O' i) (w : W') :
    (proverVia (O' := O') P (fun w ↦ (read w, ()))).run (s, o') w =
      (fun r ↦ (r.1, (r.2.1.1, o'), w)) <$> P.run (s, read w) () := by
  simp only [Prover.run, runToRound_proverVia]
  simp [proverVia, map_bind]

omit [∀ i, OracleInterface (O i)] [∀ i, OracleInterface (pSpec.Message i)]
  [∀ i, SampleableType (pSpec.Challenge i)] [∀ i, OracleInterface (O' i)] in
/-- The run of a reduction whose verifier is guarded: the prover's run, then the verdict when the
check passes on the prover's transcript and a rejection otherwise. -/
private theorem run_eq_map_of_guarded {S W T W₂ : Type}
    (red : Reduction []ₒ S W T W₂ pSpec) (G : red.verifier.GuardedForm) (stmt : S) (wit : W) :
    (red.run stmt wit).run =
      (fun pr ↦ if G.check stmt pr.1 then some (pr, G.out stmt pr.1) else none) <$>
        red.prover.run stmt wit := by
  unfold Reduction.run
  conv_rhs => rw [map_eq_bind_pure_comp]
  simp only [OptionT.run_bind, Option.elimM, OptionT.run_monadLift, monadLift_self,
    bind_map_left, Option.elim_some, Function.comp_def]
  refine bind_congr fun pr ↦ ?_
  rw [Verifier.run, show red.verifier.verify stmt pr.1 = _ from G.verify_eq stmt pr.1]
  by_cases hc : G.check stmt pr.1 = true
  · simp only [hc, ↓reduceIte, OptionT.run_pure, liftM_pure, pure_bind, Option.elim_some,
      Option.getM_some]
  · simp only [hc, Bool.false_eq_true, ↓reduceIte, OptionT.run_failure, liftM_pure,
      OptionT.run_pure, pure_bind, Option.elim_some, Option.getM_none, Option.elim_none]

/-- A relation over the oracles `O` read through a witness: the new oracles and the witness are
`good` together, and the statement is related to the oracles read off the witness. -/
def viaRel {S : Type} (good : (∀ i, O' i) → W' → Prop) (read : W' → ∀ i, O i)
    (rel : Set ((S × ∀ i, O i) × Unit)) : Set ((S × ∀ i, O' i) × W') :=
  {p | good p.1.2 p.2 ∧ ((p.1.1, read p.2), ()) ∈ rel}

/-- **Completeness over other oracles.** A front component with the trivial witness, perfectly
complete over `O`, run over `O'` with the prover that reads its oracles off the witness, is
perfectly complete at the relations read through the witness: the honest runs are the old
ones, and the two verifiers have one check and one verdict. -/
theorem Front.over_complete {D : Def StmtIn O Unit StmtOut O Unit pSpec} (F : Front D)
    (o₀ : ∀ i, O i) (read : W' → ∀ i, O i) (good : (∀ i, O' i) → W' → Prop)
    {relIn : Set ((StmtIn × ∀ i, O i) × Unit)} {relOut : Set ((StmtOut × ∀ i, O i) × Unit)}
    (C : Complete D relIn relOut) {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (F.over o₀ (proverVia D.red.prover fun w ↦ (read w, ()))).red.perfectCompleteness init impl
      (viaRel good read relIn) (viaRel good read relOut) := by
  have hC := C.complete init impl
  unfold OracleReduction.perfectCompleteness at hC ⊢
  rw [Reduction.perfectCompleteness_eq_prob_one] at hC ⊢
  rintro ⟨s, o'⟩ q ⟨hgood, hin⟩
  have hD := (OptionT.prEvent_mk_eq_one_iff _ _).mp (hC (s, read q) () hin)
  refine (OptionT.prEvent_mk_eq_one_iff _ _).mpr fun x hx ↦ ?_
  set F' := F.overFront o₀ (proverVia (O' := O') D.red.prover fun w ↦ (read w, ()))
  have hrun' := run_eq_map_of_guarded _ F'.toGuarded.guarded (s, o') q
  have hrun := run_eq_map_of_guarded _ F.toGuarded.guarded (s, read q) ()
  simp only [OptionT.run] at hrun' hrun
  rw [hrun', show (F.over o₀ (proverVia D.red.prover fun w ↦ (read w, ()))).red.toReduction.prover
    = proverVia (O' := O') D.red.prover (fun w ↦ (read w, ())) from rfl,
    run_proverVia D.red.prover read s o' q] at hx
  simp only [simulateQ_map, Functor.map_map] at hx
  rw [hrun] at hD
  simp only [simulateQ_map, mem_support_bind_iff, StateT.run'_eq, StateT.run_map, Functor.map_map,
    support_map, Set.mem_image, forall_exists_index, and_imp] at hD
  simp only [mem_support_bind_iff, StateT.run'_eq, StateT.run_map, Functor.map_map, support_map,
    Set.mem_image] at hx
  obtain ⟨st, hst, y, hy, rfl⟩ := hx
  obtain ⟨r, hr, hrel, hstmt⟩ := hD _ st hst y hy rfl
  by_cases hc : F.toGuarded.guarded.check (s, read q) y.1.1 = true
  · have hc' : F'.toGuarded.guarded.check (s, o') y.1.1 = true := hc
    rw [ite_eq_left hc, Option.some.injEq] at hr
    subst hr
    refine ⟨_, ite_eq_left hc', ⟨hgood, hrel⟩, ?_⟩
    show (y.1.2.1.1, o') = _
    rw [hstmt]
    rfl
  · rw [ite_eq_right hc] at hr
    cases hr

/-- The completeness half over other oracles, from the completeness half over `O`. -/
def Front.overComplete {D : Def StmtIn O Unit StmtOut O Unit pSpec} (F : Front D)
    (o₀ : ∀ i, O i) (read : W' → ∀ i, O i) (good : (∀ i, O' i) → W' → Prop)
    {relIn : Set ((StmtIn × ∀ i, O i) × Unit)} {relOut : Set ((StmtOut × ∀ i, O i) × Unit)}
    (C : Complete D relIn relOut) :
    Complete (F.over o₀ (proverVia D.red.prover fun w ↦ (read w, ())))
      (viaRel good read relIn) (viaRel good read relOut) where
  toGuarded := (F.overFront o₀ _).toGuarded
  complete := fun init impl ↦ F.over_complete o₀ read good C init impl

end Over

/-! ## Knowledge soundness through a list -/

section Relist

variable {StmtIn StmtOut W W' : Type} {ι ι' : Type} {O : ι → Type} {O' : ι' → Type}
  [∀ i, OracleInterface (O i)] [∀ i, OracleInterface (O' i)] {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, OracleInterface (pSpec.Message i)] [∀ i, SampleableType (pSpec.Challenge i)]
  {D : Def StmtIn O W StmtOut O W pSpec} {D' : Def StmtIn O' W' StmtOut O' W' pSpec}
  (F : Front D) (F' : Front D') (hcheck : ∀ s tr, F'.check s tr = F.check s tr)
  (hout : ∀ s tr, F'.out s tr = F.out s tr)
  {relIn : Set ((StmtIn × ∀ i, O i) × W)} {relOut : Set ((StmtOut × ∀ i, O i) × W)}
  (X : Extraction D relIn relOut) (list : (∀ i, O' i) → List (∀ i, O i))
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

include F F' hcheck hout

/-- The state function through the list: some value in the list satisfies the old state
function, with some intermediate witness. -/
def Front.relistStateFunction :
    D'.red.verifier.toVerifier.KnowledgeStateFunction init impl (relistRel list relIn)
      (relistRel list relOut) (keepExtractor (StmtIn × ∀ i, O' i) W' pSpec) where
  toFun := fun m s tr _ ↦ ∃ q ∈ list s.2, ∃ wm, (X.kSF init impl).toFun m (s.1, q) tr wm
  toFun_empty := fun s _ ↦ by
    constructor
    · rintro ⟨q, hq, w, hw⟩
      refine ⟨q, hq, cast X.extractor.eqIn.symm w, ((X.kSF init impl).toFun_empty _ _).mp ?_⟩
      rw [cast_cast, cast_eq]
      exact hw
    · rintro ⟨q, hq, wm, h⟩
      exact ⟨q, hq, cast X.extractor.eqIn wm, ((X.kSF init impl).toFun_empty _ _).mpr h⟩
  toFun_next := fun m hdir s tr msg _ ⟨q, hq, wm, h⟩ ↦
    ⟨q, hq, X.extractor.extractMid m (s.1, q) (tr.concat msg) wm,
      (X.kSF init impl).toFun_next m hdir (s.1, q) tr msg wm h⟩
  toFun_full := fun s tr _ hpos ↦ by
    obtain ⟨hc, q, hq, w, hw⟩ :=
      Verifier.GuardedForm.of_probEvent_pos F'.toGuarded.guarded init impl s tr _ hpos
    refine ⟨q, hq, X.extractor.extractOut (s.1, q) tr w,
      (X.kSF init impl).toFun_full (s.1, q) tr w ?_⟩
    refine Verifier.GuardedForm.probEvent_pos_of_check F.toGuarded.guarded init impl (s.1, q) tr
      (fun t ↦ (t, w) ∈ relOut) ((hcheck s.1 tr).symm.trans hc) ?_
    have hw' : ((F'.out s.1 tr, q), w) ∈ relOut := hw
    exact (congrArg (fun t ↦ ((t, q), w) ∈ relOut) (hout s.1 tr)).mp hw'

/-- **Relisting**: a front component over `O`, round by round knowledge sound at `ε`, gives any
front component over `O'` with the same check and verdict, round by round knowledge sound through
lists of at most `L` values at `L · ε`, with the extractor that keeps the witness. Inlined before
compilation, so the errors never reach compiled code. -/
@[macro_inline]
def Front.relist {ε : pSpec.ChallengeIdx → ℝ≥0} (S : Security D relIn relOut ε) (L : ℕ)
    (hL : ∀ o, (list o).length ≤ L) :
    Security D' (relistRel list relIn) (relistRel list relOut) (fun i ↦ L • ε i) where
  guarded := F'.toGuarded.guarded
  witMid := fun _ ↦ W'
  extractor := keepExtractor (StmtIn × ∀ i, O' i) W' pSpec
  kSF := fun init impl ↦ Front.relistStateFunction F F' hcheck hout S.toExtraction list init impl
  rbr := fun init impl s i tr ↦ by
    refine (prEvent_mono _ _ (fun c ↦ ∃ k : Fin (list s.2).length, ∃ wm,
        ¬ (S.kSF init impl).toFun i.1.castSucc (s.1, (list s.2)[k]) tr
          (S.extractor.extractMid i.1 (s.1, (list s.2)[k]) (tr.concat c) wm) ∧
        (S.kSF init impl).toFun i.1.succ (s.1, (list s.2)[k]) (tr.concat c) wm) fun c hc ↦ ?_).trans
      ((prEvent_exists_le_card_mul _ _ fun k ↦ S.rbr init impl _ i tr).trans ?_)
    · obtain ⟨_, hnot, q, hq, wm, h⟩ := hc
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hq
      exact ⟨⟨k, hk⟩, wm, fun h' ↦ hnot ⟨_, hq, _, h'⟩, h⟩
    · rw [Fintype.card_fin, ENNReal.coe_nsmul, nsmul_eq_mul]
      gcongr
      exact_mod_cast hL s.2

end Relist

end Component

end
end LeanerVM.Protocol
