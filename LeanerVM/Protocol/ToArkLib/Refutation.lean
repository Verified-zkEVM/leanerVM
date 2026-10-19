/-
  LeanerVM.Protocol.ToArkLib.Refutation

  What a verifier cannot have when it omits a check, or makes one the honest prover fails:
  round-by-round knowledge soundness below error one, and perfect completeness.
  Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.GuardedVerdict

/-!
# Refuting a verifier

Two facts about what a verifier cannot have, for showing that a check is load-bearing.

* `Verifier.not_rbr_of_escape`: at a challenge round, if from some prefix a knowledge state
  function is false for every witness while after every challenge some witness makes it true,
  then no round-by-round knowledge error below one is possible at that round: the escape event
  is certain. `Verifier.not_rbr` is its form through acceptance, at a round after which only
  the prover speaks: the verifier can be brought to accept after every challenge.
  `Verifier.not_rbr_zero` is the case of the first round, where the prefix is empty and the
  state function is false because the statement has no witness.
* `Reduction.not_perfectCompleteness_of_reject`: if the prover, on a statement in the input
  relation, can reach a transcript on which a guarded verifier's check fails, or whose verdict
  leaves the output relation, the reduction is not perfectly complete. The reachable runs are
  those under the shared oracles' implementation and uniform challenges;
  `Reduction.not_perfectCompleteness_of_reject'` is the case without shared oracles, where
  they are the prover's own runs.

The supporting facts: the prefix of length `j + 1` of a full transcript is its prefix of length
`j` followed by its entry at `j`; a knowledge state function true at the end of a transcript is
true, for some witness, at every earlier round after which only the prover speaks; a guarded
verifier whose check passes accepts with positive probability; the run of a reduction with a
guarded verifier is the prover's run followed by the verdict; and an implementation under which
every answer to every query is reachable does not shrink a computation's support.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal

public section

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ}
  {pSpec : ProtocolSpec n}

/-! ## Transcript prefixes -/

/-- The prefix of length `j + 1` of a full transcript is its prefix of length `j` followed by
its entry at `j`. -/
private theorem FullTranscript.take_succ_eq_concat (full : pSpec.FullTranscript) (j : Fin n) :
    full.take j.succ.val j.succ.is_le =
      Transcript.concat (full j) (full.take j.val j.castSucc.is_le) :=
  Fin.take_succ_eq_snoc j.val j.isLt full

/-! ## Knowledge state functions along a transcript -/

section StateFunction

variable {V : Verifier oSpec StmtIn StmtOut pSpec} {σ : Type} {init : ProbComp σ}
  {impl : QueryImpl oSpec (StateT σ ProbComp)} {relIn : Set (StmtIn × WitIn)}
  {relOut : Set (StmtOut × WitOut)} {WitMid : Fin (n + 1) → Type}
  {E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid}
  (kSF : V.KnowledgeStateFunction init impl relIn relOut E)

/-- A knowledge state function true at the end of a full transcript is true, for some witness,
at every earlier round after which only the prover speaks. -/
theorem Verifier.KnowledgeStateFunction.exists_toFun_take (s : StmtIn)
    (full : pSpec.FullTranscript) (m : Fin (n + 1))
    (hlater : ∀ j : Fin n, m.val ≤ j.val → pSpec.dir j = .P_to_V) {w : WitMid (Fin.last n)}
    (hw : kSF.toFun (Fin.last n) s full w) :
    ∃ w', kSF.toFun m s (full.take m.val m.is_le) w' := by
  induction m using Fin.reverseInduction with
  | last => exact ⟨w, hw⟩
  | cast j ih =>
    obtain ⟨w', hw'⟩ := ih fun j' hj' ↦
      hlater j' (le_trans (Fin.val_castSucc j).le (le_trans (Nat.le_succ _) hj'))
    rw [FullTranscript.take_succ_eq_concat] at hw'
    exact ⟨_, kSF.toFun_next j (hlater j (Fin.val_castSucc j).le) s _ _ w' hw'⟩

/-- Where the statement has no witness, a knowledge state function is false at round zero for
every witness, at any index of value zero. -/
private theorem Verifier.KnowledgeStateFunction.not_toFun_of_val_eq_zero (s : StmtIn)
    (hin : ∀ w, (s, w) ∉ relIn) (m : Fin (n + 1)) (hm : m.val = 0) (tr : Transcript m pSpec)
    (w : WitMid m) : ¬ kSF.toFun m s tr w := by
  have h0 : m = 0 := Fin.ext (by simpa using hm)
  subst h0
  rw [Subsingleton.elim tr default]
  exact fun h ↦ hin _ ((kSF.toFun_empty s w).mpr h)

end StateFunction

/-! ## No round-by-round knowledge soundness below error one -/

section NotRbr

variable {V : Verifier oSpec StmtIn StmtOut pSpec} [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
  {WitMid : Fin (n + 1) → Type}
  {E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid}
  {kSF : V.KnowledgeStateFunction init impl relIn relOut E} {ε : pSpec.ChallengeIdx → ℝ≥0}

/-- No round-by-round knowledge error below one at a challenge round from whose prefix the
state function is false for every witness while, after every challenge, some witness makes it
true: the escape event is certain. -/
theorem Verifier.not_rbr_of_escape
    (h : V.rbrKnowledgeSoundnessWorstCaseWith init impl relIn relOut WitMid E kSF ε)
    (i : pSpec.ChallengeIdx) (s : StmtIn) (tr : Transcript i.1.castSucc pSpec)
    (hbad : ∀ w, ¬ kSF.toFun i.1.castSucc s tr w)
    (hesc : ∀ c : pSpec.Challenge i, ∃ w, kSF.toFun i.1.succ s (tr.concat c) w) :
    1 ≤ ε i := by
  have hall : ∀ c : pSpec.Challenge i, ∃ witMid,
      ¬ kSF.toFun i.1.castSucc s tr (E.extractMid i.1 s (tr.concat c) witMid) ∧
        kSF.toFun i.1.succ s (tr.concat c) witMid :=
    fun c ↦ (hesc c).elim fun w hw ↦ ⟨w, hbad _, hw⟩
  refine ENNReal.one_le_coe_iff.mp (le_of_eq_of_le ?_ (h s i tr))
  exact ((SampleableType.prEvent_uniformSample_eq_one_iff _).mpr hall).symm

/-- `Verifier.not_rbr_of_escape` through acceptance: at a challenge round after which only the
prover speaks, the state function is made true after every challenge when the verifier can be
brought to accept after it. -/
theorem Verifier.not_rbr
    (h : V.rbrKnowledgeSoundnessWorstCaseWith init impl relIn relOut WitMid E kSF ε)
    (i : pSpec.ChallengeIdx) (hlater : ∀ j : Fin n, i.1 < j → pSpec.dir j = .P_to_V)
    (s : StmtIn) (tr : Transcript i.1.castSucc pSpec)
    (hbad : ∀ w, ¬ kSF.toFun i.1.castSucc s tr w)
    (hacc : ∀ c : pSpec.Challenge i, ∃ full : pSpec.FullTranscript,
      full.take (i.1.val + 1) i.1.isLt = tr.concat c ∧
        ∃ witOut, 0 < Pr{let stmtOut ← OptionT.mk do
          (simulateQ impl (V.run s full)).run' (← init)}[(stmtOut, witOut) ∈ relOut]) :
    1 ≤ ε i :=
  Verifier.not_rbr_of_escape h i s tr hbad fun c ↦ by
    obtain ⟨full, hprefix, witOut, hpos⟩ := hacc c
    obtain ⟨w', hw'⟩ := Verifier.KnowledgeStateFunction.exists_toFun_take kSF s full i.1.succ
      (fun j hj ↦ hlater j (Fin.lt_def.mpr (lt_of_lt_of_le (Nat.lt_succ_self _) hj)))
      (kSF.toFun_full s full witOut hpos)
    have hpre : full.take i.1.succ.val i.1.succ.is_le = tr.concat c := hprefix
    rw [hpre] at hw'
    exact ⟨w', hw'⟩

/-- The first-round case of `Verifier.not_rbr`: the prefix `tr` is the empty transcript, on
which the state function is false because the statement has no witness. -/
theorem Verifier.not_rbr_zero
    (h : V.rbrKnowledgeSoundnessWorstCaseWith init impl relIn relOut WitMid E kSF ε)
    (i : pSpec.ChallengeIdx) (hi : i.1.val = 0)
    (hlater : ∀ j : Fin n, 0 < j.val → pSpec.dir j = .P_to_V)
    (s : StmtIn) (hin : ∀ w, (s, w) ∉ relIn) (tr : Transcript i.1.castSucc pSpec)
    (hacc : ∀ c : pSpec.Challenge i, ∃ full : pSpec.FullTranscript,
      full.take (i.1.val + 1) i.1.isLt = tr.concat c ∧
        ∃ witOut, 0 < Pr{let stmtOut ← OptionT.mk do
          (simulateQ impl (V.run s full)).run' (← init)}[(stmtOut, witOut) ∈ relOut]) :
    1 ≤ ε i :=
  Verifier.not_rbr h i (fun j hj ↦ hlater j (by rw [Fin.lt_def, hi] at hj; exact hj)) s tr
    (fun w ↦ Verifier.KnowledgeStateFunction.not_toFun_of_val_eq_zero kSF s hin i.1.castSucc
      (by simpa using hi) tr w)
    hacc

end NotRbr

/-! ## A guarded verifier that accepts -/

/-- If a guarded verifier's check passes and its verdict satisfies `P`, the verifier outputs a
statement satisfying `P` with positive probability: the converse of
`Verifier.GuardedForm.of_probEvent_pos`. -/
theorem Verifier.GuardedForm.probEvent_pos_of_check {V : Verifier oSpec StmtIn StmtOut pSpec}
    (G : V.GuardedForm) {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (stmt : StmtIn) (tr : pSpec.FullTranscript)
    (P : StmtOut → Prop) (hc : G.check stmt tr = true) (hP : P (G.out stmt tr)) :
    0 < Pr{let sample ← OptionT.mk do
      (simulateQ impl (V.run stmt tr)).run' (← init)}[P sample] := by
  have hv : V.run stmt tr = if G.check stmt tr then pure (G.out stmt tr) else failure :=
    G.verify_eq stmt tr
  rw [hv, ite_eq_left hc]
  change 0 < Pr{let sample ← OptionT.mk (do
    let st ← init
    (simulateQ impl (OptionT.run (pure (G.out stmt tr)))).run' st)}[P sample]
  rw [OptionT.run_pure]
  refine lt_of_lt_of_eq zero_lt_one
    (OptionT.prEvent_mk_simulateQ_run'_eq_one_of_support init impl _ P fun o ho ↦ ?_).symm
  rw [support_pure, Set.mem_singleton_iff] at ho
  exact ⟨_, ho, hP⟩

/-! ## The run of a reduction with a guarded verifier -/

/-- The run of a reduction whose verifier is guarded: the prover's run, then the verdict when
the check passes on the prover's transcript and a rejection otherwise. -/
private theorem Reduction.run_of_guarded
    (red : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (G : red.verifier.GuardedForm) (stmt : StmtIn) (wit : WitIn) :
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

/-! ## Reachable outputs under a full-support implementation -/

/-- An implementation under which every answer to every query is reachable from every state
does not shrink the support: every output of a computation is an output of its simulation from
any state. The converse of `support_simulateQ_run'_subset`. -/
private theorem mem_support_simulateQ_run'_of_forall {ι σ α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp))
    (hfull : ∀ (t : spec.Domain) (u : spec.Range t) (st : σ),
      ∃ st', (u, st') ∈ support ((impl t).run st))
    (oa : OracleComp spec α) {x : α} :
    x ∈ support oa → ∀ st : σ, x ∈ support ((simulateQ impl oa).run' st) := by
  induction oa using OracleComp.inductionOn with
  | pure y =>
    intro hx st
    simpa using hx
  | query_bind t k ih =>
    intro hx st
    rw [mem_support_bind_iff] at hx
    obtain ⟨u, -, hx⟩ := hx
    obtain ⟨st', hst'⟩ := hfull t u st
    have hk := ih u hx st'
    simp only [StateT.run'_eq, support_map, Set.mem_image] at hk
    obtain ⟨q, hq, rfl⟩ := hk
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind,
      support_map, support_bind, Set.mem_image, Set.mem_iUnion, exists_prop]
    exact ⟨q, ⟨(u, st'), hst', hq⟩, rfl⟩

/-! ## No perfect completeness under a failing check -/

section NotComplete

variable [∀ i, SampleableType (pSpec.Challenge i)]

/-- A reduction with a guarded verifier is not perfectly complete if, on a statement in the
input relation, its prover can reach a transcript on which the check fails or whose verdict is
outside the output relation. Reachable means under the shared oracles' implementation and
uniform challenges, from a state the initialisation can produce. -/
theorem Reduction.not_perfectCompleteness_of_reject
    (red : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) (G : red.verifier.GuardedForm)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut)) {s : StmtIn} {w : WitIn}
    (hin : (s, w) ∈ relIn)
    (hbad : ∃ st ∈ support init, ∃ pr ∈ support ((simulateQ
        (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (red.prover.run s w)).run' st),
      G.check s pr.1 = false ∨ (G.out s pr.1, pr.2.2) ∉ relOut) :
    ¬ red.perfectCompleteness init impl relIn relOut := by
  intro hpc
  rw [Reduction.perfectCompleteness_eq_prob_one] at hpc
  have h1 := (OptionT.prEvent_mk_eq_one_iff _ _).mp (hpc s w hin)
  obtain ⟨st, hst, ⟨tr, prv, wo⟩, hpr, hbad⟩ := hbad
  simp only [StateT.run'_eq, support_map, Set.mem_image] at hpr
  obtain ⟨q, hq, hq1⟩ := hpr
  -- The outcome of the run from this prover run is reachable.
  have hmem : (if G.check s tr then some ((tr, prv, wo), G.out s tr) else none) ∈
      support (do
        let st ← init
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (red.run s w).run).run' st) := by
    rw [mem_support_bind_iff]
    refine ⟨st, hst, ?_⟩
    rw [Reduction.run_of_guarded red G, simulateQ_map, StateT.run'_eq, StateT.run_map,
      Functor.map_map, support_map]
    exact ⟨q, hq, congrArg (fun a ↦ if G.check s a.1 then some (a, G.out s a.1) else none) hq1⟩
  obtain ⟨x, hx, hp⟩ := h1 _ hmem
  by_cases hc : G.check s tr = true
  · rw [ite_eq_left hc, Option.some.injEq] at hx
    subst hx
    rcases hbad with hbad | hbad
    · have hbad' : G.check s tr = false := hbad
      exact Bool.false_ne_true (hbad'.symm.trans hc)
    · exact hbad hp.1
  · rw [ite_eq_right hc] at hx
    cases hx

/-- Every query to the challenge oracles alone has an answer. -/
instance : ∀ t, Nonempty (([]ₒ + [pSpec.Challenge]ₒ).Range t)
  | .inl e => e.elim
  | .inr q => SampleableType.nonempty (pSpec.Challenge q.1)

/-- Without shared oracles, the reachable transcripts are the prover's own runs: a reduction
with a guarded verifier is not perfectly complete if its prover can reach a transcript on which
the check fails or whose verdict is outside the output relation. -/
theorem Reduction.not_perfectCompleteness_of_reject'
    (red : Reduction []ₒ StmtIn WitIn StmtOut WitOut pSpec) (G : red.verifier.GuardedForm)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut)) {s : StmtIn} {w : WitIn}
    (hin : (s, w) ∈ relIn)
    (hbad : ∃ pr ∈ support (red.prover.run s w),
      G.check s pr.1 = false ∨ (G.out s pr.1, pr.2.2) ∉ relOut) :
    ¬ red.perfectCompleteness init impl relIn relOut := by
  obtain ⟨pr, hpr, hbad⟩ := hbad
  obtain ⟨st, hst⟩ := OracleComp.support_nonempty init
  refine Reduction.not_perfectCompleteness_of_reject red G init impl relIn relOut hin
    ⟨st, hst, pr, mem_support_simulateQ_run'_of_forall _ ?_ _ hpr st, hbad⟩
  rintro (e | q) u st
  · exact e.elim
  · refine ⟨st, ?_⟩
    simp only [QueryImpl.addLift_def, QueryImpl.add_apply_inr, QueryImpl.liftTarget_apply,
      StateT.run_monadLift, monadLift_self]
    rw [mem_support_bind_iff]
    exact ⟨u, mem_support_uniformSample (pSpec.Challenge q.1), by simp⟩

end NotComplete

/-! ## Examples -/

section Examples

/-- A challenge, then a prover message, both Booleans. -/
@[reducible]
private def toySpec : ProtocolSpec 2 := ⟨!v[.V_to_P, .P_to_V], !v[Bool, Bool]⟩

private noncomputable instance : ∀ i, SampleableType (toySpec.Challenge i)
  | ⟨0, _⟩ => (inferInstance : SampleableType Bool)
  | ⟨1, h⟩ => nomatch h

/-- The verifier that accepts every transcript. -/
private def acceptAll : Verifier []ₒ Unit Unit toySpec where
  verify := fun _ _ ↦ pure ()

private def acceptAllGuarded : acceptAll.GuardedForm where
  check := fun _ _ ↦ true
  out := fun _ _ ↦ ()
  verify_eq := fun _ _ ↦ rfl

/-- Accepting every transcript leaves no round-by-round knowledge error below one for the empty
relation, whatever the extractor and the state function. -/
example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))
    {WitMid : Fin 3 → Type}
    (E : Extractor.RoundByRound (OracleSpec.emptySpec.{0, 0}) Unit Unit Unit toySpec WitMid)
    (kSF : acceptAll.KnowledgeStateFunction init impl ∅ Set.univ E)
    (ε : toySpec.ChallengeIdx → ℝ≥0)
    (h : acceptAll.rbrKnowledgeSoundnessWorstCaseWith init impl ∅ Set.univ WitMid E kSF ε) :
    1 ≤ ε ⟨0, rfl⟩ :=
  Verifier.not_rbr_zero h ⟨0, rfl⟩ rfl
    (fun j hj ↦ by
      fin_cases j
      · exact absurd hj (Nat.lt_irrefl 0)
      · rfl)
    () (fun _ h ↦ h) (fun j ↦ Fin.elim0 j) fun c ↦
      ⟨Fin.snoc (Transcript.concat c fun j ↦ Fin.elim0 j) true,
        funext fun j ↦ Fin.snoc_castSucc _ _ j, (),
        Verifier.GuardedForm.probEvent_pos_of_check acceptAllGuarded init impl () _ _ rfl
          (Set.mem_univ _)⟩

/-- The verifier that rejects every transcript. -/
private def rejectAll : Verifier []ₒ Unit Unit toySpec where
  verify := fun _ _ ↦ failure

private def rejectAllGuarded : rejectAll.GuardedForm where
  check := fun _ _ ↦ false
  out := fun _ _ ↦ ()
  verify_eq := fun _ _ ↦ rfl

/-- Rejecting every transcript is not perfectly complete for the full relation, whatever the
prover. -/
example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (P : Prover []ₒ Unit Unit Unit Unit toySpec) :
    ¬ (Reduction.mk P rejectAll).perfectCompleteness init impl Set.univ Set.univ :=
  let ⟨pr, hpr⟩ := OracleComp.support_nonempty (P.run () ())
  Reduction.not_perfectCompleteness_of_reject' _ rejectAllGuarded init impl _ _ (Set.mem_univ _)
    ⟨pr, hpr, Or.inl rfl⟩

end Examples

end
end LeanerVM.Protocol
