import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.Data.MvPolynomial.SchwartzZippelCounting

/-! Probe D3: the transcript-level reading of ArkLib's round-by-round knowledge soundness
(pin `dca90385`), proved here because ArkLib admits `rbrKnowledgeSoundness_implies_knowledgeSoundness`.

For a verifier `V`, an extractor `E` and a knowledge state function `K`:
if `V` can accept a full transcript with an output in the output relation, then either the
witness computed from the transcript by running `E` backwards is in the input relation, or, at
some verifier round of that transcript, the challenge is in the bad set of the prefix before it.
`rbrKnowledgeSoundnessWorstCaseWith` is the statement that every bad set has probability at most
the error of its round. No probability is used in the implication itself. -/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Probe

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ}
  {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
  {V : Verifier oSpec StmtIn StmtOut pSpec} {W : Fin (n + 1) → Type}
  {E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec W}

/-- The straight-line extractor read off a round-by-round extractor: from the intermediate
witness after round `m`, back to an input witness, one round at a time. -/
def toInput (E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec W) (s : StmtIn) :
    (m : Fin (n + 1)) → Transcript m pSpec → W m → WitIn :=
  Fin.induction (fun _ w => cast E.eqIn w)
    (fun m ih tr w => ih (Fin.init tr) (E.extractMid m s tr w))

/-- The bad challenges after a prefix, at the verifier round `j`. -/
def badSet (K : V.KnowledgeStateFunction init impl relIn relOut E) (s : StmtIn)
    (j : pSpec.ChallengeIdx) (pre : Transcript j.1.castSucc pSpec) : Set (pSpec.Challenge j) :=
  {c | ∃ w, ¬ K j.1.castSucc s pre (E.extractMid j.1 s (pre.concat c) w) ∧
    K j.1.succ s (pre.concat c) w}

/-- Worst-case round-by-round knowledge soundness is: every bad set has probability at most the
error of its round. By definition. -/
theorem rbr_iff_badSet (K : V.KnowledgeStateFunction init impl relIn relOut E)
    (ε : pSpec.ChallengeIdx → ℝ≥0) :
    V.rbrKnowledgeSoundnessWorstCaseWith init impl relIn relOut W E K ε ↔
      ∀ s j pre, Pr[fun c => c ∈ badSet K s j pre | $ᵗ (pSpec.Challenge j)] ≤ ε j :=
  Iff.rfl

/-- Some verifier round before round `m` of the transcript has its challenge in the bad set of
the prefix before it. -/
def badSomewhere (K : V.KnowledgeStateFunction init impl relIn relOut E) (s : StmtIn) :
    (m : Fin (n + 1)) → Transcript m pSpec → Prop :=
  Fin.induction (fun _ => False)
    (fun m ih tr =>
      (∃ h : pSpec.dir m = .V_to_P,
        (tr (Fin.last m) : pSpec.Challenge ⟨m, h⟩) ∈ badSet K s ⟨m, h⟩ (Fin.init tr)) ∨
      ih (Fin.init tr))

/-- A true state after round `m` yields a valid extracted input witness, unless a challenge
before round `m` was bad. -/
theorem state_imp (K : V.KnowledgeStateFunction init impl relIn relOut E) (s : StmtIn) :
    ∀ (m : Fin (n + 1)) (tr : Transcript m pSpec) (w : W m), K m s tr w →
      (s, toInput E s m tr w) ∈ relIn ∨ badSomewhere K s m tr := by
  intro m
  induction m using Fin.induction with
  | zero =>
    intro tr w h
    left
    have htr : tr = default := Subsingleton.elim _ _
    subst htr
    simpa [toInput] using (K.toFun_empty s w).mpr h
  | succ m ih =>
    intro tr w h
    have htr : Transcript.concat (tr (Fin.last m)) (Fin.init tr) = tr := Fin.snoc_init_self tr
    simp only [toInput, badSomewhere, Fin.induction_succ]
    by_cases hprev : K m.castSucc s (Fin.init tr) (E.extractMid m s tr w)
    · rcases ih _ _ hprev with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (Or.inr h2)
    · refine Or.inr (Or.inl ?_)
      have h' : K m.succ s (Transcript.concat (tr (Fin.last m)) (Fin.init tr)) w :=
        (congrArg (fun t : Transcript m.succ pSpec => K m.succ s t w) htr).mpr h
      have hprev' : ¬ K m.castSucc s (Fin.init tr)
          (E.extractMid m s (Transcript.concat (tr (Fin.last m)) (Fin.init tr)) w) :=
        (congrArg (fun t : Transcript m.succ pSpec =>
          ¬ K m.castSucc s (Fin.init tr) (E.extractMid m s t w)) htr).mpr hprev
      by_cases hdir : pSpec.dir m = .V_to_P
      · exact ⟨hdir, w, hprev', h'⟩
      · exact absurd (K.toFun_next m (Direction.not_P_to_V_eq_V_to_P hdir) s (Fin.init tr)
          (tr (Fin.last m)) w h') hprev'

/-- **The plain reading.** If the verifier can accept the transcript `tr` with an output that the
output relation relates to `wOut`, then the witness extracted from `tr` and `wOut` is in the
input relation, or some challenge of `tr` is in the bad set of the prefix before it. -/
theorem accept_imp_extract_or_bad (K : V.KnowledgeStateFunction init impl relIn relOut E)
    (s : StmtIn) (tr : pSpec.FullTranscript) (wOut : WitOut)
    (hacc : Pr[fun t => (t, wOut) ∈ relOut | OptionT.mk do
      (simulateQ impl (V.run s tr)).run' (← init)] > 0) :
    (s, toInput E s (Fin.last n) tr (E.extractOut s tr wOut)) ∈ relIn ∨
      badSomewhere K s (Fin.last n) tr :=
  state_imp K s (Fin.last n) tr _ (K.toFun_full s tr wOut hacc)

end Probe

#print axioms Probe.accept_imp_extract_or_bad
#print axioms Probe.rbr_iff_badSet
#print axioms schwartz_zippel_counting
#check @schwartz_zippel_counting
#check @prob_eval_zero_le_div
