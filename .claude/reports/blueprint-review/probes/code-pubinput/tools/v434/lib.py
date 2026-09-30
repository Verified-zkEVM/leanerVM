# Shared text for the probes.

# Opens the probe's namespace again after the copied module.
OPEN = """
namespace LeanerVM.Protocol.@NS@

open LeanerVM.Parameters CompPoly OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal

@[expose] public section

namespace PublicInput
"""

CLOSE = """
end PublicInput

end
end LeanerVM.Protocol.@NS@
"""

# The two refutation lemmas.
REFUTE = """
/-! ## Refutation lemmas -/

/-- The transcript `(r, cs)`, built as a knowledge state function reads it. -/
def tr2 (r : E) (cs : List E) : pSpec.FullTranscript :=
  Transcript.concat (m := (1 : Fin 2)) cs
    (Transcript.concat (m := (0 : Fin 2)) r (default : Transcript 0 pSpec))

/-- A guarded verifier on the schedule `pSpec` that, on one statement outside the input
relation, has for every challenge a message it accepts into the output relation is not
round-by-round knowledge sound at an error below one: whatever the extractor and the state
function. -/
theorem not_rbr {StmtIn StmtOut : Type} {relIn : Set (StmtIn × Unit)}
    {relOut : Set (StmtOut × Unit)}
    (V : Verifier []ₒ StmtIn StmtOut pSpec) (G : V.GuardedForm)
    (impl : QueryImpl []ₒ (StateT Unit ProbComp))
    (stmt : StmtIn) (hin : (stmt, ()) ∉ relIn) (msg : E → List E)
    (hacc : ∀ r, G.check stmt (tr2 r (msg r)) = true ∧
      (G.out stmt (tr2 r (msg r)), ()) ∈ relOut)
    (ε : pSpec.ChallengeIdx → ℝ≥0) (hε : ε ⟨0, rfl⟩ < 1) :
    ¬ V.rbrKnowledgeSoundnessWorstCase (pure ()) impl relIn relOut ε := by
  rintro ⟨WitMid, ext, kSF, h⟩
  have hbound := h stmt ⟨0, rfl⟩ (default : Transcript 0 pSpec)
  -- Every challenge is a bad challenge.
  have hall : ∀ r : E, ∃ witMid,
      ¬ kSF (Fin.castSucc 0) stmt (default : Transcript 0 pSpec)
          (ext.extractMid 0 stmt
            (Transcript.concat (m := (0 : Fin 2)) r
              (default : Transcript 0 pSpec)) witMid) ∧
        kSF (Fin.succ 0) stmt (Transcript.concat (m := (0 : Fin 2)) r
          (default : Transcript 0 pSpec)) witMid := by
    intro r
    obtain ⟨hc, hout⟩ := hacc r
    have hpos : Pr{let stmtOut ← OptionT.mk do
            (simulateQ impl (V.run stmt (tr2 r (msg r)))).run'
              (← (pure () : ProbComp Unit))}[(stmtOut, ()) ∈ relOut] > 0 := by
      have hv : V.run stmt (tr2 r (msg r)) = pure (G.out stmt (tr2 r (msg r))) := by
        have := G.verify_eq stmt (tr2 r (msg r))
        rw [ite_eq_left hc] at this
        exact this
      rw [hv]
      change Pr{let sample ← OptionT.mk (do
        let st ← (pure () : ProbComp Unit)
        (simulateQ impl (OptionT.run (pure (G.out stmt (tr2 r (msg r))) :
          OptionT (OracleComp []ₒ) StmtOut))).run' st)}[(sample, ()) ∈ relOut] > 0
      rw [OptionT.run_pure, simulateQ_pure]
      rw [gt_iff_lt, OracleComp.OptionT.prEvent_mk_pos_iff]
      refine ⟨G.out stmt (tr2 r (msg r)), ?_, hout⟩
      simp
    have hfull := kSF.toFun_full stmt (tr2 r (msg r)) () hpos
    have hnext := kSF.toFun_next 1 rfl stmt
      (Transcript.concat (m := (0 : Fin 2)) r (default : Transcript 0 pSpec))
      (msg r) _ hfull
    refine ⟨_, ?_, hnext⟩
    intro h0
    exact hin ((kSF.toFun_empty stmt _).mpr h0)
  -- So the bad event has probability one.
  have hone : Pr{let challenge ← $ᵗ E}[∃ witMid,
      ¬ kSF (Fin.castSucc 0) stmt (default : Transcript 0 pSpec)
          (ext.extractMid 0 stmt
            (Transcript.concat (m := (0 : Fin 2)) challenge
              (default : Transcript 0 pSpec)) witMid) ∧
        kSF (Fin.succ 0) stmt (Transcript.concat (m := (0 : Fin 2)) challenge
          (default : Transcript 0 pSpec)) witMid] = 1 := by
    rw [OracleComp.prEvent_eq_one_iff]
    exact fun r _ ↦ hall r
  have hle : (1 : ℝ≥0∞) ≤ ((ε ⟨0, rfl⟩ : ℝ≥0) : ℝ≥0∞) := hone ▸ hbound
  exact absurd (ENNReal.coe_lt_one_iff.mpr hε) (not_lt.mpr hle)

/-- A reduction none of whose outcomes, on one input in the input relation, satisfies the
completeness event is not perfectly complete. -/
theorem not_perfectCompleteness {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, SampleableType (pSpec.Challenge i)]
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) (hin : (stmtIn, witIn) ∈ relIn)
    (h : ∀ x ∈ support (reduction.run stmtIn witIn).run, ∀ result, x = some result →
      ¬ ((result.2, result.1.2.2) ∈ relOut ∧ result.1.2.1 = result.2)) :
    ¬ reduction.perfectCompleteness init impl relIn relOut := by
  intro hc
  rw [Reduction.perfectCompleteness_eq_prob_one] at hc
  have h1 := hc stmtIn witIn hin
  dsimp only at h1
  have hpos := lt_of_lt_of_eq (zero_lt_one' ℝ≥0∞) h1.symm
  rw [OracleComp.OptionT.prEvent_mk_pos_iff] at hpos
  obtain ⟨x, hx, hev⟩ := hpos
  rw [mem_support_bind_iff] at hx
  obtain ⟨s, _, hx⟩ := hx
  exact h (some x) (support_simulateQ_run'_subset _ _ s hx) x rfl hev

/-- The error `1/|E|` is below one. -/
theorem error_lt_one : error < 1 := by
  have h2 : (1 : ℝ≥0) < (Fintype.card E : ℝ≥0) := by
    exact_mod_cast Fintype.one_lt_card
  exact (div_lt_one (lt_trans zero_lt_one h2)).mpr h2

/-- The one implementation of the empty shared oracle. -/
def noOracle : QueryImpl []ₒ (StateT Unit ProbComp) := fun q ↦ nomatch q
"""

# Pooling the values the prover sent, for the lines whose value is sent.
POOLFROM = """
/-- The claims on the lines, a line whose value is sent taking the next value of the message
(zero when the message is too short), the others the value the verifier computes. -/
def claimsFrom (r : E) : List (PublicLine I.toShape) → List E → List (ColumnClaim I)
  | [], _ => []
  | l :: ls, cs =>
    if l.sent then ⟨l.col, linePoint l.pos r, cs.headD 0⟩ :: claimsFrom r ls cs.tail
    else lineClaim I r l :: claimsFrom r ls cs

/-- The pool, with the values the prover sent. -/
def pooledFrom (s : I.Stmt × TableOut I) (r : E) (cs : List E) : I.Stmt × PubOut I :=
  (s.1, ⟨s.2.columns ++ claimsFrom I r (I.publicLines s.1) cs⟩)

/-- On the expected values, the claims are the lines' claims. -/
theorem claimsFrom_expected (r : E) (ls : List (PublicLine I.toShape)) :
    claimsFrom I r ls ((ls.filter (·.sent)).map (lineValue I r)) = ls.map (lineClaim I r) := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    by_cases h : l.sent = true
    · simp only [claimsFrom, h, if_true, List.filter_cons_of_pos, List.map_cons,
        List.headD_cons, List.tail_cons, ih, lineClaim]
    · simp only [claimsFrom, h, Bool.false_eq_true, if_false, List.filter_cons_of_neg,
        not_false_eq_true, List.map_cons, ih]

/-- On the expected values, the pool is the pool of the lines' values. -/
theorem pooledFrom_expected (s : I.Stmt × TableOut I) (r : E) :
    pooledFrom I s r (expectedValues I s.1 r) = pooled I s r := by
  simp only [pooledFrom, pooled, expectedValues, claimsFrom_expected]
"""

AXIOMS = """
#print axioms LeanerVM.Protocol.@NS@.PublicInput.verifier_verify
#print axioms LeanerVM.Protocol.@NS@.PublicInput.complete
#print axioms LeanerVM.Protocol.@NS@.PublicInput.stateFunction
#print axioms LeanerVM.Protocol.@NS@.PublicInput.rbr
"""

IMPORT_TOY = ("public import LeanerVM.Protocol.ToArkLib.KeepOracles\n",
              "public import LeanerVM.Protocol.ToArkLib.KeepOracles\npublic import LeanerVM.Protocol.Spine.Toy\n")
