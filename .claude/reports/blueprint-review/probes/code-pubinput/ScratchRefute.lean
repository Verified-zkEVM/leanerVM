import LeanerVM.Protocol.PublicInput
import LeanerVM.Protocol.Spine.Toy

/-!
Scratch: a verifier on the public-input schedule that, on one statement outside the input
relation, has for every challenge a message it accepts into the output relation, is not
round-by-round knowledge sound at any error below one.
-/

open LeanerVM.Parameters LeanerVM.Protocol OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal

namespace Refute

/-- The transcript `(r, cs)`, built as the state function reads it. -/
def tr2 (r : E) (cs : List E) : PublicInput.pSpec.FullTranscript :=
  Transcript.concat (m := (1 : Fin 2)) cs
    (Transcript.concat (m := (0 : Fin 2)) r (default : Transcript 0 PublicInput.pSpec))

theorem tr2_zero (r : E) (cs : List E) : tr2 r cs 0 = r := rfl

theorem tr2_one (r : E) (cs : List E) : tr2 r cs 1 = cs := rfl

theorem not_rbr {StmtIn StmtOut : Type} {relIn : Set (StmtIn × Unit)}
    {relOut : Set (StmtOut × Unit)}
    (V : Verifier []ₒ StmtIn StmtOut PublicInput.pSpec) (G : V.GuardedForm)
    (impl : QueryImpl []ₒ (StateT Unit ProbComp))
    (stmt : StmtIn) (hin : (stmt, ()) ∉ relIn) (msg : E → List E)
    (hacc : ∀ r, G.check stmt (tr2 r (msg r)) = true ∧
      (G.out stmt (tr2 r (msg r)), ()) ∈ relOut)
    (ε : PublicInput.pSpec.ChallengeIdx → ℝ≥0) (hε : ε ⟨0, rfl⟩ < 1) :
    ¬ V.rbrKnowledgeSoundnessWorstCase (pure ()) impl relIn relOut ε := by
  rintro ⟨WitMid, ext, kSF, h⟩
  have hbound := h stmt ⟨0, rfl⟩ (default : Transcript 0 PublicInput.pSpec)
  -- Every challenge is a bad challenge.
  have hall : ∀ r : E, ∃ witMid,
      ¬ kSF (Fin.castSucc 0) stmt (default : Transcript 0 PublicInput.pSpec)
          (ext.extractMid 0 stmt
            (Transcript.concat (m := (0 : Fin 2)) r
              (default : Transcript 0 PublicInput.pSpec)) witMid) ∧
        kSF (Fin.succ 0) stmt (Transcript.concat (m := (0 : Fin 2)) r
          (default : Transcript 0 PublicInput.pSpec)) witMid := by
    intro r
    obtain ⟨hc, hout⟩ := hacc r
    have hpos : Pr[fun stmtOut => (stmtOut, ()) ∈ relOut
        | OptionT.mk do (simulateQ impl (V.run stmt (tr2 r (msg r)))).run' (← (pure () : ProbComp Unit))] > 0 := by
      have hv : V.run stmt (tr2 r (msg r)) = pure (G.out stmt (tr2 r (msg r))) := by
        have := G.verify_eq stmt (tr2 r (msg r))
        rw [if_pos hc] at this
        exact this
      rw [hv]
      change Pr[_ | OptionT.mk (do let st ← (pure () : ProbComp Unit); (simulateQ impl (OptionT.run
        (pure (G.out stmt (tr2 r (msg r))) : OptionT (OracleComp []ₒ) StmtOut))).run' st)] > 0
      rw [OptionT.run_pure, simulateQ_pure]
      rw [gt_iff_lt, probEvent_pos_iff]
      refine ⟨G.out stmt (tr2 r (msg r)), ?_, hout⟩
      simp
    have hfull := kSF.toFun_full stmt (tr2 r (msg r)) () hpos
    have hnext := kSF.toFun_next 1 rfl stmt
      (Transcript.concat (m := (0 : Fin 2)) r (default : Transcript 0 PublicInput.pSpec))
      (msg r) _ hfull
    refine ⟨_, ?_, hnext⟩
    intro h0
    exact hin ((kSF.toFun_empty stmt _).mpr h0)
  -- So the bad event has probability one.
  have hone : Pr[fun challenge : E => ∃ witMid,
      ¬ kSF (Fin.castSucc 0) stmt (default : Transcript 0 PublicInput.pSpec)
          (ext.extractMid 0 stmt
            (Transcript.concat (m := (0 : Fin 2)) challenge
              (default : Transcript 0 PublicInput.pSpec)) witMid) ∧
        kSF (Fin.succ 0) stmt (Transcript.concat (m := (0 : Fin 2)) challenge
          (default : Transcript 0 PublicInput.pSpec)) witMid | $ᵗ E] = 1 := by
    rw [probEvent_eq_one_iff]
    exact ⟨by simp, fun r _ ↦ hall r⟩
  have hle : (1 : ℝ≥0∞) ≤ ((ε ⟨0, rfl⟩ : ℝ≥0) : ℝ≥0∞) := hone ▸ hbound
  exact absurd (ENNReal.coe_lt_one_iff.mpr hε) (not_lt.mpr hle)

end Refute

namespace Refute

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
  obtain ⟨x, hx, hev⟩ := probEvent_pos_iff.mp hpos
  rw [OptionT.mem_support_iff, OptionT.run_mk, mem_support_bind_iff] at hx
  obtain ⟨s, _, hx⟩ := hx
  exact h (some x) (support_simulateQ_run'_subset _ _ s hx) x rfl hev

end Refute
