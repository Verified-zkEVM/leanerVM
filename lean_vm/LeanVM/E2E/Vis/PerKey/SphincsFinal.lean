/-
  LeanVM.E2E.Vis.PerKey.SphincsFinal

  W-vis, P7b: the per-key leanSPHINCS reduction wins. Its forgery's check passes wherever the game
  wins against leanSPHINCS key `j`.
-/

module

public import LeanVM.E2E.Vis.PerKey.SphincsLog
public import LeanVM.E2E.Vis.PerKey.XmssFinal

/-!
# The per-key leanSPHINCS reduction wins (W-vis, P7b)

The leanSPHINCS counterpart of `Vis/PerKey/XmssFinal.lean`.

* `run_finishJS`: where the reduction's run wins against key `j` (`SWinAt j`), the trace's answers
  outside the private class are in the challenger's cache, and the challenger's log is key `j`'s
  record within the signature limit, the single-key game's final check (`finishJS`, the steps of
  `Sphincs.Security.Det.gameCoreDet` after the adversary's run) returns `true`. Key `j`'s
  verification queries only scheme inputs of its parameter (`sphincs_verify_queries`), outside the
  private class, so it reads the challenger's cache alone (`sphincsVerifyWith_lookOff`).
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

/-- **Verification reads only its key's inputs**: valid under a trace's answers, it is valid under
those outside the private class of its key's parameter. -/
theorem sphincsVerifyWith_lookOff [Sphincs.Params] {tr : Log} {pk : Sphincs.PublicKey}
    {msg : Sphincs.Message} {σ : Sphincs.Signature}
    (h : sphincsVerifyWith (look tr) pk msg σ = some true) :
    sphincsVerifyWith (lookOff (PrivJ (Sphincs.bytesLE 16 pk.parameter)) tr) pk msg σ =
      some true := by
  rw [sphincsVerifyWith_eq_simulateQ] at h ⊢
  rw [← h]
  refine simulateQ_congr_of_allQueries _ _ _ (fun x hx ↦ ?_)
    ((queriesSat_iff _ _).mp (sphincs_verify_queries pk msg σ))
  simp only [lookOff, not_privJ_of_schemeInput hx, ↓reduceIte]

namespace PerKeyS

variable {nx ns : ℕ} [Sphincs.Params]

/-- **The single-key game's final check**, on a forgery and the challenger's log
(`Sphincs.Security.Det.gameCoreDet` after the adversary's run). -/
noncomputable def finishJS (pkj : Sphincs.PublicKey)
    (p : Sphincs.Forgery × QueryLog Sphincs.SigningSpec) : OracleComp OW Bool := do
  let verified ← sLift (Sphincs.Concrete.verify pkj p.1.message p.1.signature :
    OracleComp Sphincs.HashSpec Bool)
  return decide (Sphincs.SigningTranscript.Valid p.2 ∧
    ¬ Sphincs.SigningTranscript.Contains p.2 p.1) && verified

/-- **The check passes on a win.** -/
theorem run_finishJS (j : Fin ns) (pkj : Sphincs.PublicKey) (r : XmssRed.BOut nx ns)
    (log : QueryLog Sphincs.SigningSpec) (cpriv cpub : QueryCache LeanXmss.HashSpec)
    (hw : SWinAt j (outJS r).1 (outJS r).2) (hk : (r.1.sphincs j).1 = pkj)
    (hc : XmssRed.CacheTr (mergeCache (PrivJ (Sphincs.bytesLE 16 pkj.parameter)) cpriv cpub)
      (outJS r).2)
    (hlog : convS (r.2.2.2.2.slog j) = log) (hinv : SInvJ j r.2.2.2.2) :
    (simulateQ owImpl (finishJS pkj (forgeryOfJS j r, log))).run' cpub = pure true := by
  unfold forgeryOfJS
  simp only [hw, ↓reduceDIte]
  obtain ⟨-, hforged, hσ⟩ := hw.2.choose_spec.choose_spec
  set msg := hw.2.choose
  set σ := hw.2.choose_spec.choose
  have hk' : ((outJS r).1.keys.sphincs j).1 = pkj := hk
  have hσ' : sphincsVerifyWith (look (outJS r).2) pkj msg σ = some true := by
    rw [← hk']; exact hσ
  have hver : (simulateQ owImpl (sLift (Sphincs.Concrete.verify pkj msg σ :
      OracleComp Sphincs.HashSpec Bool))).run cpub = pure (true, cpub) := by
    unfold sLift
    have h1 := QueryImpl.simulateQ_add_liftM_right (impl₁' := unifFwdImpl Sphincs.HashSpec)
      (impl₂' := (randomOracle : QueryImpl Sphincs.HashSpec
        (StateT (QueryCache Sphincs.HashSpec) ProbComp)))
      (Sphincs.Concrete.verify pkj msg σ : OracleComp Sphincs.HashSpec Bool)
    have h2 : (simulateQ (randomOracle : QueryImpl Sphincs.HashSpec
        (StateT (QueryCache Sphincs.HashSpec) ProbComp))
        (Sphincs.Concrete.verify pkj msg σ : OracleComp Sphincs.HashSpec Bool)).run cpub =
        pure (true, cpub) :=
      run_verify_of_sphincsVerifyWith (cacheHas_lookOff _ hc) (sphincsVerifyWith_lookOff hσ')
    exact (congrArg (fun x ↦ StateT.run x cpub) h1).trans h2
  unfold finishJS
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind]
  rw [hver]
  simp only [pure_bind, simulateQ_pure, StateT.run_pure, map_pure, Bool.and_true]
  congr 1
  simp only [decide_eq_true_eq]
  rw [← hlog]
  refine ⟨?_, ?_⟩
  · simpa [Sphincs.SigningTranscript.Valid, convS, SInvJ] using hinv
  · rintro ⟨e, he, hm, hs⟩
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    simp only at hm hs
    rw [hforged e' he' hm] at hs
    exact absurd hs (by simp)

end PerKeyS

end
end LeanVM.E2E
