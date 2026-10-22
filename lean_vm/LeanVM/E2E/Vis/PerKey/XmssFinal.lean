/-
  LeanVM.E2E.Vis.PerKey.XmssFinal

  W-vis, P7b: the per-key leanXMSS reduction wins. Its forgery's check passes wherever the game
  wins against key `j`, and so the game's win against key `j` without a key coincidence is at most
  the reduction's advantage in leanXMSS's single-key game.
-/

module

public import LeanVM.E2E.Vis.PerKey.XmssLog

/-!
# The per-key leanXMSS reduction wins (W-vis, P7b)

* `run_finishJ`: where the reduction's run wins against key `j` (`XWinAt j`), the trace's answers
  outside the private class are in the challenger's cache, and the challenger's log is key `j`'s
  record with distinct leaves, the single-key game's final check returns `true`. Key `j`'s
  verification queries only scheme inputs of its parameter (`xmss_verify_queries`), outside the
  private class, so it reads the challenger's cache alone.
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

/-- A trace's answers outside a class. -/
def lookOff (Pr : List UInt8 → Prop) [DecidablePred Pr] (tr : Log) (x : List UInt8) :
    Option Digest := if Pr x then none else look tr x

/-- **Verification reads only its key's inputs**: valid under a trace's answers, it is valid under
those outside the private class of its key's parameter. -/
theorem xmssVerifyWith_lookOff {tr : Log} {pk : LeanXmss.PublicKey} {msg : LeanXmss.Message}
    {σ : LeanXmss.Signature} (h : xmssVerifyWith (look tr) pk msg σ = some true) :
    xmssVerifyWith (lookOff (PrivJ (LeanXmss.bytesLE 16 pk.parameter)) tr) pk msg σ = some true := by
  rw [xmssVerifyWith_eq_simulateQ] at h ⊢
  rw [← h]
  refine simulateQ_congr_of_allQueries _ _ _ (fun x hx ↦ ?_)
    ((queriesSat_iff _ _).mp (xmss_verify_queries pk msg σ))
  simp only [lookOff, not_privJ_of_schemeInput hx, ↓reduceIte]

/-- **A cache holding a trace's answers outside a class**, from a merged cache that holds the
whole trace. -/
theorem cacheHas_lookOff (Pr : List UInt8 → Prop) [DecidablePred Pr]
    {cpriv cpub : QueryCache LeanXmss.HashSpec} {tr : Log}
    (hc : XmssRed.CacheTr (mergeCache Pr cpriv cpub) tr) : CacheHas cpub (lookOff Pr tr) := by
  intro x d hx
  unfold lookOff at hx
  split at hx
  · cases hx
  · rename_i hp
    obtain ⟨i, hi, hei, -⟩ := (look_eq_some_iff tr x d).mp hx
    have h := hc _ (List.getElem_mem hi)
    rw [hei] at h
    simp only [mergeCache, QueryCache.ofFn_apply, hp, ↓reduceIte, hBits] at h
    exact h

namespace PerKeyX

variable {nx ns : ℕ} [Sphincs.Params]

/-- **The single-key game's final check**, on a forgery and the challenger's log. -/
noncomputable def finishJ (pkj : LeanXmss.PublicKey)
    (p : LeanXmss.Forgery × QueryLog LeanXmss.SigningSpec) : OracleComp OW Bool := do
  let verified ← liftM (LeanXmss.Concrete.verify pkj p.1.message p.1.signature :
    OracleComp LeanXmss.HashSpec Bool)
  return decide (LeanXmss.SigningTranscript.Valid p.2 ∧
    ¬ LeanXmss.SigningTranscript.Contains p.2 p.1) && verified

/-- **The check passes on a win.** -/
theorem run_finishJ (j : Fin nx) (pkj : LeanXmss.PublicKey) (r : XmssRed.BOut nx ns)
    (log : QueryLog LeanXmss.SigningSpec) (cpriv cpub : QueryCache LeanXmss.HashSpec)
    (hw : XWinAt j (outJ r).1 (outJ r).2) (hk : (r.1.xmss j).1 = pkj)
    (hc : XmssRed.CacheTr (mergeCache (PrivJ (LeanXmss.bytesLE 16 pkj.parameter)) cpriv cpub)
      (outJ r).2)
    (hlog : XmssRed.conv (r.2.2.2.2.xlog j) = log) (hinv : XInvJ j r.2.2.2.2) :
    (simulateQ owImpl (finishJ pkj (forgeryOfJ j r, log))).run' cpub = pure true := by
  unfold forgeryOfJ
  simp only [hw, ↓reduceDIte]
  obtain ⟨-, hforged, hσ⟩ := hw.2.choose_spec.choose_spec
  set msg := hw.2.choose
  set σ := hw.2.choose_spec.choose
  have hk' : ((outJ r).1.keys.xmss j).1 = pkj := hk
  have hσ' : xmssVerifyWith (look (outJ r).2) pkj msg σ = some true := by rw [← hk']; exact hσ
  have hver : (simulateQ (randomOracle : QueryImpl LeanXmss.HashSpec
      (StateT (QueryCache LeanXmss.HashSpec) ProbComp))
      (LeanXmss.Concrete.verify pkj msg σ : OracleComp LeanXmss.HashSpec Bool)).run cpub =
      pure (true, cpub) :=
    run_verify_of_xmssVerifyWith (cacheHas_lookOff _ hc) (xmssVerifyWith_lookOff hσ')
  unfold finishJ
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind]
  rw [QueryImpl.simulateQ_add_liftM_right, hver]
  simp only [pure_bind, simulateQ_pure, StateT.run_pure, map_pure, Bool.and_true]
  congr 1
  simp only [decide_eq_true_eq]
  rw [← hlog]
  refine ⟨?_, ?_⟩
  · simpa [LeanXmss.SigningTranscript.Valid, XmssRed.conv, List.map_map, Function.comp_def, XInvJ]
      using hinv
  · rintro ⟨e, he, hm, hs⟩
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    simp only at hm hs
    rw [hforged e' he' hm] at hs
    exact absurd hs (by simp)

end PerKeyX

end
end LeanVM.E2E
