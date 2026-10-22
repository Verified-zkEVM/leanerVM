/-
  LeanVM.E2E.Vis.NoForgery

  W-vis, P6: the no-forgery event at V_I's trace, and its bound from the chain's bad events and
  the per-key hybrid.
-/

module

public import LeanVM.E2E.Vis.PerKey.Sum

/-!
# No forgery at V_I's trace (W-vis, P6)

* `BreaksVis z tr`: V_I accepts, and the root statement has a forged claim of an honest key or a
  DA claim V_I's trace `tr` does not back. Its DA part is stronger than `Breaks`'s, which asks the
  oracle's final log: the trace is a sub-log of it (`breaksVis_of_breaks`,
  `prEvent_breaks_le_breaksVis`).
* `forged_of_breaksVis`: on a reachable outcome of `gameRec` without the chain's bad events
  (`AggBadV`), a break is a forgery: every DA claim is backed by the trace (P5).
* `prEvent_breaksVis_le_of`: the break's probability is at most the bad events' plus, per key,
  the reduction's win without a coincidence at its key and that coincidence.
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

variable {nx ns : ℕ} [Sphincs.Params]

/-- **The adversary wins at V_I's trace**: V_I accepts, and the root statement has a forged claim
or a DA claim V_I's trace `tr` does not back. -/
def BreaksVis (z : GameOutcome nx ns) (tr : Log) : Prop :=
  z.accepted = true ∧
    (Forged z ∨ ∃ c ∈ z.statement.claims.da, ¬ DaBacked tr deployedPads.1 deployedPads.2 c)

omit [Sphincs.Params] in
/-- **A DA claim backed by a log is backed by every log answering it.** -/
theorem daBacked_mono {ℓ ℓ' : Log} (h : LookSub (look ℓ) (look ℓ')) {pc pr : LeanDa.Digest}
    {c : DaClaim} (hc : DaBacked ℓ pc pr c) : DaBacked ℓ' pc pr c := by
  obtain ⟨rows, h1, h2, h3, hcom, hvd⟩ := hc
  exact ⟨rows, h1, h2, h3, commitCodewordsWith_optLE h pc pr rows _ hcom,
    vectorDigestOfWith_mono h hvd⟩

/-- **A break against the final log is one against the trace**, for a trace the final log
answers. -/
theorem breaksVis_of_breaks {z : GameOutcome nx ns} {tr ℓ : Log} (hsub : TrSub tr (look ℓ))
    (h : Breaks z ℓ) : BreaksVis z tr := by
  refine ⟨h.1, ?_⟩
  rcases h.2 with hf | ⟨c, hc, hn⟩
  · exact Or.inl hf
  · exact Or.inr ⟨c, hc, fun hb ↦ hn (daBacked_mono hsub.lookSub hb)⟩

/-- **Today's event is a break at the trace**: in the game, a break against the oracle's final log
is at most as likely as a break at V_I's trace in the game with V_I's trace. -/
theorem prEvent_breaks_le_breaksVis (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) :
    Pr{let z ← game guest fuel budget A}[Breaks z.1 z.2] ≤
      Pr{let p ← gameRec guest fuel budget A}[BreaksVis p.1.1 p.1.2] := by
  rw [← gameRec_map, prEvent_map]
  exact prEvent_mono_of_support _ _ _ fun p hp h ↦ breaksVis_of_breaks (gameRec_trace hp).1 h

/-- **On a good log, a break at the trace is a forgery**: the trace backs every DA claim. -/
theorem forged_of_breaksVis
    (hG : ∀ (ℓ : Log) (rows : List BlakeRow) (h : TableOK (look ℓ) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓ h))
    {fuel budget : ℕ} {A : GameAdversary nx ns} {p : (GameOutcome nx ns × Log) × Log}
    (hp : p ∈ support (gameRec Guest.guest fuel budget A)) (hb : BreaksVis p.1.1 p.1.2)
    (hbad : ¬ AggBadV p.1.1.keys p.2) : Forged p.1.1 := by
  rcases hb.2 with hf | ⟨c, hc, hn⟩
  · exact hf
  · have hk := gameRec_knows hG hp hb.1 (not_aggBadT_of_not_aggBadV hbad)
      (rankOK_of_not_aggBadV hbad)
    exact absurd (hk.2.2 c hc) hn

/-- **The break, from the bad events and the per-key hybrid.** In the game with V_I's trace, if
reduction `j`'s win without a coincidence at key `j` has probability at most `ax` (leanXMSS) or
`as` (leanSPHINCS), and each key's coincidence at most `k`, a break at the trace has probability
at most the bad events' plus `n_x (ax + k) + n_s (as + k)`. -/
theorem prEvent_breaksVis_le_of
    (hG : ∀ (ℓ : Log) (rows : List BlakeRow) (h : TableOK (look ℓ) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓ h))
    (fuel budget : ℕ) (A : GameAdversary nx ns) {ax as k : ℝ≥0∞}
    (hx : ∀ j : Fin nx, Pr{let p ← gameRec Guest.guest fuel budget A}[XWinAt j p.1.1 p.1.2 ∧
      ¬ KeyCollAt p.1.1.keys (Fin.castAdd ns j)] ≤ ax)
    (hs : ∀ j : Fin ns, Pr{let p ← gameRec Guest.guest fuel budget A}[SWinAt j p.1.1 p.1.2 ∧
      ¬ KeyCollAt p.1.1.keys (Fin.natAdd nx j)] ≤ as)
    (hk : ∀ idx, Pr{let p ← gameRec Guest.guest fuel budget A}[KeyCollAt p.1.1.keys idx] ≤ k) :
    Pr{let p ← gameRec Guest.guest fuel budget A}[BreaksVis p.1.1 p.1.2] ≤
      Pr{let p ← gameRec Guest.guest fuel budget A}[AggBadV p.1.1.keys p.2] +
        (nx * (ax + k) + ns * (as + k)) := by
  calc Pr{let p ← gameRec Guest.guest fuel budget A}[BreaksVis p.1.1 p.1.2]
      ≤ Pr{let p ← gameRec Guest.guest fuel budget A}[AggBadV p.1.1.keys p.2 ∨
          (p.1.1.accepted = true ∧ Forged p.1.1 ∧ ¬ AggBadV p.1.1.keys p.2)] := by
        refine prEvent_mono_of_support _ _ _ fun p hp h ↦ ?_
        by_cases hbad : AggBadV p.1.1.keys p.2
        · exact Or.inl hbad
        · exact Or.inr ⟨h.1, forged_of_breaksVis hG hp h hbad, hbad⟩
    _ ≤ _ := prEvent_or_le _ _ _
    _ ≤ _ := by
        refine add_le_add le_rfl ((prEvent_forged_le_perKey hG fuel budget A).trans ?_)
        refine add_le_add ?_ ?_
        · refine (Finset.sum_le_sum fun j _ ↦ add_le_add (hx j) (hk _)).trans ?_
          simp [mul_add]
        · refine (Finset.sum_le_sum fun j _ ↦ add_le_add (hs j) (hk _)).trans ?_
          simp [mul_add]

end

end LeanVM.E2E
