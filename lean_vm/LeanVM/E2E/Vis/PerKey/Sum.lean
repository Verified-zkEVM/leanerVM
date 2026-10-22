/-
  LeanVM.E2E.Vis.PerKey.Sum

  W-vis, P7c: the hybrid over keys. On the game with V_I's trace, an accepted forgery on a log
  without the chain's bad events (visible accounting) is a win of some per-key reduction, and its
  probability is at most the sum over keys of each reduction's win without a coincidence at its
  key, and that coincidence.
-/

module

public import LeanVM.E2E.Vis.Bound
public import LeanVM.E2E.Vis.PerKey.Defs

/-!
# The hybrid over keys (W-vis, P7c)

* `xWinAt_of_gameRec`, `sWinAt_of_gameRec`: on a reachable outcome of `gameRec` where V_I accepts,
  with no `AggBadV` on the final log, a forgery against key `j` has a signature valid under V_I's
  trace (P5's `gameRec_knows`, with T3's conclusion from `rankOK_of_not_aggBadV`).
* `prEvent_le_and_not_add`: an event is at most the event without `K`, plus `K`.
* `prEvent_forged_le_perKey`: the hybrid's sum.
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

variable {nx ns : ℕ} [Sphincs.Params]

/-- **A leanXMSS forgery on a good log is a win of reduction `j`.** -/
theorem xWinAt_of_gameRec
    (hG : ∀ (ℓ : Log) (rows : List BlakeRow) (h : TableOK (look ℓ) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓ h))
    {fuel budget : ℕ} {A : GameAdversary nx ns} {p : (GameOutcome nx ns × Log) × Log}
    (hp : p ∈ support (gameRec Guest.guest fuel budget A)) (ha : p.1.1.accepted = true)
    (hbad : ¬ AggBadV p.1.1.keys p.2) {j : Fin nx} (hf : ForgedXAt j p.1.1) :
    XWinAt j p.1.1 p.1.2 := by
  have hk := gameRec_knows hG hp ha (not_aggBadT_of_not_aggBadV hbad) (rankOK_of_not_aggBadV hbad)
  obtain ⟨msg, hmem, hfr⟩ := hf
  obtain ⟨σ, hσ⟩ := hk.1 _ hmem
  exact ⟨ha, msg, σ, hmem, hfr, hσ⟩

/-- **A leanSPHINCS forgery on a good log is a win of reduction `j`.** -/
theorem sWinAt_of_gameRec
    (hG : ∀ (ℓ : Log) (rows : List BlakeRow) (h : TableOK (look ℓ) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓ h))
    {fuel budget : ℕ} {A : GameAdversary nx ns} {p : (GameOutcome nx ns × Log) × Log}
    (hp : p ∈ support (gameRec Guest.guest fuel budget A)) (ha : p.1.1.accepted = true)
    (hbad : ¬ AggBadV p.1.1.keys p.2) {j : Fin ns} (hf : ForgedSAt j p.1.1) :
    SWinAt j p.1.1 p.1.2 := by
  have hk := gameRec_knows hG hp ha (not_aggBadT_of_not_aggBadV hbad) (rankOK_of_not_aggBadV hbad)
  obtain ⟨msg, hmem, hfr⟩ := hf
  obtain ⟨σ, hσ⟩ := hk.2.1 _ hmem
  exact ⟨ha, msg, σ, hmem, hfr, hσ⟩

omit [Sphincs.Params] in
/-- An event is at most the event without `K`, plus `K`. -/
theorem prEvent_le_and_not_add {α : Type} (mx : ProbComp α) (P K : α → Prop) :
    Pr{let x ← mx}[P x] ≤ Pr{let x ← mx}[P x ∧ ¬ K x] + Pr{let x ← mx}[K x] := by
  classical
  calc Pr{let x ← mx}[P x] ≤ Pr{let x ← mx}[(P x ∧ ¬ K x) ∨ K x] :=
        prEvent_mono_of_support _ _ _ fun x _ h ↦ by
          by_cases hk : K x
          · exact Or.inr hk
          · exact Or.inl ⟨h, hk⟩
    _ ≤ _ := prEvent_or_le _ _ _

/-- **The hybrid over keys (P7c).** In the game with V_I's trace, V_I accepting a forgery on a log
without the chain's bad events is at most as likely as, summed over the keys, reduction `j`'s
win without a coincidence at key `j`, plus that coincidence. -/
theorem prEvent_forged_le_perKey
    (hG : ∀ (ℓ : Log) (rows : List BlakeRow) (h : TableOK (look ℓ) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓ h))
    (fuel budget : ℕ) (A : GameAdversary nx ns) :
    Pr{let p ← gameRec Guest.guest fuel budget A}[p.1.1.accepted = true ∧ Forged p.1.1 ∧
        ¬ AggBadV p.1.1.keys p.2] ≤
      ∑ j : Fin nx, (Pr{let p ← gameRec Guest.guest fuel budget A}[XWinAt j p.1.1 p.1.2 ∧
          ¬ KeyCollAt p.1.1.keys (Fin.castAdd ns j)] +
        Pr{let p ← gameRec Guest.guest fuel budget A}[KeyCollAt p.1.1.keys (Fin.castAdd ns j)]) +
      ∑ j : Fin ns, (Pr{let p ← gameRec Guest.guest fuel budget A}[SWinAt j p.1.1 p.1.2 ∧
          ¬ KeyCollAt p.1.1.keys (Fin.natAdd nx j)] +
        Pr{let p ← gameRec Guest.guest fuel budget A}[KeyCollAt p.1.1.keys (Fin.natAdd nx j)]) := by
  calc Pr{let p ← gameRec Guest.guest fuel budget A}[p.1.1.accepted = true ∧ Forged p.1.1 ∧
        ¬ AggBadV p.1.1.keys p.2]
      ≤ Pr{let p ← gameRec Guest.guest fuel budget A}[(∃ j, XWinAt j p.1.1 p.1.2) ∨
          ∃ j, SWinAt j p.1.1 p.1.2] := by
        refine prEvent_mono_of_support _ _ _ fun p hp h ↦ ?_
        rcases (forged_iff_exists p.1.1).mp h.2.1 with ⟨j, hj⟩ | ⟨j, hj⟩
        · exact Or.inl ⟨j, xWinAt_of_gameRec hG hp h.1 h.2.2 hj⟩
        · exact Or.inr ⟨j, sWinAt_of_gameRec hG hp h.1 h.2.2 hj⟩
    _ ≤ ∑ j, Pr{let p ← gameRec Guest.guest fuel budget A}[XWinAt j p.1.1 p.1.2] +
          ∑ j, Pr{let p ← gameRec Guest.guest fuel budget A}[SWinAt j p.1.1 p.1.2] :=
        prEvent_or_exists_le_sum _ _ _
    _ ≤ _ := add_le_add (Finset.sum_le_sum fun j _ ↦ prEvent_le_and_not_add _ _ _)
        (Finset.sum_le_sum fun j _ ↦ prEvent_le_and_not_add _ _ _)

end

end LeanVM.E2E
