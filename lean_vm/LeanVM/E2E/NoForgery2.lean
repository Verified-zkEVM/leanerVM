/-
  LeanVM.E2E.NoForgery2

  T4 and T5 with T3 from two challenges: the chain's bad events `AggBad2` (`AggBad` with the
  two-challenge prediction `Pred2` for `Pred`) have probability at most `aggBadError2`, whose T3
  term is `Q³ / (6 · 2^384)`, and the no-forgery theorem and its closed form follow.
-/

module

public import LeanVM.E2E.NoForgeryClosed
public import LeanVM.E2E.Vis.NoForgery
public import LeanVM.E2E.Vis.Pred2

/-!
# No forgery (T5) with T3 from two challenges

`AggBad2` is `AggBad` (`LeanVM/E2E/Knowledge.lean`) with T3's event `Pred (predOffset)` replaced
by `Pred2 (predOffset - 24) predOffset`, the prediction of the guest's last two matrix challenges
by one input (`LeanVM/E2E/Termination2.lean`). A two-challenge prediction is a prediction, so
`AggBad2` is contained in `AggBad` (`aggBad_of_aggBad2`) and every theorem here that assumes
`¬ AggBad2` is stronger than its `AggBad` form.

* **T4** (`aggregate_knowledge_sub2`, `aggregate_knowledge_cache2`, `aggregate_knowledge2`): on
  a log without `AggBad2`, V_I's acceptance gives the root's claims. The proof is T4 at the trace
  (`aggregate_knowledge_trace`, `Vis/Knowledge.lean`) with T3's conclusion `RankOK2` from
  `¬ Pred2` (`rankOK2_of_pred2`).
* **The bound** (`prEvent_game_aggBad2_le`): `aggBadError2 Q`, `aggBadError Q` with
  `Q³ / (6 · 2^384)` (`predError2`) for `Q (Q + 1) / 2^193` (`aggBadError2_add`).
* **T5** (`aggregate_no_forgery2`, `aggregate_no_forgery_closed2`): `noForgeryError2` and
  `closedError2`, the reductions (`XmssRed.prEvent_forgedX_le2`, `SphincsRed.prEvent_forgedS_le2`)
  as before at `¬ AggBad2`. `closedError2 ≤ closedNum2 / 2^256` with T3's term rounded up
  (`closedError2_le_num`).
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.EndToEnd.Blind LeanVM.Protocol.EndToEnd.Sound LeanVM.Protocol.Rom
open OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

/-! ## T4 -/

/-- **The bad events of the chain, T3 from two challenges**: T1's, W6's, E5's (as in `AggBad`)
and a two-challenge prediction at the offsets of the guest's last two matrix coordinates. -/
def AggBad2 (ℓ : Log) : Prop :=
  1 ≤ pot anyCertBlind.D leanVmSeeds anyProgramBlind ℓ ∨ Fail leanVmSeeds ℓ ∨
    BatchBad Guest.B1.Main.aggSeedD (bytecodeWords Guest.guest) ℓ ∨
    DaBad deployedPads.1 ℓ ∨ Pred2 (predOffset (bytecodeWords Guest.guest) - 24)
      (predOffset (bytecodeWords Guest.guest)) ℓ

/-- `AggBad2` is contained in `AggBad`. -/
theorem aggBad_of_aggBad2 {ℓ : Log} (h : AggBad2 ℓ) : AggBad ℓ :=
  h.imp_right (Or.imp_right (Or.imp_right (Or.imp_right pred_of_pred2V)))

/-- **T4 at a sub-log, T3 from two challenges.** On a log `ℓ` without `AggBad2`, for a log `ℓK`
whose answers are `ℓ`'s: if V_I accepts the root statement `s` with every hash answered by `ℓK`,
and the guest's open callees are sound over the oracle models of both logs, then every leanXMSS
and leanSPHINCS claim of `s` has a signature valid under `ℓK`, and every DA claim is backed by
`ℓ` (`aggregate_knowledge_sub`'s conclusion). -/
theorem aggregate_knowledge_sub2 {ℓ ℓK : Log}
    (hG : ∀ (rows : List BlakeRow) (h : TableOK (look ℓ) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓ h))
    (hGK : ∀ (rows : List BlakeRow) (h : TableOK (look ℓK) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓK h))
    (hbad : ¬ AggBad2 ℓ) (hsub : LookSub (look ℓK) (look ℓ)) {ip : IdealProof} {fuel : ℕ}
    {s : NodeStatement} (hv : idealVerify (look ℓK) Guest.guest ip fuel s = some true) :
    (∀ c ∈ s.claims.xmss, ∃ σ, xmssVerifyWith (look ℓK) c.1 c.2 σ = some true) ∧
    (∀ c ∈ s.claims.sphincs, ∃ σ, sphincsVerifyWith (look ℓK) c.1 c.2 σ = some true) ∧
    ∀ c ∈ s.claims.da, DaBacked ℓ deployedPads.1 deployedPads.2 c := by
  have hF : ¬ Fail leanVmSeeds ℓ := fun h ↦ hbad (Or.inr (Or.inl h))
  have h := aggregate_knowledge_trace hG hGK (fun h ↦ hbad (Or.inl h)) hF
    (fun h ↦ hbad (Or.inr (Or.inr (Or.inl h))))
    (fun h ↦ hbad (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    (rankOK2_of_pred2 hF fun h ↦ hbad (Or.inr (Or.inr (Or.inr (Or.inr h))))) hsub hv
  exact ⟨h.1, h.2.1, fun c hc ↦ daBacked_mono hsub (h.2.2 c hc)⟩

/-- **T4, cache form, T3 from two challenges** (`aggregate_knowledge_cache` at `¬ AggBad2`). -/
theorem aggregate_knowledge_cache2 {ℓ : Log}
    (hG : ∀ (rows : List BlakeRow) (h : TableOK (look ℓ) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓ h))
    (hbad : ¬ AggBad2 ℓ) {ip : IdealProof} {fuel : ℕ} {s : NodeStatement}
    (hv : idealVerify (look ℓ) Guest.guest ip fuel s = some true) :
    (∀ c ∈ s.claims.xmss, ∃ σ, xmssVerifyWith (look ℓ) c.1 c.2 σ = some true) ∧
    (∀ c ∈ s.claims.sphincs, ∃ σ, sphincsVerifyWith (look ℓ) c.1 c.2 σ = some true) ∧
    ∀ c ∈ s.claims.da, DaBacked ℓ deployedPads.1 deployedPads.2 c :=
  aggregate_knowledge_sub2 hG hG hbad (LookSub.refl _) hv

/-- **T4, unconditional, T3 from two challenges** (`aggregate_knowledge` at `¬ AggBad2`). -/
theorem aggregate_knowledge2 {ℓ : Log} (hbad : ¬ AggBad2 ℓ) {ip : IdealProof} {fuel : ℕ}
    {s : NodeStatement} (hv : idealVerify (look ℓ) Guest.guest ip fuel s = some true) :
    (∀ c ∈ s.claims.xmss, ∃ σ, xmssVerifyWith (look ℓ) c.1 c.2 σ = some true) ∧
    (∀ c ∈ s.claims.sphincs, ∃ σ, sphincsVerifyWith (look ℓ) c.1 c.2 σ = some true) ∧
    ∀ c ∈ s.claims.da, DaBacked ℓ deployedPads.1 deployedPads.2 c :=
  aggregate_knowledge_cache2 (fun _ _ ↦ guestHypsM_model _) hbad hv

/-- **The chain's bad events' error, T3 from two challenges**: `aggBadError` with
`Q³ / (6 · 2^384)` for `Q (Q + 1) / 2^193`. -/
noncomputable def aggBadError2 (Q : ℕ) : ℝ≥0∞ :=
  Q * (εLean + failBound leanVmSeeds Q) + Q * (2 / 2 ^ 192 + 4 * (Q + 1) / 2 ^ 256) +
    Q * (14 / 2 ^ 192 + 4 * Q / 2 ^ 256) + predError2 Q

/-- **Against the old error**: only T3's term differs. -/
theorem aggBadError2_add (Q : ℕ) :
    aggBadError2 Q + Q * (Q + 1) / 2 ^ 193 = aggBadError Q + predError2 Q := by
  unfold aggBadError2 aggBadError
  ring

section Game

variable {nx ns : ℕ} [Sphincs.Params]

/-- **The chain's bad events in the game**, with probability at most the sum of T1's, W6's, E5's
and T3's terms, for a game with at most `Q` hash queries. -/
theorem prEvent_game_aggBad2_le (fuel budget : ℕ) (A : GameAdversary nx ns) (Q : ℕ)
    (hQ : IsQueryBoundP (gameComp Guest.guest fuel budget A) IsHash Q) :
    Pr{let z ← game Guest.guest fuel budget A}[AggBad2 z.2] ≤
      Q * (εLean + failBound leanVmSeeds Q) + Q * (2 / 2 ^ 192 + 4 * (Q + 1) / 2 ^ 256) +
        Q * (14 / 2 ^ 192 + 4 * Q / 2 ^ 256) + predError2 Q := by
  set g := game Guest.guest fuel budget A
  have e : Pr{let z ← g}[AggBad2 z.2] ≤ Pr{let z ← g}[(((1 ≤ pot anyCertBlind.D leanVmSeeds
      anyProgramBlind z.2 ∨ Fail leanVmSeeds z.2) ∨
        BatchBad Guest.B1.Main.aggSeedD (bytecodeWords Guest.guest) z.2) ∨
      DaBad deployedPads.1 z.2) ∨ Pred2 (predOffset (bytecodeWords Guest.guest) - 24)
        (predOffset (bytecodeWords Guest.guest)) z.2] :=
    prEvent_mono_of_support _ _ _ fun z _ hz ↦ by
      rcases hz with h | h | h | h | h
      · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
      · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  refine e.trans ((prEvent_or_le _ _ _).trans (add_le_add ((prEvent_or_le _ _ _).trans
    (add_le_add ((prEvent_or_le _ _ _).trans (add_le_add ?_ ?_)) ?_)) ?_))
  · exact prEvent_game_blindBad_le Guest.guest fuel budget A Q hQ
  · exact prEvent_game_batchBad_le _ _ Guest.guest fuel budget A Q hQ
  · exact prEvent_game_daBad_le _ Guest.guest fuel budget A Q hQ
  · exact prEvent_game_pred2_le_cube _ _ Guest.guest fuel budget A Q hQ


/-- **T4 in the game, cache form.** For a game of the deployed guest with at most `Q` hash
queries, V_I accepting the adversary's root statement and idealized proof with every hash
answered by the final log, while some claim of the statement is not known under that log, has
probability at most the sum of T1's, W6's, E5's and T3's terms, if the guest's open callees are
sound over every oracle model of every log. -/
theorem prEvent_game_aggregate2_le
    (hG : ∀ (ℓ : Log) (rows : List BlakeRow) (h : TableOK (look ℓ) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓ h))
    (fuel budget : ℕ) (A : GameAdversary nx ns) (Q : ℕ)
    (hQ : IsQueryBoundP (gameComp Guest.guest fuel budget A) IsHash Q) :
    Pr{let z ← game Guest.guest fuel budget A}[
        idealVerify (look z.2) Guest.guest z.1.proof fuel z.1.statement = some true ∧
          ¬ ClaimsKnown z.2 z.1.statement] ≤
      Q * (εLean + failBound leanVmSeeds Q) + Q * (2 / 2 ^ 192 + 4 * (Q + 1) / 2 ^ 256) +
        Q * (14 / 2 ^ 192 + 4 * Q / 2 ^ 256) + predError2 Q := by
  refine le_trans (prEvent_mono_of_support _ _ _ fun z _ hz ↦ ?_)
    (prEvent_game_aggBad2_le fuel budget A Q hQ)
  obtain ⟨hv, hn⟩ := hz
  by_contra hbad
  exact hn (aggregate_knowledge_cache2 (hG z.2) hbad hv)

/-- **T4 in the game, unconditional, T3 from two challenges.** -/
theorem prEvent_game_aggregate2 (fuel budget : ℕ) (A : GameAdversary nx ns) (Q : ℕ)
    (hQ : IsQueryBoundP (gameComp Guest.guest fuel budget A) IsHash Q) :
    Pr{let z ← game Guest.guest fuel budget A}[
        idealVerify (look z.2) Guest.guest z.1.proof fuel z.1.statement = some true ∧
          ¬ ClaimsKnown z.2 z.1.statement] ≤ aggBadError2 Q :=
  prEvent_game_aggregate2_le (fun _ _ _ ↦ guestHypsM_model _) fuel budget A Q hQ

end Game

/-! ## The reductions at `¬ AggBad2` -/

namespace XmssRed

variable {nx ns : ℕ} [Sphincs.Params]

/-- **On the game with V_I's trace, a leanXMSS forgery on a good log is a win of the trace**: V_I
accepts, the forged claim has a signature valid under the trace's answers (T4 at the trace,
`aggregate_knowledge_sub2`), and the final log's cache holds the trace. -/
theorem xWin_of_gameRec2
    (hG : ∀ (ℓ : Log) (rows : List BlakeRow) (h : TableOK (look ℓ) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓ h))
    {fuel budget : ℕ} {A : GameAdversary nx ns} {p : (GameOutcome nx ns × Log) × Log}
    (hp : p ∈ support (gameRec Guest.guest fuel budget A)) (ha : p.1.1.accepted = true)
    (hf : ForgedX p.1.1) (hbad : ¬ AggBad2 p.2) :
    XWin p.1.1 p.1.2 ∧ CacheTr (logCache p.2) p.1.2 := by
  obtain ⟨hsub, hv⟩ := gameRec_trace hp
  have hk := aggregate_knowledge_sub2 (hG p.2) (hG p.1.2) hbad hsub.lookSub (hv ha)
  obtain ⟨j, msg, hmem, hforged⟩ := hf
  obtain ⟨σ, hσ⟩ := hk.1 _ hmem
  refine ⟨⟨ha, j, msg, σ, hmem, hforged, hσ⟩, fun e he ↦ ?_⟩
  rw [logCache_apply, hsub e he]
  rfl

/-- **The leanXMSS reduction (T5, leanXMSS part).** In the game of the deployed guest, V_I
accepting a root statement with a leanXMSS forgery on a log without the chain's bad events is at
most as likely as the reduction's win in leanXMSS's multi-user game, if the guest's open callees
are sound over every oracle model. -/
theorem prEvent_forgedX_le2 [NeZero nx]
    (hG : ∀ (ℓ : Log) (rows : List BlakeRow) (h : TableOK (look ℓ) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓ h))
    (fuel budget : ℕ) (A : GameAdversary nx ns) :
    Pr{let z ← game Guest.guest fuel budget A}[z.1.accepted = true ∧ ForgedX z.1 ∧ ¬ AggBad2 z.2] ≤
      LeanXmss.MultiUser.forgeAdvantage (xAdv Guest.guest fuel budget A) := by
  let F : (GameOutcome nx ns × Log) × QueryCache LeanXmss.HashSpec → Prop :=
    fun o ↦ XWin o.1.1 o.1.2 ∧ CacheTr o.2 o.1.2
  calc Pr{let z ← game Guest.guest fuel budget A}[z.1.accepted = true ∧ ForgedX z.1 ∧ ¬ AggBad2 z.2]
      = Pr{let p ← gameRec Guest.guest fuel budget A}[p.1.1.accepted = true ∧ ForgedX p.1.1 ∧
          ¬ AggBad2 p.2] := by
        rw [← gameRec_map, prEvent_map]
    _ ≤ Pr{let p ← gameRec Guest.guest fuel budget A}[F (p.1, logCache p.2)] :=
        prEvent_mono_of_support _ _ _ fun p hp h ↦ xWin_of_gameRec2 hG hp h.1 h.2.1 h.2.2
    _ = Pr{let o ← Prod.map id logCache <$> gameRec Guest.guest fuel budget A}[F o] := by
        rw [prEvent_map]; rfl
    _ = Pr{let o ← (simulateQ owImpl (simulateQ toW
          (gameCompRec Guest.guest fuel budget A))).run ∅}[F o] :=
        (evalDistEq_run_toW_nil _).prEvent_eq F
    _ = Pr{let y ← (simulateQ owImpl (xPrefix Guest.guest fuel budget A)).run ∅}[
          F (fullOut y.1.1 y.1.2.1, y.2)] := by
        rw [← map_xPrefix, simulateQ_map, StateT.run_map, prEvent_map]
    _ ≤ Pr{let b ← (simulateQ owImpl (xPrefix Guest.guest fuel budget A)).run ∅ >>= fun y ↦
          (simulateQ owImpl (finishX y.1)).run' y.2}[b = true] := by
        refine le_prEvent_bind_of_pure _ _ (fun y : ((Fin nx → LeanXmss.PublicKey ×
            LeanXmss.Seeded.SecretKey) × BOut nx ns × QueryLog (LeanXmss.MultiUser.SigningSpec nx)) ×
            QueryCache LeanXmss.HashSpec ↦ F (fullOut y.1.1 y.1.2.1, y.2))
          fun y hy hF ↦ run_finishX (guest := Guest.guest) (fuel := fuel) (budget := budget)
            (A := A) ?_ hF.1 hF.2
        have h1 : y.1 ∈ support ((simulateQ owImpl (xPrefix Guest.guest fuel budget A)).run' ∅) := by
          rw [StateT.run'_eq, support_map]; exact ⟨y, hy, rfl⟩
        exact support_simulateQ_run'_subset _ _ _ h1
    _ = LeanXmss.MultiUser.forgeAdvantage (xAdv Guest.guest fuel budget A) := by
        rw [forgeAdvantage_eq, gameCore_xAdv, simulateQ_bind, StateT.run'_eq, StateT.run_bind,
          map_bind]
        simp only [StateT.run'_eq, map_bind]

end XmssRed

namespace SphincsRed

open XmssRed (map_eq_bind_pure_comp' le_prEvent_bind_of_pure CacheTr)

variable {nx ns : ℕ} [Sphincs.Params]

/-- **On the game with V_I's trace, a leanSPHINCS forgery on a good log is a win of the
trace.** -/
theorem sWin_of_gameRec2
    (hG : ∀ (ℓ : Log) (rows : List BlakeRow) (h : TableOK (look ℓ) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓ h))
    {fuel budget : ℕ} {A : GameAdversary nx ns} {p : (GameOutcome nx ns × Log) × Log}
    (hp : p ∈ support (gameRec Guest.guest fuel budget A)) (ha : p.1.1.accepted = true)
    (hf : ForgedS p.1.1) (hbad : ¬ AggBad2 p.2) :
    SWin p.1.1 p.1.2 ∧ CacheTr (logCache p.2) p.1.2 := by
  obtain ⟨hsub, hv⟩ := gameRec_trace hp
  have hk := aggregate_knowledge_sub2 (hG p.2) (hG p.1.2) hbad hsub.lookSub (hv ha)
  obtain ⟨j, msg, hmem, hforged⟩ := hf
  obtain ⟨σ, hσ⟩ := hk.2.1 _ hmem
  refine ⟨⟨ha, j, msg, σ, hmem, hforged, hσ⟩, fun e he ↦ ?_⟩
  rw [logCache_apply, hsub e he]
  rfl

/-- **The leanSPHINCS reduction (T5, leanSPHINCS part).** In the game of the deployed guest, V_I
accepting a root statement with a leanSPHINCS forgery on a log without the chain's bad events is
at most as likely as the reduction's win in leanSPHINCS's multi-user game, if the guest's open
callees are sound over every oracle model. -/
theorem prEvent_forgedS_le2 [NeZero ns]
    (hG : ∀ (ℓ : Log) (rows : List BlakeRow) (h : TableOK (look ℓ) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓ h))
    (fuel budget : ℕ) (A : GameAdversary nx ns) :
    Pr{let z ← game Guest.guest fuel budget A}[z.1.accepted = true ∧ ForgedS z.1 ∧ ¬ AggBad2 z.2] ≤
      Sphincs.Security.Multi.forgeAdvantage (sAdv Guest.guest fuel budget A) := by
  let F : (GameOutcome nx ns × Log) × QueryCache LeanXmss.HashSpec → Prop :=
    fun o ↦ SWin o.1.1 o.1.2 ∧ CacheTr o.2 o.1.2
  calc Pr{let z ← game Guest.guest fuel budget A}[z.1.accepted = true ∧ ForgedS z.1 ∧ ¬ AggBad2 z.2]
      = Pr{let p ← gameRec Guest.guest fuel budget A}[p.1.1.accepted = true ∧ ForgedS p.1.1 ∧
          ¬ AggBad2 p.2] := by
        rw [← gameRec_map, prEvent_map]
    _ ≤ Pr{let p ← gameRec Guest.guest fuel budget A}[F (p.1, logCache p.2)] :=
        prEvent_mono_of_support _ _ _ fun p hp h ↦ sWin_of_gameRec2 hG hp h.1 h.2.1 h.2.2
    _ = Pr{let o ← Prod.map id logCache <$> gameRec Guest.guest fuel budget A}[F o] := by
        rw [prEvent_map]; rfl
    _ = Pr{let o ← romRun (simulateQ toW (gameCompRec Guest.guest fuel budget A)) ∅}[F o] :=
        (evalDistEq_run_toW_nil _).prEvent_eq F
    _ = Pr{let o ← Prod.map (fun p ↦ fullOut p.1 p.2.1) id <$>
          romRun (sPrefix Guest.guest fuel budget A) ∅}[F o] :=
        ((evalDistEq_sPrefix _ _ _ _).prEvent_eq F).symm
    _ = Pr{let y ← romRun (sPrefix Guest.guest fuel budget A) ∅}[
          F (fullOut y.1.1 y.1.2.1, y.2)] := by
        rw [prEvent_map]; rfl
    _ ≤ Pr{let b ← romRun (sPrefix Guest.guest fuel budget A) ∅ >>= fun y ↦
          (simulateQ owImpl (finishS y.1)).run' y.2}[b = true] := by
        refine le_prEvent_bind_of_pure _ _ (fun y : ((Fin ns → Sphincs.PublicKey ×
            Sphincs.Seeded.SecretKey) × XmssRed.BOut nx ns ×
              QueryLog (Sphincs.Security.Multi.SigningSpec ns)) ×
            QueryCache LeanXmss.HashSpec ↦ F (fullOut y.1.1 y.1.2.1, y.2))
          fun y hy hF ↦ run_finishS (guest := Guest.guest) (fuel := fuel) (budget := budget)
            (A := A) ?_ hF.1 hF.2
        have h1 : y.1 ∈ support ((simulateQ owImpl (sPrefix Guest.guest fuel budget A)).run' ∅) := by
          rw [StateT.run'_eq, support_map]; exact ⟨y, hy, rfl⟩
        exact support_simulateQ_run'_subset _ _ _ h1
    _ = Sphincs.Security.Multi.forgeAdvantage (sAdv Guest.guest fuel budget A) := by
        rw [forgeAdvantage_eq, gameCore_sAdv, simulateQ_bind, StateT.run'_eq, StateT.run_bind,
          map_bind]
        simp only [StateT.run'_eq, map_bind]

end SphincsRed

/-! ## No forgery -/

/-- **The no-forgery error, T3 from two challenges**: `noForgeryError` with `aggBadError2`. -/
noncomputable def noForgeryError2 (Q nx cx cs : ℕ) (εs : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  aggBadError2 Q + xmssMultiError nx (Q + cx) + εs (max 1 (Q + cs))

section NoForgery

variable {nx ns : ℕ} [Sphincs.Params]

/-- **A break on a good log is a forgery**: on every reachable outcome without the chain's bad
events, an accepted DA claim is backed. -/
theorem forged_of_breaks2
    (hG : ∀ (ℓ : Log) (rows : List BlakeRow) (h : TableOK (look ℓ) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓ h))
    {fuel budget : ℕ} {A : GameAdversary nx ns} {z : GameOutcome nx ns × Log}
    (hz : z ∈ support (game Guest.guest fuel budget A)) (hb : Breaks z.1 z.2)
    (hbad : ¬ AggBad2 z.2) :
    Forged z.1 := by
  obtain ⟨ha, hf | ⟨c, hc, hnb⟩⟩ := hb
  · exact hf
  · exact absurd ((aggregate_knowledge_cache2 (hG z.2) hbad (game_accepted hz ha)).2.2 c hc) hnb

/-- The leanXMSS part of a break is at most leanXMSS's multi-user bound at the reduction's
budget. -/
theorem prEvent_forgedX_le_bound2
    (hG : ∀ (ℓ : Log) (rows : List BlakeRow) (h : TableOK (look ℓ) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓ h))
    (hxmss : LeanXmss.MultiUser.HasMultiUserSecurity) (fuel budget : ℕ) (A : GameAdversary nx ns)
    {Q cx : ℕ} (hQ : IsQueryBoundP (gameComp Guest.guest fuel budget A) IsHash Q)
    (hvx : ∀ pk msg σ, IsTotalQueryBound
      (LeanXmss.Concrete.verify pk msg σ : OracleComp LeanXmss.HashSpec Bool) cx)
    (hq : Q + cx < 2 ^ 126) :
    Pr{let z ← game Guest.guest fuel budget A}[z.1.accepted = true ∧ XmssRed.ForgedX z.1 ∧
      ¬ AggBad2 z.2] ≤ xmssMultiError nx (Q + cx) := by
  rcases Nat.eq_zero_or_pos nx with rfl | hnx
  · refine le_trans (le_of_eq ?_) zero_le
    exact prEvent_eq_zero_of_forall_not _ _ fun z h ↦ by obtain ⟨-, ⟨j, -⟩, -⟩ := h; exact j.elim0
  · have : NeZero nx := ⟨hnx.ne'⟩
    exact (XmssRed.prEvent_forgedX_le2 hG fuel budget A).trans
      (hxmss nx (Q + cx) hq _ (XmssRed.hasHashQueryBound_xAdv hQ hvx))

/-- The leanSPHINCS part of a break is at most leanSPHINCS's multi-user bound at the reduction's
budget. -/
theorem prEvent_forgedS_le_bound2
    (hG : ∀ (ℓ : Log) (rows : List BlakeRow) (h : TableOK (look ℓ) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓ h))
    {εs : ℕ → ℝ≥0∞} (hsph : Sphincs.Security.Multi.HasMultiUserBound ns εs)
    {cxk csk cxs css cs : ℕ}
    (hxk : ∀ seed, IsTotalQueryBound (LeanXmss.Seeded.keygenFromSeed seed) cxk)
    (hsk : ∀ seed, IsTotalQueryBound (Sphincs.Seeded.keygenFromSeed seed) csk)
    (hxs : ∀ sk i msg, IsTotalQueryBound
      (LeanXmss.Seeded.sign sk i msg : OracleComp LeanXmss.HashSpec _) cxs)
    (hss : ∀ sk msg, IsTotalQueryBound
      (Sphincs.Seeded.sign sk msg : OracleComp Sphincs.HashSpec _) css)
    (hvs : ∀ pk msg σ, IsTotalQueryBound
      (Sphincs.Concrete.verify pk msg σ : OracleComp Sphincs.HashSpec Bool) cs)
    (fuel budget : ℕ) (A : GameAdversary nx ns) {qH sX sS : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS) :
    Pr{let z ← game Guest.guest fuel budget A}[z.1.accepted = true ∧ SphincsRed.ForgedS z.1 ∧
      ¬ AggBad2 z.2] ≤
      εs (max 1 (nx * cxk + ns * csk + (qH + sX * cxs + sS * css) + budget + cs)) := by
  rcases Nat.eq_zero_or_pos ns with rfl | hns
  · refine le_trans (le_of_eq ?_) zero_le
    exact prEvent_eq_zero_of_forall_not _ _ fun z h ↦ by obtain ⟨-, ⟨j, -⟩, -⟩ := h; exact j.elim0
  · have : NeZero ns := ⟨hns.ne'⟩
    refine (SphincsRed.prEvent_forgedS_le2 hG fuel budget A).trans (hsph _ (le_max_left _ _) _ ?_)
    intro r hr
    exact (SphincsRed.hasHashQueryBound_sAdv hxk hsk hxs hss hvs Guest.guest fuel budget A hH hX
      hS r hr).trans (le_max_right _ _)

/-- **No forgery (T5), with the guest's open callees as a hypothesis.** For the game of the
deployed guest with an adversary making at most `qH` hash queries, `sX` leanXMSS and `sS`
leanSPHINCS signing requests, honest key generations and signatures of at most `cxk`, `csk`,
`cxs`, `css` hash queries, final verifications of at most `cx` and `cs`, and `Q` the game's total
hash queries (`isQueryBoundP_gameComp`): if leanXMSS has its multi-user security, leanSPHINCS
the multi-user bound `εs`, and `Q + cx < 2^126`, then V_I accepting a root statement with a
forged claim or an unbacked DA claim has probability at most `noForgeryError2 Q nx cx cs εs`. -/
theorem prEvent_breaks_le2
    (hG : ∀ (ℓ : Log) (rows : List BlakeRow) (h : TableOK (look ℓ) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓ h))
    (hxmss : LeanXmss.MultiUser.HasMultiUserSecurity)
    {εs : ℕ → ℝ≥0∞} (hsph : Sphincs.Security.Multi.HasMultiUserBound ns εs)
    {cxk csk cxs css cx cs : ℕ}
    (hxk : ∀ seed, IsTotalQueryBound (LeanXmss.Seeded.keygenFromSeed seed) cxk)
    (hsk : ∀ seed, IsTotalQueryBound (Sphincs.Seeded.keygenFromSeed seed) csk)
    (hxs : ∀ sk i msg, IsTotalQueryBound
      (LeanXmss.Seeded.sign sk i msg : OracleComp LeanXmss.HashSpec _) cxs)
    (hss : ∀ sk msg, IsTotalQueryBound
      (Sphincs.Seeded.sign sk msg : OracleComp Sphincs.HashSpec _) css)
    (hvx : ∀ pk msg σ, IsTotalQueryBound
      (LeanXmss.Concrete.verify pk msg σ : OracleComp LeanXmss.HashSpec Bool) cx)
    (hvs : ∀ pk msg σ, IsTotalQueryBound
      (Sphincs.Concrete.verify pk msg σ : OracleComp Sphincs.HashSpec Bool) cs)
    (fuel budget : ℕ) (A : GameAdversary nx ns) {qH sX sS : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hq : nx * cxk + ns * csk + (qH + sX * cxs + sS * css) + budget + cx < 2 ^ 126) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤
      noForgeryError2 (nx * cxk + ns * csk + (qH + sX * cxs + sS * css) + budget) nx cx cs εs := by
  set Q := nx * cxk + ns * csk + (qH + sX * cxs + sS * css) + budget
  have hQ : IsQueryBoundP (gameComp Guest.guest fuel budget A) IsHash Q :=
    isQueryBoundP_gameComp hxk hsk hxs hss Guest.guest fuel budget A hH hX hS
  set g := game Guest.guest fuel budget A
  have e : Pr{let z ← g}[Breaks z.1 z.2] ≤ Pr{let z ← g}[(AggBad2 z.2 ∨
      (z.1.accepted = true ∧ XmssRed.ForgedX z.1 ∧ ¬ AggBad2 z.2)) ∨
      (z.1.accepted = true ∧ SphincsRed.ForgedS z.1 ∧ ¬ AggBad2 z.2)] :=
    prEvent_mono_of_support _ _ _ fun z hz hb ↦ by
      by_cases hbad : AggBad2 z.2
      · exact Or.inl (Or.inl hbad)
      · rcases (forged_iff z.1).mp (forged_of_breaks2 hG hz hb hbad) with hf | hf
        · exact Or.inl (Or.inr ⟨hb.1, hf, hbad⟩)
        · exact Or.inr ⟨hb.1, hf, hbad⟩
  refine e.trans ((prEvent_or_le _ _ _).trans (add_le_add ((prEvent_or_le _ _ _).trans
    (add_le_add ?_ ?_)) ?_))
  · exact prEvent_game_aggBad2_le fuel budget A Q hQ
  · exact prEvent_forgedX_le_bound2 hG hxmss fuel budget A hQ hvx hq
  · exact (prEvent_forgedS_le_bound2 hG hsph hxk hsk hxs hss hvs fuel budget A hH hX hS).trans
      (le_of_eq (by rw [show nx * cxk + ns * csk + (qH + sX * cxs + sS * css) + budget + cs =
        Q + cs from rfl]))

/-- **No forgery (T5), the end theorem.** For the game of the deployed guest with an adversary
making at most `qH` hash queries, `sX` leanXMSS and `sS` leanSPHINCS signing requests, honest key
generations and signatures of at most `cxk`, `csk`, `cxs`, `css` hash queries and final
verifications of at most `cx` and `cs`: if leanXMSS has its multi-user security, leanSPHINCS the
multi-user bound `εs`, and the game's hash queries `Q = nx·cxk + ns·csk + (qH + sX·cxs + sS·css) +
budget` satisfy `Q + cx < 2^126`, then V_I accepting a root statement with a forged claim of an
honest key or a DA claim the oracle's final log does not back has probability at most
`noForgeryError2 Q nx cx cs εs`. -/
theorem aggregate_no_forgery2
    (hxmss : LeanXmss.MultiUser.HasMultiUserSecurity)
    {εs : ℕ → ℝ≥0∞} (hsph : Sphincs.Security.Multi.HasMultiUserBound ns εs)
    {cxk csk cxs css cx cs : ℕ}
    (hxk : ∀ seed, IsTotalQueryBound (LeanXmss.Seeded.keygenFromSeed seed) cxk)
    (hsk : ∀ seed, IsTotalQueryBound (Sphincs.Seeded.keygenFromSeed seed) csk)
    (hxs : ∀ sk i msg, IsTotalQueryBound
      (LeanXmss.Seeded.sign sk i msg : OracleComp LeanXmss.HashSpec _) cxs)
    (hss : ∀ sk msg, IsTotalQueryBound
      (Sphincs.Seeded.sign sk msg : OracleComp Sphincs.HashSpec _) css)
    (hvx : ∀ pk msg σ, IsTotalQueryBound
      (LeanXmss.Concrete.verify pk msg σ : OracleComp LeanXmss.HashSpec Bool) cx)
    (hvs : ∀ pk msg σ, IsTotalQueryBound
      (Sphincs.Concrete.verify pk msg σ : OracleComp Sphincs.HashSpec Bool) cs)
    (fuel budget : ℕ) (A : GameAdversary nx ns) {qH sX sS : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hq : nx * cxk + ns * csk + (qH + sX * cxs + sS * css) + budget + cx < 2 ^ 126) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤
      noForgeryError2 (nx * cxk + ns * csk + (qH + sX * cxs + sS * css) + budget) nx cx cs εs :=
  prEvent_breaks_le2 (fun _ _ _ ↦ guestHypsM_model _) hxmss hsph hxk hsk hxs hss hvx hvs fuel
    budget A hH hX hS hq

end NoForgery

/-! ## The closed form -/

/-- **The no-forgery error in closed form, T3 from two challenges**: `closedError` with
`Q³ / (6 · 2^384)` for `Q (Q + 1) / 2^193`. -/
noncomputable def closedError2 (Q nx ns : ℕ) : ℝ≥0∞ :=
  (Q : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ 128 + ((5 * Q : ℕ) : ℝ≥0∞) / 2 ^ 256) +
      Q * (2 / 2 ^ 192 + 4 * (Q + 1) / 2 ^ 256) + Q * (14 / 2 ^ 192 + 4 * Q / 2 ^ 256) +
      predError2 Q +
    (((Q + 384 : ℕ) : ℝ≥0∞) / ((2 ^ 127 : ℕ) : ℝ≥0∞) + (nx ^ 2 : ℕ) / ((2 ^ 127 : ℕ) : ℝ≥0∞) +
      ((Q + 384) ^ 2 : ℕ) / ((2 ^ 252 : ℕ) : ℝ≥0∞)) +
    ns * (((Q + 686 : ℕ) : ℝ≥0∞) / ((2 ^ 127 : ℕ) : ℝ≥0∞))

/-- **Against the old closed form**: only T3's term differs. -/
theorem closedError2_add (Q nx ns : ℕ) :
    closedError2 Q nx ns + Q * (Q + 1) / 2 ^ 193 = closedError Q nx ns + predError2 Q := by
  unfold closedError2 closedError
  ring

/-- `closedError2 Q nx ns`, times `2^256`, T3's term rounded up. -/
def closedNum2 (Q nx ns : ℕ) : ℕ :=
  2 ^ 128 * Q + 5 * Q * Q + 2 ^ 65 * Q + 4 * Q * (Q + 1) + 14 * 2 ^ 64 * Q + 4 * Q * Q +
    (Q ^ 3 / (6 * 2 ^ 128) + 1) + 2 ^ 129 * (Q + 384) + 2 ^ 129 * nx ^ 2 + 16 * (Q + 384) ^ 2 +
    2 ^ 129 * (ns * (Q + 686))

/-- **The no-forgery error at the proved verification costs and a leanSPHINCS bound of
`n_s · q / 2^127` is the closed form**, T3 from two challenges. -/
theorem noForgeryError2_eq_closed2 (Q nx ns : ℕ) :
    noForgeryError2 Q nx xmssVerifyBound sphincsVerifyBound
      (fun q ↦ ns * ((q : ℝ≥0∞) / ((2 ^ 127 : ℕ) : ℝ≥0∞))) = closedError2 Q nx ns := by
  have hs : (4 + leanVmSeeds.steps.length) * Q = 5 * Q := rfl
  have hm : max 1 (Q + sphincsVerifyBound) = Q + 686 :=
    max_eq_right (by unfold sphincsVerifyBound; omega)
  simp only [noForgeryError2, aggBadError2, xmssMultiError, failBound, hs, hm]
  rfl

/-- The no-forgery error is at most the closed form for every leanSPHINCS bound of at most
`n_s · q / 2^127`. -/
theorem noForgeryError2_le_closed2 {Q nx ns : ℕ} {εs : ℕ → ℝ≥0∞}
    (hε : ∀ q, εs q ≤ ns * ((q : ℝ≥0∞) / ((2 ^ 127 : ℕ) : ℝ≥0∞))) :
    noForgeryError2 Q nx xmssVerifyBound sphincsVerifyBound εs ≤ closedError2 Q nx ns := by
  rw [← noForgeryError2_eq_closed2]
  exact add_le_add_right (hε _) _

/-- **The closed form is at most one fraction.** -/
theorem closedError2_le_num (Q nx ns : ℕ) :
    closedError2 Q nx ns ≤ (closedNum2 Q nx ns : ℝ≥0∞) / 2 ^ 256 := by
  set I := ((2 : ℝ≥0∞) ^ 256)⁻¹
  have h128 : ((2 : ℝ≥0∞) ^ 128)⁻¹ = 2 ^ 128 * I := inv_two_pow_eq 128 (by norm_num)
  have h192 : ((2 : ℝ≥0∞) ^ 192)⁻¹ = 2 ^ 64 * I := inv_two_pow_eq 192 (by norm_num)
  have h127 : ((2 : ℝ≥0∞) ^ 127)⁻¹ = 2 ^ 129 * I := inv_two_pow_eq 127 (by norm_num)
  have h252 : ((2 : ℝ≥0∞) ^ 252)⁻¹ = 2 ^ 4 * I := inv_two_pow_eq 252 (by norm_num)
  have hT := predError2_le_num Q
  set T := predError2 Q
  set R := Q ^ 3 / (6 * 2 ^ 128) + 1
  have hc : closedNum2 Q nx ns - R =
      2 ^ 128 * Q + 5 * Q * Q + 2 ^ 65 * Q + 4 * Q * (Q + 1) + 14 * 2 ^ 64 * Q + 4 * Q * Q +
        2 ^ 129 * (Q + 384) + 2 ^ 129 * nx ^ 2 + 16 * (Q + 384) ^ 2 +
        2 ^ 129 * (ns * (Q + 686)) := by
    unfold closedNum2; omega
  have e : closedError2 Q nx ns = T + ((closedNum2 Q nx ns - R : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    rw [hc]
    simp only [closedError2, div_eq_mul_inv, ← ENNReal.inv_pow, Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one, h128, h192, h127, h252]
    ring
  have hsplit : (closedNum2 Q nx ns : ℝ≥0∞) / 2 ^ 256 =
      (R : ℝ≥0∞) / 2 ^ 256 + ((closedNum2 Q nx ns - R : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    rw [ENNReal.div_add_div_same, ← Nat.cast_add, Nat.add_sub_cancel' (by unfold closedNum2; omega)]
  rw [e, hsplit]
  exact add_le_add hT le_rfl

/-- `closedNum2` grows with the queries and the keys. -/
theorem closedNum2_mono {Q Q' nx nx' ns ns' : ℕ} (hQ : Q ≤ Q') (hx : nx ≤ nx') (hs : ns ≤ ns') :
    closedNum2 Q nx ns ≤ closedNum2 Q' nx' ns' := by
  have h3 : Q ^ 3 / (6 * 2 ^ 128) ≤ Q' ^ 3 / (6 * 2 ^ 128) :=
    Nat.div_le_div_right (Nat.pow_le_pow_left hQ 3)
  unfold closedNum2
  gcongr

/-- A numerator of at most `2^(256 - k)` is an error of at most `2^-k`. -/
theorem closedError2_le_of_num {Q nx ns k : ℕ} (hk : k ≤ 256)
    (h : closedNum2 Q nx ns ≤ 2 ^ (256 - k)) : closedError2 Q nx ns ≤ (2 : ℝ≥0∞)⁻¹ ^ k := by
  refine (closedError2_le_num Q nx ns).trans ?_
  rw [← ENNReal.inv_pow, inv_two_pow_eq k hk, div_eq_mul_inv]
  gcongr
  exact_mod_cast h

/-- **No forgery (T5) in closed form.** For the game of the deployed guest with an adversary
making at most `qH` hash queries, `sX` leanXMSS and `sS` leanSPHINCS signing requests: if
leanXMSS has its multi-user security, leanSPHINCS a multi-user bound `εs ≤ n_s · q / 2^127`, and
the game's queries `Q = gameQueries nx ns qH sX sS budget` satisfy `Q + 384 < 2^126`, then V_I
accepting a root statement with a forged claim of an honest key or an unbacked DA claim has
probability at most `closedError2 Q nx ns`. The signers' and verifications' costs are proved. -/
theorem aggregate_no_forgery_closed2 [Sphincs.Params] {nx ns : ℕ}
    (hxmss : LeanXmss.MultiUser.HasMultiUserSecurity)
    {εs : ℕ → ℝ≥0∞} (hsph : Sphincs.Security.Multi.HasMultiUserBound ns εs)
    (hε : ∀ q, εs q ≤ ns * ((q : ℝ≥0∞) / ((2 ^ 127 : ℕ) : ℝ≥0∞)))
    (fuel budget : ℕ) (A : GameAdversary nx ns) {qH sX sS : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hq : gameQueries nx ns qH sX sS budget + 384 < 2 ^ 126) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤
      closedError2 (gameQueries nx ns qH sX sS budget) nx ns :=
  (aggregate_no_forgery2 hxmss hsph keygenFromSeed_isTotalQueryBound
    sphincsKeygenFromSeed_isTotalQueryBound sign_isTotalQueryBound sphincsSign_isTotalQueryBound
    verify_isTotalQueryBound sphincsVerify_isTotalQueryBound fuel budget A hH hX hS hq).trans
    (noForgeryError2_le_closed2 hε)

end
end LeanVM.E2E
