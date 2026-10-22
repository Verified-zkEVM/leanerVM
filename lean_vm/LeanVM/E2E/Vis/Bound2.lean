/-
  LeanVM.E2E.Vis.Bound2

  W-vis, the chain's bad events with T3 from two challenges: on the game with V_I's trace, T1's,
  W6's, E5's bad events, the format event and the restricted two-challenge prediction have
  probability at most `visError2`, whose T3 term is `Q_v³ / (6 · 2^384)`.
-/

module

public import LeanVM.E2E.Vis.Bound
public import LeanVM.E2E.Vis.Pred2

/-!
# The bound on the bad events with T3 from two challenges (W-vis)

`Vis/Bound.lean` bounds `AggBadV` (T4's events at the trace `AggBadT`, T3's restricted
prediction `PredS` and the format event `FormatT`) by `visError`, whose T3 term is the
birthday bound `Q_v (Q_v + 1) / 2^193`. Here `PredS` is replaced by the restricted two-challenge
prediction `PredS2` at the offsets of the guest's last two matrix coordinates (`AggBadV2`):

* **T3's leg** (`prEvent_runGame_t3_2_le`): the potential `pot2` at `V = ¬ Hid keys` with the
  visible budget, a non-hidden fresh query spending one unit (`pot2_step`), a hidden one nothing
  (`pot2_step_of_not`); at the hidden key-generation log it is `B (0, Q_v) / 2^384`
  (`pot2_of_none`), at most `Q_v³ / (6 · 2^384)` (`predError2`).
* **The bound** (`prEvent_gameRec_aggBadV2_le`): `visError2`, `visError` with `predError2 Q_v` for
  the birthday term; the other legs are `Vis/Bound.lean`'s.
* **T3's conclusion** (`rankOK2_of_not_aggBadV2`): without `AggBadV2`, `RankOK2`, all T4 at the
  trace needs (`gameRec_knows`).

`AggBadV2` is contained in `AggBadV` (`aggBadV_of_aggBadV2`): a two-challenge prediction is a
prediction.
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.EndToEnd.Blind LeanVM.Protocol.EndToEnd.Sound LeanVM.Protocol.Rom LeanVM.Node
open LeanVM.Guest.Batch
open OracleSpec OracleComp MeasureTheory
open scoped ENNReal

@[expose] public section

/- The enumeration of `Digest` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest

/-! ## T3's leg -/

section Leg

variable {nx ns : ℕ} [Sphincs.Params]

variable (keys : Keys nx ns) {ℓ₀ : Log} (hall : ∀ e ∈ ℓ₀, Hid keys e.1) {α : Type}
  (oa : OracleComp GameSpec α) {a b : ℕ} (ha : IsQueryBoundP oa (VisQ keys) a)
  (hb : IsQueryBoundP oa IsHash b) {N : ℕ} (hN : ℓ₀.length + b ≤ N)
include hall ha hb hN

/-- **T3's leg from two challenges**: a restricted two-challenge prediction at the offsets
`o₁`, `o₂`, charged per visible query only, has probability at most `Q_v³ / (6 · 2^384)`. -/
theorem prEvent_runGame_t3_2_le (o₁ o₂ : ℕ) :
    Pr{let z ← (simulateQ gameImpl oa).run ℓ₀}[PredS2 keys o₁ o₂ z.2] ≤ predError2 a := by
  refine (prEvent_runGame_le_budgeted keys (fun _ ↦ True) (fun _ _ _ _ ↦ trivial) N
    (Φ := fun m _ ℓ ↦ pot2 (fun x ↦ ¬ Hid keys x) o₁ o₂ m ℓ) ?_ ?_ ?_ oa a b ha hb ℓ₀ trivial hN
    _ ?_).trans ?_
  · intro m n ℓ x _ _ hx _
    exact pot2_step hx m
  · intro m n ℓ x _ _ hx _
    exact pot2_step_of_not (V := fun x ↦ ¬ Hid keys x) (not_not.mpr hx) m
  · intro m n ℓ
    exact ⟨pot2_mono ℓ m, le_rfl⟩
  · intro z _ h _
    rw [pot2, ind_of (show Pred2V (fun x ↦ ¬ Hid keys x) o₁ o₂ z.2 from h)]
    exact le_add_right le_self_add
  · rw [pot2_of_none (fun e he ↦ not_not.mpr (hall e he))]
    exact budget2_zero_le a

end Leg

/-! ## The bound -/

section Bound

variable {nx ns : ℕ} [Sphincs.Params]

/-- **The chain's bad events with the visible accounting, T3 from two challenges**: T4's at the
trace, a restricted two-challenge prediction at the guest's last two matrix coordinates, the
format event. -/
def AggBadV2 (keys : Keys nx ns) (ℓ : Log) : Prop :=
  AggBadT ℓ ∨ PredS2 keys (predOffset (bytecodeWords Guest.guest) - 24)
    (predOffset (bytecodeWords Guest.guest)) ℓ ∨ FormatT keys ℓ

/-- `AggBadV2` is contained in `AggBadV`. -/
theorem aggBadV_of_aggBadV2 {keys : Keys nx ns} {ℓ : Log} (h : AggBadV2 keys ℓ) :
    AggBadV keys ℓ :=
  h.imp_right (Or.imp_left predS_of_predS2)

/-- **The chain's error, T3 from two challenges**: `visError` with `Q_v³ / (6 · 2^384)` for the
birthday term `Q_v (Q_v + 1) / 2^193`. -/
noncomputable def visError2 (Qv Q n : ℕ) : ℝ≥0∞ :=
  Qv * (εLean + 2 / 2 ^ 192) + Q * (14 / 2 ^ 192) + predError2 Qv +
    Q * (failBound leanVmSeeds (Q + 1) + 4 * (Q + 2) / 2 ^ 256 + 4 * (Q + 1) / 2 ^ 256 +
      (n * 2 ^ 64 + 1) / 2 ^ 256)

/-- **The chain's error as the proof gives it, T3 from two challenges**: `visError2` with the
failure rates at `Q`. -/
noncomputable def visErrorTight2 (Qv Q n : ℕ) : ℝ≥0∞ :=
  Qv * (εLean + 2 / 2 ^ 192) + Q * (14 / 2 ^ 192) + predError2 Qv +
    Q * (failBound leanVmSeeds Q + 4 * (Q + 1) / 2 ^ 256 + 4 * Q / 2 ^ 256 +
      (n * 2 ^ 64 + 1) / 2 ^ 256)

omit [Sphincs.Params] in
/-- The tight error is at most the plan's. -/
theorem visErrorTight2_le_visError2 (Qv Q n : ℕ) : visErrorTight2 Qv Q n ≤ visError2 Qv Q n := by
  have h1 : failBound leanVmSeeds Q ≤ failBound leanVmSeeds (Q + 1) :=
    failBound_le_of_le _ (Nat.le_succ Q)
  have h2 : (4 * (Q + 1) / 2 ^ 256 : ℝ≥0∞) ≤ 4 * (Q + 2) / 2 ^ 256 := by
    gcongr
    norm_num
  have h3 : (4 * Q / 2 ^ 256 : ℝ≥0∞) ≤ 4 * (Q + 1) / 2 ^ 256 := by
    gcongr
    exact le_self_add
  unfold visErrorTight2 visError2
  exact add_le_add le_rfl (mul_le_mul' le_rfl (add_le_add (add_le_add (add_le_add h1 h2) h3)
    le_rfl))

omit [Sphincs.Params] in
/-- **The new error against the old one**: `visError2` differs from `visError` only in T3's
term, `Q_v³ / (6 · 2^384)` for `Q_v (Q_v + 1) / 2^193`. -/
theorem visError2_add (Qv Q n : ℕ) :
    visError2 Qv Q n + Qv * (Qv + 1) / 2 ^ 193 = visError Qv Q n + predError2 Qv := by
  unfold visError2 visError
  ring

open Classical in
/-- **The bad events with the visible accounting, tight constants.** In the game with V_I's
trace, with at most `Q_v = qH + budget` visible and
`Q = n_x · c_xk + n_s · c_sk + (qH + s_X · c_xs + s_S · c_ss) + budget` hash queries, the chain's
bad events, T3's from two challenges, have probability at most
`visErrorTight2 Q_v Q (n_x + n_s)`. -/
theorem prEvent_gameRec_aggBadV2_le_tight {cxk csk cxs css : ℕ}
    (hxk : ∀ seed, IsTotalQueryBound (LeanXmss.Seeded.keygenFromSeed seed) cxk)
    (hsk : ∀ seed, IsTotalQueryBound (Sphincs.Seeded.keygenFromSeed seed) csk)
    (hxs : ∀ sk i msg, IsTotalQueryBound
      (LeanXmss.Seeded.sign sk i msg : OracleComp LeanXmss.HashSpec _) cxs)
    (hss : ∀ sk msg, IsTotalQueryBound
      (Sphincs.Seeded.sign sk msg : OracleComp Sphincs.HashSpec _) css)
    (fuel budget : ℕ) (A : GameAdversary nx ns) {qH sX sS : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS) :
    Pr{let p ← gameRec Guest.guest fuel budget A}[AggBadV2 p.1.1.keys p.2] ≤
      visErrorTight2 (qH + budget) (nx * cxk + ns * csk + (qH + sX * cxs + sS * css) + budget)
        (nx + ns) := by
  let _ : MeasurableSpace ((Keys nx ns × SignState nx ns) × Log) := ⊤
  set N := nx * cxk + ns * csk + (qH + sX * cxs + sS * css) + budget with hNdef
  set Qv := qH + budget with hQv
  set Qk := nx * cxk + ns * csk with hQk
  set Qr := (qH + sX * cxs + sS * css) + budget with hQr
  have hNk : Qk + Qr = N := by rw [hQk, hQr, hNdef]; omega
  -- The scheme walks (P2b, P2c) in the form of the counts (P2d).
  have hxw : ∀ sk i msg, IsQueryBoundP (LeanXmss.Seeded.sign sk i msg :
      OracleComp LeanXmss.HashSpec _)
      (fun x ↦ ¬ ∃ a, AddrOK a ∧ LeanXmss.bytesLE 16 sk.parameter ++ a <+: x) 0 :=
    fun sk i msg ↦ by
      refine IsQueryBoundP.of_imp ?_ (xmss_sign_queries sk i msg)
      exact fun _ hx h ↦ hx h.1
  have hsw : ∀ sk msg, IsQueryBoundP (Sphincs.Seeded.sign sk msg : OracleComp Sphincs.HashSpec _)
      (fun x ↦ ¬ ∃ a, AddrOK a ∧ Sphincs.bytesLE 16 sk.parameter ++ a <+: x) 0 :=
    fun sk msg ↦ by
      refine IsQueryBoundP.of_imp ?_ (sphincs_sign_queries sk msg)
      exact fun _ hx h ↦ hx h.1
  have hkg := keygenPhase_hid (nx := nx) (ns := ns)
    (fun seed z hz x hx ↦ (xmss_keygen_queries seed z hz x hx).imp_right (·.1))
    (fun seed z hz x hx ↦ (sphincs_keygen_queries seed z hz x hx).imp_right (·.1))
  have hKQ : IsQueryBoundP ((keygen : GameM nx ns (Keys nx ns)).run (SignState.init nx ns))
      IsHash Qk := costs_keygen hxk hsk _
  -- The rates.
  set fbL := failBound leanVmSeeds N with hfbL
  set bq := ((4 * (N + 1) : ℕ) : ℝ≥0∞) / Fintype.card Digest with hbq
  set dq := 14 * (Fintype.card E : ℝ≥0∞)⁻¹ + ((4 * N : ℕ) : ℝ≥0∞) / Fintype.card Digest with hdq
  set r := (((nx + ns) * 2 ^ 64 + 1 : ℕ) : ℝ≥0∞) / 2 ^ 256 with hr
  set T3 := predError2 Qv with hT3
  set C := Qr * r + ((Qv * εLean + Qr * fbL) + ((Qv * batchε + Qr * bq) + (Qr * dq + T3)))
    with hC
  -- The bound at a reachable outcome of key generation.
  have hrest : ∀ k ∈ support (keygenPhase (nx := nx) (ns := ns)),
      Pr{let z ← (simulateQ gameImpl (restRec Guest.guest fuel budget A k.1.1 k.1.2)).run k.2}[
        AggBadV2 z.1.1.keys z.2] ≤
      ind (Fail leanVmSeeds k.2) + ind (Fail batchSeedsAll (startLog Guest.B1.Main.aggSeedD k.2)) +
        daPot deployedPads.1 k.2 + C := by
    intro k hk
    have hall := hkg k hk
    have ha : IsQueryBoundP (restRec Guest.guest fuel budget A k.1.1 k.1.2) (VisQ k.1.1) Qv :=
      isQueryBoundP_restRec_vis hxw hsw k.1.1 k.1.2 hH
    have hb : IsQueryBoundP (restRec Guest.guest fuel budget A k.1.1 k.1.2) IsHash Qr :=
      isQueryBoundP_restRec hxs hss Guest.guest fuel budget A hH hX hS k.1.1 k.1.2
    have hN : k.2.length + Qr ≤ N := by
      have := length_le_of_mem_support_runGame _ Qk hKQ [] hk
      simp only [List.length_nil, Nat.zero_add] at this
      omega
    have hinc : ∀ z ∈ support ((simulateQ gameImpl
          (restRec Guest.guest fuel budget A k.1.1 k.1.2)).run k.2),
        AggBadV2 z.1.1.keys z.2 →
        (FormatT k.1.1 z.2 ∨ FormatI k.1.1 k.2.length z.2) ∨
          (((1 ≤ pot anyCertBlind.D leanVmSeeds anyProgramBlind z.2 ∨ Fail leanVmSeeds z.2) ∧
              ¬ FormatI k.1.1 k.2.length z.2) ∨
            ((BatchBad Guest.B1.Main.aggSeedD (bytecodeWords Guest.guest) z.2 ∧
                ¬ FormatI k.1.1 k.2.length z.2) ∨
              ((DaBad deployedPads.1 z.2 ∧ ¬ FormatI k.1.1 k.2.length z.2) ∨
                PredS2 k.1.1 (predOffset (bytecodeWords Guest.guest) - 24)
                  (predOffset (bytecodeWords Guest.guest)) z.2))) := by
      intro z hz h
      have hz1 : z.1 ∈ support (restRec Guest.guest fuel budget A k.1.1 k.1.2) :=
        support_simulateQ_run'_subset gameImpl
          (restRec Guest.guest fuel budget A k.1.1 k.1.2) k.2
          (by rw [StateT.run'_eq, support_map]; exact ⟨z, hz, rfl⟩)
      rw [restRec_keys hz1] at h
      by_cases hF : FormatI k.1.1 k.2.length z.2
      · exact Or.inl (Or.inr hF)
      rcases h with (h | h | h | h) | h | h
      · exact Or.inr (Or.inl ⟨Or.inl h, hF⟩)
      · exact Or.inr (Or.inl ⟨Or.inr h, hF⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨h, hF⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h, hF⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
      · exact Or.inl (Or.inl h)
    refine (prEvent_mono_of_support _ _ _ hinc).trans ?_
    refine ((prEvent_or_le _ _ _).trans (add_le_add le_rfl ((prEvent_or_le _ _ _).trans
      (add_le_add le_rfl ((prEvent_or_le _ _ _).trans (add_le_add le_rfl
        (prEvent_or_le _ _ _))))))).trans ?_
    refine (add_le_add (prEvent_runGame_fmt_le k.1.1 hall _ ha hb hN)
      (add_le_add (prEvent_runGame_t1_le k.1.1 hall _ ha hb hN)
        (add_le_add (prEvent_runGame_w6_le k.1.1 hall _ ha hb hN)
          (add_le_add (prEvent_runGame_e5_le k.1.1 hall _ ha hb hN)
            (prEvent_runGame_t3_2_le k.1.1 hall _ ha hb hN _ _))))).trans (le_of_eq ?_)
    rw [hC, hT3, hr, hbq, hdq, hfbL]
    ring
  refine (prEvent_gameRec_le_of_phase (fun p ↦ AggBadV2 p.1.1.keys p.2)
    (fun k ↦ ind (Fail leanVmSeeds k.2) +
      ind (Fail batchSeedsAll (startLog Guest.B1.Main.aggSeedD k.2)) +
        daPot deployedPads.1 k.2 + C) hrest).trans ?_
  -- Key generation: the failure potentials.
  have hT1 : ∫⁻ k, ind (Fail leanVmSeeds k.2) ∂𝒟[keygenPhase (nx := nx) (ns := ns)] ≤
      Qk * fbL := by
    refine (lintegral_keygenPhase_le (f := fun ℓ ↦ ind (Fail leanVmSeeds ℓ)) (δ := fbL) N
      (fun ℓ x hlt _ ↦ (avg_ind_fail_le _ ℓ x).trans
      (add_le_add le_rfl (failBound_le_of_le _ (by omega)))) hKQ (by omega)).trans (le_of_eq ?_)
    rw [ind_of_not (not_fail_nil _), zero_add]
  have hW6 : ∫⁻ k, ind (Fail batchSeedsAll (startLog Guest.B1.Main.aggSeedD k.2))
      ∂𝒟[keygenPhase (nx := nx) (ns := ns)] ≤ Qk * bq := by
    refine (lintegral_keygenPhase_le
      (f := fun ℓ ↦ ind (Fail batchSeedsAll (startLog Guest.B1.Main.aggSeedD ℓ))) (δ := bq) N
      (fun ℓ x hlt _ ↦ ?_) hKQ (by omega)).trans (le_of_eq ?_)
    · by_cases hl : x = batchLabel
      · subst hl
        simp only [startLog_append_label]
        exact (avg_le_of_le fun _ ↦ le_rfl).trans le_self_add
      · simp only [startLog_append_of_ne _ ℓ hl]
        refine (avg_ind_fail_le _ _ x).trans (add_le_add le_rfl ?_)
        have hlen := length_startLog_le Guest.B1.Main.aggSeedD ℓ
        have hsteps : (batchSeedsAll.steps).length = 0 := rfl
        rw [failBound, hsteps, hbq, card_digest, Nat.cast_pow, Nat.cast_ofNat]
        have h4 : (4 + 0) * ((startLog Guest.B1.Main.aggSeedD ℓ).length + 1) ≤ 4 * (N + 1) := by
          omega
        exact ENNReal.div_le_div_right (by exact_mod_cast h4) _
    · rw [ind_of_not (not_fail_startLog_nil _), zero_add]
  have hE5 : ∫⁻ k, daPot deployedPads.1 k.2 ∂𝒟[keygenPhase (nx := nx) (ns := ns)] ≤
      Qk * dq := by
    refine (lintegral_keygenPhase_le (f := daPot deployedPads.1) (δ := dq) N
      (fun ℓ x hlt _ ↦ ?_) hKQ (by omega)).trans (le_of_eq ?_)
    · refine daPot_step.trans ?_
      rw [hdq]
      have h4 : ((4 * (ℓ.length + 1) : ℕ) : ℝ≥0∞) ≤ ((4 * N : ℕ) : ℝ≥0∞) := by
        exact_mod_cast Nat.mul_le_mul_left 4 (by omega)
      exact add_le_add le_rfl (add_le_add le_rfl (ENNReal.div_le_div_right h4 _))
    · rw [daPot_nil, zero_add]
  -- The integral of the per-outcome bound.
  have hint : ∫⁻ k, (ind (Fail leanVmSeeds k.2) +
      ind (Fail batchSeedsAll (startLog Guest.B1.Main.aggSeedD k.2)) +
        daPot deployedPads.1 k.2 + C) ∂𝒟[keygenPhase (nx := nx) (ns := ns)] ≤
      Qk * fbL + Qk * bq + Qk * dq + C := by
    rw [lintegral_add_right _ measurable_const, lintegral_add_left Measurable.of_discrete,
      lintegral_add_left Measurable.of_discrete, lintegral_const]
    exact add_le_add (add_le_add (add_le_add hT1 hW6) hE5)
      (mul_le_of_le_one_right' (evalDist_apply_univ_le_one _))
  refine hint.trans ?_
  -- The constants.
  have hE : ∀ i : Fintype E, @Fintype.card E i = 2 ^ 192 := fun i ↦ by convert card_E
  have hbe : batchε = 2 / 2 ^ 192 := by rw [batchε, hE]; norm_cast
  have hdq' : dq = 14 / 2 ^ 192 + 4 * N / 2 ^ 256 := by
    rw [hdq, hE, card_digest, div_eq_mul_inv (14 : ℝ≥0∞)]
    norm_cast
  have hbq' : bq = 4 * (N + 1) / 2 ^ 256 := by
    rw [hbq, card_digest]
    norm_cast
  have hr' : r = ((nx + ns : ℕ) * 2 ^ 64 + 1) / 2 ^ 256 := by
    rw [hr]
    norm_cast
  have hNc : (N : ℝ≥0∞) = Qk + Qr := by rw [← hNk]; norm_cast
  calc Qk * fbL + Qk * bq + Qk * dq + C ≤ Qk * fbL + Qk * bq + Qk * dq + C + Qk * r :=
        le_self_add
    _ = visErrorTight2 Qv N (nx + ns) := by
        rw [visErrorTight2, hC, hT3, hdq', hbq', hr', hbe, ← hfbL, hNc]
        ring

/-- **The bad events with the visible accounting.** In the game with V_I's trace, with at most
`Q_v = qH + budget` visible and `Q = n_x · c_xk + n_s · c_sk + (qH + s_X · c_xs + s_S · c_ss) +
budget` hash queries, the chain's bad events, T3's from two challenges, have probability at most
`visError2 Q_v Q (n_x + n_s)`. -/
theorem prEvent_gameRec_aggBadV2_le {cxk csk cxs css : ℕ}
    (hxk : ∀ seed, IsTotalQueryBound (LeanXmss.Seeded.keygenFromSeed seed) cxk)
    (hsk : ∀ seed, IsTotalQueryBound (Sphincs.Seeded.keygenFromSeed seed) csk)
    (hxs : ∀ sk i msg, IsTotalQueryBound
      (LeanXmss.Seeded.sign sk i msg : OracleComp LeanXmss.HashSpec _) cxs)
    (hss : ∀ sk msg, IsTotalQueryBound
      (Sphincs.Seeded.sign sk msg : OracleComp Sphincs.HashSpec _) css)
    (fuel budget : ℕ) (A : GameAdversary nx ns) {qH sX sS : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS) :
    Pr{let p ← gameRec Guest.guest fuel budget A}[AggBadV2 p.1.1.keys p.2] ≤
      visError2 (qH + budget) (nx * cxk + ns * csk + (qH + sX * cxs + sS * css) + budget)
        (nx + ns) :=
  (prEvent_gameRec_aggBadV2_le_tight hxk hsk hxs hss fuel budget A hH hX hS).trans
    (visErrorTight2_le_visError2 _ _ _)


/-- **No bad event, T3's conclusion at the guest's shape**: on a log without `AggBadV2`, the
guest's rank holds at the guest's shape. -/
theorem rankOK2_of_not_aggBadV2 {keys : Keys nx ns} {ℓ : Log} (h : ¬ AggBadV2 keys ℓ) :
    RankOK2 ℓ :=
  rankOK2_of_vis2 (fun hf ↦ h (Or.inl (Or.inr (Or.inl hf)))) (fun hF ↦ h (Or.inr (Or.inr hF)))
    (fun hP ↦ h (Or.inr (Or.inl hP)))

/-- **No bad event, T4's events at the trace.** -/
theorem not_aggBadT_of_not_aggBadV2 {keys : Keys nx ns} {ℓ : Log} (h : ¬ AggBadV2 keys ℓ) :
    ¬ AggBadT ℓ :=
  fun h' ↦ h (Or.inl h')

end Bound

end
end LeanVM.E2E
