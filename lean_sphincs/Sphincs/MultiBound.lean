import Sphincs.MultiCollide

/-! **The multi-user bound paid per key.** For each key `j` the reduction `toSingle adversary j`,
padded to `F = q + 307` calls off its key, wins within `2 F` calls; the small route bounds its wins
by `ρ / 2^128 / (1 − 2 F ρ / 2^128)` times its expected hash calls on its key, which the padding
makes the calls of key `j` before the check of the multi-user game plus 309. Summed over the keys
these are `q` times one plus the expected pairs of keys sharing their parameter. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.Det

open Completeness SeedCoupling Internalize Eager Short SeedModel _root_.Sphincs.Security.Graph Assembly Stop
  HiddenCost GraphView Reduce DetValue

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
attribute [local instance] Classical.propDecidable

variable [Params]

/-- Staying within the budget in the internalized experiment is finishing the capped seed-free
game. -/
theorem completes_le_seedFree_int (adversary : Adversary) (b : Nat) :
    Pr{let result ← experimentDet (internalize adversary)}[result.2 ≤ b] ≤
      Pr{let x ← seedFreeExperiment (internalize (Memo.memoAdv adversary)) b}[∃ v, x.1 = some v ∧ True] +
        3 * (b / (2 : ℝ≥0∞) ^ 256) := by
  calc
    _ = Pr{let result ← experimentDet (internalize adversary)}[True ∧ result.2 ≤ b] :=
        prEvent_congr_of_support _ _ _ fun _ _ => ⟨fun h => ⟨trivial, h⟩, And.right⟩
    _ ≤ Pr{let result ← experimentMasterDet (internalize adversary)}[True ∧ result.2 ≤ b] +
          b / (2 : ℝ≥0∞) ^ 256 := budgetedE_le_master adversary b (fun _ => True)
    _ ≤ Pr{let x ← seedFreeExperiment (internalize (Memo.memoAdv adversary)) b}[∃ v, x.1 = some v ∧ True] +
          2 * (b / (2 : ℝ≥0∞) ^ 256) + b / (2 : ℝ≥0∞) ^ 256 :=
        add_le_add (doneMaster_le_seedFree adversary b) le_rfl
    _ ≤ _ := by
        rw [add_assoc]
        refine add_le_add le_rfl (le_of_eq ?_)
        ring

theorem seedFree_gt_le_gen (adversary : Adversary) (E : ProbComp (Bool × ℕ))
    (hcomp : ∀ b, Pr{let r ← E}[r.2 ≤ b] ≤
      Pr{let x ← seedFreeExperiment (internalize (Memo.memoAdv adversary)) b}[∃ v, x.1 = some v ∧ True] +
        3 * (b / (2 : ℝ≥0∞) ^ 256)) (q b : ℕ) (hbq : b ≤ q) :
    Pr{let x ← seedFreeExperiment (internalize (Memo.memoAdv adversary)) q}[b < traceCost x.2] ≤
      Pr{let r ← E}[b < r.2] + 3 * (b / (2 : ℝ≥0∞) ^ 256) := by
  have hstop : Pr{let x ← seedFreeExperiment (internalize (Memo.memoAdv adversary)) q}[b < traceCost x.2] ≤
      Pr{let x ← seedFreeExperiment (internalize (Memo.memoAdv adversary)) b}[¬∃ v, x.1 = some v ∧ True] := by
    unfold seedFreeExperiment
    refine HiddenBridge.probEvent_bind_mono_support _ _ _ _ _ fun material _ => ?_
    refine HiddenBridge.probEvent_bind_mono_support _ _ _ _ _ fun answers _ => ?_
    refine HiddenBridge.probEvent_bind_mono_support _ _ _ _ _ fun table _ => ?_
    unfold seedFreeRun
    refine le_trans (traceCost_cap_gt_le _ _ _ q b hbq) (prEvent_mono_of_support _ _ _ fun x _ hx => ?_)
    rintro ⟨v, hv, -⟩
    rw [hx] at hv
    cases hv
  have hdone := hcomp b
  have h1 := prob_add_not (seedFreeExperiment (internalize (Memo.memoAdv adversary)) b)
    (fun x => ∃ v, x.1 = some v ∧ True)
  have h2 := prob_add_not (E) (fun r => r.2 ≤ b)
  refine hstop.trans ?_
  set S := Pr{let x ← seedFreeExperiment (internalize (Memo.memoAdv adversary)) b}[∃ v, x.1 = some v ∧ True]
  set N := Pr{let x ← seedFreeExperiment (internalize (Memo.memoAdv adversary)) b}[¬∃ v, x.1 = some v ∧ True]
  set W := Pr{let r ← E}[r.2 ≤ b]
  have hW : Pr{let r ← E}[¬r.2 ≤ b] = Pr{let r ← E}[b < r.2] :=
    prEvent_congr_of_support _ _ _ fun r _ => not_le
  rw [hW] at h2
  set G := Pr{let r ← E}[b < r.2]
  have hWfin : W ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (prEvent_le_one _)
  refine (ENNReal.add_le_add_iff_left hWfin).1 ?_
  calc W + N ≤ (S + 3 * (b / (2 : ℝ≥0∞) ^ 256)) + N := add_le_add hdone le_rfl
    _ = (S + N) + 3 * (b / (2 : ℝ≥0∞) ^ 256) := by ring
    _ = (W + G) + 3 * (b / (2 : ℝ≥0∞) ^ 256) := by rw [h1, h2]
    _ = W + (G + 3 * (b / (2 : ℝ≥0∞) ^ 256)) := by ring

/-- **The expected hash calls of the capped seed-free game are at most those of the experiment**,
capped at the same budget, up to the seed terms. -/
theorem mean_seedFree_le_gen (adversary : Adversary) (E : ProbComp (Bool × ℕ))
    (hcomp : ∀ b, Pr{let r ← E}[r.2 ≤ b] ≤
      Pr{let x ← seedFreeExperiment (internalize (Memo.memoAdv adversary)) b}[∃ v, x.1 = some v ∧ True] +
        3 * (b / (2 : ℝ≥0∞) ^ 256)) (q : ℕ) :
    mean (seedFreeExperiment (internalize (Memo.memoAdv adversary)) q) (fun x => (traceCost x.2 : ℝ≥0∞)) ≤
      mean (E) (fun r => ((min r.2 q : ℕ) : ℝ≥0∞)) +
        3 * ((q : ℝ≥0∞) * q / (2 : ℝ≥0∞) ^ 256) := by
  have hcap : mean (seedFreeExperiment (internalize (Memo.memoAdv adversary)) q) (fun x => (traceCost x.2 : ℝ≥0∞)) =
      mean (seedFreeExperiment (internalize (Memo.memoAdv adversary)) q)
        (fun x => ((min (traceCost x.2) q : ℕ) : ℝ≥0∞)) := by
    refine le_antisymm (mean_mono_support _ fun x hx => ?_) (mean_mono _ fun x => by exact_mod_cast min_le_left _ _)
    have hle : traceCost x.2 ≤ q := by
      unfold seedFreeExperiment at hx
      simp only [mem_support_bind_iff] at hx
      obtain ⟨material, -, answers, -, table, -, hx⟩ := hx
      exact costRun_cap_cost_le _ _ _ q x hx
    rw [min_eq_left hle]
  rw [hcap, mean_min_eq_sum, mean_min_eq_sum]
  calc ∑ b ∈ Finset.range q, Pr{let x ← seedFreeExperiment (internalize (Memo.memoAdv adversary)) q}[b < traceCost x.2]
      ≤ ∑ b ∈ Finset.range q, (Pr{let r ← E}[b < r.2] + 3 * ((q : ℝ≥0∞) / 2 ^ 256)) := by
        refine Finset.sum_le_sum fun b hb => ?_
        have hbq : b ≤ q := (Finset.mem_range.1 hb).le
        refine (seedFree_gt_le_gen adversary E hcomp q b hbq).trans (add_le_add le_rfl (mul_le_mul' le_rfl ?_))
        exact ENNReal.div_le_div_right (by exact_mod_cast hbq) _
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        congr 1
        rw [mul_left_comm, mul_div_assoc]

end Sphincs.Security.Det

namespace Sphincs.Security.Multi

open MultiEager Completeness Internalize Short Eager SeedCoupling KeyOnly

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
attribute [local instance] Classical.propDecidable

variable [Params] {n : ℕ}

/-- **Within the budget, the game checking key `j` makes at most `q + 307` short calls.** -/
theorem short_gameAtP_le (adversary : Adversary n) (q : ℕ) (hb : HasHashQueryBound adversary q) (j : Fin n) r
    (hr : Reach (runW wS (gameAtP adversary j)) r) : r.2 ≤ q + 307 := by
  rw [show wS = fun x => ((AddMonoidHom.fst ℕ (PublicParameter → ℕ)).comp (AddMonoidHom.fst _ ℕ)) (wK x) from rfl,
    runW_hom, reach_map_iff] at hr
  obtain ⟨r1, hr1, rfl⟩ := hr
  rw [gameAtP_eq, runW_bind, reach_bind_iff] at hr1
  obtain ⟨res, hres, hr1⟩ := hr1
  rw [reach_map_iff] at hr1
  obtain ⟨c', hc', rfl⟩ := hr1
  rw [StateT.run'_eq, reach_map_iff] at hc'
  obtain ⟨c, hc, rfl⟩ := hc'
  rw [show ((fun won => (won, (res.1.1.1 j).1.parameter)) <$> checkAt j res.1.1 :
      OracleComp OracleWorld _) = (fun v => (decide (Valid res.1.1.2.2 j ∧ ¬Contains res.1.1.2.2
        ⟨j, res.1.1.2.1.message, res.1.1.2.1.signature⟩) && v, (res.1.1.1 j).1.parameter)) <$>
          (liftM (Concrete.verify (res.1.1.1 j).1 res.1.1.2.1.message res.1.1.2.1.signature :
            OracleComp HashSpec Bool) : OracleComp OracleWorld Bool) by
    simp only [checkAt, bind_pure_comp, Functor.map_map], cntW_map, simulateQ_map, StateT.run_map,
    reach_map_iff] at hc
  obtain ⟨c'', hc'', rfl⟩ := hc
  have hv := verify_wK_le _ _ _ _ c'' hc''
  have hpre := prefix_total_le adversary q hb res hres
  have hpre1 := short_le_total _ _ res hres
  simp only [AddMonoidHom.coe_comp, AddMonoidHom.coe_fst, Function.comp_apply, Prod.fst_add]
  omega

omit [Params] in
theorem prEvent_eq_one_of_reach {α : Type} (mx : ProbComp α) (p : α → Prop) (h : ∀ r, Reach mx r → p r) :
    Pr{let r ← mx}[p r] = 1 :=
  OracleComp.prEvent_eq_one_of_forall_mem_support _ _ fun r hr => h r (reach_iff.2 hr)

open ForsPotential Reduce HiddenDebt HiddenCost in
/-- **The padded reduction to key `j` charges the calls of key `j`**: its key's capped calls in
the seed-free game are at most the calls of key `j` before the check of the multi-user game plus 309
and the seed terms. -/
theorem padded_key_le (adversary : Adversary n) (q : ℕ) (hb : HasHashQueryBound adversary q) (j : Fin n) :
    mean ($ᵗ HashOutput) (fun parameterOutput => mean (seedFreeFrom (internalize (Memo.memoAdv
        (padAdv (q + 307) (toSingle adversary j)))) (2 * (q + 307)) parameterOutput)
        fun x => min ((2 * (q + 307) : ℕ) : ℝ≥0∞) (keyCharged parameterOutput x.2)) ≤
      mean ((simulateQ romImpl (cntW wK (prefixMU adversary))).run ∅)
        (fun r => ((r.1.2.1.2 ((r.1.1.1 j).1.parameter) : ℕ) : ℝ≥0∞)) +
        (309 + 3 * (((2 * (q + 307) : ℕ) : ℝ≥0∞) * ((2 * (q + 307) : ℕ) : ℝ≥0∞) / 2 ^ 256) +
          ((q + 307 : ℕ) : ℝ≥0∞) * (3 * (((2 * (q + 307) : ℕ) : ℝ≥0∞) / 2 ^ 256))) := by
  set F := q + 307 with hF
  set M := 2 * (q + 307) with hM
  set Y := toSingle adversary j with hY
  set D := padAdv F Y with hD
  set L := mean ($ᵗ HashOutput) (fun parameterOutput => mean (seedFreeFrom (internalize (Memo.memoAdv D)) M
    parameterOutput) fun x => min (M : ℝ≥0∞) (keyCharged parameterOutput x.2)) with hL
  set P := mean ((simulateQ romImpl (cntW wK (prefixMU adversary))).run ∅)
    (fun r => ((r.1.2.1.2 ((r.1.1.1 j).1.parameter) : ℕ) : ℝ≥0∞)) with hP
  set δ := 3 * ((M : ℝ≥0∞) / 2 ^ 256) with hδ
  have h5 := mean_keyCharged_add_le F M Y
  have h6 := Det.mean_seedFree_le_gen D (Det.experimentDet (internalize D)) (Det.completes_le_seedFree_int D) M
  have h8 : mean (Det.experimentDet (internalize D)) (fun r => ((min r.2 M : ℕ) : ℝ≥0∞)) ≤
      P + ((F + 309 : ℕ) : ℝ≥0∞) := by
    refine (mean_short_padAdv F M Y).trans ?_
    rw [mean_congr (runW_toSingle wJ adversary j)]
    exact mean_keyBound_le adversary q hb j F le_rfl
  have hall : Pr{let r ← Det.experimentDet (internalize D)}[r.2 ≤ M] = 1 := by
    refine prEvent_eq_one_of_reach _ _ fun r hr => ?_
    obtain ⟨r', hr', hle⟩ := support_short_padAdv F Y r hr
    have h1 : Reach (runW wS (gameCoreDetP Y)) (r'.1.1, r'.2) := by
      rw [gameCoreDetP_eq_gameCnt, runW_map, reach_map_iff]
      exact ⟨r', hr', rfl⟩
    rw [reach_congr (runW_toSingle wS adversary j)] at h1
    have h2 := short_gameAtP_le adversary q hb j _ h1
    simp only at h2
    omega
  have h7 := Det.completes_le_seedFree_int D M
  rw [hall] at h7
  have hsome : Pr{let x ← seedFreeExperiment (internalize (Memo.memoAdv D)) M}[∃ v, x.1 = some v ∧ True] =
      Pr{let x ← seedFreeExperiment (internalize (Memo.memoAdv D)) M}[x.1.isSome] :=
    prEvent_congr_of_support _ _ _ fun x _ => by cases x.1 <;> simp
  rw [hsome] at h7
  have hFfin : (F : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top F
  refine (ENNReal.add_le_add_iff_right hFfin).1 ?_
  calc L + F ≤ L + F * (Pr{let x ← seedFreeExperiment (internalize (Memo.memoAdv D)) M}[x.1.isSome] + δ) := by
        refine add_le_add le_rfl ?_
        calc (F : ℝ≥0∞) = F * 1 := (mul_one _).symm
          _ ≤ _ := mul_le_mul' le_rfl h7
    _ = (L + F * Pr{let x ← seedFreeExperiment (internalize (Memo.memoAdv D)) M}[x.1.isSome]) + F * δ := by ring
    _ ≤ mean (seedFreeExperiment (internalize (Memo.memoAdv D)) M) (fun x => (traceCost x.2 : ℝ≥0∞)) + F * δ :=
        add_le_add h5 le_rfl
    _ ≤ (mean (Det.experimentDet (internalize D)) (fun r => ((min r.2 M : ℕ) : ℝ≥0∞)) +
          3 * ((M : ℝ≥0∞) * M / 2 ^ 256)) + F * δ := add_le_add h6 le_rfl
    _ ≤ ((P + ((F + 309 : ℕ) : ℝ≥0∞)) + 3 * ((M : ℝ≥0∞) * M / 2 ^ 256)) + F * δ :=
        add_le_add (add_le_add h8 le_rfl) le_rfl
    _ = _ := by push_cast; ring

/-! ### The multi-user bound -/

open ForsPotential PotentialA

/-- **The multi-user bound of the small route**, at the budget `M = 2 (q + 307)` of the padded
reductions: `ρ / 2^128 / (1 − M ρ / 2^128)` times `q` (one plus the expected pairs of keys sharing
their parameter) and `n (309 + ...)`, plus `n` times the sample-independent terms at `M`. -/
noncomputable def multiSmall (n q : ℕ) (ρ : ℝ) (B c : ℚ) : ℝ≥0∞ :=
  ENNReal.ofReal (ρ / 2 ^ 128) * (1 - ((2 * (q + 307) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (ρ / 2 ^ 128))⁻¹ *
      ((q : ℝ≥0∞) * (1 + (n * n : ℝ≥0∞) * pairChance) +
        (n : ℝ≥0∞) * (309 + 3 * (((2 * (q + 307) : ℕ) : ℝ≥0∞) * ((2 * (q + 307) : ℕ) : ℝ≥0∞) / 2 ^ 256) +
          ((q + 307 : ℕ) : ℝ≥0∞) * (3 * (((2 * (q + 307) : ℕ) : ℝ≥0∞) / 2 ^ 256)))) +
    (n : ℝ≥0∞) * (smallRestF (2 * (q + 307)) B c + 2 * (2 : ℝ≥0∞)⁻¹ ^ 201 +
      smallFailF (2 * (q + 307)) * (2 : ℝ≥0∞)⁻¹ ^ 201 + 3 * (((2 * (q + 307) : ℕ) : ℝ≥0∞) / 2 ^ 256))

set_option maxHeartbeats 1000000 in
/-- **`n` keys, paid per key.** From the small-route check at `qh`, for `2 (q + 307) − keygenCost ≤ qh`,
the multi-user advantage within `q` hash calls is at most `multiSmall`. -/
theorem multi_small_le (hb0 : 0 < subtreeHeight) (b N : ℕ) (hb : subtreeHeight = b) (hN : signatureLimit = N)
    (qh : ℕ) (ρ : ℚ) (t : H0.PoisT) (o : H0.OptF) (on : H0.OptN) (hpt : H0.checkPT t = true)
    (hrt : H0.checkRate b N qh t = true) (ho : H0.checkOptF b t o = true) (hon : H0.checkOptN t on = true)
    (hsmall : checkSmallF b N qh ρ o.cthr o.B ((2 ^ b * on.En : ℚ) / 2) = true)
    (adversary : Adversary n) (q : ℕ) (hq : 2 * (q + 307) - keygenCost ≤ qh)
    (hbound : HasHashQueryBound adversary q) :
    forgeAdvantage adversary ≤
      multiSmall n q (ρ : ℝ) o.B ((2 - ρ + (qh : ℚ) / 2 ^ 128 + (N : ℚ) * 123 / (2 ^ b * 2 ^ 15)) *
        ((2 ^ b * on.En : ℚ) / 2)) := by
  obtain ⟨hnum, hqh, hN70, hcthr, hB, hc, hpayR, hcheck⟩ := checkSmallF_sound hsmall
  set M := 2 * (q + 307) with hM
  set κ : ℚ := 2 - ρ + (qh : ℚ) / 2 ^ 128 + (N : ℚ) * 123 / (2 ^ b * 2 ^ 15) with hκdef
  have hκR : (κ : ℝ) = 2 - (ρ : ℝ) + (qh : ℝ) / 2 ^ 128 + (N : ℝ) * 123 / (2 ^ b * 2 ^ 15) := by
    rw [hκdef]; push_cast; ring
  have hκ0 : 0 ≤ κ := by
    have hR : (0 : ℝ) ≤ (κ : ℝ) := by
      rw [hκR]
      have h1 : (ρ : ℝ) ≤ 2 := hnum.high
      have h2 : (0 : ℝ) ≤ (qh : ℝ) / 2 ^ 128 := by positivity
      have h3 : (0 : ℝ) ≤ (N : ℝ) * 123 / (2 ^ b * 2 ^ 15) := by positivity
      linarith
    exact_mod_cast hR
  have hκ1 : κ ≤ 1 := by
    have hR : (κ : ℝ) ≤ 1 := by rw [hκR]; linarith
    exact_mod_cast hR
  have hx : ((M - keygenCost : ℕ) : ℝ) / 2 ^ 128 ≤ (qh : ℝ) / 2 ^ 128 :=
    div_le_div_of_nonneg_right (Nat.cast_le.mpr hq) (by positivity)
  have hnum' : Numeric (ρ : ℝ) (((M - keygenCost : ℕ) : ℝ) / 2 ^ 128) := numeric_monoF hnum hx (by positivity)
  have hκq : 2 - (ρ : ℝ) + ((M - keygenCost : ℕ) : ℝ) / 2 ^ 128 +
      (signatureLimit : ℝ) * (123 * ((2 : ℝ) ^ subtreeHeight * 2 ^ 15)⁻¹) ≤ (κ : ℝ) := by
    have he : (signatureLimit : ℝ) * (123 * ((2 : ℝ) ^ subtreeHeight * 2 ^ 15)⁻¹) =
        (N : ℝ) * 123 / (2 ^ b * 2 ^ 15) := by
      rw [hb, hN]; field_simp
    rw [hκR, he]
    linarith
  have hkg : keygenCost = 226 * 2 ^ b + 2 * (26 - b) := by rw [← hb]; rfl
  have hMsmall : (M : ℝ) ≤ 2 ^ 123 := by
    have h64 : 64 * ((qh : ℝ) / 2 ^ 128) ≤ 1 := hnum.small
    have hqhR : (qh : ℝ) ≤ 2 ^ 122 := by
      have := h64; field_simp at this; linarith
    have hMle : M ≤ qh + keygenCost := by omega
    have hkgR : (keygenCost : ℝ) ≤ 2 ^ 122 := by
      rw [hkg]
      have hb26 : b ≤ 26 := by
        rw [← hb]
        exact Params.subtreeHeight_le
      have : 226 * 2 ^ b + 2 * (26 - b) ≤ 2 ^ 122 := by
        calc 226 * 2 ^ b + 2 * (26 - b) ≤ 226 * 2 ^ 26 + 52 := by
              have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hb26
              omega
          _ ≤ 2 ^ 122 := by norm_num
      exact_mod_cast this
    calc (M : ℝ) ≤ (qh + keygenCost : ℕ) := Nat.cast_le.mpr hMle
      _ = (qh : ℝ) + keygenCost := by push_cast; ring
      _ ≤ 2 ^ 122 + 2 ^ 122 := add_le_add hqhR hkgR
      _ = 2 ^ 123 := by norm_num
  have hcM : (M : ℝ≥0∞) * ENNReal.ofReal ((ρ : ℝ) / 2 ^ 128) < 1 := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    rw [ENNReal.ofReal_lt_one]
    have h1 : (ρ : ℝ) ≤ 2 := hnum.high
    have h0 : (0 : ℝ) ≤ ρ := by linarith [hnum.low]
    calc (M : ℝ) * ((ρ : ℝ) / 2 ^ 128) ≤ 2 ^ 123 * (2 / 2 ^ 128) :=
          mul_le_mul hMsmall (div_le_div_of_nonneg_right h1 (by positivity)) (by positivity) (by positivity)
      _ < 1 := by norm_num
  have hM256 : M < 2 ^ 256 := by
    have : (M : ℝ) < 2 ^ 256 := lt_of_le_of_lt hMsmall (by norm_num)
    exact_mod_cast this
  set k : ℝ≥0∞ := ENNReal.ofReal ((ρ : ℝ) / 2 ^ 128) * (1 - (M : ℝ≥0∞) * ENNReal.ofReal ((ρ : ℝ) / 2 ^ 128))⁻¹
    with hk
  set cc : ℚ := κ * ((2 ^ b * on.En : ℚ) / 2) with hcc
  set R : ℝ≥0∞ := smallRestF M o.B cc + 2 * (2 : ℝ≥0∞)⁻¹ ^ 201 + smallFailF M * (2 : ℝ≥0∞)⁻¹ ^ 201 +
    3 * ((M : ℝ≥0∞) / 2 ^ 256) with hR
  set Lj : Fin n → ℝ≥0∞ := fun j => mean ($ᵗ HashOutput) (fun parameterOutput => mean
    (seedFreeFrom (internalize (Memo.memoAdv (padAdv (q + 307) (toSingle adversary j)))) M parameterOutput)
    fun x => min (M : ℝ≥0∞) (keyCharged parameterOutput x.2)) with hLj
  set c0 : ℝ≥0∞ := 309 + 3 * ((M : ℝ≥0∞) * (M : ℝ≥0∞) / 2 ^ 256) +
    ((q + 307 : ℕ) : ℝ≥0∞) * (3 * ((M : ℝ≥0∞) / 2 ^ 256)) with hc0
  have hj : ∀ j, Det.winWithin (toSingle adversary j) q ≤ k * Lj j + R := by
    intro j
    set D := padAdv (q + 307) (toSingle adversary j) with hD
    refine (winWithin_le_padAdv (q + 307) q _).trans ?_
    have hmono : Det.budgetedAdvantageDet D (q + (q + 307)) ≤ Det.budgetedAdvantageDet D M :=
      prEvent_mono_of_support _ _ _ fun r _ h => ⟨h.1, by omega⟩
    refine hmono.trans ((Det.budgetedAdvantageDet_le_seedFree D M).trans ?_)
    have hsf := small_seedFree_trace hb0 (Memo.memoAdv D) (Memo.memoAdv_noRepeat D) M hM256 (ρ : ℝ) hnum' κ hκ0 hκ1
      hκq b N hb hN t o on hpt qh hrt hq ho hon hcthr hcM
    refine (add_le_add hsf le_rfl).trans ?_
    rw [hR]
    have hlam := lam_start_leF (M - keygenCost)
    have hfail := expectedFail_le
    calc _ ≤ k * Lj j + (smallRestF M o.B cc + 2 * (2 : ℝ≥0∞)⁻¹ ^ 201) + smallFailF M * (2 : ℝ≥0∞)⁻¹ ^ 201 +
          3 * ((M : ℝ≥0∞) / 2 ^ 256) := by
          gcongr
      _ = _ := by ring
  have hL : ∀ j, Lj j ≤ mean ((simulateQ romImpl (cntW wK (prefixMU adversary))).run ∅)
      (fun r => ((r.1.2.1.2 ((r.1.1.1 j).1.parameter) : ℕ) : ℝ≥0∞)) + c0 :=
    fun j => padded_key_le adversary q hbound j
  calc forgeAdvantage adversary ≤ ∑ j, Det.winWithin (toSingle adversary j) q :=
        forgeAdvantage_le_sum adversary q hbound
    _ ≤ ∑ j, (k * Lj j + R) := Finset.sum_le_sum fun j _ => hj j
    _ = k * ∑ j, Lj j + n * R := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
    _ ≤ k * (q * (1 + (n * n : ℝ≥0∞) * pairChance) + n * c0) + n * R := by
        refine add_le_add (mul_le_mul' le_rfl ?_) le_rfl
        calc ∑ j, Lj j ≤ ∑ j, (mean ((simulateQ romImpl (cntW wK (prefixMU adversary))).run ∅)
              (fun r => ((r.1.2.1.2 ((r.1.1.1 j).1.parameter) : ℕ) : ℝ≥0∞)) + c0) := Finset.sum_le_sum fun j _ => hL j
          _ = ∑ j, mean ((simulateQ romImpl (cntW wK (prefixMU adversary))).run ∅)
              (fun r => ((r.1.2.1.2 ((r.1.1.1 j).1.parameter) : ℕ) : ℝ≥0∞)) + n * c0 := by
              rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          _ ≤ q * (1 + mean ((simulateQ romImpl (cntW wK (prefixMU adversary))).run ∅)
              (fun r => ((pairs fun i => (r.1.1.1 i).1.parameter : ℕ) : ℝ≥0∞))) + n * c0 :=
              add_le_add (sum_prefix_le adversary q hbound) le_rfl
          _ ≤ q * (1 + (n * n : ℝ≥0∞) * pairChance) + n * c0 :=
              add_le_add (mul_le_mul' le_rfl (add_le_add le_rfl (mean_pairs_prefix adversary))) le_rfl
    _ = _ := by rw [multiSmall]

/-- **The multi-user bound**: `multiSmall` (or `n q / 2^127` when smaller) for the budgets of the
small route, `n q / 2^127` beyond. -/
noncomputable def multiBound (n qh : ℕ) (ρ : ℝ) (B c : ℚ) (q : ℕ) : ℝ≥0∞ :=
  if 2 * (q + 307) - keygenCost ≤ qh then min (multiSmall n q ρ B c) (n * (q / ((2 ^ 127 : ℕ) : ℝ≥0∞)))
  else n * (q / ((2 ^ 127 : ℕ) : ℝ≥0∞))

/-- **`n` keys from the certificates of one parameter set.** -/
theorem hasMultiUserBound_multiBound (hb0 : 0 < subtreeHeight) (b N : ℕ) (hb : subtreeHeight = b)
    (hN : signatureLimit = N) (qh : ℕ) (ρ : ℚ) (t : H0.PoisT) (o : H0.OptF) (on : H0.OptN)
    (hpt : H0.checkPT t = true) (hrt : H0.checkRate b N qh t = true) (ho : H0.checkOptF b t o = true)
    (hon : H0.checkOptN t on = true)
    (hsmall : checkSmallF b N qh ρ o.cthr o.B ((2 ^ b * on.En : ℚ) / 2) = true)
    (hbits : Det.HasClassicalSecurityBitsDetBudgeted 127) (n : ℕ) :
    HasMultiUserBound n (multiBound n qh (ρ : ℝ) o.B ((2 - ρ + (qh : ℚ) / 2 ^ 128 + (N : ℚ) * 123 / (2 ^ b * 2 ^ 15)) *
      ((2 ^ b * on.En : ℚ) / 2))) := by
  intro q hq adversary hbound
  have hlarge := hasMultiUserBound_of_budgeted hbits n q hq adversary hbound
  unfold multiBound
  split_ifs with hsm
  · exact le_min (multi_small_le hb0 b N hb hN qh ρ t o on hpt hrt ho hon hsmall adversary q hsm hbound) hlarge
  · exact hlarge

end Sphincs.Security.Multi
