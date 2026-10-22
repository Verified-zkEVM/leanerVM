/-
  LeanerVM.Protocol.ToVCVio.ChargedInvariant

  The expected potential of a lazy random oracle's cache grows by at most the expected sum of
  per-query charges; so does the probability that a cache invariant fails. Candidate for VCVio.
-/

module

public import LeanerVM.Protocol.ToVCVio.ScalarExpectation
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
public import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

/-!
# The charged invariant of a lazy random oracle

`chargedRandomOracle charge` is the lazy random oracle with a running total beside its cache: a
query `t` absent from the cache `c` adds `charge c t`, a cached query adds nothing. Forgetting the
total, it is `randomOracle` (`chargedRandomOracle_run_map`). Expectations are written
`∫⁻ r, r ∂𝒟[f <$> mx]`, the expectation of `f` on the output of `mx`.

The main theorem, `potential_le_expected_charge`, is a supermartingale bound: if at every fresh
query the expected potential `Φ` of the cache after the uniform answer is at most the potential
before plus the charge, the expected final potential is at most the initial one plus the
expected total charge. A charge may thus pay in advance for a bad event that a group of later
queries completes. Its consequences:

* `probEvent_le_of_potential`: an event on the final cache where `Φ ≥ 1` has probability at most
  the initial potential plus the expected total charge;
* `probEvent_not_good_le_expected_charge`: a cache invariant `Good`, true at the start, broken at
  a fresh query from a good cache with probability at most the charge, is broken at the end with
  probability at most the expected total charge;
* `expected_charge_le_mul`, `probEvent_not_good_le_mul`: with charges at most `κ`, a computation
  making at most `n` queries has expected total charge, and breaks `Good`, at most `n * κ`;
* `expected_fresh_le`, `expected_fresh_in_le`: if a fresh answer lies in `S` with probability at
  most `p`, the expected number of fresh answers in `S` is at most `n * p`, so `n * |S| / |Y|`
  for a set `S` of answers in `Y`.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

@[expose] public section

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec.{0, 0} ι}
  [∀ t, SampleableType (spec.Range t)] {α : Type}

/-- The lazy random oracle with a running total of charges: a query `t` absent from the cache
`c` is answered uniformly and adds `charge c t` to the total; a cached query adds nothing. -/
def chargedRandomOracle (charge : spec.QueryCache → spec.Domain → ℝ≥0∞) :
    QueryImpl spec (StateT (spec.QueryCache × ℝ≥0∞) ProbComp) :=
  QueryImpl.withCachingAux (fun _ _ _ total ↦ total)
    (fun t c total ↦ (fun u ↦ (u, total + charge c t)) <$> ($ᵗ spec.Range t))

omit [DecidableEq ι] [∀ t, SampleableType (spec.Range t)] in
/-- Running a query and then a continuation under a stateful implementation. -/
private theorem run_query_bind {σ : Type} (impl : QueryImpl spec (StateT σ ProbComp))
    (t : spec.Domain) (k : spec.Range t → OracleComp spec α) (s : σ) :
    (simulateQ impl (liftM (spec.query t) >>= k)).run s =
      (impl t).run s >>= fun p ↦ (simulateQ impl (k p.1)).run p.2 := by
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]

/-- A cached query returns its answer and keeps the cache and the total. -/
private theorem chargedRandomOracle_run_of_some (charge : spec.QueryCache → spec.Domain → ℝ≥0∞)
    {t : spec.Domain} {c : spec.QueryCache} {u : spec.Range t} (hc : c t = some u)
    (total : ℝ≥0∞) :
    (chargedRandomOracle charge t).run (c, total) = pure (u, c, total) := by
  simp [chargedRandomOracle, QueryImpl.withCachingAux_apply, hc]

/-- A fresh query draws a uniform answer, caches it, and adds its charge to the total. -/
private theorem chargedRandomOracle_run_of_none (charge : spec.QueryCache → spec.Domain → ℝ≥0∞)
    {t : spec.Domain} {c : spec.QueryCache} (hc : c t = none) (total : ℝ≥0∞) :
    (chargedRandomOracle charge t).run (c, total) =
      (fun u ↦ (u, c.cacheQuery t u, total + charge c t)) <$> ($ᵗ spec.Range t) := by
  simp [chargedRandomOracle, QueryImpl.withCachingAux_apply, hc, Functor.map_map]

/-- Forgetting the total, the charged oracle is the random oracle. -/
theorem chargedRandomOracle_run_map (charge : spec.QueryCache → spec.Domain → ℝ≥0∞)
    (oa : OracleComp spec α) (c : spec.QueryCache) (total : ℝ≥0∞) :
    Prod.map id Prod.fst <$> (simulateQ (chargedRandomOracle charge) oa).run (c, total) =
      (simulateQ spec.randomOracle oa).run c :=
  QueryImpl.withCachingAux_run_proj_eq uniformSampleImpl _ _
    (fun t _ _ ↦ by simp [Functor.map_map]) oa c total

/-- The total starts where it is given: a run from total `total` is a run from total `0`
with `total` added. -/
theorem chargedRandomOracle_run_total (charge : spec.QueryCache → spec.Domain → ℝ≥0∞)
    (oa : OracleComp spec α) (c : spec.QueryCache) (total : ℝ≥0∞) :
    (simulateQ (chargedRandomOracle charge) oa).run (c, total) =
      (fun z ↦ (z.1, z.2.1, total + z.2.2)) <$>
        (simulateQ (chargedRandomOracle charge) oa).run (c, 0) := by
  induction oa using OracleComp.inductionOn generalizing c total with
  | pure a => simp
  | query_bind t k ih =>
    rw [run_query_bind, run_query_bind]
    cases hc : c t with
    | some u =>
      rw [chargedRandomOracle_run_of_some charge hc, chargedRandomOracle_run_of_some charge hc,
        pure_bind, pure_bind]
      exact ih u c total
    | none =>
      rw [chargedRandomOracle_run_of_none charge hc, chargedRandomOracle_run_of_none charge hc,
        bind_map_left, bind_map_left, map_bind]
      refine bind_congr fun u ↦ ?_
      rw [ih u _ (total + charge c t), ih u _ (0 + charge c t), Functor.map_map]
      simp [add_assoc]

omit [DecidableEq ι] [∀ t, SampleableType (spec.Range t)] in
/-- A probabilistic computation has total mass one, so a constant comes out of an
expectation. -/
theorem lintegral_id_evalDist_map_const_add {β : Type} (mx : ProbComp β) (a : ℝ≥0∞)
    (f : β → ℝ≥0∞) :
    ∫⁻ r, r ∂𝒟[(fun x ↦ a + f x) <$> mx] = a + ∫⁻ r, r ∂𝒟[f <$> mx] := by
  rw [lintegral_id_evalDist_map_add mx (fun _ ↦ a) f]
  congr 1
  let : MeasurableSpace β := ⊤
  have hmass : 𝒟[mx] Set.univ = 1 := by
    rw [← prEvent_true_eq_evalDist_apply_univ, OracleComp.prEvent_true_eq_one]
  rw [lintegral_id_evalDist_map, lintegral_const, hmass, mul_one]

omit [DecidableEq ι] [∀ t, SampleableType (spec.Range t)] in
/-- An event's probability is the expectation of its indicator. -/
theorem prEvent_eq_lintegral_id_evalDist_map_ite {β : Type} (mx : ProbComp β)
    (p : β → Prop) [DecidablePred p] :
    Pr{let x ← mx}[p x] = ∫⁻ r, r ∂𝒟[(fun x ↦ if p x then 1 else 0) <$> mx] := by
  let : MeasurableSpace β := ⊤
  rw [prEvent_eq_evalDist_of_discrete, lintegral_id_evalDist_map,
    ← lintegral_indicator_one MeasurableSet.of_discrete]
  exact lintegral_congr fun x ↦ by by_cases hx : p x <;> simp [hx]

/-- The expected total of a run from total `total` is `total` plus that of a run from `0`. -/
private theorem lintegral_total_eq_add (charge : spec.QueryCache → spec.Domain → ℝ≥0∞)
    (oa : OracleComp spec α) (c : spec.QueryCache) (total : ℝ≥0∞) :
    ∫⁻ r, r ∂𝒟[(fun z ↦ z.2.2) <$> (simulateQ (chargedRandomOracle charge) oa).run (c, total)] =
      total + ∫⁻ r, r ∂𝒟[(fun z ↦ z.2.2) <$>
        (simulateQ (chargedRandomOracle charge) oa).run (c, 0)] := by
  rw [chargedRandomOracle_run_total charge oa c total, Functor.map_map]
  exact lintegral_id_evalDist_map_const_add _ total _

/-- **Expected potential.** If at every fresh query the expected potential of the cache after
the uniform answer is at most the potential before plus the query's charge, the expected final
potential of a run is at most the initial potential plus the expected total charge. -/
theorem potential_le_expected_charge (Φ : spec.QueryCache → ℝ≥0∞)
    (charge : spec.QueryCache → spec.Domain → ℝ≥0∞)
    (hstep : ∀ c t, c t = none →
      ∫⁻ r, r ∂𝒟[(fun u ↦ Φ (c.cacheQuery t u)) <$> ($ᵗ spec.Range t)] ≤ Φ c + charge c t)
    (oa : OracleComp spec α) (c : spec.QueryCache) :
    ∫⁻ r, r ∂𝒟[(fun z ↦ Φ z.2) <$> (simulateQ spec.randomOracle oa).run c] ≤
      Φ c + ∫⁻ r, r ∂𝒟[(fun z ↦ z.2.2) <$>
        (simulateQ (chargedRandomOracle charge) oa).run (c, 0)] := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, map_pure, evalDist_pure, lintegral_dirac]
    exact le_self_add
  | query_bind t k ih =>
    rw [run_query_bind, run_query_bind]
    cases hc : c t with
    | some u =>
      rw [QueryImpl.withCaching_run_some _ hc, chargedRandomOracle_run_of_some charge hc,
        pure_bind, pure_bind]
      exact ih u c
    | none =>
      rw [QueryImpl.withCaching_run_none _ hc, chargedRandomOracle_run_of_none charge hc,
        uniformSampleImpl_apply, bind_map_left, bind_map_left, lintegral_id_evalDist_map_bind,
        lintegral_id_evalDist_map_bind]
      dsimp only
      simp only [zero_add, lintegral_total_eq_add charge _ _ (charge c t)]
      rw [lintegral_id_evalDist_map_const_add, ← add_assoc]
      calc _ ≤ ∫⁻ r, r ∂𝒟[(fun u ↦ Φ (c.cacheQuery t u) + ∫⁻ r, r ∂𝒟[(fun z ↦ z.2.2) <$>
              (simulateQ (chargedRandomOracle charge) (k u)).run (c.cacheQuery t u, 0)]) <$>
              ($ᵗ spec.Range t)] :=
            lintegral_id_evalDist_map_mono _ fun u ↦ ih u _
        _ = _ := lintegral_id_evalDist_map_add _ _ _
        _ ≤ _ := add_le_add_left (hstep c t hc) _

/-- An event on the final cache whose every occurrence has potential at least `1` has
probability at most the initial potential plus the expected total charge. -/
theorem probEvent_le_of_potential (E : spec.QueryCache → Prop) (Φ : spec.QueryCache → ℝ≥0∞)
    (hE : ∀ c, E c → 1 ≤ Φ c) (charge : spec.QueryCache → spec.Domain → ℝ≥0∞)
    (hstep : ∀ c t, c t = none →
      ∫⁻ r, r ∂𝒟[(fun u ↦ Φ (c.cacheQuery t u)) <$> ($ᵗ spec.Range t)] ≤ Φ c + charge c t)
    (oa : OracleComp spec α) (c : spec.QueryCache) :
    Pr{let z ← (simulateQ spec.randomOracle oa).run c}[E z.2] ≤
      Φ c + ∫⁻ r, r ∂𝒟[(fun z ↦ z.2.2) <$>
        (simulateQ (chargedRandomOracle charge) oa).run (c, 0)] := by
  classical
  rw [prEvent_eq_lintegral_id_evalDist_map_ite]
  refine le_trans (lintegral_id_evalDist_map_mono _ fun z ↦ ?_)
    (potential_le_expected_charge Φ charge hstep oa c)
  split_ifs with h
  · exact hE _ h
  · exact bot_le

/-- **The charged invariant.** Let `Good` hold of the initial cache, and let a fresh query `t`
at a good cache `c` break it with probability at most `charge c t` over the uniform answer.
Then the final cache is bad with probability at most the expected total charge. -/
theorem probEvent_not_good_le_expected_charge (Good : spec.QueryCache → Prop)
    (charge : spec.QueryCache → spec.Domain → ℝ≥0∞)
    (hstep : ∀ c t, c t = none → Good c →
      Pr{let u ← $ᵗ spec.Range t}[¬ Good (c.cacheQuery t u)] ≤ charge c t)
    (oa : OracleComp spec α) {c : spec.QueryCache} (hc : Good c) :
    Pr{let z ← (simulateQ spec.randomOracle oa).run c}[¬ Good z.2] ≤
      ∫⁻ r, r ∂𝒟[(fun z ↦ z.2.2) <$>
        (simulateQ (chargedRandomOracle charge) oa).run (c, 0)] := by
  classical
  have h := potential_le_expected_charge (fun c ↦ if ¬ Good c then 1 else 0) charge
    (fun c t ht ↦ ?_) oa c
  · rw [prEvent_eq_lintegral_id_evalDist_map_ite]
    simpa only [hc, not_true_eq_false, ↓reduceIte, zero_add] using h
  · by_cases hg : Good c
    · simp only [hg, not_true_eq_false, ↓reduceIte, zero_add]
      exact (prEvent_eq_lintegral_id_evalDist_map_ite _ _).symm.trans_le (hstep c t ht hg)
    · simp only [hg, not_false_eq_true, ↓reduceIte]
      exact (lintegral_id_evalDist_map_le_of_le _ fun u ↦ by split_ifs <;> simp).trans le_self_add

/-- Each query adds at most `κ` to the total, so a run of at most `n` queries adds at most
`n * κ`. -/
theorem charge_le_of_mem_support {charge : spec.QueryCache → spec.Domain → ℝ≥0∞} {κ : ℝ≥0∞}
    (hκ : ∀ c t, c t = none → charge c t ≤ κ) {oa : OracleComp spec α} {n : ℕ}
    (hn : IsTotalQueryBound oa n) (c : spec.QueryCache) (total : ℝ≥0∞)
    {z : α × spec.QueryCache × ℝ≥0∞}
    (hz : z ∈ support ((simulateQ (chargedRandomOracle charge) oa).run (c, total))) :
    z.2.2 ≤ total + n * κ := by
  induction oa using OracleComp.inductionOn generalizing n c total with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact le_self_add (a := total)
  | query_bind t k ih =>
    obtain ⟨hpos, hk⟩ := isTotalQueryBound_query_bind_iff.mp hn
    have hsplit : (n : ℝ≥0∞) * κ = κ + ((n - 1 : ℕ) : ℝ≥0∞) * κ := by
      conv_lhs => rw [← Nat.succ_pred_eq_of_pos hpos]
      rw [Nat.cast_succ, add_mul, one_mul, add_comm, Nat.pred_eq_sub_one]
    rw [run_query_bind, mem_support_bind_iff] at hz
    obtain ⟨p, hp, hz⟩ := hz
    cases hc : c t with
    | some u =>
      rw [chargedRandomOracle_run_of_some charge hc, support_pure,
        Set.mem_singleton_iff] at hp
      subst hp
      refine (ih u (hk u) c total hz).trans ?_
      rw [hsplit]
      gcongr
      exact le_add_self
    | none =>
      rw [chargedRandomOracle_run_of_none charge hc, support_map] at hp
      obtain ⟨u, -, rfl⟩ := hp
      refine (ih u (hk u) _ _ hz).trans ?_
      rw [hsplit, ← add_assoc]
      gcongr
      exact hκ c t hc

/-- The expected total charge of a run of at most `n` queries, each charged at most `κ`, is at
most `n * κ`. -/
theorem expected_charge_le_mul {charge : spec.QueryCache → spec.Domain → ℝ≥0∞} {κ : ℝ≥0∞}
    (hκ : ∀ c t, c t = none → charge c t ≤ κ) {oa : OracleComp spec α} {n : ℕ}
    (hn : IsTotalQueryBound oa n) (c : spec.QueryCache) :
    ∫⁻ r, r ∂𝒟[(fun z ↦ z.2.2) <$>
      (simulateQ (chargedRandomOracle charge) oa).run (c, 0)] ≤ n * κ :=
  lintegral_id_evalDist_map_le_of_le_of_mem_support _ fun _ hz ↦
    (charge_le_of_mem_support hκ hn c 0 hz).trans (zero_add _).le

/-- **The charged invariant, uniform charge.** If a fresh query at a good cache breaks `Good`
with probability at most `κ`, a computation making at most `n` queries from a good cache ends
with a bad one with probability at most `n * κ`. -/
theorem probEvent_not_good_le_mul (Good : spec.QueryCache → Prop) {κ : ℝ≥0∞}
    (hstep : ∀ c t, c t = none → Good c →
      Pr{let u ← $ᵗ spec.Range t}[¬ Good (c.cacheQuery t u)] ≤ κ)
    {oa : OracleComp spec α} {n : ℕ} (hn : IsTotalQueryBound oa n) {c : spec.QueryCache}
    (hc : Good c) :
    Pr{let z ← (simulateQ spec.randomOracle oa).run c}[¬ Good z.2] ≤ n * κ :=
  (probEvent_not_good_le_expected_charge Good (fun _ _ ↦ κ) hstep oa hc).trans
    (expected_charge_le_mul (fun _ _ _ ↦ le_rfl) hn c)

/-- The number of entries of the cache `c` whose answer satisfies `S`. -/
noncomputable def answersIn (S : (t : spec.Domain) → spec.Range t → Prop)
    (c : spec.QueryCache) : ℝ≥0∞ :=
  ((c.toSet ∩ {p | S p.1 p.2}).encard : ℝ≥0∞)

omit [DecidableEq ι] [∀ t, SampleableType (spec.Range t)] in
@[simp]
theorem answersIn_empty (S : (t : spec.Domain) → spec.Range t → Prop) :
    answersIn S (∅ : spec.QueryCache) = 0 := by
  simp [answersIn]

omit [∀ t, SampleableType (spec.Range t)] in
/-- Caching a fresh answer adds one to the count when the answer satisfies `S`. -/
theorem answersIn_cacheQuery (S : (t : spec.Domain) → spec.Range t → Prop)
    {c : spec.QueryCache} {t : spec.Domain} (hc : c t = none) (u : spec.Range t)
    [Decidable (S t u)] :
    answersIn S (c.cacheQuery t u) = answersIn S c + if S t u then 1 else 0 := by
  have hset : (c.cacheQuery t u).toSet = insert ⟨t, u⟩ c.toSet := by
    ext ⟨t', u'⟩
    by_cases ht : t' = t
    · subst ht
      simp [hc, eq_comm]
    · simp [ht]
  have hnot : (⟨t, u⟩ : (t : spec.Domain) × spec.Range t) ∉ c.toSet ∩ {p | S p.1 p.2} :=
    fun h ↦ by simp [hc] at h
  unfold answersIn
  rw [hset]
  split_ifs with hS
  · rw [Set.insert_inter_of_mem (show _ ∈ {p : (t : spec.Domain) × spec.Range t | S p.1 p.2}
      from hS), Set.encard_insert_of_notMem hnot]
    simp
  · rw [Set.insert_inter_of_notMem (show _ ∉ {p : (t : spec.Domain) × spec.Range t | S p.1 p.2}
      from hS)]
    simp

/-- **Expected count.** If a fresh answer satisfies `S` with probability at most `p`, a
computation making at most `n` queries adds in expectation at most `n * p` cached answers
satisfying `S`. -/
theorem expected_fresh_le (S : (t : spec.Domain) → spec.Range t → Prop) {p : ℝ≥0∞}
    (hS : ∀ t, Pr{let u ← $ᵗ spec.Range t}[S t u] ≤ p) {oa : OracleComp spec α} {n : ℕ}
    (hn : IsTotalQueryBound oa n) (c : spec.QueryCache) :
    ∫⁻ r, r ∂𝒟[(fun z ↦ answersIn S z.2) <$> (simulateQ spec.randomOracle oa).run c] ≤
      answersIn S c + n * p := by
  classical
  refine (potential_le_expected_charge (answersIn S) (fun _ _ ↦ p) (fun c t ht ↦ ?_) oa c).trans
    (add_le_add_right (expected_charge_le_mul (fun _ _ _ ↦ le_rfl) hn c) _)
  simp only [answersIn_cacheQuery S ht]
  rw [lintegral_id_evalDist_map_const_add, ← prEvent_eq_lintegral_id_evalDist_map_ite]
  exact add_le_add_right (hS t) _

/-- **Expected count, for a set of answers.** A computation making at most `n` queries to a
random oracle answering in `Y` caches in expectation at most `n * |S| / |Y|` fresh answers in
`S`. -/
theorem expected_fresh_in_le {Y : Type} [SampleableType Y] [Fintype Y] (S : Finset Y)
    {oa : OracleComp (ι →ₒ Y) α} {n : ℕ} (hn : IsTotalQueryBound oa n) :
    ∫⁻ r, r ∂𝒟[(fun z ↦ answersIn (fun _ (u : Y) ↦ u ∈ S) z.2) <$>
      (simulateQ (ι →ₒ Y).randomOracle oa).run ∅] ≤ n * (S.card / Fintype.card Y) := by
  classical
  have hS (t : ι) :
      Pr{let u ← $ᵗ (ι →ₒ Y).Range t}[u ∈ S] ≤ (S.card / Fintype.card Y : ℝ≥0∞) := by
    rw [SampleableType.prEvent_uniformSample (α := Y)]
    simp
  simpa using expected_fresh_le (spec := ι →ₒ Y) (fun _ (u : Y) ↦ u ∈ S) hS hn ∅

end

end LeanerVM.Protocol
