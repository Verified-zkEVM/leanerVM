/-
  LeanerVM.Protocol.ToVCVio.ProofOfWork

  A proof-of-work search against a lazy random oracle runs out of candidates with small
  probability, whatever else the computation asks and in whatever order. Candidate for VCVio.
-/

module

public import LeanerVM.Protocol.ToVCVio.ChargedInvariant

/-!
# Exhausting a proof-of-work search

A proof-of-work search (`PowSearch`) on an oracle `D →ₒ Y` starts from a *base* `b : Y`, the
answer to a base-shaped query (`isBase`) or a fixed `start`, and tries the candidate inputs
`cand b 0, cand b 1, …, cand b (F - 1)` until one is answered by a passing digest (`ok`). The
candidates of distinct bases and indices below `F` are distinct, and no candidate is base-shaped.

`PowSearch.Exhausted c` says that the cache `c` holds a search that failed: a base counted in `c`
(the start, or an answer to a base-shaped query) whose `F` candidates are all cached with failing
answers. `PowSearch.prEvent_exhausted_le`: if a uniform answer fails with probability at most
`q ≤ 1`, a computation making at most `N` queries to the lazy random oracle ends with an exhausted
search with probability at most `(N + 1) q^F + N^2 / |Y|`.

The proof is a potential over the cache (`QueryHistory.prEvent_le_of_potential`): each counted
base carries `q` to the number of its candidates not yet asked, or `0` once one passed. A fresh
candidate query keeps the expectation (a martingale step); a fresh base-shaped query counts one more
base, `q^F` in expectation, or up to `1` when the new base already has a cached candidate, which
happens with probability at most `|c| / |Y|`. Nothing about the order of the queries, or about
the bases being fresh, is used.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

@[expose] public section

/-- A proof-of-work search on the oracle `D →ₒ Y`: bases are the answers to base-shaped queries
and `start`; the search from `b` tries `cand b n` for `n < F` and passes on an answer satisfying
`ok`. -/
structure PowSearch (D Y : Type) where
  /-- The base-shaped queries. -/
  isBase : D → Prop
  /-- The candidate inputs of a base. -/
  cand : Y → ℕ → D
  /-- A passing answer. -/
  ok : Y → Prop
  /-- The base counted from the start. -/
  start : Y
  /-- The number of candidates of a search. -/
  F : ℕ
  /-- Candidates below `F` determine their base and index. -/
  cand_inj : ∀ {b b' : Y} {n n' : ℕ}, n < F → n' < F → cand b n = cand b' n' → b = b' ∧ n = n'
  /-- No candidate below `F` is base-shaped. -/
  cand_not_base : ∀ (b : Y) {n : ℕ}, n < F → ¬ isBase (cand b n)

namespace PowSearch

variable {D Y : Type} (S : PowSearch D Y)

/-- A base counted in the cache: the start, or a cached answer to a base-shaped query. -/
def Counted (c : (D →ₒ Y).QueryCache) (b : Y) : Prop :=
  b = S.start ∨ ∃ x, S.isBase x ∧ c x = some b

/-- **An exhausted search**: a counted base whose `F` candidates are cached with failing
answers. -/
def Exhausted (c : (D →ₒ Y).QueryCache) : Prop :=
  ∃ b, S.Counted c b ∧ ∀ n < S.F, ∃ d, c (S.cand b n) = some d ∧ ¬ S.ok d

/-- Some candidate of `b` below `F` is cached with a passing answer. -/
def Found (c : (D →ₒ Y).QueryCache) (b : Y) : Prop :=
  ∃ n < S.F, ∃ d, c (S.cand b n) = some d ∧ S.ok d

open Classical in
/-- The number of candidates of `b` below `F` the cache holds. -/
noncomputable def asked (c : (D →ₒ Y).QueryCache) (b : Y) : ℕ :=
  ((Finset.range S.F).filter fun n ↦ (c (S.cand b n)).isSome).card

open Classical in
/-- The probability that the search from `b` fails, given the cache: `0` once a candidate
passed, `q` to the number of candidates not yet asked otherwise. -/
noncomputable def π (q : ℝ≥0∞) (c : (D →ₒ Y).QueryCache) (b : Y) : ℝ≥0∞ :=
  if S.Found c b then 0 else q ^ (S.F - S.asked c b)

open Classical in
/-- The potential: the failure probabilities of the counted bases, summed. -/
noncomputable def Φ [Fintype Y] (q : ℝ≥0∞) (c : (D →ₒ Y).QueryCache) : ℝ≥0∞ :=
  ∑ b, if S.Counted c b then S.π q c b else 0

open Classical in
/-- The charge of a fresh query: a base-shaped one adds `q^F`, and `|c| / |Y|` for a base whose
candidates were asked before it. -/
noncomputable def charge [Fintype Y] (q : ℝ≥0∞) (c : (D →ₒ Y).QueryCache) (t : D) : ℝ≥0∞ :=
  if S.isBase t then q ^ S.F + c.enncard / Fintype.card Y else 0

/-! ## The cache after a fresh query -/

section Step

variable [DecidableEq D] {c : (D →ₒ Y).QueryCache} {t : D}

theorem counted_cacheQuery_of_not_base (ht : ¬ S.isBase t) (u : Y) (b : Y) :
    S.Counted (c.cacheQuery t u) b ↔ S.Counted c b := by
  refine or_congr Iff.rfl (exists_congr fun x ↦ and_congr_right fun hx ↦ ?_)
  have hxt : x ≠ t := fun h ↦ ht (h ▸ hx)
  rw [QueryCache.cacheQuery_of_ne _ _ hxt]

theorem counted_cacheQuery_of_base (hc : c t = none) (ht : S.isBase t) (u : Y) (b : Y) :
    S.Counted (c.cacheQuery t u) b ↔ S.Counted c b ∨ b = u := by
  constructor
  · rintro (h | ⟨x, hx, hxb⟩)
    · exact .inl (.inl h)
    · by_cases hxt : x = t
      · subst hxt
        rw [QueryCache.cacheQuery_self] at hxb
        exact .inr (Option.some.inj hxb).symm
      · rw [QueryCache.cacheQuery_of_ne _ _ hxt] at hxb
        exact .inl (.inr ⟨x, hx, hxb⟩)
  · rintro ((h | ⟨x, hx, hxb⟩) | rfl)
    · exact .inl h
    · refine .inr ⟨x, hx, ?_⟩
      have hxt : x ≠ t := fun h ↦ by rw [h, hc] at hxb; cases hxb
      rwa [QueryCache.cacheQuery_of_ne _ _ hxt]
    · exact .inr ⟨t, ht, QueryCache.cacheQuery_self _ _ _⟩

/-- A query no candidate of `b` below `F` leaves `b`'s failure probability as it was. -/
theorem π_cacheQuery_of_ne (q : ℝ≥0∞) (b : Y) (hb : ∀ n < S.F, S.cand b n ≠ t) (u : Y) :
    S.π q (c.cacheQuery t u) b = S.π q c b := by
  have hc : ∀ n < S.F, (c.cacheQuery t u) (S.cand b n) = c (S.cand b n) := fun n hn ↦
    QueryCache.cacheQuery_of_ne _ _ (hb n hn)
  have hF : S.Found (c.cacheQuery t u) b ↔ S.Found c b :=
    exists_congr fun n ↦ and_congr_right fun hn ↦ by rw [hc n hn]
  have ha : S.asked (c.cacheQuery t u) b = S.asked c b := by
    unfold asked
    congr 1
    exact Finset.filter_congr fun n hn ↦ by rw [hc n (Finset.mem_range.mp hn)]
  unfold π
  rw [ha]
  by_cases h : S.Found c b
  · rw [ite_eq_left (hF.mpr h), ite_eq_left h]
  · rw [ite_eq_right (mt hF.mp h), ite_eq_right h]

omit [DecidableEq D] in
/-- A search with no candidate asked fails with probability `q^F`. -/
theorem π_of_not_asked (q : ℝ≥0∞) (b : Y) (hb : ∀ n < S.F, c (S.cand b n) = none) :
    S.π q c b = q ^ S.F := by
  have hF : ¬ S.Found c b := fun ⟨n, hn, d, hd, _⟩ ↦ by rw [hb n hn] at hd; cases hd
  have ha : S.asked c b = 0 := by
    unfold asked
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro n hn
    simp [hb n (Finset.mem_range.mp hn)]
  unfold π
  rw [ite_eq_right hF, ha, Nat.sub_zero]

omit [DecidableEq D] in
theorem π_le_one {q : ℝ≥0∞} (hq1 : q ≤ 1) (b : Y) : S.π q c b ≤ 1 := by
  unfold π
  split_ifs
  exacts [zero_le_one, pow_le_one₀ zero_le hq1]

omit [DecidableEq D] in
/-- A search whose `F` candidates are all cached with failing answers has failed: probability
`1`. -/
theorem π_eq_one (q : ℝ≥0∞) (b : Y) (hb : ∀ n < S.F, ∃ d, c (S.cand b n) = some d ∧ ¬ S.ok d) :
    S.π q c b = 1 := by
  have hF : ¬ S.Found c b := fun ⟨n, hn, d, hd, hok⟩ ↦ by
    obtain ⟨d', hd', hnok⟩ := hb n hn
    rw [hd] at hd'
    exact hnok (Option.some.inj hd' ▸ hok)
  have ha : S.asked c b = S.F := by
    unfold asked
    rw [Finset.filter_true_of_mem fun n hn ↦ ?_, Finset.card_range]
    obtain ⟨d, hd, -⟩ := hb n (Finset.mem_range.mp hn)
    simp [hd]
  unfold π
  rw [ite_eq_right hF, ha, Nat.sub_self, pow_zero]

/-- The expectation of `K` on an event is `K` times its probability. -/
private theorem lintegral_ite_const {α : Type} (mx : ProbComp α) (p : α → Prop) [DecidablePred p]
    (K : ℝ≥0∞) :
    ∫⁻ r, r ∂𝒟[(fun x ↦ if p x then K else 0) <$> mx] = K * Pr{let x ← mx}[p x] := by
  let _ : MeasurableSpace α := ⊤
  rw [prEvent_eq_lintegral_id_evalDist_map_ite, lintegral_id_evalDist_map,
    lintegral_id_evalDist_map, ← lintegral_const_mul K Measurable.of_discrete]
  congr 1
  funext x
  split_ifs <;> simp

/-- At a fresh query, the expected failure probability of any base's search is at most what it
was: unchanged unless the query is one of its candidates, a martingale step if it is. -/
theorem lintegral_π_le [SampleableType Y] {q : ℝ≥0∞}
    (hq : Pr{let u ← $ᵗ Y}[¬ S.ok u] ≤ q) (hc : c t = none) (b : Y) :
    ∫⁻ r, r ∂𝒟[(fun u ↦ S.π q (c.cacheQuery t u) b) <$> ($ᵗ Y)] ≤ S.π q c b := by
  classical
  by_cases hcand : ∃ n < S.F, S.cand b n = t
  · obtain ⟨n, hn, rfl⟩ := hcand
    by_cases hfound : S.Found c b
    · refine lintegral_id_evalDist_map_le_of_le _ fun u ↦ ?_
      obtain ⟨n', hn', d, hd, hok⟩ := hfound
      have hne : S.cand b n' ≠ S.cand b n := fun h ↦ by rw [h, hc] at hd; cases hd
      have hd' : (c.cacheQuery (S.cand b n) u) (S.cand b n') = some d := by
        rwa [QueryCache.cacheQuery_of_ne _ _ hne]
      have : S.Found (c.cacheQuery (S.cand b n) u) b := ⟨n', hn', d, hd', hok⟩
      simp only [π, ite_eq_left this, zero_le]
    -- the candidate is new: it passes, or one more candidate is asked
    have hset : ∀ u, ((Finset.range S.F).filter fun n' ↦
        ((c.cacheQuery (S.cand b n) u) (S.cand b n')).isSome) =
        insert n ((Finset.range S.F).filter fun n' ↦ (c (S.cand b n')).isSome) := fun u ↦ by
      ext n'
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_range]
      by_cases h : n' = n
      · subst h
        simp [hn]
      · by_cases hn' : n' < S.F
        · have hne : S.cand b n' ≠ S.cand b n := fun e ↦ h (S.cand_inj hn' hn e).2
          simp [h, hn', QueryCache.cacheQuery_of_ne _ _ hne]
        · simp [h, hn']
    have hnotin : n ∉ (Finset.range S.F).filter fun n' ↦ (c (S.cand b n')).isSome := by
      simp [hc]
    have hlt : S.asked c b < S.F := by
      have hsub : ((Finset.range S.F).filter fun n' ↦ (c (S.cand b n')).isSome) ⊆
          (Finset.range S.F).erase n := fun n' hn' ↦ by
        refine Finset.mem_erase.mpr ⟨fun h ↦ hnotin (h ▸ hn'), (Finset.mem_filter.mp hn').1⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hn), Finset.card_range] at this
      unfold asked
      omega
    have hpt : ∀ u, S.π q (c.cacheQuery (S.cand b n) u) b =
        if ¬ S.ok u then q ^ (S.F - (S.asked c b + 1)) else 0 := fun u ↦ by
      by_cases hok : S.ok u
      · have : S.Found (c.cacheQuery (S.cand b n) u) b :=
          ⟨n, hn, u, QueryCache.cacheQuery_self _ _ _, hok⟩
        simp only [π, ite_eq_left this, hok, not_true_eq_false, ite_false]
      · have hF : ¬ S.Found (c.cacheQuery (S.cand b n) u) b := by
          rintro ⟨n', hn', d, hd, hokd⟩
          by_cases h : n' = n
          · subst h
            rw [QueryCache.cacheQuery_self] at hd
            exact hok (Option.some.inj hd ▸ hokd)
          · have hne : S.cand b n' ≠ S.cand b n := fun e ↦ h (S.cand_inj hn' hn e).2
            rw [QueryCache.cacheQuery_of_ne _ _ hne] at hd
            exact hfound ⟨n', hn', d, hd, hokd⟩
        have ha : S.asked (c.cacheQuery (S.cand b n) u) b = S.asked c b + 1 := by
          unfold asked
          rw [hset u, Finset.card_insert_of_notMem hnotin]
        simp only [π, ite_eq_right hF, ha, hok, not_false_eq_true, ite_true]
    simp only [hpt, lintegral_ite_const]
    rw [π, ite_eq_right hfound, show S.F - S.asked c b = (S.F - (S.asked c b + 1)) + 1 by omega,
      pow_succ]
    gcongr
  · push Not at hcand
    refine lintegral_id_evalDist_map_le_of_le _ fun u ↦ ?_
    rw [S.π_cacheQuery_of_ne q b hcand u]

omit [DecidableEq D] in
/-- At most `|c|` bases have a candidate the cache holds. -/
theorem card_asked_le [Fintype Y] (c : (D →ₒ Y).QueryCache) [DecidablePred fun b ↦
    ∃ n < S.F, (c (S.cand b n)).isSome] :
    ((Finset.univ.filter fun b ↦ ∃ n < S.F, (c (S.cand b n)).isSome).card : ℝ≥0∞) ≤
      c.enncard := by
  classical
  let g : Y → (t : D) × (D →ₒ Y).Range t := fun b ↦
    if h : ∃ n < S.F, (c (S.cand b n)).isSome then
      ⟨S.cand b h.choose, (c (S.cand b h.choose)).get h.choose_spec.2⟩
    else ⟨S.cand b 0, b⟩
  have hmaps : Set.MapsTo g (Finset.univ.filter fun b ↦ ∃ n < S.F, (c (S.cand b n)).isSome :
      Finset Y) c.toSet := fun b hb ↦ by
    have h : ∃ n < S.F, (c (S.cand b n)).isSome := (Finset.mem_filter.mp hb).2
    simp only [g, dite_eq_left h, QueryCache.mem_toSet, Option.some_get]
  have hinj : Set.InjOn g (Finset.univ.filter fun b ↦ ∃ n < S.F, (c (S.cand b n)).isSome :
      Finset Y) := fun b hb b' hb' he ↦ by
    have h : ∃ n < S.F, (c (S.cand b n)).isSome := (Finset.mem_filter.mp hb).2
    have h' : ∃ n < S.F, (c (S.cand b' n)).isSome := (Finset.mem_filter.mp hb').2
    simp only [g, dite_eq_left h, dite_eq_left h'] at he
    exact (S.cand_inj h.choose_spec.1 h'.choose_spec.1 (Sigma.mk.inj he).1).1
  have := Set.encard_le_encard_of_injOn hmaps hinj
  rw [Set.encard_coe_eq_coe_finsetCard] at this
  unfold QueryCache.enncard
  rw [← ENat.toENNReal_coe]
  exact ENat.toENNReal_le.mpr this

omit [DecidableEq D] in
/-- The expected failure probability of the search from a uniform base: `q^F`, or up to `1` for
the at most `|c|` bases the cache holds a candidate of. -/
theorem lintegral_π_uniform_le [Fintype Y] [SampleableType Y] {q : ℝ≥0∞} (hq1 : q ≤ 1)
    (c : (D →ₒ Y).QueryCache) :
    ∫⁻ r, r ∂𝒟[(fun u ↦ S.π q c u) <$> ($ᵗ Y)] ≤ q ^ S.F + c.enncard / Fintype.card Y := by
  classical
  let T : Y → Prop := fun b ↦ ∃ n < S.F, (c (S.cand b n)).isSome
  have hpt : ∀ u, S.π q c u ≤ q ^ S.F + if T u then 1 else 0 := fun u ↦ by
    by_cases hT : T u
    · simp only [hT, ite_true]
      exact (S.π_le_one hq1 u).trans le_add_self
    · simp only [hT, ite_false, add_zero]
      refine (S.π_of_not_asked q u fun n hn ↦ ?_).le
      exact Option.not_isSome_iff_eq_none.mp fun h ↦ hT ⟨n, hn, h⟩
  refine (lintegral_id_evalDist_map_mono _ hpt).trans ?_
  rw [lintegral_id_evalDist_map_const_add _ (OracleComp.prEvent_true_eq_one _),
    ← prEvent_eq_lintegral_id_evalDist_map_ite]
  refine add_le_add le_rfl (((SampleableType.prEvent_uniformSample_le_div_iff T).mpr
    le_rfl).trans ?_)
  exact ENNReal.div_le_div_right (S.card_asked_le c) _

/-- **The step of the potential**: at a fresh query, the expected potential after the uniform
answer is at most the potential before plus the charge. -/
theorem potential_step [Fintype Y] [SampleableType Y] {q : ℝ≥0∞}
    (hq : Pr{let u ← $ᵗ Y}[¬ S.ok u] ≤ q) (hq1 : q ≤ 1) (hc : c t = none) :
    ∫⁻ r, r ∂𝒟[(fun u ↦ S.Φ q (c.cacheQuery t u)) <$> ($ᵗ Y)] ≤
      S.Φ q c + S.charge q c t := by
  classical
  by_cases ht : S.isBase t
  · -- one more base is counted; no search's candidates change
    have hne : ∀ b, ∀ n < S.F, S.cand b n ≠ t := fun b n hn h ↦ S.cand_not_base b hn (h ▸ ht)
    have hpt : ∀ u, S.Φ q (c.cacheQuery t u) ≤ S.Φ q c + S.π q c u := fun u ↦ by
      unfold Φ
      calc _ = ∑ b, if S.Counted c b ∨ b = u then S.π q c b else 0 :=
            Finset.sum_congr rfl fun b _ ↦ by
              rw [if_congr (S.counted_cacheQuery_of_base hc ht u b)
                (S.π_cacheQuery_of_ne q b (hne b) u) rfl]
        _ ≤ ∑ b, ((if S.Counted c b then S.π q c b else 0) +
              if b = u then S.π q c b else 0) :=
            Finset.sum_le_sum fun b _ ↦ by split_ifs <;> simp_all
        _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_ite_eq']; simp
    refine (lintegral_id_evalDist_map_mono _ hpt).trans ?_
    rw [lintegral_id_evalDist_map_const_add _ (OracleComp.prEvent_true_eq_one _), charge,
      ite_eq_left ht]
    exact add_le_add le_rfl (S.lintegral_π_uniform_le hq1 c)
  · -- the counted bases stay; each search is a martingale
    have hpt : (fun u ↦ S.Φ q (c.cacheQuery t u)) =
        fun u ↦ ∑ b, if S.Counted c b then S.π q (c.cacheQuery t u) b else 0 :=
      funext fun u ↦ Finset.sum_congr rfl fun b _ ↦ by
        rw [if_congr (S.counted_cacheQuery_of_not_base ht u b) rfl rfl]
    rw [hpt, lintegral_id_evalDist_map_finset_sum]
    refine le_trans (Finset.sum_le_sum fun b _ ↦ ?_) le_self_add
    split_ifs
    · exact S.lintegral_π_le hq hc b
    · simp

end Step

/-! ## The bound -/

variable [DecidableEq D]

omit [DecidableEq D] in
/-- An exhausted search makes the potential at least `1`. -/
theorem one_le_Φ [Fintype Y] {q : ℝ≥0∞} {c : (D →ₒ Y).QueryCache} (h : S.Exhausted c) :
    1 ≤ S.Φ q c := by
  classical
  obtain ⟨b, hb, hfail⟩ := h
  unfold Φ
  refine le_trans ?_ (Finset.single_le_sum (fun b _ ↦ zero_le) (Finset.mem_univ b))
  rw [ite_eq_left hb, S.π_eq_one q b hfail]

omit [DecidableEq D] in
/-- From the empty cache only the start is counted, with nothing asked. -/
theorem Φ_empty [Fintype Y] (q : ℝ≥0∞) : S.Φ q (∅ : (D →ₒ Y).QueryCache) = q ^ S.F := by
  classical
  unfold Φ
  have : ∀ b, S.Counted (∅ : (D →ₒ Y).QueryCache) b ↔ b = S.start := fun b ↦
    ⟨fun h ↦ h.elim id (fun ⟨_, _, h⟩ ↦ by cases h), .inl⟩
  rw [Finset.sum_congr rfl fun b _ ↦ if_congr (this b) rfl rfl, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  exact S.π_of_not_asked q _ fun _ _ ↦ rfl

/-- **A proof-of-work search is exhausted with small probability.** If a uniform answer fails
with probability at most `q ≤ 1`, a computation making at most `N` queries to the lazy random
oracle ends, from the empty cache, with a counted base whose `F` candidates are all cached and
failing with probability at most `(N + 1) q^F + N^2 / |Y|`. -/
theorem prEvent_exhausted_le [Fintype Y] [SampleableType Y] {q : ℝ≥0∞}
    (hq : Pr{let u ← $ᵗ Y}[¬ S.ok u] ≤ q) (hq1 : q ≤ 1) {α : Type} {oa : OracleComp (D →ₒ Y) α}
    {N : ℕ} (hN : IsTotalQueryBound oa N) :
    Pr{let z ← (simulateQ (D →ₒ Y).randomOracle oa).run ∅}[S.Exhausted z.2] ≤
      (N + 1) * q ^ S.F + N * N / Fintype.card Y := by
  refine (prEvent_le_of_potential _ (S.Φ q) (fun z hz ↦ S.one_le_Φ hz) (S.charge q)
    (fun c t hc ↦ S.potential_step hq hq1 hc) oa ∅).trans ?_
  rw [S.Φ_empty]
  refine (add_le_add le_rfl (QueryHistory.cache.expected_charge_le_mul (κ := q ^ S.F +
    N / Fintype.card Y) hN ∅ fun c t _ hc ↦ ?_)).trans_eq ?_
  · simp only [QueryHistory.cache_view, QueryCache.enncard_empty, zero_add] at hc
    unfold charge
    split_ifs
    · exact add_le_add le_rfl (ENNReal.div_le_div_right (le_self_add.trans hc) _)
    · exact zero_le
  · rw [mul_add, ← mul_div_assoc]
    ring

end PowSearch

end

end LeanerVM.Protocol
