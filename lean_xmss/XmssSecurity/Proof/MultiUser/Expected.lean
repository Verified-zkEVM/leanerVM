import XmssSecurity.Proof.MultiUser.Budget

/-!
# The reductions' counts sum to the budget

A hash input starts with the parameters of at most `1 + C` keys, `C` the ordered pairs of distinct
keys sharing a parameter (`card_attributed_le`); so the counts, over one run's traces, of the calls
starting with each key's parameter sum to at most `(1 + C)` times the run's length, at most
`(1 + C) q` (`sum_counts_le`). The reduction against key `j` counts every trace but key `j`'s own
generation, which holds at least `2^16` of key `j`'s calls, and one verification of at most
`verifyHashBound` calls; the mean of `C` is at most `n^2` pair bounds (`mean_pairs_le`). Summed over
the keys (`sum_expectedAttributedQueries_le`):

`∑ⱼ Eⱼ + 2^16 n ≤ q (1 + n^2 pairBound) + n verifyHashBound`.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.MultiUser

open Seeded

set_option backward.isDefEq.respectTransparency false

-- Keep elaboration from unfolding the seed's uniform draw and key generation's literal tree.
attribute [local irreducible] LeanXmss.sampleMasterSeed LeanXmss.Seeded.keygenFromSeed
  LeanXmss.Seeded.treeNode

variable {n : Nat}

/-! ## Counting over a trace -/

/-- The ordered pairs of distinct keys with the same parameter. -/
def pairs (parameters : Fin n → PublicParameter) : Nat :=
  ((Finset.univ ×ˢ Finset.univ).filter fun ik : Fin n × Fin n =>
    ik.1 ≠ ik.2 ∧ parameters ik.1 = parameters ik.2).card

theorem parameter_eq_of_prefix {left right : PublicParameter} {input : HashInput}
    (hleft : IsParameterHashInput left input) (hright : IsParameterHashInput right input) :
    left = right := by
  unfold IsParameterHashInput at hleft hright
  have hlen : (bytesLE 16 left).length ≤ (bytesLE 16 right).length := by
    simp [bytesLE]
  have h := (List.prefix_of_prefix_length_le hleft hright hlen).eq_of_length (by simp [bytesLE])
  exact bytesLE_injective 16 h

/-- An input starts with the parameters of at most `1 + C` keys. -/
theorem card_attributed_le (parameters : Fin n → PublicParameter) (input : HashInput) :
    (Finset.univ.filter fun j => IsParameterHashInput (parameters j) input).card ≤
      1 + pairs parameters := by
  by_cases hempty : (Finset.univ.filter fun j => IsParameterHashInput (parameters j) input) = ∅
  · rw [hempty, Finset.card_empty]
    exact Nat.zero_le _
  · obtain ⟨j₀, hj₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hj₀' := (Finset.mem_filter.mp hj₀).2
    have hsub : (Finset.univ.filter fun j => IsParameterHashInput (parameters j) input) ⊆
        insert j₀ (Finset.univ.filter fun j => j ≠ j₀ ∧ parameters j = parameters j₀) := by
      intro j hj
      have hj' := (Finset.mem_filter.mp hj).2
      by_cases hjj : j = j₀
      · exact Finset.mem_insert.mpr (.inl hjj)
      · exact Finset.mem_insert.mpr (.inr (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hjj, parameter_eq_of_prefix hj' hj₀'⟩))
    have hpairs : (Finset.univ.filter fun j => j ≠ j₀ ∧ parameters j = parameters j₀).card ≤
        pairs parameters := by
      unfold pairs
      refine Finset.card_le_card_of_injOn (fun j => (j, j₀)) (fun j hj => ?_) (fun a _ b _ h => ?_)
      · have hj' := (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).2
        exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hj'⟩)
      · exact (Prod.mk.inj h).1
    calc _ ≤ (insert j₀ (Finset.univ.filter fun j => j ≠ j₀ ∧ parameters j = parameters j₀)).card :=
          Finset.card_le_card hsub
      _ ≤ (Finset.univ.filter fun j => j ≠ j₀ ∧ parameters j = parameters j₀).card + 1 :=
          Finset.card_insert_le _ _
      _ ≤ 1 + pairs parameters := by omega

/-- **The keys' counts over one trace sum to at most `1 + C` per call.** -/
theorem sum_countP_le (parameters : Fin n → PublicParameter) :
    ∀ trace : List HashInput,
      (∑ j, trace.countP fun input => decide (IsParameterHashInput (parameters j) input)) ≤
        (1 + pairs parameters) * trace.length
  | [] => by simp
  | input :: trace => by
      have hcons : ∀ j, (input :: trace).countP
          (fun input => decide (IsParameterHashInput (parameters j) input)) =
          (if IsParameterHashInput (parameters j) input then 1 else 0) +
            trace.countP fun input => decide (IsParameterHashInput (parameters j) input) := by
        intro j
        rw [List.countP_cons]
        by_cases h : IsParameterHashInput (parameters j) input <;> simp [h, Nat.add_comm]
      simp only [hcons, Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id, List.length_cons]
      have h1 := card_attributed_le parameters input
      have h2 := sum_countP_le parameters trace
      calc _ ≤ (1 + pairs parameters) + (1 + pairs parameters) * trace.length := Nat.add_le_add h1 h2
        _ = _ := by ring

/-! ## Means -/

theorem tsum_mul_le_of_support {α : Type} (mx : ProbComp α) (g : α → ℝ≥0∞) (c : ℝ≥0∞)
    (h : ∀ x ∈ support mx, g x ≤ c) : ∑' x, Pr{let y ← mx}[y = x] * g x ≤ c := by
  calc ∑' x, Pr{let y ← mx}[y = x] * g x ≤ ∑' x, Pr{let y ← mx}[y = x] * c := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        by_cases hx : x ∈ support mx
        · exact mul_le_mul' le_rfl (h x hx)
        · rw [prEvent_eq_zero_of_not_mem_support mx hx, zero_mul, zero_mul]
    _ = c := by rw [ENNReal.tsum_mul_right, OracleComp.tsum_prEvent_eq_one, one_mul]

theorem tsum_mul_mono_of_support {α : Type} (mx : ProbComp α) (g g' : α → ℝ≥0∞)
    (h : ∀ x ∈ support mx, g x ≤ g' x) :
    ∑' x, Pr{let y ← mx}[y = x] * g x ≤ ∑' x, Pr{let y ← mx}[y = x] * g' x := by
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : x ∈ support mx
  · exact mul_le_mul' le_rfl (h x hx)
  · rw [prEvent_eq_zero_of_not_mem_support mx hx, zero_mul, zero_mul]

/-! ## One reduction's count -/

/-- The parameters of a prefix's keys. -/
def prefixParameters (parts : Fin n → KeyPair × List HashInput) : Fin n → PublicParameter :=
  fun i => (parts i).1.1.parameter

/-- Key `j`'s count over a prefix's traces but its own generation. -/
def prefixCount (j : Fin n) (parts : Fin n → KeyPair × List HashInput) (rest : List HashInput) : Nat :=
  (flatTrace (blank j parts) ++ rest).countP fun input =>
    decide (IsParameterHashInput (prefixParameters parts j) input)

theorem expectedAttributedQueries_le_prefix (adversary : LeanXmss.MultiUser.Adversary n) (j : Fin n) :
    LeanXmss.Security.expectedAttributedQueries (reduction adversary j) ≤
      ∑' y, Pr{let x ← romRun (tracedPrefix adversary) ∅}[x = y] *
        ((prefixCount j y.1.1 y.1.2.2 : Nat) + (verifyHashBound : ℝ≥0∞)) := by
  rw [expectedAttributedQueries_reduction, tracedAt_eq, StateT.run'_eq]
  change ∑' x, Pr{let y ← Prod.fst <$> romRun _ ∅}[y = x] * _ ≤ _
  rw [OracleComp.tsum_prEvent_map_mul, romRun_bind, OracleComp.tsum_prEvent_bind_mul]
  refine ENNReal.tsum_le_tsum fun y => mul_le_mul' le_rfl ?_
  refine tsum_mul_le_of_support _ _ _ fun z hz => ?_
  rw [romRun_bind, mem_support_bind_iff] at hz
  obtain ⟨f, hf, hz⟩ := hz
  simp only [romRun, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  have hfinish := length_trace_finish_le _ _ _ _ f hf
  have hle : (flatTrace (blank j y.1.1) ++ (y.1.2.2 ++ f.1.2)).countP
        (fun input => decide (IsParameterHashInput (y.1.1 j).1.1.parameter input)) ≤
      prefixCount j y.1.1 y.1.2.2 + verifyHashBound := by
    unfold prefixCount prefixParameters
    rw [← List.append_assoc, List.countP_append]
    exact Nat.add_le_add le_rfl (List.countP_le_length.trans hfinish)
  exact_mod_cast hle

/-! ## The sum over the keys -/

theorem mem_support_sequenceFin {α : Type} :
    ∀ {n : Nat} (computation : Fin n → OracleComp OracleWorld α) (cache : QueryCache HashSpec)
      (r : (Fin n → α) × QueryCache HashSpec),
      r ∈ support (romRun (LeanXmss.Concrete.sequenceFin computation) cache) →
        ∀ i, ∃ start finish, (r.1 i, finish) ∈ support (romRun (computation i) start)
  | 0, _, _, _, _, i => i.elim0
  | n + 1, computation, cache, r, hr, i => by
      simp only [LeanXmss.Concrete.sequenceFin] at hr
      rw [romRun_bind, mem_support_bind_iff] at hr
      obtain ⟨head, hhead, hrest⟩ := hr
      rw [romRun_bind, mem_support_bind_iff] at hrest
      obtain ⟨tail, htail, hfinal⟩ := hrest
      simp only [romRun, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hfinal
      subst hfinal
      cases i using Fin.cases with
      | zero => exact ⟨cache, head.2, hhead⟩
      | succ i => exact mem_support_sequenceFin (fun i => computation i.succ) _ tail htail i

theorem tracedPrefix_parts (adversary : LeanXmss.MultiUser.Adversary n) (cache : QueryCache HashSpec)
    (y : _ × QueryCache HashSpec) (hy : y ∈ support (romRun (tracedPrefix adversary) cache)) :
    ∃ parts ∈ support (romRun (LeanXmss.Concrete.sequenceFin (fun _ : Fin n => tracedKeygen)) cache),
      parts.1 = y.1.1 := by
  unfold tracedPrefix at hy
  rw [romRun_bind, mem_support_bind_iff] at hy
  obtain ⟨parts, hparts, hy⟩ := hy
  rw [romRun, simulateQ_map, StateT.run_map, support_map] at hy
  obtain ⟨s, _, rfl⟩ := hy
  exact ⟨parts, hparts, rfl⟩

/-- **Pointwise**: the keys' counts and their own generations' calls are at most `(1 + C) q`. -/
theorem sum_prefixCount_le (adversary : LeanXmss.MultiUser.Adversary n) (q : Nat)
    (hbound : LeanXmss.MultiUser.HasHashQueryBound adversary q)
    (y : _ × QueryCache HashSpec) (hy : y ∈ support (romRun (tracedPrefix adversary) ∅)) :
    (∑ j, prefixCount j y.1.1 y.1.2.2) + n * 2 ^ 16 ≤
      (1 + pairs (prefixParameters y.1.1)) * q := by
  obtain ⟨parts, hparts, hpartsEq⟩ := tracedPrefix_parts adversary ∅ y hy
  have hown : ∀ j, 2 ^ 16 ≤ (y.1.1 j).2.countP fun input =>
      decide (IsParameterHashInput (prefixParameters y.1.1 j) input) := by
    intro j
    obtain ⟨start, finish, hmem⟩ := mem_support_sequenceFin _ ∅ parts hparts j
    rw [hpartsEq] at hmem
    have h := own_count_le start _ hmem
    unfold prefixParameters
    exact h
  have hsplit : ∀ j, prefixCount j y.1.1 y.1.2.2 + (y.1.1 j).2.countP (fun input =>
        decide (IsParameterHashInput (prefixParameters y.1.1 j) input)) =
      (flatTrace y.1.1 ++ y.1.2.2).countP fun input =>
        decide (IsParameterHashInput (prefixParameters y.1.1 j) input) := by
    intro j
    unfold prefixCount
    rw [List.countP_append, List.countP_append, countP_flatTrace, countP_flatTrace,
      Nat.add_right_comm, sum_blank j y.1.1 _ rfl]
  have htotal := sum_countP_le (prefixParameters y.1.1) (flatTrace y.1.1 ++ y.1.2.2)
  have hlen := prefix_length_le adversary q hbound y hy
  rw [List.length_append] at htotal
  calc (∑ j, prefixCount j y.1.1 y.1.2.2) + n * 2 ^ 16
      ≤ (∑ j, prefixCount j y.1.1 y.1.2.2) + ∑ j, (y.1.1 j).2.countP (fun input =>
          decide (IsParameterHashInput (prefixParameters y.1.1 j) input)) := by
        refine Nat.add_le_add le_rfl ?_
        have := Finset.card_nsmul_le_sum Finset.univ _ (2 ^ 16) fun j _ => hown j
        simpa using this
    _ = ∑ j, (flatTrace y.1.1 ++ y.1.2.2).countP (fun input =>
          decide (IsParameterHashInput (prefixParameters y.1.1 j) input)) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => hsplit j
    _ ≤ (1 + pairs (prefixParameters y.1.1)) * ((flatTrace y.1.1).length + y.1.2.2.length) := htotal
    _ ≤ _ := Nat.mul_le_mul le_rfl hlen

/-- A prefix's result and cache. -/
abbrev PrefixState (n : Nat) :=
  ((Fin n → KeyPair × List HashInput) × ((LeanXmss.MultiUser.Forgery n ×
    QueryLog (LeanXmss.MultiUser.SigningSpec n)) × List HashInput)) × QueryCache HashSpec

/-- **The mean number of pairs sharing a parameter.** -/
theorem mean_pairs_le (adversary : LeanXmss.MultiUser.Adversary n) :
    ∑' y, Pr{let x ← romRun (tracedPrefix adversary) ∅}[x = y] *
        ((pairs (prefixParameters y.1.1) : Nat) : ℝ≥0∞) ≤ ((n * n : Nat) : ℝ≥0∞) * pairBound := by
  have hpairs : ∀ y : PrefixState n, ((pairs (prefixParameters y.1.1) : Nat) : ℝ≥0∞) =
      ∑ ik ∈ (Finset.univ ×ˢ Finset.univ : Finset (Fin n × Fin n)),
        if ik.1 ≠ ik.2 ∧ prefixParameters y.1.1 ik.1 = prefixParameters y.1.1 ik.2 then 1 else 0 := by
    intro y
    unfold pairs
    rw [Finset.card_filter]
    push_cast
    rfl
  simp only [hpairs, Finset.mul_sum]
  rw [Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
  have hcard : ((n * n : Nat) : ℝ≥0∞) * pairBound =
      ∑ _ik ∈ (Finset.univ ×ˢ Finset.univ : Finset (Fin n × Fin n)), pairBound := by
    rw [Finset.sum_const, Finset.card_product, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hcard]
  refine Finset.sum_le_sum fun ik _ => ?_
  have hevent : ∑' y, Pr{let x ← romRun (tracedPrefix adversary) ∅}[x = y] *
        (if ik.1 ≠ ik.2 ∧ prefixParameters y.1.1 ik.1 = prefixParameters y.1.1 ik.2 then 1 else 0) =
      Pr{let x ← romRun (tracedPrefix adversary) ∅}[ik.1 ≠ ik.2 ∧
        prefixParameters x.1.1 ik.1 = prefixParameters x.1.1 ik.2] := by
    rw [OracleComp.prEvent_eq_tsum_ite]
    refine tsum_congr fun y => ?_
    split <;> simp
  rw [hevent]
  by_cases hik : ik.1 = ik.2
  · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun y _ h => h.1 hik]
    exact zero_le
  · unfold tracedPrefix
    refine probEvent_sequence_pair_le ik.1 ik.2 hik _
      (fun r : (Fin n → KeyPair × List HashInput) × ((LeanXmss.MultiUser.Forgery n ×
          QueryLog (LeanXmss.MultiUser.SigningSpec n)) × List HashInput) =>
        ik.1 ≠ ik.2 ∧ prefixParameters r.1 ik.1 = prefixParameters r.1 ik.2) ?_
    intro parts cache r hr hevent
    rw [romRun, simulateQ_map, StateT.run_map, support_map] at hr
    obtain ⟨s, _, rfl⟩ := hr
    exact hevent.2

/-- **The reductions' attributable counts sum to the budget**, up to the pairs sharing a parameter
and one verification per key, less the `2^16` own calls of each key generation. -/
theorem sum_expectedAttributedQueries_le (adversary : LeanXmss.MultiUser.Adversary n) (q : Nat)
    (hbound : LeanXmss.MultiUser.HasHashQueryBound adversary q) :
    (∑ j, LeanXmss.Security.expectedAttributedQueries (reduction adversary j)) +
        ((n * 2 ^ 16 : Nat) : ℝ≥0∞) ≤
      (q : ℝ≥0∞) * (1 + ((n * n : Nat) : ℝ≥0∞) * pairBound) + ((n * verifyHashBound : Nat) : ℝ≥0∞) := by
  set μ := romRun (tracedPrefix adversary) ∅
  have hone : ∀ c : ℝ≥0∞, ∑' y, Pr{let x ← μ}[x = y] * c = c := fun c => by
    rw [ENNReal.tsum_mul_right, OracleComp.tsum_prEvent_eq_one, one_mul]
  calc (∑ j, LeanXmss.Security.expectedAttributedQueries (reduction adversary j)) +
        ((n * 2 ^ 16 : Nat) : ℝ≥0∞)
      ≤ (∑ j, ∑' y, Pr{let x ← μ}[x = y] *
          ((prefixCount j y.1.1 y.1.2.2 : Nat) + (verifyHashBound : ℝ≥0∞))) +
          ∑' y, Pr{let x ← μ}[x = y] * ((n * 2 ^ 16 : Nat) : ℝ≥0∞) := by
        rw [hone]
        exact add_le_add (Finset.sum_le_sum fun j _ => expectedAttributedQueries_le_prefix adversary j)
          le_rfl
    _ = ∑' y, Pr{let x ← μ}[x = y] *
          (((∑ j, prefixCount j y.1.1 y.1.2.2 + n * 2 ^ 16 : Nat) : ℝ≥0∞) +
            ((n * verifyHashBound : Nat) : ℝ≥0∞)) := by
        rw [← Summable.tsum_finsetSum fun _ _ => ENNReal.summable, ← ENNReal.tsum_add]
        refine tsum_congr fun y => ?_
        rw [← Finset.mul_sum, ← mul_add]
        congr 1
        push_cast
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
    _ ≤ ∑' y, Pr{let x ← μ}[x = y] *
          (((1 + pairs (prefixParameters y.1.1)) * q : Nat) + ((n * verifyHashBound : Nat) : ℝ≥0∞)) := by
        refine tsum_mul_mono_of_support μ _ _ fun y hy => ?_
        gcongr
        exact_mod_cast sum_prefixCount_le adversary q hbound y hy
    _ = (q : ℝ≥0∞) * (1 + ∑' y, Pr{let x ← μ}[x = y] * ((pairs (prefixParameters y.1.1) : Nat) : ℝ≥0∞)) +
          ((n * verifyHashBound : Nat) : ℝ≥0∞) := by
        have hsplit : ∀ y : PrefixState n,
            Pr{let x ← μ}[x = y] * ((((1 + pairs (prefixParameters y.1.1)) * q : Nat) : ℝ≥0∞) +
              ((n * verifyHashBound : Nat) : ℝ≥0∞)) =
            Pr{let x ← μ}[x = y] * (q : ℝ≥0∞) +
              (q : ℝ≥0∞) * (Pr{let x ← μ}[x = y] * ((pairs (prefixParameters y.1.1) : Nat) : ℝ≥0∞)) +
              Pr{let x ← μ}[x = y] * ((n * verifyHashBound : Nat) : ℝ≥0∞) := by
          intro y
          push_cast
          ring
        simp only [hsplit]
        rw [ENNReal.tsum_add, ENNReal.tsum_add, hone, hone, ENNReal.tsum_mul_left, mul_add, mul_one]
    _ ≤ _ := by
        gcongr
        exact mean_pairs_le adversary

end XmssSecurity.MultiUser
