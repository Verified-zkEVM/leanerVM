import Sphincs.MultiFree
import Sphincs.Uniform

/-! **Keys sharing a parameter.** Two keys generated from independent seeds share their public
parameter with chance at most `2^-128 + 2 · 2^-256`: equal seeds, equal scheme seeds, or a collision
of the 128-bit parameters of two distinct parameter derivations. Summed over the pairs, the expected
number of pairs of the `n` keys sharing their parameter is at most `n (n - 1) / 2` times that. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.Multi

open MultiEager Completeness Internalize Short Eager SeedCoupling KeyOnly

set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-! ### Two points of a uniform table -/

theorem mean_update (x : ShortIn) (G : Table → ℝ≥0∞) :
    mean ($ᵗ Table) G = mean ($ᵗ Table) fun g => mean ($ᵗ HashOutput) fun u => G (Function.update g x u) := by
  rw [← mean_congr (uniformSample_bind_update_evalDistEq (D := ShortIn) (R := HashOutput) x),
    ← mean_congr (OracleComp.EvalDistEq.bind_bind_swap _ _ _)]
  simp only [mean_bind, mean_pure]

theorem mean_const' {α : Type} (mx : ProbComp α) (c : ℝ≥0∞) : mean mx (fun _ => c) = c := by
  have h := mean_const_mul mx c (fun _ => 1)
  simp only [mul_one] at h
  rw [h, Det.mean_one, mul_one]

theorem mean_comm {α β : Type} (mx : ProbComp α) (my : ProbComp β) (G : α → β → ℝ≥0∞) :
    mean mx (fun a => mean my (G a)) = mean my (fun b => mean mx fun a => G a b) := by
  have h := mean_congr (OracleComp.EvalDistEq.bind_bind_swap mx my (fun a b => pure (a, b)))
    (fun p : α × β => G p.1 p.2)
  simp only [mean_bind, mean_pure] at h
  exact h

/-- Two distinct points of a uniform table collide in their first 128 bits with chance `2^-128`. -/
theorem mean_trunc_collide (x y : ShortIn) (hxy : x ≠ y) :
    mean ($ᵗ Table) (fun T => if truncateHash (T x) = truncateHash (T y) then 1 else 0) =
      (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  rw [mean_update x]
  have hin : ∀ g : Table, mean ($ᵗ HashOutput) (fun u => if truncateHash (Function.update g x u x) =
      truncateHash (Function.update g x u y) then 1 else 0) = (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
    intro g
    simp only [Function.update_self, Function.update_of_ne hxy.symm]
    rw [mean_indicator]
    exact probEvent_uniform_truncateHash_eq _
  simp only [hin]
  exact mean_const' _ _

/-! ### Two keys -/

/-- The public parameter of the key of seed `s` under the table `T`. -/
noncomputable def paramOf (T : Table) (s : MasterSeed) : PublicParameter :=
  truncateHash (extend ∅ T (keygenHashInput 0 .parameter (extend ∅ T (schemeSeedInput s))))

theorem extend_empty_short (T : Table) (x : HashInput) (hx : IsShort x) : extend ∅ T x = T ⟨x, hx⟩ := by
  simp [extend, hx]

theorem keygenHashInput_short (p : PublicParameter) (d : KeygenDomain) (m : MasterSeed) :
    IsShort (keygenHashInput p d m) := by
  simp [IsShort, bound, keygenHashInput_length]

theorem keygenHashInput_ne_schemeSeedInput (p : PublicParameter) (d : KeygenDomain) (m s : MasterSeed) :
    keygenHashInput p d m ≠ schemeSeedInput s := by
  intro h
  have := congrArg List.length h
  rw [keygenHashInput_length, schemeSeedInput_length] at this
  omega

theorem keygenHashInput_seed_injective (p : PublicParameter) (d : KeygenDomain) {m m' : MasterSeed}
    (h : keygenHashInput p d m = keygenHashInput p d m') : m = m' := by
  unfold keygenHashInput at h
  rw [List.append_assoc, List.append_assoc] at h
  exact bytesLE_injective (List.append_cancel_left (List.append_cancel_left h))

/-- **Two keys from distinct seeds share their parameter with chance `2^-128 + 2^-256`.** -/
theorem mean_paramOf_collide (s s' : MasterSeed) (hs : s ≠ s') :
    mean ($ᵗ Table) (fun T => if paramOf T s = paramOf T s' then 1 else 0) ≤
      (Fintype.card HashOutput : ℝ≥0∞)⁻¹ + (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  set a : ShortIn := ⟨schemeSeedInput s, Det.schemeSeedInput_short s⟩ with ha
  set a' : ShortIn := ⟨schemeSeedInput s', Det.schemeSeedInput_short s'⟩ with ha'
  have haa : a ≠ a' := fun h => hs (Det.schemeSeedInput_injective (congrArg Subtype.val h))
  set pi : MasterSeed → ShortIn := fun m => ⟨keygenHashInput 0 .parameter m, keygenHashInput_short _ _ _⟩ with hpi
  have hpa : ∀ m, pi m ≠ a := fun m h => keygenHashInput_ne_schemeSeedInput _ _ _ _ (congrArg Subtype.val h)
  have hpa' : ∀ m, pi m ≠ a' := fun m h => keygenHashInput_ne_schemeSeedInput _ _ _ _ (congrArg Subtype.val h)
  have hval : ∀ (h : Table) (u u' : HashOutput),
      (paramOf (Function.update (Function.update h a' u') a u) s =
        paramOf (Function.update (Function.update h a' u') a u) s') ↔
        truncateHash (h (pi u)) = truncateHash (h (pi u')) := by
    intro h u u'
    unfold paramOf
    rw [extend_empty_short _ _ (Det.schemeSeedInput_short s), extend_empty_short _ _ (Det.schemeSeedInput_short s'),
      extend_empty_short _ _ (keygenHashInput_short _ _ _), extend_empty_short _ _ (keygenHashInput_short _ _ _)]
    change truncateHash (Function.update (Function.update h a' u') a u
        (pi (Function.update (Function.update h a' u') a u a))) =
      truncateHash (Function.update (Function.update h a' u') a u
        (pi (Function.update (Function.update h a' u') a u a'))) ↔ _
    rw [Function.update_self, Function.update_of_ne haa.symm, Function.update_self,
      Function.update_of_ne (hpa u), Function.update_of_ne (hpa' u), Function.update_of_ne (hpa u'),
      Function.update_of_ne (hpa' u')]
  rw [mean_update a, mean_update a']
  simp only [hval]
  have hbound : ∀ u u' : HashOutput, mean ($ᵗ Table) (fun h =>
      if truncateHash (h (pi u)) = truncateHash (h (pi u')) then (1 : ℝ≥0∞) else 0) ≤
      (if u = u' then 1 else 0) + (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
    intro u u'
    by_cases huu : u = u'
    · rw [ite_eq_left huu]
      exact (mean_le_const _ fun _ => by split_ifs <;> simp).trans le_self_add
    · rw [ite_eq_right huu, zero_add]
      refine le_of_eq (mean_trunc_collide (pi u) (pi u') fun h => huu ?_)
      exact keygenHashInput_seed_injective _ _ (congrArg Subtype.val h)
  calc _ = mean ($ᵗ HashOutput) (fun u' => mean ($ᵗ Table) fun h => mean ($ᵗ HashOutput) fun u =>
        if truncateHash (h (pi u)) = truncateHash (h (pi u')) then (1 : ℝ≥0∞) else 0) := mean_comm _ _ _
    _ = mean ($ᵗ HashOutput) (fun u' => mean ($ᵗ HashOutput) fun u => mean ($ᵗ Table) fun h =>
        if truncateHash (h (pi u)) = truncateHash (h (pi u')) then (1 : ℝ≥0∞) else 0) :=
        congrArg _ (funext fun u' => mean_comm _ _ _)
    _ ≤ mean ($ᵗ HashOutput) (fun u' => mean ($ᵗ HashOutput) fun u =>
        (if u = u' then 1 else 0) + (Fintype.card Digest : ℝ≥0∞)⁻¹) :=
        mean_mono _ fun u' => mean_mono _ fun u => hbound u u'
    _ = _ := by
        simp only [mean_add, mean_indicator, SampleableType.prEvent_uniformSample_eq_singleton, mean_const']

/-! ### The seeds -/

theorem mean_seeds_eq {n : ℕ} (i k : Fin n) (hik : i ≠ k) :
    mean (sampleSeeds n) (fun seeds => if seeds i = seeds k then 1 else 0) = (Fintype.card MasterSeed : ℝ≥0∞)⁻¹ := by
  let : SampleableType (Fin n → MasterSeed) := SampleableType.ofFintype (Fin n → MasterSeed)
  change mean ($ᵗ (Fin n → MasterSeed)) _ = _
  rw [← mean_congr (uniformSample_bind_update_evalDistEq (D := Fin n) (R := MasterSeed) k),
    ← mean_congr (OracleComp.EvalDistEq.bind_bind_swap _ _ _)]
  simp only [mean_bind, mean_pure, Function.update_self, Function.update_of_ne hik]
  have hin : ∀ g : Fin n → MasterSeed, mean ($ᵗ MasterSeed) (fun u => if g i = u then (1 : ℝ≥0∞) else 0) =
      (Fintype.card MasterSeed : ℝ≥0∞)⁻¹ := by
    intro g
    rw [mean_indicator, ← SampleableType.prEvent_uniformSample_eq_singleton (g i)]
    exact prEvent_congr_of_support _ _ _ fun u _ => eq_comm
  simp only [hin]
  exact mean_const' _ _

/-! ### The keys of the multi-user game -/

variable [Params] {n : ℕ}

theorem valF_keygenAll_param (T : Table) (seeds : Fin n → MasterSeed) (i : Fin n) :
    (valF (extend ∅ T) (keygenAll n seeds) i).1.parameter = paramOf T (seeds i) := by
  rw [keygenAll_eq, valF_keygenSel]
  simp only [keyAt, Option.elim_none]
  rw [show (keygenOne (seeds i) : OracleComp HashSpec _) =
    (liftM (HashSpec.query (schemeSeedInput (seeds i))) >>= fun master =>
      liftM (HashSpec.query (keygenHashInput 0 .parameter master)) >>= fun out =>
        Seeded.treeRoot (truncateHash out) topLayer Concrete.rootTree master >>= fun root =>
          pure (⟨root, truncateHash out⟩, ⟨master, truncateHash out, root⟩)) from rfl]
  rw [valF_query_bind, valF_query_bind, valF_bind]
  rfl

/-- The keys of the game before the check are those of key generation under a uniform table. -/
theorem mean_prefix_keys (adversary : Adversary n) (G : (Fin n → PublicKey × Seeded.SecretKey) → ℝ≥0∞) :
    mean ((simulateQ romImpl (cntW wK (prefixMU adversary))).run ∅) (fun r => G r.1.1.1) =
      mean (sampleSeeds n) (fun seeds => mean ($ᵗ Table) fun T => G (valF (extend ∅ T) (keygenAll n seeds))) := by
  rw [show prefixMU adversary = (liftM (sampleSeeds n) : OracleComp OracleWorld _) >>= fun seeds =>
      (liftM (keygenAll n seeds) : OracleComp OracleWorld _) >>= fun keys =>
        (fun result => (keys, result)) <$> runMU keys (adversary.main fun i => (keys i).1) by
    simp only [prefixMU, bind_pure_comp],
    cntW_sampling_bind, simulateQ_bind, StateT.run_bind, run_lift_prob, bind_map_left, mean_bind]
  refine congrArg _ (funext fun seeds => ?_)
  rw [cntW_bind, simulateQ_bind, StateT.run_bind, mean_bind]
  have hin : ∀ r1 : ((Fin n → PublicKey × Seeded.SecretKey) × (ℕ × (PublicParameter → ℕ)) × ℕ) ×
      QueryCache HashSpec,
      mean ((simulateQ romImpl (do
        let second ← cntW wK ((fun result => (r1.1.1, result)) <$> runMU r1.1.1
          (adversary.main fun i => (r1.1.1 i).1))
        pure (second.1, r1.1.2 + second.2))).run r1.2) (fun r => G r.1.1.1) = G r1.1.1 := by
    intro r1
    rw [cntW_map, simulateQ_bind, StateT.run_bind, mean_bind, simulateQ_map, StateT.run_map, mean_map]
    simp only [simulateQ_pure, StateT.run_pure, mean_pure]
    exact mean_const' _ (G r1.1.1)
  simp only [hin]
  rw [mean_congr (evalDist_cntW_liftM wK (keygenAll n seeds) (by rw [keygenAll_eq]; exact only_keygenSel n _ _)),
    mean_bind]
  simp only [mean_pure]

/-- The chance that two keys share their parameter. -/
noncomputable def pairChance : ℝ≥0∞ :=
  (Fintype.card MasterSeed : ℝ≥0∞)⁻¹ + ((Fintype.card HashOutput : ℝ≥0∞)⁻¹ + (Fintype.card Digest : ℝ≥0∞)⁻¹)

/-- **The expected pairs of keys sharing their parameter.** -/
theorem mean_pairs_prefix (adversary : Adversary n) :
    mean ((simulateQ romImpl (cntW wK (prefixMU adversary))).run ∅)
        (fun r => ((pairs fun i => (r.1.1.1 i).1.parameter : ℕ) : ℝ≥0∞)) ≤ (n * n : ℝ≥0∞) * pairChance := by
  rw [mean_prefix_keys adversary (fun keys => ((pairs fun i => (keys i).1.parameter : ℕ) : ℝ≥0∞))]
  simp only [valF_keygenAll_param, pairs, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero]
  rw [show (fun seeds : Fin n → MasterSeed => mean ($ᵗ Table) fun T =>
      ∑ ik : Fin n × Fin n, if ik.1 < ik.2 ∧ paramOf T (seeds ik.1) = paramOf T (seeds ik.2) then (1 : ℝ≥0∞) else 0) =
      fun seeds => ∑ ik : Fin n × Fin n, mean ($ᵗ Table) fun T =>
        if ik.1 < ik.2 ∧ paramOf T (seeds ik.1) = paramOf T (seeds ik.2) then (1 : ℝ≥0∞) else 0 from
    funext fun seeds => mean_finset_sum' _ _ _, mean_finset_sum']
  calc _ ≤ ∑ _ik : Fin n × Fin n, pairChance := by
        refine Finset.sum_le_sum fun ik _ => ?_
        by_cases hlt : ik.1 < ik.2
        · have hne : ik.1 ≠ ik.2 := ne_of_lt hlt
          calc _ ≤ mean (sampleSeeds n) (fun seeds => (if seeds ik.1 = seeds ik.2 then 1 else 0) +
                ((Fintype.card HashOutput : ℝ≥0∞)⁻¹ + (Fintype.card Digest : ℝ≥0∞)⁻¹)) := by
                refine mean_mono _ fun seeds => ?_
                simp only [hlt, true_and]
                by_cases hs : seeds ik.1 = seeds ik.2
                · rw [ite_eq_left hs]
                  exact (mean_le_const _ fun _ => by split_ifs <;> simp).trans le_self_add
                · rw [ite_eq_right hs, zero_add]
                  exact mean_paramOf_collide _ _ hs
            _ = pairChance := by
                rw [mean_add, mean_seeds_eq _ _ hne, mean_const']
                rfl
        · simp only [hlt, false_and, ite_false]
          rw [mean_const', mean_const']
          exact bot_le
    _ = (n * n : ℝ≥0∞) * pairChance := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

end Sphincs.Security.Multi
