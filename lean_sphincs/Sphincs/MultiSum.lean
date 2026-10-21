import Sphincs.MultiKey
import Sphincs.VerificationCost

/-! **Summing the keys.** The multi-user game checking key `j` makes at most `q + 307` short calls
when the experiment makes at most `q` (the check is one verification, at most 307 calls), and the
short calls on the keys, summed over the keys, are at most the short calls times one plus the
number of pairs of keys sharing their parameter. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.Multi

open MultiEager Completeness Internalize Short Eager SeedCoupling KeyOnly

set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-! ### Runs read their answers from the final cache -/

/-- The answers of a cache, a default where it has none. -/
noncomputable def cacheFn (cache : QueryCache HashSpec) : HashInput → HashOutput :=
  fun x => (cache x).getD 0

theorem run_cntW_cache {ω : Type} [AddCommMonoid ω] (w : HashInput → ω) {α : Type} (oa : OracleComp HashSpec α) :
    ∀ (cache : QueryCache HashSpec) r,
      r ∈ support ((simulateQ romImpl (cntW w (liftM oa : OracleComp OracleWorld α))).run cache) →
        (∀ x v, cache x = some v → r.2 x = some v) ∧ r.1.2 = callsW w (cacheFn r.2) oa := by
  induction oa using OracleComp.inductionOn with
  | pure value =>
      intro cache r hr
      rw [show (liftM (pure value : OracleComp HashSpec α) : OracleComp OracleWorld α) = pure value from rfl] at hr
      rw [mem_support_run_cntW_pure w value hr]
      exact ⟨fun x v h => h, rfl⟩
  | query_bind input next ih =>
      intro cache r hr
      rw [liftM_bind] at hr
      obtain ⟨r1, hr1, r2, hr2, rfl⟩ := mem_support_run_cntW_bind w
        (g := (liftM (OracleWorld.query (.inr input)) : OracleComp OracleWorld _)) hr
      have h1 := mem_support_run_cntW_query w (.inr input) hr1
      have hc1 : (∀ x v, cache x = some v → r1.2 x = some v) ∧ r1.2 input = some r1.1.1 := by
        rw [show (liftM (OracleWorld.query (.inr input)) : OracleComp OracleWorld _) =
          liftM (OracleWorld.query (.inr input)) >>= fun a => pure a from (bind_pure _).symm, cntW_query_bind] at hr1
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff, cntW_pure,
          simulateQ_pure, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hr1
        obtain ⟨a, ha, rfl⟩ := hr1
        change a ∈ support ((randomOracle (spec := HashSpec) input).run cache) at ha
        cases hc : cache input with
        | some answer =>
            rw [QueryImpl.withCaching_run_some _ hc, support_pure, Set.mem_singleton_iff] at ha
            subst ha
            exact ⟨fun x v h => h, hc⟩
        | none =>
            rw [QueryImpl.withCaching_run_none _ hc, support_map] at ha
            obtain ⟨u, -, rfl⟩ := ha
            refine ⟨fun x v h => ?_, by simp⟩
            by_cases hx : x = input
            · subst hx; rw [hc] at h; cases h
            · rw [QueryCache.cacheQuery_of_ne _ _ hx]; exact h
      obtain ⟨hext, hcalls⟩ := ih r1.1.1 r1.2 r2 hr2
      refine ⟨fun x v h => hext x v (hc1.1 x v h), ?_⟩
      have hans : cacheFn r2.2 input = r1.1.1 := by simp [cacheFn, hext input r1.1.1 hc1.2]
      simp only [callsW_query_bind, hans, ← hcalls, h1, weightOf]

theorem callsW_wS_le_hashTrace (f : HashInput → HashOutput) {α : Type} (oa : OracleComp HashSpec α) :
    callsW wS f oa ≤ (Cost.hashTrace f oa).length := by
  induction oa using OracleComp.inductionOn with
  | pure value => simp [callsW]
  | query_bind input next ih =>
      rw [callsW_query_bind, Cost.hashTrace_query_bind, List.length_cons]
      have : wS input ≤ 1 := by unfold wS; split_ifs <;> omega
      have h := ih (f input)
      omega

theorem hashTrace_length_le_compressions (f : HashInput → HashOutput) {α : Type} (oa : OracleComp HashSpec α) :
    (Cost.hashTrace f oa).length ≤ Cost.compressions f oa := by
  unfold Cost.compressions
  generalize Cost.hashTrace f oa = l
  induction l with
  | nil => simp
  | cons x l ih =>
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      have : 1 ≤ Cost.blocks x.length := le_max_left _ _
      omega

/-- **A verification makes at most 307 short calls.** -/
theorem verify_short_le (pk : PublicKey) (message : Message) (signature : Signature) (cache : QueryCache HashSpec)
    r (hr : r ∈ support ((simulateQ romImpl (cntW wS (liftM (Concrete.verify pk message signature :
      OracleComp HashSpec Bool) : OracleComp OracleWorld Bool))).run cache)) : r.1.2 ≤ 307 := by
  rw [(run_cntW_cache wS _ cache r hr).2]
  exact (callsW_wS_le_hashTrace _ _).trans ((hashTrace_length_le_compressions _ _).trans
    (Cost.verification_compressions_le _ _ _ _))

/-! ### Reachable runs -/

theorem reach_bind_iff {α β : Type} (mx : ProbComp α) (f : α → ProbComp β) (y : β) :
    Reach (mx >>= f) y ↔ ∃ x, Reach mx x ∧ Reach (f x) y := by
  simp only [reach_iff, mem_support_bind_iff]

theorem reach_nonempty {α : Type} (mx : ProbComp α) : ∃ x, Reach mx x := by
  obtain ⟨x, hx⟩ := support_nonempty mx
  exact ⟨x, reach_iff.2 hx⟩

theorem reach_run_cntW_bind {ω : Type} [AddCommMonoid ω] (w : HashInput → ω) {α β : Type}
    (g : OracleComp OracleWorld α) (k : α → OracleComp OracleWorld β) (cache : QueryCache HashSpec)
    (r : (β × ω) × QueryCache HashSpec) :
    Reach ((simulateQ romImpl (cntW w (g >>= k))).run cache) r ↔
      ∃ r1 r2, Reach ((simulateQ romImpl (cntW w g)).run cache) r1 ∧
        Reach ((simulateQ romImpl (cntW w (k r1.1.1))).run r1.2) r2 ∧ r = ((r2.1.1, r1.1.2 + r2.1.2), r2.2) := by
  rw [cntW_bind, simulateQ_bind, StateT.run_bind, reach_bind_iff]
  refine exists_congr fun r1 => ?_
  rw [simulateQ_bind, StateT.run_bind]
  simp only [simulateQ_pure, StateT.run_pure, reach_iff, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨h1, r2, h2, rfl⟩
    exact ⟨r2, h1, h2, rfl⟩
  · rintro ⟨r2, h1, h2, rfl⟩
    exact ⟨h1, r2, h2, rfl⟩

/-- A weight bounded componentwise bounds the counts componentwise. -/
theorem run_cntW_le {α : Type} (w : HashInput → ℕ × ℕ) (hw : ∀ x, (w x).1 ≤ (w x).2)
    (g : OracleComp OracleWorld α) :
    ∀ (cache : QueryCache HashSpec) r, Reach ((simulateQ romImpl (cntW w g)).run cache) r → r.1.2.1 ≤ r.1.2.2 := by
  induction g using OracleComp.inductionOn with
  | pure value =>
      intro cache r hr
      rw [mem_support_run_cntW_pure w value (reach_iff.1 hr)]
      exact le_rfl
  | query_bind input next ih =>
      intro cache r hr
      obtain ⟨r1, r2, h1, h2, rfl⟩ := (reach_run_cntW_bind w _ _ cache r).1 hr
      have e1 := mem_support_run_cntW_query w input (reach_iff.1 h1)
      have e2 := ih r1.1.1 r1.2 r2 h2
      simp only [Prod.fst_add, Prod.snd_add, e1]
      cases input with
      | inl d => simpa [weightOf] using e2
      | inr x => exact Nat.add_le_add (hw x) e2

/-! ### The budget of the multi-user game -/

/-- The short calls, those of each key, and all calls. -/
noncomputable def wK (x : HashInput) : (ℕ × (PublicParameter → ℕ)) × ℕ := (wJ x, 1)

variable [Params] {n : ℕ}

omit [Params] in
theorem counted_eq_run {α : Type} (g : OracleComp OracleWorld α) :
    counted g = (fun r => r.1) <$> (simulateQ romImpl (cntW (fun _ => (1 : ℕ)) g)).run ∅ := by
  rw [counted, countHashQueries_eq_cntW, StateT.run'_eq]

omit [Params] in
theorem run_cntW_one {α : Type} (g : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    (simulateQ romImpl (cntW (fun _ => (1 : ℕ)) g)).run cache =
      (fun r => ((r.1.1, r.1.2.2), r.2)) <$> (simulateQ romImpl (cntW wK g)).run cache := by
  rw [show (fun _ : HashInput => (1 : ℕ)) = fun x => (AddMonoidHom.snd (ℕ × (PublicParameter → ℕ)) ℕ) (wK x)
    from rfl, cntW_hom, simulateQ_map, StateT.run_map]
  rfl

/-- **The multi-user game before the check makes at most `q` hash calls.** -/
theorem prefix_total_le (adversary : Adversary n) (q : ℕ) (hb : HasHashQueryBound adversary q)
    (r : (((Fin n → PublicKey × Seeded.SecretKey) × (Forgery n × QueryLog (SigningSpec n))) ×
      (ℕ × (PublicParameter → ℕ)) × ℕ) × QueryCache HashSpec)
    (hr : Reach ((simulateQ romImpl (cntW wK (prefixMU adversary))).run ∅) r) : r.1.2.2 ≤ q := by
  obtain ⟨c, hc⟩ := reach_nonempty ((simulateQ romImpl (cntW wK ((fun won => (won, r.1.1.2.1.key)) <$>
    checkAt r.1.1.2.1.key r.1.1))).run r.2)
  have hkey : Reach ((simulateQ romImpl (cntW wK (gameKey adversary))).run ∅) ((c.1.1, r.1.2 + c.1.2), c.2) := by
    rw [gameKey_eq, reach_run_cntW_bind]
    exact ⟨r, c, hr, hc, rfl⟩
  have hexp : Reach (experiment adversary) (c.1.1.1, (r.1.2 + c.1.2).2) := by
    rw [experiment_eq, counted_eq_run, run_cntW_one, Functor.map_map, Functor.map_map, reach_map_iff]
    exact ⟨_, hkey, rfl⟩
  have := hb _ (reach_iff.1 hexp)
  simp only [Prod.snd_add] at this
  omega

/-! ### The counts of the check and of the prefix -/

omit [Params] in
theorem run_cntW_hom_le {α : Type} {ω : Type} [AddCommMonoid ω] (w : HashInput → ω) (f : ω →+ ℕ × ℕ)
    (hw : ∀ x, (f (w x)).1 ≤ (f (w x)).2) (g : OracleComp OracleWorld α) (cache : QueryCache HashSpec) r
    (hr : Reach ((simulateQ romImpl (cntW w g)).run cache) r) : (f r.1.2).1 ≤ (f r.1.2).2 := by
  have h := run_cntW_le (fun x => f (w x)) hw g cache ((r.1.1, f r.1.2), r.2) (by
    rw [cntW_hom, simulateQ_map, StateT.run_map, reach_map_iff]
    exact ⟨r, hr, rfl⟩)
  exact h

/-- The short calls of the key `p` against the short calls. -/
noncomputable def homKey (p : PublicParameter) : (ℕ × (PublicParameter → ℕ)) × ℕ →+ ℕ × ℕ :=
  AddMonoidHom.prod (((Pi.evalAddMonoidHom (fun _ : PublicParameter => ℕ) p).comp
      (AddMonoidHom.snd ℕ (PublicParameter → ℕ))).comp (AddMonoidHom.fst _ ℕ))
    ((AddMonoidHom.fst ℕ (PublicParameter → ℕ)).comp (AddMonoidHom.fst _ ℕ))

/-- The short calls against all calls. -/
noncomputable def homShort : (ℕ × (PublicParameter → ℕ)) × ℕ →+ ℕ × ℕ :=
  AddMonoidHom.prod ((AddMonoidHom.fst ℕ (PublicParameter → ℕ)).comp (AddMonoidHom.fst _ ℕ))
    (AddMonoidHom.snd _ ℕ)

omit [Params] in
theorem key_le_short {α : Type} (p : PublicParameter) (g : OracleComp OracleWorld α) (cache : QueryCache HashSpec) r
    (hr : Reach ((simulateQ romImpl (cntW wK g)).run cache) r) : r.1.2.1.2 p ≤ r.1.2.1.1 :=
  run_cntW_hom_le wK (homKey p) (fun x => by simpa [homKey, wK] using wJ_le p x) g cache r hr

omit [Params] in
theorem short_le_total {α : Type} (g : OracleComp OracleWorld α) (cache : QueryCache HashSpec) r
    (hr : Reach ((simulateQ romImpl (cntW wK g)).run cache) r) : r.1.2.1.1 ≤ r.1.2.2 :=
  run_cntW_hom_le wK homShort (fun x => by
    simp only [homShort, wK, wJ, wS, AddMonoidHom.prod_apply, AddMonoidHom.coe_comp, Function.comp_apply,
      AddMonoidHom.coe_fst, AddMonoidHom.coe_snd]
    split_ifs <;> omega) g cache r hr

omit [Params] in
/-- The short calls of a verification, with any weights. -/
theorem verify_wK_le (pk : PublicKey) (message : Message) (signature : Signature) (cache : QueryCache HashSpec) r
    (hr : Reach ((simulateQ romImpl (cntW wK (liftM (Concrete.verify pk message signature :
      OracleComp HashSpec Bool) : OracleComp OracleWorld Bool))).run cache) r) : r.1.2.1.1 ≤ 307 := by
  refine verify_short_le pk message signature cache ((r.1.1, r.1.2.1.1), r.2) ?_
  rw [show wS = fun x => ((AddMonoidHom.fst ℕ (PublicParameter → ℕ)).comp (AddMonoidHom.fst _ ℕ)) (wK x) from rfl,
    cntW_hom, simulateQ_map, StateT.run_map, support_map]
  exact ⟨r, reach_iff.1 hr, rfl⟩

/-! ### One key of the multi-user game -/

theorem gameAtP_eq (adversary : Adversary n) (j : Fin n) :
    gameAtP adversary j = prefixMU adversary >>= fun state =>
      (fun won => (won, (state.1 j).1.parameter)) <$> checkAt j state := by
  simp only [gameAtP, restAtP, restAt, prefixMU, checkAt, bind_assoc, pure_bind, map_bind, map_pure]

/-- The bound of the padded reduction's calls in the multi-user game checking key `j`. -/
noncomputable def keyBound (F : ℕ) (r : (Bool × PublicParameter) × ℕ × (PublicParameter → ℕ)) : ℝ≥0∞ :=
  ((r.2.2 r.1.2 + 2 + max F (r.2.1 - r.2.2 r.1.2) : ℕ) : ℝ≥0∞)

/-- **One key of the multi-user game**: within the budget, the padded reduction's bound is at most
the short calls on the key before the check, plus `F + 309`. -/
theorem mean_keyBound_le (adversary : Adversary n) (q : ℕ) (hb : HasHashQueryBound adversary q) (j : Fin n)
    (F : ℕ) (hF : q + 307 ≤ F) :
    mean (runW wJ (gameAtP adversary j)) (keyBound F) ≤
      mean ((simulateQ romImpl (cntW wK (prefixMU adversary))).run ∅)
        (fun r => ((r.1.2.1.2 ((r.1.1.1 j).1.parameter) : ℕ) : ℝ≥0∞)) + ((F + 309 : ℕ) : ℝ≥0∞) := by
  rw [show wJ = fun x => (AddMonoidHom.fst (ℕ × (PublicParameter → ℕ)) ℕ) (wK x) from rfl, runW_hom, mean_map,
    gameAtP_eq, runW_bind, mean_bind]
  refine (mean_mono_reach _ (G := fun r => ((r.1.2.1.2 ((r.1.1.1 j).1.parameter) : ℕ) : ℝ≥0∞) +
    ((F + 309 : ℕ) : ℝ≥0∞)) fun res hres => ?_).trans ?_
  · rw [mean_map]
    refine (mean_mono_reach _ (G := fun _ => ((res.1.2.1.2 ((res.1.1.1 j).1.parameter) : ℕ) : ℝ≥0∞) +
      ((F + 309 : ℕ) : ℝ≥0∞)) fun c hc => ?_).trans (mean_le_const _ fun _ => le_rfl)
    have hpre := prefix_total_le adversary q hb res hres
    have hpre1 := short_le_total _ _ res hres
    rw [StateT.run'_eq, reach_map_iff] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    rw [show ((fun won => (won, (res.1.1.1 j).1.parameter)) <$> checkAt j res.1.1 :
        OracleComp OracleWorld _) = (fun v => (decide (Valid res.1.1.2.2 j ∧ ¬Contains res.1.1.2.2
          ⟨j, res.1.1.2.1.message, res.1.1.2.1.signature⟩) && v, (res.1.1.1 j).1.parameter)) <$>
            (liftM (Concrete.verify (res.1.1.1 j).1 res.1.1.2.1.message res.1.1.2.1.signature :
              OracleComp HashSpec Bool) : OracleComp OracleWorld Bool) by
      simp only [checkAt, bind_pure_comp, Functor.map_map], cntW_map, simulateQ_map, StateT.run_map,
      reach_map_iff] at hc'
    obtain ⟨c'', hc'', rfl⟩ := hc'
    have hv := verify_wK_le _ _ _ _ c'' hc''
    have hk := key_le_short (res.1.1.1 j).1.parameter _ _ c'' hc''
    simp only [Function.comp_apply, keyBound, AddMonoidHom.coe_fst, Prod.fst_add, Prod.snd_add, Pi.add_apply]
    have key : res.1.2.1.2 ((res.1.1.1 j).1.parameter) + c''.1.2.1.2 ((res.1.1.1 j).1.parameter) + 2 +
        max F (res.1.2.1.1 + c''.1.2.1.1 - (res.1.2.1.2 ((res.1.1.1 j).1.parameter) +
          c''.1.2.1.2 ((res.1.1.1 j).1.parameter))) ≤ res.1.2.1.2 ((res.1.1.1 j).1.parameter) + (F + 309) := by
      omega
    exact_mod_cast key
  · rw [mean_add]
    exact add_le_add le_rfl (mean_le_const _ fun _ => le_rfl)

/-! ### Summing over the keys -/

/-- The pairs of keys sharing their parameter. -/
noncomputable def pairs (P : Fin n → PublicParameter) : ℕ :=
  ((Finset.univ : Finset (Fin n × Fin n)).filter fun ik => ik.1 < ik.2 ∧ P ik.1 = P ik.2).card

omit [Params] in
theorem ofKey_unique {p p' : PublicParameter} {x : HashInput} (h : OfKey p x) (h' : OfKey p' x) : p = p' :=
  bytesLE_injective (h.symm.trans h')

omit [Params] in
/-- An input is of at most one plus the number of pairs of keys. -/
theorem card_ofKey_le (P : Fin n → PublicParameter) (x : HashInput) :
    ((Finset.univ : Finset (Fin n)).filter fun j => OfKey (P j) x).card ≤ 1 + pairs P := by
  set S := (Finset.univ : Finset (Fin n)).filter fun j => OfKey (P j) x with hS
  rcases S.eq_empty_or_nonempty with h | h
  · rw [h, Finset.card_empty]; omega
  set m := S.min' h with hm
  have hmS : m ∈ S := S.min'_mem h
  have hinj : (S.erase m).card ≤ pairs P := by
    refine Finset.card_le_card_of_injOn (fun k => (m, k)) (fun k hk => ?_) (fun a _ b _ hab => ?_)
    · have hkS := Finset.mem_of_mem_erase hk
      have hne := Finset.ne_of_mem_erase hk
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      refine ⟨lt_of_le_of_ne (S.min'_le k hkS) (Ne.symm hne), ?_⟩
      rw [hS, Finset.mem_filter] at hmS hkS
      exact ofKey_unique hmS.2 hkS.2
    · exact (Prod.ext_iff.1 hab).2
  have := Finset.card_erase_add_one hmS
  omega

omit [Params] in
theorem sum_wPi_le (P : Fin n → PublicParameter) (x : HashInput) :
    ∑ j, wPi x (P j) ≤ wS x * (1 + pairs P) := by
  unfold wPi wS
  by_cases hs : IsShort x
  · simp only [hs, true_and, ite_true, one_mul]
    rw [Finset.sum_boole]
    exact card_ofKey_le P x
  · simp [hs]

/-- The calls of every key against the short calls. -/
noncomputable def homSum (P : Fin n → PublicParameter) : (ℕ × (PublicParameter → ℕ)) × ℕ →+ ℕ × ℕ :=
  AddMonoidHom.prod (∑ j, ((Pi.evalAddMonoidHom (fun _ : PublicParameter => ℕ) (P j)).comp
      (AddMonoidHom.snd ℕ (PublicParameter → ℕ))).comp (AddMonoidHom.fst _ ℕ))
    ((1 + pairs P) • (AddMonoidHom.fst ℕ (PublicParameter → ℕ)).comp (AddMonoidHom.fst _ ℕ))

omit [Params] in
theorem sum_key_le {α : Type} (g : OracleComp OracleWorld α) (cache : QueryCache HashSpec) r
    (hr : Reach ((simulateQ romImpl (cntW wK g)).run cache) r) (P : Fin n → PublicParameter) :
    ∑ j, r.1.2.1.2 (P j) ≤ r.1.2.1.1 * (1 + pairs P) := by
  have h := run_cntW_hom_le wK (homSum P) (fun x => by
    simpa [homSum, wK, wJ, AddMonoidHom.finsetSum_apply, mul_comm] using sum_wPi_le P x) g cache r hr
  simpa [homSum, AddMonoidHom.finsetSum_apply, mul_comm] using h

omit [Params] in
theorem mean_finset_sum' {α ι : Type} (mx : ProbComp α) (s : Finset ι) (G : ι → α → ℝ≥0∞) :
    mean mx (fun a => ∑ b ∈ s, G b a) = ∑ b ∈ s, mean mx (G b) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      unfold mean
      simp
  | insert b s hb ih =>
      simp only [Finset.sum_insert hb]
      rw [mean_add, ih]

/-- **The calls of the keys before the check, summed over the keys.** -/
theorem sum_prefix_le (adversary : Adversary n) (q : ℕ) (hb : HasHashQueryBound adversary q) :
    ∑ j, mean ((simulateQ romImpl (cntW wK (prefixMU adversary))).run ∅)
        (fun r => ((r.1.2.1.2 ((r.1.1.1 j).1.parameter) : ℕ) : ℝ≥0∞)) ≤
      q * (1 + mean ((simulateQ romImpl (cntW wK (prefixMU adversary))).run ∅)
        (fun r => ((pairs fun i => (r.1.1.1 i).1.parameter : ℕ) : ℝ≥0∞))) := by
  rw [← mean_finset_sum', show (1 : ℝ≥0∞) = mean ((simulateQ romImpl (cntW wK
    (prefixMU adversary))).run ∅) (fun _ => 1) from (Det.mean_one _).symm, ← mean_add, ← mean_const_mul]
  refine mean_mono_reach _ fun r hr => ?_
  have h1 := sum_key_le _ _ r hr fun i => (r.1.1.1 i).1.parameter
  have h2 := short_le_total _ _ r hr
  have h3 := prefix_total_le adversary q hb r hr
  have key : ∑ j, r.1.2.1.2 ((r.1.1.1 j).1.parameter) ≤ q * (1 + pairs fun i => (r.1.1.1 i).1.parameter) :=
    h1.trans (Nat.mul_le_mul_right _ (h2.trans h3))
  simp only [← Nat.cast_sum]
  exact_mod_cast key

end Sphincs.Security.Multi
