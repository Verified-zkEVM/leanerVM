import Sphincs.MultiSum

/-! **The padding in the seed-free game.** Every path of the padded adversary makes at least `F`
short calls off its key, whatever the oracle answers (`AtLeast`). Memoizing and internalizing keep
those calls, and the cost game records each of them in the trace, so a finished capped seed-free
run spends at least `F` units of budget off the key: its calls charged to the key are at most its
trace cost minus `F` (`keyCharged_add_le`). -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.Multi

open MultiEager Completeness Internalize Short Eager SeedCoupling KeyOnly HiddenCost GraphView Stop HiddenDebt

set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-! ### Paths with many selected queries -/

section Paths

variable {ι : Type} {spec : OracleSpec ι}

/-- Every path makes at least `F` selected queries. -/
def AtLeast (sel : ι → Prop) (F : ℕ) {α : Type} (M : OracleComp spec α) : Prop :=
  ∀ r ∈ support (SphincsBase.QueryCap.counted sel M), F ≤ r.2

theorem AtLeast.pure_iff (sel : ι → Prop) (F : ℕ) {α : Type} (v : α) :
    AtLeast sel F (pure v : OracleComp spec α) ↔ F = 0 := by
  simp [AtLeast, SphincsBase.QueryCap.counted_pure]

theorem AtLeast.query_bind {sel : ι → Prop} {F : ℕ} {α : Type} {t : ι} {next : spec.Range t → OracleComp spec α}
    (h : AtLeast sel F (liftM (spec.query t) >>= next)) (a : spec.Range t) :
    AtLeast sel (F - if sel t then 1 else 0) (next a) := by
  intro r hr
  have := h ((r.1, (if sel t then 1 else 0) + r.2)) (by
    rw [SphincsBase.QueryCap.counted_query_bind]
    simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff, exists_prop, support_query,
      Set.mem_univ, true_and]
    exact ⟨a, r, hr, rfl⟩)
  simp only at this
  omega

theorem AtLeast.bind_left {sel : ι → Prop} {F : ℕ} {α β : Type} {M : OracleComp spec α}
    {k : α → OracleComp spec β} (h : AtLeast sel F M) : AtLeast sel F (M >>= k) := by
  intro r hr
  rw [SphincsBase.QueryCap.counted_bind] at hr
  simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff, exists_prop] at hr
  obtain ⟨r1, hr1, r2, -, rfl⟩ := hr
  exact (h r1 hr1).trans (Nat.le_add_right _ _)

end Paths

section Pad

theorem counted_counted {ι : Type} {spec : OracleSpec ι} (sel : ι → Prop) [DecidablePred sel] {α : Type}
    (M : OracleComp spec α) :
    ∀ r ∈ support (SphincsBase.QueryCap.counted sel (SphincsBase.QueryCap.counted sel M)), r.2 = r.1.2 := by
  induction M using OracleComp.inductionOn with
  | pure value =>
      intro r hr
      simp [SphincsBase.QueryCap.counted_pure] at hr
      simp [hr]
  | query_bind t next ih =>
      intro r hr
      rw [SphincsBase.QueryCap.counted_query_bind, SphincsBase.QueryCap.counted_query_bind] at hr
      simp only [support_bind, Set.mem_iUnion, exists_prop, bind_pure_comp, support_map, Set.mem_image,
        SphincsBase.QueryCap.counted_map] at hr
      obtain ⟨a, -, r1, ⟨r0, hr0, rfl⟩, rfl⟩ := hr
      simp only [ih a r0 hr0]

theorem counted_padW (p : PublicParameter) :
    ∀ (k : ℕ), ∀ r ∈ support (SphincsBase.QueryCap.counted (selFree p) (liftWorld (padW p k))), r.2 = k
  | 0, r, hr => by
      simp [padW, liftWorld, SphincsBase.QueryCap.counted_pure] at hr
      simp [hr]
  | k + 1, r, hr => by
      rw [padW, liftWorld, simulateQ_bind, simulateQ_spec_query, ← liftWorld] at hr
      change r ∈ support (SphincsBase.QueryCap.counted (selFree p)
        ((liftM (AdvSpec.query (.inl (.inr (padInput p)))) : OracleComp AdvSpec _) >>= fun _ =>
          liftWorld (padW p k))) at hr
      rw [SphincsBase.QueryCap.counted_query_bind] at hr
      simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff, exists_prop] at hr
      obtain ⟨a, -, r1, hr1, rfl⟩ := hr
      have hsel : selFree p (.inl (.inr (padInput p))) := ⟨padInput_short p, padInput_not_ofKey p⟩
      simp only [hsel, ite_true, counted_padW p k r1 hr1]
      omega

variable [Params]

omit [Params] in
/-- **Every path of the padded adversary makes at least `F` short calls off its key.** -/
theorem atLeast_padAdv (F : ℕ) (Y : Security.Adversary) (pk : PublicKey) :
    AtLeast (selFree pk.parameter) F ((padAdv F Y).main pk) := by
  intro r hr
  simp only [padAdv, SphincsBase.QueryCap.counted_bind, SphincsBase.QueryCap.counted_pure, support_bind,
    Set.mem_iUnion, support_pure, Set.mem_singleton_iff, exists_prop] at hr
  obtain ⟨r1, hr1, r2, ⟨r3, hr3, r4, rfl, rfl⟩, rfl⟩ := hr
  have h1 := counted_counted _ _ r1 hr1
  have h3 := counted_padW _ _ r3 hr3
  simp only [h3, add_zero]
  omega

end Pad

/-! ### Memoizing and internalizing keep the calls -/

section Keep

variable {sel : AdvSpec.Domain → Prop}

theorem counted_query_map_count {ι : Type} {spec : OracleSpec ι} {sel : ι → Prop} {β : Type} (t : ι)
    (f : spec.Range t → β) r
    (hr : r ∈ support (SphincsBase.QueryCap.counted sel (f <$> (liftM (spec.query t) : OracleComp spec _)))) :
    r.2 = if sel t then 1 else 0 := by
  rw [SphincsBase.QueryCap.counted_map, support_map] at hr
  obtain ⟨r0, hr0, rfl⟩ := hr
  rw [show (liftM (spec.query t) : OracleComp spec _) = liftM (spec.query t) >>= fun a => pure a
    from (bind_pure _).symm, SphincsBase.QueryCap.counted_query_bind] at hr0
  simp [SphincsBase.QueryCap.counted_pure] at hr0
  obtain ⟨a, rfl⟩ := hr0
  simp

theorem mem_counted_query_bind {α : Type} (t : AdvSpec.Domain) (next : AdvSpec.Range t → OracleComp AdvSpec α)
    (a : AdvSpec.Range t) r (hr : r ∈ support (SphincsBase.QueryCap.counted sel (next a))) :
    (r.1, (if sel t then 1 else 0) + r.2) ∈
      support (SphincsBase.QueryCap.counted sel ((liftM (AdvSpec.query t) : OracleComp AdvSpec _) >>= next)) := by
  rw [SphincsBase.QueryCap.counted_query_bind]
  simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff, exists_prop, support_query,
    Set.mem_univ, true_and]
  exact ⟨a, r, hr, rfl⟩

/-- **Memoizing keeps the counted calls**, the signing requests being uncounted. -/
theorem dom_memo (hsel : ∀ m, ¬sel (.inr m)) {α : Type} (M : OracleComp AdvSpec α) :
    ∀ (record : Memo.Record) r', r' ∈ support (SphincsBase.QueryCap.counted sel
        ((simulateQ Memo.memoImpl M).run record)) →
      ∃ r ∈ support (SphincsBase.QueryCap.counted sel M), r.2 ≤ r'.2 := by
  induction M using OracleComp.inductionOn with
  | pure value =>
      intro record r' hr'
      simp [SphincsBase.QueryCap.counted_pure] at hr'
      exact ⟨(value, 0), by simp [SphincsBase.QueryCap.counted_pure], by simp [hr']⟩
  | query_bind t next ih =>
      intro record r' hr'
      rw [Memo.memo_run_query_bind, SphincsBase.QueryCap.counted_bind] at hr'
      simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff, exists_prop] at hr'
      obtain ⟨c1, hc1, c2, hc2, rfl⟩ := hr'
      obtain ⟨r0, hr0, hle⟩ := ih c1.1.1 c1.1.2 c2 hc2
      refine ⟨_, mem_counted_query_bind t next c1.1.1 r0 hr0, ?_⟩
      have hc : (if sel t then 1 else 0) ≤ c1.2 := by
        rcases t with q | m
        · rw [Memo.memoImpl_world] at hc1
          rw [counted_query_map_count _ _ c1 hc1]
        · simp [hsel m]
      simp only
      omega

/-- **Internalizing keeps the counted calls**, if only short calls are counted. -/
theorem dom_internal (hlong : ∀ x, ¬IsShort x → ¬sel (.inl (.inr x)))
    {α : Type} (M : OracleComp AdvSpec α) :
    ∀ (cache : QueryCache HashSpec) r', r' ∈ support (SphincsBase.QueryCap.counted sel
        ((simulateQ internalImpl M).run cache)) →
      ∃ r ∈ support (SphincsBase.QueryCap.counted sel M), r.2 ≤ r'.2 := by
  induction M using OracleComp.inductionOn with
  | pure value =>
      intro cache r' hr'
      simp [SphincsBase.QueryCap.counted_pure] at hr'
      exact ⟨(value, 0), by simp [SphincsBase.QueryCap.counted_pure], by simp [hr']⟩
  | query_bind t next ih =>
      intro cache r' hr'
      rw [Memo.internal_run_query_bind, SphincsBase.QueryCap.counted_bind] at hr'
      simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff, exists_prop] at hr'
      obtain ⟨c1, hc1, c2, hc2, rfl⟩ := hr'
      obtain ⟨r0, hr0, hle⟩ := ih c1.1.1 c1.1.2 c2 hc2
      refine ⟨_, mem_counted_query_bind t next c1.1.1 r0 hr0, ?_⟩
      have hc : (if sel t then 1 else 0) ≤ c1.2 := by
        rcases t with (d | x) | m
        · rw [Memo.internal_forward_run _ rfl] at hc1
          rw [counted_query_map_count _ _ c1 hc1]
        · by_cases hx : IsShort x
          · rw [Memo.internal_forward_run _ (by simp [internalImpl, hx])] at hc1
            rw [counted_query_map_count _ _ c1 hc1]
          · simp [hlong x hx]
        · rw [Memo.internal_forward_run _ rfl] at hc1
          rw [counted_query_map_count _ _ c1 hc1]
      simp only
      omega

theorem atLeast_of_dom {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {sel : ι → Prop}
    {sel' : ι' → Prop} {F : ℕ} {α β : Type}
    {M : OracleComp spec α} {M' : OracleComp spec' β} (h : AtLeast sel F M)
    (hdom : ∀ r' ∈ support (SphincsBase.QueryCap.counted sel' M'),
      ∃ r ∈ support (SphincsBase.QueryCap.counted sel M), r.2 ≤ r'.2) : AtLeast sel' F M' := by
  intro r' hr'
  obtain ⟨r, hr, hle⟩ := hdom r' hr'
  exact (h r hr).trans hle

theorem atLeast_map {ι : Type} {spec : OracleSpec ι} {sel : ι → Prop} {F : ℕ} {α β : Type}
    {M : OracleComp spec α} (f : α → β) (h : AtLeast sel F M) : AtLeast sel F (f <$> M) := by
  intro r hr
  rw [SphincsBase.QueryCap.counted_map, support_map] at hr
  obtain ⟨r0, hr0, rfl⟩ := hr
  exact h r0 hr0

/-- **The adversary of the seed-free game keeps the padding.** -/
theorem atLeast_internalize_memo (F : ℕ) (Y : Security.Adversary) (pk : PublicKey) :
    AtLeast (selFree pk.parameter) F ((internalize (Memo.memoAdv (padAdv F Y))).main pk) := by
  have hm : AtLeast (selFree pk.parameter) F ((Memo.memoAdv (padAdv F Y)).main pk) := by
    change AtLeast _ F ((simulateQ Memo.memoImpl ((padAdv F Y).main pk)).run' Memo.emptyRecord)
    rw [StateT.run'_eq]
    exact atLeast_map _ (atLeast_of_dom (atLeast_padAdv F Y pk)
      (dom_memo (fun m h => h) _ Memo.emptyRecord))
  change AtLeast _ F ((simulateQ internalImpl ((Memo.memoAdv (padAdv F Y)).main pk)).run' ∅)
  rw [StateT.run'_eq]
  exact atLeast_map _ (atLeast_of_dom hm (dom_internal (fun x hx h => hx h.1) _ ∅))

/-! ### The cost game records the calls -/

/-- The short calls off the key `p` in the cost game. -/
def selCost (p : PublicParameter) : CostSpec.Domain → Prop
  | .inl (.inr (.inl x)) => IsShort x ∧ ¬OfKey p x
  | _ => False

/-- The short calls off the key `p` in a trace. -/
noncomputable def freeCount (p : PublicParameter) (entries : List (Entry HashInput)) : ℕ :=
  (entries.map fun e => match e with
    | .inl x => if IsShort x ∧ ¬OfKey p x then 1 else 0
    | .inr _ => 0).sum

theorem freeCount_append (p : PublicParameter) (a b : List (Entry HashInput)) :
    freeCount p (a ++ b) = freeCount p a + freeCount p b := by
  simp [freeCount]

theorem freeCount_recorded (p : PublicParameter) (i : CostSpec.Domain) :
    freeCount p (recorded i) = if selCost p i then 1 else 0 := by
  rcases i with (d | (x | c)) | a <;> simp [freeCount, recorded, selCost]

/-- **A finished capped run records the selected calls of its path.** -/
theorem freeCount_cap (p : PublicParameter) (f : HashInput → HashOutput) (table : HiddenGraph.Table) {α : Type}
    (C : OracleComp CostSpec α) :
    ∀ (F M : ℕ), AtLeast (selCost p) F C → ∀ x, Reach (costRun f table (cap C M)) x → x.1.isSome →
      F ≤ freeCount p x.2 := by
  induction C using OracleComp.inductionOn with
  | pure value =>
      intro F M hF x hx _
      rw [AtLeast.pure_iff] at hF
      omega
  | query_bind i next ih =>
      intro F M hF x hx hsome
      rw [cap_query_bind'] at hx
      split at hx
      · rw [costRun_query_bind, reach_bind_iff] at hx
        obtain ⟨a, -, hx⟩ := hx
        rw [reach_map_iff] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        have h := ih a _ _ (hF.query_bind a) y hy hsome
        rw [freeCount_append, freeCount_recorded]
        omega
      · rw [costRun_pure, reach_iff, support_pure, Set.mem_singleton_iff] at hx
        subst hx
        simp at hsome

theorem AtLeast.query_bind_of {ι : Type} {spec : OracleSpec ι} {sel : ι → Prop} {F : ℕ} {α : Type} {t : ι}
    {next : spec.Range t → OracleComp spec α} (h : ∀ a, AtLeast sel F (next a)) :
    AtLeast sel F (liftM (spec.query t) >>= next) := by
  intro r hr
  rw [SphincsBase.QueryCap.counted_query_bind] at hr
  simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff, exists_prop] at hr
  obtain ⟨a, -, r1, hr1, rfl⟩ := hr
  exact (h a r1 hr1).trans (Nat.le_add_left _ _)

variable [Params]

/-- **The cost interaction keeps the counted calls.** -/
theorem dom_costInteraction (p p' : PublicParameter) (data : PublicData) {α : Type} (N : OracleComp AdvSpec α) :
    ∀ r', r' ∈ support (SphincsBase.QueryCap.counted (selCost p) ((simulateQ (costInteraction p' data) N).run)) →
      ∃ r ∈ support (SphincsBase.QueryCap.counted (selFree p) N), r.2 ≤ r'.2 := by
  induction N using OracleComp.inductionOn with
  | pure value =>
      intro r' hr'
      simp [SphincsBase.QueryCap.counted_pure] at hr'
      exact ⟨(value, 0), by simp [SphincsBase.QueryCap.counted_pure], by simp [hr']⟩
  | query_bind t next ih =>
      intro r' hr'
      rw [simulateQ_bind, WriterT.run_bind, simulateQ_spec_query, SphincsBase.QueryCap.counted_bind] at hr'
      simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff, exists_prop] at hr'
      obtain ⟨c1, hc1, c2, hc2, rfl⟩ := hr'
      rw [SphincsBase.QueryCap.counted_map, support_map] at hc2
      obtain ⟨c3, hc3, rfl⟩ := hc2
      obtain ⟨r0, hr0, hle⟩ := ih c1.1.1 c3 hc3
      refine ⟨_, mem_counted_query_bind t next c1.1.1 r0 hr0, ?_⟩
      have hc : (if selFree p t then 1 else 0) ≤ c1.2 := by
        rcases t with (d | x) | m
        · have hrun : (costInteraction p' data (.inl (.inl d))).run =
              (fun a => (a, ∅)) <$> (liftM (CostSpec.query (.inl (.inl d))) : OracleComp CostSpec _) := rfl
          rw [hrun] at hc1
          rw [counted_query_map_count _ _ c1 hc1]
          simp [selFree, selCost]
        · have hrun : (costInteraction p' data (.inl (.inr x))).run =
              (fun a => (a, ∅)) <$> (liftM (CostSpec.query (.inl (.inr (.inl x)))) : OracleComp CostSpec _) := rfl
          rw [hrun] at hc1
          rw [counted_query_map_count _ _ c1 hc1]
          simp [selFree, selCost]
        · simp [selFree]
      simp only
      omega

/-- **Every path of the cost game makes the padded number of short calls off the key.** -/
theorem atLeast_costGame (p : PublicParameter) (data : PublicData) (X : Security.Adversary) (F : ℕ)
    (hX : AtLeast (selFree p) F (X.main ⟨data.root, p⟩)) : AtLeast (selCost p) F (costGame p data X) := by
  unfold costGame HiddenCost.tick costRest
  refine AtLeast.query_bind_of fun _ => AtLeast.bind_left ?_
  exact atLeast_of_dom hX (dom_costInteraction p p data _)

omit [Params] in
theorem charged_add_free_le (p : PublicParameter) (entries : List (Entry HashInput)) :
    chargedCost (fun x => ¬OfKey p x) entries + freeCount p entries ≤ traceCost entries := by
  induction entries with
  | nil => simp [chargedCost, freeCount, traceCost]
  | cons e es ih =>
      simp only [chargedCost, freeCount, traceCost, List.map_cons, List.sum_cons] at ih ⊢
      have he : chargedEntry (fun x => ¬OfKey p x) e + (match e with
          | .inl x => if IsShort x ∧ ¬OfKey p x then 1 else 0
          | .inr _ => 0) ≤ entryCost e := by
        cases e with
        | inl x => by_cases h1 : OfKey p x <;> by_cases h2 : IsShort x <;> simp [chargedEntry, entryCost, h1, h2]
        | inr a => simp [chargedEntry, entryCost]
      omega

open ForsPotential HiddenBridge SeedModel _root_.Sphincs.Security.Graph Assembly Reduce HiddenGraph in
/-- **A finished seed-free run of the padded adversary spends `F` off its key.** -/
theorem keyCharged_add_le (F M : ℕ) (Y : Security.Adversary) (parameterOutput : HashOutput) x
    (hx : Reach (seedFreeFrom (internalize (Memo.memoAdv (padAdv F Y))) M parameterOutput) x)
    (hsome : x.1.isSome) :
    chargedCost (fun y => ¬OfKey (truncateHash parameterOutput) y) x.2 + F ≤ traceCost x.2 := by
  unfold seedFreeFrom at hx
  simp only [reach_bind_iff] at hx
  obtain ⟨fixed, -, highs, -, remaining, -, outsideTable, -, table, -, hx⟩ := hx
  rw [hiddenRun_eq] at hx
  unfold sampleProgram at hx
  set data := GraphView.publicData
    (labelsOf (splitMaterial parameterOutput highs remaining fixed) (splitAnswers highs remaining fixed)) with hdata
  have hat := atLeast_costGame (truncateHash parameterOutput) data (internalize (Memo.memoAdv (padAdv F Y))) F
    (atLeast_internalize_memo F Y ⟨data.root, truncateHash parameterOutput⟩)
  have h := freeCount_cap (truncateHash parameterOutput) _ table _ F M hat x hx hsome
  have h2 := charged_add_free_le (truncateHash parameterOutput) x.2
  omega

open ForsPotential Reduce in
/-- **The padding in mean**: the key's capped calls of the seed-free game and `F` per finished run
are at most its hash calls. -/
theorem mean_keyCharged_add_le (F M : ℕ) (Y : Security.Adversary) :
    mean ($ᵗ HashOutput) (fun parameterOutput => mean (seedFreeFrom (internalize (Memo.memoAdv (padAdv F Y))) M
        parameterOutput) fun x => min (M : ℝ≥0∞) (keyCharged parameterOutput x.2)) +
      F * Pr{let x ← seedFreeExperiment (internalize (Memo.memoAdv (padAdv F Y))) M}[x.1.isSome] ≤
      mean (seedFreeExperiment (internalize (Memo.memoAdv (padAdv F Y))) M) (fun x => (traceCost x.2 : ℝ≥0∞)) := by
  rw [← mean_indicator, ← mean_const_mul, mean_seedFree _ _ (fun x => F * if x.1.isSome then 1 else 0),
    mean_seedFree, ← mean_add]
  refine mean_mono _ fun parameterOutput => ?_
  rw [← mean_add]
  refine mean_mono_reach _ fun x hx => ?_
  by_cases hs : x.1.isSome
  · have h := keyCharged_add_le F M Y parameterOutput x hx hs
    simp only [hs, ite_true, mul_one]
    calc min (M : ℝ≥0∞) (keyCharged parameterOutput x.2) + F ≤ (keyCharged parameterOutput x.2) + F :=
          add_le_add (min_le_right _ _) le_rfl
      _ ≤ _ := by unfold keyCharged; exact_mod_cast h
  · simp only [hs, Bool.false_eq_true, ite_false, mul_zero, add_zero]
    refine (min_le_right _ _).trans ?_
    unfold keyCharged
    exact_mod_cast chargedCost_le _ _

end Keep

end Sphincs.Security.Multi
