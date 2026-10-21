import Sphincs.MultiCount

/-! **Padding a reduction to the calls of its key.** The single-key experiment counts every hash
call of the adversary. The padded adversary `padAdv F Y` counts the short calls of `Y` off its key
(`selFree`) and adds `F` minus that many calls on a fixed short input off its key (`padInput`): the
padded game makes `F` such calls plus at most two of key generation, whatever `Y` does, so its
short calls are those of `Y` on its key plus `F` plus at most two. The calls off the key are free
for the small route, which pays only the calls of its key. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.Multi

open MultiEager Completeness Internalize Short Eager SeedCoupling KeyOnly

set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-! ### Reachable outcomes -/

/-- The outcome is reachable: a wrapper of the support that whnf does not unfold, for statements
about the outcomes of whole games. -/
@[irreducible] def Reach {α : Type} (mx : ProbComp α) (r : α) : Prop := r ∈ support mx

theorem reach_iff {α : Type} {mx : ProbComp α} {r : α} : Reach mx r ↔ r ∈ support mx := by
  unfold Reach; rfl

/-- `reach_iff` with the support taken over `OracleComp unifSpec`, as the support lemmas of
`OracleComp` give it. -/
theorem reach_iff' {α : Type} {mx : OracleComp unifSpec α} {r : α} :
    Reach mx r ↔ r ∈ support (m := OracleComp unifSpec) mx := by
  unfold Reach; rfl

theorem reach_congr {α : Type} {mx my : ProbComp α} (h : mx =ᵈ my) (r : α) : Reach mx r ↔ Reach my r := by
  rw [reach_iff, reach_iff, OracleComp.support_eq_of_evalDistEq h]

theorem reach_map_iff {α β : Type} (mx : ProbComp α) (f : α → β) (y : β) :
    Reach (f <$> mx) y ↔ ∃ x, Reach mx x ∧ f x = y := by
  simp only [reach_iff, support_map, Set.mem_image]

theorem mean_mono_reach {α : Type} (mx : ProbComp α) {F G : α → ℝ≥0∞} (h : ∀ a, Reach mx a → F a ≤ G a) :
    mean mx F ≤ mean mx G :=
  mean_mono_support mx fun a ha => h a (reach_iff.2 ha)

/-! ### The weights -/

/-- The short calls. -/
noncomputable def wS (x : HashInput) : ℕ := if IsShort x then 1 else 0

/-- The short calls of each key. -/
noncomputable def wPi (x : HashInput) : PublicParameter → ℕ := fun p => if IsShort x ∧ OfKey p x then 1 else 0

/-- The short calls, and those of each key. -/
noncomputable def wJ (x : HashInput) : ℕ × (PublicParameter → ℕ) := (wS x, wPi x)

theorem wJ_ofKey {p : PublicParameter} {x : HashInput} (h : OfKey p x) : (wJ x).1 = (wJ x).2 p := by
  simp [wJ, wS, wPi, h]

theorem wJ_le (p : PublicParameter) (x : HashInput) : (wJ x).2 p ≤ (wJ x).1 := by
  unfold wJ wS wPi
  by_cases h1 : IsShort x <;> by_cases h2 : OfKey p x <;> simp [h1, h2]

/-! ### A query that is never made -/

/-- The computation never queries `x`. -/
def Avoids {α : Type} (x : HashInput) (oa : OracleComp OracleWorld α) : Prop :=
  oa.IsQueryBoundP (fun query => query = .inr x) 0

theorem Avoids.of_onlyK {p : PublicParameter} {x : HashInput} (hx : ¬OfKey p x) {α : Type}
    {oa : OracleComp HashSpec α} (h : OnlyK p oa) : Avoids x (liftM oa : OracleComp OracleWorld α) := by
  induction oa using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind input next ih =>
      rw [OnlyK, isQueryBoundP_query_bind_iff] at h
      rw [liftM_bind]
      change (liftM (OracleWorld.query (.inr input)) >>= fun answer => (liftM (next answer) :
        OracleComp OracleWorld α)).IsQueryBoundP _ 0
      rw [isQueryBoundP_query_bind_iff]
      have hin : OfKey p input := by
        rcases h.1 with h1 | h1
        · exact not_not.mp h1
        · omega
      refine ⟨Or.inl fun heq => hx (by cases heq; exact hin), fun answer => ?_⟩
      have := ih answer (by have := h.2 answer; split at this <;> simpa [OnlyK] using this)
      simpa [Avoids] using this

theorem Avoids.bind {x : HashInput} {α β : Type} {oa : OracleComp OracleWorld α}
    {next : α → OracleComp OracleWorld β} (h : Avoids x oa) (hnext : ∀ value, Avoids x (next value)) :
    Avoids x (oa >>= next) := by
  have := isQueryBoundP_bind (n := 0) (m := 0) h (fun value _ => hnext value)
  simpa [Avoids] using this

theorem Avoids.cntW {ω : Type} [AddCommMonoid ω] (w : HashInput → ω) {x : HashInput} {α : Type}
    {oa : OracleComp OracleWorld α} (h : Avoids x oa) : Avoids x (cntW w oa) := by
  induction oa using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind input next ih =>
      rw [Avoids, isQueryBoundP_query_bind_iff] at h
      rw [cntW_query_bind, Avoids, isQueryBoundP_query_bind_iff]
      refine ⟨h.1, fun answer => ?_⟩
      have hnext : Avoids x (next answer) := by
        have := h.2 answer
        split at this <;> simpa [Avoids] using this
      have := Avoids.bind (ih answer hnext) (fun result => isQueryBoundP_pure _ (result.1,
        weightOf w input + result.2) 0)
      simpa [Avoids] using this

/-- **A cached answer the computation never reads changes nothing but the final cache.** -/
theorem run'_cacheQuery_avoids {α : Type} (x : HashInput) (a : HashOutput) (oa : OracleComp OracleWorld α)
    (h : Avoids x oa) (cache : QueryCache HashSpec) :
    (simulateQ romImpl oa).run' (cache.cacheQuery x a) =ᵈ (simulateQ romImpl oa).run' cache := by
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure value => exact EvalDistEq.refl _
  | query_bind input next ih =>
      rw [Avoids, isQueryBoundP_query_bind_iff] at h
      have hnext : ∀ answer, Avoids x (next answer) := fun answer => by
        have := h.2 answer
        split at this <;> simpa [Avoids] using this
      have hne : input ≠ .inr x := by
        rcases h.1 with h1 | h1
        · exact h1
        · omega
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, map_bind]
      cases input with
      | inl draw =>
          change (unifFwdImpl HashSpec draw).run (cache.cacheQuery x a) >>= _ =ᵈ
            (unifFwdImpl HashSpec draw).run cache >>= _
          have hrun : ∀ c : QueryCache HashSpec, (unifFwdImpl HashSpec draw).run c =
              (fun answer => (answer, c)) <$> (liftM (unifSpec.query draw) : ProbComp (Fin (draw + 1))) :=
            fun c => by
              simpa using (unifFwdImpl.simulateQ_run (hashSpec := HashSpec)
                (liftM (unifSpec.query draw) : ProbComp (Fin (draw + 1))) c)
          rw [hrun, hrun]
          refine (evalDist_map_bind' _ _ _).trans (EvalDistEq.trans ?_ (evalDist_map_bind' _ _ _).symm)
          refine EvalDistEq.bind_right _ fun answer => ?_
          have := ih answer (hnext answer) cache
          simpa [StateT.run'_eq] using this
      | inr bytes =>
          have hb : bytes ≠ x := fun heq => hne (heq ▸ rfl)
          change (randomOracle (spec := HashSpec) bytes).run (cache.cacheQuery x a) >>= _ =ᵈ
            (randomOracle (spec := HashSpec) bytes).run cache >>= _
          have hc : (cache.cacheQuery x a) bytes = cache bytes := QueryCache.cacheQuery_of_ne _ _ hb
          cases hcb : cache bytes with
          | some answer =>
              rw [QueryImpl.withCaching_run_some _ (hc.trans hcb), QueryImpl.withCaching_run_some _ hcb,
                pure_bind, pure_bind]
              have := ih answer (hnext answer) cache
              simpa [StateT.run'_eq] using this
          | none =>
              rw [QueryImpl.withCaching_run_none _ (hc.trans hcb), QueryImpl.withCaching_run_none _ hcb]
              refine (evalDist_map_bind' _ _ _).trans (EvalDistEq.trans ?_ (evalDist_map_bind' _ _ _).symm)
              refine EvalDistEq.bind_right _ fun answer => ?_
              have hcomm : (cache.cacheQuery x a).cacheQuery bytes answer =
                  (cache.cacheQuery bytes answer).cacheQuery x a := by
                refine QueryCache.ext fun y => ?_
                by_cases hy : y = bytes
                · subst hy
                  rw [QueryCache.cacheQuery_self, QueryCache.cacheQuery_of_ne _ _ hb, QueryCache.cacheQuery_self]
                · by_cases hyx : y = x
                  · subst hyx
                    rw [QueryCache.cacheQuery_of_ne _ _ hy, QueryCache.cacheQuery_self, QueryCache.cacheQuery_self]
                  · rw [QueryCache.cacheQuery_of_ne _ _ hy, QueryCache.cacheQuery_of_ne _ _ hyx,
                      QueryCache.cacheQuery_of_ne _ _ hyx, QueryCache.cacheQuery_of_ne _ _ hy]
              rw [hcomm]
              have := ih answer (hnext answer) (cache.cacheQuery bytes answer)
              simpa [StateT.run'_eq] using this

/-! ### The padded adversary -/

/-- The padding input of the key with parameter `p`: off the key. -/
def padInput (p : PublicParameter) : HashInput := bytesLE 16 (p + (1 : PublicParameter))

theorem padInput_not_ofKey (p : PublicParameter) : ¬OfKey p (padInput p) := by
  intro h
  unfold OfKey padInput at h
  rw [List.take_of_length_le (by rw [bytesLE_length])] at h
  have h1 := bytesLE_injective h
  have h2 : (1 : PublicParameter) = 0 := by simpa using congrArg (fun z => z - p) h1
  exact absurd h2 (by decide)

theorem padInput_short (p : PublicParameter) : IsShort (padInput p) := by
  simp [IsShort, bound, padInput, bytesLE_length]

/-- The calls of the adversary counted off the key: short calls not of the key. -/
def selFree (p : PublicParameter) : AdvSpec.Domain → Prop
  | .inl (.inr x) => IsShort x ∧ ¬OfKey p x
  | _ => False

/-- `k` calls on the padding input. -/
noncomputable def padW (p : PublicParameter) : ℕ → OracleComp OracleWorld Unit
  | 0 => pure ()
  | k + 1 => liftM (OracleWorld.query (.inr (padInput p))) >>= fun _ => padW p k

variable [Params]

/-- **The padded adversary**: `Y`, its short calls off the key counted, then `F` minus that many
calls on the padding input. -/
noncomputable def padAdv (F : ℕ) (Y : Security.Adversary) : Security.Adversary where
  main pk := do
    let r ← SphincsBase.QueryCap.counted (selFree pk.parameter) (Y.main pk)
    liftWorld (padW pk.parameter (F - r.2))
    return r.1

/-- The single-key game of `Y` with the count of its short calls off the key. -/
noncomputable def gameCnt (Y : Security.Adversary) : OracleComp OracleWorld ((Bool × PublicParameter) × ℕ) := do
  let seed ← liftM sampleMasterSeed
  let (pk, sk) ← liftM (Seeded.keygenFromSeed seed)
  let (((forgery, c), log) : (_root_.Sphincs.Forgery × ℕ) × QueryLog Sphincs.SigningSpec) ←
    (simulateQ (QueryImpl.ofLift OracleWorld
      (WriterT (QueryLog Sphincs.SigningSpec) (OracleComp OracleWorld)) + Det.signingOracleDet sk)
      (SphincsBase.QueryCap.counted (selFree pk.parameter) (Y.main pk))).run
  let verified ← liftM (Concrete.verify pk forgery.message forgery.signature : OracleComp HashSpec Bool)
  return ((decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified, pk.parameter), c)

theorem run_counted_forget {α : Type} (sk : Seeded.SecretKey) (sel : AdvSpec.Domain → Prop) [DecidablePred sel]
    (M : OracleComp AdvSpec α) :
    (simulateQ (Det.gameImplDet sk) M).run =
      (fun r => (r.1.1, r.2)) <$> (simulateQ (Det.gameImplDet sk) (SphincsBase.QueryCap.counted sel M)).run := by
  conv_lhs => rw [← SphincsBase.QueryCap.counted_forget sel M]
  rw [simulateQ_map, WriterT.run_map]

theorem gameCoreDetP_eq_gameCnt (Y : Security.Adversary) :
    gameCoreDetP Y = Prod.fst <$> gameCnt Y := by
  unfold gameCoreDetP gameCnt
  simp only [map_bind, map_pure]
  refine bind_congr fun seed => bind_congr fun key => ?_
  rcases key with ⟨pk, sk⟩
  change (simulateQ (Det.gameImplDet sk) (Y.main pk)).run >>= _ = (simulateQ (Det.gameImplDet sk) _).run >>= _
  rw [run_counted_forget sk (selFree pk.parameter), bind_map_left]

omit [Params] in
/-- `k` padding calls before a computation avoiding the padding input add `k` times its weight. -/
theorem run'_padW {ω : Type} [AddCommMonoid ω] (w : HashInput → ω) (p : PublicParameter) {β : Type}
    (Z : OracleComp OracleWorld β) (hZ : Avoids (padInput p) Z) :
    ∀ (k : ℕ) (cache : QueryCache HashSpec),
      (simulateQ romImpl (cntW w (padW p k >>= fun _ => Z))).run' cache =ᵈ
        (fun r => (r.1, k • w (padInput p) + r.2)) <$> (simulateQ romImpl (cntW w Z)).run' cache
  | 0, cache => by
      simp only [padW, pure_bind, zero_smul, zero_add, Prod.mk.eta, id_map']
      exact EvalDistEq.refl _
  | k + 1, cache => by
      rw [padW, bind_assoc, cntW_query_bind]
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, map_bind,
        simulateQ_pure, StateT.run_pure]
      change (randomOracle (spec := HashSpec) (padInput p)).run cache >>= _ =ᵈ _
      have hstep : ∀ cache' : QueryCache HashSpec, cache' (padInput p) ≠ none →
          (fun r => (r.1, w (padInput p) + r.2)) <$>
            (simulateQ romImpl (cntW w (padW p k >>= fun _ => Z))).run' cache' =ᵈ
          (fun r => (r.1, (k + 1) • w (padInput p) + r.2)) <$> (simulateQ romImpl (cntW w Z)).run' cache' := by
        intro cache' _
        refine ((run'_padW w p Z hZ k cache').map _).trans ?_
        rw [Functor.map_map]
        have he : (fun a : β × ω => ((a.1, k • w (padInput p) + a.2).1,
              w (padInput p) + (a.1, k • w (padInput p) + a.2).2)) =
            fun r => (r.1, (k + 1) • w (padInput p) + r.2) :=
          funext fun r => by simp [succ_nsmul', add_assoc]
        rw [he]
      cases hc : cache (padInput p) with
      | some answer =>
          rw [QueryImpl.withCaching_run_some _ hc, pure_bind]
          have h := hstep cache (by rw [hc]; simp)
          simpa [StateT.run'_eq, Functor.map_map, weightOf] using h
      | none =>
          rw [QueryImpl.withCaching_run_none _ hc]
          refine (evalDist_map_bind' _ _ _).trans ?_
          refine EvalDistEq.trans (my := (uniformSampleImpl (spec := HashSpec) (padInput p) : ProbComp HashOutput) >>=
            fun _ => (fun r => (r.1, (k + 1) • w (padInput p) + r.2)) <$> (simulateQ romImpl (cntW w Z)).run' cache)
            ?_ (OracleComp.EvalDistEq.bind_const _ _)
          refine EvalDistEq.bind_right _ fun answer => ?_
          have h := hstep (cache.cacheQuery (padInput p) answer) (by simp)
          refine EvalDistEq.trans ?_ (h.trans ((run'_cacheQuery_avoids (padInput p) answer _
            (Avoids.cntW w hZ) cache).map _))
          simp [StateT.run'_eq, Functor.map_map, weightOf]

/-- The part of the padded game before the padding: the key and the counted interaction. -/
noncomputable def prePad (Y : Security.Adversary) :
    OracleComp OracleWorld (PublicKey × ((_root_.Sphincs.Forgery × ℕ) × QueryLog Sphincs.SigningSpec)) := do
  let seed ← liftM sampleMasterSeed
  let key ← liftM (Seeded.keygenFromSeed seed)
  let r ← (simulateQ (Det.gameImplDet key.2) (SphincsBase.QueryCap.counted (selFree key.1.parameter) (Y.main key.1))).run
  return (key.1, r)

/-- The check after the padding. -/
noncomputable def postPad (s : PublicKey × ((_root_.Sphincs.Forgery × ℕ) × QueryLog Sphincs.SigningSpec)) :
    OracleComp OracleWorld ((Bool × PublicParameter) × ℕ) := do
  let verified ← liftM (Concrete.verify s.1 s.2.1.1.message s.2.1.1.signature : OracleComp HashSpec Bool)
  return ((decide (SigningTranscript.Valid s.2.2 ∧ ¬SigningTranscript.Contains s.2.2 s.2.1.1) && verified,
    s.1.parameter), s.2.1.2)

theorem gameCnt_eq (Y : Security.Adversary) : gameCnt Y = prePad Y >>= postPad := by
  simp only [gameCnt, prePad, postPad, bind_assoc, pure_bind]
  rfl

theorem gameCoreDetP_padAdv (F : ℕ) (Y : Security.Adversary) :
    gameCoreDetP (padAdv F Y) = Prod.fst <$> (prePad Y >>= fun s =>
      padW s.1.parameter (F - s.2.1.2) >>= fun _ => postPad s) := by
  simp only [gameCoreDetP, prePad, postPad, bind_assoc, pure_bind, map_bind, map_pure]
  refine bind_congr fun seed => bind_congr fun key => ?_
  rcases key with ⟨pk, sk⟩
  change (simulateQ (Det.gameImplDet sk) ((padAdv F Y).main pk)).run >>= _ = _
  simp only [padAdv, simulateQ_bind, WriterT.run_bind, Det.gameImplDet_liftWorld, bind_map_left, bind_assoc,
    simulateQ_pure, map_bind]
  refine bind_congr fun r => ?_
  refine bind_congr fun u => ?_
  simp [List.empty_eq]

omit [Params] in
theorem run'_cntW_map {ω : Type} [AddCommMonoid ω] (w : HashInput → ω) {α β : Type} (g : OracleComp OracleWorld α)
    (f : α → β) (cache : QueryCache HashSpec) :
    (simulateQ romImpl (cntW w (f <$> g))).run' cache =
      (fun r => (f r.1, r.2)) <$> (simulateQ romImpl (cntW w g)).run' cache := by
  simp only [cntW_map, simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map]

omit [Params] in
theorem runW_map {ω : Type} [AddCommMonoid ω] (w : HashInput → ω) {α β : Type} (g : OracleComp OracleWorld α)
    (f : α → β) : runW w (f <$> g) = (fun r => (f r.1, r.2)) <$> runW w g :=
  run'_cntW_map w g f ∅

theorem postPad_eq (s : PublicKey × ((_root_.Sphincs.Forgery × ℕ) × QueryLog Sphincs.SigningSpec)) :
    postPad s = (fun verified => ((decide (SigningTranscript.Valid s.2.2 ∧ ¬SigningTranscript.Contains s.2.2 s.2.1.1) &&
      verified, s.1.parameter), s.2.1.2)) <$>
        (liftM (Concrete.verify s.1 s.2.1.1.message s.2.1.1.signature : OracleComp HashSpec Bool) :
          OracleComp OracleWorld Bool) := by
  rw [postPad, map_eq_bind_pure_comp]
  rfl

/-- **The padded game weighs as the game of `Y` plus the padding.** -/
theorem runW_padAdv {ω : Type} [AddCommMonoid ω] (w : HashInput → ω) (F : ℕ) (Y : Security.Adversary) :
    runW w (gameCoreDetP (padAdv F Y)) =ᵈ
      (fun r => (r.1.1, r.2 + (F - r.1.2) • w (padInput r.1.1.2))) <$> runW w (gameCnt Y) := by
  rw [gameCoreDetP_padAdv, gameCnt_eq, runW_map, runW_bind, runW_bind, map_bind, map_bind]
  refine EvalDistEq.bind_right _ fun res => ?_
  have havoid : Avoids (padInput res.1.1.1.parameter) (postPad res.1.1) := by
    refine Avoids.bind (Avoids.of_onlyK (padInput_not_ofKey _) (OnlyK.verify _ _ _)) fun _ => ?_
    exact isQueryBoundP_pure _ _ 0
  refine (((run'_padW w _ (postPad res.1.1) havoid _ res.2).map _).map _).trans ?_
  simp only [postPad_eq, run'_cntW_map, Functor.map_map]
  convert EvalDistEq.refl _ using 2
  funext r
  simp only [Prod.mk.injEq, true_and]
  abel

/-! ### The counts of the game of `Y` -/

omit [Params] in
theorem mem_support_run_cntW_bind {ω : Type} [AddCommMonoid ω] (w : HashInput → ω) {α β : Type}
    {g : OracleComp OracleWorld α} {k : α → OracleComp OracleWorld β} {cache : QueryCache HashSpec}
    {r : (β × ω) × QueryCache HashSpec} (hr : r ∈ support ((simulateQ romImpl (cntW w (g >>= k))).run cache)) :
    ∃ r1 ∈ support ((simulateQ romImpl (cntW w g)).run cache),
      ∃ r2 ∈ support ((simulateQ romImpl (cntW w (k r1.1.1))).run r1.2),
        r = ((r2.1.1, r1.1.2 + r2.1.2), r2.2) := by
  rw [cntW_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨r1, hr1, hr⟩ := hr
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨r2, hr2, hr⟩ := hr
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  exact ⟨r1, hr1, r2, hr2, hr⟩

omit [Params] in
theorem mem_support_run_cntW_pure {ω : Type} [AddCommMonoid ω] (w : HashInput → ω) {α : Type} (v : α)
    {cache : QueryCache HashSpec} {r : (α × ω) × QueryCache HashSpec}
    (hr : r ∈ support ((simulateQ romImpl (cntW w (pure v : OracleComp OracleWorld α))).run cache)) :
    r = ((v, 0), cache) := by
  simpa [cntW_pure] using hr

omit [Params] in
theorem mem_support_run_cntW_query {ω : Type} [AddCommMonoid ω] (w : HashInput → ω) (q : OracleWorld.Domain)
    {cache : QueryCache HashSpec} {r : (OracleWorld.Range q × ω) × QueryCache HashSpec}
    (hr : r ∈ support ((simulateQ romImpl (cntW w (liftM (OracleWorld.query q) :
      OracleComp OracleWorld _))).run cache)) : r.1.2 = weightOf w q := by
  rw [show (liftM (OracleWorld.query q) : OracleComp OracleWorld _) =
    liftM (OracleWorld.query q) >>= fun a => pure a from (bind_pure _).symm, cntW_query_bind] at hr
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff, cntW_pure,
    simulateQ_pure, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨a, -, rfl⟩ := hr
  simp

omit [Params] in
/-- **A computation of one key counts its short calls on its key.** -/
theorem onlyK_counts {p : PublicParameter} {α : Type} (Z : OracleComp HashSpec α) (hZ : OnlyK p Z) :
    ∀ (cache : QueryCache HashSpec) r,
      r ∈ support ((simulateQ romImpl (cntW wJ (liftM Z : OracleComp OracleWorld α))).run cache) →
        r.1.2.1 = r.1.2.2 p := by
  induction Z using OracleComp.inductionOn with
  | pure value =>
      intro cache r hr
      rw [show (liftM (pure value : OracleComp HashSpec α) : OracleComp OracleWorld α) = pure value from rfl] at hr
      rw [mem_support_run_cntW_pure wJ value hr]
      rfl
  | query_bind input next ih =>
      intro cache r hr
      rw [OnlyK, isQueryBoundP_query_bind_iff] at hZ
      have hin : OfKey p input := by
        rcases hZ.1 with h1 | h1
        · exact not_not.mp h1
        · omega
      have hnext : ∀ answer, OnlyK p (next answer) := fun answer => by
        have := hZ.2 answer
        split at this <;> simpa [OnlyK] using this
      rw [liftM_bind] at hr
      obtain ⟨r1, hr1, r2, hr2, rfl⟩ := mem_support_run_cntW_bind wJ
        (g := (liftM (OracleWorld.query (.inr input)) : OracleComp OracleWorld _)) hr
      have h1 := mem_support_run_cntW_query wJ (.inr input) hr1
      have h2 := ih r1.1.1 (hnext r1.1.1) r1.2 r2 hr2
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, h1, h2, weightOf, wJ_ofKey hin]

/-- **Key generation makes at most two short calls off its key.** -/
theorem keygen_counts (seed : MasterSeed) (cache : QueryCache HashSpec) r
    (hr : r ∈ support ((simulateQ romImpl (cntW wJ (liftM (Seeded.keygenFromSeed seed) :
      OracleComp OracleWorld _))).run cache)) :
    (r.1.2.2 r.1.1.1.parameter ≤ r.1.2.1 ∧ r.1.2.1 ≤ r.1.2.2 r.1.1.1.parameter + 2) ∧
      r.1.1.2.parameter = r.1.1.1.parameter := by
  rw [show (Seeded.keygenFromSeed seed : OracleComp HashSpec _) =
    (liftM (HashSpec.query (schemeSeedInput seed)) >>= fun master =>
      liftM (HashSpec.query (keygenHashInput 0 .parameter master)) >>= fun out =>
        Seeded.treeRoot (truncateHash out) topLayer Concrete.rootTree master >>= fun root =>
          pure (⟨root, truncateHash out⟩, ⟨master, truncateHash out, root⟩)) from rfl] at hr
  simp only [liftM_bind] at hr
  obtain ⟨r1, hr1, r2, hr2, rfl⟩ := mem_support_run_cntW_bind wJ
    (g := (liftM (OracleWorld.query (.inr (schemeSeedInput seed))) : OracleComp OracleWorld _)) hr
  obtain ⟨r3, hr3, r4, hr4, rfl⟩ := mem_support_run_cntW_bind wJ
    (g := (liftM (OracleWorld.query (.inr (keygenHashInput 0 .parameter r1.1.1))) : OracleComp OracleWorld _)) hr2
  have h1 := mem_support_run_cntW_query wJ _ hr1
  have h3 := mem_support_run_cntW_query wJ _ hr3
  simp only [liftM_pure, bind_pure_comp] at hr4
  rw [cntW_map, simulateQ_map, StateT.run_map, support_map] at hr4
  obtain ⟨r5, hr5, rfl⟩ := hr4
  have h5 := onlyK_counts _ (Seeded.OnlyK.treeRoot (truncateHash r3.1.1) topLayer Concrete.rootTree r1.1.1) r3.2 r5 hr5
  have hs1 : (wJ (schemeSeedInput seed)).1 ≤ 1 := by simp only [wJ, wS]; split_ifs <;> omega
  have hs3 : (wJ (keygenHashInput 0 .parameter r1.1.1)).1 ≤ 1 := by simp only [wJ, wS]; split_ifs <;> omega
  have hl1 := wJ_le (truncateHash r3.1.1) (schemeSeedInput seed)
  have hl3 := wJ_le (truncateHash r3.1.1) (keygenHashInput 0 .parameter r1.1.1)
  refine ⟨?_, rfl⟩
  simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, h1, h3, weightOf] at hl1 hl3 ⊢
  constructor <;> omega

/-- **The interaction counts the calls of the adversary off the key**: its short calls are those on
the key plus the adversary's count. -/
theorem interaction_counts (sk : Seeded.SecretKey) {α : Type} (M : OracleComp AdvSpec α) :
    ∀ (cache : QueryCache HashSpec) r,
      r ∈ support ((simulateQ romImpl (cntW wJ ((simulateQ (Det.gameImplDet sk)
        (SphincsBase.QueryCap.counted (selFree sk.parameter) M)).run))).run cache) →
        r.1.2.1 = r.1.2.2 sk.parameter + r.1.1.1.2 := by
  induction M using OracleComp.inductionOn with
  | pure value =>
      intro cache r hr
      simp only [SphincsBase.QueryCap.counted_pure, simulateQ_pure, WriterT.run_pure] at hr
      rw [mem_support_run_cntW_pure wJ _ hr]
      rfl
  | query_bind input next ih =>
      intro cache r hr
      rw [SphincsBase.QueryCap.counted_query_bind, simulateQ_bind, WriterT.run_bind, simulateQ_spec_query] at hr
      rcases input with q | m
      · have hq : (Det.gameImplDet sk (Sum.inl q)).run =
            (fun a => (a, ∅)) <$> (liftM (OracleWorld.query q) : OracleComp OracleWorld _) := by
          simp only [Det.gameImplDet, QueryImpl.add_apply_inl, QueryImpl.ofLift_apply]
          exact run_liftM_world_writer q
        rw [hq, bind_map_left] at hr
        obtain ⟨r1, hr1, r2, hr2, rfl⟩ := mem_support_run_cntW_bind wJ
          (g := (liftM (OracleWorld.query q) : OracleComp OracleWorld _)) hr
        have h1 := mem_support_run_cntW_query wJ q hr1
        simp only [bind_pure_comp, Functor.map_map, simulateQ_map, WriterT.run_map] at hr2
        rw [cntW_map, simulateQ_map, StateT.run_map, support_map] at hr2
        obtain ⟨r3, hr3, rfl⟩ := hr2
        have h3 := ih r1.1.1 r1.2 r3 hr3
        simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, h1, h3]
        rcases q with d | x
        · simp [weightOf, selFree]
        · by_cases hs : IsShort x <;> by_cases hk : OfKey sk.parameter x <;>
            simp [weightOf, selFree, wJ, wS, wPi, hs, hk] <;> omega
      · have hm : (Det.gameImplDet sk (Sum.inr m)).run = (do
            let signature ← (liftM (Seeded.sign sk m : OracleComp HashSpec (Option Signature)) :
              OracleComp OracleWorld (Option Signature))
            pure (signature, [⟨m, signature⟩])) := by
          simp only [Det.gameImplDet, QueryImpl.add_apply_inr, Det.signingOracleDet, QueryImpl.run_withLogging_apply]
        rw [hm, bind_assoc] at hr
        simp only [pure_bind] at hr
        obtain ⟨r1, hr1, r2, hr2, rfl⟩ := mem_support_run_cntW_bind wJ
          (g := (liftM (Seeded.sign sk m : OracleComp HashSpec (Option Signature)) :
            OracleComp OracleWorld (Option Signature))) hr
        have h1 := onlyK_counts _ (Seeded.OnlyK.seededSign sk m) cache r1 hr1
        simp only [bind_pure_comp, Functor.map_map, simulateQ_map, WriterT.run_map] at hr2
        rw [cntW_map, simulateQ_map, StateT.run_map, support_map] at hr2
        obtain ⟨r3, hr3, rfl⟩ := hr2
        have h3 := ih r1.1.1 r1.2 r3 hr3
        simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, h1, h3, selFree]
        simp only [ite_false, zero_add]
        omega

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
/-- **The game of `Y` counts its short calls**: those on the key, the adversary's count of the
others, and at most two of key generation. -/
theorem gameCnt_counts (Y : Security.Adversary) r (hr : Reach (runW wJ (gameCnt Y)) r) :
    r.1.2 + r.2.2 r.1.1.2 ≤ r.2.1 ∧ r.2.1 ≤ r.2.2 r.1.1.2 + r.1.2 + 2 := by
  rw [reach_iff, runW, StateT.run'_eq, support_map] at hr
  obtain ⟨r0, hr0, rfl⟩ := hr
  rw [gameCnt_eq, prePad] at hr0
  simp only [bind_assoc] at hr0
  rw [cntW_sampling_bind, simulateQ_bind, StateT.run_bind, run_lift_prob, bind_map_left,
    mem_support_bind_iff] at hr0
  obtain ⟨seed, -, hr1⟩ := hr0
  obtain ⟨s2, hs2, r2, hr2, rfl⟩ := mem_support_run_cntW_bind wJ
    (g := (liftM (Seeded.keygenFromSeed seed) : OracleComp OracleWorld _)) hr1
  have hk := keygen_counts seed ∅ s2 hs2
  obtain ⟨s3, hs3, r3, hr3, rfl⟩ := mem_support_run_cntW_bind wJ hr2
  have hi := interaction_counts s2.1.1.2 (Y.main s2.1.1.1) s2.2 s3 (by rw [hk.2]; exact hs3)
  simp only [pure_bind] at hr3
  rw [postPad_eq, cntW_map, simulateQ_map, StateT.run_map, support_map] at hr3
  obtain ⟨r4, hr4, rfl⟩ := hr3
  have hv := onlyK_counts _ (OnlyK.verify s2.1.1.1 s3.1.1.1.1.message s3.1.1.1.1.signature) s3.2 r4 hr4
  rw [hk.2] at hi
  simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, hi, hv] at hk ⊢
  constructor <;> omega

end Sphincs.Security.Multi
