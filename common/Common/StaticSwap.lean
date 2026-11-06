module

public import Common.SeedKey
public import Common.Eager

@[expose] public section

/-!
# A signer swapped for one with the same values and at least its hash calls

Two hash-query schemes `S₁` and `S₂` (`Common.SufCma.SchemeWithHash`) whose honest algorithms,
evaluated on any answer function `f`, give the same public key and the same signatures, `S₂`
making at least `S₁`'s hash calls (`StaticSwap`), have the same success in the random-oracle game,
and a game against `S₂` within `q` hash calls on every path is one against `S₁` within `q` calls on
every outcome. So a random-oracle bound for `S₁`, counted on the outcomes of its experiment, is one
for `S₂` (`StaticSwap.romBound`).

The order of the hash calls is free: the success is compared with the honest algorithms' part of
the random oracle sampled in advance (`Common.Eager`), on which the honest algorithms are
functions of the table; the hash calls are compared on the outcomes of `S₁`'s game, whose answers
`S₂`'s game can give, path by path.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace Common.SufCma

/-! ## A hash-only computation on an answer function -/

section Answers

variable {α β : Type} (f : QueryImpl SchemeHashSpec Id)

/-- The inputs `X` queries when `f` answers. -/
def answerLog (X : OracleComp SchemeHashSpec α) : List (List UInt8) :=
  ((simulateQ f.withLogging X).run).2.map Sigma.fst

/-- The number of hash calls of `X` when `f` answers. -/
def answerCalls (X : OracleComp SchemeHashSpec α) : ℕ := (answerLog f X).length

@[simp] theorem answerLog_pure (a : α) : answerLog f (pure a : OracleComp SchemeHashSpec α) = [] := by
  simp [answerLog]; rfl

@[simp] theorem answerLog_query_bind (t : List UInt8)
    (k : BitVec 256 → OracleComp SchemeHashSpec α) :
    answerLog f (liftM (SchemeHashSpec.query t) >>= k) = t :: answerLog f (k (f t)) := by
  simp [answerLog]; rfl

theorem answerLog_bind (X : OracleComp SchemeHashSpec α) (k : α → OracleComp SchemeHashSpec β) :
    answerLog f (X >>= k) = answerLog f X ++ answerLog f (k (evalWithAnswerFn f X)) := by
  induction X using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t rest ih =>
    rw [bind_assoc, answerLog_query_bind, answerLog_query_bind, ih, evalWithAnswerFn_bind,
      show evalWithAnswerFn f (liftM (SchemeHashSpec.query t)) = f t from
        simulateQ_spec_query f t, List.cons_append]

@[simp] theorem answerCalls_pure (a : α) :
    answerCalls f (pure a : OracleComp SchemeHashSpec α) = 0 := by
  simp [answerCalls]

@[simp] theorem answerCalls_query_bind (t : List UInt8)
    (k : BitVec 256 → OracleComp SchemeHashSpec α) :
    answerCalls f (liftM (SchemeHashSpec.query t) >>= k) = answerCalls f (k (f t)) + 1 := by
  simp [answerCalls]

theorem answerCalls_bind (X : OracleComp SchemeHashSpec α) (k : α → OracleComp SchemeHashSpec β) :
    answerCalls f (X >>= k) = answerCalls f X + answerCalls f (k (evalWithAnswerFn f X)) := by
  simp only [answerCalls, answerLog_bind, List.length_append]

/-- `f` answers as the cache `c` wherever `c` holds an answer. -/
def Agrees (c : SchemeHashSpec.QueryCache) : Prop := ∀ t u, c t = some u → f t = u

/-- An answer function that answers as the cache, where it holds an answer. -/
def cacheAnswers (c : SchemeHashSpec.QueryCache) : QueryImpl SchemeHashSpec Id :=
  fun t ↦ (c t).getD 0

theorem agrees_cacheAnswers (c : SchemeHashSpec.QueryCache) : Agrees (cacheAnswers c) c :=
  fun t u h ↦ by simp [cacheAnswers, h]

theorem Agrees.mono {f : QueryImpl SchemeHashSpec Id} {c c' : SchemeHashSpec.QueryCache}
    (h : Agrees f c') (hc : c ≤ c') : Agrees f c :=
  fun t u hu ↦ h t u (hc hu)

end Answers

/-! ## The counted random oracle, one call at a time -/

/-- A run of the counted random oracle from the cache `c`. -/
noncomputable abbrev countedRun {α : Type} (x : OracleComp World α) (c : SchemeHashSpec.QueryCache) :=
  (simulateQ countedImpl x).run.run c

theorem countedRun_hq_bind {α : Type} (t : List UInt8) (k : BitVec 256 → OracleComp World α)
    (c : SchemeHashSpec.QueryCache) :
    countedRun (liftM (World.query (.inr t)) >>= k) c = roStep t c >>= fun a ↦
      (fun p ↦ ((p.1.1, Multiplicative.ofAdd 1 * p.1.2), p.2)) <$> countedRun (k a.1) a.2 := by
  simp only [countedRun, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, WriterT.run_bind, StateT.run_bind]
  simp only [countedImpl, QueryImpl.withAddCost_apply]
  simp
  congr 1
  rcases h : c t with _ | u
  · rw [roStep_of_none h]
    simp
  · rw [roStep_of_some h]
    simp

theorem liftM_query_bind {α : Type} (t : List UInt8)
    (k : BitVec 256 → OracleComp SchemeHashSpec α) :
    (liftM (liftM (SchemeHashSpec.query t) >>= k) : OracleComp World α) =
      liftM (World.query (.inr t)) >>= fun u ↦ liftM (k u) := by
  rw [liftM_bind]; rfl

/-- **A hash-only computation's counted run**: it keeps the cache's answers, and on every outcome
its value and its number of calls are those of the answer function of its final cache. -/
theorem countedRun_liftM {α : Type} (X : OracleComp SchemeHashSpec α) :
    ∀ (c : SchemeHashSpec.QueryCache), ∀ z ∈ support (countedRun (liftM X : OracleComp World α) c),
      c ≤ z.2 ∧ ∀ f, Agrees f z.2 →
        z.1.1 = evalWithAnswerFn f X ∧ Multiplicative.toAdd z.1.2 = answerCalls f X := by
  induction X using OracleComp.inductionOn with
  | pure a =>
    intro c z hz
    simp only [liftM_pure, countedRun, simulateQ_pure, WriterT.run_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨le_refl _, fun f _ ↦ ⟨rfl, by simp⟩⟩
  | query_bind t k ih =>
    intro c z hz
    rw [liftM_query_bind, countedRun_hq_bind, mem_support_bind_iff] at hz
    obtain ⟨w, hw, hz⟩ := hz
    rw [support_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨hcw, hwt⟩ := le_of_mem_support_roStep t c hw
    obtain ⟨hwy, hy⟩ := ih w.1 w.2 y hy
    refine ⟨le_trans hcw hwy, fun f hf ↦ ?_⟩
    have hft : f t = w.1 := hf t w.1 (hwy hwt)
    obtain ⟨h1, h2⟩ := hy f hf
    refine ⟨?_, ?_⟩
    · rw [evalWithAnswerFn_bind, show evalWithAnswerFn f (liftM (SchemeHashSpec.query t)) = f t from
        simulateQ_spec_query f t, hft]
      exact h1
    · rw [answerCalls_query_bind, hft, ← h2]
      simp only [toAdd_mul, toAdd_ofAdd]
      omega

theorem countedRun_coin_bind {α : Type} (n : ℕ) (k : Fin (n + 1) → OracleComp World α)
    (c : SchemeHashSpec.QueryCache) :
    countedRun (liftM (World.query (.inl n)) >>= k) c = ($ᵗ Fin (n + 1)) >>= fun u ↦
      (fun p ↦ ((p.1.1, Multiplicative.ofAdd 0 * p.1.2), p.2)) <$> countedRun (k u) c := by
  simp only [countedRun, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, WriterT.run_bind, StateT.run_bind]
  simp only [countedImpl, QueryImpl.withAddCost_apply]
  simp
  rfl

theorem countedRun_bind {α β : Type} (x : OracleComp World α) (g : α → OracleComp World β)
    (c : SchemeHashSpec.QueryCache) :
    countedRun (x >>= g) c = countedRun x c >>= fun z ↦
      (fun p ↦ ((p.1.1, z.1.2 * p.1.2), p.2)) <$> countedRun (g z.1.1) z.2 := by
  simp only [countedRun, simulateQ_bind, WriterT.run_bind, StateT.run_bind]
  simp

/-! ## Hash calls on a path -/

/-- **A shared prefix**: within `q` calls on every path of `x >>= g`, an outcome of `x`'s counted
run leaves the continuation at its output within the rest. -/
theorem prefix_cost {α β : Type} (x : OracleComp World α) :
    ∀ (g : α → OracleComp World β) (q : ℕ) (c : SchemeHashSpec.QueryCache),
      QueryCostAtMost (x >>= g) hashCalls q → ∀ z ∈ support (countedRun x c),
        c ≤ z.2 ∧ Multiplicative.toAdd z.1.2 ≤ q ∧
          QueryCostAtMost (g z.1.1) hashCalls (q - Multiplicative.toAdd z.1.2) := by
  induction x using OracleComp.inductionOn with
  | pure a =>
    intro g q c hq z hz
    simp only [countedRun, simulateQ_pure, WriterT.run_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at hz
    subst hz
    simpa using hq
  | query_bind t k ih =>
    intro g q c hq z hz
    rw [bind_assoc, isWeightBound_query_bind_iff] at hq
    rcases t with n | t
    · rw [countedRun_coin_bind, mem_support_bind_iff] at hz
      obtain ⟨u, -, hz⟩ := hz
      rw [support_map] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      obtain ⟨h1, h2, h3⟩ := ih u g _ c (hq.2 u) y hy
      refine ⟨h1, ?_, ?_⟩
      · simp only [toAdd_mul, toAdd_ofAdd]; simp only [hashCalls] at h2 ⊢; omega
      · simpa [hashCalls] using h3
    · rw [countedRun_hq_bind, mem_support_bind_iff] at hz
      obtain ⟨w, hw, hz⟩ := hz
      rw [support_map] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      obtain ⟨hcw, -⟩ := le_of_mem_support_roStep t c hw
      obtain ⟨h1, h2, h3⟩ := ih w.1 g _ w.2 (hq.2 w.1) y hy
      have h4 := hq.1
      simp only [hashCalls] at h2 h3 h4
      refine ⟨le_trans hcw h1, ?_, ?_⟩
      · simp only [toAdd_mul, toAdd_ofAdd]; omega
      · simp only [toAdd_mul, toAdd_ofAdd]
        exact h3.mono (by omega)

/-- **A hash-only computation on an answer function**: within `q` calls on every path of
`liftM X >>= k`, the path answered by `f` leaves `k` at `X`'s value on `f` within the rest. -/
theorem answer_cost {α β : Type} (X : OracleComp SchemeHashSpec α) (f : QueryImpl SchemeHashSpec Id) :
    ∀ (k : α → OracleComp World β) (q : ℕ),
      QueryCostAtMost ((liftM X : OracleComp World α) >>= k) hashCalls q →
        answerCalls f X ≤ q ∧
          QueryCostAtMost (k (evalWithAnswerFn f X)) hashCalls (q - answerCalls f X) := by
  induction X using OracleComp.inductionOn with
  | pure a =>
    intro k q hq
    simpa using hq
  | query_bind t rest ih =>
    intro k q hq
    rw [liftM_query_bind, bind_assoc, isWeightBound_query_bind_iff] at hq
    obtain ⟨h1, h2⟩ := ih (f t) k _ (hq.2 (f t))
    have h3 := hq.1
    simp only [hashCalls] at h1 h2 h3
    rw [answerCalls_query_bind, evalWithAnswerFn_bind,
      show evalWithAnswerFn f (liftM (SchemeHashSpec.query t)) = f t from
        simulateQ_spec_query f t]
    exact ⟨by omega, h2.mono (by omega)⟩

/-! ## The adversary's phase -/

section Phase

variable {Seed PK SK₁ SK₂ Req Resp F : Type}

/-- **The phase's hash calls**: when the signer of `S₂` with `sk₂` gives the values of the signer
of `S₁` with `sk₁` on every answer function agreeing with the cache `c₀`, with at least its hash
calls, every outcome of the phase against `S₁` from a cache extending `c₀`, followed by a common
continuation, makes at most the calls of the worst path against `S₂`. -/
theorem phase_count_le (S₁ : SchemeWithHash Seed PK SK₁ Req Resp F)
    (S₂ : SchemeWithHash Seed PK SK₂ Req Resp F) (sk₁ : SK₁) (sk₂ : SK₂)
    (c₀ : SchemeHashSpec.QueryCache)
    (hsign : ∀ f, Agrees f c₀ → ∀ r, evalWithAnswerFn f (S₂.sign sk₂ r) =
      evalWithAnswerFn f (S₁.sign sk₁ r) ∧ answerCalls f (S₁.sign sk₁ r) ≤ answerCalls f (S₂.sign sk₂ r))
    {β γ : Type} (M : OracleComp (World + (Req →ₒ Resp)) β) :
    ∀ (post : β × QueryLog (Req →ₒ Resp) → OracleComp World γ) (q : ℕ)
      (c : SchemeHashSpec.QueryCache), c₀ ≤ c →
      QueryCostAtMost ((simulateQ (gameOracles S₂ sk₂) M).run >>= post) hashCalls q →
        ∀ z ∈ support (countedRun ((simulateQ (gameOracles S₁ sk₁) M).run >>= post) c),
          Multiplicative.toAdd z.1.2 ≤ q := by
  induction M using OracleComp.inductionOn with
  | pure a =>
    intro post q c _ hq z hz
    simp only [simulateQ_pure, WriterT.run_pure, pure_bind] at hq hz
    exact count_le_of_isWeightBound hq c z hz
  | query_bind t k ih =>
    intro post q c hc hq z hz
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, WriterT.run_bind', bind_assoc] at hq hz
    rcases t with t | r
    · rw [gameOracles_inl] at hq hz
      simp only [bind_map_left] at hq hz
      rcases t with n | t
      · rw [countedRun_coin_bind, mem_support_bind_iff] at hz
        obtain ⟨u, -, hz⟩ := hz
        rw [support_map] at hz
        obtain ⟨y, hy, rfl⟩ := hz
        rw [isWeightBound_query_bind_iff] at hq
        have h := ih u _ _ c hc (hq.2 u) y hy
        simp only [hashCalls] at h
        simpa using h
      · rw [countedRun_hq_bind, mem_support_bind_iff] at hz
        obtain ⟨w, hw, hz⟩ := hz
        rw [support_map] at hz
        obtain ⟨y, hy, rfl⟩ := hz
        obtain ⟨hcw, -⟩ := le_of_mem_support_roStep t c hw
        rw [isWeightBound_query_bind_iff] at hq
        have h := ih w.1 _ _ w.2 (le_trans hc hcw) (hq.2 w.1) y hy
        have h1 := hq.1
        simp only [hashCalls] at h h1
        simp only [toAdd_mul, toAdd_ofAdd]
        omega
    · rw [gameOracles_inr] at hq hz
      simp only [bind_map_left] at hq hz
      rw [countedRun_bind, mem_support_bind_iff] at hz
      obtain ⟨w, hw, hz⟩ := hz
      rw [support_map] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      obtain ⟨hcw, hw⟩ := countedRun_liftM _ c w hw
      let f := cacheAnswers w.2
      have hf : Agrees f w.2 := agrees_cacheAnswers w.2
      obtain ⟨hval, hcount⟩ := hw f hf
      obtain ⟨hsv, hsc⟩ := hsign f (hf.mono (le_trans hc hcw)) r
      obtain ⟨h1, h2⟩ := answer_cost _ f _ q hq
      rw [hsv, ← hval] at h2
      have h := ih w.1.1 _ _ w.2 (le_trans hc hcw) h2 y hy
      simp only [toAdd_mul]
      omega

/-- A query of the adversary's own, in the phase. -/
theorem phase_inl {SK : Type} (S : SchemeWithHash Seed PK SK Req Resp F) (sk : SK) {β γ : Type}
    (t : World.Domain) (k : World.Range t → OracleComp (World + (Req →ₒ Resp)) β)
    (post : β × QueryLog (Req →ₒ Resp) → OracleComp World γ) :
    (simulateQ (gameOracles S sk)
      (liftM ((World + (Req →ₒ Resp)).query (.inl t)) >>= k)).run >>= post =
      liftM (World.query t) >>= fun u ↦
        (simulateQ (gameOracles S sk) (k u)).run >>= fun p ↦ post (p.1, ∅ ++ p.2) := by
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, WriterT.run_bind', bind_assoc, gameOracles_inl,
    bind_map_left]
  rfl

/-- A signing query, in the phase. -/
theorem phase_inr {SK : Type} (S : SchemeWithHash Seed PK SK Req Resp F) (sk : SK) {β γ : Type}
    (r : Req) (k : Resp → OracleComp (World + (Req →ₒ Resp)) β)
    (post : β × QueryLog (Req →ₒ Resp) → OracleComp World γ) :
    (simulateQ (gameOracles S sk)
      (liftM ((World + (Req →ₒ Resp)).query (.inr r)) >>= k)).run >>= post =
      liftM (S.sign sk r) >>= fun u ↦
        (simulateQ (gameOracles S sk) (k u)).run >>= fun p ↦ post (p.1, [⟨r, u⟩] ++ p.2) := by
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, WriterT.run_bind', bind_assoc, gameOracles_inr,
    bind_map_left]
  rfl

/-- The game with its pairs taken apart. -/
theorem romGame_eq {SK : Type} (S : SchemeWithHash Seed PK SK Req Resp F)
    (main : PK → OracleComp (World + (Req →ₒ Resp)) F) :
    romGame S main = liftM S.sample >>= fun seed ↦ liftM (S.keygen seed) >>= fun keys ↦
      (simulateQ (gameOracles S keys.2) (main keys.1)).run >>= fun p ↦
        liftM (S.verify keys.1 p.1) >>= fun verified ↦ pure (S.win p.2 p.1 && verified) := rfl

end Phase

/-! ## Queries in a part of the domain -/

/-- Every query of `X`, on every path, lies in `P`. -/
def QueriesIn (P : List UInt8 → Prop) {α : Type} : OracleComp SchemeHashSpec α → Prop
  | .pure _ => True
  | .liftBind t k => P t ∧ ∀ u, QueriesIn P (k u)

section QueriesIn

variable {P : List UInt8 → Prop} {α β : Type}

theorem queriesIn_pure (a : α) : QueriesIn P (pure a : OracleComp SchemeHashSpec α) := trivial

theorem queriesIn_query_bind (t : List UInt8) (k : BitVec 256 → OracleComp SchemeHashSpec α) :
    QueriesIn P (liftM (SchemeHashSpec.query t) >>= k) ↔ P t ∧ ∀ u, QueriesIn P (k u) := Iff.rfl

theorem queriesIn_bind {X : OracleComp SchemeHashSpec α} {f : α → OracleComp SchemeHashSpec β}
    (hX : QueriesIn P X) (hf : ∀ a, QueriesIn P (f a)) : QueriesIn P (X >>= f) := by
  induction X using OracleComp.inductionOn with
  | pure a => simpa using hf a
  | query_bind t k ih =>
    rw [bind_assoc, queriesIn_query_bind]
    exact ⟨hX.1, fun u ↦ ih u (hX.2 u)⟩

theorem queriesIn_map {X : OracleComp SchemeHashSpec α} (f : α → β) (hX : QueriesIn P X) :
    QueriesIn P (f <$> X) := by
  rw [map_eq_bind_pure_comp]
  exact queriesIn_bind hX fun _ ↦ trivial

theorem queriesIn_query {t : List UInt8} (ht : P t) :
    QueriesIn P (liftM (SchemeHashSpec.query t) : OracleComp SchemeHashSpec (BitVec 256)) := by
  have := (queriesIn_query_bind (P := P) t pure).mpr ⟨ht, fun _ ↦ trivial⟩
  simpa using this

end QueriesIn

/-! ## The honest part of the random oracle sampled in advance -/

section Eager

variable (P : List UInt8 → Prop) [DecidablePred P] [Fintype {d // P d}]

/-- **The random oracle with its `P`-part a table `g`**: a `P`-point is answered from the cache
if cached, else by `g`, and never cached; every other query is the lazy random oracle. -/
noncomputable def eagerW (g : {d // P d} → BitVec 256) :
    QueryImpl World (StateT SchemeHashSpec.QueryCache ProbComp)
  | .inl n => unifFwdImpl _ n
  | .inr d =>
      if h : P d then StateT.mk fun c ↦ pure ((c d).getD (g ⟨d, h⟩), c)
      else SchemeHashSpec.randomOracle d

omit [DecidablePred P] [Fintype {d // P d}] in
theorem randomOracle_run_comm' (t d : List UInt8) (ht : t ≠ d) (c : SchemeHashSpec.QueryCache)
    (u : BitVec 256) :
    Prod.map id (fun c' ↦ c'.cacheQuery d u) <$> (SchemeHashSpec.randomOracle t).run c =
      (SchemeHashSpec.randomOracle t).run (c.cacheQuery d u) := by
  rw [randomOracle.run_eq, randomOracle.run_eq, QueryCache.cacheQuery_of_ne _ _ ht]
  rcases h : c t with _ | v
  · simp only [map_bind, map_pure, Prod.map_apply, id_eq]
    refine bind_congr fun w ↦ ?_
    rw [QueryCache.cacheQuery_comm _ (Ne.symm ht)]
  · simp

omit [DecidablePred P] [Fintype {d // P d}] in
theorem mem_support_randomOracle_run' {t : List UInt8} {c : SchemeHashSpec.QueryCache} {z}
    (hz : z ∈ support ((SchemeHashSpec.randomOracle t).run c)) :
    z.2 = c ∨ ∃ v, z.2 = c.cacheQuery t v := by
  rw [randomOracle.run_eq] at hz
  rcases h : c t with _ | v
  · simp only [h, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨w, -, rfl⟩ := hz
    exact Or.inr ⟨w, rfl⟩
  · simp only [h, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inl rfl

theorem unifFwd_run' (n : ℕ) (c : SchemeHashSpec.QueryCache) :
    (unifFwdImpl SchemeHashSpec n).run c =
      (·, c) <$> (unifSpec.query n : ProbComp (Fin (n + 1))) := by
  simpa using unifFwdImpl.simulateQ_run (hashSpec := SchemeHashSpec)
    (unifSpec.query n : ProbComp (Fin (n + 1))) c

omit [Fintype {d // P d}] in
/-- Moving a cached `P`-answer into the table. -/
theorem run'_eagerW_cacheQuery (g : {d // P d} → BitVec 256) (d : List UInt8) (hd : P d)
    (u : BitVec 256) {α : Type} (Y : OracleComp World α) (c : SchemeHashSpec.QueryCache)
    (hc : c d = none) :
    (simulateQ (eagerW P g) Y).run' (c.cacheQuery d u) =ᵈ
      (simulateQ (eagerW P (Function.update g ⟨d, hd⟩ u)) Y).run' c := by
  refine (run'_simulateQ_evalDistEq_of_inv (eagerW P (Function.update g ⟨d, hd⟩ u))
    (eagerW P g) (fun c ↦ c d = none) (fun c ↦ c.cacheQuery d u) ?_ ?_ Y c hc).symm
  · intro t s hsd z hz
    rcases t with n | d'
    · change z ∈ support ((unifFwdImpl _ n).run s) at hz
      rw [unifFwd_run', support_map] at hz
      obtain ⟨_, -, rfl⟩ := hz
      exact hsd
    · simp only [eagerW] at hz
      split at hz
      · simp only [StateT.run_mk, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hsd
      · next hd' =>
        rcases mem_support_randomOracle_run' hz with h | ⟨v, h⟩
        · rw [h]; exact hsd
        · rw [h, QueryCache.cacheQuery_of_ne _ _ (by rintro rfl; exact hd' hd)]; exact hsd
  · intro t s hsd
    rcases t with n | d'
    · change _ <$> (unifFwdImpl _ n).run s =ᵈ (unifFwdImpl _ n).run _
      rw [unifFwd_run', unifFwd_run', Functor.map_map]
      exact EvalDistEq.rfl
    · simp only [eagerW]
      split
      · next hd' =>
        simp only [StateT.run_mk, map_pure, Prod.map_apply, id_eq]
        by_cases hdd : d' = d
        · subst hdd
          simp [hsd]
        · rw [QueryCache.cacheQuery_of_ne _ _ hdd]
          have : (⟨d', hd'⟩ : {d // P d}) ≠ ⟨d, hd⟩ := fun h ↦ hdd (congrArg Subtype.val h)
          simp [Function.update_of_ne this]
      · next hd' =>
        exact (randomOracle_run_comm' d' d (by rintro rfl; exact hd' hd) s u) ▸ EvalDistEq.rfl

/-- **Eager sampling of the `P`-part of the random oracle.** -/
theorem run'_romImpl_evalDistEq_eagerW {α : Type} (X : OracleComp World α)
    (c : SchemeHashSpec.QueryCache) :
    (simulateQ SchemeHashSpec.romImpl X).run' c =ᵈ
      (($ᵗ ({d // P d} → BitVec 256) : ProbComp _) >>= fun g ↦
        (simulateQ (eagerW P g) X).run' c) := by
  induction X using OracleComp.inductionOn generalizing c with
  | pure a =>
    simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
    exact (EvalDistEq.bind_const _ _).symm
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run'_eq, StateT.run_bind, map_bind]
    simp only [← StateT.run'_eq]
    rcases t with n | d
    · exact common_step_evalDistEq P ((unifFwdImpl _ n).run c) _ _ fun a ↦ ih a.1 a.2
    · by_cases hd : P d
      · have h1 : ∀ g, (eagerW P g (.inr d)).run c = pure ((c d).getD (g ⟨d, hd⟩), c) :=
          fun g ↦ by simp [eagerW, hd]
        simp only [h1, pure_bind]
        change (((SchemeHashSpec.randomOracle d).run c) >>= _) =ᵈ _
        rw [randomOracle.run_eq]
        rcases hc : c d with _ | v
        · simp only [bind_assoc, pure_bind, Option.getD_none]
          let ψ : ({d // P d} → BitVec 256) → ProbComp α := fun g ↦
            (simulateQ (eagerW P g) (k (g ⟨d, hd⟩))).run' c
          refine (EvalDistEq.bind_right _ fun u ↦ (ih u _).trans (EvalDistEq.bind_right _
            fun g ↦ run'_eagerW_cacheQuery P g d hd u (k u) c hc)).trans ?_
          have h2 : ∀ (u : BitVec 256) (g : {d // P d} → BitVec 256),
              (simulateQ (eagerW P (Function.update g ⟨d, hd⟩ u)) (k u)).run' c =
                ψ (Function.update g ⟨d, hd⟩ u) := fun u g ↦ by simp [ψ]
          simp only [h2]
          exact uniform_update_evalDistEq P ⟨d, hd⟩ ψ
        · simp only [pure_bind, Option.getD_some]
          exact ih v c
      · have h1 : ∀ g, eagerW P g (.inr d) = SchemeHashSpec.randomOracle d :=
          fun g ↦ by simp [eagerW, hd]
        simp only [h1]
        exact common_step_evalDistEq P ((SchemeHashSpec.randomOracle d).run c) _ _
          fun a ↦ ih a.1 a.2

/-- A cache without `P`-points: those of every run under the table from the empty cache. -/
def PFree (c : SchemeHashSpec.QueryCache) : Prop := ∀ d, P d → c d = none

/-- The table as an answer function. -/
def tableAnswers (g : {d // P d} → BitVec 256) : QueryImpl SchemeHashSpec Id :=
  fun d ↦ if h : P d then g ⟨d, h⟩ else 0

omit [DecidablePred P] [Fintype {d // P d}] in
theorem pFree_empty : PFree P ∅ := fun _ _ ↦ rfl

omit [Fintype {d // P d}] in
theorem pFree_step (g : {d // P d} → BitVec 256) (t : World.Domain) (c : SchemeHashSpec.QueryCache)
    (hc : PFree P c) : ∀ z ∈ support ((eagerW P g t).run c), PFree P z.2 := by
  intro z hz
  rcases t with n | d
  · change z ∈ support ((unifFwdImpl _ n).run c) at hz
    rw [unifFwd_run', support_map] at hz
    obtain ⟨_, -, rfl⟩ := hz
    exact hc
  · simp only [eagerW] at hz
    split at hz
    · simp only [StateT.run_mk, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hc
    · next hd =>
      rcases mem_support_randomOracle_run' hz with h | ⟨v, h⟩
      · rw [h]; exact hc
      · intro d' hd'
        rw [h, QueryCache.cacheQuery_of_ne _ _ (by rintro rfl; exact hd hd')]
        exact hc d' hd'

omit [Fintype {d // P d}] in
/-- Runs under the table keep caches without `P`-points. -/
theorem pFree_run (g : {d // P d} → BitVec 256) {α : Type} (X : OracleComp World α) :
    ∀ c, PFree P c → ∀ z ∈ support ((simulateQ (eagerW P g) X).run c), PFree P z.2 := by
  induction X using OracleComp.inductionOn with
  | pure a =>
    intro c hc z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact hc
  | query_bind t k ih =>
    intro c hc z hz
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨w, hw, hz⟩ := hz
    exact ih w.1 w.2 (pFree_step P g t c hc w hw) z hz

omit [Fintype {d // P d}] in
/-- **An honest computation under the table** is its value on the table, from a cache without
`P`-points, which it leaves unchanged. -/
theorem eagerW_liftM (g : {d // P d} → BitVec 256) {α : Type} (X : OracleComp SchemeHashSpec α)
    (hX : QueriesIn P X) :
    ∀ c, PFree P c → (simulateQ (eagerW P g) (liftM X : OracleComp World α)).run c =
      pure (evalWithAnswerFn (tableAnswers P g) X, c) := by
  induction X using OracleComp.inductionOn with
  | pure a =>
    intro c _
    simp
  | query_bind t k ih =>
    intro c hc
    rw [queriesIn_query_bind] at hX
    rw [liftM_query_bind]
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind]
    have hstep : (eagerW P g (.inr t)).run c = pure (g ⟨t, hX.1⟩, c) := by
      simp [eagerW, hX.1, hc t hX.1]
    rw [hstep, pure_bind, ih _ (hX.2 _) c hc, evalWithAnswerFn_bind,
      show evalWithAnswerFn (tableAnswers P g) (liftM (SchemeHashSpec.query t)) =
        tableAnswers P g t from simulateQ_spec_query _ t]
    simp [tableAnswers, hX.1]

end Eager

/-! ## The adversary's phase under the table -/

section PhaseEager

variable (P : List UInt8 → Prop) [DecidablePred P] [Fintype {d // P d}]
  {Seed PK SK₁ SK₂ Req Resp F : Type}

omit [Fintype {d // P d}] in
theorem run'_bind_congr (g : {d // P d} → BitVec 256) {α β : Type} (x : OracleComp World α)
    (f₁ f₂ : α → OracleComp World β) (c : SchemeHashSpec.QueryCache)
    (h : ∀ z ∈ support ((simulateQ (eagerW P g) x).run c),
      (simulateQ (eagerW P g) (f₂ z.1)).run' z.2 =ᵈ (simulateQ (eagerW P g) (f₁ z.1)).run' z.2) :
    (simulateQ (eagerW P g) (x >>= f₂)).run' c =ᵈ (simulateQ (eagerW P g) (x >>= f₁)).run' c := by
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  exact evalDistEq_bind_of_support EvalDistEq.rfl fun z hz ↦ by
    simpa only [StateT.run'_eq] using h z hz

omit [Fintype {d // P d}] in
theorem run'_liftM_bind (g : {d // P d} → BitVec 256) {α β : Type}
    (X : OracleComp SchemeHashSpec α) (hX : QueriesIn P X) (f : α → OracleComp World β)
    (c : SchemeHashSpec.QueryCache) (hc : PFree P c) :
    (simulateQ (eagerW P g) ((liftM X : OracleComp World α) >>= f)).run' c =
      (simulateQ (eagerW P g) (f (evalWithAnswerFn (tableAnswers P g) X))).run' c := by
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, eagerW_liftM P g X hX c hc,
    pure_bind]

omit [Fintype {d // P d}] in
/-- **The phase under the table**: when the two signers are honest computations with the same
values on the table, the phase against either, followed by a common continuation, is the same in
distribution from a cache without `P`-points. -/
theorem phase_eager (g : {d // P d} → BitVec 256) (S₁ : SchemeWithHash Seed PK SK₁ Req Resp F)
    (S₂ : SchemeWithHash Seed PK SK₂ Req Resp F) (sk₁ : SK₁) (sk₂ : SK₂)
    (h₁ : ∀ r, QueriesIn P (S₁.sign sk₁ r)) (h₂ : ∀ r, QueriesIn P (S₂.sign sk₂ r))
    (heq : ∀ r, evalWithAnswerFn (tableAnswers P g) (S₂.sign sk₂ r) =
      evalWithAnswerFn (tableAnswers P g) (S₁.sign sk₁ r))
    {β γ : Type} (M : OracleComp (World + (Req →ₒ Resp)) β) :
    ∀ (post : β × QueryLog (Req →ₒ Resp) → OracleComp World γ) (c : SchemeHashSpec.QueryCache),
      PFree P c →
      (simulateQ (eagerW P g) ((simulateQ (gameOracles S₂ sk₂) M).run >>= post)).run' c =ᵈ
        (simulateQ (eagerW P g) ((simulateQ (gameOracles S₁ sk₁) M).run >>= post)).run' c := by
  induction M using OracleComp.inductionOn with
  | pure a =>
    intro post c _
    exact EvalDistEq.rfl
  | query_bind t k ih =>
    intro post c hc
    rcases t with t | r
    · rw [phase_inl, phase_inl]
      exact run'_bind_congr P g _ _ _ c fun z hz ↦
        ih z.1 _ z.2 (pFree_run P g _ c hc z hz)
    · rw [phase_inr, phase_inr]
      rw [run'_liftM_bind P g _ (h₂ r) _ c hc, run'_liftM_bind P g _ (h₁ r) _ c hc, heq r]
      exact ih _ _ c hc

end PhaseEager

/-! ## The swap -/

/-- **A signer swapped for one with the same values and at least its hash calls.** `S₂`'s secret
key is a function `keep` of the seed; on every answer function `f`, `S₂`'s key generation gives
`S₁`'s public key with at least its calls, and `S₂`'s signer with the kept key gives the
signatures of `S₁`'s signer with `S₁`'s key on `f`, with at least its calls. The honest
algorithms query a finite part `P` of the hash's domain. -/
structure StaticSwap {Seed PK SK₁ SK₂ Req Resp F : Type}
    (S₁ : SchemeWithHash Seed PK SK₁ Req Resp F) (S₂ : SchemeWithHash Seed PK SK₂ Req Resp F) where
  keep : Seed → SK₂
  sample_eq : S₂.sample = S₁.sample
  verify_eq : S₂.verify = S₁.verify
  win_eq : S₂.win = S₁.win
  keygen_eval : ∀ f seed, evalWithAnswerFn f (S₂.keygen seed) =
    ((evalWithAnswerFn f (S₁.keygen seed)).1, keep seed)
  keygen_calls : ∀ f seed, answerCalls f (S₁.keygen seed) ≤ answerCalls f (S₂.keygen seed)
  sign_eval : ∀ f seed r, evalWithAnswerFn f (S₂.sign (keep seed) r) =
    evalWithAnswerFn f (S₁.sign (evalWithAnswerFn f (S₁.keygen seed)).2 r)
  sign_calls : ∀ f seed r, answerCalls f (S₁.sign (evalWithAnswerFn f (S₁.keygen seed)).2 r) ≤
    answerCalls f (S₂.sign (keep seed) r)

namespace StaticSwap

variable {Seed PK SK₁ SK₂ Req Resp F : Type} {S₁ : SchemeWithHash Seed PK SK₁ Req Resp F}
  {S₂ : SchemeWithHash Seed PK SK₂ Req Resp F}

/-- **The game's hash calls**: within `q` calls on every path of the game against `S₂`, every
outcome of the game against `S₁` makes at most `q` calls. -/
theorem romGame_count_le (K : StaticSwap S₁ S₂) (main : PK → OracleComp (World + (Req →ₒ Resp)) F) (q : ℕ)
    (h : QueryCostAtMost (romGame S₂ main) hashCalls q) :
    ∀ z ∈ support (countedRun (romGame S₁ main) ∅), Multiplicative.toAdd z.1.2 ≤ q := by
  intro z hz
  rw [romGame_eq, K.sample_eq] at h
  rw [romGame_eq, countedRun_bind, mem_support_bind_iff] at hz
  obtain ⟨w, hw, hz⟩ := hz
  rw [support_map] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  obtain ⟨-, hw1, hw2⟩ := prefix_cost _ _ q ∅ h w hw
  rw [countedRun_bind, mem_support_bind_iff] at hy
  obtain ⟨v, hv, hy⟩ := hy
  rw [support_map] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨-, hv⟩ := countedRun_liftM _ w.2 v hv
  let f := cacheAnswers v.2
  have hf : Agrees f v.2 := agrees_cacheAnswers v.2
  obtain ⟨hval, hcount⟩ := hv f hf
  obtain ⟨h1, h2⟩ := answer_cost _ f _ _ hw2
  rw [K.keygen_eval, ← hval] at h2
  simp only [K.verify_eq, K.win_eq] at h2
  have hsign : ∀ f', Agrees f' v.2 → ∀ r, evalWithAnswerFn f' (S₂.sign (K.keep w.1.1) r) =
      evalWithAnswerFn f' (S₁.sign v.1.1.2 r) ∧
        answerCalls f' (S₁.sign v.1.1.2 r) ≤ answerCalls f' (S₂.sign (K.keep w.1.1) r) := by
    intro f' hf' r
    have hkey : evalWithAnswerFn f' (S₁.keygen w.1.1) = v.1.1 := ((hv f' hf').1).symm
    have := K.sign_calls f' w.1.1 r
    rw [K.sign_eval, hkey]
    rw [hkey] at this
    exact ⟨rfl, this⟩
  have hx' := phase_count_le S₁ S₂ v.1.1.2 (K.keep w.1.1) v.2 hsign (main v.1.1.1) _ _ v.2
    (le_refl _) h2 x hx
  have hk := K.keygen_calls f w.1.1
  simp only [toAdd_mul]
  omega

/-- **The same success**: in the random-oracle model, the game against `S₂` is won as often as
the game against `S₁`. -/
theorem success_eq (K : StaticSwap S₁ S₂) (P : List UInt8 → Prop) [DecidablePred P]
    [Fintype {d // P d}] (hk₁ : ∀ seed, QueriesIn P (S₁.keygen seed))
    (hk₂ : ∀ seed, QueriesIn P (S₂.keygen seed)) (hs₁ : ∀ sk r, QueriesIn P (S₁.sign sk r))
    (hs₂ : ∀ seed r, QueriesIn P (S₂.sign (K.keep seed) r))
    (main : PK → OracleComp (World + (Req →ₒ Resp)) F) :
    Pr{let r ← romExperiment S₂ main}[r.1 = true] =
      Pr{let r ← romExperiment S₁ main}[r.1 = true] := by
  rw [prob_romExperiment, prob_romExperiment,
    (run'_romImpl_evalDistEq_eagerW P (romGame S₂ main) ∅).prEvent_eq,
    (run'_romImpl_evalDistEq_eagerW P (romGame S₁ main) ∅).prEvent_eq]
  refine (EvalDistEq.bind_right _ fun g ↦ ?_).prEvent_eq _
  rw [romGame_eq, romGame_eq, K.sample_eq]
  refine run'_bind_congr P g _ _ _ ∅ fun z hz ↦ ?_
  have hc := pFree_run P g _ ∅ (pFree_empty P) z hz
  rw [run'_liftM_bind P g _ (hk₂ z.1) _ z.2 hc, run'_liftM_bind P g _ (hk₁ z.1) _ z.2 hc,
    K.keygen_eval]
  simp only [K.verify_eq, K.win_eq]
  exact phase_eager P g S₁ S₂ _ _ (fun r ↦ hs₁ _ r) (hs₂ z.1) (fun r ↦ K.sign_eval _ z.1 r) _ _ z.2
    hc

/-- **A random-oracle bound passes to `S₂`**: a bound for `S₁` on every adversary whose
experiment makes at most `q` hash calls on every outcome is a `RomBound` of `S₂`. -/
theorem romBound (K : StaticSwap S₁ S₂) (P : List UInt8 → Prop) [DecidablePred P]
    [Fintype {d // P d}] (hk₁ : ∀ seed, QueriesIn P (S₁.keygen seed))
    (hk₂ : ∀ seed, QueriesIn P (S₂.keygen seed)) (hs₁ : ∀ sk r, QueriesIn P (S₁.sign sk r))
    (hs₂ : ∀ seed r, QueriesIn P (S₂.sign (K.keep seed) r)) {bits : ℕ}
    (h : ∀ q, 1 ≤ q → ∀ main : PK → OracleComp (World + (Req →ₒ Resp)) F,
      (∀ r ∈ support (romExperiment S₁ main), r.2 ≤ q) →
        Pr{let r ← romExperiment S₁ main}[r.1 = true] ≤ q / ((2 ^ bits : ℕ) : ℝ≥0∞)) :
    RomBound S₂ bits := by
  intro q hq main hcost
  rw [K.success_eq P hk₁ hk₂ hs₁ hs₂ main]
  refine h q hq main fun r hr ↦ ?_
  rw [romExperiment, StateT.run'_eq] at hr
  erw [support_map] at hr
  obtain ⟨z, hz, rfl⟩ := hr
  exact K.romGame_count_le main q hcost z hz

end StaticSwap

end Common.SufCma
