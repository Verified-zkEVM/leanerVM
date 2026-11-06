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

/-- The game with its pairs taken apart. -/
theorem romGame_eq {SK : Type} (S : SchemeWithHash Seed PK SK Req Resp F)
    (main : PK → OracleComp (World + (Req →ₒ Resp)) F) :
    romGame S main = liftM S.sample >>= fun seed ↦ liftM (S.keygen seed) >>= fun keys ↦
      (simulateQ (gameOracles S keys.2) (main keys.1)).run >>= fun p ↦
        liftM (S.verify keys.1 p.1) >>= fun verified ↦ pure (S.win p.2 p.1 && verified) := rfl

end Phase

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

end StaticSwap

end Common.SufCma
