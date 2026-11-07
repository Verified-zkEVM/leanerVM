/-
  LeanVM.Wire.ModelPerm

  Replay and cache for the lazily sampled permutation: a run that ended with some edges is the run
  with the answers of any permutation through them, and a computation whose queries are all
  recorded runs deterministically, adding no edge.
-/

module

public import Common.Model

/-!
# The lazy permutation: replay and cache

Completeness on the wire decodes the honest proof's bytes after the prover's run, every hash call
answered by the sponge over the lazily sampled permutation. These generic facts reduce that to the
pure decoding (`LeanVM.Wire.Model`):

* `queriesWith ans oc`: the queries `oc` makes when each query `q` is answered `ans q`; a logged run
  (`logImpl`) is the pure run (`pureImpl`) with the images of these queries (`run_logImpl`);
* **replay** (`replay_perm`, and `replay_calls` for calls that are computations over the
  permutation, as Keccak-256 is the sponge over it): a run against the lazy permutation that ends with
  edges `s` on a permutation `σ` (`OnPerm σ s`, and there is one, `exists_onPerm_of_mem_support_calls`)
  is the run with `σ`'s answers, and every query it made is recorded in `s`;
* **cache** (`cached_perm`, `cached_calls`): a computation whose queries with `σ`'s answers are all
  recorded in edges on `σ` runs from them to its result with `σ`, adding no edge.
-/

@[expose] public section

open OracleComp OracleSpec

namespace LeanVM.Wire

open Common (PermutationEdges PermutationQuery permutationOracleSpec lazyRandomPermutation
  forwardLookup inverseLookup)

/-! ## Logged runs with fixed answers -/

section Log

variable {ι : Type} {spec : OracleSpec ι}

/-- Answer each query `q` with `ans q`, appending `f q` to the log. -/
def logImpl {β : Type} (f : ι → List β) (ans : (q : ι) → spec.Range q) :
    QueryImpl spec (StateM (List β)) :=
  fun q ↦ do
    modify (· ++ f q)
    pure (ans q)

/-- Answer each query `q` with `ans q`. -/
def pureImpl (ans : (q : ι) → spec.Range q) : QueryImpl spec Id := fun q ↦ ans q

/-- The queries a computation makes with the answers `ans`, in order. -/
def queriesWith (ans : (q : ι) → spec.Range q) {α : Type} (oc : OracleComp spec α) : List ι :=
  ((simulateQ (logImpl (fun q ↦ [q]) ans) oc).run []).2

/-- One query, then `k`: logged. -/
theorem run_logImpl_query_bind {β : Type} (g : ι → List β) (ans : (q : ι) → spec.Range q)
    {α : Type} (t : ι) (k : spec.Range t → OracleComp spec α) (l : List β) :
    (simulateQ (logImpl g ans) (liftM (spec.query t) >>= k)).run l =
      (simulateQ (logImpl g ans) (k (ans t))).run (l ++ g t) := by
  simp [simulateQ_bind, logImpl]

theorem simulateQ_pureImpl_query_bind (ans : (q : ι) → spec.Range q) {α : Type} (t : ι)
    (k : spec.Range t → OracleComp spec α) :
    simulateQ (pureImpl ans) (liftM (spec.query t) >>= k) = simulateQ (pureImpl ans) (k (ans t)) := by
  rw [simulateQ_bind, simulateQ_spec_query]
  rfl

/-- **A logged run** is the run with the answers, its log the images of the queries. -/
theorem run_logImpl (ans : (q : ι) → spec.Range q) {α : Type} (oc : OracleComp spec α) :
    ∀ {β : Type} (f : ι → List β) (l₀ : List β),
    (simulateQ (logImpl f ans) oc).run l₀ =
      (simulateQ (pureImpl ans) oc, l₀ ++ (queriesWith ans oc).flatMap f) := by
  induction oc using OracleComp.inductionOn with
  | pure a =>
    intro β f l₀
    change (a, l₀) = (a, l₀ ++ List.flatMap f [])
    simp
  | query_bind t k ih =>
    intro β f l₀
    have hq : queriesWith ans (liftM (spec.query t) >>= k) = t :: queriesWith ans (k (ans t)) := by
      conv_lhs => unfold queriesWith
      rw [run_logImpl_query_bind, List.nil_append, ih (ans t) (fun q ↦ [q]) [t]]
      simp
    rw [run_logImpl_query_bind, ih, hq, simulateQ_pureImpl_query_bind]
    simp

theorem queriesWith_query_bind (ans : (q : ι) → spec.Range q) {α : Type} (t : ι)
    (k : spec.Range t → OracleComp spec α) :
    queriesWith ans (liftM (spec.query t) >>= k) = t :: queriesWith ans (k (ans t)) := by
  conv_lhs => unfold queriesWith
  rw [run_logImpl_query_bind, run_logImpl]
  simp

theorem queriesWith_bind (ans : (q : ι) → spec.Range q) {α γ : Type} (oc : OracleComp spec α)
    (k : α → OracleComp spec γ) :
    queriesWith ans (oc >>= k) =
      queriesWith ans oc ++ queriesWith ans (k (simulateQ (pureImpl ans) oc)) := by
  conv_lhs => unfold queriesWith
  rw [simulateQ_bind, StateT.run_bind, run_logImpl]
  change ((simulateQ (logImpl (fun q ↦ [q]) ans) (k (simulateQ (pureImpl ans) oc))).run
    ([] ++ (queriesWith ans oc).flatMap fun q ↦ [q])).2 = _
  rw [run_logImpl]
  simp

end Log

/-! ## The lazy permutation: replay and cache -/

section Edges

variable {S : Type}

/-- The answer of the permutation `σ` to a query. -/
def permAnswer (σ : Equiv.Perm S) : (q : PermutationQuery S) → (permutationOracleSpec S).Range q
  | .forward x => σ x
  | .inverse y => σ.symm y

/-- The edges `E` lie on the permutation `σ`. -/
def OnPerm (σ : Equiv.Perm S) (E : PermutationEdges S) : Prop := ∀ e ∈ E, σ e.1 = e.2

/-- A query is recorded in the edges `E`. -/
def Recorded (E : PermutationEdges S) : PermutationQuery S → Prop
  | .forward x => x ∈ E.map Prod.fst
  | .inverse y => y ∈ E.map Prod.snd

theorem OnPerm.of_suffix {σ : Equiv.Perm S} {E E' : PermutationEdges S} (h : OnPerm σ E')
    (hs : E <:+ E') : OnPerm σ E := fun e he ↦ h e (hs.subset he)

theorem Recorded.of_suffix {E E' : PermutationEdges S} {q : PermutationQuery S} (h : Recorded E q)
    (hs : E <:+ E') : Recorded E' q := by
  cases q with
  | forward x => exact (hs.map Prod.fst).subset h
  | inverse y => exact (hs.map Prod.snd).subset h

end Edges

section Perm

variable {S : Type} [Fintype S] [DecidableEq S] [SampleableType S]

theorem suffix_of_mem_support_simulateQ {α : Type} (oc : OracleComp (permutationOracleSpec S) α)
    {E : PermutationEdges S} {z : α × PermutationEdges S}
    (hz : z ∈ support ((simulateQ lazyRandomPermutation oc).run E)) : E <:+ z.2 := by
  induction oc using OracleComp.inductionOn generalizing E with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact List.suffix_refl _
  | query_bind q k ih =>
    simp only [simulateQ_query_bind, StateT.run_bind, OracleQuery.input_query, monadLift_self,
      mem_support_bind_iff] at hz
    obtain ⟨w, hw, hz⟩ := hz
    exact (Common.lazyPerm_log_suffix q hw).trans (ih w.1 hz)

/-- One query answered by the lazy permutation, its edges on `σ` after it: `σ`'s answer, and
recorded. -/
theorem replay_query {σ : Equiv.Perm S} (q : PermutationQuery S) {E : PermutationEdges S}
    {z : S × PermutationEdges S} (hz : z ∈ support ((lazyRandomPermutation q).run E))
    (hσ : OnPerm σ z.2) : z.1 = permAnswer σ q ∧ Recorded z.2 q := by
  have hm := Common.lazyPerm_answer_mem q hz
  cases q with
  | forward x =>
    exact ⟨(hσ _ hm).symm, List.mem_map_of_mem (f := Prod.fst) hm⟩
  | inverse y =>
    refine ⟨?_, List.mem_map_of_mem (f := Prod.snd) hm⟩
    have := hσ _ hm
    dsimp only at this
    simp only [permAnswer]
    rw [← this, Equiv.symm_apply_apply]

/-- One recorded query on `σ`'s edges is answered from them. -/
theorem cached_query {σ : Equiv.Perm S} {E : PermutationEdges S} (hσ : OnPerm σ E)
    (q : PermutationQuery S) (hq : Recorded E q) :
    (lazyRandomPermutation q).run E = pure (permAnswer σ q, E) := by
  cases q with
  | forward x =>
    simp only [lazyRandomPermutation, StateT.run_mk]
    rcases hx : forwardLookup E x with _ | y
    · exact absurd hq (Common.fwdLookup_eq_none_iff.mp hx)
    · simp only [permAnswer]
      rw [hσ _ (Common.mem_of_fwdLookup_eq_some hx)]
  | inverse y =>
    simp only [lazyRandomPermutation, StateT.run_mk]
    rcases hy : inverseLookup E y with _ | x
    · exact absurd hq (Common.invLookup_eq_none_iff.mp hy)
    · simp only [permAnswer]
      have := hσ _ (Common.mem_of_invLookup_eq_some hy)
      dsimp only at this
      rw [← this, Equiv.symm_apply_apply]

/-- **Replay**: a run against the lazy permutation ending with edges on `σ` is the run with `σ`'s
answers, and each of its queries is recorded. -/
theorem replay_perm {σ : Equiv.Perm S} {α : Type} (oc : OracleComp (permutationOracleSpec S) α)
    {E : PermutationEdges S} {z : α × PermutationEdges S}
    (hz : z ∈ support ((simulateQ lazyRandomPermutation oc).run E)) (hσ : OnPerm σ z.2) :
    simulateQ (pureImpl (permAnswer σ)) oc = z.1 ∧
      ∀ q ∈ queriesWith (permAnswer σ) oc, Recorded z.2 q := by
  induction oc using OracleComp.inductionOn generalizing E with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨rfl, fun q hq ↦ (List.not_mem_nil hq).elim⟩
  | query_bind q k ih =>
    simp only [simulateQ_query_bind, StateT.run_bind, OracleQuery.input_query, monadLift_self,
      mem_support_bind_iff] at hz
    obtain ⟨w, hw, hz⟩ := hz
    have hs := suffix_of_mem_support_simulateQ (k w.1) hz
    obtain ⟨h1, h2⟩ := replay_query q hw (hσ.of_suffix hs)
    obtain ⟨ih1, ih2⟩ := ih w.1 hz
    rw [h1] at ih1 ih2
    refine ⟨?_, ?_⟩
    · rwa [simulateQ_pureImpl_query_bind]
    · intro q' hq'
      rw [queriesWith_query_bind, List.mem_cons] at hq'
      rcases hq' with rfl | hq'
      · exact h2.of_suffix hs
      · exact ih2 q' hq'

/-- **Cache**: a computation whose queries, with `σ`'s answers, are all recorded in edges on `σ`
runs from them to its result with `σ`, adding no edge. -/
theorem cached_perm {σ : Equiv.Perm S} {α : Type} (oc : OracleComp (permutationOracleSpec S) α)
    {E : PermutationEdges S} (hσ : OnPerm σ E)
    (h : ∀ q ∈ queriesWith (permAnswer σ) oc, Recorded E q) :
    (simulateQ lazyRandomPermutation oc).run E =
      pure (simulateQ (pureImpl (permAnswer σ)) oc, E) := by
  induction oc using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q k ih =>
    rw [queriesWith_query_bind] at h
    rw [simulateQ_pureImpl_query_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      cached_query hσ q (h q List.mem_cons_self), pure_bind]
    exact ih _ fun q' hq' ↦ h q' (List.mem_cons_of_mem _ hq')

/-! ### Calls answered by computations over the permutation -/

variable {ι : Type} {spec : OracleSpec ι}
  (toPerm : QueryImpl spec (OracleComp (permutationOracleSpec S)))

/-- The answers of the calls `toPerm` with the permutation `σ`. -/
def callAnswer (σ : Equiv.Perm S) : (t : ι) → spec.Range t :=
  fun t ↦ simulateQ (pureImpl (permAnswer σ)) (toPerm t)

/-- A call is recorded in the edges `E`: every permutation query it makes with `σ`'s answers. -/
def RecordedCall (σ : Equiv.Perm S) (E : PermutationEdges S) (t : ι) : Prop :=
  ∀ q ∈ queriesWith (permAnswer σ) (toPerm t), Recorded E q

theorem suffix_of_mem_support_calls {α : Type} (oc : OracleComp spec α)
    {E : PermutationEdges S} {z : α × PermutationEdges S}
    (hz : z ∈ support ((simulateQ (lazyRandomPermutation ∘ₛ toPerm) oc).run E)) : E <:+ z.2 := by
  rw [QueryImpl.simulateQ_compose] at hz
  exact suffix_of_mem_support_simulateQ _ hz

/-- **A run's edges lie on a permutation.** -/
theorem exists_onPerm_of_mem_support_calls {α : Type} (oc : OracleComp spec α)
    {z : α × PermutationEdges S}
    (hz : z ∈ support ((simulateQ (lazyRandomPermutation ∘ₛ toPerm) oc).run [])) :
    ∃ σ : Equiv.Perm S, OnPerm σ z.2 := by
  rw [QueryImpl.simulateQ_compose] at hz
  exact Common.exists_perm_extends
    (Common.isPartialPerm_suffix_of_mem_support_simulateQ _ Common.isPartialPerm_nil hz).1

/-- **Replay, for calls**: a run of the calls against the lazy permutation ending with edges on
`σ` is the run with the calls' answers under `σ`, and each call it made is recorded. -/
theorem replay_calls {σ : Equiv.Perm S} {α : Type} (oc : OracleComp spec α)
    {E : PermutationEdges S} {z : α × PermutationEdges S}
    (hz : z ∈ support ((simulateQ (lazyRandomPermutation ∘ₛ toPerm) oc).run E))
    (hσ : OnPerm σ z.2) :
    simulateQ (pureImpl (callAnswer toPerm σ)) oc = z.1 ∧
      ∀ t ∈ queriesWith (callAnswer toPerm σ) oc, RecordedCall toPerm σ z.2 t := by
  induction oc using OracleComp.inductionOn generalizing E with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨rfl, fun q hq ↦ (List.not_mem_nil hq).elim⟩
  | query_bind t k ih =>
    simp only [simulateQ_query_bind, StateT.run_bind, OracleQuery.input_query, monadLift_self,
      mem_support_bind_iff, QueryImpl.apply_compose] at hz
    obtain ⟨w, hw, hz⟩ := hz
    have hs := suffix_of_mem_support_calls toPerm (k w.1) hz
    obtain ⟨h1, h2⟩ := replay_perm (toPerm t) hw (hσ.of_suffix hs)
    obtain ⟨ih1, ih2⟩ := ih w.1 hz
    have h1' : callAnswer toPerm σ t = w.1 := h1
    rw [← h1'] at ih1 ih2
    refine ⟨?_, ?_⟩
    · rwa [simulateQ_pureImpl_query_bind]
    · intro t' ht'
      rw [queriesWith_query_bind, List.mem_cons] at ht'
      rcases ht' with rfl | ht'
      · exact fun q hq ↦ (h2 q hq).of_suffix hs
      · exact ih2 t' ht'

/-- **Cache, for calls**: a computation whose calls, with `σ`'s answers, are all recorded in edges
on `σ` runs from them to its result with the calls' answers under `σ`, adding no edge. -/
theorem cached_calls {σ : Equiv.Perm S} {α : Type} (oc : OracleComp spec α)
    {E : PermutationEdges S} (hσ : OnPerm σ E)
    (h : ∀ t ∈ queriesWith (callAnswer toPerm σ) oc, RecordedCall toPerm σ E t) :
    (simulateQ (lazyRandomPermutation ∘ₛ toPerm) oc).run E =
      pure (simulateQ (pureImpl (callAnswer toPerm σ)) oc, E) := by
  induction oc using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    rw [queriesWith_query_bind] at h
    rw [simulateQ_pureImpl_query_bind, simulateQ_bind, simulateQ_spec_query,
      QueryImpl.apply_compose, StateT.run_bind,
      cached_perm (toPerm t) hσ (h t List.mem_cons_self), pure_bind]
    exact ih _ fun t' ht' ↦ h t' (List.mem_cons_of_mem _ ht')

end Perm

end LeanVM.Wire

end
