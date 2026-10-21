/-
  LeanVM.E2E.Reduction.Count

  Hash-query bounds in the schemes' world: the translation of the game keeps its hash-query
  bound, and the schemes' counted oracle counts at most a computation's bound.
-/

module

public import LeanVM.E2E.Reduction.Lift

/-!
# Counting hash queries in the schemes' world

The schemes' multi-user games bound an adversary by the hash calls of the whole experiment, as
counted by their `countedOracle` (one per hash query, none per coin). This module bounds that
count by a query bound of the computation (`count_le_of_isQueryBoundP`), and carries the game's
query bound to its translation (`isQueryBoundP_simulateQ_toW`) and the schemes' computations to
their lift (`isQueryBoundP_liftM_hash`, `isQueryBoundP_sLift`).
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

/-- The hash queries of the schemes' world. -/
def IsHashW : OW.Domain → Prop
  | .inl _ => False
  | .inr _ => True

/-- The schemes' hash queries are decidable. -/
instance : DecidablePred IsHashW
  | .inl _ => isFalse id
  | .inr _ => isTrue trivial

/-- **The translation keeps the hash-query bound**: a coin query is a coin query, a hash query
one hash query. -/
theorem isQueryBoundP_simulateQ_toW {α : Type} :
    ∀ (oa : OracleComp GameSpec α) (n : ℕ), IsQueryBoundP oa IsHash n →
      IsQueryBoundP (simulateQ toW oa) IsHashW n := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure x => intro n _; trivial
  | query_bind t k ih =>
    intro n h
    rw [isQueryBoundP_query_bind_iff] at h
    rw [simulateQ_query_bind]
    rcases t with m | x
    · change IsQueryBoundP (liftM (OW.query (.inl m)) >>= fun u ↦ simulateQ toW (k u)) IsHashW n
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl id, fun u ↦ by simpa [IsHash, IsHashW] using ih u n (by simpa [IsHash] using h.2 u)⟩
    · change IsQueryBoundP ((bitsD <$> (liftM (OW.query (.inr x)) : OracleComp OW _)) >>=
        fun u ↦ simulateQ toW (k u)) IsHashW n
      rw [bind_map_left, isQueryBoundP_query_bind_iff]
      refine ⟨Or.inr (by simpa [IsHash] using h.1), fun u ↦ ?_⟩
      simpa [IsHash, IsHashW] using ih (bitsD u) (n - 1) (by simpa [IsHash] using h.2 (bitsD u))

/-- **A leanXMSS computation, lifted into the schemes' world, keeps its query bound** as a
hash-query bound. -/
theorem isQueryBoundP_liftM_hash {α : Type} :
    ∀ (oa : OracleComp LeanXmss.HashSpec α) (n : ℕ), IsTotalQueryBound oa n →
      IsQueryBoundP (liftM oa : OracleComp OW α) IsHashW n := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure x => intro n _; trivial
  | query_bind x k ih =>
    intro n h
    rw [isTotalQueryBound_query_bind_iff] at h
    rw [liftM_bind]
    change IsQueryBoundP (liftM (OW.query (.inr x)) >>= fun u ↦ liftM (k u)) IsHashW n
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inr h.1, fun u ↦ by simpa [IsHashW] using ih u (n - 1) (h.2 u)⟩

/-- **A leanSPHINCS computation, lifted into the schemes' world, keeps its query bound** as a
hash-query bound. -/
theorem isQueryBoundP_sLift {α : Type} :
    ∀ (oa : OracleComp Sphincs.HashSpec α) (n : ℕ), IsTotalQueryBound oa n →
      IsQueryBoundP (sLift oa) IsHashW n := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure x => intro n _; trivial
  | query_bind x k ih =>
    intro n h
    rw [isTotalQueryBound_query_bind_iff] at h
    unfold sLift at ih ⊢
    rw [liftM_bind]
    exact (isQueryBoundP_query_bind_iff (spec := OW) (p := IsHashW) (.inr x)
      (fun u ↦ ((liftM (k u) : OracleComp Sphincs.OracleWorld α) : OracleComp OW α)) n).mpr
      ⟨Or.inr h.1, fun u ↦ by simpa [IsHashW] using ih u (n - 1) (h.2 u)⟩

/-- **The counted oracle counts at most the hash-query bound**: on every reachable run, the cost
of a computation with at most `n` hash queries, one per hash query and none per coin, is at most
`n`. -/
theorem count_le_of_isQueryBoundP {σ : Type} (impl : QueryImpl OW (StateT σ ProbComp))
    {α : Type} : ∀ (oa : OracleComp OW α) (n : ℕ), IsQueryBoundP oa IsHashW n → ∀ (s : σ),
      ∀ r ∈ support ((simulateQ (impl.withAddCost
          (fun t ↦ match t with | .inl _ => (0 : ℕ) | .inr _ => 1)) oa).run.run s),
        Multiplicative.toAdd r.1.2 ≤ n := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro n _ s r hr
    simp only [simulateQ_pure, WriterT.run_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hr
    subst hr
    simp
  | query_bind t k ih =>
    intro n h s r hr
    rw [isQueryBoundP_query_bind_iff] at h
    rw [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind, QueryImpl.withAddCost_apply,
      WriterT.run_bind, StateT.run_bind] at hr
    simp only [AddWriterT.run_addTell, pure_bind, WriterT.run_monadLift, Functor.map_map,
      StateT.run_map, mem_support_bind_iff, support_map, Set.mem_image] at hr
    obtain ⟨⟨⟨u, w⟩, s'⟩, ⟨⟨u', s''⟩, -, hq⟩, x, hx, rfl⟩ := hr
    simp only [Prod.mk.injEq, mul_one] at hq
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hq
    have hb := ih u' _ (h.2 u') s'' x hx
    simp only [toAdd_mul, toAdd_ofAdd]
    rcases t with m | y
    · simpa [IsHashW] using hb
    · have h1 : 0 < n := h.1.resolve_left (by simp [IsHashW])
      simp only [IsHashW, ↓reduceIte] at hb
      dsimp only
      omega

/-- **A sequence of computations each with at most `b` queries of `p`** makes at most `n · b`. -/
theorem isQueryBoundP_sequenceFin {ι : Type} {spec : OracleSpec.{0, 0} ι} {p : ι → Prop}
    [DecidablePred p] {α : Type} (b : ℕ) :
    ∀ {n : ℕ} (c : Fin n → OracleComp spec α), (∀ i, IsQueryBoundP (c i) p b) →
      IsQueryBoundP (LeanXmss.Concrete.sequenceFin c) p (n * b)
  | 0, _, _ => by simp [LeanXmss.Concrete.sequenceFin]
  | n + 1, c, h => by
    simp only [LeanXmss.Concrete.sequenceFin]
    refine (isQueryBoundP_bind (n := b) (m := n * b + 0) (h 0) fun _ _ ↦
      isQueryBoundP_bind (isQueryBoundP_sequenceFin b (fun i ↦ c i.succ) fun i ↦ h i.succ)
        fun _ _ ↦ by simp).mono (by rw [Nat.add_mul, Nat.one_mul]; omega)

/-- **A sequence of computations each with at most `b` queries** makes at most `n · b`. -/
theorem isTotalQueryBound_sequenceFin {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type} (b : ℕ) :
    ∀ {n : ℕ} (c : Fin n → OracleComp spec α), (∀ i, IsTotalQueryBound (c i) b) →
      IsTotalQueryBound (LeanXmss.Concrete.sequenceFin c) (n * b)
  | 0, _, _ => trivial
  | n + 1, c, h => by
    simp only [LeanXmss.Concrete.sequenceFin]
    have := isTotalQueryBound_bind (n₁ := b) (n₂ := n * b + 0) (h 0) fun hd ↦
      isTotalQueryBound_bind (ob := fun tl ↦ (pure (fun i ↦ Fin.cases hd tl i) :
        OracleComp spec (Fin (n + 1) → α)))
        (isTotalQueryBound_sequenceFin b (fun i ↦ c i.succ) fun i ↦ h i.succ)
        fun _ ↦ trivial
    rwa [show (n + 1) * b = b + (n * b + 0) by rw [Nat.add_mul, Nat.one_mul]; omega]

end
end LeanVM.E2E
