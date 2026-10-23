/-
  LeanerVM.Protocol.ToVCVio.MerkleQueries

  The queries of the walk over a pruned Merkle opening when the node hash is an oracle
  computation of one query: at most one per opened node and level. Candidate for VCVio.
-/

module

public import LeanerVM.Protocol.ToVCVio.Merkle
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-!
# The queries of a pruned opening's walk

With a node hash `hash` of at most one query (`IsTotalQueryBound (hash a b) 1`), one level of the
walk asks at most one query per node of the level and returns at most as many parents
(`levelStep_queries`), so the walk over `k` levels from `n` opened nodes asks at most `k * n`
queries (`fold_queries`), and the root of a pruned opening of `n` leaves in a tree of depth `d`
costs at most `d * n` (`prunedRoot_queries`).
-/

namespace LeanerVM.Protocol.MerkleTree

open OracleComp OracleSpec

@[expose] public section

private theorem pure_bound {ι : Type} {spec : OracleSpec ι} {α : Type} (x : α) (n : ℕ) :
    IsTotalQueryBound (pure x : OracleComp spec α) n :=
  isQueryBound_pure x n _ _

variable {ι : Type} {spec : OracleSpec ι} {D : Type} (hash : D → D → OracleComp spec D)
  (hh : ∀ a b, IsTotalQueryBound (hash a b) 1)

include hh

/-- One level of the walk asks at most one query per node and returns at most as many parents. -/
theorem levelStep_queries {h : ℕ} (nodes : List (ℕ × D)) (sibs : List D) :
    IsTotalQueryBound (levelStep (NodeAlgebra.ofHash hash) (h := h) nodes sibs) nodes.length ∧
      ∀ r ∈ support (levelStep (NodeAlgebra.ofHash hash) (h := h) nodes sibs), ∀ p,
        r = some p → p.1.length ≤ nodes.length := by
  fun_induction levelStep (NodeAlgebra.ofHash hash) nodes sibs with
  | case1 sibs =>
    refine ⟨pure_bound _ _, fun r hr p hp ↦ ?_⟩
    rw [mem_support_pure_iff] at hr
    subst hr
    cases hp
    simp
  | case2 i a sibs j b rest hp ih =>
    simp only [consParent]
    refine ⟨(isTotalQueryBound_bind (hh a b) fun _ ↦ isTotalQueryBound_bind ih.1 fun _ ↦
      pure_bound _ 0).mono (by simp only [List.length_cons]; omega), fun r hr p hp ↦ ?_⟩
    simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨_, -, r', hr', rfl⟩ := hr
    cases r' with
    | none => cases hp
    | some x =>
      cases hp
      have := ih.2 _ hr' x rfl
      simp only [List.length_cons] at this ⊢
      omega
  | case3 i a sibs j b rest hp ih =>
    cases sibs with
    | nil =>
      refine ⟨pure_bound _ _, fun r hr p hp ↦ ?_⟩
      simp only [withNext, mem_support_pure_iff] at hr
      subst hr
      cases hp
    | cons s sibs =>
      simp only [withNext, consParent, withSupplied]
      have hs : IsTotalQueryBound (if i % 2 = 0 then hash a s else hash s a) 1 := by
        split
        · exact hh a s
        · exact hh s a
      refine ⟨(isTotalQueryBound_bind hs fun _ ↦ isTotalQueryBound_bind (ih sibs).1 fun _ ↦
        pure_bound _ 0).mono (by simp only [List.length_cons]; omega), fun r hr p hp ↦ ?_⟩
      simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨_, -, r', hr', rfl⟩ := hr
      cases r' with
      | none => cases hp
      | some x =>
        cases hp
        have := (ih sibs).2 _ hr' x rfl
        simp only [List.length_cons] at this ⊢
        omega
  | case4 i a sibs =>
    cases sibs with
    | nil =>
      refine ⟨pure_bound _ _, fun r hr p hp ↦ ?_⟩
      simp only [withNext, mem_support_pure_iff] at hr
      subst hr
      cases hp
    | cons s sibs =>
      simp only [withNext, consParent, withSupplied]
      have hs : IsTotalQueryBound (if i % 2 = 0 then hash a s else hash s a) 1 := by
        split
        · exact hh a s
        · exact hh s a
      refine ⟨(isTotalQueryBound_bind hs fun _ ↦ isTotalQueryBound_bind (pure_bound _ 0)
        fun _ ↦ pure_bound _ 0).mono (by simp only [List.length_cons]; omega), fun r hr p hp ↦ ?_⟩
      simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨_, -, r', hr', rfl⟩ := hr
      subst hr'
      cases hp
      simp

/-- **The walk over `k` levels** from `n` opened nodes asks at most `k * n` queries. -/
theorem fold_queries : ∀ (k h t : ℕ) (e : h + k = t) (nodes : List (ℕ × D)) (sibs : List D),
    IsTotalQueryBound (fold (NodeAlgebra.ofHash hash) k h t e nodes sibs) (k * nodes.length)
  | 0, _, _, rfl, nodes, sibs => pure_bound _ _
  | k + 1, h, t, e, nodes, sibs => by
    simp only [fold]
    refine (isTotalQueryBound_bind_of_mem_support (levelStep_queries hash hh (h := h) nodes sibs).1
      (suffixBound := k * nodes.length) fun r hr ↦ ?_).mono (by rw [Nat.succ_mul]; omega)
    cases r with
    | none => exact pure_bound _ _
    | some p =>
      exact (fold_queries k (h + 1) t (by omega) p.1 p.2).mono
        (Nat.mul_le_mul_left k ((levelStep_queries hash hh nodes sibs).2 _ hr p rfl))

/-- **A pruned opening's root** in a tree of depth `depth`, from `n` opened leaves, asks at most
`depth * n` queries. -/
theorem prunedRoot_queries (depth : ℕ) (leaves : List (ℕ × D)) (sibs : List D) :
    IsTotalQueryBound (prunedRoot hash depth leaves sibs) (depth * leaves.length) :=
  fold_queries hash hh depth 0 depth (Nat.zero_add depth) leaves sibs

end

end LeanerVM.Protocol.MerkleTree
