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

variable {ι : Type} {spec : OracleSpec ι} {D : Type}

/-- A level's result asks at most `n` queries and returns at most `n` parents. -/
private abbrev LevelBound {X : Type} (c : OracleComp spec (Option (List X × List D))) (n : ℕ) :
    Prop :=
  IsTotalQueryBound c n ∧ ∀ r ∈ support c, ∀ p, r = some p → p.1.length ≤ n

private theorem levelBound_mono {X : Type} {c : OracleComp spec (Option (List X × List D))}
    {n k : ℕ} (h : LevelBound c n) (hnk : n ≤ k) : LevelBound c k :=
  ⟨h.1.mono hnk, fun r hr p hp ↦ (h.2 r hr p hp).trans hnk⟩

private theorem levelBound_none {X : Type} (n : ℕ) :
    LevelBound (pure none : OracleComp spec (Option (List X × List D))) n := by
  refine ⟨pure_bound _ _, fun r hr p hp ↦ ?_⟩
  rw [mem_support_pure_iff] at hr
  subst hr
  cases hp

private theorem levelBound_nil {X : Type} (sibs : List D) :
    LevelBound (pure (some (([] : List X), sibs)) : OracleComp spec _) 0 := by
  refine ⟨pure_bound _ _, fun r hr p hp ↦ ?_⟩
  rw [mem_support_pure_iff] at hr
  subst hr
  cases hp
  simp

private theorem levelBound_consParent {U : Type} (i : ℕ) {parent : OracleComp spec U}
    {rest : OracleComp spec (Option (List (ℕ × U) × List D))} {n : ℕ}
    (hp : IsTotalQueryBound parent 1) (hr : LevelBound rest n) :
    LevelBound (consParent i parent rest) (n + 1) := by
  refine ⟨(isTotalQueryBound_bind hp fun _ ↦ isTotalQueryBound_bind hr.1 fun _ ↦
    pure_bound _ 0).mono (by omega), fun r hr' p hp' ↦ ?_⟩
  simp only [consParent, mem_support_bind_iff, mem_support_pure_iff] at hr'
  obtain ⟨_, -, r', hr'', rfl⟩ := hr'
  cases r' with
  | none => cases hp'
  | some x =>
    cases hp'
    simpa using hr.2 _ hr'' x rfl

private theorem levelBound_withNext {X : Type} {sibs : List D}
    {k : D → List D → OracleComp spec (Option (List X × List D))} {n : ℕ}
    (hk : ∀ s sibs, LevelBound (k s sibs) n) : LevelBound (withNext sibs k) n := by
  cases sibs with
  | nil => exact levelBound_none n
  | cons s sibs => exact hk s sibs

variable (hash : D → D → OracleComp spec D) (hh : ∀ a b, IsTotalQueryBound (hash a b) 1)

include hh

/-- One level of the walk asks at most one query per node and returns at most as many parents. -/
theorem levelStep_queries {h : ℕ} (nodes : List (ℕ × D)) (sibs : List D) :
    IsTotalQueryBound (levelStep (NodeAlgebra.ofHash hash) (h := h) nodes sibs) nodes.length ∧
      ∀ r ∈ support (levelStep (NodeAlgebra.ofHash hash) (h := h) nodes sibs), ∀ p,
        r = some p → p.1.length ≤ nodes.length := by
  have hs : ∀ (i : ℕ) (a s : D),
      IsTotalQueryBound (withSupplied (NodeAlgebra.ofHash hash) (h := h) i a s) 1 :=
    fun i a s ↦ by unfold withSupplied; split <;> exact hh _ _
  fun_induction levelStep (NodeAlgebra.ofHash hash) nodes sibs with
  | case1 sibs => exact levelBound_mono (levelBound_nil sibs) (Nat.zero_le _)
  | case2 i a sibs j b rest hp ih =>
    exact levelBound_mono (levelBound_consParent _ (hh a b) ih) (by simp)
  | case3 i a sibs j b rest hp ih =>
    exact levelBound_withNext fun s sibs ↦
      levelBound_mono (levelBound_consParent _ (hs i a s) (ih sibs)) (by simp)
  | case4 i a sibs =>
    exact levelBound_withNext fun s sibs ↦ levelBound_consParent _ (hs i a s) (levelBound_nil sibs)

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
