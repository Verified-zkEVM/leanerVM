/-
  LeanerVM.Protocol.ToVCVio.QueryBound

  Query bounds of oracle computations: mapping a bounded computation over a vector, and the
  existence of some bound when every oracle answers in a finite type. Candidate for VCVio.
-/

module

public import VCVio.OracleComp.QueryTracking.Iter

/-!
# Query bounds of mapped and finitely branching computations

Mapping a computation of at most `k` queries over a vector of `n` entries asks at most `n * k`
(`isTotalQueryBound_vector_mapM`, from VCVio's list form). When every oracle answers in a finite
type, every computation has some query bound (`exists_isTotalQueryBound`).
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec

@[expose] public section

/-- Mapping a computation of at most `k` queries over a vector of `n` entries asks at most
`n * k`. -/
theorem isTotalQueryBound_vector_mapM {ι : Type} {spec : OracleSpec ι} {α β : Type}
    (f : α → OracleComp spec β) (k : ℕ) (hf : ∀ x, IsTotalQueryBound (f x) k) {n : ℕ}
    (v : Vector α n) : IsTotalQueryBound (v.mapM f) (n * k) := by
  have h : IsTotalQueryBound (Vector.toArray <$> v.mapM f) (n * k) := by
    rw [Vector.toArray_mapM, Array.mapM_eq_mapM_toList]
    refine (isQueryBound_map_iff _ _ _ _ _).mpr ?_
    have := isTotalQueryBound_listMapM_const hf v.toArray.toList
    rwa [Array.length_toList, Vector.size_toArray] at this
  exact (isQueryBound_map_iff _ _ _ _ _).mp h

/-- **Every computation has a query bound** when every oracle answers in a finite type: a
computation is a finitely branching tree of finite depth. -/
theorem exists_isTotalQueryBound {ι : Type} {spec : OracleSpec.{0, 0} ι}
    [∀ t, Fintype (spec.Range t)] {α : Type} (oa : OracleComp spec α) :
    ∃ n, IsTotalQueryBound oa n := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure x => exact ⟨0, trivial⟩
  | query_bind t k ih =>
    choose n hn using ih
    refine ⟨Finset.univ.sup n + 1, isTotalQueryBound_query_bind_iff.mpr ⟨Nat.succ_pos _,
      fun u ↦ (hn u).mono ?_⟩⟩
    rw [Nat.add_sub_cancel]
    exact Finset.le_sup (Finset.mem_univ u)

end

end LeanerVM.Protocol
