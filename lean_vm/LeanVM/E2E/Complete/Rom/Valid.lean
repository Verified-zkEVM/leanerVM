/-
  LeanVM.E2E.Complete.Rom.Valid

  T6-prob: valid-tree generators — their outputs' size, shape, prover queries, validity and
  limits — and the inhabitant, the leanXMSS leaf generator.
-/

module

public import LeanVM.E2E.Complete.Rom.CompCount
public import LeanVM.E2E.Complete.Rom.Gen

/-!
# Valid generators

`docs/roadmap/t6-prob.md` §4.5, §4.6. `ValidGen ρ pfuel N QP gen`: on the generator's own support
the prover's queries on its trees are within `QP`; on every run against the lazy oracle its tree has
at most `N` nodes, the shape `ShapeOK` at every node, and is valid and within the limits at every
hash agreeing with the log. It is `ValidGenOf ρ pfuel (HonestTree.proverQueries ρ pfuel)
(HonestTree.AllNodes HonestTree.ShapeOK)` of `Rom/EndOf.lean`, verbatim.

A leaf is within the limits of the H-oblivious prover when it is within the deployed limits and
the budget at the leaf's deferred claim and hints (`withinLimitsN_leaf`); the leanXMSS leaf
generator is valid (`validGen_xmssLeafGen`), its prover's queries `xmssLeafQueries pfuel`.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Blake2sHash LeanVM.Node LeanVM.Guest LeanVM.Protocol.LeanIsa
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom LeanVM.E2E
open OracleSpec OracleComp

@[expose] public section

/-- **A valid-tree generator**: the prover's queries on its trees within `QP`; its trees of at
most `N` nodes, of the shape, valid and within the limits at every hash agreeing with its log. -/
def ValidGen (ρ pfuel N QP : ℕ) (gen : OracleComp HashSpec (Option HonestTree)) : Prop :=
  (∀ T, some T ∈ support gen → T.proverQueries ρ pfuel ≤ QP) ∧
  ∀ z ∈ support ((simulateQ loggedRO gen).run []), ∀ T, z.1 = some T →
    T.size ≤ N ∧ T.AllNodes HonestTree.ShapeOK ∧
      ∀ Ht : Bytes → Digest, (∀ x u, look z.2 x = some u → Ht x = u) →
        T.Valid Ht ∧ T.WithinLimitsN Ht ρ pfuel

/-- **A leaf within the deployed limits and the budget** at its deferred claim and hints is within
the H-oblivious prover's limits. -/
theorem withinLimitsN_leaf (H : Bytes → Digest) (ρ pfuel : ℕ) {c : Claims}
    {xs : List (Holder LeanXmss.Signature)} {ss : List (Holder Sphincs.Signature)}
    {ds : List (Holder Da.Witness)}
    (h : End.Limits ⟨c, leafDefer⟩ ⟨[], xs, ss, ds, noHints⟩ ∧
      B2C.b2cBudget'.size (End.work ⟨c, leafDefer⟩ ⟨[], xs, ss, ds, noHints⟩) ≤ 2 ^ 28) :
    (HonestTree.node c xs ss ds []).WithinLimitsN H ρ pfuel := by
  rw [HonestTree.WithinLimitsN, HonestTree.allNodes_node]
  refine ⟨?_, fun k hk ↦ absurd hk List.not_mem_nil⟩
  intro kos hkos hd hdef
  have h0 : kidOutsN H ρ pfuel [] = .ok [] := rfl
  rw [h0] at hkos
  cases hkos
  have h1 : honestDeferN H (([] : List HonestOutN).map HonestOutN.child) =
      Except.ok (noHints, leafDefer) := by
    simp [honestDeferN]
  rw [h1] at hdef
  cases hdef
  exact h

/-- **The leanXMSS leaf's prover queries**: its node's own (no batching, one leanXMSS
verification), V°'s proof and the fresh claims' run. -/
def xmssLeafQueries (pfuel : ℕ) : ℕ :=
  7 + (2 + (5 + xmssVerifyBound + (1 + 3 * 22 + 3 * (2 * blake2sR1csLogSize)))) + 3 +
    2 * (leanVmCost * proverFactor costHeight pfuel)

theorem proverQueries_xmssLeaf (ρ pfuel : ℕ) (pk : LeanXmss.PublicKey) (σ : LeanXmss.Signature) :
    (xmssLeaf pk σ).proverQueries ρ pfuel = xmssLeafQueries pfuel := by
  rw [xmssLeaf, HonestTree.proverQueries_node]
  simp only [List.attach_nil, List.map_nil, List.sum_nil, List.length_nil, nodeOwnQueries,
    deferQueries, ↓reduceIte, checksQueries, holdersQueries, Hints.direct, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, zero_mul, xmssLeafQueries]
  omega

/-- The leanXMSS leaf has the shape at every node. -/
theorem shapeOK_xmssLeaf (pk : LeanXmss.PublicKey) (σ : LeanXmss.Signature) :
    (xmssLeaf pk σ).AllNodes HonestTree.ShapeOK := by
  rw [xmssLeaf, HonestTree.allNodes_node]
  refine ⟨⟨by simp, by simp, by simp [Hints.direct], fun dw hdw ↦ absurd hdw List.not_mem_nil⟩,
    fun k hk ↦ absurd hk List.not_mem_nil⟩

/-- **The leanXMSS leaf generator is valid**: leaves, of the prover's queries
`xmssLeafQueries pfuel`, valid and within the limits at every hash agreeing with its log. -/
theorem validGen_xmssLeafGen (ρ pfuel : ℕ) :
    ValidGen ρ pfuel 1 (xmssLeafQueries pfuel) xmssLeafGen := by
  refine ⟨fun T hT ↦ ?_, fun z hz T hT ↦ ?_⟩
  · simp only [xmssLeafGen, support_map, Set.mem_image] at hT
    obtain ⟨r, -, hr⟩ := hT
    rcases r with _ | ⟨pk, σ⟩
    · cases hr
    · cases hr
      exact (proverQueries_xmssLeaf ρ pfuel pk σ).le
  · obtain ⟨pk, σ, rfl, hv⟩ := xmssLeafGen_spec z hz T hT
    exact ⟨xmssLeaf_size pk σ, shapeOK_xmssLeaf pk σ, fun Ht hHt ↦
      ⟨hv Ht hHt, withinLimitsN_leaf Ht ρ pfuel (xmssLeaf_limits pk σ)⟩⟩

end
end LeanVM.E2E.Complete
