/-
  LeanVM.E2E.Complete.Rom.RootGen

  T6-prob's two-level inhabitant: a root holding the leanXMSS leaf's claim through the leaf, its
  one child. The batching, the children's decoding and the stack-log floor are exercised.
-/

module

public import LeanVM.E2E.Complete.Rom.LimitsT
public import LeanVM.E2E.Complete.Rom.RootBudget

/-!
# The two-level inhabitant

`xmssRootGen`: the leaf generator `xmssLeafGen` (honest leanXMSS key generation, one signature),
its leaf wrapped in a root holding the same claim `(pk, 0)` through child `0` (`rootOver`,
`xmssRoot pk σ`). Its outputs are trees of two nodes, valid at every hash agreeing with the
oracle's log (`xmssRootGen_spec`), within the limits on the tree (`limitsT_xmssRoot`; the root's
budget at its work `⟨1, 1, 0, 0, 0, 0, 1, 1⟩`, `RootBudget.lean`), their children leaves; the
prover's queries at most `2 · nodeQueries pfuel` (`proverQueries_le`). So the generator is valid
(`validGenT_xmssRootGen`, `validGen_xmssRootGen`) and, at rate `1`, fuel `2^25` and V_I's fuel
`2`, the completeness error is at most `2^-124` (**`idealVerify_complete_rom_xmssRoot`**).
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Node LeanVM.Guest
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.Rom LeanVM.E2E OracleComp OracleSpec
open scoped ENNReal

@[expose] public section

/-! ## The generator -/

/-- **A root over a tree**: the tree's claims, each held through child `0`, the tree its one
child. -/
def rootOver (T : HonestTree) : HonestTree :=
  .node T.claims (T.claims.xmss.map fun _ ↦ .child 0) (T.claims.sphincs.map fun _ ↦ .child 0)
    (T.claims.da.map fun _ ↦ .child 0) [T]

/-- **The root over the leanXMSS leaf.** -/
def xmssRoot (pk : LeanXmss.PublicKey) (σ : LeanXmss.Signature) : HonestTree :=
  .node ⟨[(pk, 0)], [], []⟩ [.child 0] [] [] [xmssLeaf pk σ]

theorem rootOver_xmssLeaf (pk : LeanXmss.PublicKey) (σ : LeanXmss.Signature) :
    rootOver (xmssLeaf pk σ) = xmssRoot pk σ := rfl

/-- **The two-level generator**: the leaf generator's leaf, under a root. -/
noncomputable def xmssRootGen : OracleComp HashSpec (Option HonestTree) :=
  (fun r ↦ r.map rootOver) <$> xmssLeafGen

/-! ## Its outputs -/

/-- A mapped generator's runs are the generator's, mapped. -/
theorem mem_support_run_map {α β : Type} (f : α → β) (gen : OracleComp HashSpec α)
    {z : β × Log} (hz : z ∈ support ((simulateQ loggedRO (f <$> gen)).run [])) :
    ∃ z0 ∈ support ((simulateQ loggedRO gen).run []), z = (f z0.1, z0.2) := by
  rw [simulateQ_map, StateT.run_map, support_map] at hz
  obtain ⟨z0, hz0, rfl⟩ := hz
  exact ⟨z0, hz0, rfl⟩

/-- **The root over a valid leanXMSS leaf is valid.** -/
theorem valid_xmssRoot {H : Bytes → Digest} {pk : LeanXmss.PublicKey} {σ : LeanXmss.Signature}
    (h : (xmssLeaf pk σ).Valid H) : (xmssRoot pk σ).Valid H := by
  refine ⟨?_, fun c hc ↦ absurd hc List.not_mem_nil⟩
  rw [xmssRoot, HonestTree.allNodes_node]
  refine ⟨⟨.cons ⟨claimChild ⟨[(pk, 0)], [], []⟩, rfl, List.mem_singleton_self _⟩ .nil, .nil, .nil⟩,
    fun k hk ↦ ?_⟩
  rw [List.mem_singleton.mp hk]
  exact h.1

/-- **The generator's outputs are roots over leanXMSS leaves, valid at every hash agreeing with
its log.** -/
theorem xmssRootGen_spec :
    ∀ z ∈ support ((simulateQ loggedRO xmssRootGen).run []), ∀ T, z.1 = some T →
      ∃ pk σ, T = xmssRoot pk σ ∧
        ∀ Ht : Bytes → Digest, (∀ x u, look z.2 x = some u → Ht x = u) → T.Valid Ht := by
  intro z hz T hT
  obtain ⟨z0, hz0, rfl⟩ := mem_support_run_map _ xmssLeafGen hz
  simp only [Option.map_eq_some_iff] at hT
  obtain ⟨T0, hT0, rfl⟩ := hT
  obtain ⟨pk, σ, rfl, hv⟩ := xmssLeafGen_spec z0 hz0 T0 hT0
  exact ⟨pk, σ, rfl, fun Ht hHt ↦ valid_xmssRoot (hv Ht hHt)⟩

theorem xmssRoot_size (pk : LeanXmss.PublicKey) (σ : LeanXmss.Signature) :
    (xmssRoot pk σ).size = 2 := by
  simp [xmssRoot, xmssLeaf, HonestTree.size]

theorem shapeOK_xmssRoot (pk : LeanXmss.PublicKey) (σ : LeanXmss.Signature) :
    (xmssRoot pk σ).AllNodes HonestTree.ShapeOK := by
  rw [xmssRoot, HonestTree.allNodes_node]
  refine ⟨⟨by simp, by simp, by simp [Hints.direct], fun dw hdw ↦ absurd hdw List.not_mem_nil⟩,
    fun k hk ↦ ?_⟩
  rw [List.mem_singleton.mp hk]
  exact shapeOK_xmssLeaf pk σ

theorem kidsLeaves_xmssRoot (pk : LeanXmss.PublicKey) (σ : LeanXmss.Signature) :
    (xmssRoot pk σ).AllNodes HonestTree.KidsLeaves := by
  rw [xmssRoot, HonestTree.allNodes_node]
  refine ⟨fun k hk ↦ ⟨_, _, _, _, List.mem_singleton.mp hk⟩, fun k hk ↦ ?_⟩
  rw [List.mem_singleton.mp hk, xmssLeaf, HonestTree.allNodes_node]
  exact ⟨fun k hk ↦ absurd hk List.not_mem_nil, fun k hk ↦ absurd hk List.not_mem_nil⟩

/-! ## The limits on the tree -/

/-- **The leaf within the limits on the tree.** -/
theorem limitsT_xmssLeaf (pk : LeanXmss.PublicKey) (σ : LeanXmss.Signature) :
    (xmssLeaf pk σ).LimitsT := by
  intro cs hd hcs _
  have hc : cs = [] := List.map_eq_nil_iff.mp hcs
  subst hc
  have hcov : End.coverage ⟨⟨[(pk, 0)], [], []⟩, hd.2⟩ ⟨[], [.direct σ], [], [], hd.1⟩ = 1 := by
    simp [End.coverage, Hints.plan, Hints.direct, Hints.takeSlots, Hints.takeSlot,
      Hints.takeSlotsAll]
  have hwork : End.work ⟨⟨[(pk, 0)], [], []⟩, hd.2⟩ ⟨[], [.direct σ], [], [], hd.1⟩ =
      End.work ⟨⟨[(pk, 0)], [], []⟩, leafDefer⟩ ⟨[], [.direct σ], [], [], noHints⟩ := by
    have hcov' : End.coverage ⟨⟨[(pk, 0)], [], []⟩, leafDefer⟩ ⟨[], [.direct σ], [], [], noHints⟩ =
        1 := by
      simp [End.coverage, Hints.plan, Hints.direct, Hints.takeSlots, Hints.takeSlot,
        Hints.takeSlotsAll]
    simp only [End.work, hcov, hcov']
  refine ⟨{ stackLog := fun c hc ↦ absurd hc List.not_mem_nil
            stream := fun c hc ↦ absurd hc List.not_mem_nil
            directDa := Nat.zero_le _
            xmssHeld := fun x ↦ by simp [Hints.direct]
            sphincsHeld := fun x ↦ by simp
            daHeld := fun x ↦ by simp
            children := Nat.zero_le _
            daRoots := ⟨Nat.zero_le _, fun c hc ↦ absurd hc List.not_mem_nil⟩
            lists := fun c hc ↦ absurd hc List.not_mem_nil
            coverage := by rw [hcov]; norm_num
            nonempty := Nat.one_pos }, ?_⟩
  rw [hwork]
  exact (xmssLeaf_limits pk σ).2

/-- **The root within the limits on the tree.** -/
theorem limitsT_xmssRoot (pk : LeanXmss.PublicKey) (σ : LeanXmss.Signature) :
    (xmssRoot pk σ).LimitsT := by
  intro cs hd hcs hk
  obtain ⟨c, rfl, hcc⟩ : ∃ c, cs = [c] ∧ c.statement.claims = ⟨[(pk, 0)], [], []⟩ := by
    rcases cs with _ | ⟨c, _ | ⟨c', cs'⟩⟩
    · simp at hcs
    · exact ⟨c, rfl, by simpa [xmssRoot, xmssLeaf, HonestTree.claims] using hcs⟩
    · simp at hcs
  have hk1 := hk c (List.mem_singleton_self c)
  have hcov : End.coverage ⟨⟨[(pk, 0)], [], []⟩, hd.2⟩ ⟨[c], [.child 0], [], [], hd.1⟩ = 1 := by
    simp [End.coverage, hcc, Hints.plan, Hints.direct, Hints.takeSlots, Hints.takeSlot,
      Hints.takeSlotsAll]
  have hwork : End.work ⟨⟨[(pk, 0)], [], []⟩, hd.2⟩ ⟨[c], [.child 0], [], [], hd.1⟩ =
      ⟨1, 1, 0, 0, 0, 0, 1, 1⟩ := by
    rw [End.work, hcov]
    simp [hcc, Hints.direct]
  refine ⟨{ stackLog := fun c' hc' ↦ by rw [List.mem_singleton.mp hc']; exact hk1.1
            stream := fun c' hc' ↦ by rw [List.mem_singleton.mp hc']; exact hk1.2
            directDa := by simp [Hints.direct]
            xmssHeld := fun x ↦ by simp [hcc]
            sphincsHeld := fun x ↦ by simp
            daHeld := fun x ↦ by simp
            children := by simp
            daRoots := ⟨by simp, fun c' hc' ↦ by rw [List.mem_singleton.mp hc', hcc]; simp⟩
            lists := fun c' hc' ↦ by rw [List.mem_singleton.mp hc', hcc]; simp
            coverage := by rw [hcov]; norm_num
            nonempty := by simp }, ?_⟩
  rw [hwork]
  exact budget_rootWork

theorem limitsT_all_xmssRoot (pk : LeanXmss.PublicKey) (σ : LeanXmss.Signature) :
    (xmssRoot pk σ).AllNodes HonestTree.LimitsT := by
  rw [xmssRoot, HonestTree.allNodes_node]
  refine ⟨limitsT_xmssRoot pk σ, fun k hk ↦ ?_⟩
  rw [List.mem_singleton.mp hk, xmssLeaf, HonestTree.allNodes_node]
  exact ⟨limitsT_xmssLeaf pk σ, fun k hk ↦ absurd hk List.not_mem_nil⟩

/-! ## The generator is valid -/

/-- **The two-level generator is valid, the limits on the tree**: trees of two nodes, the
prover's queries at most `2 · nodeQueries pfuel`. -/
theorem validGenT_xmssRootGen (ρ pfuel : ℕ) :
    ValidGenT ρ pfuel 2 (2 * nodeQueries pfuel) xmssRootGen := by
  refine ⟨fun T hT ↦ ?_, fun z hz T hT ↦ ?_⟩
  · simp only [xmssRootGen, support_map, Set.mem_image] at hT
    obtain ⟨r, hr, hrT⟩ := hT
    rcases r with _ | T0
    · cases hrT
    · cases hrT
      simp only [xmssLeafGen, support_map, Set.mem_image] at hr
      obtain ⟨r', -, hr'⟩ := hr
      rcases r' with _ | ⟨pk, σ⟩
      · cases hr'
      · cases hr'
        rw [rootOver_xmssLeaf]
        have := proverQueries_le ρ pfuel _ (shapeOK_xmssRoot pk σ)
        rwa [xmssRoot_size] at this
  · obtain ⟨pk, σ, rfl, hv⟩ := xmssRootGen_spec z hz T hT
    exact ⟨(xmssRoot_size pk σ).le, shapeOK_xmssRoot pk σ, limitsT_all_xmssRoot pk σ,
      kidsLeaves_xmssRoot pk σ, hv⟩

/-- **The two-level generator is valid.** -/
theorem validGen_xmssRootGen {ρ : ℕ} (hρ : validRate ρ) (pfuel : ℕ) :
    ValidGen ρ pfuel 2 (2 * nodeQueries pfuel) xmssRootGen :=
  validGen_of_T hρ (validGenT_xmssRootGen ρ pfuel)

/-- **The two-level generator's queries**: the leaf generator's. -/
theorem isTotalQueryBound_xmssRootGen :
    IsTotalQueryBound xmssRootGen (E2E.xmssKeygenBound + E2E.xmssSignBound) := by
  unfold xmssRootGen
  rw [map_eq_bind_pure_comp]
  exact (isTotalQueryBound_bind (n₂ := 0) isTotalQueryBound_xmssLeafGen
    fun _ ↦ isQueryBound_pure _ _ _ _).mono (Nat.add_zero _).le

/-- The generator and the prover make fewer than `2^64` queries at the fuel `2^25`. -/
theorem xmssRoot_queries_le :
    E2E.xmssKeygenBound + E2E.xmssSignBound + 2 * nodeQueries (2 ^ 25) ≤ 2 ^ 64 := by
  rw [xmssLeafGen_queries_eq, nodeQueries_eq]
  norm_num

/-- **T6-prob on a two-level tree**: for the root over the honest leanXMSS leaf, at rate `1`, a
proof-of-work fuel of `2^25` nonces and V_I's fuel `2`, the bad outcome (the prover fails, or V_I
rejects at some hash agreeing with the log) has probability at most `2^-124`. -/
theorem idealVerify_complete_rom_xmssRoot :
    Pr{let z ← completeExp 1 (2 ^ 25) xmssRootGen}[¬ CompleteOK 2 z] ≤ (2 : ℝ≥0∞)⁻¹ ^ 124 :=
  (idealVerify_complete_rom hyps_wTree.1 (by norm_num) xmssRootGen isTotalQueryBound_xmssRootGen
    (validGen_xmssRootGen hyps_wTree.1 (2 ^ 25)) le_rfl).trans
    (completeError_le xmssRoot_queries_le)

end
end LeanVM.E2E.Complete
