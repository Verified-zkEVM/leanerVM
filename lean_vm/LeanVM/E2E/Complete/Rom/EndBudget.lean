/-
  LeanVM.E2E.Complete.Rom.EndBudget

  T6-prob for the game's V_I: the honest proof of a generated tree is accepted by V_I run with
  the game's budgeted hash, on `N` nodes with a budget of at least `N · viNodeBound`, against the
  same lazily sampled oracle, except with probability `completeError`.
-/

module

public import LeanVM.E2E.Complete.Rom.End
public import LeanVM.E2E.Complete.Rom.ViCost
public import LeanVM.E2E.Bridge

/-!
# T6-prob with the game's budget

The soundness game (`gameComp`) runs V_I with `budgetedQuery budget`, a hash query of the game's
oracle while fewer than `budget` were made and a rejection past it, on `fuel` nodes from the
signers' state. `idealVerify_complete_rom` is about V_I without a budget. Here V_I runs as the
game runs it:

* **the experiment** `completeRunGame ρ pfuel gen fuel budget`: the generator and the honest
  prover against the lazily sampled oracle (`completeExp`), then V_I on the prover's output with
  `budgetedQuery budget` on `fuel` nodes from the signers' initial state (`verifyStageB`), its
  queries answered by the game's oracle (`gameImpl`: coins forwarded, the hash `Rom.loggedRO`)
  continuing the same log; a failed prover, or V_I's rejection or a run past the budget, is
  `some false`;
* **the exact run** (`exactRel_idealVerify`): every outcome of V_I's budgeted run extends the log,
  and at every hash agreeing with its final log it is V_I's counted run with that hash charged
  against the budget (`charge`): V_I's `Id` run when its query count fits;
* **the count** (`queryCount_honest_le_mul`): at every such hash the honest proof's count is at
  most `N · viNodeBound`.

So **`idealVerify_complete_rom_budget`**: for a valid generator of trees of at most `N` nodes
(`ValidGen`), V_I on `N` nodes with a budget of at least `N · viNodeBound` rejects the honest
proof with probability at most `completeError (QG + QP) pfuel`, the bound of
`idealVerify_complete_rom`.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Node LeanVM.Guest
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.Rom LeanVM.E2E OracleComp OracleSpec
open scoped ENNReal

@[expose] public section

variable {nx ns : ℕ}

/-! ## The exact run -/

/-- **The budgeted run is the charged count**: every run of `x` against the game's oracle
extends its log, and at every hash `H` agreeing with the final log its outcome is the charge of
the counted computation `y` (with `H`) against the budget. -/
def ExactRel (H : Bytes → Digest) (budget : ℕ) {α : Type} (x : OptionT (GameM nx ns) α)
    (y : Counted α) : Prop :=
  ∀ (st : SignState nx ns) (ℓ : Log), ∀ p ∈ support (runG x st ℓ),
    ℓ <+: p.2 ∧ (Agrees p.2 H → p.1 = Id.run (((charge (b := Id) budget y).run).run st))

theorem exactRel_pure (H : Bytes → Digest) (budget : ℕ) {α : Type} (a : α) :
    ExactRel (nx := nx) (ns := ns) H budget (pure a) (pure a) := by
  intro st ℓ p hp
  rw [runG_pure, support_pure, Set.mem_singleton_iff] at hp
  subst hp
  refine ⟨List.prefix_refl _, fun _ ↦ ?_⟩
  rw [(isMorphism_charge (b := Id) budget).pure]
  rfl

theorem exactRel_bind (H : Bytes → Digest) (budget : ℕ) {α β : Type}
    (x : OptionT (GameM nx ns) α) (y : Counted α) (f : α → OptionT (GameM nx ns) β)
    (g : α → Counted β) (hx : ExactRel H budget x y) (hf : ∀ a, ExactRel H budget (f a) (g a)) :
    ExactRel H budget (x >>= f) (y >>= g) := by
  intro st ℓ p hp
  obtain ⟨⟨⟨q1, q2⟩, qℓ⟩, hq, hpq⟩ := mem_support_runG_bind hp
  obtain ⟨hℓq, hxq⟩ := hx st ℓ _ hq
  rw [(isMorphism_charge (b := Id) budget).bind, OptionT.run_bind, Option.elimM, StateT.run_bind]
  rcases hpq with ⟨hnone, rfl⟩ | ⟨a, ha, hp'⟩
  · refine ⟨hℓq, fun hag ↦ ?_⟩
    have hq1 := hxq hag
    generalize ((charge (b := Id) budget y).run).run st = c at hq1 ⊢
    obtain ⟨c1, c2⟩ := c
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq1
    simp only at hnone
    subst hnone
    rfl
  · obtain ⟨hqp, hfp⟩ := hf a q2 qℓ p hp'
    refine ⟨hℓq.trans hqp, fun hag ↦ ?_⟩
    have hq1 := hxq fun x u hx ↦ hag x u (look_of_prefix hqp hx)
    generalize ((charge (b := Id) budget y).run).run st = c at hq1 ⊢
    obtain ⟨c1, c2⟩ := c
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq1
    simp only at ha
    subst ha
    exact hfp hag

/-- **A budgeted query is the charge of one counted query.** -/
theorem exactRel_budgetedQuery (H : Bytes → Digest) (budget : ℕ) (x : Bytes) :
    ExactRel (nx := nx) (ns := ns) H budget (budgetedQuery budget x) (countQuery H x) := by
  intro st ℓ p hp
  unfold runG at hp
  rw [run_charge]
  by_cases hb : budget ≤ st.spent
  · rw [run_budgetedQuery_of_le hb] at hp
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    refine ⟨List.prefix_refl _, fun _ ↦ ?_⟩
    have : ¬ (1 = 0 ∨ st.spent + 1 ≤ budget) := by omega
    simp only [count_countQuery, this, ↓reduceIte, Nat.max_eq_left hb]
    rfl
  · rw [run_budgetedQuery_of_lt hb, simulateQ_map, StateT.run_map, simulateQ_spec_query,
      support_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    obtain ⟨hpre, hlook⟩ := mem_support_gameImpl_hash hq
    refine ⟨hpre, fun hag ↦ ?_⟩
    have : 1 = 0 ∨ st.spent + 1 ≤ budget := by omega
    simp only [count_countQuery, this, ↓reduceIte, val_countQuery, hag x q.1 hlook]
    rfl

/-- **V_I's budgeted run is its charged count** at every hash agreeing with the final log. -/
theorem exactRel_idealVerify (H : Bytes → Digest) (budget : ℕ) (prog : Program)
    (ip : IdealProof) (fuel : ℕ) (s : NodeStatement) :
    ExactRel (nx := nx) (ns := ns) H budget (idealVerify (budgetedQuery budget) prog ip fuel s)
      (idealVerify (countQuery H) prog ip fuel s) :=
  rel_idealVerify (fun x y ↦ ExactRel H budget x y) (exactRel_pure H budget)
    (exactRel_bind H budget) _ _ (exactRel_budgetedQuery H budget) prog ip fuel s

/-- **An outcome of V_I's budgeted run**, within the budget at the hash its final log fills:
V_I's `Id` run with that hash. -/
theorem budgeted_run_eq {budget : ℕ} {prog : Program} {ip : IdealProof} {fuel : ℕ}
    {s : NodeStatement} {st : SignState nx ns} {ℓ : Log} {p : (Option Bool × SignState nx ns) × Log}
    (hp : p ∈ support (runG (idealVerify (budgetedQuery budget) prog ip fuel s) st ℓ))
    (hb : st.spent + queryCount (fillLog p.2) prog ip fuel s ≤ budget) :
    ℓ <+: p.2 ∧ p.1.1 = some (Id.run (idealVerify (fun x ↦ (pure (fillLog p.2 x) : Id Digest))
      prog ip fuel s)) := by
  obtain ⟨hpre, hex⟩ := exactRel_idealVerify (fillLog p.2) budget prog ip fuel s st ℓ p hp
  refine ⟨hpre, ?_⟩
  rw [hex (agrees_fillLog p.2), run_charge]
  have : (idealVerify (countQuery (fillLog p.2)) prog ip fuel s).count = 0 ∨
      st.spent + (idealVerify (countQuery (fillLog p.2)) prog ip fuel s).count ≤ budget :=
    Or.inr hb
  simp only [this, ↓reduceIte]
  exact congrArg some (val_idealVerify_counted _ prog ip fuel s)

/-! ## The experiment -/

variable (ρ pfuel : ℕ)

/-- **V_I on the prover's output as the game runs it**: with the game's budgeted hash, on `fuel`
nodes; a run past the budget, a rejection or a failed prover is `some false`. -/
noncomputable def verifyStageB (fuel budget : ℕ) :
    Option (HonestTree × Except ProverFail HonestOutN) → GameM nx ns (Option Bool)
  | some (_, .ok o) => do
    let v ← (idealVerify (budgetedQuery budget) guest (idealOfN o) fuel o.stmt).run
    pure (some (v.getD false))
  | some (_, .error _) => pure (some false)
  | none => pure none

/-- **The completeness experiment with the game's V_I**: the generator and the honest prover
against the lazily sampled oracle, then V_I on the prover's output with the game's budgeted hash,
from the signers' initial state, against the game's oracle continuing the same log. -/
noncomputable def completeRunGame (gen : OracleComp HashSpec (Option HonestTree))
    (fuel budget : ℕ) : ProbComp (Option Bool × Log) :=
  completeExp ρ pfuel gen >>= fun a ↦
    (fun p ↦ (p.1.1, p.2)) <$>
      (simulateQ gameImpl ((verifyStageB (nx := nx) (ns := ns) fuel budget a.1).run
        (SignState.init nx ns))).run a.2

/-! ## The outcomes of the completeness experiment -/

/-- **What an outcome of the completeness experiment carries**: its tree is the generator's, of
at most `N` nodes and of the shape, and at every hash agreeing with its log the prover's output
is the H-oblivious prover's, and the tree is valid and within the limits. -/
theorem completeExp_facts {gen : OracleComp HashSpec (Option HonestTree)} {N QP : ℕ}
    (hgen : ValidGen ρ pfuel N QP gen) {a : Option (HonestTree × Except ProverFail HonestOutN) × Log}
    (ha : a ∈ support (completeExp ρ pfuel gen)) {T : HonestTree}
    {r : Except ProverFail HonestOutN} (h : a.1 = some (T, r)) :
    T.size ≤ N ∧ T.AllNodes HonestTree.ShapeOK ∧
      ∀ Ht : Bytes → Digest, (∀ x u, look a.2 x = some u → Ht x = u) →
        honestOutN Ht ρ pfuel T = r ∧ T.Valid Ht ∧ T.WithinLimitsN Ht ρ pfuel := by
  unfold completeExp genProve at ha
  rw [run_simulateQ_bind] at ha
  obtain ⟨z1, hz1, hz⟩ := (mem_support_bind_iff _ _ _).mp ha
  obtain ⟨hpre, -⟩ := simulateQ_look_of_mem_support _ _ a hz
  obtain ⟨g, ℓ1⟩ := z1
  cases g with
  | none =>
    simp at hz
    subst hz
    cases h
  | some T' =>
    obtain ⟨hsize, hsh, hval⟩ := hgen.2 _ hz1 T' rfl
    have hlook := (simulateQ_look_of_mem_support _ _ a hz).2 a.2 (List.prefix_refl _)
    rw [simulateQ_map] at hlook
    obtain ⟨r', hr', hzr⟩ := Option.map_eq_some_iff.mp hlook
    rw [h] at hzr
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hzr)
    exact ⟨hsize, hsh, fun Ht hH ↦ ⟨honestProverComp_look ρ pfuel hr' Ht hH,
      hval Ht (agrees_of_prefix hpre hH)⟩⟩

/-! ## T6-prob with the game's budget -/

/-- **V_I, run with the game's budget after the honest prover, rejects** (or the prover fails)
with at most the probability of the bad outcome, for a valid generator of trees of at most `N`
nodes, V_I on `N` nodes with a budget of at least `N · viNodeBound`. -/
theorem prEvent_rejectB_le_not_completeOK (hρ : validRate ρ)
    {gen : OracleComp HashSpec (Option HonestTree)} {N QP budget : ℕ}
    (hgen : ValidGen ρ pfuel N QP gen) (hB : N * viNodeBound ≤ budget) :
    Pr{let z ← completeRunGame (nx := nx) (ns := ns) ρ pfuel gen N budget}[z.1 = some false] ≤
      Pr{let z ← completeExp ρ pfuel gen}[¬ CompleteOK N z] := by
  unfold completeRunGame
  refine prEvent_bind_le_prEvent_of_support _ _ _ _ fun a ha hok ↦ ?_
  refine prEvent_eq_zero_of_forall_mem_support _ _ fun y hy hrej ↦ ?_
  have hok : CompleteOK N a := not_not.mp hok
  rw [support_map] at hy
  obtain ⟨p, hp, rfl⟩ := hy
  obtain ⟨g, ℓ⟩ := a
  rcases g with _ | ⟨T, r⟩
  · simp only [verifyStageB, StateT.run_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hp
    subst hp
    cases hrej
  · obtain ⟨o, rfl, -, hacc⟩ := hok T r rfl
    obtain ⟨hsize, hsh, hfacts⟩ := completeExp_facts ρ pfuel hgen ha (T := T) (r := .ok o) rfl
    simp only [verifyStageB, StateT.run_bind, simulateQ_bind, StateT.run_pure, simulateQ_pure,
      StateT.run_bind, support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    have hq' : q ∈ support (runG (idealVerify (budgetedQuery budget) guest (idealOfN o) N o.stmt)
        (SignState.init nx ns) ℓ) := hq
    have hag : ∀ x u, look ℓ x = some u → fillLog q.2 x = u := fun x u hx ↦
      agrees_fillLog q.2 x u (look_of_prefix
        (exactRel_idealVerify (fillLog q.2) budget guest (idealOfN o) N o.stmt _ ℓ q hq').1 hx)
    obtain ⟨hI, -, hlim⟩ := hfacts (fillLog q.2) hag
    have hcount := queryCount_honest_le_mul (fillLog q.2) ρ pfuel hρ hI hsh hlim hsize
    obtain ⟨-, hv⟩ := budgeted_run_eq hq' (by
      show 0 + _ ≤ _
      omega)
    rw [hacc (fillLog q.2) hag] at hv
    simp only [hv, Option.getD_some] at hrej
    cases hrej

/-- **T6-prob with the game's budget.** For every generator `gen` of valid honest trees within
the limits (`ValidGen`: at most `N` nodes, the prover's queries at most `QP`) with at most `QG`
queries, a valid rate and a proof-of-work fuel of at most `2^64` nonces: V_I, run after the
honest prover as the soundness game runs it (the game's budgeted hash, on `N` nodes, with a budget
of at least `N · viNodeBound`, against the same lazily sampled oracle), rejects the honest proof
(or the prover fails) with probability at most `completeError (QG + QP) pfuel`. -/
theorem idealVerify_complete_rom_budget {ρ pfuel N QG QP budget : ℕ} (hρ : validRate ρ)
    (hpf : pfuel ≤ 2 ^ 64) (gen : OracleComp HashSpec (Option HonestTree))
    (hQG : IsTotalQueryBound gen QG) (hgen : ValidGen ρ pfuel N QP gen)
    (hB : N * viNodeBound ≤ budget) :
    Pr{let z ← completeRunGame (nx := nx) (ns := ns) ρ pfuel gen N budget}[z.1 = some false] ≤
      completeError (QG + QP) pfuel :=
  (prEvent_rejectB_le_not_completeOK ρ pfuel hρ hgen hB).trans
    (idealVerify_complete_rom hρ hpf gen hQG hgen le_rfl)

end
end LeanVM.E2E.Complete
