/-
  LeanVM.E2E.Complete.Rom.EndOf

  T6-prob assembled over its pieces: the bridge from the oracle computation to the H-oblivious
  prover, the failure tags, the query bound and the valid generator, taken as hypotheses
  (`RomPieces`, `ValidGenOf`); `Rom/End.lean` discharges them.
-/

module

public import LeanVM.E2E.Complete.Rom.AssembleN
public import LeanVM.E2E.Complete.Rom.Comp
public import LeanVM.E2E.Complete.Rom.Bounds
public import LeanVM.E2E.Natural

/-!
# T6-prob, over its pieces

`docs/roadmap/t6-prob.md` §4.5. The experiment `completeExp`: a generator of honest trees, then the
honest prover of the random-oracle model (`honestProverComp`), against one lazily sampled oracle
(`Rom.loggedRO`). The good outcome `CompleteOK`: the prover outputs a statement with the tree's
claims and V_I accepts its idealized proof at every hash agreeing with the oracle's final log.

`idealVerify_complete_rom_of`: with the pieces (`RomPieces`: the prover at a log's answers is the
H-oblivious prover at every agreeing hash; its failures are tagged by a failed proof-of-work search
or vanishing weights on the log; the shapes of the weights' children) and a valid generator
(`ValidGenOf`), the bad outcome has probability at most `completeError (QG + QP) pfuel`. On a bad
outcome: an output is accepted (`idealVerify_complete_N`); `stuck` is impossible
(`honestOutN_ne_stuck`); a failed search makes `powPot ≥ 1` (`one_le_powPot_of_proveFromM`);
vanishing weights make `weightsPot ≥ 1` (`one_le_weightsPot`); `prEvent_le_completeError` sums.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Node LeanVM.Guest
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.Rom LeanVM.E2E OracleComp OracleSpec
open scoped ENNReal

@[expose] public section

variable (ρ pfuel : ℕ)

/-! ## The experiment -/

/-- The generator, then the honest prover on its tree. -/
noncomputable def genProve (gen : OracleComp HashSpec (Option HonestTree)) :
    OracleComp HashSpec (Option (HonestTree × Except ProverFail HonestOutN)) :=
  gen >>= fun g ↦ match g with
    | none => pure none
    | some T => (fun r ↦ some (T, r)) <$> honestProverComp ρ pfuel T

/-- **The completeness experiment**: `genProve` against one lazily sampled random oracle. -/
noncomputable def completeExp (gen : OracleComp HashSpec (Option HonestTree)) :
    ProbComp (Option (HonestTree × Except ProverFail HonestOutN) × Log) :=
  (simulateQ loggedRO (genProve ρ pfuel gen)).run []

/-- **The good outcome**: the prover outputs a statement with the tree's claims, and V_I accepts
its idealized proof at every hash agreeing with the oracle's final log. -/
def CompleteOK (fuel : ℕ) (z : Option (HonestTree × Except ProverFail HonestOutN) × Log) : Prop :=
  ∀ T r, z.1 = some (T, r) → ∃ o, r = .ok o ∧ o.stmt.claims = T.claims ∧
    ∀ Ht : Bytes → Digest, (∀ x u, look z.2 x = some u → Ht x = u) →
      idealVerify (m := Id) (fun x ↦ (pure (Ht x) : Id Digest)) guest (idealOfN o) fuel o.stmt =
        true

/-! ## The pieces -/

/-- **The pieces of T6-prob** that relate the oracle computation to the H-oblivious prover, for a
shape condition `Sh` of the trees. -/
structure RomPieces (Sh : HonestTree → Prop) : Prop where
  /-- The prover at a log's answers is the H-oblivious prover at every agreeing hash. -/
  lookEq : ∀ {ℓ : Log} {T : HonestTree} {r : Except ProverFail HonestOutN},
    simulateQ (lookImpl ℓ) (honestProverComp ρ pfuel T) = some r →
      ∀ Ht : Bytes → Digest, (∀ x u, look ℓ x = some u → Ht x = u) → honestOutN Ht ρ pfuel T = r
  /-- The prover at a log's answers is the prover with the hash the log. -/
  natural : ∀ (ℓ : Log) (T : HonestTree),
    simulateQ (lookImpl ℓ) (honestProverComp ρ pfuel T) = (honestProverM (look ℓ) ρ pfuel T).run
  /-- A failed search is a failed search on the hash's answers. -/
  grind : ∀ {L : Bytes → Option Digest} {T : HonestTree} {P : Prog Bool} {S : Strategy}
    {seed : Digest}, (honestProverM L ρ pfuel T).run = some (.error (.grind P S seed)) →
      (∃ pi, P = progOf pi) ∧ proveFromM L S pfuel P seed [] = some none
  /-- Vanishing weights vanish on the hash's answers. -/
  weights : ∀ {L : Bytes → Option Digest} {T : HonestTree} {cs : List ChildClaims},
    (honestProverM L ρ pfuel T).run = some (.error (.weights cs)) →
      cs ≠ [] ∧ ∃ rounds : List (E × E), rounds.length = Nat.log2 End.bytecode.length ∧
        weightsWith L B1.Main.aggSeedD cs rounds = some (0, 0)
  /-- The children of vanishing weights have the bytecode's shapes, at most `16` of them. -/
  shaped : validRate ρ → ∀ (H : Bytes → Digest) {T : HonestTree} {cs : List ChildClaims}, Sh T →
    honestOutN H ρ pfuel T = .error (.weights cs) →
      (∀ c ∈ cs, Guest.Batch.ChildShaped End.bytecode c) ∧ cs.length ≤ 16

/-- **A valid-tree generator**, for a query count `qb` of the prover and a shape `Sh`: on its
own support the prover's queries are within `QP`; on every run against the lazy oracle its tree
has at most `N` nodes, the shape, and is valid and within the limits at every hash agreeing with
the log. -/
def ValidGenOf (qb : HonestTree → ℕ) (Sh : HonestTree → Prop) (N QP : ℕ)
    (gen : OracleComp HashSpec (Option HonestTree)) : Prop :=
  (∀ T, some T ∈ support gen → qb T ≤ QP) ∧
  ∀ z ∈ support ((simulateQ loggedRO gen).run []), ∀ T, z.1 = some T →
    T.size ≤ N ∧ Sh T ∧
      ∀ Ht : Bytes → Digest, (∀ x u, look z.2 x = some u → Ht x = u) →
        T.Valid Ht ∧ T.WithinLimitsN Ht ρ pfuel

/-! ## The assembly -/

/-- The generator and the prover make at most `QG + QP` queries. -/
theorem isTotalQueryBound_genProve {gen : OracleComp HashSpec (Option HonestTree)} {QG QP : ℕ}
    (hQG : IsTotalQueryBound gen QG) (qb : HonestTree → ℕ)
    (hqb : ∀ T, IsTotalQueryBound (honestProverComp ρ pfuel T) (qb T))
    (hQP : ∀ T, some T ∈ support gen → qb T ≤ QP) :
    IsTotalQueryBound (genProve ρ pfuel gen) (QG + QP) := by
  refine isTotalQueryBound_bind_of_mem_support hQG fun g hg ↦ ?_
  cases g with
  | none => trivial
  | some T =>
    exact IsTotalQueryBound.mono ((isQueryBound_map_iff _ _ _ _ _).mpr (hqb T)) (hQP T hg)

/-- A hash agreeing with a log agrees with its prefixes. -/
theorem agrees_of_prefix {ℓ ℓ' : Log} (hp : ℓ <+: ℓ') {Ht : Bytes → Digest}
    (h : ∀ x u, look ℓ' x = some u → Ht x = u) : ∀ x u, look ℓ x = some u → Ht x = u :=
  fun x u hx ↦ h x u (look_of_prefix hp hx)

/-- The log's filled hash agrees with it. -/
theorem agrees_fillLog (ℓ : Log) : ∀ x u, look ℓ x = some u → fillLog ℓ x = u := by
  intro x u hx
  simp [fillLog, hx]

/-- **T6-prob over its pieces.** -/
theorem idealVerify_complete_rom_of {Sh : HonestTree → Prop} (hP : RomPieces ρ pfuel Sh)
    (hρ : validRate ρ) (hpf : pfuel ≤ 2 ^ 64) {gen : OracleComp HashSpec (Option HonestTree)}
    {QG QP N fuel : ℕ} (hQG : IsTotalQueryBound gen QG) (qb : HonestTree → ℕ)
    (hqb : ∀ T, IsTotalQueryBound (honestProverComp ρ pfuel T) (qb T))
    (hgen : ValidGenOf ρ pfuel qb Sh N QP gen) (hfuel : N ≤ fuel) :
    Pr{let z ← completeExp ρ pfuel gen}[¬ CompleteOK fuel z] ≤ completeError (QG + QP) pfuel := by
  refine prEvent_le_completeError (genProve ρ pfuel gen) hpf
    (isTotalQueryBound_genProve ρ pfuel hQG qb hqb hgen.1) (fun a ℓ ↦ ¬ CompleteOK fuel (a, ℓ))
    fun z hz hbad ↦ ?_
  -- the generator's run, then the prover's
  unfold genProve at hz
  rw [run_simulateQ_bind] at hz
  obtain ⟨z1, hz1, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
  obtain ⟨hpre, -⟩ := simulateQ_look_of_mem_support _ _ z hz
  obtain ⟨g, ℓ1⟩ := z1
  cases g with
  | none =>
    simp at hz
    subst hz
    exact absurd (fun T r h ↦ by cases h) hbad
  | some T =>
    obtain ⟨hsize, hsh, hval⟩ := hgen.2 _ hz1 T rfl
    have hlook := (simulateQ_look_of_mem_support _ _ z hz).2 z.2 (List.prefix_refl _)
    rw [simulateQ_map] at hlook
    obtain ⟨r, hr, hzr⟩ := Option.map_eq_some_iff.mp hlook
    have hagree : ∀ Ht : Bytes → Digest, (∀ x u, look z.2 x = some u → Ht x = u) →
        honestOutN Ht ρ pfuel T = r := fun Ht hH ↦ hP.lookEq hr Ht hH
    have hvalid : ∀ Ht : Bytes → Digest, (∀ x u, look z.2 x = some u → Ht x = u) →
        T.Valid Ht ∧ T.WithinLimitsN Ht ρ pfuel := fun Ht hH ↦ hval Ht (agrees_of_prefix hpre hH)
    set H₀ := fillLog z.2
    have h₀ := agrees_fillLog z.2
    match r, hr, hagree with
    | .ok o, _, hagree =>
      exfalso
      refine hbad fun T' r' h' ↦ ?_
      rw [← hzr] at h'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h')
      refine ⟨o, rfl, (idealVerify_complete_N H₀ ρ pfuel T hρ (hagree H₀ h₀)
        (hsize.trans hfuel) (hvalid H₀ h₀).1.2).1, fun Ht hH ↦ ?_⟩
      exact (idealVerify_complete_N Ht ρ pfuel T hρ (hagree Ht hH) (hsize.trans hfuel)
        (hvalid Ht hH).1.2).2
    | .error .stuck, _, hagree =>
      exact absurd (hagree H₀ h₀) (honestOutN_ne_stuck H₀ ρ pfuel hρ T (hvalid H₀ h₀).1.1
        (hvalid H₀ h₀).2)
    | .error (.grind P S seed), hr, _ =>
      rw [hP.natural] at hr
      obtain ⟨⟨pi, rfl⟩, hnone⟩ := hP.grind hr
      exact (one_le_powPot_of_proveFromM (grind17_blindProgram _ _) hnone).trans le_self_add
    | .error (.weights cs), hr, hagree =>
      have hshp := hP.shaped hρ H₀ hsh (hagree H₀ h₀)
      rw [hP.natural] at hr
      obtain ⟨hne, rounds, hlen, hw⟩ := hP.weights hr
      exact (one_le_weightsPot ⟨rounds, hlen, hw⟩ hne hshp.1 hshp.2).trans le_add_self

/-! ## V_I run lazily after the prover -/

/-- V_I on the prover's output, every hash a query; a failed prover rejects. -/
noncomputable def verifyStage (fuel : ℕ) :
    Option (HonestTree × Except ProverFail HonestOutN) → OracleComp HashSpec (Option Bool)
  | some (_, .ok o) => some <$> idealVerify queryH guest (idealOfN o) fuel o.stmt
  | some (_, .error _) => pure (some false)
  | none => pure none

/-- **The experiment with V_I**: the generator, the honest prover, then V_I on its output, all
against one lazily sampled random oracle. -/
noncomputable def completeRunVI (gen : OracleComp HashSpec (Option HonestTree)) (fuel : ℕ) :
    ProbComp (Option Bool × Log) :=
  (simulateQ loggedRO (genProve ρ pfuel gen >>= verifyStage fuel)).run []

/-- Simulating every query by a total hash is a monad morphism into `Id`. -/
theorem isMorphism_simulateQ_id (Ht : Bytes → Digest) :
    IsMorphism (m := OracleComp HashSpec) (n := Id)
      (fun {α : Type} (x : OracleComp HashSpec α) ↦
        simulateQ (fun x ↦ (pure (Ht x) : Id Digest)) x) where
  pure a := simulateQ_pure _ a
  bind x f := simulateQ_bind _ x f

/-- **V_I, run lazily after the honest prover, rejects** (or the prover fails) with at most the
probability of the bad outcome. -/
theorem prEvent_reject_le_not_completeOK (gen : OracleComp HashSpec (Option HonestTree))
    (fuel : ℕ) :
    Pr{let z ← completeRunVI ρ pfuel gen fuel}[z.1 = some false] ≤
      Pr{let z ← completeExp ρ pfuel gen}[¬ CompleteOK fuel z] := by
  unfold completeRunVI completeExp
  rw [run_simulateQ_bind]
  refine prEvent_bind_le_prEvent_of_support _ _ _ _ fun a _ hok ↦ ?_
  refine prEvent_eq_zero_of_forall_mem_support _ _ fun y hy hrej ↦ ?_
  have hok : CompleteOK fuel a := not_not.mp hok
  obtain ⟨hpre, hlook⟩ := simulateQ_look_of_mem_support _ _ y hy
  have hl := hlook y.2 (List.prefix_refl _)
  have hid := simulateQ_id_of_look y.2 (fillLog y.2) (agrees_fillLog y.2) _ y.1 hl
  obtain ⟨g, ℓ⟩ := a
  rcases g with _ | ⟨T, r⟩
  · simp only [verifyStage, simulateQ_pure] at hid
    rw [← hid] at hrej
    cases hrej
  · obtain ⟨o, rfl, -, hacc⟩ := hok T r rfl
    simp only [verifyStage, simulateQ_map] at hid
    rw [idealVerify_natural (isMorphism_simulateQ_id (fillLog y.2))] at hid
    simp only [simulateQ_queryH] at hid
    have h1 := hacc (fillLog y.2) (agrees_of_prefix hpre (agrees_fillLog y.2))
    rw [← hid] at hrej
    simp only [Functor.map] at hrej h1
    rw [h1] at hrej
    cases hrej

end
end LeanVM.E2E.Complete
