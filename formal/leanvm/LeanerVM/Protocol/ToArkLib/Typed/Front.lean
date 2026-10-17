/-
  LeanerVM.Protocol.ToArkLib.Typed.Front

  Front verifiers on ArkLib's typed interaction trees: the verifier that samples a fresh
  challenge at each of its nodes, reads the prover's moves, never queries an oracle, and returns
  a verdict of the path. Its challenge marginals. Candidate for ArkLib.
-/

module

public import ArkLib.Interaction.Oracle.Security.KnowledgeComposition

/-!
# Front verifiers

A verifier is *front* when it decides from the statement and the moves alone: it samples a
challenge at each of its own nodes, reads the prover's moves, makes no oracle query, and at the
leaf returns a verdict of the branch path. Every verifier of leanVM's oracle protocol before the
opening has this shape (the protocol blueprint's decision 31).

* `Samplers tree roles`: a sampler at each verifier node, constant across oracle messages (the
  verifier cannot see them);
* `Errors tree roles`: an error at each verifier node;
* `schedule`: the two as the `RoundExtractor.ChallengeSchedule` a knowledge certificate carries;
* `frontFragment samplers leaf`: the verifier fragment that samples with `samplers` and returns
  `leaf` of the branch path, with `samplesChallenges_frontFragment`: it draws exactly the
  schedule's challenges, whatever the errors, the input oracles and their handler.

The ambient oracle is `unifSpec`, so the verifier's effects are probabilistic computations.
-/

namespace LeanerVM.Protocol.Typed

open Interaction Interaction.TwoParty Interaction.Oracle Interaction.Oracle.Security
open OracleComp OracleSpec
open scoped NNReal ENNReal

@[expose] public section

/-! ## Samplers and errors -/

/-- A sampler at each verifier node of a tree. An oracle message cannot select the next sampler:
the verifier never sees its payload. -/
def Samplers : (tree : Oracle.TypeTree.{0}) → tree.RoleDecoration → Type
  | .done, _ => PUnit
  | .public Moves next, ⟨.sender, roles⟩ => (move : Moves) → Samplers (next move) (roles move)
  | .public Moves next, ⟨.receiver, roles⟩ =>
      ProbComp Moves × ((move : Moves) → Samplers (next move) (roles move))
  | .oracle _ next, roles => Samplers (next PUnit.unit) (roles.2 PUnit.unit)

/-- An error at each verifier node of a tree. -/
def Errors : (tree : Oracle.TypeTree.{0}) → tree.RoleDecoration → Type
  | .done, _ => PUnit
  | .public Moves next, ⟨.sender, roles⟩ => (move : Moves) → Errors (next move) (roles move)
  | .public Moves next, ⟨.receiver, roles⟩ =>
      ℝ≥0 × ((move : Moves) → Errors (next move) (roles move))
  | .oracle _ next, roles => Errors (next PUnit.unit) (roles.2 PUnit.unit)

/-- Errors pointwise at most others. -/
def Errors.Le : (tree : Oracle.TypeTree.{0}) → (roles : tree.RoleDecoration) →
    Errors tree roles → Errors tree roles → Prop
  | .done, _, _, _ => True
  | .public _ next, ⟨.sender, roles⟩, e, e' =>
      ∀ move, Errors.Le (next move) (roles move) (e move) (e' move)
  | .public _ next, ⟨.receiver, roles⟩, e, e' =>
      e.1 ≤ e'.1 ∧ ∀ move, Errors.Le (next move) (roles move) (e.2 move) (e'.2 move)
  | .oracle _ next, roles, e, e' => Errors.Le (next PUnit.unit) (roles.2 PUnit.unit) e e'

/-- The samplers and the errors as a knowledge certificate's challenge schedule. -/
def schedule : (tree : Oracle.TypeTree.{0}) → (roles : tree.RoleDecoration) →
    Samplers tree roles → Errors tree roles → RoundExtractor.ChallengeSchedule tree roles
  | .done, _, _, _ => PUnit.unit
  | .public _ next, ⟨.sender, roles⟩, s, e =>
      ⟨PUnit.unit, fun move => schedule (next move) (roles move) (s move) (e move)⟩
  | .public _ next, ⟨.receiver, roles⟩, s, e =>
      ⟨(s.1, (e.1 : ℝ≥0∞)), fun move => schedule (next move) (roles move) (s.2 move) (e.2 move)⟩
  | .oracle _ next, roles, s, e =>
      fun _ => schedule (next PUnit.unit) (roles.2 PUnit.unit) s e

/-! ## The front verifier -/

/-- The front verifier fragment: samples with `samplers` at its nodes, reads the prover's moves
and returns `leaf` of the branch path, querying nothing. -/
def frontFragment : (tree : Oracle.TypeTree.{0}) → (roles : tree.RoleDecoration) →
    (oracles : tree.OracleDecoration) → (initial : PFunctor) → Samplers tree roles →
    {Leaf : tree.BranchPath → Type} → ((path : tree.BranchPath) → Leaf path) →
    Verifier.Fragment unifSpec tree roles oracles initial Leaf
  | .done, _, _, _, _, _, leaf => leaf PUnit.unit
  | .public _ next, ⟨.sender, roles⟩, oracles, initial, s, _, leaf => fun move =>
      pure (frontFragment (next move) (roles move) (oracles.2 move) initial (s move)
        (fun path => leaf ⟨move, path⟩))
  | .public _ next, ⟨.receiver, roles⟩, oracles, initial, s, _, leaf => do
      let move ← OracleComp.liftComp s.1 (unifSpec + OracleSpec.ofPFunctor initial)
      return ⟨move, frontFragment (next move) (roles move) (oracles.2 move) initial (s.2 move)
        (fun path => leaf ⟨move, path⟩)⟩
  | .oracle _ next, roles, oracles, initial, s, _, leaf =>
      pure (frontFragment (next PUnit.unit) (roles.2 PUnit.unit) (oracles.2 PUnit.unit)
        (Access.extend initial oracles.1) s (fun path => leaf ⟨PUnit.unit, path⟩))

/-- The front verifier: the front fragment whose leaf returns its verdict without a query. -/
def frontVerifier (tree : Oracle.TypeTree.{0}) (roles : tree.RoleDecoration)
    (oracles : tree.OracleDecoration) (initial : PFunctor) (s : Samplers tree roles)
    {Out : tree.BranchPath → Type} (verdict : (path : tree.BranchPath) → Out path) :
    Verifier.Strategy unifSpec tree roles oracles initial Out :=
  frontFragment tree roles oracles initial s (fun path ↦ pure (verdict path))

/-- Running a lifted sampler against any handler of the input oracles is the sampler. -/
theorem simulateQ_liftComp_sampler {initial : PFunctor}
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) {α : Type} (sampler : ProbComp α) :
    simulateQ (QueryImpl.id' unifSpec)
      (simulateQ (Verifier.liftAccessImpl unifSpec initial impl)
        (OracleComp.liftComp sampler (unifSpec + OracleSpec.ofPFunctor initial))) = sampler := by
  rw [QueryImpl.simulateQ_liftComp_left_eq_of_apply _ (QueryImpl.id' unifSpec) (fun _ ↦ rfl),
    simulateQ_id', simulateQ_id']

/-- **The front verifier draws the schedule's challenges**: at each of its nodes, the challenge
it draws has exactly the sampler's law, whatever the errors, the input oracles and their
handler. -/
theorem samplesChallenges_frontFragment : (tree : Oracle.TypeTree.{0}) →
    (roles : tree.RoleDecoration) → (oracles : tree.OracleDecoration) → (initial : PFunctor) →
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) → (s : Samplers tree roles) →
    (e : Errors tree roles) → {Leaf : tree.BranchPath → Type} →
    (leaf : (path : tree.BranchPath) → Leaf path) →
    SamplesChallenges unifSpec (QueryImpl.id' unifSpec) tree roles oracles initial impl Leaf
      (frontFragment tree roles oracles initial s leaf) (schedule tree roles s e)
  | .done, _, _, _, _, _, _, _, _ => trivial
  | .public _ next, ⟨.sender, roles⟩, oracles, initial, impl, s, e, _, leaf => by
      intro move after hafter
      simp only [frontFragment, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hafter
      subst hafter
      exact samplesChallenges_frontFragment (next move) (roles move) (oracles.2 move) initial
        impl (s move) (e move) (fun path ↦ leaf ⟨move, path⟩)
  | .public _ next, ⟨.receiver, roles⟩, oracles, initial, impl, s, e, _, leaf => by
      refine ⟨fun event ↦ ?_, fun chosen hchosen ↦ ?_⟩
      · simp only [frontFragment, bind_pure_comp, simulateQ_map, simulateQ_liftComp_sampler,
          prEvent_map]
        rfl
      · simp only [frontFragment, bind_pure_comp, simulateQ_map, simulateQ_liftComp_sampler,
          support_map, Set.mem_image] at hchosen
        obtain ⟨move, -, rfl⟩ := hchosen
        exact samplesChallenges_frontFragment (next move) (roles move) (oracles.2 move) initial
          impl (s.2 move) (e.2 move) (fun path ↦ leaf ⟨move, path⟩)
  | .oracle _ next, roles, oracles, initial, impl, s, e, _, leaf => by
      intro message after hafter
      simp only [frontFragment, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hafter
      subst hafter
      exact samplesChallenges_frontFragment (next PUnit.unit) (roles.2 PUnit.unit)
        (oracles.2 PUnit.unit) (Access.extend initial oracles.1)
        (Access.extendImpl initial oracles.1 impl message) s e
        (fun path ↦ leaf ⟨PUnit.unit, path⟩)

end
end LeanerVM.Protocol.Typed
