/-
  LeanVM.E2E.Vis.PerKey.Morph

  W-vis, P7: monad morphisms through simulation and state. A simulation by a morphic image of an
  implementation is the image of the simulation; a morphism lifts through `StateT`.
-/

module

public import LeanVM.E2E.Natural
public import LeanVM.E2E.Vis.PerKey.Sim

/-!
# Morphisms (W-vis, P7)

* `isMorphism_simulateQ`: simulation is a monad morphism of `OracleComp`.
* `stMap φ`: a morphism `φ : m → n` acting on `StateT σ m` (`isMorphism_stMap`).
* `simulateQ_morph`: simulating with `φ ∘ impl` is `φ` of simulating with `impl`.
-/

namespace LeanVM.E2E

open OracleSpec OracleComp

@[expose] public section

/-- **Simulation is a monad morphism.** -/
theorem isMorphism_simulateQ {ι κ : Type} {spec : OracleSpec.{0, 0} ι} {spec' : OracleSpec.{0, 0} κ}
    (impl : QueryImpl spec (OracleComp spec')) :
    IsMorphism (fun {α : Type} (x : OracleComp spec α) ↦ simulateQ impl x) where
  pure a := simulateQ_pure impl a
  bind x f := simulateQ_bind impl x f

section St

variable {m n : Type → Type} {σ : Type}

/-- A map of computations acting under a state. -/
def stMap (φ : ∀ {α : Type}, m α → n α) {α : Type} (x : StateT σ m α) : StateT σ n α :=
  StateT.mk fun s ↦ φ (x.run s)

@[simp] theorem run_stMap (φ : ∀ {α : Type}, m α → n α) {α : Type} (x : StateT σ m α) (s : σ) :
    (stMap φ x).run s = φ (x.run s) := rfl

/-- **A morphism lifts through the state.** -/
theorem isMorphism_stMap [Monad m] [Monad n] {φ : ∀ {α : Type}, m α → n α} (hφ : IsMorphism @φ) :
    IsMorphism (fun {α : Type} (x : StateT σ m α) ↦ stMap (σ := σ) @φ x) where
  pure a := by
    refine StateT.ext fun s ↦ ?_
    simp only [run_stMap, StateT.run_pure, hφ.pure]
  bind x f := by
    refine StateT.ext fun s ↦ ?_
    simp only [run_stMap, StateT.run_bind, hφ.bind]

end St

/-- **Simulating with a morphic image is the image of simulating.** -/
theorem simulateQ_morph {ι : Type} {spec : OracleSpec.{0, 0} ι} {m n : Type → Type} [Monad m]
    [Monad n] [LawfulMonad m] [LawfulMonad n] {φ : ∀ {α : Type}, m α → n α} (hφ : IsMorphism @φ)
    (impl : QueryImpl spec m) {α : Type} (oa : OracleComp spec α) :
    simulateQ (fun t ↦ φ (impl t)) oa = φ (simulateQ impl oa) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [hφ.pure]
  | query_bind t k ih =>
    rw [simulateQ_query_bind, simulateQ_query_bind, hφ.bind]
    simp only [OracleQuery.input_query, monadLift_self]
    exact bind_congr fun u ↦ ih u

end
end LeanVM.E2E
