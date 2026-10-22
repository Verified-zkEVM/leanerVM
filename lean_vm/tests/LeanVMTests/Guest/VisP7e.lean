import LeanVM.E2E.Vis.PerKey.Agree

/-!
# Tests: W-vis P7e, agreement on good outputs

The generic agreement lemmas of the per-key reductions (`LeanVM.E2E.Vis.PerKey.Agree`: binds that
differ only on bad outputs, sequences, events after agreeing computations) rest on Lean's three
standard axioms only, and the statements keep their shape.
-/

open LeanVM.E2E

/-- info: 'LeanVM.E2E.romRun_pm_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.romRun_pm_bind

/-- info: 'LeanVM.E2E.romRun_pm_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.romRun_pm_map

/-- info: 'LeanVM.E2E.fst_mem_support_of_mem_romRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.fst_mem_support_of_mem_romRun

/-- info: 'LeanVM.E2E.mem_support_pm_bind_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.mem_support_pm_bind_pair

/-- info: 'LeanVM.E2E.fst_eq_of_mem_romRun_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.fst_eq_of_mem_romRun_pair

/-- info: 'LeanVM.E2E.AgreeOn.refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.AgreeOn.refl

/-- info: 'LeanVM.E2E.AgreeOn.symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.AgreeOn.symm

/-- info: 'LeanVM.E2E.AgreeOn.trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.AgreeOn.trans

/-- info: 'LeanVM.E2E.AgreeOn.of_not_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.AgreeOn.of_not_good

/-- info: 'LeanVM.E2E.agreeOn_bind_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.agreeOn_bind_congr

/-- info: 'LeanVM.E2E.agreeOn_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.agreeOn_bind

/-- info: 'LeanVM.E2E.AgreeOn.bind_comb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.AgreeOn.bind_comb

/-- info: 'LeanVM.E2E.AgreeOn.bind_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.AgreeOn.bind_pure

/-- info: 'LeanVM.E2E.agreeOn_sequenceFin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.agreeOn_sequenceFin

/-- info: 'LeanVM.E2E.prEvent_eq_of_agreeOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.prEvent_eq_of_agreeOn

/-- A sequence of one computation agrees with itself on its good outputs. -/
example (good : Bool → Prop) (f : Fin 3 → PM Bool) :
    AgreeOn (fun v : Fin 3 → Bool ↦ ∀ i, good (v i)) (LeanXmss.Concrete.sequenceFin f)
      (LeanXmss.Concrete.sequenceFin f) :=
  agreeOn_sequenceFin good f f fun i ↦ AgreeOn.refl good (f i)

/-- Branches that differ only where the prefix's output fails the condition agree, when the
other branch's outputs are bad there. -/
example (x : PM Bool) :
    AgreeOn (fun b : Bool ↦ b = true) (x >>= fun m ↦ pure m) (x >>= fun m ↦ if m then pure m else pure false) :=
  agreeOn_bind x _ _ (fun m ↦ m = true) _ (fun m hm ↦ by simp [hm]) fun m hm cp ↦ by
    simp only [Bool.not_eq_true] at hm
    subst hm
    simp [StateT.run_pure]
