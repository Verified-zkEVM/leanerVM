/-
  LeanVM.Guest.B1.Main.VerifySubGoals

  Each child's `verify_sub` call on `main`'s honest run, within its words: B1-d's
  `verify_sub_completeB` at the child, its exponent tables `exponent_tables`' and its fresh claim's
  slot in `main`'s children's fresh claims, moved to `main`'s words.
-/

module

public import LeanVM.Guest.B1.Main.MainGoalsHL5TB
public import LeanVM.Guest.B1.VerifySub.CompleteB
public import LeanVM.Guest.B1.Main.MainGoalsDvTB

/-!
# The children's `verify_sub` calls, bounded

`verifySubGoalsTB_of`: for `NodeRel` within `Limits`, the caps agreeing and no zero challenge,
every child's `verify_sub` call is complete within `vsBound W Bvk` (`VerifySubGoalsTB`), from
`verify_keccak`'s completeness within `Bvk` and the frame runs' certificate facts.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest (Limits NoZeroChallenge CapsAgree)
open LeanVM.Guest.B1 (CompleteAtDTB Returns log2Lin)
open LeanVM.Guest.B1.VerifySub (VsWords vsBound VkCompleteAtB verify_sub_completeB)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {fp : ℕ} {seed : Digest} {s : NodeStatement}
  {w : NodeWitness} {bytecode : List K}

/-- `exponent_tables`' tables are `log2Lin`'s. -/
theorem etL_eq (fs : String → ℕ) (fp : ℕ) (d : MainData) :
    log2Lin (etB fs (mK0 d fs fp)) (etB fs (mK0 d fs fp) + 34) = etL d fs fp := rfl

/-- **Each child's `verify_sub` call on the honest run, within `vsBound W Bvk`.** -/
theorem verifySubGoalsTB_of (hbl : bytecode.length = 2 ^ 23) (hrf : Lift.RunsFit fs cert)
    (hap : Lift.RunsApart cert) (W : VsWords fs) {Bvk : ℕ} (hvk : VkCompleteAtB fs cert 16 Bvk)
    (hr : NodeRel bytecode seed s w) (hl : Limits bytecode s w) (hca : CapsAgree bytecode seed w)
    (hnz : NoZeroChallenge bytecode seed w) :
    VerifySubGoalsTB fs cert fp seed s w (fun _ _ => True) (fun _ => vsBound W Bvk) := by
  intro c hc
  have hmem := List.getElem_mem hc
  set e := etB fs (mK0 (hData seed s w) fs fp) with he
  set outE := hP fs fp seed s w 7 + 24 * c with hout
  have h := verify_sub_completeB (fs := fs) (cert := cert) hbl hrf hap W le_rfl hvk seed
    w.children[c] e (e + 34) outE
    (log2Lin e (e + 34) ++ [(outE, fixedCells w.children[c].fresh)])
    (hl.stackLog _ hmem) (hl.stream _ hmem) (hnz _ hmem) (hca _ hmem)
    (fun q hq => List.mem_append_left _ hq) (List.mem_append_right _ (List.mem_singleton_self _))
  have hlen : ∀ a ∈ w.children, (fixedCells a.fresh).length = 24 := fun a ha => by
    simp [fixedCells, (kid_shapes hbl hr a ha).1, bytecodeVars]
  have e1 : (hm fs fp seed s w).et1 = ofK (gpow e) := gen_pow_eq_ofK _
  have e2 : (hm fs fp seed s w).et2 = ofK (gpow (e + 34)) := gen_pow_eq_ofK _
  have e3 : (hm fs fp seed s w).a400 * gen ^ (24 * c) = ofK (gpow outE) := by
    rw [hout, ← gen_pow_eq_ofK, pow_add]; rfl
  rw [e1, e2, e3]
  refine completeAtDTB_lin_mono (fun rd hM q hq => ?_) (fun i hi => ?_) h
  · rcases List.mem_append.mp hq with hq | hq
    · rw [etL_eq] at hq
      exact hM q (List.mem_append_right _ hq)
    · rw [List.mem_singleton] at hq
      subst hq
      have r7 := reads_hLmain fs fp seed s w hM (i := 7) (by omega)
      simp only [hOwn, List.getD_cons_succ, List.getD_cons_zero] at r7
      have := B1.Main.readsAt_flatMap_of w.children hlen r7 c hc
      rw [← gen_pow_eq_ofK, pow_add]
      exact this
  · obtain ⟨q, hq, h1, h2⟩ := hi
    rcases List.mem_append.mp hq with hq | hq
    · rw [etL_eq] at hq
      exact ⟨q, List.mem_append_right _ hq, h1, h2⟩
    · rw [List.mem_singleton] at hq
      subst hq
      simp only [hlen _ hmem] at h2
      have hk : 24 * c + (i - outE) < ((hOwn seed s w).getD 7 []).length := by
        simp only [hOwn, List.getD_cons_succ, List.getD_cons_zero]
        rw [length_flatMap_const _ _ 24 hlen]
        have : c + 1 ≤ w.children.length := hc
        omega
      have := region_buf fs fp seed s w (i := 7) (by omega) hk
      rwa [show hP fs fp seed s w 7 + (24 * c + (i - outE)) = i by omega] at this

end
end LeanVM.Guest.B1.Main
