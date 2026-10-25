/-
  LeanVM.Guest.B1.Main.MainGoalsDvT

  `main`'s `da_verify` on an honest run, by a tree of its honest shape (`Da.dvNH`) at the direct DA
  witness's row count and padded log.

  The witness and `Da.Witness.Opens` are Benedikt Wagner's LeanDA formalization, as ported here.
-/

module

public import LeanVM.Guest.B1.Main.MainGoalsG
public import LeanVM.Guest.B1.Da.WitnessAtT

/-!
# `da_verify` on an honest run, its honest shape

`hDvNH s w`: `da_verify`'s honest shape on the directly held DA claim's witness (no constraint
without one). `MainGoalDvT`: `MainGoalDv` by such a tree; `mainGoalDvT`: as `mainGoalDv`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.Hints (direct plan)
open LeanVM.Guest.B1 (CompleteAtD CompleteAtDT Returns)
open LeanVM.Guest.B1.Da (reads_of_memL exists_of_length_succ wLog)

@[expose] public section

/-- **`da_verify`'s honest shape on the direct DA witness.** -/
def hDvNH (s : NodeStatement) (w : NodeWitness) : Tree → Prop :=
  ((hRawD s w).map fun p => Da.dvNH p.2.rows.length (wLog p.2)).headD fun _ => True

/-- `da_verify` complete by a tree of its honest shape. -/
def MainGoalDvT (fs : String → ℕ) (cert : String → V → ℕ) (fp : ℕ) (seed : Digest)
    (s : NodeStatement) (w : NodeWitness) : Prop :=
  (hm fs fp seed s w).nd = 1 →
    CompleteAtDT fs cert 16 "da_verify" (hLmain fs fp seed s w) [(hm fs fp seed s w).et2]
      (Returns (hm fs fp seed s w).daR) (hDvNH s w)

theorem MainGoalDvT.goal {fs : String → ℕ} {cert : String → V → ℕ} {fp : ℕ} {seed : Digest}
    {s : NodeStatement} {w : NodeWitness} (h : MainGoalDvT fs cert fp seed s w) :
    MainGoalDv fs cert fp seed s w := fun hn => (h hn).toD

variable {bytecode : List K} {seed : Digest} {s : NodeStatement} {w : NodeWitness}

variable (fs : String → ℕ) (cert : String → V → ℕ) (fp : ℕ)

/-- **`da_verify` on an honest run, by a tree of its honest shape.** -/
theorem mainGoalDvT (hn : NodeRel bytecode seed s w) (hrf : Lift.RunsFit fs cert) :
    MainGoalDvT fs cert fp seed s w := by
  intro h1
  obtain ⟨p, hp, hR⟩ := direct_da fs fp h1
  rw [hR, hDvNH, hp]
  simp only [List.map_cons, List.map_nil, List.headD_cons]
  have hw : p.2.Opens p.1.daRoot p.1.membershipVectorDigest :=
    direct_held (H := DaHeld w.children)
      (P := fun c x => x.Opens c.daRoot c.membershipVectorDigest) (fun _ _ h => h)
      hn.2.2.2.2.1 p (show p ∈ hRawD s w by rw [hp]; exact List.mem_singleton_self p)
  have hL := wLog_lt hw
  have h := Da.da_verify_completeAtT fs cert hrf hw (etB fs (mK0 (hData seed s w) fs fp) + 34)
  have hq : (etB fs (mK0 (hData seed s w) fs fp) + 34, etTabs.getD 1 []) ∈ hLmain fs fp seed s w :=
    List.mem_append_right _ (by simp [etL])
  have hlen : (etTabs.getD 1 []).length = 34 := by simp [etTabs]
  refine Da.completeAtDT_lin_mono (fun rd hM => ?_) (fun i hi => ?_) h
  · have hr := reads_of_memL hM hq (wLog p.2) (by omega)
    have hv : (etTabs.getD 1 [])[wLog p.2]'(by omega) = gen ^ 2 ^ wLog p.2 := by simp [etTabs]
    rw [hv] at hr
    intro q hq'
    rw [List.mem_singleton] at hq'
    subst hq'
    intro k hk
    simp only [List.length_singleton, Nat.lt_one_iff] at hk
    subst hk
    rw [← gen_pow_eq_ofK, pow_add, loadHolds_mul_gen_pow, Nat.add_zero]
    exact hr
  · obtain ⟨q, hq', h1, h2⟩ := hi
    rw [List.mem_singleton] at hq'
    subst hq'
    simp only [List.length_singleton] at h1 h2
    exact ⟨_, hq, show etB fs (mK0 (hData seed s w) fs fp) + 34 ≤ i by omega,
      show i < etB fs (mK0 (hData seed s w) fs fp) + 34 + (etTabs.getD 1 []).length by omega⟩

end
end LeanVM.Guest.B1.Main
