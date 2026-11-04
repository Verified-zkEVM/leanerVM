/-
  LeanVM.Guest.B1.Sig.SpWotsPadCheck

  The facts about numbers `sp_wots`'s completeness reads off its template, checked by the kernel:
  where each arm's padding run goes, where the arms start and end, and the groups' inputs.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsLayout

/-!
# `sp_wots`'s template, checked for completeness

* `spArmEnd`: the end of arm `k`'s values with its run virtual (its outputs, for arm `0`);
* `spPadOK`: arm `k`'s padding run, when it has one, goes above the group's digit cells and at
  most at the arm's end; a later arm starts after arm `0`'s outputs; every arm ends in the group;
* `spGroupPadOK`: every arm of group `p`, the group's inputs below its base, its end below the
  virtual run; `spPad_all`, `spGroupPad_all`: for every group.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Parameters

@[expose] public section

/-- The end of arm `k`'s values with its run virtual: arm `0`'s outputs are after its walks. -/
def spArmEnd (first n : Nat) (fold : Bool) (B : Nat) (prodIn encIn : V) (k b : Nat) : Nat :=
  (spArmV first n fold B prodIn encIn k b).2 + (if k = 0 then 2 else 0)

/-- **Arm `k`'s numbers**: its run, when it has one, above the group's digit cells and at most at
its end; a later arm after arm `0`'s outputs; the arm inside the group. -/
def spPadOK (first n : Nat) (fold : Bool) (B : Nat) (prodIn encIn : V) (k : Nat) : Bool :=
  let b := spArmB first n fold B prodIn encIn k
  let L := (spArmV first n fold B prodIn encIn k b).1
  (match L.findIdx? isTopConst with
    | none => true
    | some i => decide (B + 5 ≤ firstDef (L.getD i default)) &&
        decide (firstDef (L.getD i default) ≤ spArmEnd first n fold B prodIn encIn k b)) &&
    decide (k ≠ 0 → groupStart fold (B + 5) + chainStride spW * n + 2 ≤ b) &&
    decide (spArmB first n fold B prodIn encIn (k + 1) ≤ spArmB first n fold B prodIn encIn (4 ^ n))

/-- **Group `p`'s numbers**: every arm's, the inputs numbered below the base, the end below the
virtual run. -/
def spGroupPadOK (p : Nat) : Bool :=
  let st := spState p
  (List.range (4 ^ spN p)).all (fun k => spPadOK (3 * p) (spN p) (p == 0) st.2.2 st.1 st.2.1 k) &&
    decide (st.1 = .n st.1.idx) && decide (st.1.idx < st.2.2) && decide (st.2.1 = .n st.2.1.idx) &&
    decide (st.2.1.idx < st.2.2) && decide (13 ≤ st.2.2) &&
    decide (spArmB (3 * p) (spN p) (p == 0) st.2.2 st.1 st.2.1 (4 ^ spN p) + 5 < spVPad)

theorem spGroupPadOK_all : (List.range 22).all spGroupPadOK = true := by decide +kernel

theorem spGroupPad_all {p : Nat} (hp : p < 22) : spGroupPadOK p = true := by
  have h := spGroupPadOK_all
  simp only [List.all_eq_true, List.mem_range] at h
  exact h p hp

theorem spPad_all {p k : Nat} (hp : p < 22) (hk : k < 4 ^ spN p) :
    spPadOK (3 * p) (spN p) (p == 0) (spState p).2.2 (spState p).1 (spState p).2.1 k = true := by
  have h := spGroupPad_all hp
  simp only [spGroupPadOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  exact h.1.1.1.1.1.1 k hk

end
end LeanVM.Guest.B1.Sig
