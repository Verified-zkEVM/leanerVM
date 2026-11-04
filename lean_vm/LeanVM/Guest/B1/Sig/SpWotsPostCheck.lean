/-
  LeanVM.Guest.B1.Sig.SpWotsPostCheck

  Where `sp_wots`'s arms leave their tips and hint their chains' starts, checked by the kernel: in
  the group, above its digit cells.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsArms

/-!
# `sp_wots`'s tips and starts, checked

`spGroupPostOK p`: in every arm `k` of group `p`, chain `t`'s tip (`spSlot`) and start
(`spStartOf`) are numbered values in the group's arms' range `B + 5 ..< end`; `spPost_all`: for
every group.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Parameters

@[expose] public section

/-- Group `p`'s tips and starts lie in its arms' range. -/
def spGroupPostOK (p : Nat) : Bool :=
  let st := spState p
  let hi := spArmB (3 * p) (spN p) (p == 0) st.2.2 st.1 st.2.1 (4 ^ spN p)
  (List.range (spN p)).all (fun t => decide (st.2.2 + 5 ≤ spSlot (p == 0) st.2.2 t 2) &&
      decide (spSlot (p == 0) st.2.2 t 2 < hi)) &&
    (List.range (4 ^ spN p)).all fun k => (List.range (spN p)).all fun t =>
      let v := spStartOf (3 * p) (spN p) (p == 0) st.2.2 st.1 st.2.1 k
        (spArmB (3 * p) (spN p) (p == 0) st.2.2 st.1 st.2.1 k) t
      decide (v = .n v.idx) && decide (st.2.2 + 5 ≤ v.idx) && decide (v.idx < hi)

theorem spGroupPostOK_all : (List.range 22).all spGroupPostOK = true := by decide +kernel

theorem spPost_all {p : Nat} (hp : p < 22) :
    (∀ t < spN p, (spState p).2.2 + 5 ≤ spSlot (p == 0) (spState p).2.2 t 2 ∧
      spSlot (p == 0) (spState p).2.2 t 2 <
        spArmB (3 * p) (spN p) (p == 0) (spState p).2.2 (spState p).1 (spState p).2.1 (4 ^ spN p)) ∧
    ∀ k < 4 ^ spN p, ∀ t < spN p, ∃ j,
      spStartOf (3 * p) (spN p) (p == 0) (spState p).2.2 (spState p).1 (spState p).2.1 k
        (spArmB (3 * p) (spN p) (p == 0) (spState p).2.2 (spState p).1 (spState p).2.1 k) t = .n j ∧
      (spState p).2.2 + 5 ≤ j ∧
      j < spArmB (3 * p) (spN p) (p == 0) (spState p).2.2 (spState p).1 (spState p).2.1 (4 ^ spN p) := by
  have h := spGroupPostOK_all
  simp only [List.all_eq_true, List.mem_range] at h
  have h2 := h p hp
  simp only [spGroupPostOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h2
  refine ⟨fun t ht => h2.1 t ht, fun k hk t ht => ?_⟩
  obtain ⟨⟨e, h1⟩, h3⟩ := h2.2 k hk t ht
  exact ⟨_, e, h1, h3⟩

end
end LeanVM.Guest.B1.Sig
