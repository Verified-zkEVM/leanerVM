/-
  LeanVM.Guest.B1.Whir.CGlue

  The query weights and a level's glue, honestly.
-/

module

public import LeanVM.Guest.B1.Whir.CFold
public import LeanVM.Guest.B1.Whir.LamPows
public import LeanVM.Guest.B1.Whir.Glue

/-!
# The query weights and the glue, honestly

`osLamPows_complete`: the powers of `λ` in `query_weights` make the block hold, `λ^Q` left.
`osOodGlue_complete`: the out-of-domain value and intro in `ood` (and the slot of `λ`), the claim
glued with `λ`. `osGlue_complete`: the level's batch glued with `β`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- The values of the query weights' block: `1`, then `λ^(j + 1)` at `k + j`. -/
def lamVals (lv : E) (k i : ℕ) : E := if i = k then 1 else lv ^ (i - k + 1)

/-- **The query weights, honestly.** -/
theorem osLamPows_complete {lam base k Q : ℕ} (hQ : 2 ≤ Q) (σ : Val) (hl : lam < k)
    (hqw : osQw < k) (hmem : ∀ i < Q, LoadHolds rd (σ (.n osQw)) (base + i) (σ (.n lam) ^ i)) :
    Blk C rd σ k (k + Q) (osLamPows lam base k Q)
      (fun σ' ↦ σ' (.n (k + Q - 1)) = σ (.n lam) ^ Q ∧ AgreeBelow k σ σ') := by
  refine ⟨lamVals (σ (.n lam)) k, fun σ' ha hv ↦ ?_⟩
  obtain ⟨q, rfl⟩ : ∃ q, Q = q + 2 := ⟨Q - 2, by omega⟩
  have el : σ' (.n lam) = σ (.n lam) := ha _ hl
  have eq : σ' (.n osQw) = σ (.n osQw) := ha _ hqw
  have vk : σ' (.n k) = 1 := by rw [hv k le_rfl (by omega)]; simp [lamVals]
  have vj : ∀ j, 1 ≤ j → j < q + 2 → σ' (.n (k + j)) = σ (.n lam) ^ (j + 1) := fun j h1 h2 ↦ by
    rw [hv _ (by omega) (by omega)]
    simp only [lamVals, show k + j ≠ k by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  refine ⟨?_, ?_, ha⟩
  · simp only [osLamPows, Nat.add_one_ne_zero, ↓reduceIte, allOk_append, allOk_cons, allOk_nil,
      and_true, allOk_flatten, StmtOk, Atom.Holds, List.mem_map, List.mem_range,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Nat.add_sub_cancel]
    refine ⟨⟨by rw [vk, word_one], by rw [vk, eq]; simpa using hmem 0 (by omega)⟩,
      by rw [el, eq]; simpa using hmem 1 (by omega), by rw [vj 1 le_rfl (by omega), el]; ring,
      fun i hi ↦ ⟨?_, ?_⟩⟩
    · rw [show k + 1 + i = k + (i + 1) by ring, vj (i + 1) (by omega) (by omega), eq]
      rw [show base + 2 + i = base + (i + 2) by ring]
      exact hmem (i + 2) (by omega)
    · rw [show k + 2 + i = k + (i + 2) by ring, show k + 1 + i = k + (i + 1) by ring,
        vj (i + 2) (by omega) (by omega), vj (i + 1) (by omega) (by omega), el]
      ring
  · rw [show k + (q + 2) - 1 = k + (q + 1) by omega, vj (q + 1) (by omega) (by omega)]

/-- The out-of-domain glue's values. -/
def oodGlueVals (σ : Val) (s : OsSt) (lam : ℕ) (y c0 c2 : E) : List E :=
  let l := σ (.n lam)
  [y, c2, c0, l * c0, σ (.n s.c) + l * c0, y + c2, l * (y + c2), σ (.n s.b) + l * (y + c2),
    l * c2, σ (.n s.a) + l * c2, l * y, σ (.n s.t) + l * y, l * l]

/-- **The out-of-domain claim glued, honestly.** -/
theorem osOodGlue_complete {lvl lam : ℕ} {s : OsSt} (σ : Val) (hb : s.Below) (hl : lam < s.k)
    (hk : 34 ≤ s.k) {y c0 c2 : E}
    (hy : LoadHolds rd (σ (.n osOod)) ((lvl + 1) * oodSlots + 1) y)
    (hc0 : LoadHolds rd (σ (.n osOod)) ((lvl + 1) * oodSlots + 2) c0)
    (hc2 : LoadHolds rd (σ (.n osOod)) ((lvl + 1) * oodSlots + 3) c2)
    (hlam : LoadHolds rd (σ (.n osOod)) ((lvl + 1) * oodSlots) (σ (.n lam))) :
    Blk C rd σ s.k (osOodGlue lvl lam s).2.k (osOodGlue lvl lam s).1
      (fun σ' ↦ (osOodGlue lvl lam s).2.quad σ' =
          [σ (.n s.c) + σ (.n lam) * c0, σ (.n s.b) + σ (.n lam) * (y + c2),
            σ (.n s.a) + σ (.n lam) * c2] ∧
        σ' (.n (osOodGlue lvl lam s).2.t) = σ (.n s.t) + σ (.n lam) * y ∧
        σ' (.n (s.k + 12)) = σ (.n lam) * σ (.n lam) ∧ (osOodGlue lvl lam s).2.Below ∧
        AgreeBelow s.k σ σ') := by
  refine ⟨fun i ↦ (oodGlueVals σ s lam y c0 c2).getD (i - s.k) 0, fun σ' ha hv ↦ ?_⟩
  have V : ∀ j < 13, σ' (.n (s.k + j)) = (oodGlueVals σ s lam y c0 c2).getD j 0 := fun j hj ↦ by
    rw [hv _ (by omega) (by simp [osOodGlue]; omega)]
    simp only [Nat.add_sub_cancel_left]
  have v0 := V 0 (by omega); have v1 := V 1 (by omega); have v2 := V 2 (by omega)
  have v3 := V 3 (by omega); have v4 := V 4 (by omega); have v5 := V 5 (by omega)
  have v6 := V 6 (by omega); have v7 := V 7 (by omega); have v8 := V 8 (by omega)
  have v9 := V 9 (by omega); have v10 := V 10 (by omega); have v11 := V 11 (by omega)
  have v12 := V 12 (by omega)
  simp only [oodGlueVals, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  have eo : σ' (.n osOod) = σ (.n osOod) := ha _ (by unfold osOod; omega)
  have el : σ' (.n lam) = σ (.n lam) := ha _ hl
  have ec := ha _ hb.c; have eb := ha _ hb.b; have ea := ha _ hb.a; have et := ha _ hb.t
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ha⟩⟩
  · simp only [osOodGlue, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
    refine ⟨by rw [v0, eo]; exact hy, by rw [v1, eo]; exact hc2, by rw [el, eo]; exact hlam,
      by rw [v2, eo]; exact hc0, by rw [v3, el, v2], by rw [v4, ec, v3], by rw [v5, v0, v1],
      by rw [v6, el, v5], by rw [v7, eb, v6], by rw [v8, el, v1], by rw [v9, ea, v8],
      by rw [v10, el, v0], by rw [v11, et, v10], by rw [v12, el]⟩
  · simp only [OsSt.quad, osOodGlue]; rw [v4, v7, v9]
  · simp only [osOodGlue]; rw [v11]
  · exact v12
  · have := hb.w0; have := hb.w1; have := hb.cb
    refine ⟨fun f hf ↦ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp [osOodGlue] at *
    all_goals first | omega | exact Nat.lt_add_right _ (hb.fs f hf)

/-- **The level's batch glued, honestly.** -/
theorem osGlue_complete {beta v c0 c1 c2 : ℕ} {s : OsSt} (σ : Val) (hb : s.Below)
    (hv0 : beta < s.k ∧ v < s.k ∧ c0 < s.k ∧ c1 < s.k ∧ c2 < s.k) :
    Blk C rd σ s.k (osGlue beta v c0 c1 c2 s).2.k (osGlue beta v c0 c1 c2 s).1
      (fun σ' ↦ (osGlue beta v c0 c1 c2 s).2.quad σ' =
          [σ (.n s.c) + σ (.n beta) * σ (.n c0), σ (.n s.b) + σ (.n beta) * σ (.n c1),
            σ (.n s.a) + σ (.n beta) * σ (.n c2)] ∧
        σ' (.n (osGlue beta v c0 c1 c2 s).2.t) = σ (.n s.t) + σ (.n beta) * σ (.n v) ∧
        (osGlue beta v c0 c1 c2 s).2.Below ∧ AgreeBelow s.k σ σ') := by
  obtain ⟨hbe, hvv, h0, h1, h2⟩ := hv0
  set vals := [σ (.n beta) * σ (.n c0), σ (.n s.c) + σ (.n beta) * σ (.n c0),
    σ (.n beta) * σ (.n c1), σ (.n s.b) + σ (.n beta) * σ (.n c1), σ (.n beta) * σ (.n c2),
    σ (.n s.a) + σ (.n beta) * σ (.n c2), σ (.n beta) * σ (.n v),
    σ (.n s.t) + σ (.n beta) * σ (.n v)] with hvals
  refine ⟨fun i ↦ vals.getD (i - s.k) 0, fun σ' ha hv ↦ ?_⟩
  have V : ∀ j < 8, σ' (.n (s.k + j)) = vals.getD j 0 := fun j hj ↦ by
    rw [hv _ (by omega) (by simp [osGlue]; omega)]
    simp only [Nat.add_sub_cancel_left]
  have v0 := V 0 (by omega); have v1 := V 1 (by omega); have v2 := V 2 (by omega)
  have v3 := V 3 (by omega); have v4 := V 4 (by omega); have v5 := V 5 (by omega)
  have v6 := V 6 (by omega); have v7 := V 7 (by omega)
  simp only [hvals, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1 v2 v3 v4 v5 v6 v7
  have eb := ha _ hbe; have evv := ha _ hvv; have e0 := ha _ h0; have e1 := ha _ h1
  have e2 := ha _ h2
  have ec := ha _ hb.c; have ebb := ha _ hb.b; have ea := ha _ hb.a; have et := ha _ hb.t
  refine ⟨?_, ⟨?_, ?_, ?_, ha⟩⟩
  · simp only [osGlue, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
    exact ⟨by rw [v0, eb, e0], by rw [v1, ec, v0], by rw [v2, eb, e1], by rw [v3, ebb, v2],
      by rw [v4, eb, e2], by rw [v5, ea, v4], by rw [v6, eb, evv], by rw [v7, et, v6]⟩
  · simp only [OsSt.quad, osGlue]; rw [v1, v3, v5]
  · simp only [osGlue]; rw [v7]
  · have := hb.w0; have := hb.w1; have := hb.cb
    refine ⟨fun f hf ↦ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp [osGlue] at *
    all_goals first | omega | exact Nat.lt_add_right _ (hb.fs f hf)

end
end LeanVM.Guest.B1.Whir
