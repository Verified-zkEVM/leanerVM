/-
  LeanVM.Guest.B1.Whir.CFold

  The template's sumcheck rounds, honestly: the completeness of `osFold`, `osFolds`.
-/

module

public import LeanVM.Guest.B1.Whir.CVal
public import LeanVM.Guest.B1.Whir.Folds

/-!
# The fold rounds, honestly

`osMat_complete`: the materialized pointer. `osFold_complete`: from the carried sponge (canonical
capacity), the cursor's two words in memory and the challenge's slot holding the challenge, the
round's values make the block hold, `opening_fold` holding of its meaning (B1-a, `.mpr`), with
`FoldOut`. `osFolds_complete`: `n` rounds.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- The state's values lie below its next free value. -/
structure OsSt.Below (st : OsSt) : Prop where
  fs : ∀ f ∈ st.fs, f < st.k
  w0 : st.w0 < st.k
  w1 : st.w1 < st.k
  cb : st.cb < st.k
  c : st.c < st.k
  b : st.b < st.k
  a : st.a < st.k
  t : st.t < st.k

/-- The values of `osMat base off k`. -/
def matVal (σ : Val) (base off k i : ℕ) : E :=
  if i = k then gw off else σ (.n base) * gw off

/-- **The materialized pointer.** -/
theorem osMat_complete {base off k : ℕ} (hoff : off < u128Bound) (hb : base < k) {σ σ' : Val}
    (ha : AgreeBelow k σ σ') (hv : RangeVals σ' k (osMat base off k).2.2 (matVal σ base off k)) :
    AllOk C rd σ' (osMat base off k).1 ∧
      σ' (.n (osMat base off k).2.1) = σ (.n base) * gen ^ off := by
  by_cases h0 : off = 0
  · subst h0
    simp only [osMat, ↓reduceIte, pow_zero, mul_one]
    exact ⟨allOk_nil, ha base hb⟩
  · simp only [osMat, h0, ↓reduceIte] at hv ⊢
    have e0 := hv k le_rfl (by omega)
    have e1 := hv (k + 1) (by omega) (by omega)
    simp only [matVal, ↓reduceIte, show k + 1 ≠ k by omega] at e0 e1
    refine ⟨?_, by rw [e1, gw_eq hoff]⟩
    simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
    exact ⟨e0, by rw [e1, e0, ha base hb]⟩

/-- The values of one round after its pointer: the squeeze's capacity, the cursor, the claim, the
two words, the challenge, the next `b`. -/
def foldVals (σ : Val) (st : OsSt) (d0 d2 : E) : List E :=
  let r := (st.F σ).squeeze
  let claim := (σ (.n st.a) * r.1 + σ (.n st.b)) * r.1 + σ (.n st.c)
  r.2.cap ++ [st.cur σ * gen ^ 2, claim, d0, d2, r.1, claim + d2]

/-- The round's values. -/
def osFoldF (σ : Val) (st : OsSt) (d0 d2 : E) (i : ℕ) : E :=
  if i < (osMat st.cb st.co st.k).2.2 then matVal σ st.cb st.co st.k i
  else (foldVals σ st d0 d2).getD (i - (osMat st.cb st.co st.k).2.2) 0

theorem foldVals_length (σ : Val) (st : OsSt) (d0 d2 : E) :
    (foldVals σ st d0 d2).length = 11 := by
  simp only [foldVals, List.length_append, List.length_cons, List.length_nil]
  simp [Fs.squeeze, capOf]

/-- **One round, honestly.** -/
theorem osFold_complete
    (hC : ∀ args rets, MeaningOpeningFold rd args rets → C "opening_fold" args rets)
    {p off : ℕ} {st : OsSt} (σ : Val) (hfs : st.fs.length = 5) (hco : st.co < u128Bound)
    (hb : st.Below) (hp : p < st.k) (hcan : AllCanonical (st.fsv σ)) {d0 d2 : E}
    (hrd : ReadsAt rd (st.cur σ) [d0, d2])
    (hst : LoadHolds rd (σ (.n p)) off (st.F σ).squeeze.1) :
    Blk C rd σ st.k (osFold p off st).2.k (osFold p off st).1
      (fun σ' ↦ FoldOut σ' st (osFold p off st).2 d0 d2 ∧ AgreeBelow st.k σ σ') := by
  obtain ⟨f0, f1, f2, f3, f4, hf⟩ := fold_args st hfs
  refine ⟨osFoldF σ st d0 d2, fun σ' ha hv ↦ ?_⟩
  have hk' : (osFold p off st).2.k = (osMat st.cb st.co st.k).2.2 + 11 := rfl
  have hmk : st.k ≤ (osMat st.cb st.co st.k).2.2 := osMat_next _ _ _
  have hmv : RangeVals σ' st.k (osMat st.cb st.co st.k).2.2 (matVal σ st.cb st.co st.k) :=
    fun i h1 h2 ↦ by
      rw [hv i h1 (by omega)]
      simp only [osFoldF, h2, ↓reduceIte]
  obtain ⟨okm, hcur⟩ := osMat_complete (C := C) (rd := rd) hco hb.cb ha hmv
  have hval : ∀ j < 11, σ' (.n ((osMat st.cb st.co st.k).2.2 + j)) =
      (foldVals σ st d0 d2).getD j 0 := fun j hj ↦ by
    rw [hv _ (by omega) (by omega)]
    simp only [osFoldF, show ¬ ((osMat st.cb st.co st.k).2.2 + j < (osMat st.cb st.co st.k).2.2)
      by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  set r := (osMat st.cb st.co st.k).2.2 with hr
  have hF : st.F σ = ⟨[σ (.n f0), σ (.n f1), σ (.n f2), σ (.n f3), σ (.n f4)],
      [(σ (.n st.w0), dsObserve), (σ (.n st.w1), dsObserve)]⟩ := by
    simp [OsSt.F, OsSt.fsv, hf]
  have hfl : ∀ f ∈ st.fs, f < st.k := hb.fs
  rw [hf] at hfl
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at hfl
  have v : ∀ j, j < 11 → σ' (.n (r + j)) = _ := hval
  simp only [foldVals, List.getD_eq_getElem?_getD] at v
  -- the squeeze's values
  set S := (st.F σ).squeeze with hS
  have hcap : S.2.cap.length = 5 := by simp [hS, Fs.squeeze, capOf]
  obtain ⟨c0, c1, c2, c3, c4, hc⟩ : ∃ c0 c1 c2 c3 c4, S.2.cap = [c0, c1, c2, c3, c4] := by
    match h : S.2.cap, hcap with
    | [c0, c1, c2, c3, c4], _ => exact ⟨c0, c1, c2, c3, c4, rfl⟩
  rw [hc] at v
  have v0 := v 0 (by omega); have v1 := v 1 (by omega); have v2 := v 2 (by omega)
  have v3 := v 3 (by omega); have v4 := v 4 (by omega); have v5 := v 5 (by omega)
  have v6 := v 6 (by omega); have v7 := v 7 (by omega); have v8 := v 8 (by omega)
  have v9 := v 9 (by omega); have v10 := v 10 (by omega)
  simp only [List.cons_append, List.nil_append, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, Nat.add_zero] at v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  have hagree : ∀ i < st.k, σ' (.n i) = σ (.n i) := ha
  have hFe : OsSt.F σ' st = OsSt.F σ st := by
    simp only [OsSt.F, OsSt.fsv, hf, List.map_cons, List.map_nil, hagree f0 hfl.1,
      hagree f1 hfl.2.1, hagree f2 hfl.2.2.1, hagree f3 hfl.2.2.2.1, hagree f4 hfl.2.2.2.2,
      hagree st.w0 hb.w0, hagree st.w1 hb.w1]
  have hCe : OsSt.cur σ' st = OsSt.cur σ st := by simp only [OsSt.cur, hagree st.cb hb.cb]
  refine ⟨?_, ⟨by simp [osFold], ?_, ?_, ?_, ?_⟩, ha⟩
  · simp only [osFold]
    rw [allOk_append]
    refine ⟨okm, ?_⟩
    simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds, List.map_cons,
      List.map_nil, osRun, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
      hf, Nat.add_zero]
    refine ⟨hC _ _ ?_, ?_, ?_⟩
    · rw [hagree f0 hfl.1, hagree f1 hfl.2.1, hagree f2 hfl.2.2.1, hagree f3 hfl.2.2.2.1,
        hagree f4 hfl.2.2.2.2, hagree st.w0 hb.w0, hagree st.w1 hb.w1, hcur, hagree st.c hb.c,
        hagree st.b hb.b, hagree st.a hb.a, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9]
      refine ⟨by simpa [OsSt.fsv, hf] using hcan, d0, d2, ?_, ?_⟩
      · simpa [OsSt.cur] using hrd
      · rw [← hF]
        simp only [OsSt.cur, ← hS, hc, List.cons_append, List.nil_append]
    · rw [v9, hagree p hp]; exact hst
    · rw [v10, v6, v8]
  · rw [hFe, ← hS]
    simp only [OsSt.F, OsSt.fsv, osFold, List.map_cons, List.map_nil]
    rw [v0, v1, v2, v3, v4, v7, v8, ← hc]
  · rw [hCe]
    simp only [OsSt.cur, osFold, pow_zero, mul_one]
    rw [v5]
    rfl
  · simp only [osFold]
    rw [v6, hFe, ← hS]
    simp only [OsSt.quad, polyEval, List.foldr_cons, List.foldr_nil, hagree st.c hb.c,
      hagree st.b hb.b, hagree st.a hb.a]
    ring
  · simp only [OsSt.quad, osFold]
    rw [v10, v6, v7, v8]

end
end LeanVM.Guest.B1.Whir
