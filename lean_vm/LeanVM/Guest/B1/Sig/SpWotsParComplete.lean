/-
  LeanVM.Guest.B1.Sig.SpWotsParComplete

  A WOTS+C arm renamed is the arm of the renamed step: two arms whose steps agree once renamed, and
  whose other values the renamings move alike, are equal once renamed. So `sp_wots`'s arm with its
  run virtual, moved by `padShift`, is the arm with its run at the group's digit cells moved by
  `padRen`.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsStepComplete
public import LeanVM.Guest.B1.Sig.SpWotsArms

/-!
# Arms renamed

* `walkT_par`, `walksT_par`, `armT_par`: the walks and arms of two chain steps are equal once
  renamed when their steps are, and the renamings agree on the other values;
* `PadGood B X x`: `x` is a numbered value below `X` off the run `B ..< B + 5`, which `padRen B P`
  and `padShift X P` move alike; `spWp_par`: the step with its run at `B` and at `X`, renamed;
* `spArmT_par`: an arm laid out above `B + 5`, its values below `X`, renamed alike.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-! ## Walks and arms, renamed -/

section
variable {W W' : WotsT} {r r' : V → V}

theorem walkT_par (i : Nat) (slot : Nat → Nat) (stride d b : Nat)
    (hh : r (walkStartV slot d b) = r' (walkStartV slot d b))
    (hs : ∀ j < 3 - d, Stmt.renameList r (W.step i (d + j) (if j = 0 then .n b else .n (slot (d + j - 1)))
        (b + 1 + j * stride) (slot (d + j))) =
      Stmt.renameList r' (W'.step i (d + j) (if j = 0 then .n b else .n (slot (d + j - 1)))
        (b + 1 + j * stride) (slot (d + j)))) :
    Stmt.renameList r (walkT W i slot stride d b) = Stmt.renameList r' (walkT W' i slot stride d b) := by
  unfold walkT
  unfold walkStartV at hh
  split
  · rename_i h3
    simp only [h3, ↓reduceIte] at hh
    simp [renameList_eq_map, hintW, Stmt.rename, Atom.rename, Hint.rename, Dest.rename, hh]
  · rename_i h3
    simp only [h3, ↓reduceIte] at hh
    simp only [renameList_eq_map, List.map_cons, List.map_flatMap] at hs ⊢
    refine congrArg₂ _ (by simp [hintW, Stmt.rename, Atom.rename, Hint.rename, Dest.rename, hh]) ?_
    exact List.flatMap_congr fun j hj => hs j (List.mem_range.mp hj)

theorem walksT_par (slots : Nat → Nat → Nat) (first k stride : Nat) :
    ∀ m rr b, (∀ t < m, Stmt.renameList r (walkT W (first + (rr + t)) (slots (rr + t)) stride
        (dig k (rr + t)) (walkBase stride k rr t b)) =
      Stmt.renameList r' (walkT W' (first + (rr + t)) (slots (rr + t)) stride
        (dig k (rr + t)) (walkBase stride k rr t b))) →
    Stmt.renameList r (walksT W slots first k stride m rr b).1 =
      Stmt.renameList r' (walksT W' slots first k stride m rr b).1
  | 0, _, _, _ => rfl
  | m + 1, rr, b, h => by
      simp only [walksT]
      rw [renameList_eq_map, List.map_append, ← renameList_eq_map, ← renameList_eq_map,
        renameList_eq_map r', List.map_append, ← renameList_eq_map, ← renameList_eq_map]
      have h0 := h 0 (by omega)
      simp only [Nat.add_zero, walkBase] at h0
      rw [h0, walksT_par slots first k stride m (rr + 1) _ fun t ht => ?_]
      have := h (t + 1) (by omega)
      simpa [walkBase, show rr + (t + 1) = rr + 1 + t by omega] using this

theorem armT_par (hsz : W.size = W'.size) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn po eo : V) (k a : Nat)
    (hpw : W.power (digitSum k n) = W'.power (digitSum k n))
    (hw : ∀ t < n, Stmt.renameList r (walkT W (first + t) (slots t) (if k = 0 then W.size + 13 else W.size)
        (dig k t) (walkBase (if k = 0 then W.size + 13 else W.size) k 0 t (if fold then a + 1 else a))) =
      Stmt.renameList r' (walkT W' (first + t) (slots t) (if k = 0 then W.size + 13 else W.size)
        (dig k t) (walkBase (if k = 0 then W.size + 13 else W.size) k 0 t (if fold then a + 1 else a))))
    (htail : ∀ x ∈ [V.n a, po, eo, prodIn, encIn, W.power (digitSum k n),
      V.n (walkBase W.size k 0 n (if fold then a + 1 else a))], r x = r' x) :
    Stmt.renameList r (armT W slots first n fold prodIn encIn po eo k a).1 =
      Stmt.renameList r' (armT W' slots first n fold prodIn encIn po eo k a).1 := by
  have hW : Stmt.renameList r (walksT W slots first k (if k = 0 then W.size + 13 else W.size) n 0
      (if fold then a + 1 else a)).1 = Stmt.renameList r' (walksT W' slots first k
        (if k = 0 then W.size + 13 else W.size) n 0 (if fold then a + 1 else a)).1 :=
    walksT_par slots first k _ n 0 _ fun t ht => by simpa using hw t ht
  have t0 := htail (.n a) (by simp)
  have t1 := htail po (by simp)
  have t2 := htail eo (by simp)
  have t3 := htail prodIn (by simp)
  have t4 := htail encIn (by simp)
  have t5 := htail (W.power (digitSum k n)) (by simp)
  have t6 := htail (.n (walkBase W.size k 0 n (if fold then a + 1 else a))) (by simp)
  have hsplit : ∀ U : WotsT, U.size = W.size → U.power (digitSum k n) = W.power (digitSum k n) →
      (armT U slots first n fold prodIn encIn po eo k a).1 =
        (if fold then [cst a (word 0 0 0)] else []) ++ (walksT U slots first k
          (if k = 0 then W.size + 13 else W.size) n 0 (if fold then a + 1 else a)).1 ++
        (if k = 0 then [if fold then copyS po (W.power (digitSum k n))
            else mulS po prodIn (W.power (digitSum k n)), copyS eo (if fold then .n a else encIn)]
          else [if fold then copyS po (W.power (digitSum k n))
            else mulS po prodIn (W.power (digitSum k n)),
            cst (walkBase W.size k 0 n (if fold then a + 1 else a)) (lit (k * 4 ^ first)),
            addS eo (if fold then .n a else encIn) (.n (walkBase W.size k 0 n (if fold then a + 1 else a)))]) := by
    intro U hU hP
    unfold armT
    rw [hU, hP]
    split
    · rfl
    · simp only [walksT_snd]
  rw [hsplit W rfl rfl, hsplit W' hsz.symm hpw.symm, renameList_eq_map, renameList_eq_map,
    List.map_append, List.map_append, List.map_append, List.map_append]
  rw [renameList_eq_map, renameList_eq_map] at hW
  rw [hW]
  congr 1
  · congr 1
    cases fold <;> simp [cst, Stmt.rename, Atom.rename, t0]
  · split <;> cases fold <;> simp only [Bool.false_eq_true, ↓reduceIte] at t6 <;>
      simp [cst, copyS, mulS, addS, Stmt.rename, Atom.rename, t0, t1, t2, t3, t4, t5, t6]
end

/-! ## `sp_wots`'s step renamed -/

/-- `x` is a numbered value below `X` off the run `B ..< B + 5`. -/
def PadGood (B X : Nat) (x : V) : Prop := ∃ j, x = .n j ∧ (j < B ∨ B + 5 ≤ j) ∧ j < X

theorem padGood_agree {B P X : Nat} {x : V} (h : PadGood B X x) :
    padRen B P x = padShift X P x := by
  obtain ⟨j, rfl, h1, h2⟩ := h
  rw [padRen_n]
  have e : ¬ (B ≤ j ∧ j < B + 5) := by omega
  simp only [e, ↓reduceIte, padShift, V.n, and_self, show ¬ X ≤ j by omega]

theorem padRen_run {B P j : Nat} (hj : j < 5) : padRen B P (.n (B + j)) = .n (P + j) := by
  rw [padRen_n]
  simp only [show B ≤ B + j ∧ B + j < B + 5 by omega, and_self, ↓reduceIte, Nat.add_sub_cancel_left]

theorem padShift_run {X P j : Nat} : padShift X P (.n (X + j)) = .n (P + j) := by
  simp only [padShift, V.n, and_self, ↓reduceIte, show X ≤ X + j by omega, Nat.add_sub_cancel_left]

/-- **The step renamed**: with its run at `B` moved by `padRen B P`, and at `X` by `padShift X P`,
when its other values are `PadGood`. -/
theorem spWp_par {B P X i s : Nat} {v : V} {c o : Nat} (hv : PadGood B X v)
    (hc : ∀ q < 3, PadGood B X (.n (c + q))) (h0 : PadGood B X (.n 0)) (h1 : PadGood B X (.n 1))
    (ho : ∀ q < 13, PadGood B X (.n (o + q))) :
    Stmt.renameList (padRen B P) ((spWp B).step i s v c o) =
      Stmt.renameList (padShift X P) ((spWp X).step i s v c o) := by
  have c0 := padGood_agree (P := P) (hc 0 (by norm_num))
  have c1 := padGood_agree (P := P) (hc 1 (by norm_num))
  have c2 := padGood_agree (P := P) (hc 2 (by norm_num))
  simp only [Nat.add_zero] at c0
  have hr : (runV o 13).map (padRen B P) = (runV o 13).map (padShift X P) := by
    unfold runV
    simp only [List.map_map]
    exact List.map_congr_left fun q hq => padGood_agree (ho q (List.mem_range.mp hq))
  have p0 := padRen_run (B := B) (P := P) (j := 0) (by norm_num)
  have p1 := padRen_run (B := B) (P := P) (j := 1) (by norm_num)
  have p2 := padRen_run (B := B) (P := P) (j := 2) (by norm_num)
  have p3 := padRen_run (B := B) (P := P) (j := 3) (by norm_num)
  have p4 := padRen_run (B := B) (P := P) (j := 4) (by norm_num)
  have q0 := padShift_run (X := X) (P := P) (j := 0)
  have q1 := padShift_run (X := X) (P := P) (j := 1)
  have q2 := padShift_run (X := X) (P := P) (j := 2)
  have q3 := padShift_run (X := X) (P := P) (j := 3)
  have q4 := padShift_run (X := X) (P := P) (j := 4)
  simp only [Nat.add_zero] at p0 q0
  simp only [renameList_eq_map, spWp, k48At, cst, addS, kecS, List.map_cons, List.map_nil,
    Stmt.rename, Atom.rename, c0, c1, c2, padGood_agree hv, padGood_agree h0, padGood_agree h1, hr,
    p0, p1, p2, p3, p4, q0, q1, q2, q3, q4]

/-! ## An arm renamed -/

theorem walkT_sub_armT (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn po eo : V) (k a : Nat) {t : Nat} (ht : t < n) {x : Stmt}
    (hx : x ∈ walkT W (first + t) (slots t) (if k = 0 then W.size + 13 else W.size) (dig k t)
      (walkBase (if k = 0 then W.size + 13 else W.size) k 0 t (if fold then a + 1 else a))) :
    x ∈ (armT W slots first n fold prodIn encIn po eo k a).1 := by
  have hm := mem_walksT W slots first k (if k = 0 then W.size + 13 else W.size) n 0
    (if fold then a + 1 else a) t ht x (by simpa using hx)
  unfold armT
  dsimp only
  by_cases hk : k = 0 <;> simp only [hk, ↓reduceIte, List.mem_append] at hm ⊢ <;> exact Or.inl (Or.inr hm)

theorem mem_valsList_ex : ∀ {L : List Stmt} {v : V}, v ∈ Stmt.valsList L → ∃ y ∈ L, v ∈ y.vals
  | [], _, h => absurd h (by simp)
  | y :: L, v, h => by
      rw [valsList_cons, List.mem_append] at h
      rcases h with h | h
      · exact ⟨y, List.mem_cons_self .., h⟩
      · obtain ⟨z, hz, hv⟩ := mem_valsList_ex h
        exact ⟨z, List.mem_cons_of_mem _ hz, hv⟩

theorem padGood_of {B X j : Nat} (h1 : j < B ∨ B + 5 ≤ j) (h2 : j < X) : PadGood B X (.n j) :=
  ⟨j, rfl, h1, h2⟩

/-- **An arm renamed**: with its run at `B` moved by `padRen B P`, and virtual moved by
`padShift spVPad P`, when its walks are laid out above `B + 5`, its values below `E ≤ spVPad` and
its other values `PadGood`. -/
theorem spArm_par {B P E : Nat} {slots : Nat → Nat → Nat} {first n : Nat} {fold : Bool}
    {prodIn encIn po eo : V} {k a : Nat} (hB : 2 ≤ B) (hBX : B + 5 ≤ spVPad) (hEX : E ≤ spVPad)
    (hE : ∀ x ∈ Stmt.valsList (armT (spWp B) slots first n fold prodIn encIn po eo k a).1,
      ∃ j, x = .n j ∧ j < E)
    (hwl : ∀ t < n, WalkLay (spWp B) (B + 5) (slots t) (if k = 0 then 3 + 13 else 3) (dig k t)
      (walkBase (if k = 0 then 3 + 13 else 3) k 0 t (if fold then a + 1 else a)))
    (htail : ∀ x ∈ [V.n a, po, eo, prodIn, encIn, V.n (3 + digitSum k n),
      V.n (walkBase 3 k 0 n (if fold then a + 1 else a))], PadGood B spVPad x) :
    Stmt.renameList (padRen B P) (armT (spWp B) slots first n fold prodIn encIn po eo k a).1 =
      Stmt.renameList (padShift spVPad P) (armT spW slots first n fold prodIn encIn po eo k a).1 := by
  rw [← spWp_virtual]
  have hgood : ∀ x ∈ Stmt.valsList (armT (spWp B) slots first n fold prodIn encIn po eo k a).1,
      ∀ j, x = .n j → B + 5 ≤ j → PadGood B spVPad x := by
    intro x hx j hj hb
    obtain ⟨j', e, hj'⟩ := hE x hx
    rw [hj] at e
    simp only [V.mk.injEq, true_and] at e
    subst e
    rw [hj]
    exact padGood_of (Or.inr hb) (by omega)
  refine armT_par (W := spWp B) (W' := spWp spVPad) rfl slots first n fold prodIn encIn po eo k a rfl
    (fun t ht => ?_) (fun x hx => padGood_agree (htail x hx))
  have e3 : (spWp B).size = 3 := rfl
  simp only [e3]
  have hl := hwl t ht
  generalize hS : (if k = 0 then 3 + 13 else 3) = S at hl ⊢
  generalize hbw : walkBase S k 0 t (if fold then a + 1 else a) = bw at hl ⊢
  have hsub : ∀ x ∈ walkT (spWp B) (first + t) (slots t) S (dig k t) bw, ∀ v ∈ x.vals,
      v ∈ Stmt.valsList (armT (spWp B) slots first n fold prodIn encIn po eo k a).1 := by
    intro x hx v hv
    refine mem_valsList_of_mem (walkT_sub_armT _ slots first n fold prodIn encIn po eo k a ht ?_) hv
    simp only [e3, hS, hbw]
    exact hx
  refine walkT_par _ _ _ _ _ ?_ (fun j hj => ?_)
  · have hm : ∃ x ∈ walkT (spWp B) (first + t) (slots t) S (dig k t) bw,
        walkStartV (slots t) (dig k t) bw ∈ x.vals :=
      ⟨_, walkStart_mem _ _ _ _ _ _, by simp [hintW, Stmt.vals, Atom.vals, Hint.vals, Dest.vals]⟩
    obtain ⟨x, hx, hv⟩ := hm
    have hv' := hsub x hx _ hv
    by_cases h3 : dig k t = 3
    · simp only [walkStartV, h3, ↓reduceIte] at hv' ⊢
      exact padGood_agree (hgood _ hv' _ rfl (hl.slotB 2 (by norm_num)))
    · simp only [walkStartV, h3, ↓reduceIte] at hv' ⊢
      exact padGood_agree (hgood _ hv' _ rfl hl.base)
  · have hd3 : dig k t ≠ 3 := fun h => by omega
    have mem : ∀ v, v ∈ Stmt.valsList ((spWp B).step (first + t) (dig k t + j)
        (if j = 0 then .n bw else .n (slots t (dig k t + j - 1))) (bw + 1 + j * S) (slots t (dig k t + j))) →
        v ∈ Stmt.valsList (armT (spWp B) slots first n fold prodIn encIn po eo k a).1 := by
      intro v hv
      obtain ⟨y, hy, hv'⟩ := mem_valsList_ex hv
      exact hsub y (mem_walkT_step _ hd3 hj hy) v hv'
    have hc : B + 5 ≤ bw + 1 + j * S := by have := hl.base; omega
    have hsl := hl.slotB (dig k t + j) (by omega)
    refine spWp_par ?_ (fun q hq => ?_) (padGood_of (j := 0) (Or.inl (by omega)) (by omega))
      (padGood_of (j := 1) (Or.inl (by omega)) (by omega)) (fun q hq => ?_)
    · have hv := mem _ (spWp_mem_vals _ _ _ _ _ _ (Or.inl rfl))
      by_cases hj0 : j = 0
      · simp only [hj0, ↓reduceIte] at hv ⊢
        exact hgood _ hv _ rfl hl.base
      · simp only [hj0, ↓reduceIte] at hv ⊢
        exact hgood _ hv _ rfl (hl.slotB _ (by omega))
    · exact hgood _ (mem _ (spWp_mem_vals _ _ _ _ _ _ (Or.inr (Or.inl ⟨q, hq, rfl⟩)))) _ rfl (by omega)
    · exact hgood _ (mem _ (spWp_mem_vals _ _ _ _ _ _ (Or.inr (Or.inr ⟨q, hq, rfl⟩)))) _ rfl (by omega)

end
end LeanVM.Guest.B1.Sig
