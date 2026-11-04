/-
  LeanVM.Guest.B1.Sig.SpWotsStepComplete

  `sp_wots`'s chain step with its padding run at a base of our choice, for completeness: in
  single-assignment form, reading and writing canonical cells.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsPadComplete
public import LeanVM.Guest.B1.Sig.XmssStep

/-!
# `sp_wots`'s chain step, complete

* `spWp X`: `spW` with its padding run at `X` (`spWp spVPad = spW`); for completeness the run is
  put at a group's digit cells `b ..< b + 5`, below the arms' values;
* `k48At_ssa`, `k48At_fwd_canon`: the 48-byte `keccak` is in single-assignment form and reads and
  writes canonical cells;
* `SpGood b σ`: the values the step reads: `pp`, the key's address, the run at `b`;
  `spWp_shape`, `spWp_canon`, `spWp_atoms`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- `spW` with its padding run at `X`. -/
def spWp (X : Nat) : WotsT where
  step i s v c o := cst c (word (tw 1 + i * hiMul + s * stepMul) 0 0) ::
    addS (.n (c + 1)) (.n 1) (.n c) :: k48At (.n 0) X (.n (c + 1)) v (c + 2) o
  size := 3
  power s := .n (3 + s)

theorem spWp_virtual : spWp spVPad = spW := rfl

theorem k48_ins (pad : Nat) (m0 m1 m2 : V) (c : Nat) (x : V) :
    x ∈ [m0, m1, m2, .n pad, .n (pad + 1), .n (pad + 2), .n (pad + 3), .n (pad + 4), .n c, .n (pad + 1),
      .n (pad + 2), .n (pad + 3), .n (pad + 4)] ↔ x ∈ [m0, m1, m2] ∨ x = .n c ∨ InR pad 5 x := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, InR]
  constructor
  · rintro (h | h | h | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals first | exact Or.inl (by simp [h]) | exact Or.inr (Or.inl rfl) |
      exact Or.inr (Or.inr ⟨0, by omega, rfl⟩) | exact Or.inr (Or.inr ⟨1, by omega, rfl⟩) |
      exact Or.inr (Or.inr ⟨2, by omega, rfl⟩) | exact Or.inr (Or.inr ⟨3, by omega, rfl⟩) |
      exact Or.inr (Or.inr ⟨4, by omega, rfl⟩)
  · rintro ((h | h | h) | rfl | ⟨j, hj, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · simp
    · interval_cases j <;> simp

theorem spWp_atoms (X : Nat) : StepAtoms (spWp X) := fun _ _ _ _ _ => rfl

theorem spWp_outs (X i s : Nat) (v : V) (c o : Nat) :
    outsList ((spWp X).step i s v c o) = .n c :: .n (c + 1) :: .n (c + 2) :: runV o 13 := by
  simp [spWp, k48At, cst, addS, kecS, outsList, aOuts]

theorem spWp_vals (X i s : Nat) (v : V) (c o : Nat) {x : V}
    (hx : x ∈ Stmt.valsList ((spWp X).step i s v c o)) :
    x = v ∨ x = .n 0 ∨ x = .n 1 ∨ InR X 5 x ∨ InR c 3 x ∨ InR o 13 x := by
  simp only [spWp, k48At, cst, addS, kecS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals,
    List.append_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | (rfl | rfl | rfl) | rfl | hx | hx
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨0, by norm_num, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨1, by norm_num, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨0, by norm_num, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨2, by norm_num, rfl⟩))))
  · have hx' : x ∈ [V.n 0, .n (c + 1), v, .n X, .n (X + 1), .n (X + 2), .n (X + 3), .n (X + 4),
        .n (c + 2), .n (X + 1), .n (X + 2), .n (X + 3), .n (X + 4)] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; tauto
    rcases (k48_ins X (.n 0) (.n (c + 1)) v (c + 2) x).mp hx' with h | rfl | h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨1, by norm_num, rfl⟩))))
      · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨2, by norm_num, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (mem_runV.mp hx)))))

theorem spWp_mem_vals (X i s : Nat) (v : V) (c o : Nat) {x : V}
    (hx : x = v ∨ (∃ q < 3, x = .n (c + q)) ∨ InR o 13 x) :
    x ∈ Stmt.valsList ((spWp X).step i s v c o) := by
  simp only [spWp, k48At, cst, addS, kecS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals,
    List.append_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  rcases hx with rfl | ⟨q, hq, rfl⟩ | h
  · simp
  · interval_cases q <;> simp
  · exact Or.inr (Or.inr (Or.inr (Or.inr (mem_runV.mpr h))))

/-- **The step is in single-assignment form** from bases above `B`, its run below `B`. -/
theorem spWp_shape {b B : Nat} (hB : b + 5 ≤ B) (h2 : 2 ≤ B) : StepShape (spWp b) B := by
  intro i s v c o hc ho hco h1 h2'
  have hsz : (spWp b).size = 3 := rfl
  rw [hsz] at hco
  have hvo : ∀ j < 13, v ≠ .n (o + j) := fun j hj e => h2' ⟨j, hj, e⟩
  refine ⟨?_, fun x hx => ?_, fun x hx => ?_⟩
  · show SSA [cst c _, addS (.n (c + 1)) (.n 1) (.n c), cst (c + 2) _, kecS [.n 0, .n (c + 1), v,
      .n b, .n (b + 1), .n (b + 2), .n (b + 3), .n (b + 4), .n (c + 2), .n (b + 1), .n (b + 2),
      .n (b + 3), .n (b + 4)] (runV o 13) false false]
    have hr : ∀ x ∈ runV o 13, ∃ j < 13, x = .n (o + j) := fun x hx => mem_runV.mp hx
    refine ⟨trivial, fun x hx h => by simp [aReads] at h, fun x hx h => ?_, trivial, fun x hx h => ?_,
      fun x hx h => ?_, trivial, fun x hx h => by simp [aReads] at h, fun x hx h => ?_,
      ⟨rfl, by simp [runV], runV_nodup o 13⟩, fun x hx h => ?_, fun x hx => by simp [outsList] at hx,
      trivial⟩
    · simp only [outsList, cst, addS, kecS, aOuts, List.cons_append, List.nil_append, List.append_nil,
        List.mem_cons] at hx
      simp only [Atom.vals, List.mem_singleton] at h
      subst h
      rcases hx with e | e | hx
      · simp at e
      · simp at e
      · obtain ⟨j, hj, e⟩ := hr _ hx; simp at e; omega
    · simp only [aOuts, List.mem_singleton] at hx
      subst hx
      simp only [aReads, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with e | e <;> first | (simp at e; done) | (simp at e; omega)
    · simp only [outsList, cst, kecS, aOuts, List.cons_append, List.nil_append, List.append_nil,
        List.mem_cons] at hx
      simp only [Atom.vals, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases hx with rfl | hx
      · rcases h with e | e | e <;> simp at e
      · obtain ⟨j, hj, rfl⟩ := hr _ hx
        rcases h with e | e | e <;> simp at e <;> omega
    · simp only [outsList, kecS, aOuts, List.append_nil] at hx
      simp only [Atom.vals, List.mem_singleton] at h
      obtain ⟨j, hj, rfl⟩ := hr _ hx
      simp at h; omega
    · simp only [aOuts] at hx
      simp only [aReads] at h
      obtain ⟨j, hj, rfl⟩ := hr _ hx
      rcases (k48_ins b (.n 0) (.n (c + 1)) v (c + 2) _).mp h with h | e | ⟨k, hk, e⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with e | e | e
        · simp at e; omega
        · simp at e; omega
        · exact hvo j hj e.symm
      · simp at e; omega
      · simp at e; omega
  · rw [spWp_outs] at hx
    simp only [List.mem_cons, mem_runV] at hx
    rcases hx with rfl | rfl | rfl | h
    · exact Or.inl ⟨0, by simp [spWp], rfl⟩
    · exact Or.inl ⟨1, by simp [spWp], rfl⟩
    · exact Or.inl ⟨2, by simp [spWp], rfl⟩
    · exact Or.inr h
  · rcases spWp_vals b i s v c o hx with h | rfl | rfl | ⟨j, hj, rfl⟩ | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨0, by omega, rfl⟩)
    · exact Or.inr (Or.inl ⟨1, by omega, rfl⟩)
    · exact Or.inr (Or.inl ⟨b + j, by omega, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl (by simpa [spWp] using h)))
    · exact Or.inr (Or.inr (Or.inr h))

/-- The values `sp_wots`'s step reads: `pp`, the key's address and the padding run at `b`. -/
def SpGood (b : Nat) (σ : Val) : Prop :=
  IsCanonical128 (σ (.n 0)) ∧ IsCanonical128 (σ (.n 1)) ∧ PadOK σ b

theorem spGood_congr {b B : Nat} (hB : b + 5 ≤ B) (h2 : 2 ≤ B) {σ σ' : Val}
    (hσ : AgreeBelow B σ σ') (h : SpGood b σ) : SpGood b σ' := by
  obtain ⟨g0, g1, g2⟩ := h
  exact ⟨by rw [hσ.apply ⟨0, by omega, rfl⟩]; exact g0, by rw [hσ.apply ⟨1, by omega, rfl⟩]; exact g1,
    g2.congr (b := B) hB hσ⟩

/-- **The step reads and writes canonical cells.** -/
theorem spWp_canon {b B : Nat} (hB : b + 5 ≤ B) (h2 : 2 ≤ B) :
    StepCanon (spWp b) B (SpGood b) := by
  refine ⟨fun σ σ' hσ h => spGood_congr hB h2 hσ h, fun i s v c o σ hc ho hco h1 h2' hg hv => ?_⟩
  obtain ⟨g0, g1, g2⟩ := hg
  have hvc : ∀ j < 3, v ≠ .n (c + j) := fun j hj e => h1 ⟨j, hj, e⟩
  have hvo : ∀ j < 13, v ≠ .n (o + j) := fun j hj e => h2' ⟨j, hj, e⟩
  have hsz : (spWp b).size = 3 := rfl
  rw [hsz] at hco
  set σ1 := Function.update σ (.n c) (word (tw 1 + i * hiMul + s * stepMul) 0 0) with hσ1
  set σ2 := Function.update σ1 (.n (c + 1)) (σ1 (.n 1) + σ1 (.n c)) with hσ2
  set σ3 := Function.update σ2 (.n (c + 2)) (word (2 ^ 63) 0 0) with hσ3
  set ins : List V := [.n 0, .n (c + 1), v, .n b, .n (b + 1), .n (b + 2), .n (b + 3), .n (b + 4),
    .n (c + 2), .n (b + 1), .n (b + 2), .n (b + 3), .n (b + 4)] with hins
  have hf : fwd ((spWp b).step i s v c o) σ = updL σ3 (runV o 13) (kOut (ins.map σ3) false false) := rfl
  have hne : ∀ {x y : Nat}, x ≠ y → V.n x ≠ V.n y := fun h e => h (by simpa using e)
  -- the values the keccak reads
  have e0 : σ3 (.n 0) = σ (.n 0) := by
    rw [hσ3, Function.update_of_ne (hne (by omega)), hσ2, Function.update_of_ne (hne (by omega)),
      hσ1, Function.update_of_ne (hne (by omega))]
  have e1 : σ3 (.n (c + 1)) = σ (.n 1) + word (tw 1 + i * hiMul + s * stepMul) 0 0 := by
    rw [hσ3, Function.update_of_ne (hne (by omega)), hσ2, Function.update_self, hσ1,
      Function.update_of_ne (hne (by omega)), Function.update_self]
  have ev : σ3 v = σ v := by
    rw [hσ3, Function.update_of_ne (hvc 2 (by norm_num)), hσ2, Function.update_of_ne (hvc 1 (by norm_num)),
      hσ1, Function.update_of_ne (by simpa using hvc 0 (by norm_num))]
  have ep : ∀ k < 5, σ3 (.n (b + k)) = σ (.n (b + k)) := fun k hk => by
    rw [hσ3, Function.update_of_ne (hne (by omega)), hσ2, Function.update_of_ne (hne (by omega)),
      hσ1, Function.update_of_ne (hne (by omega))]
  have ec : σ3 (.n (c + 2)) = word (2 ^ 63) 0 0 := by rw [hσ3, Function.update_self]
  refine ⟨fun ins' outs i' o' hmem cc => ?_, fun j hj => ?_⟩
  · simp only [spWp, k48At, cst, addS, kecS, List.mem_cons, Stmt.atom.injEq, reduceCtorEq, false_or,
      List.not_mem_nil, or_false, Atom.keccak.injEq] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    rw [hf]
    have hmap : ∀ x ∈ ins, updL σ3 (runV o 13) (kOut (ins.map σ3) false false) x = σ3 x := by
      intro x hx
      refine updL_of_not_mem σ3 _ _ fun h => ?_
      rw [mem_runV] at h
      obtain ⟨j, hj, rfl⟩ := h
      rcases (k48_ins b (.n 0) (.n (c + 1)) v (c + 2) _).mp hx with h | e | ⟨k, hk, e⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with e | e | e
        · simp only [V.mk.injEq, true_and] at e; omega
        · simp only [V.mk.injEq, true_and] at e; omega
        · exact hvo j hj e.symm
      · simp only [V.mk.injEq, true_and] at e; omega
      · simp only [V.mk.injEq, true_and] at e; omega
    rw [List.map_congr_left hmap]
    obtain ⟨q0, q1, q2, q3, q4⟩ := g2
    have p0 := ep 0 (by norm_num)
    have p1 := ep 1 (by norm_num)
    have p2 := ep 2 (by norm_num)
    have p3 := ep 3 (by norm_num)
    have p4 := ep 4 (by norm_num)
    simp only [Nat.add_zero] at p0
    have ha : IsCanonical128 (σ (.n 1) + word (tw 1 + i * hiMul + s * stepMul) 0 0) :=
      canon_add g1 (canon_word _ _)
    fin_cases cc <;> simp [hins, cells13, q0, q1, q2, q3, q4, p0, p1, p2, p3, p4, e0, e1, ev, ec] <;>
      first | exact g0 | exact ha | exact hv | exact canon_word _ _ | exact canon_zero
  · rw [hf]
    have := updL_at σ3 (runV o 13) (kOut (ins.map σ3) false false) (runV_nodup o 13) j
      (by simp [runV]; exact hj)
    have hj' : (runV o 13)[j]'(by simp [runV]; exact hj) = .n (o + j) := by simp [runV]
    rw [hj'] at this
    rw [this]
    exact canon_kOut _ _ _ _

end
end LeanVM.Guest.B1.Sig
