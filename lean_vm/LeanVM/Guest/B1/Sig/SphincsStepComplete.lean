/-
  LeanVM.Guest.B1.Sig.SphincsStepComplete

  leanSPHINCS's one-time chain step, for completeness: a step equal to `sW` on the chains, steps
  and powers the codeword uses, its powers below the codeword's base.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsTail
public import LeanVM.Guest.B1.Sig.XmssStep

/-!
# leanSPHINCS's chain step, complete

* `k48_ssa`, `k48_fwd_canon`: a 48-byte `keccak` is in single-assignment form and reads and writes
  canonical cells;
* `sWc`: `sW` with its power clamped to the ones the codeword uses (`sW_weq`);
* `SGood`: the values the step reads: `P`, the leaf index, the padding run and the powers;
  `sWc_shape`, `sWc_canon`, `sWc_sound`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

variable {rd : Reader}

theorem k48_ins (a v : V) (c : Nat) (x : V) :
    x ∈ [sPP, a, v, .n sPad, .n (sPad + 1), .n (sPad + 2), .n (sPad + 3), .n (sPad + 4), .n c,
      .n (sPad + 1), .n (sPad + 2), .n (sPad + 3), .n (sPad + 4)] ↔
      x ∈ [sPP, a, v] ∨ x = .n c ∨ InR sPad 5 x := by
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

/-- **A 48-byte `keccak` is in single-assignment form**, its inputs off its outputs. -/
theorem k48_ssa {a v : V} {c o : Nat} (hco : c + 1 ≤ o ∨ o + 13 ≤ c)
    (hm : ∀ x ∈ [sPP, a, v], ¬ InR o 13 x) (hpo : sPad + 5 ≤ o) : SSA (k48 a v c o) := by
  refine ⟨trivial, fun x hx h => by simp [aReads] at h, fun x hx h => ?_, ⟨rfl, by simp [runV],
    runV_nodup o 13⟩, fun x hx h => ?_, fun x hx => by simp [outsList] at hx, trivial⟩
  · simp only [outsList, aOuts, List.append_nil, kecS] at hx
    rw [mem_runV] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    simp only [Atom.vals, List.mem_singleton, V.mk.injEq, true_and] at h
    omega
  · simp only [aOuts] at hx
    rw [mem_runV] at hx
    simp only [aReads] at h
    rcases (k48_ins a v c x).mp h with h | rfl | ⟨k, hk, rfl⟩
    · exact hm x h hx
    · obtain ⟨j, hj, e⟩ := hx
      simp only [V.mk.injEq, true_and] at e
      omega
    · obtain ⟨j, hj, e⟩ := hx
      simp only [V.mk.injEq, true_and] at e
      omega

theorem k48_outs (a v : V) (c o : Nat) : outsList (k48 a v c o) = .n c :: runV o 13 := by
  simp [k48, cst, kecS, outsList, aOuts]

theorem k48_vals (a v : V) (c o : Nat) {x : V} (hx : x ∈ Stmt.valsList (k48 a v c o)) :
    x ∈ [sPP, a, v] ∨ x = .n c ∨ InR sPad 5 x ∨ InR o 13 x := by
  simp only [k48, cst, kecS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil,
    List.mem_append, List.mem_singleton] at hx
  rcases hx with rfl | hx | hx
  · exact Or.inr (Or.inl rfl)
  · rcases (k48_ins a v c x).mp hx with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (mem_runV.mp hx)))

/-- **A 48-byte `keccak` reads and writes canonical cells**, its inputs canonical and the padding
run set. -/
theorem k48_fwd_canon {a v : V} {c o : Nat} (σ : Val) (hco : c + 1 ≤ o ∨ o + 13 ≤ c)
    (hm : ∀ x ∈ [sPP, a, v], ¬ InR o 13 x ∧ x ≠ .n c ∧ IsCanonical128 (σ x))
    (hpc : sPad + 5 ≤ c) (hpo : sPad + 5 ≤ o) (hp : PadOK σ sPad) :
    KCanon (fwd (k48 a v c o) σ) (k48 a v c o) ∧
      ∀ j < 13, IsCanonical128 (fwd (k48 a v c o) σ (.n (o + j))) := by
  set σ1 := Function.update σ (.n c) (word (2 ^ 63) 0 0) with hσ1
  have hf : fwd (k48 a v c o) σ = updL σ1 (runV o 13)
      (kOut ([sPP, a, v, .n sPad, .n (sPad + 1), .n (sPad + 2), .n (sPad + 3), .n (sPad + 4), .n c,
        .n (sPad + 1), .n (sPad + 2), .n (sPad + 3), .n (sPad + 4)].map σ1) false false) := rfl
  refine ⟨fun ins outs i o' hmem cc => ?_, fun j hj => ?_⟩
  · simp only [k48, cst, kecS, List.mem_cons, Stmt.atom.injEq, reduceCtorEq, false_or,
      List.not_mem_nil, or_false, Atom.keccak.injEq] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    rw [hf]
    have hmap : ∀ x ∈ [sPP, a, v, .n sPad, .n (sPad + 1), .n (sPad + 2), .n (sPad + 3), .n (sPad + 4),
        .n c, .n (sPad + 1), .n (sPad + 2), .n (sPad + 3), .n (sPad + 4)], updL σ1 (runV o 13)
        (kOut ([sPP, a, v, .n sPad, .n (sPad + 1), .n (sPad + 2), .n (sPad + 3), .n (sPad + 4), .n c,
          .n (sPad + 1), .n (sPad + 2), .n (sPad + 3), .n (sPad + 4)].map σ1) false false) x = σ1 x := by
      intro x hx
      refine updL_of_not_mem σ1 _ _ fun h => ?_
      rw [mem_runV] at h
      rcases (k48_ins a v c x).mp hx with h' | rfl | ⟨k, hk, rfl⟩
      · exact (hm x h').1 h
      · obtain ⟨j, hj, e⟩ := h
        simp only [V.mk.injEq, true_and] at e
        omega
      · obtain ⟨j, hj, e⟩ := h
        simp only [V.mk.injEq, true_and] at e
        omega
    rw [List.map_congr_left hmap]
    have h3 : ∀ x ∈ [sPP, a, v], IsCanonical128 (σ1 x) := fun x hx => by
      rw [hσ1, Function.update_of_ne (hm x hx).2.1]
      exact (hm x hx).2.2
    have hpk : ∀ k < 5, σ1 (.n (sPad + k)) = σ (.n (sPad + k)) := fun k hk => by
      rw [hσ1, Function.update_of_ne (by simp; omega)]
    have hc1 : σ1 (.n c) = word (2 ^ 63) 0 0 := by rw [hσ1, Function.update_self]
    obtain ⟨q0, q1, q2, q3, q4⟩ := hp
    have p0 := hpk 0 (by norm_num)
    have p1 := hpk 1 (by norm_num)
    have p2 := hpk 2 (by norm_num)
    have p3 := hpk 3 (by norm_num)
    have p4 := hpk 4 (by norm_num)
    simp only [Nat.add_zero] at p0
    fin_cases cc <;> simp [cells13, q0, q1, q2, q3, q4, p0, p1, p2, p3, p4, hc1] <;>
      first | exact h3 _ (by simp) | exact canon_word _ _ | exact canon_zero
  · rw [hf]
    have := updL_at σ1 (runV o 13) (kOut ([sPP, a, v, .n sPad, .n (sPad + 1), .n (sPad + 2),
      .n (sPad + 3), .n (sPad + 4), .n c, .n (sPad + 1), .n (sPad + 2), .n (sPad + 3),
      .n (sPad + 4)].map σ1) false false) (runV_nodup o 13) j (by simp [runV]; exact hj)
    have hj' : (runV o 13)[j]'(by simp [runV]; exact hj) = .n (o + j) := by simp [runV]
    rw [hj'] at this
    rw [this]
    exact canon_kOut _ _ _ _

/-! ## The step -/

/-- **`sW` clamped**: the power clamped to the ones the codeword uses, so that all its constants
lie below the codeword. -/
def sWc (pb : Nat) : WotsT := sWots fun s => .n (pb + min s 9)

theorem sW_weq : WEq sW (sWc sEnc.2.1) 64 :=
  ⟨rfl, fun _ _ _ _ => rfl, fun j hj => by
    simp only [sW, sWc, sWots, Nat.min_eq_left (show j ≤ 9 by omega)]⟩

/-- The values leanSPHINCS's chain step reads. -/
def SGood (pb : Nat) (σ : Val) : Prop :=
  IsCanonical128 (σ sPP) ∧ IsCanonical128 (σ (sNode 0)) ∧ PadOK σ sPad ∧
    ∀ s < 10, σ (.n (pb + s)) = gen ^ s

theorem sWc_atoms (pb : Nat) : StepAtoms (sWc pb) := fun _ _ _ _ _ => rfl

theorem sWc_step (pb i s : Nat) (v : V) (c o : Nat) : (sWc pb).step i s v c o =
    [cst c (word (tw 1 + i * hiMul + s * stepMul) 0 0), addS (.n (c + 1)) (sNode 0) (.n c)] ++
      k48 (.n (c + 1)) v (c + 2) o := rfl

theorem sWc_shape {pb : Nat} (hB : 132 ≤ pb) : StepShape (sWc pb) (pb + 10) := by
  intro i s v c o hc ho hco h1 h2
  have hsz : (sWc pb).size = 3 := rfl
  rw [hsz] at hco h1
  have hv0 : v ≠ .n c := fun e => h1 ⟨0, by norm_num, by rw [e]; rfl⟩
  have hv1 : v ≠ .n (c + 1) := fun e => h1 ⟨1, by norm_num, by rw [e]⟩
  have hv2 : v ≠ .n (c + 2) := fun e => h1 ⟨2, by norm_num, by rw [e]⟩
  rw [sWc_step, hsz]
  refine ⟨?_, fun x hx => ?_, fun x hx => ?_⟩
  · refine SSA.append' (P := fun x => x = .n c ∨ x = .n (c + 1) ∨ x = sNode 0)
      (Q := fun x => x = .n (c + 2) ∨ InR o 13 x) ?_ (k48_ssa (by omega) (fun x hx => ?_)
        (by simp [sPad]; omega)) (fun x hx => ?_) (fun x hx => ?_) (fun x hq hp => ?_)
    · refine ⟨trivial, fun x hx h => by simp [aReads] at h, fun x hx h => ?_, trivial,
        fun x hx h => ?_, fun x hx => by simp [outsList] at hx, trivial⟩
      · simp only [outsList, aOuts, addS, List.append_nil, List.mem_singleton] at hx
        simp only [Atom.vals, List.mem_singleton] at h
        rw [hx] at h
        simp at h
      · simp only [aOuts, List.mem_singleton] at hx
        simp only [aReads, List.mem_cons, List.not_mem_nil, or_false] at h
        rw [hx] at h
        rcases h with h | h
        · simp [sNode] at h; omega
        · simp at h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · rintro ⟨j, hj, e⟩; simp [sPP] at e; omega
      · rintro ⟨j, hj, e⟩; simp only [V.mk.injEq, true_and] at e; omega
      · exact h2
    · simp only [cst, addS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil,
        List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
      · exact Or.inl rfl
    · rw [k48_outs] at hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inl rfl
      · exact Or.inr (mem_runV.mp hx)
    · rcases hp with rfl | rfl | rfl <;> rcases hq with e | ⟨j, hj, e⟩ <;>
        simp [sNode] at e <;> omega
  · rw [outsList_append, k48_outs] at hx
    simp only [outsList, aOuts, cst, addS, List.append_nil, List.cons_append, List.nil_append,
      List.mem_cons] at hx
    rcases hx with rfl | rfl | rfl | hx
    · exact Or.inl ⟨0, by norm_num, rfl⟩
    · exact Or.inl ⟨1, by norm_num, rfl⟩
    · exact Or.inl ⟨2, by norm_num, rfl⟩
    · exact Or.inr (mem_runV.mp hx)
  · rw [valsList_append] at hx
    rcases List.mem_append.mp hx with hx | hx
    · simp only [cst, addS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil,
        List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inl ⟨0, by norm_num, rfl⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨1, by norm_num, rfl⟩))
      · exact Or.inr (Or.inl ⟨_, by omega, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨0, by norm_num, rfl⟩))
    · rcases k48_vals _ _ _ _ hx with hx | rfl | ⟨k, hk, rfl⟩ | hx
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact Or.inr (Or.inl ⟨2, by omega, rfl⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨1, by norm_num, rfl⟩))
        · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inl ⟨2, by norm_num, rfl⟩))
      · exact Or.inr (Or.inl ⟨_, by simp [sPad]; omega, rfl⟩)
      · exact Or.inr (Or.inr (Or.inr hx))

theorem sGood_congr {pb : Nat} (hB : 132 ≤ pb) {σ σ' : Val} (hσ : AgreeBelow (pb + 10) σ σ')
    (h : SGood pb σ) : SGood pb σ' := by
  obtain ⟨g1, g2, g3, g4⟩ := h
  refine ⟨by show IsCanonical128 (σ' (.n 2)); rw [hσ.apply ⟨2, by omega, rfl⟩]; exact g1,
    by show IsCanonical128 (σ' (.n 131)); rw [hσ.apply ⟨131, by omega, rfl⟩]; exact g2,
    g3.congr (b := pb + 10) (by simp [sPad]; omega) hσ, fun s hs => ?_⟩
  rw [hσ.apply ⟨_, by omega, rfl⟩]; exact g4 s hs

theorem sWc_canon {pb : Nat} (hB : 132 ≤ pb) : StepCanon (sWc pb) (pb + 10) (SGood pb) := by
  refine ⟨fun σ σ' hσ h => sGood_congr hB hσ h, fun i s v c o σ hc ho hco h1 h2 hg hv => ?_⟩
  obtain ⟨g1, g2, g3, -⟩ := hg
  have hsz : (sWc pb).size = 3 := rfl
  rw [hsz] at hco h1
  have hv0 : v ≠ .n c := fun e => h1 ⟨0, by norm_num, by rw [e]; rfl⟩
  have hv1 : v ≠ .n (c + 1) := fun e => h1 ⟨1, by norm_num, by rw [e]⟩
  have hv2 : v ≠ .n (c + 2) := fun e => h1 ⟨2, by norm_num, by rw [e]⟩
  set w := word (tw 1 + i * hiMul + s * stepMul) 0 0 with hw
  set σa := Function.update σ (.n c) w with hσa
  set σb := Function.update σa (.n (c + 1)) (σa (sNode 0) + σa (.n c)) with hσb
  have hfw : fwd ((sWc pb).step i s v c o) σ = fwd (k48 (.n (c + 1)) v (c + 2) o) σb := rfl
  have hb : ∀ x, x ≠ .n c → x ≠ .n (c + 1) → σb x = σ x := fun x e0 e1 => by
    rw [hσb, Function.update_of_ne e1, hσa, Function.update_of_ne e0]
  have hn0 : σb (sNode 0) = σ (sNode 0) := hb _ (by simp [sNode]; omega) (by simp [sNode]; omega)
  have hb1 : σb (.n (c + 1)) = σ (sNode 0) + w := by
    rw [hσb, Function.update_self, hσa, Function.update_of_ne (by simp [sNode]; omega), Function.update_self]
  have hk := k48_fwd_canon (a := .n (c + 1)) (v := v) (c := c + 2) (o := o) σb (by omega)
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · refine ⟨by rintro ⟨j, hj, e⟩; simp [sPP] at e; omega, by simp [sPP]; omega, ?_⟩
        rw [hb _ (by simp [sPP]; omega) (by simp [sPP]; omega)]; exact g1
      · refine ⟨by rintro ⟨j, hj, e⟩; simp only [V.mk.injEq, true_and] at e; omega, by simp, ?_⟩
        rw [hb1]; exact canon_add g2 (canon_word _ _)
      · exact ⟨h2, hv2, by rw [hb _ hv0 hv1]; exact hv⟩)
    (by simp [sPad]; omega) (by simp [sPad]; omega)
    (g3.congr (b := c) (by simp [sPad]; omega) (fun k hk => (hb (.n k) (by simp; omega) (by simp; omega)).symm))
  refine ⟨fun ins outs io oo hmem => ?_, fun j hj => by rw [hfw]; exact hk.2 j hj⟩
  rw [hfw]
  refine hk.1 ins outs io oo ?_
  rw [sWc_step] at hmem
  simp only [cst, addS, List.cons_append, List.nil_append, List.mem_cons, Stmt.atom.injEq,
    reduceCtorEq, false_or] at hmem
  exact hmem

theorem sWc_sound {pb : Nat} {σ : Val} (hg : SGood pb σ) :
    StepSound rd σ (sWc pb) (fun i s y =>
      (hcell [σ sPP, σ (sNode 0) + word (tw 1 + i * hiMul + s * stepMul) 0 0, y]).1) :=
  sStep_sound hg.2.2.1

theorem sWc_pow {pb : Nat} {σ : Val} (hg : SGood pb σ) : ∀ s < 10, σ ((sWc pb).power s) = gen ^ s := by
  intro s hs
  simp only [sWc, sWots, Nat.min_eq_left (show s ≤ 9 by omega)]
  exact hg.2.2.2 s hs

theorem sWc_pw (pb : Nat) : ∀ j, NBv (pb + 10) ((sWc pb).power j) :=
  fun j => ⟨pb + min j 9, by have := Nat.min_le_right j 9; omega, rfl⟩

end
end LeanVM.Guest.B1.Sig
