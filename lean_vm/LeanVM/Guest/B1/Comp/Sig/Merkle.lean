/-
  LeanVM.Guest.B1.Comp.Sig.Merkle

  `merkle_path` complete over a completeness model (`merkleLevel_iff.mpr`, `merkle_complete`).
-/

module

public import LeanVM.Guest.B1.Comp.CompletesB
public import LeanVM.Guest.B1.Comp.Sig.Values

/-!
# Merkle paths over a completeness model

A level holds under the model's semantics at the model's answer for its node
(`merkleLevel_holdsB_of`), and a path completes to the model's fold of it (`mFoldC`) when the model
answers every node (`mFoldAns`): `merkle_comp`. At the deployed model it is `merkle_complete`
(`merkle_of_comp`).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.E2E.Complete

@[expose] public section

variable {CM : CompModel} {C : CallRel} {rd : Reader}

/-- One level's statements hold over the model when the children are in the order of the bit, the
address is the level's and the parent the model's answer for them (`merkleLevel_iff.mpr`). -/
theorem merkleLevel_holdsB_of {σ : Val} {pp cur : V} {bit node : Nat → V} {addr : Nat → Nat}
    {isEnd : Nat → Bool} {l b : Nat} {β : Bool} (hβ : σ (bit l) = bitE β) {X : Prop}
    {kret : List E → Prop}
    (hk : σ (.n (b + 2)) = σ cur + σ (.n b) ∧ σ (.n (b + 3)) = σ (.n b) + σ (.n (b + 1)) ∧
        σ (.n (b + 4)) = word (addr l) 0 0 ∧
        (isEnd l = false → σ (.n (b + 5)) = σ (.n (b + 4)) + σ (node (l + 1))) ∧
        σ (.n ((if isEnd l then b + 4 else b + 5) + 1)) = iv0 ∧
        σ (.n ((if isEnd l then b + 4 else b + 5) + 2)) = iv1 ∧
        σ (.n ((if isEnd l then b + 4 else b + 5) + 3)) = mdw 64 true)
    (hord : (if β then σ (.n (b + 1)) else σ (.n b)) = σ cur)
    (hcan : IsCanonical128 (σ pp) ∧ IsCanonical128 (mAddr σ node addr isEnd l) ∧
      IsCanonical128 (σ (.n b)) ∧ IsCanonical128 (σ (.n (b + 1))))
    (ha : AnsCells CM [σ pp, mAddr σ node addr isEnd l, σ (.n b), σ (.n (b + 1))])
    (hh : (σ (.n ((if isEnd l then b + 4 else b + 5) + 4)), σ (.n ((if isEnd l then b + 4 else b + 5) + 5))) =
      hcellC CM [σ pp, mAddr σ node addr isEnd l, σ (.n b), σ (.n (b + 1))]) (hX : X) :
    Stmt.HoldsListB CM.sem C rd σ ([hintW "siblings" [.n b, .n (b + 1)], addS (.n (b + 2)) cur (.n b),
        addS (.n (b + 3)) (.n b) (.n (b + 1)), mulS (.n (b + 2)) (bit l) (.n (b + 3)),
        cst (b + 4) (word (addr l) 0 0)] ++
        (if isEnd l then [] else [addS (.n (b + 5)) (.n (b + 4)) (node (l + 1))]) ++
        ivs ((if isEnd l then b + 4 else b + 5) + 1) ++
        [cst ((if isEnd l then b + 4 else b + 5) + 3) (mdw 64 true),
          b2s pp (.n (if isEnd l then b + 4 else b + 5)) (.n b) (.n (b + 1))
            (.n ((if isEnd l then b + 4 else b + 5) + 1)) (.n ((if isEnd l then b + 4 else b + 5) + 2))
            (.n ((if isEnd l then b + 4 else b + 5) + 4)) (.n ((if isEnd l then b + 4 else b + 5) + 5))
            (.n ((if isEnd l then b + 4 else b + 5) + 3))]) X kret := by
  have hrow := compress4_C (CM := CM) hcan ha
  have e1 := congrArg Prod.fst hh
  have e2 := congrArg Prod.snd hh
  simp only at e1 e2
  obtain ⟨h2, h3, h4, h5, h6, h7, h8⟩ := hk
  cases he : isEnd l
  · simp only [he, Bool.false_eq_true, ↓reduceIte, hintW, addS, mulS, cst, ivs, b2s, List.cons_append,
      List.nil_append, holdsListB_cons_atom, holdsListB_nil, Atom.HoldsB, true_and, forall_const] at h5 h6 h7 h8 e1 e2 ⊢
    refine ⟨h2, h3, ?_, h4, h5, h6, h7, h8, ?_, hX⟩
    · rw [h2, hβ, h3, isChild_iff]; exact hord
    · rw [h6, h7, h8, h5, h4, e1, e2]
      simpa [mAddr, he] using hrow
  · simp only [he, ↓reduceIte, hintW, addS, mulS, cst, ivs, b2s, List.cons_append,
      List.nil_append, holdsListB_cons_atom, holdsListB_nil, Atom.HoldsB, true_and, List.append_nil] at h6 h7 h8 e1 e2 ⊢
    refine ⟨h2, h3, ?_, h4, h6, h7, h8, ?_, hX⟩
    · rw [h2, hβ, h3, isChild_iff]; exact hord
    · rw [h6, h7, h8, h4, e1, e2]
      simpa [mAddr, he] using hrow


/-- **A Merkle path is complete over the model** (`merkle_complete`): from any siblings, the
children hinted in the bits' order, every node answered. -/
theorem merkle_comp {pp : V} {bit node : Nat → V} {addr : Nat → Nat} {isEnd : Nat → Bool}
    {β : Nat → Bool} {sibs : Nat → E} :
    ∀ (m l : Nat) (cur : V) (b : Nat) (σ : Val), NB b pp → NB b cur →
      (∀ l', l ≤ l' → l' < l + m → NB b (bit l') ∧ NB b (node (l' + 1))) →
      (∀ l', l ≤ l' → l' < l + m → σ (bit l') = bitE (β l') ∧ IsCanonical128 (sibs l') ∧
        IsCanonical128 (mAddr σ node addr isEnd l')) →
      IsCanonical128 (σ pp) → IsCanonical128 (σ cur) →
      mFoldAns CM (σ pp) (mAddr σ node addr isEnd) β sibs m l (σ cur) →
      CompletesB CM.sem C rd b (merkle pp bit node addr isEnd m l cur b).2.2 (merkle pp bit node addr isEnd m l cur b).1 σ
        (fun σ' => σ' (merkle pp bit node addr isEnd m l cur b).2.1 =
          mFoldC CM (σ pp) (mAddr σ node addr isEnd) β sibs m l (σ cur))
  | 0, _, _, _, σ, _, _, _, _, _, _, _ => ⟨σ, Ext.refl _ _ _, rfl, fun _ _ hn => hn⟩
  | m + 1, l, cur, b, σ, hpp, hcur, hin, hval, hppc, hcurc, hans => by
      rw [merkle_eq]
      dsimp only
      set a := if isEnd l then b + 4 else b + 5 with ha
      have hab : b + 4 ≤ a ∧ a ≤ b + 5 := by rw [ha]; split <;> omega
      set x := σ cur
      set A := mAddr σ node addr isEnd l
      set k0 := if β l then sibs l else x
      set k1 := if β l then x else sibs l
      set h := hcellC CM [σ pp, A, k0, k1]
      obtain ⟨hβl, hsc, hAc⟩ := hval l le_rfl (by omega)
      have hk0c : IsCanonical128 k0 := by simp only [k0]; split <;> assumption
      have hk1c : IsCanonical128 k1 := by simp only [k1]; split <;> assumption
      -- the level's valuation
      let L : List (Nat × E) := [(b, k0), (b + 1, k1), (b + 2, x + k0), (b + 3, k0 + k1),
        (b + 4, word (addr l) 0 0)] ++ (if isEnd l then [] else [(b + 5, A)]) ++
        [(a + 1, iv0), (a + 2, iv1), (a + 3, mdw 64 true), (a + 4, h.1), (a + 5, h.2)]
      let σ1 := upds σ L
      have hL : ∀ p ∈ L, b ≤ p.1 ∧ p.1 < a + 6 := by
        simp only [L, List.forall_mem_append, List.forall_mem_cons]
        split <;> simp <;> omega
      have he1 : Ext b (a + 6) σ σ1 := upds_ext σ L hL
      have hσ1 : σ1 (.n b) = k0 ∧ σ1 (.n (b + 1)) = k1 ∧ σ1 (.n (b + 2)) = x + k0 ∧
          σ1 (.n (b + 3)) = k0 + k1 ∧ σ1 (.n (b + 4)) = word (addr l) 0 0 ∧
          (isEnd l = false → σ1 (.n (b + 5)) = A) ∧ σ1 (.n (a + 1)) = iv0 ∧ σ1 (.n (a + 2)) = iv1 ∧
          σ1 (.n (a + 3)) = mdw 64 true ∧ σ1 (.n (a + 4)) = h.1 ∧ σ1 (.n (a + 5)) = h.2 := by
        cases hE : isEnd l <;> simp only [hE, ↓reduceIte, Bool.false_eq_true] at ha <;>
          simp only [σ1, L, hE, ↓reduceIte, Bool.false_eq_true, List.cons_append, List.nil_append,
            List.append_nil] <;>
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          first
          | (intro hf; exact Bool.noConfusion hf)
          | ((try intro); simp (disch := omega) only [upds_cons_self, upds_cons_ne])
      have hk : ∀ {v : V}, NB b v → σ1 v = σ v := fun hv => he1.below hv
      obtain ⟨hb0, hb1, hb2, hb3, hb4, hb5, ha1, ha2, ha3, ha4, ha5⟩ := hσ1
      have hA1 : mAddr σ1 node addr isEnd l = A := by
        simp only [mAddr, A]; rw [hk (hin l le_rfl (by omega)).2]
      refine CompletesB.append (m := a + 6) (P := fun σ' => σ' (.n (a + 4)) = h.1 ∧ Ext b (a + 6) σ σ') (by omega)
        (merkle_snd_ge _ _ _ _ _ _ _ _ _) ?_ ⟨σ1, he1, ⟨ha4, he1⟩, fun next kret hn => ?_⟩ ?_
      · exact merkleLevel_below hpp hcur (hin l le_rfl (by omega)).1 (hin l le_rfl (by omega)).2
      · refine merkleLevel_holdsB_of (hβ := by rw [hk (hin l le_rfl (by omega)).1]; exact hβl)
          ⟨by rw [hb2, hb0, hk hcur], by rw [hb3, hb0, hb1], hb4, fun hE => by
            rw [hb5 hE, hb4, hk (hin l le_rfl (by omega)).2]; simp [A, mAddr, hE], ha1, ha2, ha3⟩ ?_ ?_ ?_ ?_ hn
        · rw [hb0, hb1, hk hcur]; cases hb : β l <;> simp [k0, k1, hb, x]
        · rw [hk hpp, hA1, hb0, hb1]; exact ⟨hppc, hAc, hk0c, hk1c⟩
        · rw [hk hpp, hA1, hb0, hb1]; exact hans.1
        · rw [ha4, ha5, hk hpp, hA1, hb0, hb1]
      · intro σ' he' ⟨hσ'4, he''⟩
        have hk' : ∀ {v : V}, NB b v → σ' v = σ v := fun hv => he''.below hv
        have hA' : ∀ l', l + 1 ≤ l' → l' < l + 1 + m →
            mAddr σ' node addr isEnd l' = mAddr σ node addr isEnd l' := fun l' h1 h2 => by
          simp only [mAddr]; rw [hk' (hin l' (by omega) (by omega)).2]
        have := merkle_comp (sibs := sibs) m (l + 1) (.n (a + 4)) (a + 6) σ' (hpp.mono (by omega)) ⟨_, by omega, rfl⟩
          (fun l' h1 h2 => ⟨(hin l' (by omega) (by omega)).1.mono (by omega), (hin l' (by omega) (by omega)).2.mono (by omega)⟩)
          (fun l' h1 h2 => by
            obtain ⟨e1, e2, e3⟩ := hval l' (by omega) (by omega)
            refine ⟨by rw [hk' (hin l' (by omega) (by omega)).1]; exact e1, e2, ?_⟩
            have : mAddr σ' node addr isEnd l' = mAddr σ node addr isEnd l' := by
              simp only [mAddr]; rw [hk' (hin l' (by omega) (by omega)).2]
            rw [this]; exact e3)
          (by rw [hk' hpp]; exact hppc) (by rw [hσ'4]; exact (isCanonical128_hcellC _).1)
          (by
            rw [hk' hpp, hσ'4, (mFoldC_congr2 _ _ m (l + 1) (fun l' h1 h2 => ⟨hA' l' h1 h2, rfl⟩) _).2]
            exact hans.2)
        refine this.mono le_rfl le_rfl fun σ'' h'' => ?_
        rw [h'', hk' hpp, hσ'4, mFoldC]
        exact (mFoldC_congr2 _ _ m (l + 1) (fun l' h1 h2 => ⟨hA' l' h1 h2, rfl⟩) _).1


/-- The deployed `merkle_complete`, from the model's at `CompModel.deployed`. -/
theorem merkle_of_comp {pp : V} {bit node : Nat → V} {addr : Nat → Nat} {isEnd : Nat → Bool}
    {β : Nat → Bool} {sibs : Nat → E} (m l : Nat) (cur : V) (b : Nat) (σ : Val) (hpp : NB b pp)
    (hcur : NB b cur) (hin : ∀ l', l ≤ l' → l' < l + m → NB b (bit l') ∧ NB b (node (l' + 1)))
    (hval : ∀ l', l ≤ l' → l' < l + m → σ (bit l') = bitE (β l') ∧ IsCanonical128 (sibs l') ∧
        IsCanonical128 (mAddr σ node addr isEnd l'))
    (hppc : IsCanonical128 (σ pp)) (hcurc : IsCanonical128 (σ cur)) :
    Completes C rd b (merkle pp bit node addr isEnd m l cur b).2.2 (merkle pp bit node addr isEnd m l cur b).1 σ
      (fun σ' => σ' (merkle pp bit node addr isEnd m l cur b).2.1 =
        mFold (σ pp) (mAddr σ node addr isEnd) β sibs m l (σ cur)) := by
  have := merkle_comp (CM := CompModel.deployed) (C := C) (rd := rd) (sibs := sibs) m l cur b σ hpp hcur
    hin hval hppc hcurc (mFoldAns_deployed _ _ _ _ _ _ _)
  rw [← mFoldC_deployed]
  exact this.of_deployed

end
end LeanVM.Guest.B1.Sig
