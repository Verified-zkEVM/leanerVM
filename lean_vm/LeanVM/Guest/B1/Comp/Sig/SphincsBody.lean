/-
  LeanVM.Guest.B1.Comp.Sig.SphincsBody

  `verify_sig_lean_sphincs`'s prologue and counter complete over a completeness model
  (`sPro1_complete`, `sPrologue_complete`, `sCounter_complete`); its lanes, free of `BLAKE2S`,
  carry over (`sLanes_comp`).
-/

module

public import LeanVM.Guest.B1.Comp.CompletesB
public import LeanVM.Guest.B1.Comp.Sig.Values
public import LeanVM.Guest.B1.Sig.SphincsBodyComplete
public import LeanVM.Guest.B1.Sig.Model.SphincsBody

/-!
# The prologue, the lanes and the counter over a completeness model

The message digest (two compressions, `compress_two_C`) and the counter's encoding digest (one,
`compress_final_comp`) preset to the model's answers, which exist when the model answers their
bytes; the hash-free blocks (the Booleanity checks, the shifts, the lanes) carry over from the
deployed lemmas by `CompletesB.of_free`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.E2E.Complete

@[expose] public section

variable {CM : CompModel} {C : CallRel} {rd : Reader}

/-! ## The prologue -/

/-- **The prologue's first statements are complete over the model** (`sPro1_complete`), with the
bits of `N` and `U` preset, the message digest's bytes answered. -/
theorem sPro1_comp {σ : Val} {pp m0 m1 rho : E} (hl1 : LoadHolds rd (σ (.n 0)) 1 pp)
    (hl2 : LoadHolds rd (σ (.n 0)) 2 m0) (hl3 : LoadHolds rd (σ (.n 0)) 3 m1) (hpp : IsCanonical128 pp)
    (hm0 : IsCanonical128 m0) (hm1 : IsCanonical128 m1) (hrho : IsCanonical128 rho)
    (hans : AnsCells CM [pp, word (tw 12) 0 0, m0, m1, rho]) (N U : Nat) :
    CompletesB CM.sem C rd 1 67 sPro1 σ (fun σ' =>
      σ' (.n 1) = pp ∧ σ' (.n 2) = mdw 48 true ∧ σ' (.n 3) = mdw 64 true ∧ σ' (.n 5) = m0 ∧ σ' (.n 6) = m1 ∧
      σ' (.n 12) = rho ∧ (σ' (.n 17), σ' (.n 18)) = hcellC CM [pp, word (tw 12) 0 0, m0, m1, rho] ∧
      (∀ j < 26, σ' (.n (19 + j)) = bitE (N.testBit j)) ∧ (∀ j < 22, σ' (.n (45 + j)) = bitE (U.testBit j)) ∧
      AgreeBelow 1 σ σ') := by
  set A := word (tw 12) 0 0
  set x := hmidC CM ![pp, A, m0, m1]
  set o := hbC CM (blockBytes ![pp, A, m0, m1] ++ [rho].flatMap cellBytes)
  set vs : List E := [pp, mdw 48 true, mdw 64 true, A, m0, m1, iv0, iv1, mdw 64 false, x.1, x.2, rho, 0, 0, 0,
    mdw 80 true, o.1, o.2]
  set g : Nat → E := fun k => if k < 18 then vs.getD k 0 else if k < 44 then bitE (N.testBit (k - 18))
    else bitE (U.testBit (k - 44))
  set σ' := upds σ ((List.range 66).map fun k => (1 + k, g k))
  have he : Ext 1 67 σ σ' := upds_ext σ _ (by simp; omega)
  have v : ∀ k < 66, σ' (.n (1 + k)) = g k := upds_range_at 1 _ 66 σ
  have v' : ∀ k, 1 ≤ k → k < 19 → σ' (.n k) = vs.getD (k - 1) 0 := fun k h1 h2 => by
    have := v (k - 1) (by omega); rw [show 1 + (k - 1) = k by omega] at this; rw [this]; simp [g, show k - 1 < 18 by omega]
  have h0 : σ' (.n 0) = σ (.n 0) := (he.agree 0 (by omega)).symm
  have hr : ([rho].flatMap cellBytes).length = 16 := by rw [length_flatMap_cellBytes']; rfl
  have hcmp := compress_two_C (CM := CM) (b0 := ![pp, A, m0, m1]) (b1 := ![rho, 0, 0, 0])
    (blockBytes_one rho) (by rw [hr]; omega) (by rw [hr]; omega)
    (fin4_canonical.mpr ⟨hpp, isCanonical128_word _ _, hm0, hm1⟩)
    (fin4_canonical.mpr ⟨hrho, isCanonical128_zero, isCanonical128_zero, isCanonical128_zero⟩)
    (by
      have e : blockBytes ![pp, A, m0, m1] ++ [rho].flatMap cellBytes = [pp, A, m0, m1, rho].flatMap cellBytes := by
        simp only [blockBytes_four, ← List.flatMap_append]; rfl
      rw [e]; exact hans)
  rw [hr] at hcmp
  refine ⟨σ', he, ⟨v' 1 le_rfl (by omega), v' 2 (by omega) (by omega), v' 3 (by omega) (by omega),
    v' 5 (by omega) (by omega), v' 6 (by omega) (by omega), v' 12 (by omega) (by omega), ?_, fun j hj => ?_,
    fun j hj => ?_, he.agree⟩, fun next kret hn => ?_⟩
  · rw [v' 17 (by omega) (by omega), v' 18 (by omega) (by omega)]
    show (o.1, o.2) = _
    simp only [o, blockBytes_four, hcellC, ← List.flatMap_append]
    rfl
  · rw [show 19 + j = 1 + (18 + j) by omega, v _ (by omega)]
    simp [g, show ¬ (18 + j < 18) by omega, show 18 + j < 44 by omega]
  · rw [show 45 + j = 1 + (44 + j) by omega, v _ (by omega)]
    simp [g, show ¬ (44 + j < 18) by omega, show ¬ (44 + j < 44) by omega]
  · simp only [sPro1, hintW, cst, b2s, holdsListB_cons_atom, holdsListB_nil, Atom.HoldsB, true_and]
    rw [h0, v' 1 le_rfl (by omega), v' 2 (by omega) (by omega), v' 3 (by omega) (by omega),
      v' 4 (by omega) (by omega), v' 5 (by omega) (by omega), v' 6 (by omega) (by omega), v' 7 (by omega) (by omega),
      v' 8 (by omega) (by omega), v' 9 (by omega) (by omega), v' 10 (by omega) (by omega),
      v' 11 (by omega) (by omega), v' 12 (by omega) (by omega), v' 13 (by omega) (by omega),
      v' 14 (by omega) (by omega), v' 15 (by omega) (by omega), v' 16 (by omega) (by omega),
      v' 17 (by omega) (by omega), v' 18 (by omega) (by omega)]
    simp only [vs, List.getD_cons_succ, List.getD_cons_zero, Nat.sub_self, Nat.add_one_sub_one,
      show (3 : Nat) - 1 = 2 from rfl, word_zero]
    obtain ⟨hc1, hc2⟩ := hcmp
    refine ⟨hl1, ?_, ?_, ?_, hl2, hl3, ?_, ?_, ?_, hc1, ?_, ?_, ?_, ?_, hc2, hn⟩ <;> trivial

/-- **The prologue is complete over the model** (`sPrologue_complete`): from the claim's words, a
randomizer whose message digest the model answers, and the index and unused bits `N`, `U` in range. -/
theorem sPrologue_comp {σ : Val} {pp m0 m1 rho : E} (hl1 : LoadHolds rd (σ (.n 0)) 1 pp)
    (hl2 : LoadHolds rd (σ (.n 0)) 2 m0) (hl3 : LoadHolds rd (σ (.n 0)) 3 m1) (hpp : IsCanonical128 pp)
    (hm0 : IsCanonical128 m0) (hm1 : IsCanonical128 m1) (hrho : IsCanonical128 rho)
    (hans : AnsCells CM [pp, word (tw 12) 0 0, m0, m1, rho]) {N U : Nat} (hN : N < 2 ^ 26) (hU : U < 2 ^ 22) :
    CompletesB CM.sem C rd 1 210 sPrologue σ (fun σ' =>
      SPre σ' N U ∧ σ' (.n 1) = pp ∧ σ' (.n 5) = m0 ∧ σ' (.n 6) = m1 ∧ σ' (.n 12) = rho ∧
      (σ' (.n 17), σ' (.n 18)) = hcellC CM [pp, word (tw 12) 0 0, m0, m1, rho] ∧ AgreeBelow 1 σ σ') := by
  rw [sPrologue_eq, show [.atom (.load (.n 1) (.n 0) 1), cst 2 (mdw 48 true), cst 3 (mdw 64 true),
      cst 4 (word (tw 12) 0 0), .atom (.load (.n 5) (.n 0) 2), .atom (.load (.n 6) (.n 0) 3), cst 7 iv0, cst 8 iv1,
      cst 9 (mdw 64 false), b2s (.n 1) (.n 4) (.n 5) (.n 6) (.n 7) (.n 8) (.n 10) (.n 11) (.n 9),
      hintW "sp_rand" [.n 12], cst 13 (word 0 0 0), cst 14 (word 0 0 0), cst 15 (word 0 0 0),
      cst 16 (mdw 80 true), b2s (.n 12) (.n 13) (.n 14) (.n 15) (.n 10) (.n 11) (.n 17) (.n 18) (.n 16),
      .atom (.hint (.bits (.n 18) 0 26 (.stack ((List.range 26).map fun j => .n (19 + j)))))] = sPro1 from rfl]
  refine CompletesB.append (m := 67) (by omega) (by omega) sPro1_below
    (sPro1_comp hl1 hl2 hl3 hpp hm0 hm1 hrho hans N U) fun σ1 _ ⟨h1, h2, h3, h5, h6, h12, hd, hbN, hbU, hag1⟩ => ?_
  refine CompletesB.append_holds ((valsList_booleans 19 26).mono (by omega)) (fun next kret hn =>
    (holdsListB_iff_of_freeIn (F := []) (by decide) _ _ _).mpr
      ((booleans_iff 19 26).mpr ⟨fun j hj => by rw [hbN j hj]; exact bitE_mul_self _, hn⟩)) ?_
  refine CompletesB.hint_cons _ ?_
  refine CompletesB.append_holds ((valsList_booleans 45 22).mono (by omega)) (fun next kret hn =>
    (holdsListB_iff_of_freeIn (F := []) (by decide) _ _ _).mpr
      ((booleans_iff 45 22).mpr ⟨fun j hj => by rw [hbU j hj]; exact bitE_mul_self _, hn⟩)) ?_
  refine CompletesB.append (m := 143) (by omega) (by omega) (shifts_below_gen 19 26 67 (by omega) (by omega))
    (CompletesB.of_free (F := []) (by decide)
      (shifts_complete (C := C) (rd := rd) (by omega) (by omega) hN (by omega) hbN)) fun σ2 _ ⟨hs2, hag2⟩ => ?_
  have hbU2 : ∀ j < 22, σ2 (.n (45 + j)) = bitE (U.testBit j) := fun j hj => by
    rw [← hag2 _ (by omega)]; exact hbU j hj
  refine CompletesB.append (m := 207) (by omega) (by omega) (shifts_below_gen 45 22 143 (by omega) (by omega))
    (CompletesB.of_free (F := []) (by decide)
      (shifts_complete (C := C) (rd := rd) (by omega) (by omega) hU (by omega) hbU2)) fun σ3 _ ⟨hs3, hag3⟩ => ?_
  have hk3 : ∀ k < 67, σ3 (.n k) = σ1 (.n k) := fun k hk => ((hag2 k (by omega)).trans (hag3 k (by omega))).symm
  have h142 : σ3 (.n 142) = eOfNat N := by
    have := hs2 25 (by omega); rw [show 67 + 3 * 25 = 142 from rfl, show 26 - 1 - 25 = 0 from rfl, pow_zero,
      Nat.div_one] at this; rw [← hag3 _ (by omega)]; exact this
  have h206 : σ3 (.n 206) = eOfNat U := by
    have := hs3 21 (by omega); rwa [show 143 + 3 * 21 = 206 from rfl, show 22 - 1 - 21 = 0 from rfl, pow_zero,
      Nat.div_one] at this
  set σ4 := Function.update σ3 (.n 207) (word 0 (2 ^ 42) 0)
  set σ5 := Function.update σ4 (.n 208) (eOfNat U * word 0 (2 ^ 42) 0)
  set σ6 := Function.update σ5 (.n 209) (eOfNat N + lit (U * 2 ^ 106))
  have ne : ∀ a b : Nat, a ≠ b → (V.n a) ≠ V.n b := fun a b h e => h (by simp only [V.mk.injEq] at e; exact e.2.2)
  refine CompletesB.atom_cons (word 0 (2 ^ 42) 0) (by omega) (.cons ⟨207, by omega, rfl⟩ (.nil _))
    (Function.update_self _ _ _) ?_
  refine CompletesB.atom_cons (eOfNat U * word 0 (2 ^ 42) 0) (by omega)
    (.cons ⟨208, by omega, rfl⟩ (.cons ⟨206, by omega, rfl⟩ (.cons ⟨207, by omega, rfl⟩ (.nil _)))) ?_ ?_
  · show σ5 (.n 208) = σ5 (.n 206) * σ5 (.n 207)
    simp only [σ5, σ4, Function.update_self, Function.update_of_ne (ne _ _ (show 206 ≠ 208 by omega)),
      Function.update_of_ne (ne _ _ (show 206 ≠ 207 by omega)), Function.update_of_ne (ne _ _ (show 207 ≠ 208 by omega)),
      h206]
  refine CompletesB.atom_cons (eOfNat N + lit (U * 2 ^ 106)) (by omega)
    (.cons ⟨209, by omega, rfl⟩ (.cons ⟨142, by omega, rfl⟩ (.cons ⟨208, by omega, rfl⟩ (.nil _)))) ?_
    (CompletesB.nil _ _ _ ?_)
  · show σ6 (.n 209) = σ6 (.n 142) + σ6 (.n 208)
    simp only [σ6, σ5, σ4, Function.update_self, Function.update_of_ne (ne _ _ (show 142 ≠ 209 by omega)),
      Function.update_of_ne (ne _ _ (show 142 ≠ 208 by omega)), Function.update_of_ne (ne _ _ (show 142 ≠ 207 by omega)),
      Function.update_of_ne (ne _ _ (show 208 ≠ 209 by omega)), h142, eOfNat_mul_unused hU]
  · have hk6 : ∀ k < 207, ∀ e1 e2 e3 : E, Function.update (Function.update (Function.update σ3 (.n 207) e1)
        (.n (207 + 1)) e2) (.n (207 + 1 + 1)) e3 (.n k) = σ3 (.n k) := fun k hk e1 e2 e3 => by
      rw [Function.update_of_ne (ne _ _ (by omega)), Function.update_of_ne (ne _ _ (by omega)),
        Function.update_of_ne (ne _ _ (by omega))]
    refine ⟨⟨by rw [hk6 2 (by omega), hk3 2 (by omega), h2], by rw [hk6 3 (by omega), hk3 3 (by omega), h3], hN, hU,
      fun j hj => by rw [hk6 _ (by omega), hk3 _ (by omega), hbN j hj], fun l hl => ?_, ?_⟩,
      by rw [hk6 1 (by omega), hk3 1 (by omega), h1], by rw [hk6 5 (by omega), hk3 5 (by omega), h5],
      by rw [hk6 6 (by omega), hk3 6 (by omega), h6], by rw [hk6 12 (by omega), hk3 12 (by omega), h12],
      by rw [hk6 17 (by omega), hk6 18 (by omega), hk3 17 (by omega), hk3 18 (by omega), hd],
      fun k hk => (hag1 k hk).trans (by rw [hk6 k (by omega), hk3 k (by omega)])⟩
    · have := hs2 (25 - l) (by omega)
      rw [show 67 + 3 * (25 - l) = 142 - 3 * l by omega, show 26 - 1 - (25 - l) = l by omega] at this
      rw [hk6 _ (by omega), ← hag3 _ (by omega)]; exact this
    · simp


/-! ## The lanes -/

/-- **The lanes are complete under any model** (`sLanes_complete`; no `BLAKE2S`). -/
theorem sLanes_comp {σ : Val} {wd : Nat → V} {bound : V} {b : Nat} (hb : 19 ≤ b) (hwd : ∀ k < 16, NB b (wd k))
    (hbB : NB b bound) {t : Nat → Nat} (ht : ∀ k < 16, t k < 2 ^ 8) (hwv : ∀ k < 16, σ (wd k) = eOfNat (t k))
    (h17 : σ (.n 17) = lit (∑ k ∈ Finset.range 16, t k * 2 ^ (8 * k))) (h18 : σ bound = σ (.n 18)) :
    CompletesB CM.sem C rd b (b + 45) (sLanes wd bound b) σ (fun σ' => AgreeBelow b σ σ') :=
  CompletesB.of_free (F := []) (sLanes_free wd bound b) (sLanes_complete hb hwd hbB ht hwv h17 h18)

/-! ## The counter -/

/-- **The counter is complete over the model** (`sCounter_complete`): over any counter below `2^32`
whose encoding digest the model answers. -/
theorem sCounter_comp {σ : Val} {fk : V} {b : Nat} (hb143 : 143 ≤ b) (hfk : NB b fk) {Cn : Nat}
    (hCn : Cn < 2 ^ 32) (hp : IsCanonical128 (σ (.n 1))) (ha : IsCanonical128 (σ (.n 142) + word (tw 4) 0 0))
    (hf : IsCanonical128 (σ fk))
    (hans : Ans CM (cellBytes (σ (.n 1)) ++ cellBytes (σ (.n 142) + word (tw 4) 0 0) ++ cellBytes (σ fk) ++
      leBytes Cn 4)) :
    CompletesB CM.sem C rd b (b + 133) (sCounter fk b) σ (fun σ' => σ' (.n b) = eOfNat Cn ∧
      σ' (.n (b + 126 + 1)) = σ (.n 142) + word (tw 4) 0 0 ∧
      σ' (.n (b + 126 + 5)) = (hbC CM (cellBytes (σ (.n 1)) ++ cellBytes (σ (.n 142) + word (tw 4) 0 0) ++
        cellBytes (σ fk) ++ leBytes Cn 4)).1 ∧ AgreeBelow b σ σ') := by
  rw [sCounter_split]
  refine CompletesB.hint_cons _ (CompletesB.hint_cons _ ?_)
  set cv : Nat → E := fun j => if j = 0 then eOfNat Cn else bitE (Cn.testBit (j - 1))
  set σ1 := upds σ ((List.range 33).map fun j => (b + j, cv j))
  have he1 : Ext b (b + 133) σ σ1 := upds_ext σ _ fun p hp => by
    simp only [List.mem_map, List.mem_range] at hp
    obtain ⟨j, hj, rfl⟩ := hp
    exact ⟨by omega, by omega⟩
  have hv1 : ∀ j < 33, σ1 (.n (b + j)) = cv j := upds_range_at b _ 33 σ
  have hbit : ∀ j < 32, σ1 (.n (b + 1 + j)) = bitE (Cn.testBit j) := fun j hj => by
    rw [add_assoc, hv1 _ (by omega)]
    simp only [cv, Nat.add_eq_zero_iff, one_ne_zero, false_and, ↓reduceIte, Nat.add_sub_cancel_left]
  have hc0 : σ1 (.n b) = eOfNat Cn := by
    have := hv1 0 (by omega)
    rwa [Nat.add_zero] at this
  have hag1 : AgreeBelow b σ σ1 := fun k hk => he1.agree k hk
  refine CompletesB.of_ext he1 (CompletesB.mono (lo := b + 33) ?_ (by omega) le_rfl fun σ' h => h)
  refine CompletesB.append_holds (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.nil _))))
    (fun next kret hn => ?_) ?_
  · simp only [mulS, holdsListB_cons_atom, holdsListB_nil, Atom.HoldsB]
    have h0 := hbit 0 (by omega)
    rw [Nat.add_zero] at h0
    rw [h0]
    exact ⟨(bitE_mul_self _).symm, hn⟩
  have hfm := CompletesB.flatMap_range (S := CM.sem) (C := C) (rd := rd) (f := ctrBlock b) (base := fun i => b + 33 + 3 * i)
    (Inv := fun i σ' => AgreeBelow (b + 33) σ1 σ' ∧
      σ' (if i = 0 then .n (b + 32) else .n (b + 33 + 3 * i - 1)) = eOfNat (Cn / 2 ^ (31 - i)))
    (fun _ => by omega) 31 (fun i hi => ctrBlock_below hi)
    (fun i hi σ' ⟨hag, hpv⟩ => by
      set c := b + 33 + 3 * i
      set vs : List E := [word 2 0 0, word 2 0 0 * eOfNat (Cn / 2 ^ (31 - i)), eOfNat (Cn / 2 ^ (30 - i))]
      set σ'' := upds σ' ((List.range 3).map fun j => (c + j, vs.getD j 0))
      have he : Ext c (c + 3) σ' σ'' := upds_ext σ' _ (by simp)
      have v : ∀ j < 3, σ'' (.n (c + j)) = vs.getD j 0 := upds_range_at c _ 3 σ'
      have hk' : ∀ v : V, NB c v → σ'' v = σ' v := fun v hv => he.out (out_of_lt hv)
      have hpB : NB c (if i = 0 then .n (b + 32) else .n (b + 33 + 3 * i - 1)) := by
        split
        · exact ⟨_, by omega, rfl⟩
        · exact ⟨_, by omega, rfl⟩
      have hb1 : σ'' (.n (b + 1 + (i + 1))) = bitE (Cn.testBit (i + 1)) := by
        rw [hk' _ ⟨_, by omega, rfl⟩, ← hag _ (by omega), hbit _ (by omega)]
      have hb2 : σ'' (.n (b + 32 - (i + 1))) = bitE (Cn.testBit (30 - i)) := by
        rw [show b + 32 - (i + 1) = b + 1 + (30 - i) by omega, hk' _ ⟨_, by omega, rfl⟩, ← hag _ (by omega),
          hbit _ (by omega)]
      refine ⟨σ'', he, ⟨fun k hk => (hag k hk).trans (he.agree k (by omega)), ?_⟩, fun next kret hn => ?_⟩
      · simp only [Nat.add_one_ne_zero, ↓reduceIte]
        rw [show b + 33 + 3 * (i + 1) - 1 = c + 2 by omega, v 2 (by omega), show 31 - (i + 1) = 30 - i by omega]
        rfl
      · simp only [ctrBlock, cst, mulS, addS, holdsListB_cons_atom, holdsListB_nil, Atom.HoldsB]
        have v0 := v 0 (by omega)
        rw [Nat.add_zero] at v0
        rw [hb1, v0, v 1 (by omega), v 2 (by omega), hk' _ hpB, hpv, hb2]
        simp only [vs, List.getD_cons_succ, List.getD_cons_zero]
        refine ⟨(bitE_mul_self _).symm, trivial, trivial, ?_, hn⟩
        rw [word_two, add_comm, show 31 - i = 30 - i + 1 by omega, shift_step (by omega)])
    σ1 ⟨fun _ _ => rfl, by
      simp only [↓reduceIte]
      rw [show b + 32 = b + 1 + 31 by omega, hbit 31 (by omega), top_bit (show Cn < 2 ^ (31 + 1) from hCn)]⟩
  refine CompletesB.append (m := b + 33 + 3 * 31) (by omega) (by omega)
    (numBelow_valsList_flatMap _ _ fun i hi => (ctrBlock_below (List.mem_range.mp hi)).mono (by
      have := List.mem_range.mp hi; omega)) hfm fun σ2 _ ⟨hag2, hpv2⟩ => ?_
  have h125 : σ2 (.n (b + 125)) = eOfNat Cn := by
    rw [ite_neg' (by omega), show b + 33 + 3 * 31 - 1 = b + 125 by omega, Nat.sub_self, pow_zero,
      Nat.div_one] at hpv2
    exact hpv2
  have h2 : ∀ k < b + 33, σ2 (.n k) = σ1 (.n k) := fun k hk => (hag2 k hk).symm
  have hagB : AgreeBelow b σ σ2 := fun k hk => (hag1 k hk).trans (hag2 k (by omega))
  have hkB : ∀ v : V, NB b v → σ2 v = σ v := fun v ⟨k, hk, e⟩ => by rw [e]; exact (hagB k hk).symm
  set A := σ (.n 142) + word (tw 4) 0 0
  set r := cellBytes (σ (.n 1)) ++ cellBytes A ++ cellBytes (σ fk) ++ leBytes Cn 4
  set o := hbC CM r
  have hr : r.length = 52 := by simp [r, length_cellBytes]
  set e := b + 126
  set vs : List E := [word (tw 4) 0 0, A, iv0, iv1, mdw 52 true, o.1, o.2]
  set σ3 := upds σ2 ((List.range 7).map fun j => (e + j, vs.getD j 0))
  have he3 : Ext e (e + 7) σ2 σ3 := upds_ext σ2 _ (by simp)
  have v : ∀ j < 7, σ3 (.n (e + j)) = vs.getD j 0 := upds_range_at e _ 7 σ2
  have hk3 : ∀ v : V, NB e v → σ3 v = σ2 v := fun v hv => he3.out (out_of_lt hv)
  have hcmp : CM.sem.check ![σ (.n 1), A, σ fk, eOfNat Cn] iv0 iv1 o.1 o.2 (mdw 52 true) := by
    rw [← hr]
    exact compress_final_comp CM (by rw [blockBytes_four, hr]; simp [r, cellBytes_counter hCn]) (by rw [hr]; omega)
      (fun i => by fin_cases i <;> simp [hp, ha, hf, isCanonical128_eOfNat]) (hbWith_of_ans hans)
  refine ⟨σ3, he3.mono (by omega) (by omega), ⟨?_, ?_, ?_, fun k hk => (hagB k hk).trans (he3.agree k (by omega))⟩,
    fun next kret hn => ?_⟩
  · rw [hk3 _ ⟨b, by omega, rfl⟩, h2 _ (by omega), hc0]
  · rw [v 1 (by omega)]; rfl
  · rw [v 5 (by omega)]; rfl
  · simp only [ctrTail, ivs, cst, addS, b2s, List.cons_append, List.nil_append, holdsListB_cons_atom, holdsListB_nil,
      Atom.HoldsB]
    have v0 := v 0 (by omega)
    rw [Nat.add_zero] at v0
    rw [v0, v 1 (by omega), v 2 (by omega), show e + 2 + 1 = e + 3 by omega, v 3 (by omega), v 4 (by omega),
      v 5 (by omega), v 6 (by omega), hk3 _ ⟨b + 125, by omega, rfl⟩, hk3 _ ⟨b, by omega, rfl⟩, h125,
      hk3 _ ⟨142, by omega, rfl⟩, hk3 _ ⟨1, by omega, rfl⟩, hk3 _ (hfk.mono (by omega)), h2 _ (by omega), hc0,
      hkB _ ⟨142, by omega, rfl⟩, hkB _ ⟨1, by omega, rfl⟩, hkB _ hfk]
    simp only [vs, List.getD_cons_succ, List.getD_cons_zero]
    exact ⟨e_add_eq_zero_iff.mpr rfl, trivial, rfl, trivial, trivial, trivial, hcmp, hn⟩

end
end LeanVM.Guest.B1.Sig
