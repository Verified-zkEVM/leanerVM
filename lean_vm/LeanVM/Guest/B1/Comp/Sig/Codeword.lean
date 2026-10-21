/-
  LeanVM.Guest.B1.Comp.Sig.Codeword

  The WOTS+C codeword of a one-time signature, complete over a completeness model
  (`cGroups_complete`, `cCodeword_complete`).
-/

module

public import LeanVM.Guest.B1.Comp.Sig.Group

/-!
# The codeword over a completeness model

`Codeword.lean`'s completeness over a `CompModel`: every chain's steps answered (`TipAnsC`), its
tips the model's chain ends (`TipSetC`).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.E2E.Complete

@[expose] public section

variable {CM : CompModel} {C : CallRel} {rd : Reader}

/-- **Groups in sequence are complete over the model** (`cGroups_complete`): for digit values `ks`
and chain values `xs`, the chains' steps answered. -/
theorem cGroups_comp {w : Wots} {power : Nat → V} (hrd : MemOK rd 64) {ks : Nat → Nat} {xs : Nat → E} :
    ∀ (m p : Nat) (prod enc : V) (b : Nat) (σ : Val), (p = 0 → 0 < m) → w.Below b → NB b prod → NB b enc →
      (∀ s < 10, NB b (power s)) → σ w.md = mdw (stepCount w.lx) true → w.Canon σ →
      (∀ s < 10, σ (power s) = gen ^ s) → (∀ q < m, ks (p + q) < 64) →
      (∀ i, IsCanonical128 (xs i)) →
      (∀ q < m, ∀ r < 3, TipAnsC CM w σ (3 * (p + q) + r) (armDigit (ks (p + q)) r) (xs (3 * (p + q) + r))) →
      CompletesB CM.sem C rd b (cGroups w power m p prod enc b).2.1 (cGroups w power m p prod enc b).1 σ (fun σ' =>
        (∀ q < m, ∀ r < 3, TipSetC CM w σ' (3 * (p + q) + r) (armDigit (ks (p + q)) r) (xs (3 * (p + q) + r))
          ((cGroups w power m p prod enc b).2.2.1.getD (3 * q + r) (.n 0, .n 0))) ∧
        σ' (cGroups w power m p prod enc b).2.2.2.1 =
          (if p = 0 then 1 else σ prod) * gen ^ (∑ q ∈ Finset.range m, digitSum (ks (p + q)) 3) ∧
        σ' (cGroups w power m p prod enc b).2.2.2.2 =
          (if p = 0 then 0 else σ enc) + ∑ q ∈ Finset.range m, lit (ks (p + q) * 4 ^ (3 * (p + q))))
  | 0, p, prod, enc, b, σ, hm, _, _, _, _, _, _, _, _, _, _ => by
      have hp : p ≠ 0 := fun h => absurd (hm h) (by omega)
      exact ⟨σ, Ext.refl _ _ _, ⟨fun q h => absurd h (by omega), by simp [cGroups, hp], by simp [cGroups, hp]⟩,
        fun _ _ hn => hn⟩
  | m + 1, p, prod, enc, b, σ, _, hw, hprod, henc, hpw, hmd, hc, hpow, hks, hxs, hans => by
      simp only [cGroups]
      have hg := cGroup_snd_ge w power prod enc (3 * p) 3 (p == 0) b
      have h5 := groupStart_ge (p == 0) b
      have hG := cGroup_comp (CM := CM) (C := C) (rd := rd) (w := w) (power := power) (first := 3 * p) (n := 3)
        (fold := p == 0) (σ := σ) (hrd.mono (by norm_num)) le_rfl hw ⟨hprod, henc, hpw⟩ hmd hc
        (k := ks (p + 0)) (by have := hks 0 (by omega); norm_num; omega) (xs := fun r => xs (3 * p + r))
        (fun r _ => hxs _) (fun r hr => by simpa using hans 0 (by omega) r hr)
      refine CompletesB.append (m := (cGroup w power prod enc (3 * p) 3 (p == 0) b).2) (by omega)
        (cGroups_snd_ge w power m (p + 1) _ _ _) (cGroup_below (by norm_num) hw ⟨hprod, henc, hpw⟩) hG.withExt ?_
      intro σ' he ⟨⟨_, htip, hfold⟩, he'⟩
      have hk := hw.keep he
      have hR := cGroups_comp hrd m (p + 1)
        (groupProd w.lx (p == 0) 3 b) (groupEnc w.lx (p == 0) 3 b) (cGroup w power prod enc (3 * p) 3 (p == 0) b).2
        σ' (by omega) (hw.mono (by omega)) ⟨_, by omega, rfl⟩ ⟨_, by omega, rfl⟩ (fun s hs => (hpw s hs).mono (by omega))
        (by rw [hk.2.2.2, hmd]) (hc.congr hk) (fun s hs => by rw [he.below (hpw s hs), hpow s hs])
        (fun q hq => by rw [show p + 1 + q = p + (q + 1) by omega]; exact hks _ (by omega)) hxs
        (fun q hq r hr => by
          rw [show p + 1 + q = p + (q + 1) by omega]; exact (hans (q + 1) (by omega) r hr).congr hk)
      refine hR.withExt.mono le_rfl le_rfl fun σ'' ⟨⟨htips, hP, hE⟩, he''⟩ => ⟨fun q hq r hr => ?_, ?_, ?_⟩
      · have hk'' := (hw.mono (show b ≤ (cGroup w power prod enc (3 * p) 3 (p == 0) b).2 by omega)).keep he''
        by_cases hq0 : q = 0
        · subst hq0
          obtain ⟨o1, o2⟩ := groupTips_lt w.lx (p == 0) b r 3 hr
          have := (htip r hr).congr hk'' (he''.below (NB.mono o1 hg)) (he''.below (NB.mono o2 hg))
          rw [List.getD_append _ _ _ _ (by simpa using hr)]
          simpa [hr] using this
        · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
          simp only [List.length_map, List.length_range]
          have := htips (q - 1) (by omega) r hr
          rw [show 3 * q + r - 3 = 3 * (q - 1) + r by omega]
          rw [show p + 1 + (q - 1) = p + q by omega] at this
          exact this
      · rw [hP, Finset.sum_range_succ', groupProd]
        unfold ArmFold groupProd at hfold
        simp only [↓reduceIte, Nat.add_one_ne_zero, Nat.add_zero]
        rw [hfold.1, he.below (hpw _ (pow_digitSum_lt _)), hpow _ (pow_digitSum_lt _), pow_add, he.below hprod]
        simp only [show ∀ q, p + 1 + q = p + (q + 1) from fun q => by omega]
        by_cases hp : p = 0 <;> simp [hp] <;> ring
      · rw [hE, Finset.sum_range_succ', groupEnc]
        unfold ArmFold groupEnc at hfold
        simp only [↓reduceIte, Nat.add_one_ne_zero, Nat.add_zero]
        rw [hfold.2, he.below henc]
        simp only [show ∀ q, p + 1 + q = p + (q + 1) from fun q => by omega]
        by_cases hp : p = 0 <;> simp [hp] <;> ring_nf

/-- **The codeword is complete over the model** (`cCodeword_complete`), its chains answered: digits below 4 summing to the target's exponent and encoding
`d0`'s preset value, chain values `xs`. -/
theorem cCodeword_comp {w : Wots} {power : Nat → V} (hrd : MemOK rd 64) {G : Nat} (hG : 0 < G)
    {target : E} {d0 : V} {b : Nat} {σ : Val} (hb : 0 < b) (hw : w.Below b) (hpw : ∀ s < 10, NB b (power s))
    (hd0 : NB b d0)
    (hmd : σ w.md = mdw (stepCount w.lx) true) (hc : w.Canon σ) (hpow : ∀ s < 10, σ (power s) = gen ^ s)
    {dig : Nat → Nat} (hdig : ∀ i, dig i < 4) {xs : Nat → E} (hxs : ∀ i, IsCanonical128 (xs i))
    (hans : ∀ i < 3 * G + 1, TipAnsC CM w σ i (dig i) (xs i))
    (htarget : target = gen ^ (∑ i ∈ Finset.range (3 * G + 1), dig i))
    (hd : σ d0 = lit (∑ i ∈ Finset.range (3 * G + 1), dig i * 4 ^ i)) :
    CompletesB CM.sem C rd b (cCodeword w power G target d0 b).2.1 (cCodeword w power G target d0 b).1 σ
      (fun σ' => ∀ i < 3 * G + 1, TipSetC CM w σ' i (dig i) (xs i) ((cCodeword w power G target d0 b).2.2.getD i (.n 0, .n 0))) := by
  set ks : Nat → Nat := fun q => dig (3 * q) + 4 * dig (3 * q + 1) + 16 * dig (3 * q + 2) with hks_def
  set kl := dig (3 * G)
  have hks : ∀ q, ks q < 64 := fun q => by
    have := hdig (3 * q); have := hdig (3 * q + 1); have := hdig (3 * q + 2); simp only [hks_def]; omega
  have hcd : ∀ i < 3 * G + 1, codeDigit G ks kl i = dig i := by
    intro i hi
    by_cases h : i < 3 * G
    · obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 3 ∧ i = 3 * q + r := ⟨i / 3, i % 3, Nat.mod_lt _ (by norm_num), by omega⟩
      rw [codeDigit_group (by omega) hr]
      have := hdig (3 * q); have := hdig (3 * q + 1); have := hdig (3 * q + 2)
      simp only [hks_def, armDigit]
      interval_cases r <;> simp <;> omega
    · simp only [codeDigit, h, ↓reduceIte, kl]
      rw [show i = 3 * G by omega]
  have hsum : ∑ i ∈ Finset.range (3 * G + 1), dig i = ∑ q ∈ Finset.range G, digitSum (ks q) 3 + kl := by
    rw [← codeDigit_sum G ks kl]
    exact Finset.sum_congr rfl fun i hi => (hcd i (Finset.mem_range.mp hi)).symm
  have henc : ∑ i ∈ Finset.range (3 * G + 1), dig i * 4 ^ i =
      ∑ q ∈ Finset.range G, ks q * 4 ^ (3 * q) + kl * 4 ^ (3 * G) := by
    rw [← codeDigit_enc G ks kl fun q _ => hks q]
    exact Finset.sum_congr rfl fun i hi => by rw [hcd i (Finset.mem_range.mp hi)]
  simp only [cCodeword]
  set gs := cGroups w power G 0 (.n 0) (.n 0) b with hgs
  have hgsb := cGroups_snd_ge w power G 0 (.n 0) (.n 0) b
  rw [← hgs] at hgsb
  have hout := cGroups_outs_lt w power G 0 (.n 0) (.n 0) b hG
  rw [← hgs] at hout
  have htl := cGroups_tips_lt w power G 0 (.n 0) (.n 0) b
  rw [← hgs] at htl
  have hlen := cGroups_tips_length w power G 0 (.n 0) (.n 0) b
  rw [← hgs] at hlen
  set L := cGroup w power gs.2.2.2.1 gs.2.2.2.2 (3 * G) 1 false gs.2.1 with hL
  have hLb := cGroup_snd_ge w power gs.2.2.2.1 gs.2.2.2.2 (3 * G) 1 false gs.2.1
  rw [← hL] at hLb
  have h5 := groupStart_ge false gs.2.1
  have hA := cGroups_comp (CM := CM) (C := C) (rd := rd) (w := w) (power := power) hrd (ks := ks) (xs := xs) G 0 (.n 0)
    (.n 0) b σ (fun _ => hG) hw ⟨0, hb, rfl⟩ ⟨0, hb, rfl⟩ hpw hmd hc hpow (fun q _ => by simpa using hks q) hxs
    (fun q hq r hr => by
      have := hans (3 * q + r) (by omega)
      rw [← hcd _ (by omega), codeDigit_group hq hr] at this
      simpa using this)
  rw [← hgs] at hA
  refine CompletesB.append (m := L.2) (P := fun σ' => (∀ q < G, ∀ r < 3, TipSetC CM w σ' (3 * q + r)
      (armDigit (ks q) r) (xs (3 * q + r)) (gs.2.2.1.getD (3 * q + r) (.n 0, .n 0))) ∧
      TipSetC CM w σ' (3 * G) kl (xs (3 * G)) (groupTips w.lx false gs.2.1 0) ∧
      σ' (groupProd w.lx false 1 gs.2.1) = target ∧ σ' (groupEnc w.lx false 1 gs.2.1) = σ d0 ∧
      Ext b L.2 σ σ') (by omega) (by omega) ?_ ?_ ?_
  · rw [valsList_append]
    have := cGroups_below G 0 (.n 0) (.n 0) b hw ⟨0, hb, rfl⟩ ⟨0, hb, rfl⟩ hpw
    rw [← hgs] at this
    exact (this.mono (by omega)).append
      (cGroup_below (by norm_num) (hw.mono (by omega)) ⟨hout.1, hout.2, fun s hs => (hpw s hs).mono (by omega)⟩)
  · have hgb := cGroups_below G 0 (.n 0) (.n 0) b hw ⟨0, hb, rfl⟩ ⟨0, hb, rfl⟩ hpw
    rw [← hgs] at hgb
    refine CompletesB.append (m := gs.2.1) hgsb (by omega) hgb hA.withExt ?_
    rintro σ1 he1 ⟨⟨htips1, hprod1, henc1⟩, -⟩
    have hk1 := hw.keep he1
    have hB := cGroup_comp (CM := CM) (C := C) (rd := rd) (w := w) (power := power) (prodIn := gs.2.2.2.1)
      (encIn := gs.2.2.2.2) (first := 3 * G) (n := 1) (fold := false) (b := gs.2.1) (σ := σ1)
      (hrd.mono (by norm_num)) (by norm_num) (hw.mono hgsb) ⟨hout.1, hout.2, fun s hs => (hpw s hs).mono hgsb⟩
      (by rw [hk1.2.2.2, hmd]) (hc.congr hk1) (k := kl) (by have := hdig (3 * G); simp; omega)
      (xs := fun r => xs (3 * G + r)) (fun r _ => hxs _)
      (fun r hr => by
        obtain rfl : r = 0 := by omega
        have := (hans (3 * G) (by omega)).congr hk1
        simpa [armDigit, Nat.mod_eq_of_lt (hdig (3 * G)), kl] using this)
    refine hB.withExt.mono le_rfl le_rfl fun σ2 ⟨⟨_, htip2, hfold2⟩, he2⟩ => ⟨fun q hq r hr => ?_, ?_, ?_, ?_,
      he1.trans he2 hgsb (by omega)⟩
    · have hk2 := (hw.mono hgsb).keep he2
      obtain ⟨o1, o2⟩ := htl (3 * q + r) (by omega)
      have := (htips1 q hq r hr).congr hk2 (he2.below o1) (he2.below o2)
      simpa using this
    · have hk2 := (hw.mono hgsb).keep he2
      have := htip2 0 (by norm_num)
      simpa [armDigit, Nat.mod_eq_of_lt (hdig (3 * G)), kl] using this
    · unfold ArmFold at hfold2; unfold groupProd at hfold2 ⊢
      rw [hfold2.1, he2.below hout.1, hprod1, he2.below ((hpw _ (digitSum_lt_ten _ (by norm_num))).mono hgsb),
        he1.below (hpw _ (digitSum_lt_ten _ (by norm_num))),
        hpow _ (by rw [digitSum_one (hdig (3 * G))]; have := hdig (3 * G); omega), digitSum_one (hdig (3 * G)),
        htarget, hsum]
      simp only [↓reduceIte, Bool.false_eq_true, one_mul, pow_add, Nat.zero_add, kl]
    · unfold ArmFold at hfold2; unfold groupEnc at hfold2 ⊢
      rw [hfold2.2, he2.below hout.2, henc1, hd, henc]
      simp only [↓reduceIte, zero_add, Bool.false_eq_true]
      rw [(lit_sum_groups ks G fun q _ => hks q).1]
      have h2 := (lit_sum_groups ks G fun q _ => hks q).2
      have e : kl * 4 ^ (3 * G) = 2 ^ (6 * G) * kl := by
        have h4 : (4 : Nat) ^ (3 * G) = 2 ^ (6 * G) := by
          rw [show (4 : Nat) = 2 ^ 2 from rfl, ← pow_mul]; ring_nf
        rw [Nat.mul_comm, h4]
      rw [e, add_comm (∑ q ∈ Finset.range G, ks q * 4 ^ (3 * q)), lit_add_of_lt h2, add_comm]
  · rintro σ' he ⟨htips, htipL, hpr, hen, -⟩
    have he3 : Ext L.2 (L.2 + 1) σ' (Function.update σ' (.n L.2) target) := ext_update _ _ le_rfl (by omega)
    have hk3 := (hw.mono (show b ≤ L.2 by omega)).keep he3
    have hst := ws_lt_stride w.lx
    refine ⟨Function.update σ' (.n L.2) target, he3, fun i hi => ?_, fun next kret hn => ?_⟩
    · by_cases hi' : i < 3 * G
      · obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 3 ∧ i = 3 * q + r :=
          ⟨i / 3, i % 3, Nat.mod_lt _ (by norm_num), by omega⟩
        obtain ⟨o1, o2⟩ := htl (3 * q + r) (by omega)
        have := (htips q (by omega) r hr).congr hk3 (he3.below (NB.mono o1 (by omega)))
          (he3.below (NB.mono o2 (by omega)))
        rw [List.getD_append _ _ _ _ (by omega), ← hcd _ hi, codeDigit_group (by omega) hr]
        exact this
      · have hi3 : i = 3 * G := by omega
        subst hi3
        obtain ⟨o1, o2⟩ := groupTips_lt w.lx false gs.2.1 0 1 (by norm_num)
        have := htipL.congr hk3 (he3.below (NB.mono o1 (by omega))) (he3.below (NB.mono o2 (by omega)))
        rw [List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self]
        simpa using this
    · have hpo : NB L.2 (groupProd w.lx false 1 gs.2.1) := ⟨_, by unfold groupProd at *; omega, rfl⟩
      have heo : NB L.2 (groupEnc w.lx false 1 gs.2.1) := ⟨_, by unfold groupEnc at *; omega, rfl⟩
      simp only [cst, holdsListB_cons_atom, holdsListB_nil, Atom.HoldsB]
      rw [he3.below hpo, he3.below heo, he3.below (NB.mono hd0 (by omega)), Function.update_self, hpr, hen,
        e_add_eq_zero_iff, e_add_eq_zero_iff, he.below hd0]
      exact ⟨rfl, rfl, rfl, hn⟩


end
end LeanVM.Guest.B1.Sig
