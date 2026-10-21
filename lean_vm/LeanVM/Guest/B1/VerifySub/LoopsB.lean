/-
  LeanVM.Guest.B1.VerifySub.LoopsB

  `verify_sub`'s loops under any semantics of `BLAKE2S`: the ring switch's target and `z_vals`.
-/

module

public import LeanVM.Guest.B1.VerifySub.RingB
public import LeanVM.Guest.B1.VerifySub.Loops

/-!
# The ring switch's target and `z_vals`, under any semantics (G:2190-2210)

`Loops.lean` over `S : BlakeSem`: `__loop84` and `__loop85` are free of `BLAKE2S`, so their
calls hold as deployed (`VsHoldsB.callF`, `sliceF`) and `vs_transposedB`, `vs_zvalsB` are
`vs_transposed`'s and `vs_zvals`' proofs.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {S : BlakeSem} {rd : Reader} {σ : Val}

/-- **The ring switch's target under `S`** (`vs_transposed`) (G:2190-2203): `__loop84` from `g^0` over `rs_chain`, whose row
`64` holds `Σ_i g^i Φ(s_i)` (`ringTarget`, V:2031). -/
theorem vs_transposedB (h : VsHoldsB S rd σ) {zs cs : List E} (hzl : zs.length = 64)
    (hz : ReadsAt rd (σ (.n 723)) zs) (hcl : cs.length = 6) (hc : ReadsAt rd (σ (.n 732)) cs) :
    σ (.n 1150) = ringTarget zs cs := by
  have hi := h.sliceF 1305 [.atom (.const (.n 1145) (word 1 0 0)), .atom (.load (.n 1145) (.n 1144) 0),
    .atom (.const (.n 1146) (word 0 0 0)), .atom (.load (.n 1146) (.n 1144) 1),
    .atom (.const (.n 1147) (word 1 0 0))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, word_one, word_zero] at hi
  obtain ⟨e1145, i0, e1146, i1, e1147⟩ := hi
  rw [e1145] at i0
  rw [e1146] at i1
  have hcall := h.callF 1310 "__loop84" [.n 1147, .n 723, .n 732, .n 1144] [] (by decide +kernel)
  simp only [List.map_cons, List.map_nil, e1147] at hcall
  rw [← pow_zero gen] at hcall
  have hb := loop_to (fun d x => loop84_step rd _ _ _ d x) (by decide) hcall
  -- the slices and the challenges, through every body
  have hrow : ∀ j ≤ 64, LoadHolds rd (σ (.n 1144)) (2 * j) (gen ^ j) ∧
      LoadHolds rd (σ (.n 1144)) (2 * j + 1)
        ((List.range j).map fun i ↦ phiMap (zs.getD i 0) cs * gen ^ i).sum := by
    intro j hj
    induction j with
    | zero => exact ⟨by simpa using i0, by simpa using i1⟩
    | succ j ih =>
      obtain ⟨ih0, ih1⟩ := ih (by omega)
      obtain ⟨lin, xp, sm, cs', hcs', hc', hlin, l0, l1, l2, l3⟩ := hb j (by omega)
      rw [gen_pow_two_mul, loadHolds_mul_gen_pow, Nat.add_zero] at l0
      rw [gen_pow_two_mul, loadHolds_mul_gen_pow] at l1 l2 l3
      have hxp := loadHolds_unique l0 ih0
      have hsm := loadHolds_unique l1 ih1
      have hcs : cs' = cs := List.ext_getElem (by rw [hcs', hcl]) fun k h1 h2 =>
        loadHolds_unique (hc' k h1) (hc k h2)
      have hlz : lin = zs.getD j 0 := by
        rw [List.getD_eq_getElem _ _ (by omega)]
        rw [loadHolds_mul_gen_pow, Nat.add_zero] at hlin
        exact loadHolds_unique hlin (hz j (by omega))
      rw [hxp] at l2 l3
      rw [hsm, hcs, hlz] at l3
      refine ⟨by rw [show 2 * (j + 1) = 2 * j + 2 by ring, pow_succ]; exact l2, ?_⟩
      rw [show 2 * (j + 1) + 1 = 2 * j + 3 by ring, List.range_succ, List.map_append,
        List.sum_append]
      simpa [mul_comm] using l3
  have ht := h.sliceF 1311 [.atom (.const (.n 1148) (word 325 0 0)),
    .atom (.mul (.n 1149) (.n 1144) (.n 1148)), .atom (.load (.n 1150) (.n 1149) 1)]
    (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at ht
  obtain ⟨e1148, e1149, l1150⟩ := ht
  have w325 : word 325 0 0 = gen ^ 128 := by
    rw [word_eOfNat, show (325 : ℕ) = gSquaresBits.getD 7 0 from rfl,
      eOfNat_gSquaresBits 7 (by decide)]
    norm_num
  rw [e1149, e1148, w325, loadHolds_mul_gen_pow] at l1150
  rw [loadHolds_unique l1150 (hrow 64 le_rfl).2, ringTarget, polyEval_eq_sum, List.length_map, hzl]
  refine congrArg List.sum (List.map_congr_left fun i hi => ?_)
  have hi' : i < 64 := by simpa using hi
  rw [List.getD_eq_getElem _ _ (by simpa [hzl] using hi'),
    List.getD_eq_getElem _ _ (by simpa [hzl] using hi'), List.getElem_map]

/-- **`z_vals` under `S`** (`vs_zvals`) (G:2204-2210): Flock's point, the lincheck's challenges reversed then the
zerocheck's beyond its first eight. -/
theorem vs_zvalsB (h : VsHoldsB S rd σ) {τ : ℕ} (hτ : τ < 29) (htau : σ (.n 718) = gen ^ τ)
    {chi rcs : List E} (hcl : chi.length = 8 + τ) (hrl : rcs.length = 8)
    (hchi : ReadsAt rd (σ (.n 721)) chi) (hrcs : ReadsAt rd (σ (.n 722)) rcs) :
    ReadsAt rd (σ (.n 734)) (rcs.reverse ++ chi.drop 8) := by
  have hcp := fun t (ht : t < 8) => h.sliceF (1314 + 2 * t)
    [.atom (.load (.n (1151 + t)) (.n 722) (7 - t)), .atom (.load (.n (1151 + t)) (.n 734) t)]
    (by revert t ht; decide +kernel)
  have hg := h.sliceF 1330 [.atom (.const (.n 1159) (word 1 0 0)),
    .atom (.add (.n 1160) (.n 1159) (.n 718)), .atom (.const (.n 1161) (word 1 0 0)),
    .atom (.const (.n 1162) (word 256 0 0)), .atom (.mul (.n 1163) (.n 734) (.n 1162)),
    .atom (.const (.n 1164) (word 256 0 0)), .atom (.mul (.n 1165) (.n 721) (.n 1164)),
    .callIf (.n 1160) "__loop85" [.n 1161, .n 718, .n 1163, .n 1165]] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, word_one, List.map_cons,
    List.map_nil] at hg
  obtain ⟨e1159, e1160, e1161, e1162, e1163, e1164, e1165, -, hcall⟩ := hg
  have w8 : word 256 0 0 = gen ^ 8 := word_two_pow (a := 8) (by decide)
  have hloop : ∀ j < τ, ∃ v, LoadHolds rd (σ (.n 721)) (8 + j) v ∧ LoadHolds rd (σ (.n 734)) (8 + j) v := by
    rcases Nat.eq_zero_or_pos τ with rfl | hp
    · exact fun j hj => absurd hj (Nat.not_lt_zero j)
    have hne : σ (.n 1160) ≠ 0 := by
      rw [e1160, e1159, htau]
      intro he
      have := gen_pow_inj (a := 0) (b := τ) (by decide) (by omega)
        (by rw [pow_zero]; exact (e_add_eq_zero_iff.mp he))
      omega
    have hc := hcall hne
    rw [e1161, e1163, e1165, e1162, e1164, w8, htau, ← pow_zero gen] at hc
    have hb := loop_to (fun d x => loop85_step rd _ _ _ d x) (by unfold ordG; omega) hc
    intro j hj
    obtain ⟨v, l1, l2⟩ := hb j hj
    rw [mul_assoc, ← pow_add, loadHolds_mul_gen_pow, Nat.add_zero] at l1 l2
    exact ⟨v, l1, l2⟩
  intro k hk
  simp only [List.length_append, List.length_reverse, List.length_drop, hrl, hcl] at hk
  rcases Nat.lt_or_ge k 8 with hk8 | hk8
  · rw [List.getElem_append_left (by simp [hrl]; omega), List.getElem_reverse]
    have := hcp k hk8
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at this
    have e1 := loadHolds_unique this.1 (hrcs (7 - k) (by omega))
    have e2 : rcs[rcs.length - 1 - k] = rcs[7 - k] := by simp only [hrl]
    rw [e2, ← e1]
    exact this.2
  · rw [List.getElem_append_right (by simp [hrl]; omega), List.getElem_drop]
    obtain ⟨v, l1, l2⟩ := hloop (k - 8) (by omega)
    rw [show 8 + (k - 8) = k by omega] at l1 l2
    simp only [List.length_reverse, hrl, show 8 + (k - 8) = k by omega]
    rw [← loadHolds_unique l1 (hchi k (by omega))]
    exact l2

end
end LeanVM.Guest.B1.VerifySub
