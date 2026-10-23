/-
  LeanVM.Guest.B1.VerifySub.Stack

  `verify_sub`'s stack: the committed columns' placement, the stack's log and the candidate it
  dispatches on.
-/

module

public import LeanVM.Guest.B1.VerifySub.LanesK
public import LeanVM.Guest.B1.Tables.HoldsC

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem word_pow_eq {a : ℕ} (h : a < 64) : word (2 ^ a) 0 0 = ofK (Parameters.gpow a) := by
  rw [word_two_pow h, gen_pow_eq_ofK]

/-- A range check against `g^(K-1)` (`K ≤ 64`) on a memory of at least `64` words. -/
theorem rc_lt {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (L : MemImage κ) {x y t1 t2 : E} {a : ℕ}
    (ha : a < 6 + 1) (h1 : LoadHolds L.read x 0 t1) (hk : word (2 ^ a) 0 0 = x * y)
    (h2 : LoadHolds L.read y 0 t2) : ∃ e < a + 1, x = gen ^ e := by
  have h64 : a + 1 ≤ 2 ^ κ := le_trans (show a + 1 ≤ 2 ^ 6 by omega)
    (Nat.pow_le_pow_right (by decide) hκ6)
  obtain ⟨e, he, hx⟩ := (rangeCheck_iff hκ L x (K := a + 1) (by omega) h64).mp
    ⟨y, t1, t2, h1, by rw [Nat.add_sub_cancel, ← word_pow_eq (by omega)]; exact hk, h2⟩
  exact ⟨e, he, by rw [hx, gen_pow_eq_ofK]⟩

/-- A range check against `g^27` on a memory of at least `64` words. -/
theorem rc_lt28 {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (L : MemImage κ) {x y t1 t2 : E}
    (h1 : LoadHolds L.read x 0 t1) (hk : word (2 ^ 27) 0 0 = x * y)
    (h2 : LoadHolds L.read y 0 t2) : ∃ e < 28, x = gen ^ e := by
  have h64 : 28 ≤ 2 ^ κ := le_trans (show 28 ≤ 2 ^ 6 by omega)
    (Nat.pow_le_pow_right (by decide) hκ6)
  obtain ⟨e, he, hx⟩ := (rangeCheck_iff hκ L x (K := 28) (by omega) h64).mp
    ⟨y, t1, t2, h1, by rw [show 28 - 1 = 27 from rfl, ← word_pow_eq (by omega)]; exact hk, h2⟩
  exact ⟨e, he, by rw [hx, gen_pow_eq_ofK]⟩

/-- **The stack** (G:3301-3324): the placement certified, the stack's log `μ ∈ [22, 28]`, the
candidate `g^((μ - 22) + 7·(r - 1))` dispatched on, and the committed columns' logs below `29`. -/
theorem vs_stack {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (L : MemImage κ) {C : CallRel}
    (hLe : CallRel.Le C (coreProgram.Rel L.read)) {bytecode : List K}
    (hbl : bytecode.length = 2 ^ 23) {σ : Val} (F : VsFront bytecode C L.read σ)
    (hexp : ExpTables L.read (σ (.n 4)) (σ (.n 5)))
    (hcp : C "certify_placement" [σ (.n 141), σ (.n 5)] [σ (.n 1887), σ (.n 1888), σ (.n 1889)])
    (hl2 : C "log2_ceil_in_the_exponent__L15_L34" [σ (.n 1887), σ (.n 4), σ (.n 5)] [σ (.n 1890)])
    (e1892 : σ (.n 1892) = σ (.n 1890) * word 8198552432976855044 0 0)
    (r1 : LoadHolds L.read (σ (.n 1892)) 0 (σ (.n 1895)) ∧ word 64 0 0 = σ (.n 1892) * σ (.n 1894) ∧
      LoadHolds L.read (σ (.n 1894)) 0 (σ (.n 1896)))
    (e1901 : σ (.n 1901) = σ (.n 1892) * (σ (.n 124) * σ (.n 124) * σ (.n 124) *
      (σ (.n 124) * σ (.n 124) * σ (.n 124)) * σ (.n 124)))
    (r2 : LoadHolds L.read (σ (.n 1901)) 0 (σ (.n 1904)) ∧
      word 134217728 0 0 = σ (.n 1901) * σ (.n 1903) ∧ LoadHolds L.read (σ (.n 1903)) 0 (σ (.n 1905))) :
    22 ≤ (Tables.layoutOf bytecode F.logMem F.rowsN).stackLog ∧
      (Tables.layoutOf bytecode F.logMem F.rowsN).stackLog ≤ 28 ∧
      σ (.n 1901) = gen ^ B1.Whir.candidate (Tables.layoutOf bytecode F.logMem F.rowsN).stackLog F.lir ∧
      Tables.PCtx L.read (columnKappas F.logMem 19 (Tables.tableHeightsOf F.rowsN)) (σ (.n 1888))
        (σ (.n 1889)) ∧ Tables.KappasBelow L.read (σ (.n 1889)) := by
  have hsL := tableHeights_length _ F.hrowsL
  -- the placement
  obtain ⟨off, kap, hrets, hP⟩ := Tables.certify_placement_holdsC hκ L hLe F.logMem
    (Tables.tableHeightsOf F.rowsN) _ _ _ F.hm32 hsL F.hh29 F.hkb (gSquares_of_exp hexp) hcp
  simp only [List.cons.injEq, and_true] at hrets
  obtain ⟨e1887, rfl, rfl⟩ := hrets
  -- the stack's log
  obtain ⟨N, hN, hgN, hm34, -, -, hret⟩ := ((log2_holds.2.2.2 hκ hκ6 L _ _ _ hexp _).1
    (hLe _ _ _ hl2))
  simp only [List.cons.injEq, and_true] at hret
  have hT := stackTotal_lt F.hm32 hsL F.hh29
  have eN : N = Tables.stackTotal (columnKappas F.logMem 19 (Tables.tableHeightsOf F.rowsN)) :=
    gen_pow_inj (by omega) (by omega) (hgN.symm.trans e1887)
  subst eN
  rw [← stackLog_eq hbl] at hret hm34
  set μ := (Tables.layoutOf bytecode F.logMem F.rowsN).stackLog with hμ
  -- the size selector
  obtain ⟨e, he, hx⟩ := rc_lt hκ hκ6 L (a := 6) (by omega) r1.1 (by simpa using r1.2.1) r1.2.2
  have hμe : μ = e + 22 := size_sel_eq hm34 he (by rw [← hret, ← e1892, hx])
  -- the candidate
  obtain ⟨c, hc, hcx⟩ := rc_lt28 hκ hκ6 L r2.1 (by simpa using r2.2.1) r2.2.2
  have hcand : σ (.n 1901) = gen ^ B1.Whir.candidate μ F.lir := by
    rw [e1901, hx, F.e124, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← pow_add,
      ← pow_add, ← pow_add, ← pow_add]
    congr 1
    unfold B1.Whir.candidate
    omega
  refine ⟨by omega, by omega, hcand, hP, Tables.hypKappa_holds _ _ _ _ hP ?_⟩
  have : max 15 (log2Ceil (Tables.stackTotal (columnKappas F.logMem 19
    (Tables.tableHeightsOf F.rowsN)))) ≤ 28 := by rw [← stackLog_eq hbl]; omega
  omega

end
end LeanVM.Guest.B1.VerifySub
