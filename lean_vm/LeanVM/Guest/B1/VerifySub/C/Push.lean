/-
  LeanVM.Guest.B1.VerifySub.C.Push

  `verify_sub`'s push total and bus depth (G:3199-3204), honestly.
-/

module

public import LeanVM.Guest.B1.VerifySub.C.Kappa

/-!
# The push total, honestly

`vsPushT_complete`: with `block_kappa` holding `g^κ_b` and the exponent tables at `4`, `5`, every
push block reads `g_squares[κ_b] = g^(2^κ_b)` and multiplies it in, so `521` is `g^S` for the push
blocks' sum `S`; `log2_ceil_in_the_exponent` (in `C`) returns `g^(log2Ceil S)` at `522`, the bus
point's buffer is allocated by it, and `vsPushT` holds.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Tables LeanVM.Protocol.Verifier

@[expose] public section

theorem vsPushT_noNe : vsPushT.all noNeB = true := by decide +kernel

theorem vsPush_notS : ∀ b < 54, Atom.load (.n (if b = 0 then 307 else 306 + 4 * b)) (.n 149) b ∉ vsSL ∧
    Atom.load (.n (if b = 0 then 309 else 308 + 4 * b)) (.n (if b = 0 then 308 else 307 + 4 * b)) 0
      ∉ vsSL := by decide +kernel

variable {rd : Reader} {w : ℕ → E} {args : List E}

theorem vsPushT_good (hl : args.length = 7) :
    ∀ s ∈ vsPushT, GoodS rd vsSL w (vsσ rd w args) s := by
  intro s hs
  have h := vs_goodS (rd := rd) (w := w) hl (vs_mem_slice (n := 432) (blk := vsPushT)
    (by decide +kernel) hs)
  rwa [fixNe_of_noNe (List.all_eq_true.mp vsPushT_noNe s hs)] at h

theorem vsPushStep_mem {b : ℕ} (hb : b < 54) {s : Stmt} (hs : s ∈ vsPushStep b) : s ∈ vsPushT :=
  List.mem_append_left _ (List.mem_flatMap.2 ⟨b, List.mem_range.2 hb, hs⟩)

/-- The push blocks' running product, honestly. -/
theorem vsPush_loop (hl : args.length = 7) {logMem : ℕ} {hs : List ℕ} (hsl : hs.length = 6)
    (hh : ∀ x ∈ hs, x < 29) (hm : logMem ≤ 32)
    (hbk : ReadsAt rd (vsσ rd w args (.n 149))
      (Tables.blockKappaWords (gen ^ logMem) (hs.map (gen ^ ·))))
    (hexp : B1.ExpTables rd (vsσ rd w args (.n 4)) (vsσ rd w args (.n 5)))
    {C : CallRel} {kret : List E → Prop} :
    ∀ n < 54, ∀ {nx : Prop}, nx →
      vsσ rd w args (.n (vsPV n)) =
        gen ^ ((List.range (n + 1)).map fun b ↦ 2 ^ pushKappa logMem hs b).sum ∧
      Stmt.HoldsList C rd (vsσ rd w args) ((List.range (n + 1)).flatMap vsPushStep) nx kret := by
  have hG := vsPushT_good (rd := rd) (w := w) hl
  generalize hσ : vsσ rd w args = σ at *
  -- block `b`'s two reads
  have rd2 : ∀ b < 54, ∀ (k1 m k2 : ℕ), k1 = (if b = 0 then 307 else 306 + 4 * b) →
      m = (if b = 0 then 308 else 307 + 4 * b) → k2 = (if b = 0 then 309 else 308 + 4 * b) →
      vsLd k1 149 b ∈ vsPushStep b → vsMul m 5 k1 ∈ vsPushStep b → vsLd k2 m 0 ∈ vsPushStep b →
      σ (.n k1) = gen ^ pushKappa logMem hs b ∧ (Atom.load (.n k1) (.n 149) b).Holds rd σ ∧
        σ (.n m) = σ (.n 5) * σ (.n k1) ∧ (Atom.mul (.n m) (.n 5) (.n k1)).Holds rd σ ∧
        σ (.n k2) = gen ^ 2 ^ pushKappa logMem hs b ∧ (Atom.load (.n k2) (.n m) 0).Holds rd σ := by
    intro b hb k1 m k2 e1 em e2 h1 hm' h2
    have hbL : LoadHolds rd (σ (.n 149)) b (gen ^ pushKappa logMem hs b) := by
      rw [← bkw_getD hsl (by show b < 153; omega), List.getD_eq_getElem _ _
        (by simp only [Tables.blockKappaWords, List.length_map, List.length_range]; show b < 153; omega)]
      exact hbk _ _
    have g1 : Good rd vsSL w σ (.load (.n k1) (.n 149) b) := hG _ (vsPushStep_mem hb h1)
    have r1 := good_read g1 (by rw [e1]; exact (vsPush_notS b hb).1) hbL
    have gm : Good rd vsSL w σ (.mul (.n m) (.n 5) (.n k1)) := hG _ (vsPushStep_mem hb hm')
    simp only [Good] at gm
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by
      rw [e1, em]; by_cases h0 : b = 0 <;> simp [h0]; omega))] at gm
    have hq : LoadHolds rd (σ (.n m)) 0 (gen ^ 2 ^ pushKappa logMem hs b) := by
      rw [gm, r1.1, loadHolds_mul_gen_pow, add_zero]
      exact (hexp _ (pushKappa_lt hh hm hb)).2
    have g2 : Good rd vsSL w σ (.load (.n k2) (.n m) 0) := hG _ (vsPushStep_mem hb h2)
    have r2 := good_read g2 (by rw [e2, em]; exact (vsPush_notS b hb).2) hq
    exact ⟨r1.1, r1.2, gm, gm, r2.1, r2.2⟩
  intro n
  induction n with
  | zero =>
    intro _ nx hn
    obtain ⟨-, h1, -, hm1, e2, h2⟩ := rd2 0 (by norm_num) 307 308 309 rfl rfl rfl
      (by simp [vsPushStep]) (by simp [vsPushStep]) (by simp [vsPushStep])
    refine ⟨by rw [show vsPV 0 = 309 from rfl, e2]; simp, ?_⟩
    rw [show List.range (0 + 1) = [0] from rfl]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, vsPushStep, ↓reduceIte,
      Stmt.HoldsList, Stmt.Holds, vsLd, vsMul]
    exact ⟨h1, hm1, h2, hn⟩
  | succ n ih =>
    intro hn nx hnx
    have hb : n + 1 < 54 := hn
    obtain ⟨-, h1, -, hm1, e2, h2⟩ := rd2 (n + 1) hb (306 + 4 * (n + 1)) (307 + 4 * (n + 1))
      (308 + 4 * (n + 1)) (by simp) (by simp) (by simp)
      (by simp [vsPushStep]) (by simp [vsPushStep]) (by simp [vsPushStep])
    have gp : Good rd vsSL w σ (.mul (.n (vsPV (n + 1))) (.n (vsPV n)) (.n (308 + 4 * (n + 1)))) :=
      hG (vsMul (vsPV (n + 1)) (vsPV n) (308 + 4 * (n + 1))) (vsPushStep_mem hb (by simp [vsPushStep]))
    simp only [Good] at gp
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by simp [vsPV]))] at gp
    have hstep : Stmt.HoldsList C rd σ (vsPushStep (n + 1)) nx kret := by
      simp only [vsPushStep, Nat.add_one_ne_zero, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, vsLd,
        vsMul, Nat.add_sub_cancel]
      exact ⟨h1, hm1, h2, gp, hnx⟩
    obtain ⟨ep, hp⟩ := ih (by omega) hstep
    refine ⟨?_, ?_⟩
    · rw [gp, ep, e2, ← pow_add, List.range_succ (n := n + 1), List.map_append, List.sum_append]
      simp
    · rw [List.range_succ (n := n + 1), List.flatMap_append, holdsList_append]
      exact hp

/-- **The push total and the bus depth, honestly.** -/
theorem vsPushT_complete (hl : args.length = 7) {logMem : ℕ} {hs : List ℕ} (hsl : hs.length = 6)
    (hh : ∀ x ∈ hs, x < 29) (hm : logMem ≤ 32)
    (hbk : ReadsAt rd (vsσ rd w args (.n 149))
      (Tables.blockKappaWords (gen ^ logMem) (hs.map (gen ^ ·))))
    (hexp : B1.ExpTables rd (vsσ rd w args (.n 4)) (vsσ rd w args (.n 5)))
    {C : CallRel} (hC : ∀ r, vsσ rd w args (.n 522) = r →
      C "log2_ceil_in_the_exponent__L0_L34"
        [gen ^ ((List.range 54).map fun b ↦ 2 ^ pushKappa logMem hs b).sum,
          vsσ rd w args (.n 4), vsσ rd w args (.n 5)] [r])
    {next : Prop} {kret : List E → Prop} (hn : next) :
    vsσ rd w args (.n 521) = gen ^ ((List.range 54).map fun b ↦ 2 ^ pushKappa logMem hs b).sum ∧
      Stmt.HoldsList C rd (vsσ rd w args) vsPushT next kret := by
  have hrest : Stmt.HoldsList C rd (vsσ rd w args)
      [vsCall "log2_ceil_in_the_exponent__L0_L34" [521, 4, 5] [522],
        .atom (.hint (.allocDyn (.n 523) (.n 522)))] next kret := by
    obtain ⟨e521, -⟩ := vsPush_loop (C := C) (kret := kret) hl hsl hh hm hbk hexp 53 (by norm_num)
      (nx := True) trivial
    simp only [Stmt.HoldsList, Stmt.Holds, vsCall, List.map_cons, List.map_nil]
    rw [show vsPV 53 = 521 from rfl] at e521
    exact ⟨by rw [e521]; exact hC _ rfl, trivial, hn⟩
  obtain ⟨e521, h⟩ := vsPush_loop (C := C) (kret := kret) hl hsl hh hm hbk hexp 53 (by norm_num) hrest
  refine ⟨e521, ?_⟩
  rw [vsPushT, holdsList_append]
  exact h

end
end LeanVM.Guest.B1.VerifySub
