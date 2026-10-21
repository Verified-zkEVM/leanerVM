/-
  LeanVM.Guest.B1.Comp.Da.RowsInS

  The trees' level loops, the row loops and `__loop93` loading from a region (`B1/Da/LevelsIn`,
  `RowsIn`, `CellIn`, `SetupIn`), by trees of known words within weights, under any semantics of
  `BLAKE2S`.
-/

module

public import LeanVM.Guest.B1.Comp.Da.PlacedIn
public import LeanVM.Guest.B1.Da.LevelsIn
public import LeanVM.Guest.B1.Da.SetupIn

/-!
# The hashing loops by region, under any semantics

The deployed lemmas with `S : BlakeSem` a parameter (`…S`): an instance's loads, calls and
arguments follow from its atoms other than `BLAKE2S` (`atomB_holds_of_ok`), so the proofs are the
deployed ones over `Program.RelB S` (`relInTWS_of_inv`, `loop_relInTWS`): `levels_relInTS`
(`da_levels__L{2^k}_L{k}`), `da_verify_cell_relInTS`, `rowLoop_relInTS`, `l93_relInTS`.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

variable {S : BlakeSem}

/-- **An iteration of a level loop.** -/
theorem lv_instS {rd : Reader} {k l : ℕ} (hk : k ≤ 10) (hl : l < k) {σ : Val} {fn : Fn} {es : List Ev}
    {vs : List V} {j nd : ℕ} (hf : coreProgram.find? (lvName k l) = some fn)
    (hp : fn.params.map σ = [gen ^ j, gen ^ 2 ^ (k - l - 1), gen ^ nd])
    (hw : walk σ fn.body = .ret es vs) (hok : ∀ e ∈ es, e.OkB S (coreProgram.RelB S rd) rd σ)
    (hj : j < 2 ^ (k - l - 1)) :
    (∀ A ∈ loadAddrs σ es, ∃ i, A = gpow i ∧ TreeR nd k i) ∧
      calls es = [⟨lvName k l, [if l = 0 then .n 23 else .n 25, .n 1, .n 2], [],
        decide (j + 1 ≠ 2 ^ (k - l - 1))⟩] ∧
      [if l = 0 then Core.V.n 23 else .n 25, .n 1, .n 2].map σ = [gen ^ (j + 1), gen ^ 2 ^ (k - l - 1), gen ^ nd] ∧
      allocs σ es = [] := by
  rw [find_lv k l hk hl, Option.some.injEq] at hf
  subst hf
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
  obtain ⟨h0, h1, h2⟩ := hp
  rw [lvBody_split, Main.walk_straight σ _ _ (lvPre_straight k l)] at hw
  obtain ⟨rfl, -⟩ : (if l = 0 then lvBody0 k else lvBody k l).dropLast.flatMap (Main.slEvs σ) = es ∧ _ := by
    injection hw; exact ⟨by assumption, by assumption⟩
  obtain ⟨-, hal, -, hcl⟩ := Main.straight_parts σ _ (lvPre_straight k l)
  have hA : ∀ {x : Atom}, Stmt.atom x ∈ (if l = 0 then lvBody0 k else lvBody k l).dropLast → x.HoldsB S rd σ :=
    fun hx => atomB_holds_of_ok hx hok
  set P := 2 ^ (k - l - 1) with hP
  have hP1 : 2 ^ (k - l) = 2 * P := by
    rw [hP, ← pow_succ']; congr 1; omega
  have hPk : 2 * P ≤ 2 ^ k := by rw [← hP1]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hlo : lvOff k l + 8 * P ≤ 4 * 2 ^ k := by unfold lvOff; rw [hP1]; omega
  have hlo1 : lvOff k (l + 1) = lvOff k l + 4 * P := by
    unfold lvOff; rw [hP1, show k - (l + 1) = k - l - 1 by omega, ← hP]; omega
  have hjP : j + 1 < 2 ^ 64 - 1 := by have := Nat.pow_le_pow_right (n := 2) (by norm_num) hk; omega
  have hdec : ∀ {c : V}, σ c = gen ^ (j + 1) + gen ^ P → decide (σ c ≠ 0) = decide (j + 1 ≠ P) :=
    fun hc => by
      rw [hc]
      have hPb : P < 2 ^ 33 := by have := Nat.pow_le_pow_right (n := 2) (by norm_num) hk; omega
      refine decide_eq_decide.mpr ⟨fun h he => h (by rw [he, e_add_eq_zero_iff]), fun h he => h ?_⟩
      exact gen_pow_inj' (by omega) (by omega) (e_add_eq_zero_iff.mp he)
  rcases Nat.eq_zero_or_pos l with rfl | hl1
  · simp only [↓reduceIte] at hA hal hcl ⊢
    have m3 : σ (.n 3) = σ (.n 0) * σ (.n 0) := hA (x := .mul (.n 3) (.n 0) (.n 0)) (by simp [lvBody0])
    have m4 : σ (.n 4) = σ (.n 3) * σ (.n 3) := hA (x := .mul (.n 4) (.n 3) (.n 3)) (by simp [lvBody0])
    have m5 : σ (.n 5) = σ (.n 2) * σ (.n 4) := hA (x := .mul (.n 5) (.n 2) (.n 4)) (by simp [lvBody0])
    have c6 : σ (.n 6) = word (gw (lvOff k 1)) 0 0 := hA (x := .const (.n 6) _) (by simp [lvBody0])
    have m7 : σ (.n 7) = σ (.n 2) * σ (.n 6) := hA (x := .mul (.n 7) (.n 2) (.n 6)) (by simp [lvBody0])
    have m8 : σ (.n 8) = σ (.n 0) * σ (.n 0) := hA (x := .mul (.n 8) (.n 0) (.n 0)) (by simp [lvBody0])
    have m9 : σ (.n 9) = σ (.n 7) * σ (.n 8) := hA (x := .mul (.n 9) (.n 7) (.n 8)) (by simp [lvBody0])
    have c19 : σ (.n 19) = word 2 0 0 := hA (x := .const (.n 19) (word 2 0 0)) (by simp [lvBody0])
    have m20 : σ (.n 20) = σ (.n 0) * σ (.n 19) := hA (x := .mul (.n 20) (.n 0) (.n 19)) (by simp [lvBody0])
    have a21 : σ (.n 21) = σ (.n 20) + σ (.n 1) := hA (x := .add (.n 21) (.n 20) (.n 1)) (by simp [lvBody0])
    have c22 : σ (.n 22) = word 2 0 0 := hA (x := .const (.n 22) (word 2 0 0)) (by simp [lvBody0])
    have m23 : σ (.n 23) = σ (.n 0) * σ (.n 22) := hA (x := .mul (.n 23) (.n 0) (.n 22)) (by simp [lvBody0])
    have h00 : lvOff k 0 = 0 := by simp [lvOff]
    have g5 : σ (.n 5) = gen ^ (nd + lvOff k 0 + 4 * j) := by
      rw [m5, m4, m3, h2, h0, h00]; ring
    have g9 : σ (.n 9) = gen ^ (nd + lvOff k 1 + 2 * j) := by
      rw [m9, m8, m7, c6, h2, h0, gw_lvOff hk (by omega) (by omega)]; ring
    have hlo1' : lvOff k 1 = lvOff k 0 + 4 * P := by rw [← hlo1]
    refine ⟨fun A hA' => ?_, ?_, ?_, by rw [hal]; rfl⟩
    · rw [loadAddrs_straight σ _ (by simpa using lvPre_straight k 0),
        show (lvBody0 k).dropLast.filterMap stmtLoad? =
          [(.n 5, 0), (.n 5, 1), (.n 5, 2), (.n 5, 3), (.n 9, 0), (.n 9, 1)] from rfl] at hA'
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA'
      rcases hA' with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, by rw [g5, addr_gen], by unfold TreeR; omega⟩
      · exact ⟨_, by rw [g5, addr_gen], by unfold TreeR; omega⟩
      · exact ⟨_, by rw [g5, addr_gen], by unfold TreeR; omega⟩
      · exact ⟨_, by rw [g5, addr_gen], by unfold TreeR; omega⟩
      · exact ⟨_, by rw [g9, addr_gen], by unfold TreeR; omega⟩
      · exact ⟨_, by rw [g9, addr_gen], by unfold TreeR; omega⟩
    · rw [hcl, show (lvBody0 k).dropLast.filterMap Main.Stmt.callS =
        [(some (.n 21), lvName k 0, [.n 23, .n 1, .n 2], [])] from rfl]
      simp only [List.map_cons, List.map_nil, Main.mkCall]
      rw [hdec (by rw [a21, m20, c19, h0, h1, word_gen, pow_succ])]
    · simp only [List.map_cons, List.map_nil]
      rw [m23, c22, h0, h1, h2, word_gen, pow_succ]
  · have hl0 : l ≠ 0 := by omega
    simp only [hl0, ↓reduceIte] at hA hal hcl ⊢
    have c3 : σ (.n 3) = word (gw (lvOff k l)) 0 0 := hA (x := .const (.n 3) _) (by simp [lvBody])
    have m4 : σ (.n 4) = σ (.n 2) * σ (.n 3) := hA (x := .mul (.n 4) (.n 2) (.n 3)) (by simp [lvBody])
    have m5 : σ (.n 5) = σ (.n 0) * σ (.n 0) := hA (x := .mul (.n 5) (.n 0) (.n 0)) (by simp [lvBody])
    have m6 : σ (.n 6) = σ (.n 5) * σ (.n 5) := hA (x := .mul (.n 6) (.n 5) (.n 5)) (by simp [lvBody])
    have m7 : σ (.n 7) = σ (.n 4) * σ (.n 6) := hA (x := .mul (.n 7) (.n 4) (.n 6)) (by simp [lvBody])
    have c8 : σ (.n 8) = word (gw (lvOff k (l + 1))) 0 0 := hA (x := .const (.n 8) _) (by simp [lvBody])
    have m9 : σ (.n 9) = σ (.n 2) * σ (.n 8) := hA (x := .mul (.n 9) (.n 2) (.n 8)) (by simp [lvBody])
    have m10 : σ (.n 10) = σ (.n 0) * σ (.n 0) := hA (x := .mul (.n 10) (.n 0) (.n 0)) (by simp [lvBody])
    have m11 : σ (.n 11) = σ (.n 9) * σ (.n 10) := hA (x := .mul (.n 11) (.n 9) (.n 10)) (by simp [lvBody])
    have c21 : σ (.n 21) = word 2 0 0 := hA (x := .const (.n 21) (word 2 0 0)) (by simp [lvBody])
    have m22 : σ (.n 22) = σ (.n 0) * σ (.n 21) := hA (x := .mul (.n 22) (.n 0) (.n 21)) (by simp [lvBody])
    have a23 : σ (.n 23) = σ (.n 22) + σ (.n 1) := hA (x := .add (.n 23) (.n 22) (.n 1)) (by simp [lvBody])
    have c24 : σ (.n 24) = word 2 0 0 := hA (x := .const (.n 24) (word 2 0 0)) (by simp [lvBody])
    have m25 : σ (.n 25) = σ (.n 0) * σ (.n 24) := hA (x := .mul (.n 25) (.n 0) (.n 24)) (by simp [lvBody])
    have g7 : σ (.n 7) = gen ^ (nd + lvOff k l + 4 * j) := by
      rw [m7, m6, m5, m4, c3, h2, h0, gw_lvOff hk (by omega) (by omega)]; ring
    have g11 : σ (.n 11) = gen ^ (nd + lvOff k (l + 1) + 2 * j) := by
      rw [m11, m10, m9, c8, h2, h0, gw_lvOff hk (by omega) (by omega)]; ring
    refine ⟨fun A hA' => ?_, ?_, ?_, by rw [hal]; rfl⟩
    · rw [loadAddrs_straight σ _ (by simpa [hl0] using lvPre_straight k l),
        show (lvBody k l).dropLast.filterMap stmtLoad? =
          [(.n 7, 0), (.n 7, 1), (.n 7, 2), (.n 7, 3), (.n 11, 0), (.n 11, 1)] from rfl] at hA'
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA'
      rcases hA' with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, by rw [g7, addr_gen], by unfold TreeR; omega⟩
      · exact ⟨_, by rw [g7, addr_gen], by unfold TreeR; omega⟩
      · exact ⟨_, by rw [g7, addr_gen], by unfold TreeR; omega⟩
      · exact ⟨_, by rw [g7, addr_gen], by unfold TreeR; omega⟩
      · exact ⟨_, by rw [g11, addr_gen], by unfold TreeR; omega⟩
      · exact ⟨_, by rw [g11, addr_gen], by unfold TreeR; omega⟩
    · rw [hcl, show (lvBody k l).dropLast.filterMap Main.Stmt.callS =
        [(some (.n 23), lvName k l, [.n 25, .n 1, .n 2], [])] from rfl]
      simp only [List.map_cons, List.map_nil, Main.mkCall]
      rw [hdec (by rw [a23, m22, c21, h0, h1, word_gen, pow_succ])]
    · simp only [List.map_cons, List.map_nil]
      rw [m25, c24, h0, h1, h2, word_gen, pow_succ]

/-- **An instance of the tree `da_levels__L{2^k}_L{k}` at `g^nd`.** -/
theorem dl_instS {rd : Reader} {k : ℕ} (hk : k ≤ 10) {σ : Val} {fn : Fn} {es : List Ev} {vs : List V}
    {nd : ℕ} (hf : coreProgram.find? (dlNames.getD k "") = some fn) (hp : fn.params.map σ = [gen ^ nd])
    (hw : walk σ fn.body = .ret es vs) (hok : ∀ e ∈ es, e.OkB S (coreProgram.RelB S rd) rd σ) :
    (∀ A ∈ loadAddrs σ es, ∃ i, A = gpow i ∧ TreeR nd k i) ∧
      calls es = (List.range k).map (fun l => ⟨lvName k l, [.n (4 + 5 * l), .n (5 + 5 * l), .n 0], [], true⟩) ∧
      (∀ l < k, [Core.V.n (4 + 5 * l), .n (5 + 5 * l), .n 0].map σ = [gen ^ 0, gen ^ 2 ^ (k - l - 1), gen ^ nd]) ∧
      allocs σ es = [] := by
  rw [find_dl k hk, Option.some.injEq] at hf
  subst hf
  have h0 : σ (.n 0) = gen ^ nd := by simpa using hp
  rw [dlBody_split, Main.walk_straight σ _ _ (dlPre_straight k)] at hw
  obtain ⟨rfl, -⟩ : (dlPre k).flatMap (Main.slEvs σ) = es ∧ _ := by
    injection hw; exact ⟨by assumption, by assumption⟩
  obtain ⟨-, hal, -, hcl⟩ := Main.straight_parts σ _ (dlPre_straight k)
  have hA : ∀ {x : Atom}, Stmt.atom x ∈ dlPre k → x.HoldsB S rd σ := fun hx => atomB_holds_of_ok hx hok
  have hblk : ∀ l < k, ∀ {x : Atom}, Stmt.atom x ∈ dlBlk k l → x.HoldsB S rd σ := fun l hl x hx =>
    hA (List.mem_append_left _ (List.mem_flatMap.mpr ⟨l, List.mem_range.mpr hl, hx⟩))
  have hvals : ∀ l < k, σ (.n (1 + 5 * l)) = 1 ∧ σ (.n (2 + 5 * l)) = gen ^ 2 ^ (k - l - 1) ∧
      σ (.n (3 + 5 * l)) = σ (.n (1 + 5 * l)) + σ (.n (2 + 5 * l)) ∧ σ (.n (4 + 5 * l)) = 1 ∧
      σ (.n (5 + 5 * l)) = gen ^ 2 ^ (k - l - 1) := fun l hl => by
    have c1 : σ (.n (1 + 5 * l)) = word 1 0 0 := hblk l hl (x := .const _ _) (by simp [dlBlk])
    have c2 : σ (.n (2 + 5 * l)) = word (gw (2 ^ (k - l - 1))) 0 0 := hblk l hl (x := .const _ _) (by simp [dlBlk])
    have a3 : σ (.n (3 + 5 * l)) = σ (.n (1 + 5 * l)) + σ (.n (2 + 5 * l)) :=
      hblk l hl (x := .add _ _ _) (by simp [dlBlk])
    have c4 : σ (.n (4 + 5 * l)) = word 1 0 0 := hblk l hl (x := .const (.n (4 + 5 * l)) _) (by simp [dlBlk])
    have c5 : σ (.n (5 + 5 * l)) = word (gw (2 ^ (k - l - 1))) 0 0 :=
      hblk l hl (x := .const (.n (5 + 5 * l)) _) (by simp [dlBlk])
    rw [word_one] at c1 c4
    rw [gw_end hk hl] at c2 c5
    exact ⟨c1, c2, a3, c4, c5⟩
  refine ⟨fun A hA' => ?_, ?_, fun l hl => ?_, by rw [hal, dlPre_allocs]; rfl⟩
  · rw [loadAddrs_straight σ _ (dlPre_straight k), dlPre_loads] at hA'
    have hpk : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA'
    rcases hA' with rfl | rfl
    · exact ⟨_, by rw [h0, addr_gen], by unfold TreeR; omega⟩
    · exact ⟨_, by rw [h0, addr_gen], by unfold TreeR; omega⟩
  · rw [hcl, dlPre_calls, List.map_map]
    refine List.map_congr_left fun l hl => ?_
    have hl' := List.mem_range.mp hl
    obtain ⟨e1, e2, e3, -, -⟩ := hvals l hl'
    simp only [Function.comp_apply, Main.mkCall]
    congr 1
    rw [e3, e1, e2, decide_eq_true_iff, ne_eq, e_add_eq_zero_iff]
    intro he
    have hb : 2 ^ (k - l - 1) ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := (gen_pow_eq_one_iff (show 2 ^ (k - l - 1) < 2 ^ 64 - 1 by omega)).mp he.symm
    exact absurd this (by positivity)
  · obtain ⟨-, -, -, e4, e5⟩ := hvals l hl
    simp only [List.map_cons, List.map_nil, e4, e5, h0, pow_zero]

/-- **A tree by region**: `da_levels__L{2^k}_L{k}` at `g^nd` loads only its own words. -/
theorem levels_relInTS (fs : String → ℕ) {rd : Reader} {k : ℕ} (hk : k ≤ 10) {nd : ℕ} {R : ℕ → Prop}
    (hR : ∀ i, TreeR nd k i → R i) {rets : List E} (h : coreProgram.RelB S rd (dlNames.getD k "") [gen ^ nd] rets) :
    RelInTWS S fs rd R (dlTot fs k) (dlNames.getD k "") [gen ^ nd] rets fun θ => dlTot θ k := by
  have hb : ∀ l < k, 2 ^ (k - l - 1) < 2 ^ 64 - 2 := fun l hl => by
    have : 2 ^ (k - l - 1) ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have key := relInTWS_of_inv fs (R := R)
    (fun f args => (f = dlNames.getD k "" ∧ args = [gen ^ nd]) ∨
      (∃ l < k, f = lvName k l ∧ ∃ j < 2 ^ (k - l - 1), args = [gen ^ j, gen ^ 2 ^ (k - l - 1), gen ^ nd]))
    (fun θ f args => if f = dlNames.getD k "" then dlTot θ k
      else lvTot θ f (logG (args.getD 1 0)) (logG (args.getD 0 0)))
    (fun f args σ fn es vs hI hf hp hw hok => ?_) (Or.inl ⟨rfl, rfl⟩) h
  · simpa using key
  rcases hI with ⟨rfl, rfl⟩ | ⟨l, hl, rfl, j, hj, rfl⟩
  · obtain ⟨hld, hc, hargs, ha⟩ := dl_instS hk hf hp hw hok
    refine ⟨fun A hA => ?_, fun c hc' _ => ?_, ?_⟩
    · obtain ⟨i, hi, hT⟩ := hld A hA
      exact ⟨i, hi, hR i hT⟩
    · rw [hc] at hc'
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hc'
      have hl' := List.mem_range.mp hl
      exact Or.inr ⟨l, hl', rfl, 0, by positivity, hargs l hl'⟩
    · intro θ
      rw [hc, ha, callsTot, List.map_map, List.sum_nil, Nat.add_zero]
      simp only [↓reduceIte, dlTot]
      congr 2
      refine List.map_congr_left fun l hl => ?_
      have hl' := List.mem_range.mp hl
      simp only [Function.comp_apply, ↓reduceIte, hargs l hl', lvName_ne hk hl', List.getD_cons_succ,
        List.getD_cons_zero, logG_gen_pow (show 0 < 2 ^ 64 - 1 by norm_num),
        logG_gen_pow (show 2 ^ (k - l - 1) < 2 ^ 64 - 1 by have := hb l hl'; omega)]
  · obtain ⟨hld, hc, hnext, ha⟩ := lv_instS hk hl hf hp hw hok hj
    refine ⟨fun A hA => ?_, fun c hc' ht => ?_, ?_⟩
    · obtain ⟨i, hi, hT⟩ := hld A hA
      exact ⟨i, hi, hR i hT⟩
    · rw [hc] at hc'
      obtain rfl := List.mem_singleton.mp hc'
      simp only [decide_eq_true_eq] at ht
      exact Or.inr ⟨l, hl, rfl, j + 1, by omega, hnext⟩
    · intro θ
      have hbl := hb l hl
      rw [hc, ha, callsTot]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, lvName_ne hk hl,
        ↓reduceIte, hnext, List.getD_cons_succ, List.getD_cons_zero]
      rw [logG_gen_pow (show j < 2 ^ 64 - 1 by omega), logG_gen_pow (show 2 ^ (k - l - 1) < 2 ^ 64 - 1 by omega)]
      by_cases hj1 : j + 1 = 2 ^ (k - l - 1)
      · simp only [hj1, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte, lvTot]
        rw [show 2 ^ (k - l - 1) - j = 1 by omega]
        ring
      · simp only [ne_eq, hj1, not_false_eq_true, decide_true, ↓reduceIte, lvTot]
        rw [logG_gen_pow (show j + 1 < 2 ^ 64 - 1 by omega),
          show 2 ^ (k - l - 1) - j = (2 ^ (k - l - 1) - (j + 1)) + 1 by omega]
        ring

/-- **`da_verify_cell(lvals)` loads the 256 words at `lvals`**, `lvals = g^l`: from a region holding
them it holds in that region, by a tree of its frame. -/
theorem da_verify_cell_relInTS (fs : String → ℕ) {rd : Reader} {R : ℕ → Prop} {l : ℕ}
    (hR : ∀ k < 256, R (l + k)) {rets : List E} (h : coreProgram.RelB S rd "da_verify_cell" [gen ^ l] rets) :
    RelInTWS S fs rd R (fs "da_verify_cell") "da_verify_cell" [gen ^ l] rets fun θ => θ "da_verify_cell" := by
  refine relInTWS_of_inv fs (fun f args => f = "da_verify_cell" ∧ args = [gen ^ l]) (fun θ f _ => θ f)
    (fun f args σ fn es vs hI hf hp hw _ => ?_) ⟨rfl, rfl⟩ h
  obtain ⟨rfl, rfl⟩ := hI
  obtain ⟨hl, hc, ha⟩ := vc_inst hf hp hw
  refine ⟨fun A hA => ?_, fun c hc' => by rw [hc] at hc'; simp at hc', fun θ => by rw [hc, ha]; rfl⟩
  obtain ⟨i, hi, h1, h2⟩ := hl A hA
  exact ⟨i, hi, by have := hR (i - l) (by omega); rwa [show l + (i - l) = i by omega] at this⟩

/-- **An iteration of the row loop.** -/
theorem row_instS {rd : Reader} (store : Bool) {σ : Val} {fn : Fn} {es : List Ev} {vs : List V}
    {j r l q b nd p a pd : ℕ} (hf : coreProgram.find? (rowName store) = some fn)
    (hp : fn.params.map σ = [gen ^ j, gen ^ r, gen ^ l, gen ^ q, gen ^ b, gen ^ nd, gen ^ p])
    (hw : walk σ fn.body = .ret es vs) (hok : ∀ e ∈ es, e.OkB S (coreProgram.RelB S rd) rd σ)
    (hj : j < r) (hr : r < 2 ^ 33) (hrb : rd (gpow (q + j)) = some (gen ^ (a + 129 * j)))
    (hpb : store = true → rd (gpow (p + j)) = some (gen ^ (pd + 128 * j))) :
    (∀ A ∈ loadAddrs σ es, ∃ i, A = gpow i ∧ RowR store r l q b nd p a pd i) ∧
      calls es = [⟨"da_verify_cell", [.n 2], [.n 7, .n 8, .n 9], true⟩,
        ⟨rowName store, if store then [.n 25, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6]
          else [.n 21, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6], [], decide (j + 1 ≠ r)⟩] ∧
      [Core.V.n 2].map σ = [gen ^ l] ∧
      (if store then [Core.V.n 25, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6]
        else [.n 21, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6]).map σ =
        [gen ^ (j + 1), gen ^ r, gen ^ l, gen ^ q, gen ^ b, gen ^ nd, gen ^ p] ∧
      allocs σ es = [] := by
  rw [find_row, Option.some.injEq] at hf
  subst hf
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hp
  rw [rowBody_split, Main.walk_straight σ _ _ (rowPre_straight store)] at hw
  obtain ⟨rfl, -⟩ : (rowBody store).dropLast.flatMap (Main.slEvs σ) = es ∧ _ := by
    injection hw; exact ⟨by assumption, by assumption⟩
  obtain ⟨-, hal, -, hcl⟩ := Main.straight_parts σ _ (rowPre_straight store)
  have hA : ∀ {x : Atom}, Stmt.atom x ∈ (rowBody store).dropLast → x.HoldsB S rd σ :=
    fun hx => atomB_holds_of_ok hx hok
  have hsucc : ∀ {x y : V}, σ x = gen ^ j → σ y = word 2 0 0 → σ x * σ y = gen ^ (j + 1) := fun hx hy => by
    rw [hx, hy, word_gen, pow_succ]
  have hdec : ∀ {c : V}, σ c = gen ^ (j + 1) + gen ^ r → decide (σ c ≠ 0) = decide (j + 1 ≠ r) := fun hc => by
    rw [hc]
    refine decide_eq_decide.mpr ⟨fun h he => h (by rw [he, e_add_eq_zero_iff]), fun h he => h ?_⟩
    exact gen_pow_inj' (by omega) (by omega) (e_add_eq_zero_iff.mp he)
  have e11 : ∀ {x : V}, σ x = gen ^ (q + j) → LoadHolds rd (σ x) 0 (σ (.n 11)) →
      σ (.n 11) = gen ^ (a + 129 * j) := fun hx hl => by
    have := load_rd hl
    rw [hx, addr_gen, Nat.add_zero] at this
    exact Option.some.inj (this.symm.trans hrb)
  cases store
  · have m10 : σ (.n 10) = σ (.n 3) * σ (.n 0) := hA (x := .mul (.n 10) (.n 3) (.n 0)) (by simp [rowBody])
    have l11 : LoadHolds rd (σ (.n 10)) 0 (σ (.n 11)) := hA (x := .load (.n 11) (.n 10) 0) (by simp [rowBody])
    have m12 : σ (.n 12) = σ (.n 11) * σ (.n 4) := hA (x := .mul (.n 12) (.n 11) (.n 4)) (by simp [rowBody])
    have m15 : σ (.n 15) = σ (.n 0) * σ (.n 0) := hA (x := .mul (.n 15) (.n 0) (.n 0)) (by simp [rowBody])
    have m16 : σ (.n 16) = σ (.n 5) * σ (.n 15) := hA (x := .mul (.n 16) (.n 5) (.n 15)) (by simp [rowBody])
    have c17 : σ (.n 17) = word 2 0 0 := hA (x := .const (.n 17) (word 2 0 0)) (by simp [rowBody])
    have m18 : σ (.n 18) = σ (.n 0) * σ (.n 17) := hA (x := .mul (.n 18) (.n 0) (.n 17)) (by simp [rowBody])
    have a19 : σ (.n 19) = σ (.n 18) + σ (.n 1) := hA (x := .add (.n 19) (.n 18) (.n 1)) (by simp [rowBody])
    have c20 : σ (.n 20) = word 2 0 0 := hA (x := .const (.n 20) (word 2 0 0)) (by simp [rowBody])
    have m21 : σ (.n 21) = σ (.n 0) * σ (.n 20) := hA (x := .mul (.n 21) (.n 0) (.n 20)) (by simp [rowBody])
    have g10 : σ (.n 10) = gen ^ (q + j) := by rw [m10, h3, h0, ← pow_add]
    have g11 := e11 g10 l11
    have g12 : σ (.n 12) = gen ^ (a + 129 * j + b) := by rw [m12, g11, h4, ← pow_add]
    have g16 : σ (.n 16) = gen ^ (nd + 2 * j) := by rw [m16, m15, h5, h0, ← pow_add, ← pow_add, two_mul]
    refine ⟨fun A hA => ?_, ?_, by rw [List.map_cons, List.map_nil, h2], ?_, by rw [hal]; rfl⟩
    · rw [loadAddrs_straight σ _ (rowPre_straight false),
        show (rowBody false).dropLast.filterMap stmtLoad? =
          [(.n 10, 0), (.n 12, 0), (.n 12, 1), (.n 16, 0), (.n 16, 1)] from rfl] at hA
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl | rfl | rfl | rfl
      · exact ⟨q + j, by rw [g10, addr_gen, Nat.add_zero], Or.inl ⟨j, hj, Or.inl rfl⟩⟩
      · exact ⟨a + 129 * j + b, by rw [g12, addr_gen, Nat.add_zero], Or.inl ⟨j, hj, Or.inr (Or.inl rfl)⟩⟩
      · exact ⟨a + 129 * j + b + 1, by rw [g12, addr_gen], Or.inl ⟨j, hj, Or.inr (Or.inr (Or.inl rfl))⟩⟩
      · exact ⟨nd + 2 * j, by rw [g16, addr_gen, Nat.add_zero], Or.inl ⟨j, hj, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩⟩
      · exact ⟨nd + 2 * j + 1, by rw [g16, addr_gen],
          Or.inl ⟨j, hj, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩⟩
    · rw [hcl, show (rowBody false).dropLast.filterMap Main.Stmt.callS =
        [(none, "da_verify_cell", [.n 2], [.n 7, .n 8, .n 9]),
         (some (.n 19), "__loop486", [.n 21, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6], [])] from rfl]
      simp only [List.map_cons, List.map_nil, Main.mkCall, Bool.false_eq_true, ↓reduceIte]
      rw [hdec (by rw [a19, m18, hsucc h0 c17, h1])]
      rfl
    · simp only [Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil]
      rw [m21, hsucc h0 c20, h1, h2, h3, h4, h5, h6]
  · have m10 : σ (.n 10) = σ (.n 3) * σ (.n 0) := hA (x := .mul (.n 10) (.n 3) (.n 0)) (by simp [rowBody])
    have l11 : LoadHolds rd (σ (.n 10)) 0 (σ (.n 11)) := hA (x := .load (.n 11) (.n 10) 0) (by simp [rowBody])
    have m12 : σ (.n 12) = σ (.n 11) * σ (.n 4) := hA (x := .mul (.n 12) (.n 11) (.n 4)) (by simp [rowBody])
    have m15 : σ (.n 15) = σ (.n 0) * σ (.n 0) := hA (x := .mul (.n 15) (.n 0) (.n 0)) (by simp [rowBody])
    have m16 : σ (.n 16) = σ (.n 5) * σ (.n 15) := hA (x := .mul (.n 16) (.n 5) (.n 15)) (by simp [rowBody])
    have m17 : σ (.n 17) = σ (.n 6) * σ (.n 0) := hA (x := .mul (.n 17) (.n 6) (.n 0)) (by simp [rowBody])
    have l18 : LoadHolds rd (σ (.n 17)) 0 (σ (.n 18)) := hA (x := .load (.n 18) (.n 17) 0) (by simp [rowBody])
    have m19 : σ (.n 19) = σ (.n 4) * σ (.n 4) := hA (x := .mul (.n 19) (.n 4) (.n 4)) (by simp [rowBody])
    have m20 : σ (.n 20) = σ (.n 18) * σ (.n 19) := hA (x := .mul (.n 20) (.n 18) (.n 19)) (by simp [rowBody])
    have c21 : σ (.n 21) = word 2 0 0 := hA (x := .const (.n 21) (word 2 0 0)) (by simp [rowBody])
    have m22 : σ (.n 22) = σ (.n 0) * σ (.n 21) := hA (x := .mul (.n 22) (.n 0) (.n 21)) (by simp [rowBody])
    have a23 : σ (.n 23) = σ (.n 22) + σ (.n 1) := hA (x := .add (.n 23) (.n 22) (.n 1)) (by simp [rowBody])
    have c24 : σ (.n 24) = word 2 0 0 := hA (x := .const (.n 24) (word 2 0 0)) (by simp [rowBody])
    have m25 : σ (.n 25) = σ (.n 0) * σ (.n 24) := hA (x := .mul (.n 25) (.n 0) (.n 24)) (by simp [rowBody])
    have g10 : σ (.n 10) = gen ^ (q + j) := by rw [m10, h3, h0, ← pow_add]
    have g11 := e11 g10 l11
    have g12 : σ (.n 12) = gen ^ (a + 129 * j + b) := by rw [m12, g11, h4, ← pow_add]
    have g16 : σ (.n 16) = gen ^ (nd + 2 * j) := by rw [m16, m15, h5, h0, ← pow_add, ← pow_add, two_mul]
    have g17 : σ (.n 17) = gen ^ (p + j) := by rw [m17, h6, h0, ← pow_add]
    have g18 : σ (.n 18) = gen ^ (pd + 128 * j) := by
      have := load_rd l18
      rw [g17, addr_gen, Nat.add_zero] at this
      exact Option.some.inj (this.symm.trans (hpb rfl))
    have g20 : σ (.n 20) = gen ^ (pd + 128 * j + 2 * b) := by
      rw [m20, m19, g18, h4, ← pow_add, ← pow_add, two_mul]
    refine ⟨fun A hA => ?_, ?_, by rw [List.map_cons, List.map_nil, h2], ?_, by rw [hal]; rfl⟩
    · rw [loadAddrs_straight σ _ (rowPre_straight true),
        show (rowBody true).dropLast.filterMap stmtLoad? =
          [(.n 10, 0), (.n 12, 0), (.n 12, 1), (.n 16, 0), (.n 16, 1), (.n 17, 0), (.n 20, 0), (.n 20, 1)]
          from rfl] at hA
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨q + j, by rw [g10, addr_gen, Nat.add_zero], Or.inl ⟨j, hj, Or.inl rfl⟩⟩
      · exact ⟨a + 129 * j + b, by rw [g12, addr_gen, Nat.add_zero], Or.inl ⟨j, hj, Or.inr (Or.inl rfl)⟩⟩
      · exact ⟨a + 129 * j + b + 1, by rw [g12, addr_gen], Or.inl ⟨j, hj, Or.inr (Or.inr (Or.inl rfl))⟩⟩
      · exact ⟨nd + 2 * j, by rw [g16, addr_gen, Nat.add_zero], Or.inl ⟨j, hj, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩⟩
      · exact ⟨nd + 2 * j + 1, by rw [g16, addr_gen],
          Or.inl ⟨j, hj, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩⟩
      · exact ⟨p + j, by rw [g17, addr_gen, Nat.add_zero],
          Or.inl ⟨j, hj, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inl rfl⟩))))⟩⟩
      · exact ⟨pd + 128 * j + 2 * b, by rw [g20, addr_gen, Nat.add_zero],
          Or.inl ⟨j, hj, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inl rfl)⟩))))⟩⟩
      · exact ⟨pd + 128 * j + 2 * b + 1, by rw [g20, addr_gen],
          Or.inl ⟨j, hj, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inr rfl)⟩))))⟩⟩
    · rw [hcl, show (rowBody true).dropLast.filterMap Main.Stmt.callS =
        [(none, "da_verify_cell", [.n 2], [.n 7, .n 8, .n 9]),
         (some (.n 23), "__loop484", [.n 25, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6], [])] from rfl]
      simp only [List.map_cons, List.map_nil, Main.mkCall, ↓reduceIte]
      rw [hdec (by rw [a23, m22, hsucc h0 c21, h1])]
      rfl
    · simp only [↓reduceIte, List.map_cons, List.map_nil]
      rw [m25, hsucc h0 c24, h1, h2, h3, h4, h5, h6]

/-- **The row loop by region**: from row `g^j`, `j < r`, on a memory holding the rows' chains at
`rowbase` and, in the prefix columns, the rows' prefix bases, a tree of `rowTot` words whose loads
are in `RowR`. -/
theorem rowLoop_relInTS (fs : String → ℕ) (store : Bool) {rd : Reader} {r l q b nd p a pd : ℕ} {R : ℕ → Prop}
    (hr : r < 2 ^ 33) (hrb : ∀ j < r, rd (gpow (q + j)) = some (gen ^ (a + 129 * j)))
    (hpb : store = true → ∀ j < r, rd (gpow (p + j)) = some (gen ^ (pd + 128 * j)))
    (hR : ∀ i, RowR store r l q b nd p a pd i → R i) {j : ℕ} (hj : j < r)
    (h : coreProgram.RelB S rd (rowName store) [gen ^ j, gen ^ r, gen ^ l, gen ^ q, gen ^ b, gen ^ nd, gen ^ p] []) :
    RelInTWS S fs rd R (rowTot fs store r j) (rowName store)
      [gen ^ j, gen ^ r, gen ^ l, gen ^ q, gen ^ b, gen ^ nd, gen ^ p] [] fun θ => rowTot θ store r j := by
  have key := relInTWS_of_inv fs (R := R)
    (fun f args => (f = rowName store ∧ ∃ j < r, args = [gen ^ j, gen ^ r, gen ^ l, gen ^ q, gen ^ b, gen ^ nd, gen ^ p]) ∨
      (f = "da_verify_cell" ∧ args = [gen ^ l]))
    (fun θ f args => if f = "da_verify_cell" then θ "da_verify_cell" else rowTot θ store r (logG (args.headD 0)))
    (fun f args σ fn es vs hI hf hp hw hok => ?_) (Or.inl ⟨rfl, j, hj, rfl⟩) h
  · simpa [rowName_ne store, logG_gen_pow (show j < 2 ^ 64 - 1 by omega)] using key
  rcases hI with ⟨rfl, j, hj, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨hl, hc, h2, hnext, ha⟩ := row_instS store hf hp hw hok hj hr (hrb j hj) (fun hs => hpb hs j hj)
    refine ⟨fun A hA => ?_, fun c hc' ht => ?_, ?_⟩
    · obtain ⟨i, hi, hRi⟩ := hl A hA
      exact ⟨i, hi, hR i hRi⟩
    · rw [hc] at hc'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
      rcases hc' with rfl | rfl
      · exact Or.inr ⟨rfl, h2⟩
      · simp only [decide_eq_true_eq] at ht
        exact Or.inl ⟨rfl, j + 1, by omega, hnext⟩
    · intro θ
      rw [hc, ha, callsTot]
      simp only [List.map_cons, List.map_nil, ↓reduceIte, List.sum_cons, List.sum_nil,
        rowName_ne store, hnext, List.headD_cons, Nat.add_zero, List.sum_nil]
      rw [logG_gen_pow (show j < 2 ^ 64 - 1 by omega)]
      by_cases hj1 : j + 1 = r
      · simp only [hj1, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte, rowTot]
        rw [show r - j = 1 by omega]
        ring
      · simp only [ne_eq, hj1, not_false_eq_true, decide_true, ↓reduceIte, rowTot]
        rw [logG_gen_pow (show j + 1 < 2 ^ 64 - 1 by omega), show r - j = (r - (j + 1)) + 1 by omega]
        ring
  · obtain ⟨hl, hc, ha⟩ := vc_inst hf hp hw
    refine ⟨fun A hA => ?_, fun c hc' => by rw [hc] at hc'; simp at hc', fun θ => by rw [hc, ha]; simp [callsTot]⟩
    obtain ⟨i, hi, h1, h2⟩ := hl A hA
    exact ⟨i, hi, hR i (Or.inr ⟨h1, h2⟩)⟩

theorem l93_relInTS (fs : String → ℕ) {rd : Reader} {r P D T : ℕ} {R : ℕ → Prop} (hr : r < 2 ^ 33)
    (hpb : ∀ j < r, rd (gpow (P + j)) = some (gen ^ (D + 128 * j)))
    (hR : ∀ i, R93 r P D T i → R i) {j : ℕ} (hj : j < r)
    (h : coreProgram.RelB S rd "__loop93" [gen ^ j, gen ^ r, gen ^ P, gen ^ T] []) :
    RelInTWS S fs rd R ((r - j) * fs "__loop93" + fs "__loop93") "__loop93" [gen ^ j, gen ^ r, gen ^ P, gen ^ T] []
      fun θ => (r - j) * θ "__loop93" + θ "__loop93" := by
  have hs : rhPre.all Main.Stmt.straight = true := by simp [rhPre, Main.Stmt.straight]
  refine loop_relInTWS fs (pre := rhPre) (c := .n 236) (targs := [.n 238, .n 1, .n 2, .n 3])
    (ps := [gen ^ r, gen ^ P, gen ^ T]) find_l93 (by simp [rhBody, rhPre]) hs
    (by rw [rhPre, List.filterMap_append, show (rhAtoms.map Stmt.atom).filterMap Main.Stmt.callS = [] by
      rw [List.filterMap_map]; simp [Function.comp_def, Main.Stmt.callS]]; rfl)
    (by rw [rhPre, List.filterMap_append, show (rhAtoms.map Stmt.atom).filterMap Main.Stmt.allocSz = [] by
      decide +kernel]; rfl) hr (fun j hj σ hp hok => ?_) hj h
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
  obtain ⟨h0, h1, h2, h3⟩ := hp
  have hA : ∀ {x : Atom}, x ∈ rhAtoms → x.HoldsB S rd σ := fun hx =>
    atomB_holds_of_ok (List.mem_append_left _ (List.mem_map.mpr ⟨_, hx, rfl⟩)) hok
  have m4 : σ (.n 4) = σ (.n 2) * σ (.n 0) := hA (x := .mul (.n 4) (.n 2) (.n 0)) (by simp [rhAtoms])
  have l5 : LoadHolds rd (σ (.n 4)) 0 (σ (.n 5)) := hA (x := .load (.n 5) (.n 4) 0) (by simp [rhAtoms])
  have m232 : σ (.n 232) = σ (.n 0) * σ (.n 0) := hA (x := .mul (.n 232) (.n 0) (.n 0)) (by simp [rhAtoms])
  have m233 : σ (.n 233) = σ (.n 3) * σ (.n 232) := hA (x := .mul (.n 233) (.n 3) (.n 232)) (by simp [rhAtoms])
  have c234 : σ (.n 234) = word 2 0 0 := hA (x := .const (.n 234) (word 2 0 0)) (by simp [rhAtoms])
  have m235 : σ (.n 235) = σ (.n 0) * σ (.n 234) := hA (x := .mul (.n 235) (.n 0) (.n 234)) (by simp [rhAtoms])
  have a236 : σ (.n 236) = σ (.n 235) + σ (.n 1) := hA (x := .add (.n 236) (.n 235) (.n 1)) (by simp [rhAtoms])
  have c237 : σ (.n 237) = word 2 0 0 := hA (x := .const (.n 237) (word 2 0 0)) (by simp [rhAtoms])
  have m238 : σ (.n 238) = σ (.n 0) * σ (.n 237) := hA (x := .mul (.n 238) (.n 0) (.n 237)) (by simp [rhAtoms])
  have g4 : σ (.n 4) = gen ^ (P + j) := by rw [m4, h2, h0, ← pow_add]
  have g5 : σ (.n 5) = gen ^ (D + 128 * j) := by
    have := load_rd l5
    rw [g4, addr_gen, Nat.add_zero] at this
    exact Option.some.inj (this.symm.trans (hpb j hj))
  have g233 : σ (.n 233) = gen ^ (T + 2 * j) := by rw [m233, m232, h3, h0]; ring
  refine ⟨fun A' hA' => ?_, tail_iff hj hr a236 (by rw [m235, gen_mul_w2 h0 c234]) h1, ?_⟩
  · rw [loadAddrs_straight σ _ hs, rh_loads] at hA'
    simp only [List.map_append, List.map_cons, List.map_nil, List.map_map, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, List.mem_map, List.mem_range, Function.comp_apply] at hA'
    rcases hA' with (rfl | ⟨k, hk, rfl⟩) | rfl | rfl
    · exact ⟨P + j, by rw [g4, addr_gen, Nat.add_zero], hR _ ⟨j, hj, Or.inl rfl⟩⟩
    · exact ⟨D + 128 * j + k, by rw [g5, addr_gen], hR _ ⟨j, hj, Or.inr (Or.inl ⟨by omega, by omega⟩)⟩⟩
    · exact ⟨T + 2 * j, by rw [g233, addr_gen, Nat.add_zero], hR _ ⟨j, hj, Or.inr (Or.inr (Or.inl rfl))⟩⟩
    · exact ⟨T + 2 * j + 1, by rw [g233, addr_gen], hR _ ⟨j, hj, Or.inr (Or.inr (Or.inr rfl))⟩⟩
  · simp only [List.map_cons, List.map_nil, m238, gen_mul_w2 h0 c237, h1, h2, h3]

end
end LeanVM.Guest.B1.Digest
