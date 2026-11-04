/-
  LeanVM.Guest.B1.Eq.RsEqRun

  B1 for `rs_eq_run`: the telescoped ring-switch rows, eight coordinates a row.
-/

module

public import LeanVM.Guest.B1.Eq.RsLoop
public import LeanVM.Guest.B1.Bits.GPower

/-!
# `rs_eq_run` (lean_ethereum.py:1011-1037 at leanVM `c4f4bc92`)

`rs_eq_run(chain, z_vals, point1, count_g)` hints the six bits of `count` (`count_g = g^count`),
pins them by booleanity and `q_g^8 · r_g = count_g` (`r_g` from bits `0 .. 2`, `q_g` from bits
`3 .. 5`, so `count = 8q + r`), runs `__loop5` over the `q` full chunks (`rs_eq_rows__L8` each),
and dispatches the remainder's `rs_eq_rows__L{r}` on the row `chain·g^(64q)`; it returns that
call's return, the last row (`rs_eq_run_holds`).

The rows from the chunks and back: `rows_of_chunks`, `chunks_of_rows` (chunk `t` is coordinates
`8t ..` and row `t`, `ChunkOk`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The template -/

/-- The expansion of `rs_eq_run`. -/
def rsBody : List Stmt :=
  [.atom (.hint (.bitsExp (.n 3) 6 (.stack [.n 4, .n 5, .n 6, .n 7, .n 8, .n 9]))),
    .atom (.mul (.n 4) (.n 4) (.n 4)), .atom (.const (.n 10) (word 1 0 0)),
    .atom (.const (.n 11) (word 3 0 0)), .atom (.mul (.n 12) (.n 4) (.n 11)),
    .atom (.add (.n 13) (.n 10) (.n 12)), .atom (.mul (.n 5) (.n 5) (.n 5)),
    .atom (.const (.n 14) (word 1 0 0)), .atom (.const (.n 15) (word 5 0 0)),
    .atom (.mul (.n 16) (.n 5) (.n 15)), .atom (.add (.n 17) (.n 14) (.n 16)),
    .atom (.mul (.n 18) (.n 13) (.n 17)), .atom (.mul (.n 6) (.n 6) (.n 6)),
    .atom (.const (.n 19) (word 1 0 0)), .atom (.const (.n 20) (word 17 0 0)),
    .atom (.mul (.n 21) (.n 6) (.n 20)), .atom (.add (.n 22) (.n 19) (.n 21)),
    .atom (.mul (.n 23) (.n 18) (.n 22)), .atom (.mul (.n 7) (.n 7) (.n 7)),
    .atom (.const (.n 24) (word 1 0 0)), .atom (.const (.n 25) (word 3 0 0)),
    .atom (.mul (.n 26) (.n 7) (.n 25)), .atom (.add (.n 27) (.n 24) (.n 26)),
    .atom (.mul (.n 8) (.n 8) (.n 8)), .atom (.const (.n 28) (word 1 0 0)),
    .atom (.const (.n 29) (word 5 0 0)), .atom (.mul (.n 30) (.n 8) (.n 29)),
    .atom (.add (.n 31) (.n 28) (.n 30)), .atom (.mul (.n 32) (.n 27) (.n 31)),
    .atom (.mul (.n 9) (.n 9) (.n 9)), .atom (.const (.n 33) (word 1 0 0)),
    .atom (.const (.n 34) (word 17 0 0)), .atom (.mul (.n 35) (.n 9) (.n 34)),
    .atom (.add (.n 36) (.n 33) (.n 35)), .atom (.mul (.n 37) (.n 32) (.n 36)),
    .atom (.mul (.n 38) (.n 37) (.n 37)), .atom (.mul (.n 39) (.n 38) (.n 38)),
    .atom (.mul (.n 40) (.n 39) (.n 39)), .atom (.mul (.n 41) (.n 40) (.n 23)),
    .atom (.assertEq (.n 41) (.n 3)), .atom (.const (.n 42) (word 1 0 0)),
    .atom (.add (.n 43) (.n 42) (.n 37)), .atom (.const (.n 44) (word 1 0 0)),
    .callIf (.n 43) "__loop5" [.n 44, .n 37, .n 0, .n 1, .n 2],
    .atom (.mul (.n 45) (.n 37) (.n 37)), .atom (.mul (.n 46) (.n 45) (.n 45)),
    .atom (.mul (.n 47) (.n 46) (.n 46)), .atom (.mul (.n 48) (.n 37) (.n 37)),
    .atom (.mul (.n 49) (.n 48) (.n 48)), .atom (.mul (.n 50) (.n 49) (.n 49)),
    .atom (.mul (.n 51) (.n 50) (.n 50)), .atom (.mul (.n 52) (.n 51) (.n 51)),
    .atom (.mul (.n 53) (.n 52) (.n 52)), .atom (.mul (.n 54) (.n 0) (.n 53)),
    .atom (.mul (.n 55) (.n 1) (.n 47)), .atom (.mul (.n 56) (.n 2) (.n 47)),
    .dispatch (.n 23) ["rs_eq_rows__L0", "rs_eq_rows__L1", "rs_eq_rows__L2", "rs_eq_rows__L3",
      "rs_eq_rows__L4", "rs_eq_rows__L5", "rs_eq_rows__L6", "rs_eq_rows__L7"] [.n 54, .n 55, .n 56]
      [.n 57],
    .atom (.copy (.n 58) (.n 57)), .ret [.n 58]]

theorem core6_body : Fn.body Data.core6 = rsBody := stmtsEqb_sound (by decide +kernel)

theorem find_rs_eq_run : coreProgram.find? "rs_eq_run" = some Data.core6 :=
  Program.find?_of_indexOf? (j := 6) (by decide +kernel) rfl

theorem rs_consts : word 3 0 0 = gen ^ 2 ^ 0 + 1 ∧ word 5 0 0 = gen ^ 2 ^ 1 + 1 ∧
    word 17 0 0 = gen ^ 2 ^ 2 + 1 :=
  ⟨word_gpow_one 0 (by norm_num) 3 (by decide), word_gpow_one 1 (by norm_num) 5 (by decide),
    word_gpow_one 2 (by norm_num) 17 (by decide)⟩

/-! ## Chunks and rows -/

/-- Chunk `t`: its coordinates from `z·g^(8t)`, `p·g^(8t)`, row `t` from `chain·g^(64t)`, and
row `t + 1` its product. -/
def ChunkOk (rd : Reader) (chain z p : E) (t : ℕ) (zt pt ct : List E) : Prop :=
  ReadsAt rd (z * gen ^ (8 * t)) zt ∧ ReadsAt rd (p * gen ^ (8 * t)) pt ∧ ct.length = 64 ∧
    ReadsAt rd (chain * gen ^ (64 * t)) ct ∧
    ∀ k < 64, LoadHolds rd (chain * gen ^ (64 * t)) (64 + k) (ringRow (ct.getD k 0) zt pt k)

theorem ringRow_append (c : E) (A A' B B' : List E) (k : ℕ) (h : A.length = B.length) :
    ringRow c (A ++ A') (B ++ B') k = ringRow (ringRow c A B k) A' B' k := by
  rw [ringRow, ringRow, ringRow, List.zipWith_append h, List.foldl_append]

theorem take_flatMap_eight (Z : ℕ → List E) (q : ℕ) (hZ : ∀ t < q, (Z t).length = 8)
    (rest : List E) (t : ℕ) (h : t ≤ q) :
    ((List.range q).flatMap Z ++ rest).take (8 * t) = (List.range t).flatMap Z := by
  obtain ⟨q', rfl⟩ : ∃ q', q = t + q' := ⟨q - t, by omega⟩
  have hl : ((List.range t).flatMap Z).length = 8 * t := by
    rw [length_flatMap_range 8 Z t (fun i hi ↦ hZ i (by omega)), Nat.mul_comm]
  rw [List.range_add, List.flatMap_append, List.append_assoc, List.take_append_of_le_length
    (by rw [hl]), List.take_of_length_le (by rw [hl])]

theorem readsAt_mul_gen_pow {rd : Reader} {p : E} {o : ℕ} {xs : List E} :
    ReadsAt rd (p * gen ^ o) xs ↔ ∀ i < xs.length, LoadHolds rd p (o + i) (xs.getD i 0) := by
  constructor
  · intro h i hi
    rw [← loadHolds_mul_gen_pow]
    exact readsAt_getD h hi
  · intro h i hi
    have := h i hi
    rwa [← loadHolds_mul_gen_pow, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some] at this

/-- The honest rows: row `t` is row `0` times the products over the first `8t` coordinates. -/
def rsR (c zs ps : List E) (t k : ℕ) : E := ringRow (c.getD k 0) (zs.take (8 * t)) (ps.take (8 * t)) k

/-- The words of `q` chunks of eight, then one of `r`, read from `z`. -/
theorem readsAt_chunks {rd : Reader} {z : E} {q r : ℕ} (Z : ℕ → List E)
    (hZ : ∀ t < q, (Z t).length = 8) (hZq : (Z q).length = r)
    (hrd : ∀ t < q, ReadsAt rd (z * gen ^ (8 * t)) (Z t))
    (hl : 0 < r → ReadsAt rd (z * gen ^ (8 * q)) (Z q)) :
    ReadsAt rd z ((List.range q).flatMap Z ++ Z q) := by
  have lZ : ((List.range q).flatMap Z).length = 8 * q := by
    rw [length_flatMap_range 8 Z q hZ, Nat.mul_comm]
  intro i hi
  rw [List.length_append, lZ, hZq] at hi
  rw [← List.getD_eq_getElem _ (0 : E)]
  rcases Nat.lt_or_ge i (8 * q) with h | h
  · rw [List.getD_append _ _ _ _ (by rw [lZ]; exact h),
      show i = i / 8 * 8 + i % 8 by omega,
      getD_flatMap_range 8 0 (i / 8) Z q (i % 8) (by omega) (fun j hj ↦ hZ j (by omega))
        (by rw [hZ _ (by omega)]; omega)]
    have := (readsAt_mul_gen_pow.mp (hrd (i / 8) (by omega))) (i % 8)
      (by rw [hZ _ (by omega)]; omega)
    rwa [show 8 * (i / 8) + i % 8 = i / 8 * 8 + i % 8 by ring] at this
  · rw [List.getD_append_right _ _ _ _ (by rw [lZ]; exact h), lZ]
    have := (readsAt_mul_gen_pow.mp (hl (by omega))) (i - 8 * q) (by rw [hZq]; omega)
    rwa [show 8 * q + (i - 8 * q) = i by omega] at this

/-- **The rows from the chunks**: `q` chunks of eight coordinates, then one of `r`. -/
theorem rows_of_chunks {rd : Reader} {chain z p : E} {q r : ℕ} (hr8 : r < 8) (Z P C : ℕ → List E)
    (hZ : ∀ t < q, (Z t).length = 8) (hP : ∀ t < q, (P t).length = 8) (hZq : (Z q).length = r)
    (hPq : (P q).length = r) (hok : ∀ t < q, ChunkOk rd chain z p t (Z t) (P t) (C t))
    (hlast : 0 < r → ChunkOk rd chain z p q (Z q) (P q) (C q)) :
    let zs := (List.range q).flatMap Z ++ Z q
    let ps := (List.range q).flatMap P ++ P q
    let c := (List.range 64).map fun k ↦ (C 0).getD k 0
    zs.length = 8 * q + r ∧ ps.length = 8 * q + r ∧ c.length = 64 ∧ ReadsAt rd z zs ∧
      ReadsAt rd p ps ∧ (0 < 8 * q + r → ReadsAt rd chain c) ∧
      ∀ h, 1 ≤ h → h ≤ (8 * q + r + 7) / 8 → ∀ k < 64,
        LoadHolds rd chain (64 * h + k)
          (ringRow (c.getD k 0) (zs.take (min (8 * h) (8 * q + r)))
            (ps.take (min (8 * h) (8 * q + r))) k) := by
  intro zs ps c
  have lZ : ((List.range q).flatMap Z).length = 8 * q := by
    rw [length_flatMap_range 8 Z q hZ, Nat.mul_comm]
  have lP : ((List.range q).flatMap P).length = 8 * q := by
    rw [length_flatMap_range 8 P q hP, Nat.mul_comm]
  have hzs : zs.length = 8 * q + r := by simp only [zs, List.length_append, lZ, hZq]
  have hps : ps.length = 8 * q + r := by simp only [ps, List.length_append, lP, hPq]
  have hc : c.length = 64 := by simp [c]
  have ex : 0 < q ∨ 0 < r → ∀ t, t ≤ q → (t < q ∨ 0 < r) →
      ChunkOk rd chain z p t (Z t) (P t) (C t) := fun _ t ht h ↦ by
    rcases Nat.lt_or_ge t q with h' | h'
    · exact hok t h'
    · obtain rfl : t = q := by omega
      exact hlast (by omega)
  -- the take of the first `t` chunks
  have tz : ∀ t ≤ q, zs.take (8 * t) = (List.range t).flatMap Z := fun t ht ↦
    take_flatMap_eight Z q hZ (Z q) t ht
  have tp : ∀ t ≤ q, ps.take (8 * t) = (List.range t).flatMap P := fun t ht ↦
    take_flatMap_eight P q hP (P q) t ht
  have rstep : ∀ t < q, ∀ k, rsR c zs ps (t + 1) k = ringRow (rsR c zs ps t k) (Z t) (P t) k := by
    intro t ht k
    rw [rsR, rsR, tz (t + 1) ht, tp (t + 1) ht, tz t ht.le, tp t ht.le, List.range_succ,
      List.flatMap_append, List.flatMap_append, List.flatMap_singleton, List.flatMap_singleton,
      ringRow_append _ _ _ _ _ _ (by rw [length_flatMap_range 8 Z t (fun i hi ↦ hZ i (by omega)),
        length_flatMap_range 8 P t (fun i hi ↦ hP i (by omega))])]
  -- row `t` is what chunk `t` reads
  have hrow : ∀ t ≤ q, (t < q ∨ 0 < r) → ∀ k < 64, (C t).getD k 0 = rsR c zs ps t k := by
    intro t
    induction t with
    | zero =>
      intro _ _ k hk
      rw [rsR, Nat.mul_zero, ringRow_nil]
      simp [c, List.getD_eq_getElem?_getD, hk]
    | succ t ih =>
      intro ht hex k hk
      obtain ⟨-, -, -, -, hst⟩ := hok t (by omega)
      obtain ⟨-, -, hl, hrd, -⟩ := ex (by omega) (t + 1) ht hex
      have a := readsAt_getD hrd (show k < (C (t + 1)).length by omega)
      have b := hst k hk
      rw [ih (by omega) (by omega) k hk, ← rstep t (by omega) k] at b
      rw [loadHolds_mul_gen_pow] at a b
      rw [show 64 * (t + 1) + k = 64 * t + (64 + k) by ring] at a
      exact loadHolds_unique a b
  refine ⟨hzs, hps, hc, fun i hi ↦ ?_, fun i hi ↦ ?_, fun hpos ↦ ?_, fun h h1 h2 k hk ↦ ?_⟩
  · exact readsAt_chunks Z hZ hZq (fun t ht ↦ (hok t ht).1) (fun h ↦ (hlast h).1) i hi
  · exact readsAt_chunks P hP hPq (fun t ht ↦ (hok t ht).2.1) (fun h ↦ (hlast h).2.1) i hi
  · obtain ⟨-, -, hl, hrd, -⟩ := ex (by omega) 0 (Nat.zero_le _) (by omega)
    refine readsAt_range fun k hk ↦ ?_
    have := (readsAt_mul_gen_pow.mp hrd) k (by omega)
    rwa [Nat.mul_zero, Nat.zero_add] at this
  · rcases Nat.lt_or_ge q h with hq | hq
    · -- the remainder's row
      have hr0 : 0 < r := by omega
      obtain rfl : h = q + 1 := by omega
      obtain ⟨-, -, -, -, hst⟩ := hlast hr0
      have b := hst k hk
      rw [hrow q le_rfl (Or.inr hr0) k hk, rsR, tz q le_rfl, tp q le_rfl,
        ← ringRow_append _ _ _ _ _ _ (by rw [lZ, lP]), loadHolds_mul_gen_pow] at b
      rw [min_eq_right (by omega), ← hzs, List.take_length, hzs, ← hps, List.take_length,
        show 64 * (q + 1) + k = 64 * q + (64 + k) by ring]
      exact b
    · obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
      obtain ⟨-, -, -, -, hst⟩ := hok h' (by omega)
      have b := hst k hk
      rw [hrow h' (by omega) (Or.inl (by omega)) k hk, ← rstep h' (by omega) k,
        loadHolds_mul_gen_pow] at b
      rw [min_eq_left (by omega), show 64 * (h' + 1) + k = 64 * h' + (64 + k) by ring]
      exact b

/-! ## The theorem -/

theorem rsNames_get (j : ℕ) (hj : j < 8) :
    ["rs_eq_rows__L0", "rs_eq_rows__L1", "rs_eq_rows__L2", "rs_eq_rows__L3", "rs_eq_rows__L4",
      "rs_eq_rows__L5", "rs_eq_rows__L6", "rs_eq_rows__L7"][j] = rsEqRowsNames.getD j "" := by
  interval_cases j <;> rfl

theorem pow_sq3 (x : E) : (x * x * (x * x)) * (x * x * (x * x)) = x ^ 8 := by ring

/-- A chunk of `n > 0` coordinates from `rs_eq_rows__L{n}`'s meaning. -/
theorem chunk_of_meaning {rd : Reader} {chain z p ret : E} {n t : ℕ} (hn : 0 < n)
    (h : MeaningRsEqRows n rd [chain * gen ^ (64 * t), z * gen ^ (8 * t), p * gen ^ (8 * t)] [ret]) :
    ∃ zt pt ct, zt.length = n ∧ pt.length = n ∧ ChunkOk rd chain z p t zt pt ct ∧
      ret = chain * gen ^ (64 * t) * gen ^ 64 := by
  rcases h with ⟨h0, -⟩ | ⟨-, zt, pt, ct, hz, hp, hc, rz, rp, rc, hst, hret⟩
  · omega
  · simp only [List.cons.injEq, and_true] at hret
    exact ⟨zt, pt, ct, hz, hp, ⟨rz, rp, hc, rc, hst⟩, hret⟩

/-- **`rs_eq_run`'s core IR computes its meaning.** -/
theorem rs_eq_run_sound (rd : Reader) (args rets : List E)
    (h : coreProgram.Rel rd "rs_eq_run" args rets) : MeaningRsEqRun rd args rets := by
  obtain ⟨w3, w5, w17⟩ := rs_consts
  rw [rel_iff_sem find_rs_eq_run, show Fn.params Data.core6 = [.n 0, .n 1, .n 2, .n 3] from rfl,
    core6_body, rsBody] at h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, true_and] at h
  obtain ⟨σ, hp, b0, h10, h11, h12, h13, b1, h14, h15, h16, h17, h18, b2, h19, h20, h21, h22, h23,
    b3, h24, h25, h26, h27, b4, h28, h29, h30, h31, h32, b5, h33, h34, h35, h36, h37, h38, h39,
    h40, h41, ha, h42, h43, h44, hK, hcall, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54,
    h55, h56, ⟨j, hj, hx, hdisp⟩, h58, hret⟩ := h
  subst hp
  have hbr : ∀ j < 3, σ (.n (4 + j)) * σ (.n (4 + j)) = σ (.n (4 + j)) := by
    intro j hj; interval_cases j
    exacts [b0.symm, b1.symm, b2.symm]
  have hbq : ∀ j < 3, σ (.n (7 + j)) * σ (.n (7 + j)) = σ (.n (7 + j)) := by
    intro j hj; interval_cases j
    exacts [b3.symm, b4.symm, b5.symm]
  have rg : σ (.n 23) = ∏ j ∈ Finset.range 3, (1 + σ (.n (4 + j)) * (gen ^ 2 ^ j + 1)) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    rw [h23, h18, h13, h17, h22, h12, h16, h21, h10, h14, h19, h11, h15, h20, w3, w5, w17, word_one]
  have qg : σ (.n 37) = ∏ j ∈ Finset.range 3, (1 + σ (.n (7 + j)) * (gen ^ 2 ^ j + 1)) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    rw [h37, h32, h27, h31, h36, h26, h30, h35, h24, h28, h33, h25, h29, h34, w3, w5, w17, word_one]
  rw [prod_gen_pow_of_bool hbr] at rg
  rw [prod_gen_pow_of_bool hbq] at qg
  set r := bitsVal (fun j ↦ decide (σ (.n (4 + j)) = 1)) 3 with hrdef
  set q := bitsVal (fun j ↦ decide (σ (.n (7 + j)) = 1)) 3 with hqdef
  have hr8 : r < 8 := bitsVal_lt _ 3
  have hq8 : q < 8 := bitsVal_lt _ 3
  have hcg : σ (.n 3) = gen ^ (8 * q + r) := by
    rw [← e_add_eq_zero_iff.mp ha, h41, h40, h39, h38, qg, rg, ← pow_add, ← pow_add, ← pow_add,
      ← pow_add]
    congr 1; ring
  -- the loop over the full chunks
  rw [h43, h42, word_one] at hK hcall
  rw [h44, word_one] at hcall
  obtain ⟨m, hm, hm', hB⟩ := (guarded_loop_rel_iff
    (fun d x ↦ loop5_sound rd (σ (.n 37)) (σ (.n 0)) (σ (.n 1)) (σ (.n 2)) d x)
    (fun x hb hk hn ↦ loop5_complete rd _ _ _ _ x hb hk hn)).mp ⟨hK, hcall⟩
  have hmq : m = q := by
    rw [qg] at hm'
    exact gen_pow_inj hm (by show q < 2 ^ 64 - 1; omega) hm'.symm
  subst hmq
  have hch : ∀ t < q, ∃ zt pt ct, zt.length = 8 ∧ pt.length = 8 ∧
      ChunkOk rd (σ (.n 0)) (σ (.n 1)) (σ (.n 2)) t zt pt ct := fun t ht ↦ by
    obtain ⟨ret, hr⟩ := hB t ht
    rw [← pow_mul, ← pow_mul, Nat.mul_comm t 64, Nat.mul_comm t 8] at hr
    obtain ⟨zt, pt, ct, a, b, c, -⟩ :=
      chunk_of_meaning (by norm_num) ((rs_eq_rows_holds 8 le_rfl rd _ _).1 hr)
    exact ⟨zt, pt, ct, a, b, c⟩
  choose! Zc Pc Cc hZc hPc hCc using hch
  -- the remainder
  have hj' : j = r := by
    rw [rg, gen_pow_eq_ofK] at hx
    exact gen_pow_inj (by simp only [List.length_cons, List.length_nil] at hj; show j < 2 ^ 64 - 1; omega) (by show r < 2 ^ 64 - 1; omega)
      (by rw [gen_pow_eq_ofK, gen_pow_eq_ofK]; exact hx.symm)
  subst hj'
  rw [rsNames_get _ hj] at hdisp
  have e53 : σ (.n 53) = gen ^ (64 * q) := by
    rw [h53, h52, h51, h50, h49, h48, qg]; ring
  have e47 : σ (.n 47) = gen ^ (8 * q) := by rw [h47, h46, h45, qg]; ring
  rw [h54, h55, h56, e53, e47] at hdisp
  have hm8 := (rs_eq_rows_holds r (by omega) rd _ _).1 hdisp
  obtain ⟨Zl, Pl, Cl, hZl, hPl, hl, h57⟩ : ∃ Zl Pl Cl, Zl.length = r ∧ Pl.length = r ∧
      (0 < r → ChunkOk rd (σ (.n 0)) (σ (.n 1)) (σ (.n 2)) q Zl Pl Cl) ∧
      σ (.n 57) = σ (.n 0) * gen ^ (64 * ((8 * q + r + 7) / 8)) := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · rcases hm8 with ⟨-, hr⟩ | ⟨h, -⟩
      · simp only [List.cons.injEq, and_true] at hr
        refine ⟨[], [], [], by simp [h0], by simp [h0], fun h ↦ absurd h (by omega), ?_⟩
        rw [hr, show (8 * q + r + 7) / 8 = q by omega]
      · omega
    · obtain ⟨zt, pt, ct, a, b, c, d⟩ := chunk_of_meaning h0 hm8
      refine ⟨zt, pt, ct, a, b, fun _ ↦ c, ?_⟩
      rw [d, mul_assoc, ← pow_add, show (8 * q + r + 7) / 8 = q + 1 by omega]
      ring_nf
  let Z : ℕ → List E := fun t ↦ if t < q then Zc t else Zl
  let P : ℕ → List E := fun t ↦ if t < q then Pc t else Pl
  let C : ℕ → List E := fun t ↦ if t < q then Cc t else Cl
  obtain ⟨lz, lp, lc, rz, rp, rc, rows⟩ := rows_of_chunks (rd := rd) (chain := σ (.n 0))
    (z := σ (.n 1)) (p := σ (.n 2)) (q := q) (r := r) (by omega) Z P C
    (fun t ht ↦ by simp only [Z, ite_pos' ht]; exact hZc t ht)
    (fun t ht ↦ by simp only [P, ite_pos' ht]; exact hPc t ht)
    (by simp only [Z, ite_neg' (lt_irrefl q)]; exact hZl)
    (by simp only [P, ite_neg' (lt_irrefl q)]; exact hPl)
    (fun t ht ↦ by simp only [Z, P, C, ite_pos' ht]; exact hCc t ht)
    (fun h ↦ by simp only [Z, P, C, ite_neg' (lt_irrefl q)]; exact hl h)
  refine ⟨8 * q + r, by omega, hcg, _, _, _, lz, lp, lc, rz, rp, rc, rows, ?_⟩
  rw [← hret, h58, h57]

end
end LeanVM.Guest.B1
