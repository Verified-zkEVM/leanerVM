/-
  LeanVM.Guest.B1.Eq.RsEqRun

  B1 for `rs_eq_run`: the telescoped ring-switch rows, two coordinates a row.
-/

module

public import LeanVM.Guest.B1.Eq.RsLoop
public import LeanVM.Guest.B1.Bits.GPower

/-!
# `rs_eq_run` (G:895-939, TRIAGE #28)

`rs_eq_run(chain, z_vals, point1, count_g)` hints the six bits of `count` (`count_g = g^count`,
pinned by `half_g² · odd_g = count_g`, `half_g` from bits `1 .. 5`, `odd_g` from bit `0`), runs
`__loop6` over the pairs (`loop6_step`), and when the count is odd (`ite` on `odd + 1`, its
zero branch `rsOdd`) multiplies the last row by the last coordinate's factors; it returns the
last row's pointer.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The template -/

/-- The odd tail's `z` powers. -/
def roz : ℕ → ℕ
  | 0 => 47
  | k + 1 => 60 + 4 * k

/-- The odd tail's row word read at `k`. -/
def row : ℕ → ℕ
  | 0 => 57
  | k + 1 => 61 + 4 * k

/-- The odd tail's coordinate `k`. -/
def roBlk : ℕ → List Stmt
  | 0 => [.atom (.load (.n 57) (.n 56) 0), .atom (.add (.n 58) (.n 47) (.n 49)),
      .atom (.mul (.n 59) (.n 57) (.n 58)), .atom (.load (.n 59) (.n 56) 64)]
  | k + 1 => [.atom (.mul (.n (60 + 4 * k)) (.n (roz k)) (.n (roz k))),
      .atom (.load (.n (61 + 4 * k)) (.n 56) (k + 1)),
      .atom (.add (.n (62 + 4 * k)) (.n (60 + 4 * k)) (.n 49)),
      .atom (.mul (.n (63 + 4 * k)) (.n (61 + 4 * k)) (.n (62 + 4 * k))),
      .atom (.load (.n (63 + 4 * k)) (.n 56) (65 + k))]

/-- The odd tail (`if odd == 1`). -/
def rsOdd : List Stmt :=
  [.atom (.mul (.n 45) (.n 33) (.n 33)), .atom (.mul (.n 46) (.n 1) (.n 45)),
    .atom (.load (.n 47) (.n 46) 0), .atom (.mul (.n 48) (.n 2) (.n 45)),
    .atom (.load (.n 49) (.n 48) 0), .atom (.mul (.n 50) (.n 33) (.n 33)),
    .atom (.mul (.n 51) (.n 50) (.n 50)), .atom (.mul (.n 52) (.n 51) (.n 51)),
    .atom (.mul (.n 53) (.n 52) (.n 52)), .atom (.mul (.n 54) (.n 53) (.n 53)),
    .atom (.mul (.n 55) (.n 54) (.n 54)), .atom (.mul (.n 56) (.n 0) (.n 55))] ++
  ((List.range 64).map roBlk).flatten

/-- The expansion of `rs_eq_run`. -/
def rsBody : List Stmt :=
  [.atom (.hint (.bitsExp (.n 3) 6 (.stack [.n 4, .n 5, .n 6, .n 7, .n 8, .n 9]))),
    .atom (.mul (.n 4) (.n 4) (.n 4)), .atom (.mul (.n 5) (.n 5) (.n 5)),
    .atom (.const (.n 10) (word 1 0 0)), .atom (.const (.n 11) (word 3 0 0)),
    .atom (.mul (.n 12) (.n 5) (.n 11)), .atom (.add (.n 13) (.n 10) (.n 12)),
    .atom (.mul (.n 6) (.n 6) (.n 6)), .atom (.const (.n 14) (word 1 0 0)),
    .atom (.const (.n 15) (word 5 0 0)), .atom (.mul (.n 16) (.n 6) (.n 15)),
    .atom (.add (.n 17) (.n 14) (.n 16)), .atom (.mul (.n 18) (.n 13) (.n 17)),
    .atom (.mul (.n 7) (.n 7) (.n 7)), .atom (.const (.n 19) (word 1 0 0)),
    .atom (.const (.n 20) (word 17 0 0)), .atom (.mul (.n 21) (.n 7) (.n 20)),
    .atom (.add (.n 22) (.n 19) (.n 21)), .atom (.mul (.n 23) (.n 18) (.n 22)),
    .atom (.mul (.n 8) (.n 8) (.n 8)), .atom (.const (.n 24) (word 1 0 0)),
    .atom (.const (.n 25) (word 257 0 0)), .atom (.mul (.n 26) (.n 8) (.n 25)),
    .atom (.add (.n 27) (.n 24) (.n 26)), .atom (.mul (.n 28) (.n 23) (.n 27)),
    .atom (.mul (.n 9) (.n 9) (.n 9)), .atom (.const (.n 29) (word 1 0 0)),
    .atom (.const (.n 30) (word 65537 0 0)), .atom (.mul (.n 31) (.n 9) (.n 30)),
    .atom (.add (.n 32) (.n 29) (.n 31)), .atom (.mul (.n 33) (.n 28) (.n 32)),
    .atom (.const (.n 34) (word 1 0 0)), .atom (.const (.n 35) (word 3 0 0)),
    .atom (.mul (.n 36) (.n 4) (.n 35)), .atom (.add (.n 37) (.n 34) (.n 36)),
    .atom (.mul (.n 38) (.n 33) (.n 33)), .atom (.mul (.n 39) (.n 38) (.n 37)),
    .atom (.assertEq (.n 39) (.n 3)), .atom (.const (.n 40) (word 1 0 0)),
    .atom (.add (.n 41) (.n 40) (.n 33)), .atom (.const (.n 42) (word 1 0 0)),
    .callIf (.n 41) "__loop6" [.n 42, .n 33, .n 1, .n 2, .n 0],
    .atom (.const (.n 43) (word 1 0 0)), .atom (.add (.n 44) (.n 4) (.n 43)),
    .ite (.n 44) rsOdd [],
    .atom (.mul (.n 312) (.n 33) (.n 37)), .atom (.mul (.n 313) (.n 312) (.n 312)),
    .atom (.mul (.n 314) (.n 313) (.n 313)), .atom (.mul (.n 315) (.n 314) (.n 314)),
    .atom (.mul (.n 316) (.n 315) (.n 315)), .atom (.mul (.n 317) (.n 316) (.n 316)),
    .atom (.mul (.n 318) (.n 317) (.n 317)), .atom (.mul (.n 319) (.n 0) (.n 318)),
    .ret [.n 319]]

theorem core5_body : Fn.body Data.core5 = rsBody := stmtsEqb_sound (by decide +kernel)

theorem find_rs_eq_run : coreProgram.find? "rs_eq_run" = some Data.core5 :=
  Program.find?_of_indexOf? (j := 5) (by decide +kernel) rfl

/-! ## The odd tail -/

/-- What the odd tail's coordinate `k` asks. -/
def RoOk (rd : Reader) (σ : Val) : ℕ → Prop
  | 0 => LoadHolds rd (σ (.n 56)) 0 (σ (.n 57)) ∧ σ (.n 58) = σ (.n 47) + σ (.n 49) ∧
      σ (.n 59) = σ (.n 57) * σ (.n 58) ∧ LoadHolds rd (σ (.n 56)) 64 (σ (.n 59))
  | k + 1 => σ (.n (60 + 4 * k)) = σ (.n (roz k)) * σ (.n (roz k)) ∧
      LoadHolds rd (σ (.n 56)) (k + 1) (σ (.n (61 + 4 * k))) ∧
      σ (.n (62 + 4 * k)) = σ (.n (60 + 4 * k)) + σ (.n 49) ∧
      σ (.n (63 + 4 * k)) = σ (.n (61 + 4 * k)) * σ (.n (62 + 4 * k)) ∧
      LoadHolds rd (σ (.n 56)) (65 + k) (σ (.n (63 + 4 * k)))

theorem holds_roBlk {C : CallRel} {rd : Reader} {σ : Val} (k : ℕ) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (roBlk k) True kret ↔ RoOk rd σ k := by
  cases k <;> simp only [roBlk, RoOk, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]

/-- What the odd tail does: the last coordinate's words at `hg²`, and the next row. -/
def OddBody (rd : Reader) (z p chain hg : E) : Prop :=
  ∃ zo qo : E, LoadHolds rd (z * (hg * hg)) 0 zo ∧ LoadHolds rd (p * (hg * hg)) 0 qo ∧
    ∀ k < 64, ∃ w, LoadHolds rd (chain * hg ^ 64) k w ∧
      LoadHolds rd (chain * hg ^ 64) (64 + k) (w * (zo ^ 2 ^ k + qo))

theorem rsOdd_noRet : Stmt.noRetList rsOdd = true := by decide +kernel

theorem holds_rsOdd {C : CallRel} {rd : Reader} {σ : Val} (kret : List E → Prop) :
    Stmt.HoldsList C rd σ rsOdd True kret ↔
      σ (.n 45) = σ (.n 33) * σ (.n 33) ∧ σ (.n 46) = σ (.n 1) * σ (.n 45) ∧
      LoadHolds rd (σ (.n 46)) 0 (σ (.n 47)) ∧ σ (.n 48) = σ (.n 2) * σ (.n 45) ∧
      LoadHolds rd (σ (.n 48)) 0 (σ (.n 49)) ∧ σ (.n 50) = σ (.n 33) * σ (.n 33) ∧
      σ (.n 51) = σ (.n 50) * σ (.n 50) ∧ σ (.n 52) = σ (.n 51) * σ (.n 51) ∧
      σ (.n 53) = σ (.n 52) * σ (.n 52) ∧ σ (.n 54) = σ (.n 53) * σ (.n 53) ∧
      σ (.n 55) = σ (.n 54) * σ (.n 54) ∧ σ (.n 56) = σ (.n 0) * σ (.n 55) ∧
      ∀ k < 64, RoOk rd σ k := by
  rw [rsOdd, holdsList_append, holdsList_range_flatten 64 roBlk (fun k => by cases k <;> rfl)]
  simp only [holds_roBlk, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]

theorem pow_64_eq (x : E) : ((((((x * x) * (x * x)) * ((x * x) * (x * x))) *
    (((x * x) * (x * x)) * ((x * x) * (x * x)))) * ((((x * x) * (x * x)) * ((x * x) * (x * x))) *
    (((x * x) * (x * x)) * ((x * x) * (x * x))))) * (((((x * x) * (x * x)) * ((x * x) * (x * x))) *
    (((x * x) * (x * x)) * ((x * x) * (x * x)))) * ((((x * x) * (x * x)) * ((x * x) * (x * x))) *
    (((x * x) * (x * x)) * ((x * x) * (x * x)))))) = x ^ 64 := by ring

theorem roz_pow {rd : Reader} {σ : Val} (h : ∀ k < 64, RoOk rd σ k) :
    ∀ k < 64, σ (.n (roz k)) = σ (.n 47) ^ 2 ^ k
  | 0, _ => by simp [roz]
  | k + 1, hk => by
    rw [roz, (h (k + 1) hk).1, roz_pow h k (by omega), ← pow_add, ← two_mul, pow_succ, Nat.mul_comm]

theorem rsOdd_sound {rd : Reader} {σ : Val} {kret : List E → Prop}
    (h : Stmt.HoldsList (coreProgram.Rel rd) rd σ rsOdd True kret) :
    OddBody rd (σ (.n 1)) (σ (.n 2)) (σ (.n 0)) (σ (.n 33)) := by
  obtain ⟨h45, h46, l47, h48, l49, h50, h51, h52, h53, h54, h55, h56, hblk⟩ :=
    (holds_rsOdd kret).mp h
  have h56' : σ (.n 56) = σ (.n 0) * σ (.n 33) ^ 64 := by
    rw [h56, h55, h54, h53, h52, h51, h50, pow_64_eq]
  refine ⟨σ (.n 47), σ (.n 49), by rwa [h46, h45] at l47, by rwa [h48, h45] at l49,
    fun k hk => ?_⟩
  rw [← h56']
  cases k with
  | zero =>
    obtain ⟨lw, e58, e59, lo⟩ := hblk 0 hk
    refine ⟨σ (.n 57), lw, ?_⟩
    rw [e59, e58] at lo
    simpa using lo
  | succ k =>
    obtain ⟨e60, lw, e62, e63, lo⟩ := hblk (k + 1) hk
    refine ⟨σ (.n (61 + 4 * k)), lw, ?_⟩
    have hp : σ (.n (roz k)) * σ (.n (roz k)) = σ (.n 47) ^ 2 ^ (k + 1) := by
      rw [roz_pow hblk k (by omega), ← pow_add, ← two_mul, pow_succ, Nat.mul_comm]
    rw [e63, e62, e60, hp, show 65 + k = 64 + (k + 1) by omega] at lo
    exact lo

/-! ## The rows -/

theorem ringRow_take_succ (c : E) (zs ps : List E) (k i : ℕ) (hz : i < zs.length)
    (hp : i < ps.length) :
    ringRow c (zs.take (i + 1)) (ps.take (i + 1)) k =
      ringRow c (zs.take i) (ps.take i) k * (zs[i] ^ 2 ^ k + ps[i]) := by
  rw [ringRow, ringRow, List.take_add_one, List.take_add_one, List.getElem?_eq_getElem hz,
    List.getElem?_eq_getElem hp]
  simp only [Option.toList_some]
  rw [List.zipWith_append (by simp; omega), List.foldl_append]
  rfl

theorem ringRow_nil (c : E) (zs ps : List E) (k : ℕ) : ringRow c (zs.take 0) (ps.take 0) k = c := by
  simp [ringRow]

theorem load_gen_pow_sq {rd : Reader} {q w : E} {j o : ℕ}
    (h : LoadHolds rd (q * (gen ^ j * gen ^ j)) o w) : LoadHolds rd q (2 * j + o) w := by
  rwa [← pow_add, ← two_mul, loadHolds_mul_gen_pow] at h

theorem load_gen_pow_64 {rd : Reader} {q w : E} {j o : ℕ}
    (h : LoadHolds rd (q * (gen ^ j) ^ 64) o w) : LoadHolds rd q (64 * j + o) w := by
  rwa [← pow_mul, Nat.mul_comm, loadHolds_mul_gen_pow] at h

/-- **The rows from the loop's and the odd tail's bodies.** -/
theorem rows_of_bodies {rd : Reader} {z p chain : E} {H O : ℕ} (hO : O ≤ 1)
    (hB : ∀ j < H, Loop6Body rd z p chain (gen ^ j))
    (hOdd : O = 1 → OddBody rd z p chain (gen ^ H)) :
    ∃ zs ps c : List E, zs.length = 2 * H + O ∧ ps.length = 2 * H + O ∧ c.length = 64 ∧
      ReadsAt rd z zs ∧ ReadsAt rd p ps ∧ (0 < 2 * H + O → ReadsAt rd chain c) ∧
      (∀ h, 1 ≤ h → h ≤ (2 * H + O + 1) / 2 → ∀ k < 64,
        LoadHolds rd chain (64 * h + k)
          (ringRow (c.getD k 0) (zs.take (min (2 * h) (2 * H + O)))
            (ps.take (min (2 * h) (2 * H + O))) k)) := by
  classical
  choose! Z0 Z1 Q0 Q1 hZ0 hZ1 hQ0 hQ1 hW using hB
  choose! W hW1 hW2 using hW
  obtain ⟨zo, qo, Wo, hzo, hqo, hWo1, hWo2⟩ : ∃ (zo qo : E) (Wo : ℕ → E),
      (O = 1 → LoadHolds rd (z * (gen ^ H * gen ^ H)) 0 zo) ∧
      (O = 1 → LoadHolds rd (p * (gen ^ H * gen ^ H)) 0 qo) ∧
      (O = 1 → ∀ k < 64, LoadHolds rd (chain * (gen ^ H) ^ 64) k (Wo k)) ∧
      (O = 1 → ∀ k < 64, LoadHolds rd (chain * (gen ^ H) ^ 64) (64 + k)
        (Wo k * (zo ^ 2 ^ k + qo))) := by
    by_cases h1 : O = 1
    · obtain ⟨zo, qo, a, b, hw⟩ := hOdd h1
      choose! Wo hWo using hw
      exact ⟨zo, qo, Wo, fun _ => a, fun _ => b, fun _ k hk => (hWo k hk).1,
        fun _ k hk => (hWo k hk).2⟩
    · exact ⟨0, 0, fun _ => 0, fun h => absurd h h1, fun h => absurd h h1, fun h => absurd h h1,
        fun h => absurd h h1⟩
  let zf : ℕ → E := fun i => if i < 2 * H then (if i % 2 = 0 then Z0 (i / 2) else Z1 (i / 2)) else zo
  let pf : ℕ → E := fun i => if i < 2 * H then (if i % 2 = 0 then Q0 (i / 2) else Q1 (i / 2)) else qo
  let cf : ℕ → E := fun k => if 0 < H then W 0 k else Wo k
  refine ⟨(List.range (2 * H + O)).map zf, (List.range (2 * H + O)).map pf,
    (List.range 64).map cf, by simp, by simp, by simp, fun i hi => ?_, fun i hi => ?_,
    fun hc k hk => ?_, ?_⟩
  · simp only [List.length_map, List.length_range] at hi
    simp only [List.getElem_map, List.getElem_range, zf]
    by_cases h2 : i < 2 * H
    · rw [ite_T h2]
      rcases Nat.mod_two_eq_zero_or_one i with he | he
      · rw [ite_T he]
        have := load_gen_pow_sq (hZ0 (i / 2) (by omega))
        rwa [show 2 * (i / 2) + 0 = i by omega] at this
      · rw [ite_F (by omega)]
        have := load_gen_pow_sq (hZ1 (i / 2) (by omega))
        rwa [show 2 * (i / 2) + 1 = i by omega] at this
    · rw [ite_F h2]
      have := load_gen_pow_sq (hzo (by omega))
      rwa [show 2 * H + 0 = i by omega] at this
  · simp only [List.length_map, List.length_range] at hi
    simp only [List.getElem_map, List.getElem_range, pf]
    by_cases h2 : i < 2 * H
    · rw [ite_T h2]
      rcases Nat.mod_two_eq_zero_or_one i with he | he
      · rw [ite_T he]
        have := load_gen_pow_sq (hQ0 (i / 2) (by omega))
        rwa [show 2 * (i / 2) + 0 = i by omega] at this
      · rw [ite_F (by omega)]
        have := load_gen_pow_sq (hQ1 (i / 2) (by omega))
        rwa [show 2 * (i / 2) + 1 = i by omega] at this
    · rw [ite_F h2]
      have := load_gen_pow_sq (hqo (by omega))
      rwa [show 2 * H + 0 = i by omega] at this
  · simp only [List.length_map, List.length_range] at hk
    simp only [List.getElem_map, List.getElem_range, cf]
    by_cases h0 : 0 < H
    · rw [ite_T h0]
      simpa using load_gen_pow_64 (j := 0) (hW1 0 h0 k hk)
    · rw [ite_F h0]
      have hH : H = 0 := by omega
      subst hH
      simpa using load_gen_pow_64 (j := 0) (hWo1 (by omega) k hk)
  · obtain ⟨zs, hzs⟩ : ∃ zs, zs = (List.range (2 * H + O)).map zf := ⟨_, rfl⟩
    obtain ⟨ps, hps⟩ : ∃ ps, ps = (List.range (2 * H + O)).map pf := ⟨_, rfl⟩
    rw [← hzs, ← hps]
    have lz : zs.length = 2 * H + O := by rw [hzs]; simp
    have lp : ps.length = 2 * H + O := by rw [hps]; simp
    have gz : ∀ i (hi : i < zs.length), zs[i] = zf i := fun i hi => by subst hzs; simp
    have gp : ∀ i (hi : i < ps.length), ps[i] = pf i := fun i hi => by subst hps; simp
    have gc : ∀ k < 64, ((List.range 64).map cf).getD k 0 = cf k := fun k hk => by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]; rfl
    have z0 : ∀ h < H, zf (2 * h) = Z0 h := fun h hh => by
      simp only [zf, ite_T (show 2 * h < 2 * H by omega), ite_T (show 2 * h % 2 = 0 by omega),
        show 2 * h / 2 = h by omega]
    have z1 : ∀ h < H, zf (2 * h + 1) = Z1 h := fun h hh => by
      simp only [zf, ite_T (show 2 * h + 1 < 2 * H by omega),
        ite_F (show ¬ (2 * h + 1) % 2 = 0 by omega), show (2 * h + 1) / 2 = h by omega]
    have p0 : ∀ h < H, pf (2 * h) = Q0 h := fun h hh => by
      simp only [pf, ite_T (show 2 * h < 2 * H by omega), ite_T (show 2 * h % 2 = 0 by omega),
        show 2 * h / 2 = h by omega]
    have p1 : ∀ h < H, pf (2 * h + 1) = Q1 h := fun h hh => by
      simp only [pf, ite_T (show 2 * h + 1 < 2 * H by omega),
        ite_F (show ¬ (2 * h + 1) % 2 = 0 by omega), show (2 * h + 1) / 2 = h by omega]
    have rowsH : 0 < H → ∀ h ≤ H, ∀ k < 64, LoadHolds rd chain (64 * h + k)
        (ringRow (cf k) (zs.take (2 * h)) (ps.take (2 * h)) k) := by
      intro hH h hh
      induction h with
      | zero =>
        intro k hk
        rw [ringRow_nil]
        have := load_gen_pow_64 (j := 0) (hW1 0 hH k hk)
        simp only [cf, ite_T hH]
        simpa using this
      | succ h ih =>
        intro k hk
        have e1 := loadHolds_unique (load_gen_pow_64 (hW1 h (by omega) k hk)) (ih (by omega) k hk)
        have e2 := load_gen_pow_64 (hW2 h (by omega) k hk)
        rw [e1] at e2
        have r1 := ringRow_take_succ (cf k) zs ps k (2 * h) (by omega) (by omega)
        have r2 := ringRow_take_succ (cf k) zs ps k (2 * h + 1) (by omega) (by omega)
        rw [gz _ (by omega), gp _ (by omega), z0 h (by omega), p0 h (by omega)] at r1
        rw [gz _ (by omega), gp _ (by omega), z1 h (by omega), p1 h (by omega)] at r2
        rw [show 2 * (h + 1) = 2 * h + 1 + 1 by omega, r2, r1,
          show 64 * (h + 1) + k = 64 * h + (64 + k) by ring]
        exact e2
    intro h h1 h2 k hk
    rw [gc k hk]
    by_cases hh : h ≤ H
    · rw [min_eq_left (by omega)]
      exact rowsH (by omega) h hh k hk
    · have hO1 : O = 1 := by omega
      have hh' : h = H + 1 := by omega
      subst hh'
      rw [min_eq_right (by omega), show 2 * H + O = 2 * H + 1 by omega]
      have hrowH : LoadHolds rd chain (64 * H + k)
          (ringRow (cf k) (zs.take (2 * H)) (ps.take (2 * H)) k) := by
        by_cases hH : 0 < H
        · exact rowsH hH H le_rfl k hk
        · have : H = 0 := by omega
          subst this
          rw [ringRow_nil]
          have := load_gen_pow_64 (j := 0) (hWo1 hO1 k hk)
          simp only [cf, ite_F hH]
          simpa using this
      have e1 := loadHolds_unique (load_gen_pow_64 (hWo1 hO1 k hk)) hrowH
      have e2 := load_gen_pow_64 (hWo2 hO1 k hk)
      rw [e1] at e2
      have r1 := ringRow_take_succ (cf k) zs ps k (2 * H) (by omega) (by omega)
      have ez : zf (2 * H) = zo := by simp only [zf, ite_F (show ¬ 2 * H < 2 * H by omega)]
      have ep : pf (2 * H) = qo := by simp only [pf, ite_F (show ¬ 2 * H < 2 * H by omega)]
      rw [gz _ (by omega), gp _ (by omega), ez, ep] at r1
      rw [r1, show 64 * (H + 1) + k = 64 * H + (64 + k) by ring]
      exact e2

end
end LeanVM.Guest.B1
