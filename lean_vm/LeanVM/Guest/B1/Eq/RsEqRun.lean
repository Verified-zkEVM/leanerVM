/-
  LeanVM.Guest.B1.Eq.RsEqRun

  B1 for `rs_eq_run`: the telescoped ring-switch rows, two coordinates a row.
-/

module

public import LeanVM.Guest.B1.Eq.RsLoop
public import LeanVM.Guest.B1.Bits.GPower

/-!
# `rs_eq_run` (G:888-932, TRIAGE #28)

`rs_eq_run(chain, z_vals, point1, count_g)` hints the six bits of `count` (`count_g = g^count`,
pinned by `half_g² · odd_g = count_g`, `half_g` from bits `1 .. 5`, `odd_g` from bit `0`), runs
`__loop5` over the pairs (`loop6_step`), and when the count is odd (`ite` on `odd + 1`, its
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
    .callIf (.n 41) "__loop5" [.n 42, .n 33, .n 1, .n 2, .n 0],
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

theorem load_gen_pow_sq' {rd : Reader} {q w : E} {j o : ℕ} (h : LoadHolds rd q (2 * j + o) w) :
    LoadHolds rd (q * (gen ^ j * gen ^ j)) o w := by
  rwa [← pow_add, ← two_mul, loadHolds_mul_gen_pow]

theorem load_gen_pow_64' {rd : Reader} {q w : E} {j o : ℕ} (h : LoadHolds rd q (64 * j + o) w) :
    LoadHolds rd (q * (gen ^ j) ^ 64) o w := by
  rw [← pow_mul, show j * 64 = 64 * j from Nat.mul_comm _ _, loadHolds_mul_gen_pow]
  exact h

/-- **The loop's and the odd tail's bodies from the rows.** -/
theorem bodies_of_rows {rd : Reader} {z p chain : E} {H O : ℕ} (hO : O ≤ 1) {zs ps c : List E}
    (lz : zs.length = 2 * H + O) (lp : ps.length = 2 * H + O) (lc : c.length = 64)
    (hz : ReadsAt rd z zs) (hp : ReadsAt rd p ps) (hc : 0 < 2 * H + O → ReadsAt rd chain c)
    (hr : ∀ h, 1 ≤ h → h ≤ (2 * H + O + 1) / 2 → ∀ k < 64,
        LoadHolds rd chain (64 * h + k)
          (ringRow (c.getD k 0) (zs.take (min (2 * h) (2 * H + O)))
            (ps.take (min (2 * h) (2 * H + O))) k)) :
    (∀ j < H, Loop6Body rd z p chain (gen ^ j)) ∧ (O = 1 → OddBody rd z p chain (gen ^ H)) := by
  have row : ∀ j, j ≤ H → 0 < 2 * H + O → ∀ k < 64, LoadHolds rd chain (64 * j + k)
      (ringRow (c.getD k 0) (zs.take (2 * j)) (ps.take (2 * j)) k) := by
    intro j hj hpos k hk
    cases j with
    | zero =>
      rw [ringRow_nil, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
        Option.getD_some]
      simpa using hc hpos k (by omega)
    | succ j =>
      have := hr (j + 1) (by omega) (by omega) k hk
      rwa [min_eq_left (by omega)] at this
  constructor
  · intro j hj
    have i0 : 2 * j < zs.length := by omega
    have i1 : 2 * j + 1 < zs.length := by omega
    have j0 : 2 * j < ps.length := by omega
    have j1 : 2 * j + 1 < ps.length := by omega
    have a0 : LoadHolds rd z (2 * j + 0) zs[2 * j] := hz (2 * j) i0
    have a1 : LoadHolds rd z (2 * j + 1) zs[2 * j + 1] := hz (2 * j + 1) i1
    have b0 : LoadHolds rd p (2 * j + 0) ps[2 * j] := hp (2 * j) j0
    have b1 : LoadHolds rd p (2 * j + 1) ps[2 * j + 1] := hp (2 * j + 1) j1
    refine ⟨zs[2 * j], zs[2 * j + 1], ps[2 * j], ps[2 * j + 1], load_gen_pow_sq' a0,
      load_gen_pow_sq' a1, load_gen_pow_sq' b0, load_gen_pow_sq' b1, fun k hk => ?_⟩
    refine ⟨_, load_gen_pow_64' (row j (by omega) (by omega) k hk), load_gen_pow_64' ?_⟩
    have := hr (j + 1) (by omega) (by omega) k hk
    rw [min_eq_left (by omega), show 2 * (j + 1) = 2 * j + 1 + 1 by omega,
      ringRow_take_succ _ _ _ _ _ i1 j1, ringRow_take_succ _ _ _ _ _ i0 j0] at this
    rwa [show 64 * (j + 1) + k = 64 * j + (64 + k) by ring] at this
  · intro hO1
    have i0 : 2 * H < zs.length := by omega
    have j0 : 2 * H < ps.length := by omega
    have a0 : LoadHolds rd z (2 * H + 0) zs[2 * H] := hz (2 * H) i0
    have b0 : LoadHolds rd p (2 * H + 0) ps[2 * H] := hp (2 * H) j0
    refine ⟨zs[2 * H], ps[2 * H], load_gen_pow_sq' a0, load_gen_pow_sq' b0, fun k hk => ?_⟩
    refine ⟨_, load_gen_pow_64' (row H le_rfl (by omega) k hk), load_gen_pow_64' ?_⟩
    have := hr (H + 1) (by omega) (by omega) k hk
    rw [min_eq_right (by omega), show 2 * H + O = 2 * H + 1 by omega,
      ringRow_take_succ _ _ _ _ _ i0 j0] at this
    rwa [show 64 * (H + 1) + k = 64 * H + (64 + k) by ring] at this

/-! ## The theorem -/

theorem rs_consts : word 3 0 0 = gen ^ 2 ^ 0 + 1 ∧ word 5 0 0 = gen ^ 2 ^ 1 + 1 ∧
    word 17 0 0 = gen ^ 2 ^ 2 + 1 ∧ word 257 0 0 = gen ^ 2 ^ 3 + 1 ∧
    word 65537 0 0 = gen ^ 2 ^ 4 + 1 :=
  ⟨word_gpow_one 0 (by norm_num) 3 (by decide), word_gpow_one 1 (by norm_num) 5 (by decide),
    word_gpow_one 2 (by norm_num) 17 (by decide), word_gpow_one 3 (by norm_num) 257 (by decide),
    word_gpow_one 4 (by norm_num) 65537 (by decide)⟩

/-! ## The honest values -/

/-- `n` squarings. -/
def sqn : ℕ → E → E
  | 0, x => x
  | n + 1, x => sqn n x * sqn n x

theorem sqn_eq (n : ℕ) (x : E) : sqn n x = x ^ 2 ^ n := by
  induction n with
  | zero => simp [sqn]
  | succ n ih => rw [sqn, ih, ← pow_add, ← two_mul, pow_succ, Nat.mul_comm]

/-- The bits' factors. -/
def rsF (count : ℕ) (j c : ℕ) : E := word 1 0 0 + bitE (count.testBit j) * word c 0 0

/-- `half_g`, as the guest computes it. -/
def rsHg (count : ℕ) : E :=
  rsF count 1 3 * rsF count 2 5 * rsF count 3 17 * rsF count 4 257 * rsF count 5 65537

theorem rsHg_eq (count : ℕ) (h : count < 64) : rsHg count = gen ^ (count / 2) := by
  obtain ⟨w3, w5, w17, w257, w65537⟩ := rs_consts
  have hp := prod_bitE_gen_pow (fun j => (count / 2).testBit j) 5
  rw [bitsVal_testBit (by omega)] at hp
  rw [← hp]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, Nat.testBit_div_two]
  rw [rsHg, rsF, rsF, rsF, rsF, rsF, w3, w5, w17, w257, w65537, word_one]

theorem rsOg_eq (count : ℕ) : rsF count 0 3 = gen ^ (count % 2) := by
  obtain ⟨w3, -⟩ := rs_consts
  rw [rsF, w3, word_one]
  by_cases h : count % 2 = 1
  · have hb : count.testBit 0 = true := by simp [Nat.testBit_zero, h]
    rw [hb, h, bitE, ite_T rfl, one_mul, pow_zero, pow_one]
    calc (1 : E) + (gen + 1) = gen + (1 + 1) := by ring
      _ = gen := by rw [e_add_self, add_zero]
  · have hb : count.testBit 0 = false := by simp [Nat.testBit_zero, h]
    rw [hb, show count % 2 = 0 by omega, bitE]
    simp

/-- The honest values of `rs_eq_run`. -/
def rsVals (chain z p : E) (count : ℕ) (zo qo : E) (Wo : ℕ → E) (i : ℕ) : E :=
  let b := fun j => bitE (count.testBit j)
  let w := fun c => word c 0 0
  let hg := rsHg count
  let og := rsF count 0 3
  if i < 45 then
    [chain, z, p, gen ^ count, b 0, b 1, b 2, b 3, b 4, b 5,
      w 1, w 3, b 1 * w 3, rsF count 1 3,
      w 1, w 5, b 2 * w 5, rsF count 2 5, rsF count 1 3 * rsF count 2 5,
      w 1, w 17, b 3 * w 17, rsF count 3 17, rsF count 1 3 * rsF count 2 5 * rsF count 3 17,
      w 1, w 257, b 4 * w 257, rsF count 4 257,
      rsF count 1 3 * rsF count 2 5 * rsF count 3 17 * rsF count 4 257,
      w 1, w 65537, b 5 * w 65537, rsF count 5 65537, hg,
      w 1, w 3, b 0 * w 3, og, hg * hg, hg * hg * og,
      w 1, w 1 + hg, w 1, w 1, b 0 + w 1].getD i 0
  else if i < 57 then
    [hg * hg, z * (hg * hg), zo, p * (hg * hg), qo, sqn 1 hg, sqn 2 hg, sqn 3 hg, sqn 4 hg,
      sqn 5 hg, sqn 6 hg, chain * sqn 6 hg].getD (i - 45) 0
  else if i < 60 then [Wo 0, zo + qo, Wo 0 * (zo + qo)].getD (i - 57) 0
  else if i < 312 then
    let k := (i - 60) / 4 + 1
    match (i - 60) % 4 with
    | 0 => zo ^ 2 ^ k
    | 1 => Wo k
    | 2 => zo ^ 2 ^ k + qo
    | _ => Wo k * (zo ^ 2 ^ k + qo)
  else [hg * og, sqn 1 (hg * og), sqn 2 (hg * og), sqn 3 (hg * og), sqn 4 (hg * og),
    sqn 5 (hg * og), sqn 6 (hg * og), chain * sqn 6 (hg * og)].getD (i - 312) 0

theorem rsVals_blk (chain z p : E) (count : ℕ) (zo qo : E) (Wo : ℕ → E) (k : ℕ) (hk : k < 63) :
    let v := rsVals chain z p count zo qo Wo
    v (60 + 4 * k) = zo ^ 2 ^ (k + 1) ∧ v (61 + 4 * k) = Wo (k + 1) ∧
      v (62 + 4 * k) = zo ^ 2 ^ (k + 1) + qo ∧
      v (63 + 4 * k) = Wo (k + 1) * (zo ^ 2 ^ (k + 1) + qo) := by
  intro v
  simp only [v, rsVals]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [ite_F (by omega), ite_F (by omega), ite_F (by omega),
    ite_T (by omega)]
  · rw [show (60 + 4 * k - 60) % 4 = 0 by omega, show (60 + 4 * k - 60) / 4 = k by omega]; rfl
  · rw [show (61 + 4 * k - 60) % 4 = 1 by omega, show (61 + 4 * k - 60) / 4 = k by omega]; rfl
  · rw [show (62 + 4 * k - 60) % 4 = 2 by omega, show (62 + 4 * k - 60) / 4 = k by omega]; rfl
  · rw [show (63 + 4 * k - 60) % 4 = 3 by omega, show (63 + 4 * k - 60) / 4 = k by omega]; rfl

/-- The body's relation, the `ite` pulled out. -/
theorem rs_unfold (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "rs_eq_run" args rets ↔ ∃ σ : Val,
      [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3)] = args ∧
      σ (.n 4) = σ (.n 4) * σ (.n 4) ∧ σ (.n 5) = σ (.n 5) * σ (.n 5) ∧
      σ (.n 10) = word 1 0 0 ∧ σ (.n 11) = word 3 0 0 ∧ σ (.n 12) = σ (.n 5) * σ (.n 11) ∧
      σ (.n 13) = σ (.n 10) + σ (.n 12) ∧ σ (.n 6) = σ (.n 6) * σ (.n 6) ∧
      σ (.n 14) = word 1 0 0 ∧ σ (.n 15) = word 5 0 0 ∧ σ (.n 16) = σ (.n 6) * σ (.n 15) ∧
      σ (.n 17) = σ (.n 14) + σ (.n 16) ∧ σ (.n 18) = σ (.n 13) * σ (.n 17) ∧
      σ (.n 7) = σ (.n 7) * σ (.n 7) ∧ σ (.n 19) = word 1 0 0 ∧ σ (.n 20) = word 17 0 0 ∧
      σ (.n 21) = σ (.n 7) * σ (.n 20) ∧ σ (.n 22) = σ (.n 19) + σ (.n 21) ∧
      σ (.n 23) = σ (.n 18) * σ (.n 22) ∧ σ (.n 8) = σ (.n 8) * σ (.n 8) ∧
      σ (.n 24) = word 1 0 0 ∧ σ (.n 25) = word 257 0 0 ∧ σ (.n 26) = σ (.n 8) * σ (.n 25) ∧
      σ (.n 27) = σ (.n 24) + σ (.n 26) ∧ σ (.n 28) = σ (.n 23) * σ (.n 27) ∧
      σ (.n 9) = σ (.n 9) * σ (.n 9) ∧ σ (.n 29) = word 1 0 0 ∧ σ (.n 30) = word 65537 0 0 ∧
      σ (.n 31) = σ (.n 9) * σ (.n 30) ∧ σ (.n 32) = σ (.n 29) + σ (.n 31) ∧
      σ (.n 33) = σ (.n 28) * σ (.n 32) ∧ σ (.n 34) = word 1 0 0 ∧ σ (.n 35) = word 3 0 0 ∧
      σ (.n 36) = σ (.n 4) * σ (.n 35) ∧ σ (.n 37) = σ (.n 34) + σ (.n 36) ∧
      σ (.n 38) = σ (.n 33) * σ (.n 33) ∧ σ (.n 39) = σ (.n 38) * σ (.n 37) ∧
      σ (.n 39) + σ (.n 3) = 0 ∧ σ (.n 40) = word 1 0 0 ∧ σ (.n 41) = σ (.n 40) + σ (.n 33) ∧
      σ (.n 42) = word 1 0 0 ∧
      IsInK (σ (.n 41)) ∧ (σ (.n 41) ≠ 0 → coreProgram.Rel rd "__loop5"
        [σ (.n 42), σ (.n 33), σ (.n 1), σ (.n 2), σ (.n 0)] []) ∧
      σ (.n 43) = word 1 0 0 ∧ σ (.n 44) = σ (.n 4) + σ (.n 43) ∧
      (IsInK (σ (.n 44)) ∧ (σ (.n 44) = 0 →
        Stmt.HoldsList (coreProgram.Rel rd) rd σ rsOdd True (fun rs => rs = rets))) ∧
      σ (.n 312) = σ (.n 33) * σ (.n 37) ∧ σ (.n 313) = σ (.n 312) * σ (.n 312) ∧
      σ (.n 314) = σ (.n 313) * σ (.n 313) ∧ σ (.n 315) = σ (.n 314) * σ (.n 314) ∧
      σ (.n 316) = σ (.n 315) * σ (.n 315) ∧ σ (.n 317) = σ (.n 316) * σ (.n 316) ∧
      σ (.n 318) = σ (.n 317) * σ (.n 317) ∧ σ (.n 319) = σ (.n 0) * σ (.n 318) ∧
      [σ (.n 319)] = rets := by
  rw [rel_iff_sem find_rs_eq_run, show Fn.params Data.core5 = [.n 0, .n 1, .n 2, .n 3] from rfl,
    core5_body, rsBody]
  simp only [Stmt.HoldsList]
  simp only [holds_ite_noRet (.n 44) rsOdd [] rsOdd_noRet rfl]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, true_and,
    and_true, implies_true]

/-- **`rs_eq_run`'s core IR is its meaning.** -/
theorem rs_eq_run_holds : rs_eq_run_Spec := by
  intro rd args rets
  obtain ⟨w3, w5, w17, w257, w65537⟩ := rs_consts
  rw [rs_unfold]
  constructor
  · rintro ⟨σ, hp, b0, b1, h10, h11, h12, h13, b2, h14, h15, h16, h17, h18, b3, h19, h20, h21,
      h22, h23, b4, h24, h25, h26, h27, h28, b5, h29, h30, h31, h32, h33, h34, h35, h36, h37,
      h38, h39, ha, h40, h41, h42, hK, hcall, h43, h44, ⟨-, hodd⟩, h312, h313, h314, h315,
      h316, h317, h318, h319, hret⟩
    subst hp
    have hbH : ∀ j < 5, σ (.n (5 + j)) * σ (.n (5 + j)) = σ (.n (5 + j)) := by
      intro j hj
      interval_cases j
      exacts [b1.symm, b2.symm, b3.symm, b4.symm, b5.symm]
    have hg : σ (.n 33) = ∏ j ∈ Finset.range 5, (1 + σ (.n (5 + j)) * (gen ^ 2 ^ j + 1)) := by
      simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
      rw [h33, h28, h23, h18, h13, h17, h22, h27, h32, h12, h16, h21, h26, h31, h10, h14, h19,
        h24, h29, h11, h15, h20, h25, h30, w3, w5, w17, w257, w65537, word_one]
    rw [prod_gen_pow_of_bool hbH] at hg
    set H := bitsVal (fun j => decide (σ (.n (5 + j)) = 1)) 5 with hHdef
    have hH : H < 2 ^ 5 := bitsVal_lt _ 5
    have hb0 : ∀ j < 1, σ (.n (4 + j)) * σ (.n (4 + j)) = σ (.n (4 + j)) := by
      intro j hj
      interval_cases j
      exact b0.symm
    have og : σ (.n 37) = ∏ j ∈ Finset.range 1, (1 + σ (.n (4 + j)) * (gen ^ 2 ^ j + 1)) := by
      simp only [Finset.prod_range_one]
      rw [h37, h36, h34, h35, w3, word_one]
    rw [prod_gen_pow_of_bool hb0] at og
    set O := bitsVal (fun j => decide (σ (.n (4 + j)) = 1)) 1 with hOdef
    have hO : O < 2 ^ 1 := bitsVal_lt _ 1
    have hcg : σ (.n 3) = gen ^ (2 * H + O) := by
      rw [← e_add_eq_zero_iff.mp ha, h39, h38, hg, og, ← pow_add, ← pow_add, two_mul]
    rw [h41, h40, word_one] at hK hcall
    rw [h42, word_one] at hcall
    obtain ⟨m, hm, hm', hB⟩ := (guarded_loop_iff (fun d x => loop6_step rd (σ (.n 33)) (σ (.n 1))
      (σ (.n 2)) (σ (.n 0)) d x)).mp ⟨hK, hcall⟩
    have hmH : m = H := by
      rw [hg] at hm'
      exact gen_pow_inj hm (by omega) hm'.symm
    subst hmH
    have hodd' : O = 1 → OddBody rd (σ (.n 1)) (σ (.n 2)) (σ (.n 0)) (gen ^ H) := by
      intro hO1
      have h4 : σ (.n 4) = 1 := by
        have := bitE_of_mul_self b0.symm
        by_contra hne
        have : O = 0 := by
          rw [hOdef]; simp [bitsVal, hne]
        omega
      rw [← hg]
      exact rsOdd_sound (hodd (by rw [h44, h43, h4, word_one]; exact e_add_self 1))
    obtain ⟨zs, ps, c, lz, lp, lc, hz, hpp, hc, hr⟩ := rows_of_bodies (by omega) hB hodd'
    refine ⟨2 * H + O, by omega, hcg, zs, ps, c, lz, lp, lc, hz, hpp, hc, hr, ?_⟩
    have e318 : σ (.n 318) = σ (.n 312) ^ 64 := by
      rw [h318, h317, h316, h315, h314, h313]; ring
    rw [← hret, h319, e318, h312, hg, og, ← pow_add, ← pow_mul,
      show (2 * H + O + 1) / 2 = H + O by omega, Nat.mul_comm]
  · intro hm
    obtain ⟨chain, z, p, cg, rfl⟩ : ∃ chain z p cg, args = [chain, z, p, cg] := by
      match args, hm with
      | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩
    obtain ⟨count, hcount, rfl, zs, ps, c, lz, lp, lc, hz, hpp, hc, hr, rfl⟩ := hm
    obtain ⟨H, O, hO, hHO⟩ : ∃ H O, O ≤ 1 ∧ count = 2 * H + O :=
      ⟨count / 2, count % 2, by omega, by omega⟩
    have hH : count / 2 = H := by omega
    have hO' : count % 2 = O := by omega
    rw [hHO] at lz lp hc hr
    obtain ⟨hB, hOdd⟩ := bodies_of_rows hO lz lp lc hz hpp hc hr
    obtain ⟨hK, hcall⟩ := (guarded_loop_iff (fun d x => loop6_step rd (gen ^ H) z p chain d x)).mpr
      ⟨H, by show H < 2 ^ 64 - 1; omega, rfl, hB⟩
    obtain ⟨zo, qo, Wo, hzo, hqo, hWo⟩ : ∃ (zo qo : E) (Wo : ℕ → E),
        (O = 1 → LoadHolds rd (z * (gen ^ H * gen ^ H)) 0 zo) ∧
        (O = 1 → LoadHolds rd (p * (gen ^ H * gen ^ H)) 0 qo) ∧
        (O = 1 → ∀ k < 64, LoadHolds rd (chain * (gen ^ H) ^ 64) k (Wo k) ∧
          LoadHolds rd (chain * (gen ^ H) ^ 64) (64 + k) (Wo k * (zo ^ 2 ^ k + qo))) := by
      by_cases h1 : O = 1
      · obtain ⟨zo, qo, a, b, hw⟩ := hOdd h1
        choose! Wo hWo using hw
        exact ⟨zo, qo, Wo, fun _ => a, fun _ => b, fun _ => hWo⟩
      · exact ⟨0, 0, fun _ => 0, fun h => absurd h h1, fun h => absurd h h1, fun h => absurd h h1⟩
    have hg := rsHg_eq count hcount
    have og := rsOg_eq count
    rw [hH] at hg
    rw [hO'] at og
    let σ : Val := fun v => rsVals chain z p count zo qo Wo v.idx
    have ev : ∀ i, σ (.n i) = rsVals chain z p count zo qo Wo i := fun _ => rfl
    have e33 : σ (.n 33) = gen ^ H := by rw [ev, ← hg]; simp [rsVals]
    have e37 : σ (.n 37) = gen ^ O := by rw [ev, ← og]; simp [rsVals]
    refine ⟨σ, rfl, ?_⟩
    refine ⟨(bitE_mul_self _).symm, (bitE_mul_self _).symm, rfl, rfl, rfl, rfl, (bitE_mul_self
      _).symm, rfl, rfl, rfl, rfl, rfl, (bitE_mul_self _).symm, rfl, rfl, rfl, rfl, rfl,
      (bitE_mul_self _).symm, rfl, rfl, rfl, rfl, rfl, (bitE_mul_self _).symm, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl, ?_, ?_, rfl, rfl, ?_, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    · rw [e_add_eq_zero_iff, show σ (.n 39) = σ (.n 33) * σ (.n 33) * σ (.n 37) from rfl, e33, e37,
        ← pow_add, ← pow_add]
      show _ = gen ^ count
      rw [hHO, two_mul]
    · show IsInK (word 1 0 0 + σ (.n 33))
      rw [word_one, e33]; exact hK
    · intro hne
      have := hcall (by rwa [show σ (.n 41) = word 1 0 0 + σ (.n 33) from rfl, word_one, e33] at hne)
      rwa [show σ (.n 42) = word 1 0 0 from rfl, word_one, e33]
    · have e44 : σ (.n 44) = bitE (count.testBit 0) + 1 := by
        show bitE (count.testBit 0) + word 1 0 0 = _; rw [word_one]
      have hbK : IsInK (bitE (count.testBit 0)) := by
        unfold bitE; split
        · rw [← ofK_one]; exact ofK_isInK _
        · rw [← ofK_zero]; exact ofK_isInK _
      refine ⟨by rw [e44]; exact isInK_add hbK (by rw [← ofK_one]; exact ofK_isInK _), fun h0 => ?_⟩
      have hO1 : O = 1 := by
        rw [e44] at h0
        have hb : count.testBit 0 = true := by
          by_contra hf
          simp only [Bool.not_eq_true] at hf
          rw [hf, bitE] at h0
          simp at h0
        rw [Nat.testBit_zero] at hb
        simp at hb
        omega
      have e45 : σ (.n 45) = gen ^ H * gen ^ H := by
        rw [show σ (.n 45) = σ (.n 33) * σ (.n 33) from rfl, e33]
      have e55 : σ (.n 55) = (gen ^ H) ^ 64 := by
        rw [show σ (.n 55) = sqn 6 (σ (.n 33)) from rfl, sqn_eq, e33]; norm_num
      have e47 : σ (.n 47) = zo := rfl
      have e49 : σ (.n 49) = qo := rfl
      have e56 : σ (.n 56) = chain * (gen ^ H) ^ 64 := by
        rw [show σ (.n 56) = σ (.n 0) * σ (.n 55) from rfl, e55]; rfl
      have hroz : ∀ k < 64, σ (.n (roz k)) = zo ^ 2 ^ k := by
        intro k hk
        cases k with
        | zero => simp [roz, e47]
        | succ k =>
          obtain ⟨a, -⟩ := rsVals_blk chain z p count zo qo Wo k (by omega)
          exact a
      refine (holds_rsOdd _).mpr ⟨rfl, rfl, ?_, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        fun k hk => ?_⟩
      · rw [show σ (.n 46) = σ (.n 1) * σ (.n 45) from rfl, e45, e47]; exact hzo hO1
      · rw [show σ (.n 48) = σ (.n 2) * σ (.n 45) from rfl, e45, e49]; exact hqo hO1
      · obtain ⟨lw, lo⟩ := hWo hO1 k hk
        cases k with
        | zero =>
          refine ⟨by rw [e56]; exact lw, rfl, rfl, ?_⟩
          rw [e56, show σ (.n 59) = Wo 0 * (zo ^ 2 ^ 0 + qo) by rw [pow_zero, pow_one]; rfl]
          exact lo
        | succ k =>
          obtain ⟨a, b, c, d⟩ := rsVals_blk chain z p count zo qo Wo k (by omega)
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · rw [ev, a, hroz k (by omega), ← pow_add, ← two_mul, pow_succ, Nat.mul_comm]
          · rw [e56, ev, b]; exact lw
          · rw [ev, ev, c, a, e49]
          · rw [ev, ev, ev, d, b, c]
          · rw [e56, ev, d, show 65 + k = 64 + (k + 1) by omega]; exact lo
    · show [σ (.n 0) * σ (.n 318)] = _
      rw [show σ (.n 318) = sqn 6 (σ (.n 33) * σ (.n 37)) from rfl, sqn_eq, e33, e37, ← pow_add,
        ← pow_mul, hHO, show (2 * H + O + 1) / 2 = H + O by omega]
      show [chain * _] = _
      rw [show (H + O) * 2 ^ 6 = 64 * (H + O) by ring]

end
end LeanVM.Guest.B1
