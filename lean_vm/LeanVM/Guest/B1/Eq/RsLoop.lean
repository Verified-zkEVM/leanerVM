/-
  LeanVM.Guest.B1.Eq.RsLoop

  B1 for `__loop5`, the paired loop of `rs_eq_run`.
-/

module

public import LeanVM.Guest.B1.Eq.Meaning

/-!
# `__loop5` (`rs_eq_run`'s `mul_range` loop, G:916-929)

At `xp = g^h` the body reads `z[2h]`, `z[2h + 1]`, `point1[2h]`, `point1[2h + 1]` and, for every
`k < 64`, the row word `w = chain[64h + k]`, storing `chain[64h + 64 + k] = w · (z0^(2^k) + p0) ·
(z1^(2^k) + p1)` (`l6Blk k`, the `z` powers squared along `k`), then continues at `xp·g`
(`loop6_step`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The values of `z0^(2^k)` and `z1^(2^k)`. -/
def l6z0 : ℕ → ℕ
  | 0 => 8
  | k + 1 => 24 + 7 * k

def l6z1 : ℕ → ℕ
  | 0 => 9
  | k + 1 => 25 + 7 * k

/-- The row word read at `k`. -/
def l6w : ℕ → ℕ
  | 0 => 19
  | k + 1 => 26 + 7 * k

/-- The row word stored at `64 + k`. -/
def l6o : ℕ → ℕ
  | 0 => 23
  | k + 1 => 30 + 7 * k

/-- Coordinate `k` of the row. -/
def l6Blk : ℕ → List Stmt
  | 0 => [.atom (.load (.n 19) (.n 18) 0), .atom (.add (.n 20) (.n 8) (.n 10)),
      .atom (.mul (.n 21) (.n 19) (.n 20)), .atom (.add (.n 22) (.n 9) (.n 11)),
      .atom (.mul (.n 23) (.n 21) (.n 22)), .atom (.load (.n 23) (.n 18) 64)]
  | k + 1 => [.atom (.mul (.n (24 + 7 * k)) (.n (l6z0 k)) (.n (l6z0 k))),
      .atom (.mul (.n (25 + 7 * k)) (.n (l6z1 k)) (.n (l6z1 k))),
      .atom (.load (.n (26 + 7 * k)) (.n 18) (k + 1)),
      .atom (.add (.n (27 + 7 * k)) (.n (24 + 7 * k)) (.n 10)),
      .atom (.mul (.n (28 + 7 * k)) (.n (26 + 7 * k)) (.n (27 + 7 * k))),
      .atom (.add (.n (29 + 7 * k)) (.n (25 + 7 * k)) (.n 11)),
      .atom (.mul (.n (30 + 7 * k)) (.n (28 + 7 * k)) (.n (29 + 7 * k))),
      .atom (.load (.n (30 + 7 * k)) (.n 18) (65 + k))]

/-- The expansion of `__loop5`. -/
def l6Body : List Stmt :=
  [.atom (.mul (.n 5) (.n 0) (.n 0)), .atom (.mul (.n 6) (.n 2) (.n 5)),
    .atom (.mul (.n 7) (.n 3) (.n 5)), .atom (.load (.n 8) (.n 6) 0),
    .atom (.load (.n 9) (.n 6) 1), .atom (.load (.n 10) (.n 7) 0),
    .atom (.load (.n 11) (.n 7) 1), .atom (.mul (.n 12) (.n 0) (.n 0)),
    .atom (.mul (.n 13) (.n 12) (.n 12)), .atom (.mul (.n 14) (.n 13) (.n 13)),
    .atom (.mul (.n 15) (.n 14) (.n 14)), .atom (.mul (.n 16) (.n 15) (.n 15)),
    .atom (.mul (.n 17) (.n 16) (.n 16)), .atom (.mul (.n 18) (.n 4) (.n 17))] ++
  ((List.range 64).map l6Blk).flatten ++
  [.atom (.const (.n 465) (word 2 0 0)), .atom (.mul (.n 466) (.n 0) (.n 465)),
    .atom (.add (.n 467) (.n 466) (.n 1)), .atom (.const (.n 468) (word 2 0 0)),
    .atom (.mul (.n 469) (.n 0) (.n 468)),
    .callIf (.n 467) "__loop5" [.n 469, .n 1, .n 2, .n 3, .n 4], .ret []]

theorem core76_body : Fn.body Data.core76 = l6Body := stmtsEqb_sound (by decide +kernel)

theorem find_loop6 : coreProgram.find? "__loop5" = some Data.core76 :=
  Program.find?_of_indexOf? (j := 76) (by decide +kernel) rfl

/-- What coordinate `k` asks. -/
def L6Ok (rd : Reader) (σ : Val) : ℕ → Prop
  | 0 => LoadHolds rd (σ (.n 18)) 0 (σ (.n 19)) ∧ σ (.n 20) = σ (.n 8) + σ (.n 10) ∧
      σ (.n 21) = σ (.n 19) * σ (.n 20) ∧ σ (.n 22) = σ (.n 9) + σ (.n 11) ∧
      σ (.n 23) = σ (.n 21) * σ (.n 22) ∧ LoadHolds rd (σ (.n 18)) 64 (σ (.n 23))
  | k + 1 => σ (.n (24 + 7 * k)) = σ (.n (l6z0 k)) * σ (.n (l6z0 k)) ∧
      σ (.n (25 + 7 * k)) = σ (.n (l6z1 k)) * σ (.n (l6z1 k)) ∧
      LoadHolds rd (σ (.n 18)) (k + 1) (σ (.n (26 + 7 * k))) ∧
      σ (.n (27 + 7 * k)) = σ (.n (24 + 7 * k)) + σ (.n 10) ∧
      σ (.n (28 + 7 * k)) = σ (.n (26 + 7 * k)) * σ (.n (27 + 7 * k)) ∧
      σ (.n (29 + 7 * k)) = σ (.n (25 + 7 * k)) + σ (.n 11) ∧
      σ (.n (30 + 7 * k)) = σ (.n (28 + 7 * k)) * σ (.n (29 + 7 * k)) ∧
      LoadHolds rd (σ (.n 18)) (65 + k) (σ (.n (30 + 7 * k)))

theorem holds_l6Blk {C : CallRel} {rd : Reader} {σ : Val} (k : ℕ) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (l6Blk k) True kret ↔ L6Ok rd σ k := by
  cases k <;> simp only [l6Blk, L6Ok, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]

/-- The loop's body at `x`: the two `z` and `point1` words at `x²`, and every coordinate `k` of
the next row the row's word times the two factors. -/
def Loop6Body (rd : Reader) (z p chain x : E) : Prop :=
  ∃ z0 z1 q0 q1 : E, LoadHolds rd (z * (x * x)) 0 z0 ∧ LoadHolds rd (z * (x * x)) 1 z1 ∧
    LoadHolds rd (p * (x * x)) 0 q0 ∧ LoadHolds rd (p * (x * x)) 1 q1 ∧
    ∀ k < 64, ∃ w, LoadHolds rd (chain * x ^ 64) k w ∧
      LoadHolds rd (chain * x ^ 64) (64 + k) (w * (z0 ^ 2 ^ k + q0) * (z1 ^ 2 ^ k + q1))

theorem l6_pow {σ : Val} {rd : Reader} (h : ∀ k < 64, L6Ok rd σ k) :
    ∀ k < 64, σ (.n (l6z0 k)) = σ (.n 8) ^ 2 ^ k ∧ σ (.n (l6z1 k)) = σ (.n 9) ^ 2 ^ k
  | 0, _ => by simp [l6z0, l6z1]
  | k + 1, hk => by
    obtain ⟨e0, e1, -⟩ := h (k + 1) hk
    obtain ⟨i0, i1⟩ := l6_pow h k (by omega)
    refine ⟨?_, ?_⟩
    · rw [l6z0, e0, i0, ← pow_add, ← two_mul, pow_succ, Nat.mul_comm]
    · rw [l6z1, e1, i1, ← pow_add, ← two_mul, pow_succ, Nat.mul_comm]

theorem x_pow_64 (x : E) : ((((((x * x) * (x * x)) * ((x * x) * (x * x))) *
    (((x * x) * (x * x)) * ((x * x) * (x * x)))) * ((((x * x) * (x * x)) * ((x * x) * (x * x))) *
    (((x * x) * (x * x)) * ((x * x) * (x * x))))) * (((((x * x) * (x * x)) * ((x * x) * (x * x))) *
    (((x * x) * (x * x)) * ((x * x) * (x * x)))) * ((((x * x) * (x * x)) * ((x * x) * (x * x))) *
    (((x * x) * (x * x)) * ((x * x) * (x * x)))))) = x ^ 64 := by ring

/-- The honest values of `__loop5` at `x`, from the words of `Loop6Body`. -/
def l6Vals (x N z p chain z0 z1 q0 q1 : E) (w : ℕ → E) (i : ℕ) : E :=
  if i < 24 then
    [x, N, z, p, chain, x * x, z * (x * x), p * (x * x), z0, z1, q0, q1, x ^ 2, x ^ 4, x ^ 8,
      x ^ 16, x ^ 32, x ^ 64, chain * x ^ 64, w 0, z0 + q0, w 0 * (z0 + q0), z1 + q1,
      w 0 * (z0 + q0) * (z1 + q1)].getD i 0
  else if i < 465 then
    let k := (i - 24) / 7 + 1
    match (i - 24) % 7 with
    | 0 => z0 ^ 2 ^ k
    | 1 => z1 ^ 2 ^ k
    | 2 => w k
    | 3 => z0 ^ 2 ^ k + q0
    | 4 => w k * (z0 ^ 2 ^ k + q0)
    | 5 => z1 ^ 2 ^ k + q1
    | _ => w k * (z0 ^ 2 ^ k + q0) * (z1 ^ 2 ^ k + q1)
  else [gen, x * gen, x * gen + N, gen, x * gen].getD (i - 465) 0

theorem ite_F {α : Type} {c : Prop} [Decidable c] {x y : α} (h : ¬c) : (if c then x else y) = y := by
  simp [h]

theorem ite_T {α : Type} {c : Prop} [Decidable c] {x y : α} (h : c) : (if c then x else y) = x := by
  simp [h]

/-- The honest values of coordinate `k + 1`. -/
theorem l6Vals_blk (x N z p chain z0 z1 q0 q1 : E) (w : ℕ → E) (k : ℕ) (hk : k < 63) :
    let v := l6Vals x N z p chain z0 z1 q0 q1 w
    v (24 + 7 * k) = z0 ^ 2 ^ (k + 1) ∧ v (25 + 7 * k) = z1 ^ 2 ^ (k + 1) ∧
      v (26 + 7 * k) = w (k + 1) ∧ v (27 + 7 * k) = z0 ^ 2 ^ (k + 1) + q0 ∧
      v (28 + 7 * k) = w (k + 1) * (z0 ^ 2 ^ (k + 1) + q0) ∧
      v (29 + 7 * k) = z1 ^ 2 ^ (k + 1) + q1 ∧
      v (30 + 7 * k) = w (k + 1) * (z0 ^ 2 ^ (k + 1) + q0) * (z1 ^ 2 ^ (k + 1) + q1) := by
  intro v
  simp only [v, l6Vals]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [ite_F (by omega), ite_T (by omega)]
  · rw [show (24 + 7 * k - 24) % 7 = 0 by omega, show (24 + 7 * k - 24) / 7 = k by omega]; rfl
  · rw [show (25 + 7 * k - 24) % 7 = 1 by omega, show (25 + 7 * k - 24) / 7 = k by omega]; rfl
  · rw [show (26 + 7 * k - 24) % 7 = 2 by omega, show (26 + 7 * k - 24) / 7 = k by omega]; rfl
  · rw [show (27 + 7 * k - 24) % 7 = 3 by omega, show (27 + 7 * k - 24) / 7 = k by omega]; rfl
  · rw [show (28 + 7 * k - 24) % 7 = 4 by omega, show (28 + 7 * k - 24) / 7 = k by omega]; rfl
  · rw [show (29 + 7 * k - 24) % 7 = 5 by omega, show (29 + 7 * k - 24) / 7 = k by omega]; rfl
  · rw [show (30 + 7 * k - 24) % 7 = 6 by omega, show (30 + 7 * k - 24) / 7 = k by omega]; rfl

/-- **`__loop5`, one step**: at depth `d + 1` its relation at `x` is the body at `x` and the
conditional call at `x·g`. -/
theorem loop6_step (rd : Reader) (N z p chain : E) (d : ℕ) (x : E) :
    coreProgram.relN rd (d + 1) "__loop5" (x :: [N, z, p, chain]) [] ↔
      Loop6Body rd z p chain x ∧ IsInK (x * gen + N) ∧
        (x * gen + N ≠ 0 → coreProgram.relN rd d "__loop5" (x * gen :: [N, z, p, chain]) []) := by
  rw [relN_succ_iff find_loop6, show Fn.params Data.core76 = [.n 0, .n 1, .n 2, .n 3, .n 4] from rfl,
    core76_body, l6Body]
  simp only [holdsList_append, holdsList_range_flatten 64 l6Blk (fun k => by cases k <;> rfl),
    holds_l6Blk, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, and_true,
    word_gen]
  constructor
  · rintro ⟨σ, hp, h5, h6, h7, l8, l9, l10, l11, h12, h13, h14, h15, h16, h17, h18, hblk, h465,
      h466, h467, h468, h469, hK, hcall⟩
    simp only [List.cons.injEq] at hp
    obtain ⟨rfl, rfl, rfl, rfl, rfl, -⟩ := hp
    have hx64 : σ (.n 17) = σ (.n 0) ^ 64 := by
      rw [h17, h16, h15, h14, h13, h12, x_pow_64]
    have hpw := l6_pow hblk
    refine ⟨⟨σ (.n 8), σ (.n 9), σ (.n 10), σ (.n 11), by rwa [h6, h5] at l8,
      by rwa [h6, h5] at l9, by rwa [h7, h5] at l10, by rwa [h7, h5] at l11, fun k hk => ?_⟩,
      by rwa [h467, h466, h465] at hK, fun hne => ?_⟩
    · rw [← hx64, ← h18]
      cases k with
      | zero =>
        obtain ⟨lw, e20, e21, e22, e23, lo⟩ := hblk 0 hk
        refine ⟨σ (.n 19), lw, ?_⟩
        rw [e23, e21, e20, e22] at lo
        simpa using lo
      | succ k =>
        obtain ⟨-, -, lw, e27, e28, e29, e30, lo⟩ := hblk (k + 1) hk
        obtain ⟨p0, p1⟩ := hpw (k + 1) hk
        refine ⟨σ (.n (26 + 7 * k)), lw, ?_⟩
        rw [e30, e28, e29, e27, show 24 + 7 * k = l6z0 (k + 1) from rfl,
          show 25 + 7 * k = l6z1 (k + 1) from rfl, p0, p1, show 65 + k = 64 + (k + 1) by omega] at lo
        exact lo
    · have := hcall (by rwa [h467, h466, h465])
      rwa [h469, h468] at this
  · rintro ⟨⟨z0, z1, q0, q1, l8, l9, l10, l11, hrow⟩, hK, hcall⟩
    choose! wf hwf using hrow
    let σ : Val := fun v => l6Vals x N z p chain z0 z1 q0 q1 wf v.idx
    have ev : ∀ i, σ (.n i) = l6Vals x N z p chain z0 z1 q0 q1 wf i := fun _ => rfl
    have hz0 : ∀ k < 64, σ (.n (l6z0 k)) = z0 ^ 2 ^ k ∧ σ (.n (l6z1 k)) = z1 ^ 2 ^ k := by
      intro k hk
      cases k with
      | zero => simp [ev, l6Vals, l6z0, l6z1]
      | succ k =>
        obtain ⟨a, b, -⟩ := l6Vals_blk x N z p chain z0 z1 q0 q1 wf k (by omega)
        exact ⟨a, b⟩
    refine ⟨σ, rfl, ?_⟩
    simp only [ev]
    refine ⟨by simp [l6Vals], by simp [l6Vals], by simp [l6Vals], by simpa [l6Vals] using l8,
      by simpa [l6Vals] using l9, by simpa [l6Vals] using l10, by simpa [l6Vals] using l11,
      by simp [l6Vals]; ring, by simp [l6Vals]; ring, by simp [l6Vals]; ring,
      by simp [l6Vals]; ring, by simp [l6Vals]; ring, by simp [l6Vals]; ring, by simp [l6Vals],
      fun k hk => ?_, by simp [l6Vals], by simp [l6Vals], by simp [l6Vals], by simp [l6Vals],
      by simp [l6Vals], by simpa [l6Vals] using hK, fun hne => ?_⟩
    · obtain ⟨lw, lo⟩ := hwf k hk
      cases k with
      | zero =>
        simp only [L6Ok, ev]
        refine ⟨by simpa [l6Vals] using lw, by simp [l6Vals], by simp [l6Vals], by simp [l6Vals],
          by simp [l6Vals], by simpa [l6Vals] using lo⟩
      | succ k =>
        obtain ⟨a, b, c, d, e, f, g⟩ := l6Vals_blk x N z p chain z0 z1 q0 q1 wf k (by omega)
        obtain ⟨i0, i1⟩ := hz0 k (by omega)
        rw [ev] at i0 i1
        simp only [L6Ok, ev]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [a, i0, ← pow_add, ← two_mul, pow_succ, Nat.mul_comm]
        · rw [b, i1, ← pow_add, ← two_mul, pow_succ, Nat.mul_comm]
        · rw [c]; simpa [l6Vals] using lw
        · rw [d, a, show l6Vals x N z p chain z0 z1 q0 q1 wf 10 = q0 by simp [l6Vals]]
        · rw [e, c, d]
        · rw [f, b, show l6Vals x N z p chain z0 z1 q0 q1 wf 11 = q1 by simp [l6Vals]]
        · rw [g, e, f]
        · rw [g, show 65 + k = 64 + (k + 1) by omega]; simpa [l6Vals] using lo
    · have := hcall (by simpa [l6Vals] using hne)
      simpa [l6Vals] using this

end
end LeanVM.Guest.B1
