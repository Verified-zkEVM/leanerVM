/-
  LeanVM.Guest.B1.BasicS

  `Basic.lean` under any semantics of `BLAKE2S` (`S : BlakeSem`).
-/

module

public import LeanVM.Guest.B1.Basic
public import LeanVM.Guest.CoreB

/-!
# `Basic.lean` under any `BLAKE2S` semantics

Each definition and lemma of `Basic.lean` that mentions the semantics, with `S : BlakeSem` a
parameter and a `S` in its name.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {S : BlakeSem}

/-! ## Unfolding a function -/

/-- A function's relation is its body's, once it is found by name. -/
theorem relS_iff_sem {P : Core.Program} {rd : Reader} {f : String} {fn : Fn}
    (h : P.find? f = some fn) (args rets : List E) :
    P.RelB S rd f args rets ↔
      ∃ σ : Val, fn.params.map σ = args ∧
        Stmt.HoldsListB S (P.RelB S rd) rd σ fn.body False (fun rs => rs = rets) := by
  rw [relB_iff]
  simp only [h, Option.some.injEq, exists_eq_left', Fn.SemB]

/-- The same at a finite depth: the body's calls one level shallower. -/
theorem relNS_succ_iff {P : Core.Program} {rd : Reader} {f : String} {fn : Fn}
    (h : P.find? f = some fn) (n : ℕ) (args rets : List E) :
    P.relNB S rd (n + 1) f args rets ↔
      ∃ σ : Val, fn.params.map σ = args ∧
        Stmt.HoldsListB S (P.relNB S rd n) rd σ fn.body False (fun rs => rs = rets) := by
  simp only [Program.relNB, h, Option.some.injEq, exists_eq_left', Fn.SemB]

/-! ## `mul_range` loops -/

/-- **A `mul_range` loop** (`for x in mul_range(g^k, N)`, lowered to a helper `f` that runs its
body at `x`, then calls itself at `x·g` while `x·g ≠ N`): if `f`'s relation at depth `d + 1` is
its body's meaning `B x` and the conditional call, then `f` holds at `g^k` exactly when the loop
ends: `N = g^m` for the first `m > k` it reaches, and `B` holds at every `g^j`, `k ≤ j < m`. -/
theorem loopS_iff {P : Core.Program} {rd : Reader} {f : String} {ps : List E} {N : E}
    {B : E → Prop}
    (hstep : ∀ d x, P.relNB S rd (d + 1) f (x :: ps) [] ↔
      B x ∧ IsInK (x * gen + N) ∧ (x * gen + N ≠ 0 → P.relNB S rd d f (x * gen :: ps) []))
    (k : ℕ) :
    P.RelB S rd f (gen ^ k :: ps) [] ↔
      ∃ m, k < m ∧ N = gen ^ m ∧ (∀ j, k < j → j < m → gen ^ j ≠ N) ∧
        ∀ j, k ≤ j → j < m → B (gen ^ j) := by
  constructor
  · rintro ⟨d, hd⟩
    induction d generalizing k with
    | zero => exact hd.elim
    | succ d ih =>
      obtain ⟨hB, -, hnext⟩ := (hstep d _).mp hd
      by_cases h0 : gen ^ k * gen + N = 0
      · refine ⟨k + 1, by omega, (gen_pow_add_eq_zero_iff k).mp h0, fun j h1 h2 => by omega,
          fun j h1 h2 => ?_⟩
        rwa [show j = k by omega]
      · have := hnext h0
        rw [gen_pow_mul_gen] at this
        obtain ⟨m, hm, hN, hfirst, hall⟩ := ih (k + 1) this
        refine ⟨m, by omega, hN, fun j h1 h2 => ?_, fun j h1 h2 => ?_⟩
        · rcases Nat.lt_or_ge (k + 1) j with h | h
          · exact hfirst j h h2
          · rw [show j = k + 1 by omega]
            intro he
            exact h0 ((gen_pow_add_eq_zero_iff k).mpr he.symm)
        · rcases Nat.lt_or_ge k j with h | h
          · exact hall j (by omega) h2
          · rwa [show j = k by omega]
  · rintro ⟨m, hkm, hN, hfirst, hall⟩
    obtain ⟨t, rfl⟩ : ∃ t, m = k + 1 + t := ⟨m - k - 1, by omega⟩
    have hK : ∀ j, IsInK (gen ^ j * gen + N) := fun j => by
      rw [hN]; exact isInK_add (isInK_mul (gen_pow_isInK j) (by simpa using gen_pow_isInK 1)) (gen_pow_isInK _)
    refine ⟨t + 1, ?_⟩
    induction t generalizing k with
    | zero =>
      exact (hstep 0 _).mpr ⟨hall k le_rfl (by omega), hK k,
        fun h => absurd ((gen_pow_add_eq_zero_iff k).mpr hN) h⟩
    | succ t ih =>
      refine (hstep (t + 1) _).mpr ⟨hall k le_rfl (by omega), hK k, fun _ => ?_⟩
      rw [gen_pow_mul_gen]
      exact ih (k + 1) (by omega) (by rw [hN]; congr 1; omega)
        (fun j h1 h2 => hfirst j (by omega) (by omega)) (fun j h1 h2 => hall j (by omega) (by omega))

/-! ## Comparing statement lists by kernel evaluation

`stmtsEqb` is a structural Boolean equality on statements, comparing words limb by limb (the
kernel reduces `E.limb` on literal words, not `DecidableEq E`). `stmtsEqb_sound`: a template
equal to a function's body by `decide +kernel` on `stmtsEqb`, where `rfl` would unfold both
sides in the elaborator. -/

/-- **A loop behind its guard** (`for x in mul_range(1, N)`: `callIf (1 + N) f [1, …]`): the guard
is in `K` and, when nonzero, the loop runs, exactly when `N = g^m` for some `m` below the order of
`g` and the body holds at every `g^j`, `j < m`. -/
theorem guardedS_loop_iff {P : Core.Program} {rd : Reader} {f : String} {ps : List E} {N : E}
    {B : E → Prop}
    (hstep : ∀ d x, P.relNB S rd (d + 1) f (x :: ps) [] ↔
      B x ∧ IsInK (x * gen + N) ∧ (x * gen + N ≠ 0 → P.relNB S rd d f (x * gen :: ps) [])) :
    (IsInK (1 + N) ∧ (1 + N ≠ 0 → P.RelB S rd f (1 :: ps) [])) ↔
      ∃ m < ordG, N = gen ^ m ∧ ∀ j < m, B (gen ^ j) := by
  have hl := loopS_iff hstep 0
  rw [pow_zero] at hl
  constructor
  · rintro ⟨hK, hrun⟩
    by_cases h1 : 1 + N = 0
    · refine ⟨0, by decide, ?_, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
      rw [pow_zero]; exact (e_add_eq_zero_iff.mp h1).symm
    · obtain ⟨m, hm, hN, hfirst, hall⟩ := hl.mp (hrun h1)
      refine ⟨m, ?_, hN, fun j hj => hall j (Nat.zero_le j) hj⟩
      by_contra hge
      rcases Nat.lt_or_ge ordG m with hgt | hle
      · have : gen ^ (m - ordG) = N := by
          obtain ⟨t, rfl⟩ : ∃ t, m = ordG + t := ⟨m - ordG, by omega⟩
          rw [hN, pow_add, gen_pow_ordG, one_mul, Nat.add_sub_cancel_left]
        exact hfirst (m - ordG) (Nat.sub_pos_of_lt hgt) (Nat.sub_lt (by omega) ordG_pos) this
      · have hm' : m = ordG := by omega
        rw [hm', gen_pow_ordG] at hN
        exact h1 (by rw [hN]; exact e_add_self 1)
  · rintro ⟨m, hm, hN, hall⟩
    refine ⟨?_, fun h1 => ?_⟩
    · rw [hN]
      exact isInK_add (by rw [← pow_zero gen]; exact gen_pow_isInK 0) (gen_pow_isInK m)
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · exact absurd (show 1 + N = 0 by rw [hN, h, pow_zero]; exact e_add_self 1) h1
      · exact h
    exact hl.mpr ⟨m, hm0, hN, first_hit_of_lt hm hN, fun j _ hj => hall j hj⟩

/-- A forward branch whose blocks have no `ret` holds, then its continuation. -/
theorem holdsS_ite_noRet {C : CallRel} {rd : Reader} {σ : Val} (c : V) (z n : List Stmt)
    (hz : Stmt.noRetList z = true) (hn : Stmt.noRetList n = true) (next : Prop)
    (kret : List E → Prop) :
    Stmt.HoldsB S C rd σ (.ite c z n) next kret ↔
      (IsInK (σ c) ∧ (σ c = 0 → Stmt.HoldsListB S C rd σ z True kret) ∧
        (σ c ≠ 0 → Stmt.HoldsListB S C rd σ n True kret)) ∧ next := by
  rw [holdsB_noRet (.ite c z n) (by simp [Stmt.noRet, hz, hn]) next kret]
  rfl

end
end LeanVM.Guest.B1
