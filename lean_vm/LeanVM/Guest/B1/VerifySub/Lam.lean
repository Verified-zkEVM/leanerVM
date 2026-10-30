/-
  LeanVM.Guest.B1.VerifySub.Lam

  `verify_sub`'s batching (G:3274-3292): the challenge `λ`, the powers stored for the terminal, and
  the batched target.
-/

module

public import LeanVM.Guest.B1.VerifySub.Front
public import LeanVM.Guest.B1.Terminal.Interface
public import LeanVM.Protocol.Keccak.Multilinear
public import LeanVM.Protocol.Keccak.Rmfe

/-!
# The batching

After `λ`'s squeeze, `vsLamT` walks the `140` claims the opening batches (the pool's `165` but
the `25` output lanes', at `110 .. 134`; `vsKept`): claim `i`'s power `λ^(i+1)` is stored at its
pool slot, its value read, and the target accumulates `λ^(i+1)·value`; then `λ^141` times the
output lanes' claim. `kept_eq`: the skipped slots are exactly the claims whose column is an output
lane, so claim `j`'s power is `λ^(1 + poolRank j)`, and the target is the specification's
`dot (powers λ (n + 2)) (ring target :: values ++ [outputs' value])`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val} {next : Prop} {kret : List E → Prop}

/-! ## The batched claims -/

/-- **The batched claims are the kept ones**: the pool's claims whose column is not an output
lane are `vsKept 0, …, vsKept 139`. -/
theorem kept_eq : (List.range Tables.nClaims).filter
    (fun j ↦ Tables.claimColumns.getD j 0 ∉ keccakOutputColumns) = (List.range 140).map vsKept := by
  decide +kernel

theorem poolRank_kept : ∀ i < 140, poolRank (vsKept i) = i := by decide +kernel

theorem poolRank_end : poolRank Tables.nClaims = 140 := by decide +kernel

theorem vsKept_lt {i : ℕ} (hi : i < 140) : vsKept i < Tables.nClaims := by
  unfold vsKept; show _ < 165; split <;> omega

/-- The elements of a list that pass `p`, by index. -/
theorem filter_eq_map_idx {α : Type} [Inhabited α] (p : α → Bool) : ∀ l : List α,
    l.filter p = ((List.range l.length).filter (fun j ↦ p (l.getD j default))).map
      (l.getD · default)
  | [] => rfl
  | a :: l => by
    rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_cons,
      filter_eq_map_idx p l]
    simp only [List.getD_cons_zero, List.filter_map, Function.comp_def, List.getD_cons_succ]
    split <;> simp

/-- The batched claims' values: claim `vsKept i`'s, in order. -/
theorem kept_values {claims : List ColumnClaim} (hcol : claims.map (·.column) = Tables.claimColumns) :
    (claims.filter fun c ↦ c.column ∉ keccakOutputColumns).map (·.value) =
      (List.range 140).map fun i ↦ (claims.map (·.value)).getD (vsKept i) 0 := by
  have hl : claims.length = Tables.nClaims := by
    rw [← List.length_map (f := (·.column)), hcol]; decide +kernel
  have hc : ∀ j < claims.length, (claims.getD j default).column = Tables.claimColumns.getD j 0 := by
    intro j hj
    rw [← hcol, List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ (by simpa using hj),
      List.getElem_map]
  rw [filter_eq_map_idx, List.filter_congr (q := fun j ↦ Tables.claimColumns.getD j 0 ∉
      keccakOutputColumns) fun j hj ↦ by
    rw [hc j (List.mem_range.1 hj)], hl, kept_eq, List.map_map, List.map_map]
  refine List.map_congr_left fun i hi ↦ ?_
  have hk := vsKept_lt (List.mem_range.1 hi)
  simp only [Function.comp_apply]
  rw [List.getD_eq_getElem _ _ (by rw [hl]; exact hk), List.getD_eq_getElem _ _ (by simp [hl, hk]),
    List.getElem_map]

/-! ## The target -/

theorem lam_powersFrom_length (acc base : E) : ∀ n, (powersFrom acc base n).length = n
  | 0 => rfl
  | n + 1 => by rw [powersFrom, List.length_cons, lam_powersFrom_length _ base n]

/-- `dot (powers λ (m + 2)) (T :: f₀ … f_{m-1} ++ [x]) = T + Σ λ^(i+1) f_i + λ^(m+1) x`. -/
theorem dot_powers_batch (lam T x : E) (m : ℕ) (f : ℕ → E) :
    dot (powers lam (m + 2)) (T :: ((List.range m).map f ++ [x])) =
      T + ∑ i ∈ range m, lam ^ (i + 1) * f i + lam ^ (m + 1) * x := by
  have hlen : (powers lam (m + 2)).length = m + 2 := lam_powersFrom_length _ _ _
  rw [dot_eq _ _ (by simp [hlen]), hlen, Finset.sum_range_succ, Finset.sum_range_succ',
    powers_getD lam (by omega : 0 < m + 2), powers_getD lam (by omega : m + 1 < m + 2)]
  have hmid : ∀ i ∈ range m, (powers lam (m + 2)).getD (i + 1) 0 *
      (T :: ((List.range m).map f ++ [x])).getD (i + 1) 0 = lam ^ (i + 1) * f i := by
    intro i hi
    have hi' := List.mem_range.1 hi
    rw [powers_getD lam (by omega), List.getD_cons_succ,
      List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left (by simpa using hi'),
      List.getElem_map, List.getElem_range]
  rw [Finset.sum_congr rfl hmid, List.getD_cons_succ, List.getD_cons_zero,
    List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (by simp)]
  simp only [List.length_map, List.length_range, Nat.sub_self, List.getElem_cons_zero, pow_zero,
    one_mul]
  ring

/-! ## The walk -/

theorem vsPw_succ (n : ℕ) : vsPw (n + 1) = 1328 + 4 * n := by
  simp only [vsPw, Nat.add_one_ne_zero, ↓reduceIte]; omega

theorem vsTg_succ (n : ℕ) : vsTg (n + 1) = 1327 + 4 * n := by
  simp only [vsTg, Nat.add_one_ne_zero, ↓reduceIte]; omega

/-- The first `n` batched claims: their powers stored, the power `λ^(n+1)`, the target. -/
theorem lam_loop {lam T : E} {vals : List E} (hlam : σ (.n 1323) = lam) (hT : σ (.n 1303) = T)
    (hval : ReadsAt rd (σ (.n 7)) vals) (hvl : vals.length = Tables.nClaims) :
    ∀ n ≤ 140, ∀ {nx : Prop}, Stmt.HoldsList C rd σ ((List.range n).flatMap vsLamStep) nx kret →
      (∀ i < n, LoadHolds rd (σ (.n 1324)) (vsKept i) (lam ^ (i + 1))) ∧
      σ (.n (vsPw n)) = lam ^ (n + 1) ∧
      σ (.n (vsTg n)) = T + ∑ i ∈ range n, lam ^ (i + 1) * vals.getD (vsKept i) 0 ∧ nx
  | 0, _, nx, h => ⟨fun i hi ↦ absurd hi (by omega), by simp [vsPw, hlam], by simp [vsTg, hT], h⟩
  | n + 1, hn, nx, h => by
    rw [List.range_succ, List.flatMap_append, holdsList_append] at h
    obtain ⟨hs, hp, ht, h⟩ := lam_loop hlam hT hval hvl n (by omega) h
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, vsLamStep, Stmt.HoldsList,
      Stmt.Holds, Atom.Holds, vsLd, vsMul, vsAdd] at h
    obtain ⟨st, ld, m1, a1, m2, h⟩ := h
    have hk := vsKept_lt (by omega : n < 140)
    have hv : σ (.n (1325 + 4 * n)) = vals.getD (vsKept n) 0 := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact loadHolds_unique ld (hval _ (by omega))
    refine ⟨fun i hi ↦ ?_, ?_, ?_, h⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact hs i hi
      · rw [← hp]; exact st
    · rw [vsPw_succ, m2, hp, hlam]; ring
    · rw [vsTg_succ, a1, ht, m1, hp, hv, Finset.sum_range_succ]; ring

/-- **The batching** (G:3274-3292), after `λ`'s squeeze (`hsq`, the squeeze's facts `SQ`):
claim `j`'s power `λ^(1 + poolRank j)` stored for every batched claim, `λ^141` at `1884`, and
the batched target at `1886`. -/
theorem vsLamT_holds_of {SQ : Prop}
    (hsq : ∀ {nx : Prop}, Stmt.HoldsList C rd σ (vsSqzT 966 1304) nx kret → SQ ∧ nx)
    {claims : List ColumnClaim} (hcol : claims.map (·.column) = Tables.claimColumns)
    (hval : ReadsAt rd (σ (.n 7)) (claims.map (·.value)))
    (h : Stmt.HoldsList C rd σ vsLamT next kret) :
    SQ ∧
    (∀ j < Tables.nClaims, Tables.claimColumns.getD j 0 ∉ keccakOutputColumns →
      LoadHolds rd (σ (.n 1324)) j (σ (.n 1323) ^ (1 + poolRank j))) ∧
    σ (.n 1884) = σ (.n 1323) ^ (1 + poolRank Tables.nClaims) ∧
    σ (.n 1886) = dot (powers (σ (.n 1323))
      ((claims.filter fun c ↦ c.column ∉ keccakOutputColumns).length + 2))
      (σ (.n 1303) :: ((claims.filter fun c ↦ c.column ∉ keccakOutputColumns).map (·.value) ++
        [σ (.n 869)])) ∧ next := by
  have hvl : (claims.map (·.value)).length = Tables.nClaims := by
    rw [List.length_map, ← List.length_map (f := (·.column)), hcol]; decide +kernel
  unfold vsLamT at h
  rw [holdsList_append, holdsList_append, holdsList_append] at h
  obtain ⟨hS, h⟩ := hsq h
  simp only [Stmt.HoldsList, Stmt.Holds, vsAlloc, Atom.Holds, true_and] at h
  obtain ⟨hs, hp, ht, h⟩ := lam_loop rfl rfl hval hvl 140 le_rfl h
  simp only [Stmt.Holds, Atom.Holds, vsMul, vsAdd] at h
  obtain ⟨m, a, h⟩ := h
  have hv := kept_values hcol
  have hfl : (claims.filter fun c ↦ c.column ∉ keccakOutputColumns).length = 140 := by
    rw [← List.length_map (f := (·.value)), hv, List.length_map, List.length_range]
  refine ⟨hS, fun j hj hout ↦ ?_, ?_, ?_, h⟩
  · have hm : j ∈ (List.range 140).map vsKept := by
      rw [← kept_eq]; exact List.mem_filter.2 ⟨List.mem_range.2 hj, by simpa using hout⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hm
    have hi' := List.mem_range.1 hi
    rw [poolRank_kept i hi', add_comm]
    exact hs i hi'
  · rw [poolRank_end]; exact hp
  · rw [hv, hfl, dot_powers_batch, a, m]
    rw [show vsTg 140 = 1883 from rfl] at ht
    rw [show vsPw 140 = 1884 from rfl] at hp
    rw [ht, hp]

/-- **The batching** (G:3274-3292): `λ`'s squeeze, claim `j`'s power `λ^(1 + poolRank j)` stored
for every batched claim, `λ^141` at `1884`, and the batched target at `1886`. -/
theorem vsLamT_holds (h10 : σ (.n 10) = 0) (h11 : σ (.n 11) = 0) (h12 : σ (.n 12) = 0)
    (h13 : σ (.n 13) = 0) {claims : List ColumnClaim}
    (hcol : claims.map (·.column) = Tables.claimColumns)
    (hval : ReadsAt rd (σ (.n 7)) (claims.map (·.value)))
    (h : Stmt.HoldsList C rd σ vsLamT next kret) :
    (⟨[σ (.n 966), σ (.n 967), σ (.n 968), σ (.n 969), σ (.n 970)], []⟩ : Fs).squeeze =
      (σ (.n 1323), ⟨[σ (.n 1312), σ (.n 1313), σ (.n 1314), σ (.n 1315), σ (.n 1316)], []⟩) ∧
    (∀ j < Tables.nClaims, Tables.claimColumns.getD j 0 ∉ keccakOutputColumns →
      LoadHolds rd (σ (.n 1324)) j (σ (.n 1323) ^ (1 + poolRank j))) ∧
    σ (.n 1884) = σ (.n 1323) ^ (1 + poolRank Tables.nClaims) ∧
    σ (.n 1886) = dot (powers (σ (.n 1323))
      ((claims.filter fun c ↦ c.column ∉ keccakOutputColumns).length + 2))
      (σ (.n 1303) :: ((claims.filter fun c ↦ c.column ∉ keccakOutputColumns).map (·.value) ++
        [σ (.n 869)])) ∧ next :=
  vsLamT_holds_of (fun hs ↦ vsSqzT_holds (capb := 966) (o := 1304) h10 h11 h12 h13 hs) hcol hval h

end
end LeanVM.Guest.B1.VerifySub
