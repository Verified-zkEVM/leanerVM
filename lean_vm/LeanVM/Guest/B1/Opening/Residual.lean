/-
  LeanVM.Guest.B1.Opening.Residual

  The expansion of the guest's inline `residual_query`, and the factoring of the induced weight's
  coordinates it rests on.
-/

module

public import LeanVM.Guest.B1.Common.Atoms

/-!
# `residual_query` (G:1265-1273, TRIAGE #41)

`residual_query(basis_chain, row_d, vanish, n)` is `Π_{t<n} (d_t + chain_t)` over the row
`d_t = row_d[t]`, `chain_0` the query position and
`chain_{t+1} = chain_t·(chain_t + VALS[vanish + t])` (`LIG_VANISH_VALS`, the subspace roots,
`subspaceRoots`, V:1709). Its expansion from the value `b`, the position at `x`, the row at `r`
and the constants `vals` (`open_stacked`'s query loops number it) is `residualT x r vals b`.

* `residualT_sound`: the template's value is `Π_{t<n} (d_t + chain_t)`.
* `residual_factor`: `1 + c·(1 + x·inv) = (c·inv)·((1 + c)/(c·inv) + x)` when `c·inv ≠ 0`, so the
  product of `inducedWeight`'s factors (V:1715) at one query is `Π_t (c_t·inv_t)` (the level's
  scale, `open_stacked`'s `level_scale`) times the template's value at `d_t = (1 + c_t)/(c_t·inv_t)`
  (`basis_d`, G:1553-1559): `residual_prod`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

/-- Coordinate `t + 1`'s block (`t < vals.length`) from its first value `B = b + 2 + 6t`. -/
def residualBlkT (x r : V) (vals : List E) (b t : ℕ) : List Stmt :=
  let B := b + 2 + 6 * t
  let chainPrev : V := if t = 0 then x else .n (B - 4)
  let prefixPrev : V := if t = 0 then .n (b + 1) else .n (B - 1)
  [.atom (.const (.n B) (vals.getD t 0)), .atom (.add (.n (B + 1)) chainPrev (.n B)),
    .atom (.mul (.n (B + 2)) chainPrev (.n (B + 1))), .atom (.load (.n (B + 3)) r (t + 1)),
    .atom (.add (.n (B + 4)) (.n (B + 3)) (.n (B + 2))), .atom (.mul (.n (B + 5)) prefixPrev (.n (B + 4)))]

/-- **`residual_query(position, row_d, vanish, vals.length + 1)`** from the value `b`. -/
def residualT (x r : V) (vals : List E) (b : ℕ) : List Stmt :=
  [.atom (.load (.n b) r 0), .atom (.add (.n (b + 1)) (.n b) x)] ++
    ((List.range vals.length).map (residualBlkT x r vals b)).flatten

/-- The value `residual_query` returns. -/
def residualV (b n : ℕ) : ℕ := if n = 0 then b + 1 else b + 2 + 6 * (n - 1) + 5

theorem residualT_atoms (x r : V) (vals : List E) (b : ℕ) : AllAtoms (residualT x r vals b) := by
  unfold residualT
  refine allAtoms_append (allAtoms_cons (allAtoms_cons allAtoms_nil))
    (allAtoms_map_flatten fun t _ => ?_)
  unfold residualBlkT
  exact allAtoms_cons (allAtoms_cons (allAtoms_cons (allAtoms_cons (allAtoms_cons
    (allAtoms_cons allAtoms_nil)))))

/-- The subspace-vanishing walk from the position `x`. -/
def residualChain (vals : List E) (x : E) : ℕ → E
  | 0 => x
  | t + 1 => residualChain vals x t * (residualChain vals x t + vals.getD t 0)

/-- `Π_{t<n} (d_t + chain_t)`, left to right. -/
def residualProd (vals : List E) (x : E) (d : ℕ → E) : ℕ → E
  | 0 => 1
  | n + 1 => residualProd vals x d n * (d n + residualChain vals x n)

/-- **`residual_query`** (G:1265-1273): with the row's words `d t` at `r`, the template's value is
`Π_{t ≤ vals.length} (d_t + chain_t)`. -/
theorem residualT_sound {x r : V} {vals : List E} {b : ℕ}
    (hA : ∀ a, Stmt.atom a ∈ residualT x r vals b → a.Holds rd σ) {d : ℕ → E}
    (hd : ∀ t ≤ vals.length, LoadHolds rd (σ r) t (d t)) :
    σ (.n (residualV b (vals.length))) = residualProd vals (σ x) d (vals.length + 1) := by
  have l0 := hA _ (by simp [residualT] : Stmt.atom (.load (.n b) r 0) ∈ _)
  have a1 := hA _ (by simp [residualT] : Stmt.atom (.add (.n (b + 1)) (.n b) x) ∈ _)
  simp only [Atom.Holds] at a1
  have hd0 : σ (.n b) = d 0 := loadHolds_unique l0 (hd 0 (by omega))
  -- the walk and the product after each block
  have key : ∀ t ≤ vals.length,
      σ (if t = 0 then x else .n (b + 2 + 6 * (t - 1) + 2)) = residualChain vals (σ x) t ∧
      σ (.n (residualV b t)) = residualProd vals (σ x) d (t + 1) := by
    intro t ht
    induction t with
    | zero =>
      refine ⟨rfl, ?_⟩
      simp only [residualV, ↓reduceIte, residualProd, one_mul, residualChain]
      rw [a1, hd0]
    | succ t ih =>
      obtain ⟨ihc, ihp⟩ := ih (by omega)
      have mem : ∀ a, Stmt.atom a ∈ residualBlkT x r vals b t → a.Holds rd σ := fun a ha =>
        hA a (List.mem_append_right _ (List.mem_flatten.mpr ⟨_, List.mem_map.mpr
          ⟨t, List.mem_range.mpr (by omega), rfl⟩, ha⟩))
      set B := b + 2 + 6 * t with hB
      have hcp : (if t = 0 then x else (V.n (B - 4))) = (if t = 0 then x else .n (b + 2 + 6 * (t - 1) + 2)) := by
        split
        · rfl
        · congr 1; omega
      have hpp : (if t = 0 then V.n (b + 1) else .n (B - 1)) = .n (residualV b t) := by
        unfold residualV
        split
        · rfl
        · congr 1; omega
      have c0 := mem _ (by simp [residualBlkT, ← hB] : Stmt.atom (.const (.n B) (vals.getD t 0)) ∈ _)
      have c1 := mem _ (by simp [residualBlkT, ← hB] : Stmt.atom (.add (.n (B + 1))
        (if t = 0 then x else .n (B - 4)) (.n B)) ∈ _)
      have c2 := mem _ (by simp [residualBlkT, ← hB] : Stmt.atom (.mul (.n (B + 2))
        (if t = 0 then x else .n (B - 4)) (.n (B + 1))) ∈ _)
      have c3 := mem _ (by simp [residualBlkT, ← hB] : Stmt.atom (.load (.n (B + 3)) r (t + 1)) ∈ _)
      have c4 := mem _ (by simp [residualBlkT, ← hB] :
        Stmt.atom (.add (.n (B + 4)) (.n (B + 3)) (.n (B + 2))) ∈ _)
      have c5 := mem _ (by simp [residualBlkT, ← hB] : Stmt.atom (.mul (.n (B + 5))
        (if t = 0 then .n (b + 1) else .n (B - 1)) (.n (B + 4))) ∈ _)
      simp only [Atom.Holds] at c0 c1 c2 c4 c5
      rw [hcp, ihc] at c1 c2
      rw [hpp, ihp] at c5
      have hch : σ (.n (B + 2)) = residualChain vals (σ x) (t + 1) := by
        rw [c2, c1, c0]; rfl
      have hd1 : σ (.n (B + 3)) = d (t + 1) := loadHolds_unique c3 (hd (t + 1) ht)
      refine ⟨by simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]; exact hch, ?_⟩
      have hv : residualV b (t + 1) = B + 5 := by simp [residualV, hB]
      rw [hv, c5, c4, hd1, hch]
      rfl
  exact (key _ le_rfl).2

/-! ## The factoring -/

/-- **A coordinate's factor** (G:1533-1541): `1 + c·(1 + x·inv) = (c·inv)·((1 + c)/(c·inv) + x)`. -/
theorem residual_factor {c inv x : E} (h : c * inv ≠ 0) :
    1 + c * (1 + x * inv) = c * inv * ((1 + c) / (c * inv) + x) := by
  have e : c * inv * ((1 + c) / (c * inv)) = 1 + c := mul_div_cancel₀ _ h
  rw [mul_add (c * inv), e]
  ring

/-- **The product of `inducedWeight`'s factors** (V:1715) at one query is the level's scale times
`residual_query`'s value at `d_t = (1 + c_t)/(c_t·inv_t)`. -/
theorem residual_prod (vals : List E) (x : E) (c inv : ℕ → E) (n : ℕ)
    (h : ∀ t < n, c t * inv t ≠ 0) :
    (∏ t ∈ Finset.range n, (1 + c t * (1 + residualChain vals x t * inv t))) =
      (∏ t ∈ Finset.range n, (c t * inv t)) *
        residualProd vals x (fun t ↦ (1 + c t) / (c t * inv t)) n := by
  induction n with
  | zero => simp [residualProd]
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, ih (fun t ht => h t (by omega)),
      residual_factor (h n (by omega)), residualProd]
    ring

/-! ## The honest values -/

/-- The honest value at offset `o` of `residualT`: `d_0`, `d_0 + x`, then per coordinate `t + 1`
the constant, `chain_t + c`, `chain_{t+1}`, `d_{t+1}`, `d_{t+1} + chain_{t+1}`, the product. -/
def residualVal (vals : List E) (x : E) (d : ℕ → E) (o : ℕ) : E :=
  if o = 0 then d 0 else if o = 1 then d 0 + x
  else
    let t := (o - 2) / 6
    [vals.getD t 0, residualChain vals x t + vals.getD t 0, residualChain vals x (t + 1), d (t + 1),
      d (t + 1) + residualChain vals x (t + 1), residualProd vals x d (t + 2)].getD ((o - 2) % 6) 0

theorem residualVal_blk (vals : List E) (x : E) (d : ℕ → E) (t j : ℕ) (hj : j < 6) :
    residualVal vals x d (2 + 6 * t + j) =
      [vals.getD t 0, residualChain vals x t + vals.getD t 0, residualChain vals x (t + 1), d (t + 1),
        d (t + 1) + residualChain vals x (t + 1), residualProd vals x d (t + 2)].getD j 0 := by
  simp only [residualVal, show ¬ 2 + 6 * t + j = 0 by omega, show ¬ 2 + 6 * t + j = 1 by omega,
    ↓reduceIte, show (2 + 6 * t + j - 2) / 6 = t by omega, show (2 + 6 * t + j - 2) % 6 = j by omega]

/-- **The honest values satisfy `residual_query`**, the row's words `d t` in memory at `r`. -/
theorem residualT_complete {x r : V} {vals : List E} {b : ℕ} {d : ℕ → E}
    (hd : ∀ t ≤ vals.length, LoadHolds rd (σ r) t (d t))
    (hv : ∀ o < 2 + 6 * vals.length, σ (.n (b + o)) = residualVal vals (σ x) d o) :
    ∀ a, Stmt.atom a ∈ residualT x r vals b → a.Holds rd σ := by
  intro a ha
  have v0 : σ (.n b) = d 0 := by simpa [residualVal] using hv 0 (by omega)
  have v1 : σ (.n (b + 1)) = d 0 + σ x := by simpa [residualVal] using hv 1 (by omega)
  simp only [residualT, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatten, List.mem_map, List.mem_range] at ha
  rcases ha with (h | h) | ⟨blk, ⟨t, ht, rfl⟩, hb⟩
  all_goals try (obtain rfl := Stmt.atom.inj h)
  · show LoadHolds rd (σ r) 0 (σ (.n b)); rw [v0]; exact hd 0 (by omega)
  · show σ (.n (b + 1)) = σ (.n b) + σ x; rw [v1, v0]
  · set B := b + 2 + 6 * t with hB
    have w : ∀ j < 6, σ (.n (B + j)) = [vals.getD t 0, residualChain vals (σ x) t + vals.getD t 0,
        residualChain vals (σ x) (t + 1), d (t + 1), d (t + 1) + residualChain vals (σ x) (t + 1),
        residualProd vals (σ x) d (t + 2)].getD j 0 := fun j hj => by
      rw [show B + j = b + (2 + 6 * t + j) by omega, hv _ (by omega), residualVal_blk _ _ _ _ _ hj]
    have w0 : σ (.n B) = vals.getD t 0 := w 0 (by omega)
    have w1 := w 1 (by omega); have w2 := w 2 (by omega); have w3 := w 3 (by omega)
    have w4 := w 4 (by omega); have w5 := w 5 (by omega)
    simp only [List.getD_cons_succ, List.getD_cons_zero] at w1 w2 w3 w4 w5
    have hprev : σ (if t = 0 then x else .n (B - 4)) = residualChain vals (σ x) t := by
      split
      · rename_i h; subst h; rfl
      · rename_i h
        obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
        have := hv (2 + 6 * u + 2) (by omega)
        rw [residualVal_blk _ _ _ _ _ (by omega)] at this
        rw [show B - 4 = b + (2 + 6 * u + 2) by omega, this]; rfl
    have hpp : σ (if t = 0 then .n (b + 1) else .n (B - 1)) = residualProd vals (σ x) d (t + 1) := by
      split
      · rename_i h; subst h; rw [v1]; simp [residualProd, residualChain]
      · rename_i h
        obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
        have := hv (2 + 6 * u + 5) (by omega)
        rw [residualVal_blk _ _ _ _ _ (by omega)] at this
        rw [show B - 1 = b + (2 + 6 * u + 5) by omega, this]; rfl
    simp only [residualBlkT, ← hB, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with h | h | h | h | h | h <;> obtain rfl := Stmt.atom.inj h
    · show σ (.n B) = vals.getD t 0; exact w0
    · show σ (.n (B + 1)) = σ (if t = 0 then x else .n (B - 4)) + σ (.n B); rw [w1, hprev, w0]
    · show σ (.n (B + 2)) = σ (if t = 0 then x else .n (B - 4)) * σ (.n (B + 1))
      rw [w2, w1, hprev]; rfl
    · show LoadHolds rd (σ r) (t + 1) (σ (.n (B + 3))); rw [w3]; exact hd (t + 1) ht
    · show σ (.n (B + 4)) = σ (.n (B + 3)) + σ (.n (B + 2)); rw [w4, w3, w2]
    · show σ (.n (B + 5)) = σ (if t = 0 then .n (b + 1) else .n (B - 1)) * σ (.n (B + 4))
      rw [w5, w4, hpp]; rfl

end
end LeanVM.Guest.B1
