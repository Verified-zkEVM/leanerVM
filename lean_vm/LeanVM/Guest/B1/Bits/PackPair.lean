/-
  LeanVM.Guest.B1.Bits.PackPair

  The expansion of the guest's inline `pack_pair`: two field elements as three canonical cells.
-/

module

public import LeanVM.Guest.B1.Bits.Templates

/-!
# `pack_pair` (G:507-517, TRIAGE #4)

`pack_pair(out, at, s, t)` hints two limbs of each word, derives each top limb by `y⁻¹` and packs
`(s0, s1)`, `(s2, t0)`, `(t1, t2)` into three cells with `pack64x2`. Its expansion from the value
`b` (its callers `statement_digest`, G:3787, and `da_vector_cell`, G:4050, number it) is
`packPairT s t b`: the hints at `b .. b + 3`, the cells at `b + 6`, `b + 15`, `b + 24`.

* `packPairT_sound`: the template holds only at `s`'s and `t`'s limbs, and its cells are
  `E.ofLimbs s0 s1 0`, `E.ofLimbs s2 t0 0`, `E.ofLimbs t1 t2 0`, whose bytes are
  `eBytes s ++ eBytes t` (`Node.eBytes`, N:191; `packPair_cellsBytes`).
* `packPairVals`, `packPairT_complete`: the honest values satisfy it.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- `pack_pair(out, at, s, t)`'s atoms from the value `b`. -/
def packPairT (s t : V) (b : ℕ) : List Stmt :=
  [.atom (.hint (.limbs s [.n b, .n (b + 1)])), .atom (.hint (.limbs t [.n (b + 2), .n (b + 3)])),
    .atom (.assertInK (.n b) (.n (b + 1))), .atom (.const (.n (b + 4)) (word 0 1 0)),
    .atom (.mul (.n (b + 5)) (.n (b + 4)) (.n (b + 1))), .atom (.add (.n (b + 6)) (.n b) (.n (b + 5))),
    .atom (.add (.n (b + 7)) s (.n b)), .atom (.const (.n (b + 8)) (word 1 0 1)),
    .atom (.mul (.n (b + 9)) (.n (b + 7)) (.n (b + 8))),
    .atom (.add (.n (b + 10)) (.n (b + 9)) (.n (b + 1))), .atom (.const (.n (b + 11)) (word 1 0 1)),
    .atom (.mul (.n (b + 12)) (.n (b + 10)) (.n (b + 11))),
    .atom (.assertInK (.n (b + 12)) (.n (b + 2))), .atom (.const (.n (b + 13)) (word 0 1 0)),
    .atom (.mul (.n (b + 14)) (.n (b + 13)) (.n (b + 2))),
    .atom (.add (.n (b + 15)) (.n (b + 12)) (.n (b + 14))),
    .atom (.add (.n (b + 16)) t (.n (b + 2))), .atom (.const (.n (b + 17)) (word 1 0 1)),
    .atom (.mul (.n (b + 18)) (.n (b + 16)) (.n (b + 17))),
    .atom (.add (.n (b + 19)) (.n (b + 18)) (.n (b + 3))), .atom (.const (.n (b + 20)) (word 1 0 1)),
    .atom (.mul (.n (b + 21)) (.n (b + 19)) (.n (b + 20))),
    .atom (.assertInK (.n (b + 3)) (.n (b + 21))), .atom (.const (.n (b + 22)) (word 0 1 0)),
    .atom (.mul (.n (b + 23)) (.n (b + 22)) (.n (b + 21))),
    .atom (.add (.n (b + 24)) (.n (b + 3)) (.n (b + 23)))]

/-- What `packPairT` asks of a valuation. -/
def PackPairOk (σ : Val) (s t : V) (b : ℕ) : Prop :=
  IsInK (σ (.n b)) ∧ IsInK (σ (.n (b + 1))) ∧ σ (.n (b + 4)) = word 0 1 0 ∧
    σ (.n (b + 5)) = σ (.n (b + 4)) * σ (.n (b + 1)) ∧
    σ (.n (b + 6)) = σ (.n b) + σ (.n (b + 5)) ∧ σ (.n (b + 7)) = σ s + σ (.n b) ∧
    σ (.n (b + 8)) = word 1 0 1 ∧ σ (.n (b + 9)) = σ (.n (b + 7)) * σ (.n (b + 8)) ∧
    σ (.n (b + 10)) = σ (.n (b + 9)) + σ (.n (b + 1)) ∧ σ (.n (b + 11)) = word 1 0 1 ∧
    σ (.n (b + 12)) = σ (.n (b + 10)) * σ (.n (b + 11)) ∧
    IsInK (σ (.n (b + 12))) ∧ IsInK (σ (.n (b + 2))) ∧ σ (.n (b + 13)) = word 0 1 0 ∧
    σ (.n (b + 14)) = σ (.n (b + 13)) * σ (.n (b + 2)) ∧
    σ (.n (b + 15)) = σ (.n (b + 12)) + σ (.n (b + 14)) ∧ σ (.n (b + 16)) = σ t + σ (.n (b + 2)) ∧
    σ (.n (b + 17)) = word 1 0 1 ∧ σ (.n (b + 18)) = σ (.n (b + 16)) * σ (.n (b + 17)) ∧
    σ (.n (b + 19)) = σ (.n (b + 18)) + σ (.n (b + 3)) ∧ σ (.n (b + 20)) = word 1 0 1 ∧
    σ (.n (b + 21)) = σ (.n (b + 19)) * σ (.n (b + 20)) ∧
    IsInK (σ (.n (b + 3))) ∧ IsInK (σ (.n (b + 21))) ∧ σ (.n (b + 22)) = word 0 1 0 ∧
    σ (.n (b + 23)) = σ (.n (b + 22)) * σ (.n (b + 21)) ∧
    σ (.n (b + 24)) = σ (.n (b + 3)) + σ (.n (b + 23))

theorem holds_packPairT (s t : V) (b : ℕ) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (packPairT s t b) next kret ↔ PackPairOk σ s t b ∧ next := by
  simp only [packPairT, PackPairOk, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and, and_assoc]

/-- The three cells of two words: `(s0, s1)`, `(s2, t0)`, `(t1, t2)`. -/
def packPairCells (s t : E) : List E :=
  [E.ofLimbs (s.limb 0) (s.limb 1) 0, E.ofLimbs (s.limb 2) (t.limb 0) 0,
    E.ofLimbs (t.limb 1) (t.limb 2) 0]

/-- The three cells' bytes are the two words' (`eBytes`). -/
theorem packPair_cellsBytes (s t : E) :
    Keccak.cellsBytes (packPairCells s t) = Node.eBytes s ++ Node.eBytes t := by
  simp [packPairCells, Keccak.cellsBytes, Keccak.cellBytes, Node.eBytes]

/-- **`pack_pair`** (G:507-517): the template holds only at the words' limbs, and its cells are
`packPairCells s t`. -/
theorem packPairT_sound {s t : V} {b : ℕ} (h : PackPairOk σ s t b) :
    [σ (.n (b + 6)), σ (.n (b + 15)), σ (.n (b + 24))] = packPairCells (σ s) (σ t) := by
  obtain ⟨k0, k1, h4, h5, h6, h7, h8, h9, h10, h11, h12, k12, k2, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, k3, k21, h22, h23, h24⟩ := h
  have hs : σ (.n (b + 12)) = ((σ s + σ (.n b)) * y⁻¹ + σ (.n (b + 1))) * y⁻¹ := by
    rw [h12, h11, h10, h9, h8, h7, word_y_inv]
  have ht : σ (.n (b + 21)) = ((σ t + σ (.n (b + 2))) * y⁻¹ + σ (.n (b + 3))) * y⁻¹ := by
    rw [h21, h20, h19, h18, h17, h16, word_y_inv]
  obtain ⟨es0, es1⟩ := (split3_iff (σ s) _ _).mp ⟨k0, k1, by rw [← hs]; exact k12⟩
  obtain ⟨et0, et1⟩ := (split3_iff (σ t) _ _).mp ⟨k2, k3, by rw [← ht]; exact k21⟩
  have es2 : σ (.n (b + 12)) = ofK ((σ s).limb 2) := by rw [hs, es0, es1, split3_top]
  have et2 : σ (.n (b + 21)) = ofK ((σ t).limb 2) := by rw [ht, et0, et1, split3_top]
  simp only [packPairCells, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_⟩
  · rw [h6, h5, h4, word_y, es0, es1, ofK_add_y_mul_ofK]
  · rw [h15, h14, h13, word_y, es2, et0, ofK_add_y_mul_ofK]
  · rw [h24, h23, h22, word_y, et1, et2, ofK_add_y_mul_ofK]

/-- The honest values of `packPairT` on the words `s`, `t`, by offset. -/
def packPairVals (s t : E) : ℕ → E
  | 0 => ofK (s.limb 0)
  | 1 => ofK (s.limb 1)
  | 2 => ofK (t.limb 0)
  | 3 => ofK (t.limb 1)
  | 4 => word 0 1 0
  | 5 => word 0 1 0 * ofK (s.limb 1)
  | 6 => ofK (s.limb 0) + word 0 1 0 * ofK (s.limb 1)
  | 7 => s + ofK (s.limb 0)
  | 8 => word 1 0 1
  | 9 => (s + ofK (s.limb 0)) * word 1 0 1
  | 10 => (s + ofK (s.limb 0)) * word 1 0 1 + ofK (s.limb 1)
  | 11 => word 1 0 1
  | 12 => ofK (s.limb 2)
  | 13 => word 0 1 0
  | 14 => word 0 1 0 * ofK (t.limb 0)
  | 15 => ofK (s.limb 2) + word 0 1 0 * ofK (t.limb 0)
  | 16 => t + ofK (t.limb 0)
  | 17 => word 1 0 1
  | 18 => (t + ofK (t.limb 0)) * word 1 0 1
  | 19 => (t + ofK (t.limb 0)) * word 1 0 1 + ofK (t.limb 1)
  | 20 => word 1 0 1
  | 21 => ofK (t.limb 2)
  | 22 => word 0 1 0
  | 23 => word 0 1 0 * ofK (t.limb 2)
  | _ => ofK (t.limb 1) + word 0 1 0 * ofK (t.limb 2)

/-- **The honest values satisfy `pack_pair`.** -/
theorem packPairOk_of_vals {s t : V} {b : ℕ}
    (h : ∀ i < 25, σ (.n (b + i)) = packPairVals (σ s) (σ t) i) : PackPairOk σ s t b := by
  have e : ∀ i, i < 25 → σ (.n (b + i)) = packPairVals (σ s) (σ t) i := h
  have e0 : σ (.n b) = ofK ((σ s).limb 0) := e 0 (by omega)
  have e1 := e 1 (by omega)
  have e2 := e 2 (by omega)
  have e3 := e 3 (by omega)
  have e4 := e 4 (by omega)
  have e5 := e 5 (by omega)
  have e6 := e 6 (by omega)
  have e7 := e 7 (by omega)
  have e8 := e 8 (by omega)
  have e9 := e 9 (by omega)
  have e10 := e 10 (by omega)
  have e11 := e 11 (by omega)
  have e12 := e 12 (by omega)
  have e13 := e 13 (by omega)
  have e14 := e 14 (by omega)
  have e15 := e 15 (by omega)
  have e16 := e 16 (by omega)
  have e17 := e 17 (by omega)
  have e18 := e 18 (by omega)
  have e19 := e 19 (by omega)
  have e20 := e 20 (by omega)
  have e21 := e 21 (by omega)
  have e22 := e 22 (by omega)
  have e23 := e 23 (by omega)
  have e24 := e 24 (by omega)
  simp only [packPairVals] at e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24
  have top_s : ((σ s + ofK ((σ s).limb 0)) * word 1 0 1 + ofK ((σ s).limb 1)) * word 1 0 1 =
      ofK ((σ s).limb 2) := by rw [word_y_inv, split3_top]
  have top_t : ((σ t + ofK ((σ t).limb 0)) * word 1 0 1 + ofK ((σ t).limb 1)) * word 1 0 1 =
      ofK ((σ t).limb 2) := by rw [word_y_inv, split3_top]
  refine ⟨by rw [e0]; exact ofK_isInK _, by rw [e1]; exact ofK_isInK _, e4, by rw [e5, e4, e1],
    by rw [e6, e0, e5], by rw [e7, e0], e8, by rw [e9, e8, e7], by rw [e10, e9, e1], e11,
    by rw [e12, e11, e10, top_s], by rw [e12]; exact ofK_isInK _, by rw [e2]; exact ofK_isInK _,
    e13, by rw [e14, e13, e2], by rw [e15, e12, e14], by rw [e16, e2], e17,
    by rw [e18, e17, e16], by rw [e19, e18, e3], e20, by rw [e21, e20, e19, top_t],
    by rw [e3]; exact ofK_isInK _, by rw [e21]; exact ofK_isInK _, e22, by rw [e23, e22, e21],
    by rw [e24, e3, e23]⟩

end
end LeanVM.Guest.B1
