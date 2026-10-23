/-
  LeanVM.Guest.B1.Sig.SphincsCoordsComplete

  The eight coordinates of `verify_sig_lean_sphincs`'s forest complete in a row, the running
  encoding and bound the sums of their hints' terms, the last checking the digest's cells.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsCoordComplete
public import LeanVM.Guest.B1.Sig.SphincsCoords

/-!
# The coordinates, complete

* `cSt_shape`: each coordinate's base is past `206`, its running encoding's and bound's cells
  below it;
* `sCoords_complete`: coordinates `c ..< c + m` complete from a valuation agreeing below `206` with
  `σ`, the running sums the hints' terms so far, the digest's cells the full sums.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

attribute [local irreducible] fkArms foldArms sSubtree sCoord

variable {C : CallRel} {rd : Reader}

theorem cSt_shape : ∀ c, 206 ≤ (cSt c).2.2 ∧ (∀ en, (cSt c).1 = some en → NBv (cSt c).2.2 en) ∧
    NBv (cSt c).2.2 (cSt c).2.1 ∧ (0 < c → ∃ en, (cSt c).1 = some en)
  | 0 => ⟨le_rfl, fun en h => by simp [cSt] at h, ⟨161, by simp [cSt], rfl⟩, fun h => absurd h (by omega)⟩
  | c + 1 => by
      obtain ⟨h1, h2, h3, -⟩ := cSt_shape c
      obtain ⟨s1, ⟨k, ek, hk⟩, ⟨k', ek', hk'⟩, -⟩ := sCoord_shape c (enc := (cSt c).1) (bound := (cSt c).2.1)
        (b := (cSt c).2.2) h1 h2 h3
      refine ⟨by simp only [cSt]; omega, fun en he => ?_, ?_, fun _ => ⟨_, rfl⟩⟩
      · simp only [cSt, Option.some.injEq] at he
        rw [← he, ek]; exact ⟨k, hk, rfl⟩
      · simp only [cSt]; rw [ek']; exact ⟨k', hk', rfl⟩

theorem cSt_step (c : Nat) : (cSt c).2.2 + 20 ≤ (cSt (c + 1)).2.2 := by
  obtain ⟨b1, b2, b3, -⟩ := cSt_shape c
  exact (sCoord_shape c b1 b2 b3).1

theorem cSt_mono (c : Nat) : ∀ m, (cSt c).2.2 ≤ (cSt (c + m)).2.2
  | 0 => le_rfl
  | m + 1 => le_trans (cSt_mono c m) (le_trans (Nat.le_add_right _ 20) (cSt_step (c + m)))

/-- **The coordinates complete**, their hints `H` loaded, the running sums the hints' terms. -/
theorem sCoords_complete (hm : MemOK rd 256) (H : Nat → CoordH) (hH : ∀ c < 8, (H c).OK) (σ : Val)
    (hX : ForestX σ) (hn0 : IsCanonical128 (σ (sNode 0)))
    (h17 : σ (.n 17) = ∑ k ∈ Finset.range 8, hEnc k (H k))
    (h18 : σ (.n 18) = σ (.n 161) + ∑ k ∈ Finset.range 8, hBound k (H k)) :
    ∀ m c, c + m = 8 → ∀ σc : Val, (∀ k < 206, σc (.n k) = σ (.n k)) →
      encVal σc (cSt c).1 = ∑ k ∈ Finset.range c, hEnc k (H k) →
      σc (cSt c).2.1 = σ (.n 161) + ∑ k ∈ Finset.range c, hBound k (H k) →
      Completes C rd (cSt c).2.2 (cSt (c + m)).2.2 (sCoords m c (cSt c).1 (cSt c).2.1 (cSt c).2.2).1 σc
        (fun σ' => ∀ σ'', AgreeBelow (cSt (c + m)).2.2 σ' σ'' → ∀ k, c ≤ k → k < c + m →
          CoordPost (∑ i ∈ Finset.range k, hEnc i (H i)) (σ (.n 161) + ∑ i ∈ Finset.range k, hBound i (H i))
            k (cSt k).1 (cSt k).2.1 (cSt k).2.2 (H k) σ'')
  | 0, c, _, σc, _, _, _ => ⟨σc, Ext.refl _ _ _, fun _ _ k h1 h2 => absurd h2 (by omega), fun _ _ hn => hn⟩
  | m + 1, c, hcm, σc, hag, he, hb => by
      obtain ⟨b1, b2, b3, b4⟩ := cSt_shape c
      obtain ⟨s1, -, -, snb⟩ := sCoord_shape c b1 b2 b3
      have hagX : AgreeBelow 206 σ σc := fun k hk => (hag k hk).symm
      have hcoord := sCoord_complete (C := C) (rd := rd) (c := c) (enc := (cSt c).1) (bound := (cSt c).2.1)
        (b := (cSt c).2.2) b1 b2 b3 hm (H c) (hH c (by omega)) σc (hX.congr le_rfl hagX)
        (by rw [show sNode 0 = V.n 131 from rfl, hag 131 (by omega)]; exact hn0)
        (fun hl => by
          refine ⟨b4 (by omega), ?_, ?_⟩
          · rw [hag 17 (by omega), h17, he, show (8 : Nat) = c + 1 by omega, Finset.sum_range_succ]
          · rw [hag 18 (by omega), h18, hb, show (8 : Nat) = c + 1 by omega, Finset.sum_range_succ, add_assoc])
      rw [sCoords_cons]
      refine Completes.append (m := (cSt (c + 1)).2.2) (by simp only [cSt]; omega)
        (by rw [show c + (m + 1) = c + 1 + m by omega]; exact cSt_mono (c + 1) m)
        snb hcoord (fun σ1 he1 hp1 => ?_)
      rw [he, hb] at hp1
      have hq := hp1 σ1 (fun _ _ => rfl)
      have hq1 := hq.2.2.2.2.2.2.2.2.1
      have hq2 := hq.2.2.2.2.2.2.2.2.2
      obtain ⟨σ2, he2, hp2, hh2⟩ := sCoords_complete hm H hH σ hX hn0 h17 h18 m (c + 1) (by omega) σ1
        (fun k hk => by rw [he1.apply (Or.inl (by omega)), hag k hk])
        (by show σ1 (sCoord c (cSt c).1 (cSt c).2.1 (cSt c).2.2).2.2.1 = _
            rw [hq1, Finset.sum_range_succ])
        (by show σ1 (sCoord c (cSt c).1 (cSt c).2.1 (cSt c).2.2).2.2.2.1 = _
            rw [hq2, Finset.sum_range_succ, add_assoc])
      rw [show c + (m + 1) = c + 1 + m by omega]
      refine ⟨σ2, he2, fun σ'' hag2 k h1 h2 => ?_, hh2⟩
      by_cases hk : k = c
      · subst hk
        exact hp1 σ'' (fun j hj => by
          show σ1 (.n j) = σ'' (.n j)
          rw [he2.agree j hj]
          exact hag2 j (lt_of_lt_of_le hj (cSt_mono (k + 1) m)))
      · exact hp2 σ'' hag2 k (by omega) h2

end
end LeanVM.Guest.B1.Sig
