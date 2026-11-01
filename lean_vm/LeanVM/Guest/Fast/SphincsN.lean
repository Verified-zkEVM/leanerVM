module

public import LeanVM.Guest.B1.Sig.SphincsFoldArms
public import LeanVM.Guest.B1.Sig.SphincsSub
public import LeanVM.Guest.Fast.Numbers

/-!
# leanSPHINCS's forest positions, as numbers

The cells a coordinate's opening is read at (`subVal`, `subSib`, `topSib`,
`B1/Sig/SphincsForest.lean`) are bases of the forest keys' and the folds' arms (`fkAB`, `foAB`),
computed by template generators. Here they are arithmetic:

* `fkChainN`, `fkChainsN`, `fkABN` (`Fast/Numbers.lean`): a forest key's chains and the arms' bases
  (`fkChains_eq`, `fkAB_eq`), translated (`fkChainsN_shift`, `fkABN_shift`): chain `i` of arm `t`
  from base `B` is at `B + fkOffN t i`;
* `foldPos first rest b a`: the base of a fold's arm `a`, its first arm `first` cells, the others
  `rest` (`foAB_eq`), for a fold whose levels all take `d` cells (`subAdr`: `16`, `coordAdr`:
  `17`).
-/

namespace LeanVM.Guest.Fast

open LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1.Sig

@[expose] public section

/-! ## The forest keys -/

theorem fkChain_eq (t i : ℕ) (keyAt : V) (b : ℕ) : (fkChain t i keyAt b).2.1 = fkChainN t i b := by
  unfold fkChain fkChainN
  simp only
  split
  · rfl
  · split <;> rfl

theorem fkChains_eq (t : ℕ) (keyAt : V) : ∀ (m i b : ℕ),
    (fkChains t keyAt m i b).2.1 = fkChainsN t m i b
  | 0, _, _ => rfl
  | m + 1, i, b => by
      simp only [fkChains]
      rw [fkChains_eq t keyAt m (i + 1), fkChain_eq]
      rfl

theorem fkAB_eq (w : ℕ) (keyAt : V) (b : ℕ) : ∀ t, fkAB w keyAt b t = fkABN t b
  | 0 => rfl
  | t + 1 => by
      rcases Nat.eq_zero_or_pos t with rfl | ht
      · rw [fkAB_one, fkArm_snd, fkChains_eq]; rfl
      · rw [fkAB_succ ht, fkArm_snd, fkChains_eq, fkAB_eq w keyAt b t, fkABN]
        simp [show t ≠ 0 by omega]

theorem fkChainN_shift (t i b : ℕ) : fkChainN t i b = b + fkChainN t i 0 := by
  unfold fkChainN; split
  · omega
  · split <;> omega

theorem fkChainsN_shift (t : ℕ) : ∀ (m i b : ℕ), fkChainsN t m i b = b + fkChainsN t m i 0
  | 0, _, _ => by simp [fkChainsN]
  | m + 1, i, b => by
      rw [fkChainsN, fkChainsN, fkChainsN_shift t m (i + 1), fkChainN_shift,
        fkChainsN_shift t m (i + 1) (fkChainN t i 0)]
      omega

theorem fkABN_shift : ∀ (t b : ℕ), fkABN t b = b + fkABN t 0
  | 0, _ => by simp [fkABN]
  | t + 1, b => by
      rw [fkABN, fkABN, fkChainsN_shift, fkABN_shift t b,
        fkChainsN_shift t 6 0 (fkABN t 0)]
      omega

/-- **Chain `i` of arm `t`**, the arms from `B` (`fkCB` at `fkAB`). -/
theorem fkCB_fkAB (w t i B : ℕ) (keyAt : V) :
    fkCB t keyAt 0 (fkAB w keyAt B t) i = B + fkOffN t i := by
  unfold fkCB fkOffN
  rw [fkChains_eq, fkAB_eq, fkChainsN_shift, fkABN_shift t B, fkChainsN_shift t i 0 (fkABN t 0)]
  omega

/-! ## The folds -/

theorem flBase_const {adr : ℕ → Sum V ℕ} {d : ℕ} (h : ∀ l b, flNext adr l b = b + d) :
    ∀ (l m b : ℕ), flBase adr l m b = b + d * m
  | _, 0, _ => by simp [flBase]
  | l, m + 1, b => by
      rw [flBase, flBase_const h (l + 1) m, h]
      ring

theorem foAB_eq {atV node0 markV : V} {adr : ℕ → ℕ → Sum V ℕ} {height : ℕ} {markC wC : ℕ → E}
    {d : ℕ} (h : ∀ a l b, flNext (adr a) l b = b + d) (b : ℕ) : ∀ a,
    foAB atV adr height node0 markV markC wC b a =
      foldPos (d * (height - 1) + 3) (d * (height - 1)) b a
  | 0 => rfl
  | a + 1 => by
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · rw [foAB_one, foldArm_snd, foldLevels_snd, flBase_const (h 0)]
        simp [foldPos]; omega
      · rw [foAB_succ ha, foldArm_snd, foldLevels_snd, flBase_const (h a), foAB_eq h b a]
        simp [foldPos, show a ≠ 0 by omega]
        rw [show a = a - 1 + 1 by omega, Nat.mul_succ]
        simp only [Nat.add_sub_cancel]
        ring

theorem flNext_subAdr (a l b : ℕ) : flNext (subAdr a) l b = b + 16 := rfl

theorem flNext_coordAdr (s l b : ℕ) : flNext (coordAdr s) l b = b + 17 := rfl

end
end LeanVM.Guest.Fast
