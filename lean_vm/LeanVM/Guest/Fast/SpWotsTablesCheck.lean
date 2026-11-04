module

public import LeanVM.Guest.Fast.SpWotsStarts
public import LeanVM.Guest.Fast.SpWotsTables
public import LeanVM.Guest.Fast.Numbers

/-!
# `sp_wots`' chain starts are the literal tables', by evaluation

* `spState_p`: group `p`'s running product's and encoding's cells and its base (`spState`,
  `B1/Sig/SpWotsLayout.lean`), the kernel evaluating one group's arms at a time (`spState (p + 1)`
  from `spState p`);
* `spGroupStarts_p`: group `p`'s arms' starts (`spArmsStarts`, `Fast/SpWotsStarts.lean`, one pass
  over its arms) are its selector cell plus the literal table's (`spSel`, `spTabOf`,
  `Fast/SpWotsTables.lean`);
* combined: `spSel_eq` (the selectors are the groups' bases) and `spGroupStarts`.

The whole module checks in about `10` seconds. It imports the templates and the tables alone
(`Fast/Firewall.lean`).
-/

namespace LeanVM.Guest.Fast

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.B1.Sig

public section

theorem spState_0 : spState 0 = (.n 0, .n 0, 13) := rfl

theorem spState_1 : spState 1 = (V.n 171, V.n 172, 1587) := by decide +kernel

theorem spState_2 : spState 2 = (V.n 1744, V.n 1745, 3097) := by
  rw [show (2 : Nat) = 1 + 1 from rfl, spState, spState_1]
  decide +kernel

theorem spState_3 : spState 3 = (V.n 3254, V.n 3255, 4607) := by
  rw [show (3 : Nat) = 2 + 1 from rfl, spState, spState_2]
  decide +kernel

theorem spState_4 : spState 4 = (V.n 4764, V.n 4765, 6117) := by
  rw [show (4 : Nat) = 3 + 1 from rfl, spState, spState_3]
  decide +kernel

theorem spState_5 : spState 5 = (V.n 6274, V.n 6275, 7627) := by
  rw [show (5 : Nat) = 4 + 1 from rfl, spState, spState_4]
  decide +kernel

theorem spState_6 : spState 6 = (V.n 7784, V.n 7785, 9137) := by
  rw [show (6 : Nat) = 5 + 1 from rfl, spState, spState_5]
  decide +kernel

theorem spState_7 : spState 7 = (V.n 9294, V.n 9295, 10647) := by
  rw [show (7 : Nat) = 6 + 1 from rfl, spState, spState_6]
  decide +kernel

theorem spState_8 : spState 8 = (V.n 10804, V.n 10805, 12157) := by
  rw [show (8 : Nat) = 7 + 1 from rfl, spState, spState_7]
  decide +kernel

theorem spState_9 : spState 9 = (V.n 12314, V.n 12315, 13667) := by
  rw [show (9 : Nat) = 8 + 1 from rfl, spState, spState_8]
  decide +kernel

theorem spState_10 : spState 10 = (V.n 13824, V.n 13825, 15177) := by
  rw [show (10 : Nat) = 9 + 1 from rfl, spState, spState_9]
  decide +kernel

theorem spState_11 : spState 11 = (V.n 15334, V.n 15335, 16687) := by
  rw [show (11 : Nat) = 10 + 1 from rfl, spState, spState_10]
  decide +kernel

theorem spState_12 : spState 12 = (V.n 16844, V.n 16845, 18197) := by
  rw [show (12 : Nat) = 11 + 1 from rfl, spState, spState_11]
  decide +kernel

theorem spState_13 : spState 13 = (V.n 18354, V.n 18355, 19707) := by
  rw [show (13 : Nat) = 12 + 1 from rfl, spState, spState_12]
  decide +kernel

theorem spState_14 : spState 14 = (V.n 19864, V.n 19865, 21217) := by
  rw [show (14 : Nat) = 13 + 1 from rfl, spState, spState_13]
  decide +kernel

theorem spState_15 : spState 15 = (V.n 21374, V.n 21375, 22727) := by
  rw [show (15 : Nat) = 14 + 1 from rfl, spState, spState_14]
  decide +kernel

theorem spState_16 : spState 16 = (V.n 22884, V.n 22885, 24237) := by
  rw [show (16 : Nat) = 15 + 1 from rfl, spState, spState_15]
  decide +kernel

theorem spState_17 : spState 17 = (V.n 24394, V.n 24395, 25747) := by
  rw [show (17 : Nat) = 16 + 1 from rfl, spState, spState_16]
  decide +kernel

theorem spState_18 : spState 18 = (V.n 25904, V.n 25905, 27257) := by
  rw [show (18 : Nat) = 17 + 1 from rfl, spState, spState_17]
  decide +kernel

theorem spState_19 : spState 19 = (V.n 27414, V.n 27415, 28767) := by
  rw [show (19 : Nat) = 18 + 1 from rfl, spState, spState_18]
  decide +kernel

theorem spState_20 : spState 20 = (V.n 28924, V.n 28925, 30277) := by
  rw [show (20 : Nat) = 19 + 1 from rfl, spState, spState_19]
  decide +kernel

theorem spState_21 : spState 21 = (V.n 30434, V.n 30435, 31787) := by
  rw [show (21 : Nat) = 20 + 1 from rfl, spState, spState_20]
  decide +kernel

theorem spState_22 : spState 22 = (V.n 31944, V.n 31945, 33297) := by
  rw [show (22 : Nat) = 21 + 1 from rfl, spState, spState_21]
  decide +kernel

/-- Group `0`'s arms' starts: its selector plus the table's. -/
theorem spGroupStarts_0 :
    spArmsStarts 0 (V.n 0, V.n 0, 13) (4 ^ spN 0) 0 ((V.n 0, V.n 0, 13).2.2 + 5) =
      (List.range (4 ^ spN 0)).map fun k ↦ (List.range (spN 0)).map fun r ↦
        V.n (spSel.getD 0 0 + offAt (spTabOf 0) r k) := by
  decide +kernel

/-- Group `1`'s arms' starts: its selector plus the table's. -/
theorem spGroupStarts_1 :
    spArmsStarts 1 (V.n 171, V.n 172, 1587) (4 ^ spN 1) 0 ((V.n 171, V.n 172, 1587).2.2 + 5) =
      (List.range (4 ^ spN 1)).map fun k ↦ (List.range (spN 1)).map fun r ↦
        V.n (spSel.getD 1 0 + offAt (spTabOf 1) r k) := by
  decide +kernel

/-- Group `2`'s arms' starts: its selector plus the table's. -/
theorem spGroupStarts_2 :
    spArmsStarts 2 (V.n 1744, V.n 1745, 3097) (4 ^ spN 2) 0 ((V.n 1744, V.n 1745, 3097).2.2 + 5) =
      (List.range (4 ^ spN 2)).map fun k ↦ (List.range (spN 2)).map fun r ↦
        V.n (spSel.getD 2 0 + offAt (spTabOf 2) r k) := by
  decide +kernel

/-- Group `3`'s arms' starts: its selector plus the table's. -/
theorem spGroupStarts_3 :
    spArmsStarts 3 (V.n 3254, V.n 3255, 4607) (4 ^ spN 3) 0 ((V.n 3254, V.n 3255, 4607).2.2 + 5) =
      (List.range (4 ^ spN 3)).map fun k ↦ (List.range (spN 3)).map fun r ↦
        V.n (spSel.getD 3 0 + offAt (spTabOf 3) r k) := by
  decide +kernel

/-- Group `4`'s arms' starts: its selector plus the table's. -/
theorem spGroupStarts_4 :
    spArmsStarts 4 (V.n 4764, V.n 4765, 6117) (4 ^ spN 4) 0 ((V.n 4764, V.n 4765, 6117).2.2 + 5) =
      (List.range (4 ^ spN 4)).map fun k ↦ (List.range (spN 4)).map fun r ↦
        V.n (spSel.getD 4 0 + offAt (spTabOf 4) r k) := by
  decide +kernel

/-- Group `5`'s arms' starts: its selector plus the table's. -/
theorem spGroupStarts_5 :
    spArmsStarts 5 (V.n 6274, V.n 6275, 7627) (4 ^ spN 5) 0 ((V.n 6274, V.n 6275, 7627).2.2 + 5) =
      (List.range (4 ^ spN 5)).map fun k ↦ (List.range (spN 5)).map fun r ↦
        V.n (spSel.getD 5 0 + offAt (spTabOf 5) r k) := by
  decide +kernel

/-- Group `6`'s arms' starts: its selector plus the table's. -/
theorem spGroupStarts_6 :
    spArmsStarts 6 (V.n 7784, V.n 7785, 9137) (4 ^ spN 6) 0 ((V.n 7784, V.n 7785, 9137).2.2 + 5) =
      (List.range (4 ^ spN 6)).map fun k ↦ (List.range (spN 6)).map fun r ↦
        V.n (spSel.getD 6 0 + offAt (spTabOf 6) r k) := by
  decide +kernel

/-- Group `7`'s arms' starts: its selector plus the table's. -/
theorem spGroupStarts_7 :
    spArmsStarts 7 (V.n 9294, V.n 9295, 10647) (4 ^ spN 7) 0 ((V.n 9294, V.n 9295, 10647).2.2 + 5) =
      (List.range (4 ^ spN 7)).map fun k ↦ (List.range (spN 7)).map fun r ↦
        V.n (spSel.getD 7 0 + offAt (spTabOf 7) r k) := by
  decide +kernel

/-- Group `8`'s arms' starts: its selector plus the table's. -/
theorem spGroupStarts_8 :
    spArmsStarts 8 (V.n 10804, V.n 10805, 12157) (4 ^ spN 8) 0 ((V.n 10804, V.n 10805, 12157).2.2 + 5) =
      (List.range (4 ^ spN 8)).map fun k ↦ (List.range (spN 8)).map fun r ↦
        V.n (spSel.getD 8 0 + offAt (spTabOf 8) r k) := by
  decide +kernel

/-- Group `9`'s arms' starts: its selector plus the table's. -/
theorem spGroupStarts_9 :
    spArmsStarts 9 (V.n 12314, V.n 12315, 13667) (4 ^ spN 9) 0 ((V.n 12314, V.n 12315, 13667).2.2 + 5) =
      (List.range (4 ^ spN 9)).map fun k ↦ (List.range (spN 9)).map fun r ↦
        V.n (spSel.getD 9 0 + offAt (spTabOf 9) r k) := by
  decide +kernel

/-- Group `10`'s arms' starts: its selector plus the table's. -/
theorem spGroupStarts_10 :
    spArmsStarts 10 (V.n 13824, V.n 13825, 15177) (4 ^ spN 10) 0 ((V.n 13824, V.n 13825, 15177).2.2 + 5) =
      (List.range (4 ^ spN 10)).map fun k ↦ (List.range (spN 10)).map fun r ↦
        V.n (spSel.getD 10 0 + offAt (spTabOf 10) r k) := by
  decide +kernel

/-- Group `11`'s arms' starts: its selector plus the table's. -/
theorem spGroupStarts_11 :
    spArmsStarts 11 (V.n 15334, V.n 15335, 16687) (4 ^ spN 11) 0 ((V.n 15334, V.n 15335, 16687).2.2 + 5) =
      (List.range (4 ^ spN 11)).map fun k ↦ (List.range (spN 11)).map fun r ↦
        V.n (spSel.getD 11 0 + offAt (spTabOf 11) r k) := by
  decide +kernel

/-- Group `12`'s arms' starts: its selector plus the table's. -/
theorem spGroupStarts_12 :
    spArmsStarts 12 (V.n 16844, V.n 16845, 18197) (4 ^ spN 12) 0 ((V.n 16844, V.n 16845, 18197).2.2 + 5) =
      (List.range (4 ^ spN 12)).map fun k ↦ (List.range (spN 12)).map fun r ↦
        V.n (spSel.getD 12 0 + offAt (spTabOf 12) r k) := by
  decide +kernel

/-- Group `13`'s arms' starts: its selector plus the table's. -/
theorem spGroupStarts_13 :
    spArmsStarts 13 (V.n 18354, V.n 18355, 19707) (4 ^ spN 13) 0 ((V.n 18354, V.n 18355, 19707).2.2 + 5) =
      (List.range (4 ^ spN 13)).map fun k ↦ (List.range (spN 13)).map fun r ↦
        V.n (spSel.getD 13 0 + offAt (spTabOf 13) r k) := by
  decide +kernel

/-- Group `14`'s arms' starts: its selector plus the table's. -/
theorem spGroupStarts_14 :
    spArmsStarts 14 (V.n 19864, V.n 19865, 21217) (4 ^ spN 14) 0 ((V.n 19864, V.n 19865, 21217).2.2 + 5) =
      (List.range (4 ^ spN 14)).map fun k ↦ (List.range (spN 14)).map fun r ↦
        V.n (spSel.getD 14 0 + offAt (spTabOf 14) r k) := by
  decide +kernel

/-- Group `15`'s arms' starts: its selector plus the table's. -/
theorem spGroupStarts_15 :
    spArmsStarts 15 (V.n 21374, V.n 21375, 22727) (4 ^ spN 15) 0 ((V.n 21374, V.n 21375, 22727).2.2 + 5) =
      (List.range (4 ^ spN 15)).map fun k ↦ (List.range (spN 15)).map fun r ↦
        V.n (spSel.getD 15 0 + offAt (spTabOf 15) r k) := by
  decide +kernel

/-- Group `16`'s arms' starts: its selector plus the table's. -/
theorem spGroupStarts_16 :
    spArmsStarts 16 (V.n 22884, V.n 22885, 24237) (4 ^ spN 16) 0 ((V.n 22884, V.n 22885, 24237).2.2 + 5) =
      (List.range (4 ^ spN 16)).map fun k ↦ (List.range (spN 16)).map fun r ↦
        V.n (spSel.getD 16 0 + offAt (spTabOf 16) r k) := by
  decide +kernel

/-- Group `17`'s arms' starts: its selector plus the table's. -/
theorem spGroupStarts_17 :
    spArmsStarts 17 (V.n 24394, V.n 24395, 25747) (4 ^ spN 17) 0 ((V.n 24394, V.n 24395, 25747).2.2 + 5) =
      (List.range (4 ^ spN 17)).map fun k ↦ (List.range (spN 17)).map fun r ↦
        V.n (spSel.getD 17 0 + offAt (spTabOf 17) r k) := by
  decide +kernel

/-- Group `18`'s arms' starts: its selector plus the table's. -/
theorem spGroupStarts_18 :
    spArmsStarts 18 (V.n 25904, V.n 25905, 27257) (4 ^ spN 18) 0 ((V.n 25904, V.n 25905, 27257).2.2 + 5) =
      (List.range (4 ^ spN 18)).map fun k ↦ (List.range (spN 18)).map fun r ↦
        V.n (spSel.getD 18 0 + offAt (spTabOf 18) r k) := by
  decide +kernel

/-- Group `19`'s arms' starts: its selector plus the table's. -/
theorem spGroupStarts_19 :
    spArmsStarts 19 (V.n 27414, V.n 27415, 28767) (4 ^ spN 19) 0 ((V.n 27414, V.n 27415, 28767).2.2 + 5) =
      (List.range (4 ^ spN 19)).map fun k ↦ (List.range (spN 19)).map fun r ↦
        V.n (spSel.getD 19 0 + offAt (spTabOf 19) r k) := by
  decide +kernel

/-- Group `20`'s arms' starts: its selector plus the table's. -/
theorem spGroupStarts_20 :
    spArmsStarts 20 (V.n 28924, V.n 28925, 30277) (4 ^ spN 20) 0 ((V.n 28924, V.n 28925, 30277).2.2 + 5) =
      (List.range (4 ^ spN 20)).map fun k ↦ (List.range (spN 20)).map fun r ↦
        V.n (spSel.getD 20 0 + offAt (spTabOf 20) r k) := by
  decide +kernel

/-- Group `21`'s arms' starts: its selector plus the table's. -/
theorem spGroupStarts_21 :
    spArmsStarts 21 (V.n 30434, V.n 30435, 31787) (4 ^ spN 21) 0 ((V.n 30434, V.n 30435, 31787).2.2 + 5) =
      (List.range (4 ^ spN 21)).map fun k ↦ (List.range (spN 21)).map fun r ↦
        V.n (spSel.getD 21 0 + offAt (spTabOf 21) r k) := by
  decide +kernel

/-- **The selectors are the groups' bases.** -/
theorem spSel_eq : ∀ p < 22, spSel.getD p 0 = (spState p).2.2 := by
  intro p hp
  interval_cases p <;> simp only [spState_0, spState_1, spState_2, spState_3, spState_4, spState_5,
    spState_6, spState_7, spState_8, spState_9, spState_10, spState_11, spState_12, spState_13,
    spState_14, spState_15, spState_16, spState_17, spState_18, spState_19, spState_20,
    spState_21] <;> rfl

/-- **Group `p`'s arms' starts**: its selector plus its table's. -/
theorem spGroupStarts (p : Nat) (hp : p < 22) :
    spArmsStarts p (spState p) (4 ^ spN p) 0 ((spState p).2.2 + 5) =
      (List.range (4 ^ spN p)).map fun k ↦ (List.range (spN p)).map fun r ↦
        V.n (spSel.getD p 0 + offAt (spTabOf p) r k) := by
  interval_cases p
  · rw [spState_0]; exact spGroupStarts_0
  · rw [spState_1]; exact spGroupStarts_1
  · rw [spState_2]; exact spGroupStarts_2
  · rw [spState_3]; exact spGroupStarts_3
  · rw [spState_4]; exact spGroupStarts_4
  · rw [spState_5]; exact spGroupStarts_5
  · rw [spState_6]; exact spGroupStarts_6
  · rw [spState_7]; exact spGroupStarts_7
  · rw [spState_8]; exact spGroupStarts_8
  · rw [spState_9]; exact spGroupStarts_9
  · rw [spState_10]; exact spGroupStarts_10
  · rw [spState_11]; exact spGroupStarts_11
  · rw [spState_12]; exact spGroupStarts_12
  · rw [spState_13]; exact spGroupStarts_13
  · rw [spState_14]; exact spGroupStarts_14
  · rw [spState_15]; exact spGroupStarts_15
  · rw [spState_16]; exact spGroupStarts_16
  · rw [spState_17]; exact spGroupStarts_17
  · rw [spState_18]; exact spGroupStarts_18
  · rw [spState_19]; exact spGroupStarts_19
  · rw [spState_20]; exact spGroupStarts_20
  · rw [spState_21]; exact spGroupStarts_21

end
end LeanVM.Guest.Fast
