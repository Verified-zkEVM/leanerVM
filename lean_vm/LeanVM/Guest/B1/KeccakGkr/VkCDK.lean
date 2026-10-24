/-
  LeanVM.Guest.B1.KeccakGkr.VkCDK

  What the kernel checks of `verify_keccak`'s openings.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCCK

/-!
# The openings' blocks

`vkOutKer`: of the committed outputs' opening, the loads that are not stores and the residual
loads' pointers of its lane weights (`vkOutSL`) and their dot product (`vkOutDL`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- The committed outputs' lane weights. -/
abbrev vkOutSL : List Stmt := slotLanesT 3691 3711 3712 1 1

/-- The committed outputs' dot product. -/
abbrev vkOutDL : List Stmt := dotLoadsT ((List.range 25).map (slotLaneV 3712 1)) (.n 274) 30 3895

theorem vkOut_ker :
    noneIn [.load (.n 3701) (.n 3699) 0] vkSt = true ∧
    vkOutSL.all isAtom = true ∧ canonChk [] (atomsL ([] ++ vkOutSL)) = true ∧
    (resid (atomsL vkOutSL)).all (ldR [(.n 3691, 0, 6), (.n 3711, 0, 1)]) = true ∧
    noneIn (resid (atomsL vkOutSL)) vkSt = true ∧
    vkOutDL.all isAtom = true ∧ canonChk [] (atomsL ([] ++ vkOutDL)) = true ∧
    (resid (atomsL vkOutDL)).all (ldR [(.n 274, 30, 55)]) = true ∧
    noneIn (resid (atomsL vkOutDL)) vkSt = true := by
  decide +kernel

/-- The inputs' pairs: the low point's weights and the last claim's `μ`. -/
abbrev vkInPD : List Stmt := pairsDotT (.n 3987) (.n 201) (consecOffs 14 270 16) 4042

theorem vkIn_ker :
    noneIn [.load (.n 3977) (.n 201) 264] vkSt = true ∧
    noneIn (eqtreeReads (.n 9) (.n 3987) 39 3988 4) vkSt = true ∧
    vkInPD.all isAtom = true ∧ canonChk [] (atomsL ([] ++ vkInPD)) = true ∧
    (resid (atomsL vkInPD)).all (ldR [(.n 3987, 14, 30), (.n 201, 270, 286)]) = true ∧
    noneIn (resid (atomsL vkInPD)) vkSt = true := by
  decide +kernel

/-- The slices but the ring map's first challenge. -/
def slicesPre (cur : V) (capb b : ℕ) : List Stmt :=
  ((List.range 16).map fun g ↦
    (if g = 0 then [] else
      [keccakA (slCells b (g - 1) ++ cap5 (slCap capb b (g - 1)))
        ((List.range 13).map fun k ↦ .n (slP b g + k))]) ++
    ((List.range 4).map fun j ↦
      fsNextT cur (4 * g + j) (slB b (4 * g + j)) ++
        [.atom (.load (.n (slB b (4 * g + j))) (.n 10) (4 * g + j))]).flatten).flatten ++
  [keccakA (slCells b 15 ++ cap5 (slCap capb b 15)) ((List.range 13).map fun k ↦ .n (b + 835 + k))]

theorem slicesT_pre (cur : V) (capb b : ℕ) :
    slicesT cur capb b = slicesPre cur capb b ++ challengeT (.n (b + 835)) (.n (b + 836)) (b + 848) :=
  rfl

/-- The canonical values of the slices' permutations' inputs: the capacity, the reads' cells. -/
def slA : List ℕ :=
  [4117, 4118, 4119, 4120, 4121] ++ (List.range 64).flatMap fun z ↦ [slB 4122 z + 7, slB 4122 z + 9]

/-- A residual atom of the slices: a read at the cursor, or the store of a read. -/
def slRes (a : Atom) : Bool := match a with
  | .load d p off => (p == .n 4115 && decide (off < 64) && !vkSt.contains a) ||
      (p == .n 10 && decide (off < 64) && d == .n (slB 4122 off) && vkSt.contains a)
  | _ => false

theorem vkSlices_ker :
    (slicesPre (.n 4115) 4117 4122).all isAtom = true ∧
    canonChk slA (atomsL ([] ++ slicesPre (.n 4115) 4117 4122)) = true ∧
    (resid (atomsL (slicesPre (.n 4115) 4117 4122))).all slRes = true := by
  decide +kernel

/-- The inputs' lane weights. -/
abbrev vkFinSL : List Stmt := slotLanesT 4107 4978 4979 0 2

/-- The shifts of the slices. -/
abbrev vkFinFT : List Stmt := foldT (fun j ↦ 5213 + j) 5277 (.n 5212)

/-- `keccak_form`. -/
abbrev vkFinFA : List Stmt := (formAll (.n 6363) vkSh (slotLaneV 4979 2) 6364).1

theorem vkFin_ker :
    noneIn ([.load (.n 4977) (.n 201) 266, .load (.n 5212) (.n 201) 268,
      .load (.n 6363) (.n 201) 267] ++ (List.range 64).map fun z ↦ .load (.n (5213 + z)) (.n 10) z)
      vkSt = true ∧
    vkFinSL.all isAtom = true ∧ canonChk [] (atomsL ([] ++ vkFinSL)) = true ∧
    (resid (atomsL vkFinSL)).all (ldR [(.n 4107, 0, 6), (.n 4978, 0, 1)]) = true ∧
    noneIn (resid (atomsL vkFinSL)) vkSt = true ∧
    vkFinFT.all isAtom = true ∧ canonChk [] (atomsL ([] ++ vkFinFT)) = true ∧
    (resid (atomsL vkFinFT)).all (ldR [(.n 5212, 0, 6)]) = true ∧
    noneIn (resid (atomsL vkFinFT)) vkSt = true ∧
    vkFinFA.all isAtom = true ∧ canonChk [] (atomsL ([] ++ vkFinFA)) = true ∧
    (resid (atomsL vkFinFA)).all (ldR [(.n 6363, 0, 25)]) = true ∧
    noneIn (resid (atomsL vkFinFA)) vkSt = true ∧
    (formAll (.n 6363) vkSh (slotLaneV 4979 2) 6364).2.2 = 6577 := by
  decide +kernel

end
end LeanVM.Guest.B1.VerifySub
