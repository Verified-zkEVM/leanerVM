/-
  LeanVM.Guest.B1.Sig.SphincsBridgePath

  The statement's leanSPHINCS tree fold (`Sphincs.Verification.treeFold`, over Keccak-f[1600] in
  `Id`) is the fold of `sp_path`'s nodes over cells (`tNode`, `pFold`).
-/

module

public import LeanVM.Guest.B1.Sig.SphincsPathComplete
public import LeanVM.Guest.B1.Sig.SphincsHash

/-!
# The tree fold over cells

* `laneCell layer tree`: the high lane of the tree's addresses, the key address cell of leaf `0`;
  `keyAddressCell_lane`: a key's address cell is the lane plus its leaf;
* `nodeAdr_bytes`: the address of a tree node is the bytes of `tAdr`;
* `sTreeFold_cells`: `treeFold` from the leaf `e`, siblings `path` with `cellVal (sib l) = path l`,
  from the value of the cell `x`, is the value of `pFold (tNode pp (laneCell layer tree) e sib) h x`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat kToNat)
open HashSig HashSig.OverPermutation

@[expose] public section

/-- The high lane of the addresses of tree `tree` of layer `layer`: the key address cell of leaf
`0`. -/
def laneCell (layer : Sphincs.Layer) (tree : Sphincs.TreeIndex) : E :=
  keyAddressCell layer tree ⟨0, by decide⟩

theorem keyAddressCell_lane (layer : Sphincs.Layer) (tree : Sphincs.TreeIndex) (leaf : Sphincs.TreeLeafIndex) :
    keyAddressCell layer tree leaf = laneCell layer tree + eOfNat leaf.val := by
  have hl : leaf.val < 2 ^ 64 := lt_of_lt_of_le leaf.isLt (by decide)
  rw [laneCell, keyAddressCell_eq, keyAddressCell_eq, ← eOfNat192_of_lt hl, ← eOfNat192_xor]
  congr 1
  simp only [keyNat, Nat.zero_add]
  have h2 := two_pow_mul_xor (s := 64) (q := layer.val + 2 ^ 8 * tree.val) hl
  rw [h2, Nat.add_comm]

/-- **A tree node's address is `tAdr`'s bytes.** -/
theorem nodeAdr_bytes (layer : Sphincs.Layer) (tree : Sphincs.TreeIndex) {l q : Nat} (hl : l + 1 < 2 ^ 24)
    (hq : q < 2 ^ 10) :
    addressBytes (Sphincs.hashDomainFields (.node layer tree (l + 1) q)) =
      cellBytes (tAdr (laneCell layer tree) l q) := by
  have hkey := keyAddress_bytes (layer := layer) (tree := tree) (leaf := ⟨q, by simpa [Sphincs.layerHeight,
    Sphincs.topLayer] using hq⟩) (tag := 3) (step := 0) (hi := l + 1) (by norm_num) (by norm_num) hl
  simp only [Sphincs.hashDomainFields]
  rw [hkey, keyAddressCell_lane, tAdr,
    show 2 ^ 32 * (l + 1 + 2 ^ 24 * (3 + 32 * 0)) = tw 3 + (l + 1) * hiMul by simp only [tw, hiMul]; ring]
  congr 1
  ring

theorem nodePayload_cells (a b : E) : nodePayload (cellVal a) (cellVal b) = [a, b].flatMap cellBytes := by
  simp [nodePayload, bytesLE_cellVal]

/-- **`treeFold` over cells**: the tree's fold from the leaf `e`, the siblings the values of `sib`,
from the value of `x`, is the value of the fold of `tNode` at the tree's lane. -/
theorem sTreeFold_cells (pp : E) (layer : Sphincs.Layer) (tree : Sphincs.TreeIndex) (leaf : Sphincs.TreeLeafIndex)
    {sib : Nat → E} {path : Nat → Digest} {h : Nat} (hh : h ≤ 10) (hsib : ∀ l < h, cellVal (sib l) = path l)
    (x : E) :
    Id.run (Sphincs.Verification.treeFold keccakF1600 (cellVal pp) layer tree leaf path h (cellVal x)) =
      cellVal (pFold (tNode pp (laneCell layer tree) leaf.val sib) h x) := by
  have hleaf : leaf.val < 2 ^ 10 := leaf.isLt
  induction h with
  | zero => rfl
  | succ l ih =>
      have ih' := ih (by omega) (fun j hj => hsib j (by omega))
      show Sphincs.Verification.tweakableHash (m := Id) keccakF1600 (cellVal pp)
        (.node layer tree (l + 1) (leaf.val / 2 ^ (l + 1)))
        (if leaf.val.testBit l then nodePayload (path l) (foldPath (m := Id) _ leaf.val path l (cellVal x))
          else nodePayload (foldPath (m := Id) _ leaf.val path l (cellVal x)) (path l)) = _
      have ih'' : foldPath (m := Id) (fun level nodeIndex ↦ Sphincs.Verification.tweakableHash (m := Id)
          keccakF1600 (cellVal pp) (.node layer tree (level + 1) nodeIndex)) leaf.val path l (cellVal x) =
          cellVal (pFold (tNode pp (laneCell layer tree) leaf.val sib) l x) := ih'
      rw [ih'', ← hsib l (by omega)]
      have hq : leaf.val / 2 ^ (l + 1) < 2 ^ 10 := lt_of_le_of_lt (Nat.div_le_self _ _) hleaf
      have hpay : (if leaf.val.testBit l then nodePayload (cellVal (sib l))
          (cellVal (pFold (tNode pp (laneCell layer tree) leaf.val sib) l x))
          else nodePayload (cellVal (pFold (tNode pp (laneCell layer tree) leaf.val sib) l x)) (cellVal (sib l))) =
          [(mPair (leaf.val.testBit l) (pFold (tNode pp (laneCell layer tree) leaf.val sib) l x) (sib l)).1,
            (mPair (leaf.val.testBit l) (pFold (tNode pp (laneCell layer tree) leaf.val sib) l x) (sib l)).2].flatMap
            cellBytes := by
        split <;> rename_i hb <;> simp only [mPair, hb, ↓reduceIte, Bool.false_eq_true, nodePayload_cells]
      rw [hpay]
      refine th_cells (thInput_cells (nodeAdr_bytes layer tree (by omega) hq) _) |>.trans ?_
      simp only [pFold, tNode, Nat.shiftRight_eq_div_pow]
      rfl

end
end LeanVM.Guest.B1.Sig
