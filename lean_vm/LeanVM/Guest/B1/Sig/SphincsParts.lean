/-
  LeanVM.Guest.B1.Sig.SphincsParts

  The three `keccak` structures after the forest, as cells: the encoding's digest (292 bytes), the
  one-time leaf (1056 bytes) and the tree's fold.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsMsg

/-!
# The encoding, the leaf and the tree, as cells

`sEnc_sound`: the encoding's first output cell is the digest of `P`, its address, the sixteen
top nodes and the counter's first four bytes. `sLeaf_sound`: the one-time leaf is `hcell` of `P`,
its address and the 64 tips. `sTree_sound`, `sTree_adr`: the tree folds the leaf up the hinted path,
its addresses the levels' constants plus the parents' indices.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat)

@[expose] public section

attribute [local irreducible] sCoords kMsg codewordT merkleT

variable {rd : Reader} {σ : Val}

theorem sTops_count : sCs.2.2.2.2.length = 16 := by
  rw [sCs, sCoords_tops, pairs_length]

theorem map_getD_range {α β : Type} (f : α → β) (d : α) (l : List α) :
    (List.range l.length).map (fun k => f (l.getD k d)) = l.map f := by
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by simpa using h1)]
    rfl

/-- The sixteen top nodes' values. -/
noncomputable def sT (σ : Val) (k : Nat) : E := σ (sCs.2.2.2.2.getD k (.n 0))

theorem sTops_vals : (sTops.map KC.cell).map (KC.val σ) =
    σ (.n 162) :: σ (.n 164) :: (List.range 16).map (sT σ) ++ [σ (.n sFb.2.1)] := by
  have e := map_getD_range σ (.n 0) sCs.2.2.2.2
  rw [sTops_count] at e
  have e' : (List.range 16).map (sT σ) = sCs.2.2.2.2.map σ := e
  rw [e']
  simp only [sTops, List.map_append, List.map_map, List.map_cons, List.map_nil]
  rfl

/-- **The encoding's digest.** -/
theorem sEnc_sound (hp : PadOK σ sPad) (h : AtomsHold rd σ sEnc.1) {N : Nat} (hN : N < 2 ^ 32)
    (hx : σ (.n sFb.2.1) = eOfNat N) :
    σ (.n sEnc.2.2) = (digestScalars (keccak256 ((cellsBytes (σ (.n 162) :: σ (.n 164) ::
      (List.range 16).map (sT σ) ++ [σ (.n sFb.2.1)])).take 292))).1 := by
  have hl : 8 ≤ sTops.length := by simp [sTops, sTops_count]
  have := kMsg_sound (out := none) (tailRun := true) hp (fun _ => tailCells_292 sTops hl _) h
    (by simp [sTops, sTops_count]) (fun j hj => by
      rw [sTops_vals, hx]
      exact bytes_past_counter _ (by simp) hN j hj)
  rw [sTops_vals] at this
  exact congrArg Prod.fst this

/-- **The one-time leaf.** -/
theorem sLeaf_sound (hp : PadOK σ sPad) (h : AtomsHold rd σ sLeaf.1) :
    σ (.n sLeaf.2.2) = (hcell (σ sPP :: σ (.n (sCw.2.1 + 1)) ::
      (List.range 64).map (fun i => σ (cwTip sW (sEnc.2.1 + 10) i)))).1 := by
  have htips := codewordT_tips sW (G := 21) (by norm_num) sTarget (.n sEnc.2.2) (sEnc.2.1 + 10)
  have hcells : ((sPP :: V.n (sCw.2.1 + 1) :: sCw.2.2).map KC.cell).map (KC.val σ) =
      σ sPP :: σ (.n (sCw.2.1 + 1)) :: (List.range 64).map (fun i => σ (cwTip sW (sEnc.2.1 + 10) i)) := by
    rw [show sCw.2.2 = (codewordT sW 21 sTarget (.n sEnc.2.2) (sEnc.2.1 + 10)).2.2 from rfl, htips]
    simp [KC.val]
  have hlen : (sPP :: V.n (sCw.2.1 + 1) :: sCw.2.2).length = 66 := by
    rw [show sCw.2.2 = (codewordT sW 21 sTarget (.n sEnc.2.2) (sEnc.2.1 + 10)).2.2 from rfl, htips]
    simp
  have := kMsg_sound (out := none) (tailRun := false) hp (by simp) h
    (by rw [List.length_map, hlen]) (fun j hj => by
      rw [hcells]
      exact cellsBytes_getD_past (by simp; omega))
  rw [hcells, List.take_of_length_le (by rw [length_cellsBytes]; simp)] at this
  exact congrArg Prod.fst this

/-- **The tree.** -/
theorem sTree_sound (hpre : SPre rd σ) (h : AtomsHold rd σ sMk.1) :
    σ sMk.2.2 = xFold (σ sPP) (fun l => σ (mAdr sNodeOf l (mBase sNodeOf 0 l sLeaf.2.1)))
      (fun l => decide (σ (sBit l) = 1)) (fun l => mSib σ sBit l (mBase sNodeOf 0 l sLeaf.2.1)) 26
      (σ (.n sLeaf.2.2)) := by
  have := merkleT_sound (bound := 26) hpre.pad hpre.bits 26 0 _ _ (by norm_num) h
  rw [mFold_eq_xFold] at this
  simp only [Nat.sub_zero] at this
  exact this

theorem sTree_adr (hpre : SPre rd σ) (h : AtomsHold rd σ sMk.1) {l : Nat} (hl : l < 26) :
    σ (mAdr sNodeOf l (mBase sNodeOf 0 l sLeaf.2.1)) =
      word (tw 3 + (l + 1) * hiMul) 0 0 + (if l + 1 = 26 then 0 else eOfNat (sIdx σ >>> (l + 1))) := by
  have e := merkleT_adr 26 0 _ _ h l hl
  rw [Nat.zero_add] at e
  rw [e]
  by_cases h26 : l + 1 = 26
  · simp [sNodeOf, sAddrOf, h26]
  · simp only [sNodeOf, sAddrOf, h26, ↓reduceIte]
    rw [hpre.nodes _ (by omega)]

end
end LeanVM.Guest.B1.Sig
