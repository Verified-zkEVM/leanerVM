/-
  LeanVM.Guest.B1.Sig.SphincsSoundLayer

  A hypertree layer of `verify_sig_lean_sphincs` (`lean_ethereum.py:3816-3878` and the bottom
  layer's lines `3907-3922` at leanVM `b7a8d0cb`) is sound: its encoding's digest, the call of
  `sp_wots` at the key's address and the path reach the statement's layer root.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsSoundPath
public import LeanVM.Guest.B1.Sig.SphincsBridgeEnc
public import LeanVM.Guest.B1.Sig.SphincsBridge
public import LeanVM.Guest.B1.Sig.SpWotsSound

/-!
# A layer, sound

* `otsLeaf_of_valid`: a counter whose encoding's digits reach the target sum recovers
  `wotsLeafOf` (the converse of `otsLeaf_some`);
* `layer_of_cells`: the encoding's digest at a cell, `sp_wots`'s leaf at the key's address and a
  fold of `tNode` at the tree's lane reach `LayerReaches`;
* `encDigest_sound`: the guest's encoding `KECCAK` of `[P, A + TW_ENC, …, counter]` is the
  statement's encoding hash;
* `laneCell_eq`, `eOfNat_mul_word_hi`, `word_hi_add`: the lanes of the hypertree's addresses.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat kToNat)
open HashSig HashSig.OverPermutation
open Sphincs Sphincs.Verification

@[expose] public section

variable {rd : Reader} {σ : Val}

/-! ## The one-time leaf -/

/-- **A counter whose encoding is a codeword recovers the leaf of its digits.** -/
theorem otsLeaf_of_valid {P : PublicParameter} {layer : Layer} {tree : TreeIndex} {leaf : TreeLeafIndex}
    {msg : HashInput} {ctr : EncodingCounter} {values : ChainIndex → HashSig.Digest}
    (hv : TargetSum.Valid (digestDigits (th (m := Id) keccakF1600 P (hashDomainFields (.encoding layer tree leaf))
      (msg ++ littleEndianBytes 4 ctr)))) :
    Id.run (otsLeaf (m := Id) keccakF1600 P layer tree leaf msg ctr values) =
      some (wotsLeafOf P layer tree leaf (th (m := Id) keccakF1600 P (hashDomainFields (.encoding layer tree leaf))
        (msg ++ littleEndianBytes 4 ctr)) values) := by
  rw [sOtsLeaf_id]
  generalize th (m := Id) keccakF1600 P (hashDomainFields (.encoding layer tree leaf))
    (msg ++ littleEndianBytes 4 ctr) = d at hv ⊢
  rw [show TargetSum.decodeDigest d = some (digestDigits d) from by
    unfold TargetSum.decodeDigest; split <;> simp_all, Option.map_some, wotsLeafOf_eq]

/-- **A layer over cells reaches its root**: the encoding's digest at `enc` is the statement's of
`msg` and the layer's counter, `sp_wots` at the key's address gives the leaf of the layer's chain
values, and the root is the fold of `tNode` at the tree's lane, the siblings the layer's path. -/
theorem layer_of_cells {P : PublicParameter} {idx : Index} {sig : Sphincs.Signature} {l : Layer}
    {msg : HashInput} {pp atC encC leafC : E} {values : ChainIndex → HashSig.Digest} (hP : cellVal pp = P)
    (henc : cellVal encC = th (m := Id) keccakF1600 P
      (hashDomainFields (.encoding l (treeOfIndex l idx) (leafOfIndex l idx)))
      (msg ++ littleEndianBytes 4 (sig.layers l).counter))
    (hat : atC = keyAddressCell l (treeOfIndex l idx) (leafOfIndex l idx))
    (hwots : ∀ (layer : Layer) (tree : TreeIndex) (lf : TreeLeafIndex), atC = keyAddressCell layer tree lf →
      TargetSum.Valid (digestDigits (cellVal encC)) ∧
        cellVal leafC = wotsLeafOf (cellVal pp) layer tree lf (cellVal encC) values)
    (hvals : (sig.layers l).chainValues = values) {sib : Nat → E}
    (hsib : ∀ j < layerHeight l, cellVal (sib j) = layerPath sig l j) :
    LayerReaches P idx sig l msg
      (cellVal (pFold (tNode pp (laneCell l (treeOfIndex l idx)) (leafOfIndex l idx).val sib) (layerHeight l)
        leafC)) := by
  obtain ⟨hv, hleaf⟩ := hwots _ _ _ hat
  subst hP
  refine (layerReaches_iff _ _ _ _ _ _).mpr ⟨cellVal leafC, ?_, ?_⟩
  · rw [henc] at hv hleaf
    rw [otsLeaf_of_valid hv, hvals, hleaf]
  · exact sTreeFold_cells pp l _ _ (by unfold layerHeight; split <;> norm_num) hsib leafC

/-! ## The encoding -/

theorem flatMap_cellBytes_length' : ∀ cs : List E, (cs.flatMap cellBytes).length = 16 * cs.length
  | [] => rfl
  | c :: cs => by
      simp only [List.flatMap_cons, List.length_append, length_cellBytes, flatMap_cellBytes_length' cs,
        List.length_cons]
      ring

/-- The bytes of cells ending in a counter's word are zero past its four bytes. -/
theorem cellsBytes_counter_zero (cs : List E) {N : Nat} (hN : N < 2 ^ 32) :
    ∀ j, 16 * cs.length + 4 ≤ j → (cellsBytes (cs ++ [eOfNat N])).getD j 0 = 0 := by
  intro j hj
  have hl := flatMap_cellBytes_length' cs
  rw [cellsBytes_eq_flatMap, List.flatMap_append, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega), hl]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [cellBytes_eOfNat (by omega)]
  by_cases h16 : j - 16 * cs.length < 16
  · rw [List.getElem?_eq_getElem (by simp; omega), Option.getD_some, getElem_leBytes]
    have : N / 256 ^ (j - 16 * cs.length) = 0 := Nat.div_eq_of_lt (by
      calc N < 2 ^ 32 := hN
        _ ≤ 256 ^ 4 := by norm_num
        _ ≤ 256 ^ (j - 16 * cs.length) := Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [this]; rfl
  · rw [List.getElem?_eq_none (by simp; omega)]; rfl

/-- The counter of a word below `2^32`. -/
theorem counter_toNat {N : Nat} (hN : N < 2 ^ 32) : (BitVec.ofNat 32 (cellNat (eOfNat N))).toNat = N := by
  rw [BitVec.toNat_ofNat, ← eOfNat192_of_lt (by omega), cellNat_eOfNat192 (by omega), Nat.mod_eq_of_lt hN]

/-- **The encoding's `KECCAK`, sound**: over the cells `[P, A + TW_ENC] ++ cs ++ [counter]`, the
counter a word `N < 2^32`, the digest is the statement's encoding hash of `cs`'s bytes and the
counter. -/
theorem encDigest_sound (hp : PadOK σ sPad) {pp adr ctr : V} {cs : List V} {N : Nat} (hN : N < 2 ^ 32)
    (hctr : σ ctr = eOfNat N) {l : Layer} {t : TreeIndex} {lf : TreeLeafIndex}
    (hadr : σ adr = keyAddressCell l t lf + word (tw 4) 0 0) {tailRun : Bool} {b : Nat}
    (htr : tailRun = true → TailCells (blockOf (kMsgCells (([.cell pp, .cell adr] ++ cs.map KC.cell ++
      [.cell ctr])) (16 * (cs.length + 2) + 4) b) 0))
    (h : AtomsHold rd σ (kMsg sPad ([.cell pp, .cell adr] ++ cs.map KC.cell ++ [.cell ctr])
      (16 * (cs.length + 2) + 4) tailRun none b).1) :
    cellVal (σ (.n (kMsg sPad ([.cell pp, .cell adr] ++ cs.map KC.cell ++ [.cell ctr])
      (16 * (cs.length + 2) + 4) tailRun none b).2.2)) =
      th (m := Id) keccakF1600 (cellVal (σ pp)) (hashDomainFields (.encoding l t lf))
        ((cs.map σ).flatMap cellBytes ++ littleEndianBytes 4 (BitVec.ofNat 32 (cellNat (eOfNat N)))) := by
  have hmap : ([KC.cell pp, KC.cell adr] ++ cs.map KC.cell ++ [KC.cell ctr]).map (KC.val σ) =
      [σ pp, keyAddressCell l t lf + word (tw 4) 0 0] ++ cs.map σ ++ [eOfNat N] := by
    simp [KC.val, hadr, hctr, Function.comp_def]
  have k := kMsg_sound hp htr h (by simp; omega) (fun j hj => by
    rw [hmap]
    exact cellsBytes_counter_zero _ hN j (by simp at hj ⊢; omega))
  have k1 := congrArg Prod.fst k
  simp only at k1
  rw [k1, hmap]
  refine Eq.trans ?_ (encTh_cells (σ pp) l t lf (cs.map σ) (BitVec.ofNat 32 (cellNat (eOfNat N)))).symm
  erw [counter_toNat hN]
  rw [List.length_map]

/-! ## Lanes -/

theorem word_eq_ofLimbs (a b c : Nat) : word a b c = E.ofLimbs (K.ofBits a) (K.ofBits b) (K.ofBits c) := rfl

/-- **A tree's lane is the word of its layer and tree in the high limb.** -/
theorem laneCell_eq (l : Layer) (t : TreeIndex) : laneCell l t = word 0 (l.val + 2 ^ 8 * t.val) 0 := by
  have hl : l.val < 3 := l.isLt
  have ht : t.val < 2 ^ 26 := t.isLt
  rw [laneCell, keyAddressCell_eq, keyNat, Nat.zero_add, eOfNat192_two_pow_64_mul (by omega),
    word_eq_ofLimbs, Value.ofBits_zero]

/-- A word times `y·2^s`. -/
theorem eOfNat_mul_word_hi {a s : Nat} (h : 2 ^ s * a < 2 ^ 64) :
    eOfNat a * word 0 (2 ^ s) 0 = word 0 (2 ^ s * a) 0 := by
  rw [eOfNat_eq_ofLimbs, word_eq_ofLimbs, word_eq_ofLimbs, mul_comm, ← ofK_eq_ofLimbs, ofLimbs_mul_ofK,
    Value.ofBits_zero, zero_mul, ofBits_two_pow_mul h]

theorem word_hi_add (a b : Nat) : word 0 a 0 + word 0 b 0 = word 0 (a ^^^ b) 0 := by
  rw [word_eq_ofLimbs, word_eq_ofLimbs, word_eq_ofLimbs, ofLimbs_add, Value.ofBits_zero, add_zero, ofBits_xor]

end
end LeanVM.Guest.B1.Sig
