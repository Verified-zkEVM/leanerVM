/-
  LeanVM.Guest.B1.Sig.SphincsHash

  leanSPHINCS's hashes (the statement's, over Keccak-f[1600] in `Id`) as functions of the guest's
  cells: the tweakable hash of cells is the first cell of their Keccak-256 digest, and the
  one-time key's address cell plus a constant is the address of a chain step, of its leaf or of its
  encoding.
-/

module

public import LeanVM.Guest.B1.Sig.XmssScheme
public import LeanVM.Guest.B1.Sig.WotsSound
public import LeanVM.Guest.B1.Sig.Shifts
public import LeanVM.Guest.B1.Sig.SphincsCompleteSpec

/-!
# leanSPHINCS over cells

The statement's leanSPHINCS (`Statement/LeanSphincs.lean`) is written over a permutation `π` in any
monad; the deployed one is `π = keccakF1600` in `Id`, where its hash is `Node.keccakBits`
(`keccakHash_keccakF1600`). A hash's input is `P ‖ A ‖ payload` of 16-byte fields, which are the
bytes of cells; so:

* `th_cells`, `thPair_cells`: the tweakable hash of the bytes of cells is the first cell of their
  `hcell`; the untruncated one is both cells (`cellPairVal`);
* `keyAddressCell_eq`, `keyAddress_add`, `keyAddress_bytes`: the one-time key's address cell is the
  192-bit word of its packed number, and adding a constant of type, step and `hi` fields gives the
  cell of that address (`addressBytes_eq_cell`);
* `spStepF`, `spRecoverChain_cells`: chain `i` walked from digit `d` is the guest's chain of cells
  (`chainT`, `WotsSound`) at the step addresses `adr + (TW_CHAIN + i·2^32 + s·2^61)`;
* `spLeafHash_cells`, `wotsLeafOf_cells`: the one-time leaf of the chain ends hashed at
  `adr + TW_LEAF` (`wotsLeafOf`, the statement's `otsLeaf` past its encoding).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open HashSig HashSig.OverPermutation

@[expose] public section

/-! ## Hashes of cells -/

/-- **A tweakable hash of cells**: when its input is the bytes of cells, the digest is the first
cell of their `hcell`. -/
theorem th_cells {P : PublicParameter} {fields : TweakFields} {payload : HashInput} {cs : List E}
    (h : thInput P fields payload = cs.flatMap cellBytes) :
    th (m := Id) keccakF1600 P fields payload = cellVal (hcell cs).1 := by
  show truncateHash (keccakHash (m := Id) keccakF1600 (thInput P fields payload)) = _
  rw [keccakHash_keccakF1600, h, truncateHash_keccakBits]
  rfl

/-- The 256-bit hash of a byte string, as the two cells of its digest. -/
theorem keccakBits_cells (I : List UInt8) :
    Node.keccakBits I = cellPairVal (digestHalves (keccak256 I)).1 (digestHalves (keccak256 I)).2 := by
  apply BitVec.eq_of_toNat_eq
  rw [keccakBits_toNat, cellPairVal, BitVec.toNat_append, toNat_cellVal, toNat_cellVal,
    Nat.shiftLeft_eq, two_pow_mul_or' (cellNat_lt _)]
where
  two_pow_mul_or' {a b : Nat} (hb : b < 2 ^ 128) : a * 2 ^ 128 ||| b = b + 2 ^ 128 * a := by
    rw [mul_comm, two_pow_mul_or hb, add_comm]

/-- **An untruncated tweakable hash of cells** is both cells of their digest. -/
theorem thPair_cells {P : PublicParameter} {fields : TweakFields} {payload : HashInput} {cs : List E}
    (h : thInput P fields payload = cs.flatMap cellBytes) :
    thPair (m := Id) keccakF1600 P fields payload = cellPairVal (hcell cs).1 (hcell cs).2 := by
  show keccakHash (m := Id) keccakF1600 (thInput P fields payload) = _
  rw [keccakHash_keccakF1600, h, keccakBits_cells]
  rfl

/-- The input of a hash adr `P = cellVal pp`, the address cell `a` and a payload of cells. -/
theorem thInput_cells {pp a : E} {fields : TweakFields} (ha : addressBytes fields = cellBytes a)
    (cs : List E) :
    thInput (cellVal pp) fields (cs.flatMap cellBytes) = (pp :: a :: cs).flatMap cellBytes := by
  rw [thInput, bytesLE_cellVal, ha]
  simp

/-- The bytes of digests that are cells' values. -/
theorem flatMap_bytes_cellVal (l : List E) :
    (l.map cellVal).flatMap (littleEndianBytes 16) = l.flatMap cellBytes := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.map_cons, List.flatMap_cons, bytesLE_cellVal, ih]

/-- The bytes of digests that are cells' values, mapped. -/
theorem flatMap_bytes_map (f : Nat → E) (l : List Nat) :
    (l.map fun i => cellVal (f i)).flatMap (littleEndianBytes 16) = (l.map f).flatMap cellBytes := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.map_cons, List.flatMap_cons, bytesLE_cellVal, ih]

/-! ## The one-time key's addresses -/

/-- The packed number of the one-time key's address, type `0`. -/
def keyNat (layer : Sphincs.Layer) (tree : Sphincs.TreeIndex) (leaf : Sphincs.TreeLeafIndex) : Nat :=
  leaf.val + 2 ^ 64 * (layer.val + 2 ^ 8 * tree.val)

theorem keyNat_lt (layer : Sphincs.Layer) (tree : Sphincs.TreeIndex) (leaf : Sphincs.TreeLeafIndex) :
    keyNat layer tree leaf < 2 ^ 128 := by
  have h1 : layer.val < 3 := layer.isLt
  have h2 : tree.val < 2 ^ 26 := tree.isLt
  have h3 : leaf.val < 1024 := lt_of_lt_of_le leaf.isLt (by decide)
  unfold keyNat
  omega

theorem cellOf128_eq_eOfNat192 {n : Nat} (h : n < 2 ^ 128) :
    cellOf128 (BitVec.ofNat 128 n) = eOfNat192 n := by
  have h2 : n / 2 ^ 128 = 0 := Nat.div_eq_of_lt h
  simp only [cellOf128, eOfNat192, h2]
  congr 1
  · apply BF64.toBitVec_injective
    simp only [K.ofBits, BF64.toBitVec_ofBitVec]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.extractLsb'_toNat]
  · apply BF64.toBitVec_injective
    simp only [K.ofBits, BF64.toBitVec_ofBitVec]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt h]

/-- **The key's address cell is the word of its packed number.** -/
theorem keyAddressCell_eq (layer : Sphincs.Layer) (tree : Sphincs.TreeIndex)
    (leaf : Sphincs.TreeLeafIndex) : keyAddressCell layer tree leaf = eOfNat192 (keyNat layer tree leaf) :=
  cellOf128_eq_eOfNat192 (keyNat_lt layer tree leaf)

private theorem xor_low_mid {a L q : Nat} (ha : a < 2 ^ 32) (hq : q < 2 ^ 32) :
    (a + 2 ^ 64 * L) ^^^ 2 ^ 32 * q = a + 2 ^ 32 * q + 2 ^ 64 * L := by
  have e1 : a + 2 ^ 64 * L = 2 ^ 32 * (2 ^ 32 * L) ^^^ a := by
    rw [two_pow_mul_xor ha]; ring
  have e2 : 2 ^ 32 * (2 ^ 32 * L) ^^^ 2 ^ 32 * q = 2 ^ 32 * (2 ^ 32 * L + q) := by
    rw [show 2 ^ 32 * (2 ^ 32 * L) ^^^ 2 ^ 32 * q = 2 ^ 32 * (2 ^ 32 * L ^^^ q) by
      apply Nat.eq_of_testBit_eq
      intro j
      simp only [Nat.testBit_xor, Nat.testBit_two_pow_mul]
      by_cases hj : 32 ≤ j <;> simp [hj], two_pow_mul_xor hq]
  rw [e1, Nat.xor_assoc, Nat.xor_comm a, ← Nat.xor_assoc, e2, two_pow_mul_xor ha]
  ring

/-- **A constant added to the key's address cell**: a type `tag`, a step `step` and a field `hi`
give the cell of that address of the key. -/
theorem keyAddress_add {layer : Sphincs.Layer} {tree : Sphincs.TreeIndex}
    {leaf : Sphincs.TreeLeafIndex} {tag step hi : Nat} (htag : tag < 32) (hstep : step < 8)
    (hhi : hi < 2 ^ 24) :
    keyAddressCell layer tree leaf + word (2 ^ 32 * (hi + 2 ^ 24 * (tag + 32 * step))) 0 0 =
      eOfNat192 (tweakNat ((tweakFields tag step hi leaf.val).at layer.val tree.val)) := by
  have hl : leaf.val < 1024 := lt_of_lt_of_le leaf.isLt (by decide)
  have hla : layer.val < 3 := layer.isLt
  have htr : tree.val < 2 ^ 26 := tree.isLt
  have hq : hi + 2 ^ 24 * (tag + 32 * step) < 2 ^ 32 := by omega
  rw [keyAddressCell_eq, word_eq_eOfNat, ← eOfNat192_of_lt (by omega), ← eOfNat192_xor, keyNat,
    xor_low_mid (by omega) hq, tweakNat_at, addrNat]
  congr 1
  simp only [Nat.mod_eq_of_lt (show leaf.val < 2 ^ 32 by omega), Nat.mod_eq_of_lt hhi,
    Nat.mod_eq_of_lt htag, Nat.mod_eq_of_lt hstep, Nat.mod_eq_of_lt (show layer.val < 2 ^ 8 by omega),
    Nat.mod_eq_of_lt (show tree.val < 2 ^ 32 by omega)]
  ring

/-- The bytes of that cell are the address's. -/
theorem keyAddress_bytes {layer : Sphincs.Layer} {tree : Sphincs.TreeIndex}
    {leaf : Sphincs.TreeLeafIndex} {tag step hi : Nat} (htag : tag < 32) (hstep : step < 8)
    (hhi : hi < 2 ^ 24) :
    addressBytes ((tweakFields tag step hi leaf.val).at layer.val tree.val) =
      cellBytes (keyAddressCell layer tree leaf + word (2 ^ 32 * (hi + 2 ^ 24 * (tag + 32 * step))) 0 0) := by
  rw [keyAddress_add htag hstep hhi, addressBytes_eq_cell]

/-- The constant of chain `i`'s step `s`, `TW_CHAIN + i·2^32 + s·2^61`. -/
theorem chainConst_eq (i s : Nat) :
    tw 1 + i * hiMul + s * stepMul = 2 ^ 32 * (i + 2 ^ 24 * (1 + 32 * s)) := by
  simp only [tw, hiMul, stepMul]; ring

/-- The constant of the leaf, `TW_LEAF`. -/
theorem leafConst_eq : tw 2 = 2 ^ 32 * (0 + 2 ^ 24 * (2 + 32 * 0)) := by simp [tw]

/-- The constant of the encoding, `SP_TW_ENC`. -/
theorem encConst_eq : tw 4 = 2 ^ 32 * (0 + 2 ^ 24 * (4 + 32 * 0)) := by simp [tw]

/-! ## Chains -/

/-- `sp_wots`'s chain step of chain `i` leaving position `s`, on cells: the 48-byte hash of `pp`,
the step's address `adr + (TW_CHAIN + i·2^32 + s·2^61)` and the value. -/
def spStepF (pp adr : E) (i s : Nat) (x : E) : E :=
  (hcell [pp, adr + word (tw 1 + i * hiMul + s * stepMul) 0 0, x]).1

/-- **A chain walked from digit `d` over cells**: the key's address at `adr`. -/
theorem spRecoverChain_cells {pp adr : E} {layer : Sphincs.Layer} {tree : Sphincs.TreeIndex}
    {leaf : Sphincs.TreeLeafIndex} (hat : adr = keyAddressCell layer tree leaf)
    (i : Sphincs.ChainIndex) (d : WinternitzDigit) (x : E) :
    Sphincs.Verification.recoverChain (m := Id) keccakF1600 (cellVal pp) layer tree leaf i d
        (cellVal x) = cellVal (chainT (spStepF pp adr) i.val (3 - d.val) d.val x) := by
  have hi := i.isLt
  simp only [Sphincs.chainCount] at hi
  have hwalk : ∀ (n start : Nat), start + n ≤ 3 →
      Sphincs.Verification.chainWalk (m := Id) keccakF1600 (cellVal pp) layer tree leaf i start n
        (cellVal x) = cellVal (chainT (spStepF pp adr) i.val n start x) := by
    intro n
    induction n with
    | zero => intro start _; rfl
    | succ n ih =>
        intro start h
        have hs : start + n < chainLength - 1 := by simp [chainLength, winternitzBits]; omega
        rw [chainT_succ]
        have e : Sphincs.Verification.chainWalk (m := Id) keccakF1600 (cellVal pp) layer tree leaf i
            start (n + 1) (cellVal x) =
            Sphincs.Verification.tweakableHash (m := Id) keccakF1600 (cellVal pp)
              (.chain layer tree leaf i ⟨start + n, hs⟩)
              (littleEndianBytes 16 (Sphincs.Verification.chainWalk (m := Id) keccakF1600 (cellVal pp)
                layer tree leaf i start n (cellVal x))) := by
          simp only [Sphincs.Verification.chainWalk, walkChain, hs, ↓reduceDIte]
          rfl
        rw [e, ih start (by omega), bytesLE_cellVal, spStepF,
          show ∀ y : E, cellBytes y = [y].flatMap cellBytes from fun y => by simp]
        refine th_cells (thInput_cells ?_ _)
        rw [hat, chainConst_eq]
        exact keyAddress_bytes (by norm_num) (lt_of_lt_of_le (Fin.isLt _) (by decide)) (by omega)
  have hd := d.isLt
  simp only [chainLength, winternitzBits] at hd
  show Sphincs.Verification.chainWalk (m := Id) keccakF1600 (cellVal pp) layer tree leaf i d.val
    (chainLength - 1 - d.val) (cellVal x) = _
  rw [show chainLength - 1 - d.val = 3 - d.val by simp [chainLength, winternitzBits]]
  exact hwalk _ _ (by omega)

/-! ## The one-time leaf -/

/-- **The one-time leaf over cells**: the chain ends `tips` hashed adr the leaf's address
`adr + TW_LEAF`. -/
theorem spLeafHash_cells {pp adr : E} {layer : Sphincs.Layer} {tree : Sphincs.TreeIndex}
    {leaf : Sphincs.TreeLeafIndex} (hat : adr = keyAddressCell layer tree leaf) (tips : Nat → E) :
    Sphincs.Verification.leafHash (m := Id) keccakF1600 (cellVal pp) layer tree leaf
        (fun i : Sphincs.ChainIndex => cellVal (tips i.val)) =
      cellVal (hcell (pp :: (adr + word (tw 2) 0 0) :: (List.range Sphincs.chainCount).map tips)).1 := by
  have e : (List.ofFn fun i : Sphincs.ChainIndex => cellVal (tips i.val)).flatMap (littleEndianBytes 16) =
      ((List.range Sphincs.chainCount).map tips).flatMap cellBytes := by
    rw [ofFn_val_eq Sphincs.chainCount (fun i => cellVal (tips i)), flatMap_bytes_map]
  unfold Sphincs.Verification.leafHash digestsPayload
  erw [e]
  refine th_cells (thInput_cells ?_ _)
  rw [hat, leafConst_eq]
  exact keyAddress_bytes (tag := 2) (step := 0) (hi := 0) (by norm_num) (by norm_num) (by norm_num)

/-- `wotsLeafOf` in `Id`: the leaf of the chains recovered. -/
theorem wotsLeafOf_eq (P : PublicParameter) (layer : Sphincs.Layer) (tree : Sphincs.TreeIndex)
    (leaf : Sphincs.TreeLeafIndex) (digest : HashSig.Digest) (values : Sphincs.ChainIndex → HashSig.Digest) :
    wotsLeafOf P layer tree leaf digest values =
      Sphincs.Verification.leafHash (m := Id) keccakF1600 P layer tree leaf (fun i =>
        Sphincs.Verification.recoverChain (m := Id) keccakF1600 P layer tree leaf i
          (digestDigits digest i) (values i)) := by
  unfold wotsLeafOf
  rw [sequenceFin_id]
  rfl

/-- **The one-time leaf the chain values recover, over cells**: chain `i` walked from its digit
`dig i` of `digest` from `starts i`, the ends hashed at `adr + TW_LEAF`. -/
theorem wotsLeafOf_cells {pp adr : E} {layer : Sphincs.Layer} {tree : Sphincs.TreeIndex}
    {leaf : Sphincs.TreeLeafIndex} (hat : adr = keyAddressCell layer tree leaf) (digest : HashSig.Digest)
    (starts : Nat → E) (dig : Nat → Nat)
    (hdig : ∀ i : Sphincs.ChainIndex, (digestDigits digest i).val = dig i.val) :
    wotsLeafOf (cellVal pp) layer tree leaf digest (fun i => cellVal (starts i.val)) =
      cellVal (hcell (pp :: (adr + word (tw 2) 0 0) :: (List.range Sphincs.chainCount).map fun i =>
        chainT (spStepF pp adr) i (3 - dig i) (dig i) (starts i))).1 := by
  refine (wotsLeafOf_eq _ _ _ _ _ _).trans ?_
  have e : (fun chainIndex : Sphincs.ChainIndex => Sphincs.Verification.recoverChain (m := Id)
      keccakF1600 (cellVal pp) layer tree leaf chainIndex (digestDigits digest chainIndex)
      (cellVal (starts chainIndex.val))) = fun i : Sphincs.ChainIndex => cellVal ((fun i : Nat =>
        chainT (spStepF pp adr) i (3 - dig i) (dig i) (starts i)) i.val) := by
    funext i
    rw [spRecoverChain_cells hat i, hdig i]
  refine (congrArg (Sphincs.Verification.leafHash (m := Id) keccakF1600 (cellVal pp) layer tree leaf)
    e).trans ?_
  exact spLeafHash_cells (tips := fun i => chainT (spStepF pp adr) i (3 - dig i) (dig i) (starts i)) hat

end
end LeanVM.Guest.B1.Sig
