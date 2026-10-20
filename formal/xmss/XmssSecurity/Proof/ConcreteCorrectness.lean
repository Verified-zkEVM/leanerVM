import XmssSecurity.Proof.CacheReplayEval
import Mathlib.Data.Nat.Bitwise

open OracleSpec

namespace XmssSecurity.Concrete.CacheReplay

def pathNode (leafIndex : LeafIndex) (level : Nat) : MerkleNode :=
  Concrete.merkleNodeOfNat (leafIndex.val / 2 ^ level)

@[simp]
theorem pathNode_zero (leafIndex : LeafIndex) : pathNode leafIndex 0 = leafIndex := by
  apply Fin.ext
  simp only [pathNode, Concrete.merkleNodeOfNat, pow_zero, Nat.div_one]
  exact Nat.mod_eq_of_lt leafIndex.isLt

theorem testBit_div_pow (value level : Nat) :
    (value / 2 ^ level).testBit 0 = value.testBit level := by
  simpa only [Nat.zero_add] using (Nat.testBit_add value 0 level).symm

theorem div_pow_succ (value level : Nat) :
    value / 2 ^ (level + 1) = (value / 2 ^ level) / 2 := by
  rw [pow_succ, Nat.div_div_eq_div_mul]

private theorem even_parts (value : Nat) (hbit : value.testBit 0 = false) :
    value = 2 * (value / 2) ∧ value ^^^ 1 = 2 * (value / 2) + 1 := by
  have heven : Even value := Nat.even_iff.mpr
    (Nat.mod_two_eq_zero_iff_testBit_zero.mpr hbit)
  constructor
  · have h := Nat.bit_testBit_zero_shiftRight_one value
    rw [hbit, Nat.bit_false, Nat.shiftRight_one] at h
    exact h.symm
  · rw [Nat.xor_one_of_even heven]
    have h := Nat.bit_testBit_zero_shiftRight_one value
    rw [hbit, Nat.bit_false, Nat.shiftRight_one] at h
    exact congrArg (fun current => current + 1) h.symm

private theorem odd_parts (value : Nat) (hbit : value.testBit 0 = true) :
    value = 2 * (value / 2) + 1 ∧ value ^^^ 1 = 2 * (value / 2) := by
  have hodd : Odd value := Nat.odd_iff.mpr
    (Nat.mod_two_eq_one_iff_testBit_zero.mpr hbit)
  constructor
  · have h := Nat.bit_testBit_zero_shiftRight_one value
    rw [hbit, Nat.bit_true, Nat.shiftRight_one] at h
    exact h.symm
  · rw [Nat.xor_one_of_odd hodd]
    have h := Nat.bit_testBit_zero_shiftRight_one value
    rw [hbit, Nat.bit_true, Nat.shiftRight_one] at h
    calc
      value - 1 = (2 * (value / 2) + 1) - 1 :=
        congrArg (fun current => current - 1) h.symm
      _ = 2 * (value / 2) := by omega

theorem nodeIndex_eq_pathNode_succ (leafIndex : LeafIndex) (level : Nat) :
    CacheView.nodeIndex leafIndex level = pathNode leafIndex (level + 1) := by
  apply Fin.ext
  simp only [CacheView.nodeIndex, Concrete.nodeIndex, pathNode, Concrete.merkleNodeOfNat]
  exact (Nat.mod_eq_of_lt
    ((Nat.div_le_self leafIndex.val _).trans_lt leafIndex.isLt)).symm

theorem pathNode_children (leafIndex : LeafIndex) (level : Nat) (hlevel : level < treeHeight) :
    if leafIndex.val.testBit level then
      Concrete.childNode (pathNode leafIndex (level + 1)) false =
          Concrete.authenticationPathNode leafIndex ⟨level, hlevel⟩ ∧
        Concrete.childNode (pathNode leafIndex (level + 1)) true = pathNode leafIndex level
    else
      Concrete.childNode (pathNode leafIndex (level + 1)) false = pathNode leafIndex level ∧
        Concrete.childNode (pathNode leafIndex (level + 1)) true =
          Concrete.authenticationPathNode leafIndex ⟨level, hlevel⟩ := by
  let quotient := leafIndex.val / 2 ^ level
  have hquotient : quotient < lifetime :=
    (Nat.div_le_self leafIndex.val _).trans_lt leafIndex.isLt
  have hparent : (pathNode leafIndex (level + 1)).val = quotient / 2 := by
    simp only [pathNode, Concrete.merkleNodeOfNat]
    rw [div_pow_succ]
    exact Nat.mod_eq_of_lt
      ((Nat.div_le_self (leafIndex.val / 2 ^ level) _).trans_lt hquotient)
  have hcurrent : (pathNode leafIndex level).val = quotient := by
    simp [pathNode, Concrete.merkleNodeOfNat, quotient,
      Nat.mod_eq_of_lt hquotient]
  have hauth :
      (Concrete.authenticationPathNode leafIndex ⟨level, hlevel⟩).val =
        (quotient ^^^ 1) % lifetime := by
    rfl
  have hquotientBit : quotient.testBit 0 = leafIndex.val.testBit level := by
    exact testBit_div_pow leafIndex.val level
  by_cases hbit : leafIndex.val.testBit level = true
  · simp only [hbit, ↓reduceIte]
    obtain ⟨hcurrentParts, hauthParts⟩ := odd_parts quotient (hquotientBit.trans hbit)
    constructor
    · apply Fin.ext
      rw [hauth]
      simp only [Concrete.childNode, Concrete.merkleNodeOfNat, Bool.false_eq_true,
        ↓reduceIte, hparent]
      exact congrArg (fun value => value % lifetime) hauthParts.symm

    · apply Fin.ext
      rw [hcurrent]
      simp only [Concrete.childNode, Concrete.merkleNodeOfNat, ↓reduceIte, hparent]
      calc
        (2 * (quotient / 2) + 1) % lifetime = quotient % lifetime :=
          congrArg (fun value => value % lifetime) hcurrentParts.symm
        _ = quotient := Nat.mod_eq_of_lt hquotient
  · have hbitFalse : leafIndex.val.testBit level = false := Bool.eq_false_of_not_eq_true hbit
    simp only [hbitFalse, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨hcurrentParts, hauthParts⟩ := even_parts quotient
      (hquotientBit.trans hbitFalse)
    constructor
    · apply Fin.ext
      rw [hcurrent]
      simp only [Concrete.childNode, Concrete.merkleNodeOfNat, Bool.false_eq_true,
        ↓reduceIte, hparent]
      calc
        (2 * (quotient / 2) + 0) % lifetime = quotient % lifetime :=
          congrArg (fun value => value % lifetime) (by omega :
            2 * (quotient / 2) + 0 = quotient)
        _ = quotient := Nat.mod_eq_of_lt hquotient
    · apply Fin.ext
      rw [hauth]
      simp only [Concrete.childNode, Concrete.merkleNodeOfNat, ↓reduceIte, hparent]
      exact congrArg (fun value => value % lifetime) hauthParts.symm

theorem authentication_step_eq_treeNode (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (leafIndex : LeafIndex) (level : Nat) (hlevel : level < treeHeight) :
    CacheView.nodeHash cache parameter leafIndex level
        (treeNode cache parameter secret level (pathNode leafIndex level))
        (treeNode cache parameter secret level
          (Concrete.authenticationPathNode leafIndex ⟨level, hlevel⟩)) =
      treeNode cache parameter secret (level + 1) (pathNode leafIndex (level + 1)) := by
  have hnode := nodeIndex_eq_pathNode_succ leafIndex level
  have hchildren := pathNode_children leafIndex level hlevel
  by_cases hbit : leafIndex.val.testBit level = true
  · simp only [hbit, ↓reduceIte] at hchildren
    rcases hchildren with ⟨hleft, hright⟩
    simp [CacheView.nodeHash, hlevel, CacheView.nodeInput,
      CacheView.authenticationNodePayload, CacheView.merkleHash,
      CacheView.merkleInput, treeNode_succ_eq, hbit, hnode, hleft, hright]
  · have hbitFalse : leafIndex.val.testBit level = false := Bool.eq_false_of_not_eq_true hbit
    simp only [hbitFalse, Bool.false_eq_true, ↓reduceIte] at hchildren
    rcases hchildren with ⟨hleft, hright⟩
    simp [CacheView.nodeHash, hlevel, CacheView.nodeInput,
      CacheView.authenticationNodePayload, CacheView.merkleHash,
      CacheView.merkleInput, treeNode_succ_eq, hbitFalse, hnode, hleft, hright]

theorem recover_signedChainValues (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (leafIndex : LeafIndex) (encoding : Encoding) :
    XmssSecurity.recoveredEndpoints
        (fun chain => CacheView.chainStep cache secretKey.parameter leafIndex chain)
        encoding (signedChainValues cache secretKey leafIndex encoding) =
      oneTimePublicKey cache secretKey.parameter secretKey.chainStart leafIndex := by
  funext chain
  exact Wots.recover_signChain_eq_publicChain
    (CacheView.chainStep cache secretKey.parameter leafIndex chain)
    (encoding chain) (secretKey.chainStart leafIndex chain)

theorem recoveredEndpoints_signWithEncoding (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (leafIndex : LeafIndex) (randomness : Randomness)
    (encoding : Encoding) :
    XmssSecurity.recoveredEndpoints
        (fun chain => CacheView.chainStep cache secretKey.parameter leafIndex chain)
        encoding (signWithEncoding cache secretKey leafIndex randomness encoding).chainValue =
      oneTimePublicKey cache secretKey.parameter secretKey.chainStart leafIndex := by
  exact recover_signedChainValues cache secretKey leafIndex encoding

theorem leafHash_recovered_signWithEncoding (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (leafIndex : LeafIndex) (randomness : Randomness)
    (encoding : Encoding) :
    CacheView.leafHash cache secretKey.parameter leafIndex
        (XmssSecurity.recoveredEndpoints
          (fun chain => CacheView.chainStep cache secretKey.parameter leafIndex chain)
          encoding (signWithEncoding cache secretKey leafIndex randomness encoding).chainValue) =
      leafAt cache secretKey.parameter secretKey.chainStart leafIndex := by
  rw [recoveredEndpoints_signWithEncoding]
  rfl

theorem authenticationPath_ascends_to_treeNode (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (leafIndex : LeafIndex) (randomness : Randomness)
    (encoding : Encoding) (levels : Nat) (hlevels : levels ≤ treeHeight) :
    Merkle.ascend (CacheView.nodeHash cache secretKey.parameter leafIndex)
        (Concrete.signaturePath
          (signWithEncoding cache secretKey leafIndex randomness encoding))
        0 levels (leafAt cache secretKey.parameter secretKey.chainStart leafIndex) =
      treeNode cache secretKey.parameter secretKey.chainStart levels
        (pathNode leafIndex levels) := by
  induction levels with
  | zero => simp [Merkle.ascend]
  | succ level ih =>
      have hlevel : level < treeHeight := Nat.lt_of_succ_le hlevels
      rw [Merkle.ascend, ih (Nat.le_of_succ_le hlevels)]
      simp only [Nat.zero_add]
      have hpath :
          Concrete.signaturePath
              (signWithEncoding cache secretKey leafIndex randomness encoding) level =
            treeNode cache secretKey.parameter secretKey.chainStart level
              (Concrete.authenticationPathNode leafIndex ⟨level, hlevel⟩) := by
        simp [Concrete.signaturePath, signWithEncoding, authenticationPath, hlevel]
      rw [hpath]
      exact authentication_step_eq_treeNode cache secretKey.parameter
        secretKey.chainStart leafIndex level hlevel

theorem authenticationPath_ascends_to_root (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (leafIndex : LeafIndex) (randomness : Randomness)
    (encoding : Encoding) :
    Merkle.ascend (CacheView.nodeHash cache secretKey.parameter leafIndex)
        (Concrete.signaturePath
          (signWithEncoding cache secretKey leafIndex randomness encoding))
        0 treeHeight (leafAt cache secretKey.parameter secretKey.chainStart leafIndex) =
      treeNode cache secretKey.parameter secretKey.chainStart treeHeight
        Concrete.rootNode := by
  rw [authenticationPath_ascends_to_treeNode cache secretKey leafIndex randomness encoding
    treeHeight le_rfl]
  congr 1
  apply Fin.ext
  have hdiv : leafIndex.val / 2 ^ treeHeight = 0 := by
    apply Nat.div_eq_of_lt
    change leafIndex.val < lifetime
    exact leafIndex.isLt
  simp [pathNode, Concrete.rootNode, Concrete.merkleNodeOfNat, hdiv]

def publicKeyFromCache (cache : QueryCache HashSpec) (secretKey : SecretKey) : PublicKey :=
  ⟨treeNode cache secretKey.parameter secretKey.chainStart treeHeight Concrete.rootNode,
    secretKey.parameter⟩

attribute [irreducible] publicKeyFromCache

theorem publicKey_eq_publicKeyFromCache (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (root : Digest)
    (hroot : root = treeNode cache secretKey.parameter secretKey.chainStart
      treeHeight Concrete.rootNode) :
    PublicKey.mk root secretKey.parameter = publicKeyFromCache cache secretKey := by
  rw [publicKeyFromCache]
  exact congrArg₂ PublicKey.mk hroot rfl

theorem verifyFromCache_signWithEncoding (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (randomness : Randomness) (encoding : Encoding)
    (hdecode : TargetSum.decodeDigest
      (CacheView.encodingHash cache secretKey.parameter leafIndex (message, randomness)) =
        some encoding) :
    Concrete.verifyFromCache cache (publicKeyFromCache cache secretKey) leafIndex message
      (signWithEncoding cache secretKey leafIndex randomness encoding) = true := by
  unfold publicKeyFromCache
  apply (Concrete.verifyFromCache_eq_true_iff _ _ _ _ _).2
  refine ⟨encoding, hdecode, ?_⟩
  rw [leafHash_recovered_signWithEncoding]
  exact authenticationPath_ascends_to_root cache secretKey leafIndex randomness encoding

end XmssSecurity.Concrete.CacheReplay
