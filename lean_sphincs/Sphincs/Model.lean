import FORS.Statement
import Statement.LeanSphincs
import Common.WithHash

/-!
# The statement's leanSPHINCS and upstream's model: the maps and the verifier

The proof of this project (`FORS`, leanVM's `formal/lean_sphincs` at `834e6614`) is about
`FORS.Scheme`, a model of leanSPHINCS generic in its shape (`FORS.Params`), the hash a random oracle
(`FORS.HashSpec`). At the deployed configuration, `.layered 26 3 8 24 10 1182000000` (`params`), its
verifier, its queries answered by Keccak-256 over `π` (`schemeHashOverPermutation`), is the
statement's (`simulateQ_verify`), through the maps of the keys and signatures. The two differ in
presentation only:

* the model numbers the layers from the top (`lay = 0` the top layer, the address's layer word
  `2 - lay`), the statement from the bottom as the crate does (`toLayer`);
* the model's address has a 96-bit tree word, the statement's a zero word and a 64-bit tree
  (`treeBytes_eq`: the same bytes below `2^64`), and the model places a FORS node index past its
  tree's width above `2^31`, which no algorithm computes;
* the model's digest packs the index and the FORS leaves into one bit vector, the statement reads
  them off the digest's bytes (`digestIndex_eq`, `digestForsLeaves_eq`).
-/

open OracleComp OracleSpec

namespace Sphincs.Model

open HashSig HashSig.OverPermutation Common Common.SufCma

/-- The deployed configuration: height 26, three layers of 10 + 8 + 8 from the top, FORS of 24
trees of height 10, `N = 1,182,000,000`. -/
abbrev params : FORS.Params := .layered 26 3 8 24 10 1182000000

attribute [local instance] params

/-! ## Bytes -/

theorem bytesLE_eq : @FORS.bytesLE = @littleEndianBytes := rfl

theorem bytesBE_eq : @FORS.bytesBE = @bigEndianBytes := rfl

/-- **The tree word**: the model's 96-bit tree word is the statement's zero word and 64-bit tree,
below `2^64`. -/
theorem treeBytes_eq (tree : ℕ) (htree : tree < 2 ^ 64) :
    FORS.bytesBE 12 (BitVec.ofNat 96 tree) =
      bigEndianBytes 4 0 ++ bigEndianBytes 8 (BitVec.ofNat 64 tree) := by
  have h64 : tree < 18446744073709551616 := by simpa using htree
  have h96 : tree < 79228162514264337593543950336 := by omega
  simp only [FORS.bytesBE, bigEndianBytes, List.ofFn_succ, List.ofFn_zero]
  simp only [List.cons_append, List.nil_append, List.cons.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;>
  · congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    simp only [Fin.val_succ, Fin.val_zero, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul,
      Nat.reducePow, Nat.mod_eq_of_lt h96, Nat.mod_eq_of_lt h64]
    try rw [Nat.div_eq_of_lt (by omega)]
    try simp

/-! ## Layers, indices and addresses -/

/-- A model layer (`0` the top) as the statement's layer (`0` the bottom). -/
def toLayer (lay : FORS.Layer) : Layer :=
  ⟨2 - lay.val, by have := lay.isLt; unfold layerCount; omega⟩

/-- A statement layer as the model's. -/
def ofLayer (layer : Layer) : FORS.Layer :=
  ⟨2 - layer.val, by have := layer.isLt; unfold layerCount at this; show _ < 3; omega⟩

theorem toLayer_ofLayer (layer : Layer) : toLayer (ofLayer layer) = layer := by
  have := layer.isLt; unfold layerCount at this
  apply Fin.ext; simp only [toLayer, ofLayer]; omega

theorem ofLayer_toLayer (lay : FORS.Layer) : ofLayer (toLayer lay) = lay := by
  have := lay.isLt; change _ < 3 at this
  apply Fin.ext; simp only [toLayer, ofLayer]; omega

theorem layerHeight_toLayer (lay : FORS.Layer) :
    layerHeight (toLayer lay) = FORS.layerHeight lay := by
  rcases lay with ⟨_ | _ | _ | n, h⟩ <;> first | rfl | (change _ < 3 at h; omega)

theorem layerByte_eq (lay : FORS.Layer) : FORS.layerByte lay = (toLayer lay).val := rfl

theorem maxLayerHeight_eq : FORS.maxLayerHeight = 10 := rfl

/-- A model leaf (of any layer) as the statement's. -/
def toLeaf (leaf : FORS.LeafIndex) : TreeLeafIndex := ⟨leaf.val, leaf.isLt⟩

theorem treeIndexAt_eq (index : FORS.Index) (lay : FORS.Layer) :
    FORS.Concrete.treeIndexAt index lay = treeOfIndex (toLayer lay) index := by
  apply Fin.ext
  fin_cases lay <;> rfl

theorem leafIndexAt_eq (index : FORS.Index) (lay : FORS.Layer) :
    toLeaf (FORS.Concrete.leafIndexAt index lay) = leafOfIndex (toLayer lay) index := by
  apply Fin.ext
  fin_cases lay <;> rfl

/-- **An address's bytes**: the model's fields, the tree below `2^64`, are the statement's address
of the type whose word is the model's tag. -/
theorem fieldBytes_tweakFields (addressType : AddressType) (layer tree keyPair height index : ℕ)
    (htree : tree < 2 ^ 64) :
    FORS.fieldBytes (FORS.tweakFields addressType.word layer tree keyPair height index) =
      (makeAddress layer tree addressType keyPair height index).toBytes := by
  simp only [FORS.fieldBytes, FORS.tweakFields, Address.toBytes, makeAddress,
    treeBytes_eq tree htree, List.append_assoc]
  rfl

/-- A model hash domain whose FORS node lies in its tree, as every algorithm's does. -/
def InRange : FORS.HashDomain → Prop
  | .forsNode _ _ level node => node.val < 2 ^ (10 - (level.val + 1))
  | _ => True

/-- A model hash domain as the statement's: the layer reversed, a FORS level as its height. -/
def toDomain : FORS.HashDomain → HashDomain
  | .chain lay tree leaf chainIndex step => .chain (toLayer lay) tree (toLeaf leaf) chainIndex step
  | .leaf lay tree leaf => .leaf (toLayer lay) tree (toLeaf leaf)
  | .node lay tree level nodeIndex => .node (toLayer lay) tree level nodeIndex
  | .encoding lay tree leaf => .encoding (toLayer lay) tree (toLeaf leaf)
  | .forsLeaf index forsTree leaf => .forsLeaf index forsTree leaf
  | .forsNode index forsTree level node => .forsNode index forsTree (level.val + 1) node.val
  | .forsRoots index => .forsRoots index

theorem forsTree_lt (index : FORS.Index) : index.val / 2 ^ FORS.bottomHeight < 2 ^ 64 := by
  have := index.isLt; change _ < 2 ^ 26 at this
  exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)

theorem treeOfIndex_zero (index : FORS.Index) :
    (treeOfIndex 0 index).val = index.val / 2 ^ FORS.bottomHeight := rfl

theorem leafOfIndex_zero (index : FORS.Index) :
    (leafOfIndex 0 index).val = index.val % 2 ^ FORS.bottomHeight := by
  show index.val / 2 ^ 0 % 2 ^ 8 = index.val % 2 ^ 8
  simp

/-- **The same address bytes**, for a domain in range. -/
theorem fieldBytes_hashDomainFields (domain : FORS.HashDomain) (h : InRange domain) :
    FORS.fieldBytes (FORS.hashDomainFields domain) =
      (hashDomainFields (toDomain domain)).toBytes := by
  cases domain with
  | chain lay tree leaf chainIndex step =>
    exact fieldBytes_tweakFields .wotsHash _ _ _ _ _ (lt_trans tree.isLt (by decide))
  | leaf lay tree leaf =>
    exact fieldBytes_tweakFields .wotsPublicKey _ _ _ _ _ (lt_trans tree.isLt (by decide))
  | node lay tree level nodeIndex =>
    exact fieldBytes_tweakFields .tree _ _ _ _ _ (lt_trans tree.isLt (by decide))
  | encoding lay tree leaf =>
    exact fieldBytes_tweakFields .wotsEncoding _ _ _ _ _ (lt_trans tree.isLt (by decide))
  | forsLeaf index forsTree leaf =>
    have hidx : FORS.forsTreeIndex forsTree 0 leaf.val =
        forsTreeIndex (show ForsTreeIndex from forsTree) 0 leaf.val := by
      unfold FORS.forsTreeIndex forsTreeIndex
      split
      · rfl
      · next hn => exact absurd (by simp) hn
    simp only [FORS.hashDomainFields, FORS.forsFields, hashDomainFields, hidx, treeOfIndex_zero,
      leafOfIndex_zero, toDomain]
    exact fieldBytes_tweakFields .forsTree _ _ _ _ _ (forsTree_lt index)
  | forsNode index forsTree level node =>
    have hidx : FORS.forsTreeIndex forsTree (level.val + 1) node.val =
        forsTreeIndex (show ForsTreeIndex from forsTree) (level.val + 1) node.val := by
      unfold FORS.forsTreeIndex forsTreeIndex
      split
      · rfl
      · next hn => exact absurd h hn
    simp only [FORS.hashDomainFields, FORS.forsFields, hashDomainFields, hidx, treeOfIndex_zero,
      leafOfIndex_zero, toDomain]
    exact fieldBytes_tweakFields .forsTree _ _ _ _ _ (forsTree_lt index)
  | forsRoots index =>
    simp only [FORS.hashDomainFields, FORS.forsFields, hashDomainFields, treeOfIndex_zero,
      leafOfIndex_zero, toDomain]
    exact fieldBytes_tweakFields .forsRoots _ _ _ _ _ (forsTree_lt index)

/-- **The same hash input**, for a domain in range. -/
theorem tweakableHashInput_eq (parameter : FORS.PublicParameter) (domain : FORS.HashDomain)
    (h : InRange domain) (payload : FORS.HashInput) :
    FORS.tweakableHashInput parameter domain payload =
      addressedHashInput parameter (hashDomainFields (toDomain domain)) payload := by
  simp only [FORS.tweakableHashInput, FORS.tweakBytes, fieldBytes_hashDomainFields domain h,
    addressedHashInput, hasherInput]
  rfl

/-! ## The hash -/

local notation "σ" => schemeHashOverPermutation

/-- A query of the model's hash, answered by Keccak-256 over `π`, is the statement's hash. -/
theorem simulateQ_oracleHash (input : FORS.HashInput) :
    simulateQ σ (FORS.Concrete.oracleHash (m := OracleComp FORS.HashSpec) input) =
      keccakHash queryPermutation input := by
  change simulateQ σ (LeanXmss.Verification.oracleHashWithHash (m := OracleComp SchemeHashSpec) input) = _
  simp only [LeanXmss.Verification.oracleHashWithHash, simulateQ_HasQuery_query, schemeHashOverPermutation,
    keccak256OverPermutation, keccakHash, Functor.map_map]
  refine congrArg (· <$> _) (funext fun digest ↦ ?_)
  simp only [digestBytesEquivBitVec_apply, LeanVM.Protocol.Digest.toBytes, Vector.toList]

end Sphincs.Model
