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
