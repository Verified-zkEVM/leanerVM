/-
  LeanVM.Guest.WithHashBridge

  The guest's deployed definitions, over Keccak-f[1600] in the statement, are the proofs' forms with
  the deployed Keccak-256 and Keccak-f[1600] (`LeanVM.Guest.WithHash`).
-/

module

public import LeanVM.Protocol.WithHashBridge
public import LeanVM.Guest.WithHash
public import LeanDa.WithHashBridge
public import Common.WithHash
public import Sphincs.WithHash

/-!
# The guest's deployed definitions are the forms with a hash

The statement's guest specification computes over Keccak-f[1600], Keccak-256 the sponge over it;
the proofs' forms take Keccak-256 as a function of its own. With Keccak-f[1600] in `Id` the sponge
is the deployed Keccak-256 (`keccak256With_keccakF1600`), so:

* the batching's run, the verifier refusing a zero challenge, the deferring verifier refusing a zero
  challenge, the openings' climb (`runBatching_deployed`, …);
* LeanDA's commitment and vector digest (`commitCodewords_keccakF1600`, `vectorDigest_keccakF1600`);
* the signature schemes' verification (`xmssVerify_eq_withHash`, `sphincsVerify_eq_withHash`): the
  schemes read a digest as a 256-bit number through its 32 bytes (`Common.SufCma.digestBitVec`),
  which is the guest's little-endian reading (`digestBitVec_toBytes`).
-/

@[expose] public section

namespace LeanVM

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

/-- **A digest's bytes read as a number, through `digestBitVec`, are its little-endian reading.** -/
theorem digestBitVec_toBytes (d : Digest) :
    Common.SufCma.digestBitVec d.toBytes = Node.digestBits d :=
  Fast.SufCma.digestBitVec_eq_digestBitVecFold d.toBytes

/-- Keccak-256 over Keccak-f[1600], read as the schemes' hash output, is `keccakBits`. -/
theorem keccakHash_keccakF1600 :
    HashSig.Concrete.keccakHash (m := Id) keccakF1600 = Node.keccakBits := by
  funext input
  rw [HashSig.Concrete.keccakHash, keccak256With_keccakF1600]
  change Common.SufCma.digestBitVec (keccak256 input).toBytes = Node.digestBits (keccak256 input)
  exact digestBitVec_toBytes _

/-- The statement's leanXMSS verification over `π` is the hash-query one with the hash Keccak-256
over `π`. -/
theorem xmss_verify_eq_verifyWithHash {m : Type → Type} [Monad m]
    (π : KeccakState → m KeccakState) (pk : HashSig.PublicKey) (message : HashSig.Message)
    (σ : LeanXmss.Signature) :
    LeanXmss.Concrete.verify π pk message σ =
      @LeanXmss.Concrete.verifyWithHash m _ ⟨HashSig.Concrete.keccakHash π⟩ pk message σ := rfl

/-- The statement's leanSPHINCS verification over `π` is the hash-query one with the hash
Keccak-256 over `π`. -/
theorem sphincs_verify_eq_verifyWithHash {m : Type → Type} [Monad m]
    (π : KeccakState → m KeccakState) (pk : Sphincs.PublicKey) (message : Sphincs.Message)
    (σ : Sphincs.Signature) :
    Sphincs.Concrete.verify π pk message σ =
      @Sphincs.Concrete.verifyWithHash m _ ⟨HashSig.Concrete.keccakHash π⟩ pk message σ := rfl

namespace Node

/-- leanXMSS verification over Keccak-f[1600] is the hash-query verification with `keccakBits`. -/
theorem xmssVerify_eq_withHash (pk : HashSig.PublicKey) (message : HashSig.Message)
    (σ : LeanXmss.Signature) :
    xmssVerify pk message σ =
      Id.run (@LeanXmss.Concrete.verifyWithHash Id _ ⟨keccakBits⟩ pk message σ) := by
  rw [xmssVerify, xmss_verify_eq_verifyWithHash, keccakHash_keccakF1600]

/-- leanSPHINCS verification over Keccak-f[1600] is the hash-query verification with
`keccakBits`. -/
theorem sphincsVerify_eq_withHash (pk : Sphincs.PublicKey) (message : Sphincs.Message)
    (σ : Sphincs.Signature) :
    sphincsVerify pk message σ =
      Id.run (@Sphincs.Concrete.verifyWithHash Id _ ⟨keccakBits⟩ pk message σ) := by
  rw [sphincsVerify, sphincs_verify_eq_verifyWithHash, keccakHash_keccakF1600]

end Node

namespace Da

/-- LeanDA's hash over Keccak-f[1600] is Keccak-256 as LeanDA's hash. -/
theorem hashOver_keccakF1600 : LeanDa.hashOver keccakF1600 = keccak256Bytes := rfl

theorem commitCodewords_keccakF1600 (rows : List (List K)) :
    LeanDa.commitCodewords keccakF1600 rows = LeanDa.commitCodewordsWithHash keccak256Bytes rows :=
      by
  rw [LeanDa.commitCodewords_eq_withHash, hashOver_keccakF1600]

theorem vectorDigest_keccakF1600 (vector : List E) :
    LeanDa.vectorDigest keccakF1600 vector = LeanDa.vectorDigestWithHash keccak256Bytes vector := by
  rw [LeanDa.vectorDigest_eq_withHash, hashOver_keccakF1600]

end Da

namespace Guest

theorem Batch.runBatching_deployed (prog : Prog Bool) (proof : Proof) :
    Batch.runBatching (m := Id) keccakF1600 prog proof =
      Batch.runBatchingWithHash (m := Id) keccak256 keccakF1600 prog proof := by
  simp only [Batch.runBatching, Batch.runBatchingWithHash, runProof_eq_withHash,
    keccak256With_keccakF1600]

theorem Budget.verifierRefusingZero_deployed (prog : Program) (input : PublicInput)
    (proof : Proof) :
    Budget.verifierRefusingZero (m := Id) keccakF1600 prog input proof =
      Budget.verifierRefusingZeroWithHash (m := Id) keccak256 keccakF1600 prog input proof := by
  simp only [Budget.verifierRefusingZero, Budget.verifierRefusingZeroWithHash, seedWith_eq_withHash,
    runProof_eq_withHash, keccak256With_keccakF1600]

theorem Limits.verifyDeferredRefusingZero_eq_withHash (bytecode : List K) (iv publicInput : Digest)
    (c : BytecodeClaim) (π : Proof) :
    Limits.verifyDeferredRefusingZero bytecode iv publicInput c π =
      Id.run (runProofWithHash (m := Id) keccak256 keccakF1600
        (deferredProgram c bytecode publicInput).refusingZeroChallenge
        (keccakF1600 (seedInput iv publicInput)) π) := by
  rw [Limits.verifyDeferredRefusingZero, runProof_eq_withHash, keccak256With_keccakF1600]

theorem Limits.climbTo_eq_withHash (node : Digest) (q : ℕ) (path : List Digest) :
    Limits.climbTo node q path = Id.run (climbWithHash (m := Id) keccak256 node q path) := by
  rw [Limits.climbTo, climb_eq_withHash, keccak256With_keccakF1600]

end Guest

end LeanVM

end
