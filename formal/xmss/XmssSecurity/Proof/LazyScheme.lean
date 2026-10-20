import XmssSecurity.Proof.IdealStatement
import XmssSecurity.Proof.StatementLemmas

open OracleComp OracleSpec

namespace XmssSecurity

def SecretKey.withoutPrecomputation
    (parameter : PublicParameter) (chainStart : LeafIndex → ChainIndex → Digest) :
    SecretKey :=
  ⟨parameter, chainStart, fun _ _ _ => 0, fun _ _ => 0⟩

namespace Concrete

noncomputable local instance : SampleableType (LeafIndex → ChainIndex → Digest) :=
  SampleableType.ofFintype (LeafIndex → ChainIndex → Digest)

@[simp]
theorem probOutput_sampleSecret
    (secret : LeafIndex → ChainIndex → Digest) :
    Pr[= secret | sampleSecret] =
      (Fintype.card (LeafIndex → ChainIndex → Digest) : ENNReal)⁻¹ := by
  rw [sampleSecret_eq]
  exact probOutput_uniformSample (LeafIndex → ChainIndex → Digest) secret

noncomputable def keygen : OracleComp OracleWorld (PublicKey × SecretKey) := do
  let parameter ← liftM samplePublicParameter
  let secret ← liftM sampleSecret
  let root ← liftM
    (treeNode parameter secret treeHeight rootNode : OracleComp HashSpec Digest)
  return (⟨root, parameter⟩, SecretKey.withoutPrecomputation parameter secret)

attribute [irreducible] keygen

def signedChainValues {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (secretKey : SecretKey) (leafIndex : LeafIndex) (encoding : Encoding) :
    m (ChainIndex → Digest) :=
  sequenceFin fun chain =>
    chainWalk secretKey.parameter leafIndex chain 0 (encoding chain).val
      (secretKey.chainStart leafIndex chain)

def authenticationPath {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (secretKey : SecretKey) (leafIndex : LeafIndex) : m (Fin treeHeight → Digest) :=
  sequenceFin fun level =>
    treeNode secretKey.parameter secretKey.chainStart level.val
      (authenticationPathNode leafIndex level)

def signWithEncoding {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (secretKey : SecretKey) (leafIndex : LeafIndex) (randomness : Randomness)
    (encoding : Encoding) : m Signature := do
  let chainValue ← signedChainValues secretKey leafIndex encoding
  let authPath ← authenticationPath secretKey leafIndex
  return ⟨randomness, chainValue, authPath⟩

noncomputable def signAttempt {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (randomness : Randomness) : m (Option Signature) := do
  let digest ← encodingHash secretKey.parameter leafIndex message randomness
  match TargetSum.decodeDigest digest with
  | none => pure none
  | some encoding => some <$> signWithEncoding secretKey leafIndex randomness encoding

noncomputable def sign (secretKey : SecretKey)
    (leafIndex : LeafIndex) (message : Message) : OracleComp OracleWorld (Option Signature) := do
  let randomness ← liftM signingRandomness
  liftM (signAttempt secretKey leafIndex message randomness :
    OracleComp HashSpec (Option Signature))

theorem sign_eq (secretKey : SecretKey)
    (leafIndex : LeafIndex) (message : Message) :
    sign secretKey leafIndex message = (do
      let randomness ← liftM signingRandomness
      liftM (signAttempt secretKey leafIndex message randomness :
        OracleComp HashSpec (Option Signature))) := rfl

attribute [irreducible] sign

noncomputable def signBoundedAttempts : Nat → SecretKey → LeafIndex → Message →
    OracleComp OracleWorld (Option Signature)
  | 0, _secretKey, _leafIndex, _message => pure none
  | attempts + 1, secretKey, leafIndex, message => do
      let randomness ← liftM signingRandomness
      let result ← liftM (signAttempt secretKey leafIndex message randomness :
        OracleComp HashSpec (Option Signature))
      match result with
      | some signature => pure (some signature)
      | none => signBoundedAttempts attempts secretKey leafIndex message

noncomputable def cappedSign (secretKey : SecretKey)
    (leafIndex : LeafIndex) (message : Message) : OracleComp OracleWorld (Option Signature) :=
  signBoundedAttempts signingAttemptLimit secretKey leafIndex message

theorem cappedSign_eq (secretKey : SecretKey)
    (leafIndex : LeafIndex) (message : Message) :
    cappedSign secretKey leafIndex message =
      signBoundedAttempts signingAttemptLimit secretKey leafIndex message := rfl

attribute [irreducible] cappedSign

def erasePrecomputation (secretKey : SecretKey) : SecretKey :=
  SecretKey.withoutPrecomputation secretKey.parameter secretKey.chainStart

def erasePrecomputedKeyResult (result : PublicKey × SecretKey) :
    PublicKey × SecretKey :=
  (result.1, erasePrecomputation result.2)

theorem erasePrecomputedKeygen_eq_keygen :
    erasePrecomputedKeyResult <$> precomputedKeygen = keygen := by
  unfold precomputedKeygen keygen
  simp only [erasePrecomputedKeyResult, erasePrecomputation,
    precomputedSecretKey, map_bind, map_pure]
  apply bind_congr
  intro parameter
  apply bind_congr
  intro secret
  rw [bind_pure_comp, bind_pure_comp]
  rw [← liftM_map, ← liftM_map]
  apply congrArg (fun computation : OracleComp HashSpec (PublicKey × SecretKey) =>
    (liftM computation : OracleComp OracleWorld (PublicKey × SecretKey)))
  calc
    (fun result : Digest × QueryLog HashSpec =>
        (PublicKey.mk result.1 parameter,
          SecretKey.withoutPrecomputation parameter secret)) <$>
        (treeNode parameter secret treeHeight rootNode :
          OracleComp HashSpec Digest).withQueryLog =
      (fun root : Digest =>
        (PublicKey.mk root parameter,
          SecretKey.withoutPrecomputation parameter secret)) <$>
        (Prod.fst <$> (treeNode parameter secret treeHeight rootNode :
          OracleComp HashSpec Digest).withQueryLog) := by
            rw [Functor.map_map]
    _ = _ := congrArg
      (fun computation : OracleComp HashSpec Digest =>
        (fun root : Digest =>
          (PublicKey.mk root parameter,
            SecretKey.withoutPrecomputation parameter secret)) <$> computation)
      (loggingOracle.fst_map_run_simulateQ
        (treeNode parameter secret treeHeight rootNode :
          OracleComp HashSpec Digest))

end Concrete

end XmssSecurity
