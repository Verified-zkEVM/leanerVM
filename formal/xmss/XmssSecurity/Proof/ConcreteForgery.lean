import XmssSecurity.Proof.IdealStatement
import XmssSecurity.Proof.StatementLemmas
import XmssSecurity.Proof.ForgeryCases

open OracleSpec

namespace XmssSecurity.Concrete

theorem same_signaturePath_iff {left right : Signature} :
    Merkle.SamePathSegment (signaturePath left) (signaturePath right) 0 treeHeight ↔
      left.authPath = right.authPath := by
  constructor
  · intro hpath
    funext level
    have heq := hpath level.val level.isLt
    simpa [signaturePath] using heq
  · intro hpath level hlevel
    simp [signaturePath, hlevel, hpath]

theorem strong_components {signedMessage forgedMessage : Message}
    {signedSignature forgedSignature : Signature}
    (hstrong : signedMessage ≠ forgedMessage ∨ signedSignature ≠ forgedSignature) :
    (signedMessage, signedSignature.randomness) ≠
        (forgedMessage, forgedSignature.randomness) ∨
      signedSignature.chainValue ≠ forgedSignature.chainValue ∨
      ¬Merkle.SamePathSegment (signaturePath signedSignature)
        (signaturePath forgedSignature) 0 treeHeight := by
  by_cases hinput :
      (signedMessage, signedSignature.randomness) =
        (forgedMessage, forgedSignature.randomness)
  · by_cases hvalues : signedSignature.chainValue = forgedSignature.chainValue
    · right
      right
      intro hpath
      apply hstrong.elim
      · intro hmessage
        exact hmessage (congrArg Prod.fst hinput)
      · intro hsignature
        apply hsignature
        have hauth := same_signaturePath_iff.mp hpath
        cases signedSignature
        cases forgedSignature
        simp_all
    · exact Or.inr (Or.inl hvalues)
  · exact Or.inl hinput

noncomputable def SameLeafIndexBadEventOccurs
    (cache : QueryCache HashSpec) (parameter : PublicParameter) (leafIndex : LeafIndex)
    (signedMessage forgedMessage : Message)
    (signedEncoding forgedEncoding : Encoding)
    (signedSignature forgedSignature : Signature)
    (hsignedValid : TargetSum.Valid signedEncoding) : BadEvent → Prop :=
  XmssSecurity.SameLeafIndexBadEventOccurs
    (CacheView.encodingHash cache parameter leafIndex)
    (fun chain => CacheView.chainStep cache parameter leafIndex chain)
    (CacheView.leafHash cache parameter leafIndex)
    (CacheView.nodeHash cache parameter leafIndex)
    (signedMessage, signedSignature.randomness)
    (forgedMessage, forgedSignature.randomness)
    signedEncoding forgedEncoding
    signedSignature.chainValue forgedSignature.chainValue
    (signaturePath signedSignature) (signaturePath forgedSignature)
    hsignedValid

/-- Concrete same-leaf-index strong forgeries select one of the 175 cache-level bad events. -/
theorem sameLeafIndex_forgery_has_badEvent
    (cache : QueryCache HashSpec) (parameter : PublicParameter) (leafIndex : LeafIndex)
    (signedMessage forgedMessage : Message)
    (signedEncoding forgedEncoding : Encoding)
    (signedSignature forgedSignature : Signature)
    (hsignedEncoding : TargetSum.decodeDigest
      (CacheView.encodingHash cache parameter leafIndex
        (signedMessage, signedSignature.randomness)) = some signedEncoding)
    (hforgedEncoding : TargetSum.decodeDigest
      (CacheView.encodingHash cache parameter leafIndex
        (forgedMessage, forgedSignature.randomness)) = some forgedEncoding)
    (hroot : Merkle.ascend (CacheView.nodeHash cache parameter leafIndex)
        (signaturePath forgedSignature) 0 treeHeight
        (CacheView.leafHash cache parameter leafIndex
          (recoveredEndpoints
            (fun chain => CacheView.chainStep cache parameter leafIndex chain)
            forgedEncoding forgedSignature.chainValue)) =
      Merkle.ascend (CacheView.nodeHash cache parameter leafIndex)
        (signaturePath signedSignature) 0 treeHeight
        (CacheView.leafHash cache parameter leafIndex
          (recoveredEndpoints
            (fun chain => CacheView.chainStep cache parameter leafIndex chain)
            signedEncoding signedSignature.chainValue)))
    (hstrong : signedMessage ≠ forgedMessage ∨ signedSignature ≠ forgedSignature) :
    ∃ event, SameLeafIndexBadEventOccurs cache parameter leafIndex
      signedMessage forgedMessage signedEncoding forgedEncoding
      signedSignature forgedSignature
      (TargetSum.decodeDigest_eq_some_iff.mp hsignedEncoding).2 event := by
  exact XmssSecurity.sameLeafIndex_forgery_has_badEvent
    (CacheView.encodingHash cache parameter leafIndex)
    (fun chain => CacheView.chainStep cache parameter leafIndex chain)
    (CacheView.leafHash cache parameter leafIndex)
    (CacheView.nodeHash cache parameter leafIndex)
    (signedMessage, signedSignature.randomness)
    (forgedMessage, forgedSignature.randomness)
    signedEncoding forgedEncoding
    signedSignature.chainValue forgedSignature.chainValue
    (signaturePath signedSignature) (signaturePath forgedSignature)
    hsignedEncoding hforgedEncoding hroot (strong_components hstrong)

noncomputable def FreshLeafIndexBadEventOccurs
    (cache : QueryCache HashSpec) (parameter : PublicParameter) (leafIndex : LeafIndex)
    (forgedEncoding : Encoding) (forgedSignature : Signature)
    (secret : ChainIndex → Digest) (honestPath : Nat → Digest)
    (hforgedValid : TargetSum.Valid forgedEncoding) : BadEvent → Prop :=
  XmssSecurity.FreshLeafIndexBadEventOccurs
    (fun chain => CacheView.chainStep cache parameter leafIndex chain)
    (CacheView.leafHash cache parameter leafIndex)
    (CacheView.nodeHash cache parameter leafIndex)
    forgedEncoding forgedSignature.chainValue secret
    (signaturePath forgedSignature) honestPath hforgedValid

/-- Concrete fresh-leaf-index forgeries select one of the same 175 cache-level bad events. -/
theorem freshLeafIndex_forgery_has_badEvent
    (cache : QueryCache HashSpec) (parameter : PublicParameter) (leafIndex : LeafIndex)
    (forgedEncoding : Encoding) (forgedSignature : Signature)
    (secret : ChainIndex → Digest) (honestPath : Nat → Digest)
    (hforgedValid : TargetSum.Valid forgedEncoding)
    (hroot : Merkle.ascend (CacheView.nodeHash cache parameter leafIndex)
        (signaturePath forgedSignature) 0 treeHeight
        (CacheView.leafHash cache parameter leafIndex
          (recoveredEndpoints
            (fun chain => CacheView.chainStep cache parameter leafIndex chain)
            forgedEncoding forgedSignature.chainValue)) =
      Merkle.ascend (CacheView.nodeHash cache parameter leafIndex)
        honestPath 0 treeHeight
        (CacheView.leafHash cache parameter leafIndex
          (fun chain => Wots.publicChain
            (CacheView.chainStep cache parameter leafIndex chain) (secret chain)))) :
    ∃ event, FreshLeafIndexBadEventOccurs cache parameter leafIndex forgedEncoding
      forgedSignature secret honestPath hforgedValid event := by
  exact XmssSecurity.freshLeafIndex_forgery_has_badEvent
    (fun chain => CacheView.chainStep cache parameter leafIndex chain)
    (CacheView.leafHash cache parameter leafIndex)
    (CacheView.nodeHash cache parameter leafIndex)
    forgedEncoding forgedSignature.chainValue secret
    (signaturePath forgedSignature) honestPath hforgedValid hroot

end XmssSecurity.Concrete
