import XmssSecurity.Proof.SigningCacheTrace

namespace XmssSecurity

def SigningCacheTrace.HasEncodingInputPrehitAt
    (trace : SigningCacheTrace) (secretKey : SecretKey)
    (targetLeafIndex : LeafIndex) : Prop :=
  ∃ entry ∈ trace,
    entry.request.leafIndex = targetLeafIndex ∧ entry.EncodingInputPrehit secretKey

def SigningCacheTrace.HasEncodingInputPrehit
    (trace : SigningCacheTrace) (secretKey : SecretKey) : Prop :=
  ∃ entry ∈ trace, entry.EncodingInputPrehit secretKey

end XmssSecurity
