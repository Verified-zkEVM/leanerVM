import XmssSecurity.Proof.KeygenCache
import XmssSecurity.Proof.CausalTreeCoupling
import XmssSecurity.Proof.StatementLemmas

open OracleComp OracleSpec

namespace XmssSecurity

def hashCacheLookup (cache : QueryCache HashSpec) (input : HashInput) :
    Option HashOutput :=
  cache input

def MerkleHashInput
    (parameter : PublicParameter) (input : HashInput) : Prop :=
  ∃ level node, AtHashAddress parameter (.merkle level node) input

def LeafCacheOutputsCorrespond
    (parameter : PublicParameter)
    (leftEndpoints rightEndpoints : LeafIndex → ChainIndex → Digest)
    (left right : QueryCache HashSpec) : Prop :=
  ∀ leafIndex,
    hashCacheLookup left (Concrete.CacheView.leafInput parameter leafIndex
      (leftEndpoints leafIndex)) =
    hashCacheLookup right (Concrete.CacheView.leafInput parameter leafIndex
      (rightEndpoints leafIndex))

def LeafReplayOutputsCorrespond
    (parameter : PublicParameter)
    (leftSecret rightSecret : LeafIndex → ChainIndex → Digest)
    (leftCache rightCache : QueryCache HashSpec) : Prop :=
  ∀ leafIndex,
    hashCacheLookup leftCache (Concrete.CacheView.leafInput parameter leafIndex
      (Concrete.CacheReplay.oneTimePublicKey leftCache parameter
        leftSecret leafIndex)) =
    hashCacheLookup rightCache (Concrete.CacheView.leafInput parameter leafIndex
      (Concrete.CacheReplay.oneTimePublicKey rightCache parameter
        rightSecret leafIndex))

def ReplayEndpointsMatch
    (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest)
    (endpoints : LeafIndex → ChainIndex → Digest)
    (cache : QueryCache HashSpec) : Prop :=
  ∀ leafIndex,
    endpoints leafIndex =
      Concrete.CacheReplay.oneTimePublicKey cache parameter secret leafIndex

theorem Concrete.CacheView.chainInput_ne_merkleInput
    (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (step : ChainStep) (value : Digest) (level : MerkleLevel)
    (node : MerkleNode) (left right : Digest) :
    Concrete.CacheView.chainInput parameter leafIndex chain step value ≠
      Concrete.CacheView.merkleInput parameter level node left right := by
  intro heq
  have hdomain := domain_eq_of_tweakableHashInput_eq parameter heq
  simp at hdomain

theorem Concrete.CacheView.chainInput_ne_leafInput
    (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (step : ChainStep) (value : Digest) (targetLeafIndex : LeafIndex)
    (endpoints : ChainIndex → Digest) :
    Concrete.CacheView.chainInput parameter leafIndex chain step value ≠
      Concrete.CacheView.leafInput parameter targetLeafIndex endpoints := by
  intro heq
  have hdomain := domain_eq_of_tweakableHashInput_eq parameter heq
  simp at hdomain

theorem Concrete.CacheView.leafInput_ne_merkleInput
    (parameter : PublicParameter) (leafIndex : LeafIndex)
    (endpoints : ChainIndex → Digest) (level : MerkleLevel)
    (node : MerkleNode) (left right : Digest) :
    Concrete.CacheView.leafInput parameter leafIndex endpoints ≠
      Concrete.CacheView.merkleInput parameter level node left right := by
  intro heq
  have hdomain := domain_eq_of_tweakableHashInput_eq parameter heq
  simp at hdomain

theorem Concrete.CacheView.chainStep_cacheQuery_merkleInput
    (cache : QueryCache HashSpec) (output : HashOutput)
    (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (level : MerkleLevel) (node : MerkleNode) (left right : Digest) :
    Concrete.CacheView.chainStep
        (cache.cacheQuery
          (Concrete.CacheView.merkleInput parameter level node left right)
          output) parameter leafIndex chain =
      Concrete.CacheView.chainStep cache parameter leafIndex chain := by
  funext position value
  unfold Concrete.CacheView.chainStep
  split
  · unfold Concrete.CacheView.digestAt
    rw [QueryCache.cacheQuery_of_ne]
    exact Concrete.CacheView.chainInput_ne_merkleInput parameter leafIndex chain
      _ value level node left right
  · rfl

theorem Concrete.CacheView.chainStep_cacheQuery_leafInput
    (cache : QueryCache HashSpec) (output : HashOutput)
    (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (targetLeafIndex : LeafIndex) (endpoints : ChainIndex → Digest) :
    Concrete.CacheView.chainStep
        (cache.cacheQuery
          (Concrete.CacheView.leafInput parameter targetLeafIndex endpoints)
          output) parameter leafIndex chain =
      Concrete.CacheView.chainStep cache parameter leafIndex chain := by
  funext position value
  unfold Concrete.CacheView.chainStep
  split
  · unfold Concrete.CacheView.digestAt
    rw [QueryCache.cacheQuery_of_ne]
    exact Concrete.CacheView.chainInput_ne_leafInput parameter leafIndex chain
      _ value targetLeafIndex endpoints
  · rfl

theorem Concrete.CacheReplay.oneTimePublicKey_cacheQuery_merkleInput
    (cache : QueryCache HashSpec) (output : HashOutput)
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (leafIndex : LeafIndex) (level : MerkleLevel) (node : MerkleNode)
    (left right : Digest) :
    Concrete.CacheReplay.oneTimePublicKey
        (cache.cacheQuery
          (Concrete.CacheView.merkleInput parameter level node left right)
          output) parameter secret leafIndex =
      Concrete.CacheReplay.oneTimePublicKey cache parameter secret leafIndex := by
  unfold Concrete.CacheReplay.oneTimePublicKey
  funext chain
  rw [Concrete.CacheView.chainStep_cacheQuery_merkleInput]

theorem Concrete.CacheReplay.oneTimePublicKey_cacheQuery_leafInput
    (cache : QueryCache HashSpec) (output : HashOutput)
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (leafIndex targetLeafIndex : LeafIndex) (endpoints : ChainIndex → Digest) :
    Concrete.CacheReplay.oneTimePublicKey
        (cache.cacheQuery
          (Concrete.CacheView.leafInput parameter targetLeafIndex endpoints)
          output) parameter secret leafIndex =
      Concrete.CacheReplay.oneTimePublicKey cache parameter secret leafIndex := by
  unfold Concrete.CacheReplay.oneTimePublicKey
  funext chain
  rw [Concrete.CacheView.chainStep_cacheQuery_leafInput]

theorem ReplayEndpointsMatch.cacheQuery_merkleInput
    (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest)
    (endpoints : LeafIndex → ChainIndex → Digest)
    (cache : QueryCache HashSpec)
    (hrel : ReplayEndpointsMatch parameter secret endpoints cache)
    (level : MerkleLevel) (node : MerkleNode) (left right : Digest)
    (output : HashOutput) :
    ReplayEndpointsMatch parameter secret endpoints
      (cache.cacheQuery
        (Concrete.CacheView.merkleInput parameter level node left right)
        output) := by
  intro leafIndex
  rw [Concrete.CacheReplay.oneTimePublicKey_cacheQuery_merkleInput]
  exact hrel leafIndex

theorem ReplayEndpointsMatch.cacheQuery_leafInput
    (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest)
    (endpoints : LeafIndex → ChainIndex → Digest)
    (cache : QueryCache HashSpec)
    (hrel : ReplayEndpointsMatch parameter secret endpoints cache)
    (targetLeafIndex : LeafIndex) (targetEndpoints : ChainIndex → Digest)
    (output : HashOutput) :
    ReplayEndpointsMatch parameter secret endpoints
      (cache.cacheQuery
        (Concrete.CacheView.leafInput parameter targetLeafIndex targetEndpoints)
        output) := by
  intro leafIndex
  rw [Concrete.CacheReplay.oneTimePublicKey_cacheQuery_leafInput]
  exact hrel leafIndex

theorem LeafCacheOutputsCorrespond.cacheQuery_distinct
    (parameter : PublicParameter)
    (leftEndpoints rightEndpoints : LeafIndex → ChainIndex → Digest)
    (left right : QueryCache HashSpec)
    (hrel : LeafCacheOutputsCorrespond parameter leftEndpoints rightEndpoints
      left right)
    (leftInput rightInput : HashInput) (output : HashOutput)
    (hleft : ∀ leafIndex, leftInput ≠ Concrete.CacheView.leafInput parameter
      leafIndex (leftEndpoints leafIndex))
    (hright : ∀ leafIndex, rightInput ≠ Concrete.CacheView.leafInput parameter
      leafIndex (rightEndpoints leafIndex)) :
    LeafCacheOutputsCorrespond parameter leftEndpoints rightEndpoints
      (left.cacheQuery leftInput output) (right.cacheQuery rightInput output) := by
  intro leafIndex
  unfold hashCacheLookup
  rw [QueryCache.cacheQuery_of_ne left output (hleft leafIndex).symm,
    QueryCache.cacheQuery_of_ne right output (hright leafIndex).symm]
  exact hrel leafIndex

theorem Concrete.CacheView.leafInput_eq_iff
    (parameter : PublicParameter)
    (leftLeafIndex rightLeafIndex : LeafIndex)
    (leftEndpoints rightEndpoints : ChainIndex → Digest) :
    Concrete.CacheView.leafInput parameter leftLeafIndex leftEndpoints =
        Concrete.CacheView.leafInput parameter rightLeafIndex rightEndpoints ↔
      leftLeafIndex = rightLeafIndex ∧ leftEndpoints = rightEndpoints := by
  constructor
  · intro heq
    have hleafIndex : leftLeafIndex = rightLeafIndex := by
      have hdomain := domain_eq_of_tweakableHashInput_eq parameter heq
      simpa using hdomain
    subst rightLeafIndex
    exact ⟨rfl, Concrete.CacheView.leafInput_injective parameter leftLeafIndex heq⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem LeafCacheOutputsCorrespond.cacheQuery_pair
    (parameter : PublicParameter)
    (leftEndpoints rightEndpoints : LeafIndex → ChainIndex → Digest)
    (left right : QueryCache HashSpec)
    (hrel : LeafCacheOutputsCorrespond parameter leftEndpoints rightEndpoints
      left right)
    (leafIndex : LeafIndex) (output : HashOutput) :
    LeafCacheOutputsCorrespond parameter leftEndpoints rightEndpoints
      (left.cacheQuery
        (Concrete.CacheView.leafInput parameter leafIndex (leftEndpoints leafIndex))
          output)
      (right.cacheQuery
        (Concrete.CacheView.leafInput parameter leafIndex (rightEndpoints leafIndex))
          output) := by
  intro candidate
  unfold hashCacheLookup
  by_cases hleafIndex : candidate = leafIndex
  · subst candidate
    simp only [QueryCache.cacheQuery_self]
  · rw [QueryCache.cacheQuery_of_ne left output (by
        intro heq
        exact hleafIndex ((Concrete.CacheView.leafInput_eq_iff parameter candidate
          leafIndex (leftEndpoints candidate) (leftEndpoints leafIndex)).mp heq).1),
      QueryCache.cacheQuery_of_ne right output (by
        intro heq
        exact hleafIndex ((Concrete.CacheView.leafInput_eq_iff parameter candidate
          leafIndex (rightEndpoints candidate) (rightEndpoints leafIndex)).mp heq).1)]
    exact hrel candidate

def chainEndpointDigit : Digit :=
  ⟨chainLength - 1, by decide⟩

end XmssSecurity
