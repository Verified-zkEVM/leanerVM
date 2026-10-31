module

public import XmssSecurity.Proof.ExactQueryCount
public import XmssSecurity.Proof.CacheReplayEval
public import XmssSecurity.Proof.DetailedExecution
public import XmssSecurity.Proof.CappedChain.EncodingQueryBound
public import XmssSecurity.Proof.QueryBoundSupport
public import XmssSecurity.Proof.IdealStatement
public import XmssSecurity.Proof.StatementLemmas
public import VCVio.OracleComp.QueryTracking.SubSpec

@[expose] public section

open OracleComp OracleSpec
open scoped BigOperators

namespace XmssSecurity

def treeHashQueryCount : Nat → Nat
  | 0 => numChains * (chainLength - 1) + 1
  | levels + 1 => 2 * treeHashQueryCount levels + 1

namespace ExactQueryCount

theorem oneTimePublicKey (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (leafIndex : LeafIndex) :
    ExactQueryCount
      (Concrete.oneTimePublicKey (m := OracleComp HashSpec) parameter secret leafIndex)
      (numChains * (chainLength - 1)) := by
  unfold Concrete.oneTimePublicKey
  have hexact := sequenceFin
    (fun chain : ChainIndex =>
      Concrete.chainWalk (m := OracleComp HashSpec) parameter leafIndex chain 0
        (chainLength - 1) (secret leafIndex chain))
    (fun _ : ChainIndex => chainLength - 1)
    (fun chain => chainWalk parameter leafIndex chain 0 (chainLength - 1)
      (secret leafIndex chain) (by omega))
  simpa using hexact

theorem leafAt (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (leafIndex : LeafIndex) :
    ExactQueryCount
      (Concrete.leafAt (m := OracleComp HashSpec) parameter secret leafIndex)
      (numChains * (chainLength - 1) + 1) := by
  unfold Concrete.leafAt
  exact (oneTimePublicKey parameter secret leafIndex).bind
    (fun endpoints => Concrete.leafHash parameter leafIndex endpoints) 1
    (fun endpoints => tweakableHash parameter (.leaf leafIndex)
      (Concrete.leafPayload endpoints))

end ExactQueryCount

def IsHashQuery : OracleWorld.Domain → Prop := fun input => input matches .inr _

instance : DecidablePred IsHashQuery := by
  intro input
  cases input <;> unfold IsHashQuery <;> exact inferInstance

namespace ExactQueryCount.ExactPredicateQueryCount

end ExactQueryCount.ExactPredicateQueryCount

/-- The after-key-generation budget bounds every run after key generation. -/
theorem afterKeygen_hashQueryBound (adversary : Adversary) (q : Nat)
    (hbound : HasAfterKeygenHashQueryBound Concrete.scheme adversary q)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅)) :
    HashQueryBound (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)
      keyResult.2 q := by
  have hrest : HashQueryBound
      (Seeded.gameRest Concrete.scheme adversary keyResult.1.1 keyResult.1.2) keyResult.2 q := by
    simp only [HashQueryBound, simulateQ_countHashQueries]
    exact hbound keyResult hkeyResult
  have hmap : GameOutcome.won <$>
      detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2 =
        Seeded.gameRest Concrete.scheme adversary keyResult.1.1 keyResult.1.2 := by
    classical
    simp [Seeded.gameRest, detailedGameAfterKeygen, GameOutcome.won]
  exact (hashQueryBound_iff_of_map_eq hmap _ _).mpr hrest

namespace CappedChain

theorem sourceUnloggedDetailedGameAfterKeygen_hashQueryBound_sub_keygen
    (q : Nat) (adversary : Adversary) (hbound : HasAfterKeygenHashQueryBound Concrete.scheme adversary q)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅)) :
    HashQueryBound (sourceUnloggedDetailedGameAfterKeygen adversary keyResult.1.1 keyResult.1.2)
      keyResult.2 q :=
  (hashQueryBound_iff_of_map_eq
    (detailedGameAfterKeygen_unlogged_projection adversary keyResult.1.1 keyResult.1.2) _ _).mp
      (afterKeygen_hashQueryBound adversary q hbound keyResult hkeyResult)

end CappedChain

end XmssSecurity
