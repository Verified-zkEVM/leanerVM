/-
  LeanVM.E2E.Vis.PerKey.Route

  W-vis, P7: the routed oracle of a per-key reduction. Hash queries in a class are answered by a
  private lazy oracle, every other query is forwarded.
-/

module

public import LeanVM.E2E.Vis.PerKey.Defs

/-!
# The routed oracle (W-vis, P7)

`routeImpl Pr` answers a hash query in the class `Pr` from a private lazy random oracle, whose
cache is its state: the cached answer, or a fresh uniform 256-bit answer drawn with the schemes'
coins and cached. It forwards coins and every other hash query. `mergeCache Pr cPriv cPub` is the
cache that answers `Pr` from `cPriv` and the rest from `cPub`.

The partition lemma (`evalDistEq_route`, `Vis/PerKey/Partition.lean`) says that, from a public
cache with no entry in `Pr`, the routed run followed by the public lazy oracle is the lazy
oracle, the caches merged.
-/

namespace LeanVM.E2E

open OracleSpec OracleComp

@[expose] public section

/-- A fresh 256-bit answer, drawn with the schemes' coins. -/
noncomputable def freshBits : OracleComp OW LeanXmss.HashOutput :=
  liftM ($ᵗ LeanXmss.HashOutput : ProbComp LeanXmss.HashOutput)

/-- **The routed oracle**: a hash query in `Pr` answered by the private lazy oracle on the state,
coins and every other hash query forwarded. -/
noncomputable def routeImpl (Pr : List UInt8 → Prop) [DecidablePred Pr] :
    QueryImpl OW (StateT (QueryCache LeanXmss.HashSpec) (OracleComp OW))
  | .inl n => (liftM (liftM (OW.query (.inl n)) : OracleComp OW _) :
      StateT (QueryCache LeanXmss.HashSpec) (OracleComp OW) _)
  | .inr x =>
    if Pr x then StateT.mk fun c ↦
      match c x with
      | some u => pure (u, c)
      | none => (fun u ↦ (u, c.cacheQuery x u)) <$> freshBits
    else (liftM (liftM (OW.query (.inr x)) : OracleComp OW _) :
      StateT (QueryCache LeanXmss.HashSpec) (OracleComp OW) _)

/-- **Two caches merged**: `Pr` answered by `cPriv`, the rest by `cPub`. -/
def mergeCache (Pr : List UInt8 → Prop) [DecidablePred Pr]
    (cPriv cPub : QueryCache LeanXmss.HashSpec) : QueryCache LeanXmss.HashSpec :=
  QueryCache.ofFn fun x ↦ if Pr x then cPriv x else cPub x

end
end LeanVM.E2E
