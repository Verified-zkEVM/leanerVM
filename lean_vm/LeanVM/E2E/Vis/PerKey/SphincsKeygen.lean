/-
  LeanVM.E2E.Vis.PerKey.SphincsKeygen

  W-vis, P7b: the other keys' generation, routed by class in the game and partly privately in the
  per-key leanSPHINCS reduction, agree on keys whose parameter is not key `j`'s.
-/

module

public import LeanVM.E2E.Vis.PerKey.SphincsRest
public import LeanVM.E2E.Vis.PerKey.XmssKeygen

/-!
# The other keys' generation, in the leanSPHINCS reduction (W-vis, P7b)

The leanSPHINCS counterpart of `Vis/PerKey/XmssKeygen.lean`'s `ΦJ` part. Under the single-key
game's oracles, the reduction's generations are the common prefix (`PerKeyX.xPrefix'`,
`PerKeyX.sPrefix'`), then the tree private (`ΦJS_xKeygenRS`, `ΦJS_sKeygenRS`). The class-routed
game routes the tree by class; when the derived parameter is not `pj`, every tree input is in
`PrivJ pj` and the two routings agree, and when it is `pj`, the key is bad. So the two generations
agree on good keys (`agreeOn_xKeygenS`, `agreeOn_sKeygenS`).
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

namespace PerKeyS

open PerKeyX (xPrefix' xTree xTree_eq keyOfTree keyOfTree_param route_keygen_x' sPrefix' sTree
  sTree_eq keyOfTreeS keyOfTreeS_param route_keygen_s length_bytesLE16_x length_bytesLE16_s)

variable [Sphincs.Params]

/-- **The reduction's leanXMSS key generation**, under the game's oracles. -/
theorem ΦJS_xKeygenRS (sk : Sphincs.Seeded.SecretKey) (pj : Bytes) :
    ΦJS sk (xKeygenRS pj) = xPrefix' pj >>= xTree (fun _ ↦ True) := by
  unfold xKeygenRS xPrefix'
  simp only [ΦJS_bind, ΦJS_pure, rcS, rpS, ΦJS_rImpl, bind_assoc, pure_bind]
  refine bind_congr fun seed ↦ bind_congr fun S ↦ bind_congr fun o ↦ ?_
  rw [xTree_eq]
  rfl

/-- **The reduction's leanSPHINCS key generation**, under the game's oracles. -/
theorem ΦJS_sKeygenRS (sk : Sphincs.Seeded.SecretKey) (pj : Bytes) :
    ΦJS sk (sKeygenRS pj) = sPrefix' pj >>= sTree (fun _ ↦ True) := by
  unfold sKeygenRS sPrefix'
  simp only [ΦJS_bind, ΦJS_pure, rcS, rpS, ΦJS_rImpl, bind_assoc, pure_bind]
  refine bind_congr fun seed ↦ bind_congr fun S ↦ bind_congr fun o ↦ ?_
  rw [sTree_eq]
  rfl

/-- **The two leanXMSS key generations agree on keys whose parameter is not `pj`.** -/
theorem agreeOn_xKeygenS (sk : Sphincs.Seeded.SecretKey) (pj : Bytes) (hpj : pj.length = 16) :
    AgreeOn (fun k : LeanXmss.PublicKey × LeanXmss.Seeded.SecretKey ↦
        LeanXmss.bytesLE 16 k.2.parameter ≠ pj)
      (simulateQ (routeImpl (PrivJ pj)) (LeanXmss.MultiUser.keygen : OracleComp OW _))
      (ΦJS sk (xKeygenRS pj)) := by
  rw [route_keygen_x', ΦJS_xKeygenRS]
  refine agreeOn_bind _ _ _ (fun m ↦ LeanXmss.bytesLE 16 (LeanXmss.truncateHash m.2) ≠ pj) _
    (fun m hm ↦ ?_) (fun m hm cp ↦ ?_)
  · rw [xTree_eq, xTree_eq]
    unfold keyOfTree
    rw [simulateQ_routeImpl_congr (PrivJ pj) (fun _ ↦ True)]
    refine (allQueriesSatisfy_liftM_hash (walkX_treeNode _ _ _ _ _)).mono fun t ht x hx ↦ ?_
    exact ⟨fun _ ↦ trivial, fun _ ↦ privJ_of_schemeInputN (length_bytesLE16_x _) hpj hm (ht x hx)⟩
  · have key : ∀ (Pr : List UInt8 → Prop) [DecidablePred Pr],
        ∀ z ∈ support ((xTree Pr m).run cp),
          ¬ LeanXmss.bytesLE 16 z.1.2.parameter ≠ pj := by
      intro Pr _ z hz
      unfold xTree at hz
      have hp := keyOfTree_param Pr _ m.1 (LeanXmss.truncateHash m.2) cp z hz
      rw [hp]
      exact hm
    exact ⟨key _, key _⟩

/-- **The two leanSPHINCS key generations agree on keys whose parameter is not `pj`.** -/
theorem agreeOn_sKeygenS (sk : Sphincs.Seeded.SecretKey) (pj : Bytes) (hpj : pj.length = 16) :
    AgreeOn (fun k : Sphincs.PublicKey × Sphincs.Seeded.SecretKey ↦
        Sphincs.bytesLE 16 k.2.parameter ≠ pj)
      (simulateQ (routeImpl (PrivJ pj)) (sKeygen : OracleComp OW _))
      (ΦJS sk (sKeygenRS pj)) := by
  rw [route_keygen_s, ΦJS_sKeygenRS]
  refine agreeOn_bind _ _ _ (fun m ↦ Sphincs.bytesLE 16 (Sphincs.truncateHash m.2) ≠ pj) _
    (fun m hm ↦ ?_) (fun m hm cp ↦ ?_)
  · rw [sTree_eq, sTree_eq]
    unfold keyOfTreeS
    rw [simulateQ_routeImpl_congr (PrivJ pj) (fun _ ↦ True)]
    refine (allQueriesSatisfy_sLift (walkS_spineNode _ _ _ _ _)).mono fun t ht x hx ↦ ?_
    exact ⟨fun _ ↦ trivial, fun _ ↦ privJ_of_schemeInputN (length_bytesLE16_s _) hpj hm (ht x hx)⟩
  · have key : ∀ (Pr : List UInt8 → Prop) [DecidablePred Pr],
        ∀ z ∈ support ((sTree Pr m).run cp),
          ¬ Sphincs.bytesLE 16 z.1.2.parameter ≠ pj := by
      intro Pr _ z hz
      unfold sTree at hz
      have hp := keyOfTreeS_param Pr _ m.1 (Sphincs.truncateHash m.2) cp z hz
      rw [hp]
      exact hm
    exact ⟨key _, key _⟩

end PerKeyS

end
end LeanVM.E2E
