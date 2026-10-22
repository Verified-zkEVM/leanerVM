/-
  LeanVM.E2E.Vis.PerKey.XmssKeygen

  W-vis, P7b: the other keys' generation, routed by class in the game and partly privately in the
  per-key leanXMSS reduction, agree on keys whose parameter is not key `j`'s.
-/

module

public import LeanVM.E2E.Vis.PerKey.XmssRest
public import LeanVM.E2E.Vis.PerKey.Agree

/-!
# The other keys' generation (W-vis, P7b)

A key generation is two derivations, then a tree under the derived parameter
(`xmss_keygenFromSeed_eq`, `sphincs_keygenFromSeed_eq`). The class-routed game routes the tree
by class, the reduction privately. Every tree input is a scheme input of the derived parameter
(`walkX_treeNode`, `walkS_spineNode`); when that parameter is not `pj`, it is in `PrivJ pj`, and
the two routings agree. When it is `pj`, the key is bad. So the two generations agree on good keys
(`agreeOn_xKeygen`, `agreeOn_sKeygen`).
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

namespace PerKeyX

variable {nx ns : ℕ}

/-- The class-routed game's leanXMSS key generation, its tree split off. -/
theorem route_keygen_x (pj : Bytes) :
    simulateQ (routeImpl (PrivJ pj)) (LeanXmss.MultiUser.keygen : OracleComp OW _) =
      (do
        let seed ← simulateQ (routeImpl (PrivJ pj)) (liftM LeanXmss.sampleMasterSeed : OracleComp OW _)
        let S ← simulateQ (routeImpl (PrivJ pj)) (liftM (liftM (LeanXmss.HashSpec.query
          (LeanXmss.seedHashInput seed)) : OracleComp LeanXmss.HashSpec _) : OracleComp OW _)
        let o ← simulateQ (routeImpl (PrivJ pj)) (liftM (liftM (LeanXmss.HashSpec.query
          (LeanXmss.keygenHashInput 0 .parameter S)) : OracleComp LeanXmss.HashSpec _) :
            OracleComp OW _)
        pure (S, o) : PM _) >>= fun m ↦ (do
          let root ← simulateQ (routeImpl (PrivJ pj)) (liftM (LeanXmss.Seeded.treeNode
            (LeanXmss.truncateHash m.2) LeanXmss.topLayer m.1 LeanXmss.layerHeight 0 :
              OracleComp LeanXmss.HashSpec _) : OracleComp OW _)
          pure ((⟨root, LeanXmss.truncateHash m.2⟩ : LeanXmss.PublicKey),
            (⟨m.1, LeanXmss.truncateHash m.2, root⟩ : LeanXmss.Seeded.SecretKey)) : PM _) := by
  unfold LeanXmss.MultiUser.keygen
  simp only [xmss_keygenFromSeed_eq, liftM_bind, simulateQ_bind, bind_assoc, pure_bind,
    simulateQ_pure, liftM_pure]

/-- The common prefix of the leanXMSS key generations: the seed and the two derivations, routed
by class. -/
noncomputable def xPrefix' (pj : Bytes) : PM (LeanXmss.MasterSeed × LeanXmss.HashOutput) := do
  let seed ← simulateQ (routeImpl (PrivJ pj)) (liftM LeanXmss.sampleMasterSeed : OracleComp OW _)
  let S ← simulateQ (routeImpl (PrivJ pj)) (liftM (liftM (LeanXmss.HashSpec.query
    (LeanXmss.seedHashInput seed)) : OracleComp LeanXmss.HashSpec _) : OracleComp OW _)
  let o ← simulateQ (routeImpl (PrivJ pj)) (liftM (liftM (LeanXmss.HashSpec.query
    (LeanXmss.keygenHashInput 0 .parameter S)) : OracleComp LeanXmss.HashSpec _) :
      OracleComp OW _)
  pure (S, o)

/-- A key from its tree's computation, under a routing. -/
noncomputable def keyOfTree (Pr : List UInt8 → Prop) [DecidablePred Pr] (tree : OracleComp OW LeanXmss.Digest)
    (S : LeanXmss.MasterSeed) (P : LeanXmss.PublicParameter) :
    PM (LeanXmss.PublicKey × LeanXmss.Seeded.SecretKey) := do
  let root ← simulateQ (routeImpl Pr) tree
  pure (⟨root, P⟩, ⟨S, P, root⟩)

/-- A leanXMSS key's tree, in the schemes' world. Irreducible: its recursion is never unfolded
by the elaborator (`xTreeC_eq` gives it). -/
@[irreducible] noncomputable def xTreeC (P : LeanXmss.PublicParameter) (S : LeanXmss.MasterSeed) :
    OracleComp OW LeanXmss.Digest :=
  liftM (LeanXmss.Seeded.treeNode P LeanXmss.topLayer S LeanXmss.layerHeight 0 :
    OracleComp LeanXmss.HashSpec _)

theorem xTreeC_eq (P : LeanXmss.PublicParameter) (S : LeanXmss.MasterSeed) :
    xTreeC P S = liftM (LeanXmss.Seeded.treeNode P LeanXmss.topLayer S LeanXmss.layerHeight 0 :
      OracleComp LeanXmss.HashSpec _) := by
  unfold xTreeC; rfl

/-- A leanXMSS key generation's tree, under a routing. -/
noncomputable def xTree (Pr : List UInt8 → Prop) [DecidablePred Pr]
    (m : LeanXmss.MasterSeed × LeanXmss.HashOutput) :
    PM (LeanXmss.PublicKey × LeanXmss.Seeded.SecretKey) :=
  keyOfTree Pr (xTreeC (LeanXmss.truncateHash m.2) m.1) m.1 (LeanXmss.truncateHash m.2)

theorem xTree_eq (Pr : List UInt8 → Prop) [DecidablePred Pr]
    (m : LeanXmss.MasterSeed × LeanXmss.HashOutput) :
    xTree Pr m = keyOfTree Pr (liftM (LeanXmss.Seeded.treeNode (LeanXmss.truncateHash m.2)
      LeanXmss.topLayer m.1 LeanXmss.layerHeight 0 : OracleComp LeanXmss.HashSpec _)) m.1
        (LeanXmss.truncateHash m.2) := by
  unfold xTree xTreeC; rfl

/-- A key from a tree has the given parameter. -/
theorem keyOfTree_param (Pr : List UInt8 → Prop) [DecidablePred Pr]
    (tree : OracleComp OW LeanXmss.Digest) (S : LeanXmss.MasterSeed)
    (P : LeanXmss.PublicParameter) (cp : QueryCache LeanXmss.HashSpec)
    (z : (LeanXmss.PublicKey × LeanXmss.Seeded.SecretKey) × QueryCache LeanXmss.HashSpec)
    (hz : z ∈ support ((keyOfTree Pr tree S P).run cp)) : z.1.2.parameter = P := by
  unfold keyOfTree at hz
  rw [StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨r, -, hz⟩ := hz
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  rw [hz]

/-- The class-routed game's leanXMSS key generation. -/
theorem route_keygen_x' (pj : Bytes) :
    simulateQ (routeImpl (PrivJ pj)) (LeanXmss.MultiUser.keygen : OracleComp OW _) =
      xPrefix' pj >>= xTree (PrivJ pj) := by
  rw [route_keygen_x pj]
  unfold xPrefix'
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun seed ↦ bind_congr fun S ↦ bind_congr fun o ↦ ?_
  rw [xTree_eq]
  rfl

/-- **The reduction's leanXMSS key generation**, under the game's oracles. -/
theorem ΦJ_xKeygenR (sk : LeanXmss.Seeded.SecretKey) (pj : Bytes) :
    ΦJ sk (xKeygenR pj) = xPrefix' pj >>= xTree (fun _ ↦ True) := by
  unfold xKeygenR xPrefix'
  simp only [ΦJ_bind, ΦJ_pure, rc, rp, ΦJ_rImpl, bind_assoc, pure_bind]
  refine bind_congr fun seed ↦ bind_congr fun S ↦ bind_congr fun o ↦ ?_
  rw [xTree_eq]
  rfl


/-- **The two leanXMSS key generations agree on keys whose parameter is not `pj`.** -/
theorem agreeOn_xKeygen (sk : LeanXmss.Seeded.SecretKey) (pj : Bytes) (hpj : pj.length = 16) :
    AgreeOn (fun k : LeanXmss.PublicKey × LeanXmss.Seeded.SecretKey ↦
        LeanXmss.bytesLE 16 k.2.parameter ≠ pj)
      (simulateQ (routeImpl (PrivJ pj)) (LeanXmss.MultiUser.keygen : OracleComp OW _))
      (ΦJ sk (xKeygenR pj)) := by
  rw [route_keygen_x', ΦJ_xKeygenR]
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

/-! ## leanSPHINCS keys -/

/-- A key from its tree's computation, under a routing (leanSPHINCS). -/
noncomputable def keyOfTreeS (Pr : List UInt8 → Prop) [DecidablePred Pr]
    (tree : OracleComp OW Sphincs.Digest) (S : Sphincs.MasterSeed) (P : Sphincs.PublicParameter) :
    PM (Sphincs.PublicKey × Sphincs.Seeded.SecretKey) := do
  let root ← simulateQ (routeImpl Pr) tree
  pure (⟨root, P⟩, ⟨S, P, root⟩)

/-- A key from a tree has the given parameter (leanSPHINCS). -/
theorem keyOfTreeS_param (Pr : List UInt8 → Prop) [DecidablePred Pr]
    (tree : OracleComp OW Sphincs.Digest) (S : Sphincs.MasterSeed)
    (P : Sphincs.PublicParameter) (cp : QueryCache LeanXmss.HashSpec)
    (z : (Sphincs.PublicKey × Sphincs.Seeded.SecretKey) × QueryCache LeanXmss.HashSpec)
    (hz : z ∈ support ((keyOfTreeS Pr tree S P).run cp)) : z.1.2.parameter = P := by
  unfold keyOfTreeS at hz
  rw [StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨r, -, hz⟩ := hz
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  rw [hz]

/-- A leanSPHINCS key's tree, in the schemes' world (irreducible, `sTreeC` unfolded by `sTree_eq`). -/
@[irreducible] noncomputable def sTreeC [Sphincs.Params] (P : Sphincs.Digest)
    (S : Sphincs.MasterSeed) : OracleComp OW Sphincs.Digest :=
  sLift (Sphincs.Seeded.spineNode P Sphincs.topLayer Sphincs.Concrete.rootTree S
    (Sphincs.totalHeight - Sphincs.subtreeHeight) : OracleComp Sphincs.HashSpec _)

variable [Sphincs.Params]

/-- A leanSPHINCS key generation's tree, under a routing. -/
noncomputable def sTree (Pr : List UInt8 → Prop) [DecidablePred Pr]
    (m : Sphincs.MasterSeed × Sphincs.HashOutput) :
    PM (Sphincs.PublicKey × Sphincs.Seeded.SecretKey) :=
  keyOfTreeS Pr (sTreeC (Sphincs.truncateHash m.2) m.1) m.1 (Sphincs.truncateHash m.2)

theorem sTree_eq (Pr : List UInt8 → Prop) [DecidablePred Pr]
    (m : Sphincs.MasterSeed × Sphincs.HashOutput) :
    sTree Pr m = keyOfTreeS Pr (sLift (Sphincs.Seeded.spineNode (Sphincs.truncateHash m.2)
      Sphincs.topLayer Sphincs.Concrete.rootTree m.1 (Sphincs.totalHeight - Sphincs.subtreeHeight) :
        OracleComp Sphincs.HashSpec _)) m.1 (Sphincs.truncateHash m.2) := by
  unfold sTree sTreeC; rfl

/-- The common prefix of the leanSPHINCS key generations, routed by class. -/
noncomputable def sPrefix' (pj : Bytes) : PM (Sphincs.MasterSeed × Sphincs.HashOutput) := do
  let seed ← simulateQ (routeImpl (PrivJ pj)) (liftM Sphincs.sampleMasterSeed : OracleComp OW _)
  let S ← simulateQ (routeImpl (PrivJ pj)) (sLift (liftM (Sphincs.HashSpec.query
    (Sphincs.schemeSeedInput seed)) : OracleComp Sphincs.HashSpec _))
  let o ← simulateQ (routeImpl (PrivJ pj)) (sLift (liftM (Sphincs.HashSpec.query
    (Sphincs.keygenHashInput 0 .parameter S)) : OracleComp Sphincs.HashSpec _))
  pure (S, o)

omit [Sphincs.Params] in
theorem sLift_bind {α β : Type} (oa : OracleComp Sphincs.HashSpec α)
    (f : α → OracleComp Sphincs.HashSpec β) : sLift (oa >>= f) = sLift oa >>= fun a ↦ sLift (f a) := by
  unfold sLift; rw [liftM_bind]; rfl

omit [Sphincs.Params] in
theorem sLift_pure {α : Type} (a : α) : sLift (pure a : OracleComp Sphincs.HashSpec α) = pure a := by
  unfold sLift; rw [liftM_pure]; rfl

/-- The class-routed game's leanSPHINCS key generation. -/
theorem route_keygen_s (pj : Bytes) :
    simulateQ (routeImpl (PrivJ pj)) (sKeygen : OracleComp OW _) =
      sPrefix' pj >>= sTree (PrivJ pj) := by
  unfold sKeygen sPrefix'
  simp only [sphincs_keygenFromSeed_eq, sLift_bind, sLift_pure, simulateQ_bind, bind_assoc,
    pure_bind, simulateQ_pure]
  refine bind_congr fun seed ↦ bind_congr fun S ↦ bind_congr fun o ↦ ?_
  rw [sTree_eq]
  rfl

/-- **The reduction's leanSPHINCS key generation**, under the game's oracles. -/
theorem ΦJ_sKeygenR (sk : LeanXmss.Seeded.SecretKey) (pj : Bytes) :
    ΦJ sk (sKeygenR pj) = sPrefix' pj >>= sTree (fun _ ↦ True) := by
  unfold sKeygenR sPrefix'
  simp only [ΦJ_bind, ΦJ_pure, rc, rp, ΦJ_rImpl, bind_assoc, pure_bind]
  refine bind_congr fun seed ↦ bind_congr fun S ↦ bind_congr fun o ↦ ?_
  rw [sTree_eq]
  rfl

/-- **The two leanSPHINCS key generations agree on keys whose parameter is not `pj`.** -/
theorem agreeOn_sKeygen (sk : LeanXmss.Seeded.SecretKey) (pj : Bytes) (hpj : pj.length = 16) :
    AgreeOn (fun k : Sphincs.PublicKey × Sphincs.Seeded.SecretKey ↦
        Sphincs.bytesLE 16 k.2.parameter ≠ pj)
      (simulateQ (routeImpl (PrivJ pj)) (sKeygen : OracleComp OW _))
      (ΦJ sk (sKeygenR pj)) := by
  rw [route_keygen_s, ΦJ_sKeygenR]
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

end PerKeyX

end
end LeanVM.E2E
