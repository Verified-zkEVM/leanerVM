/-
  LeanVM.E2E.Reduction.GameW

  The game with V_I's trace, translated to the schemes' world: the leanXMSS keys, the leanSPHINCS
  keys, then the rest of the game at those keys.
-/

module

public import LeanVM.E2E.Reduction.Seeds

/-!
# The game in the schemes' world

`toW_gameCompRec`: the translation of `gameCompRec` is the sequence of the leanXMSS key
generations (`LeanXmss.MultiUser.keygen`, the schemes' own), the sequence of the leanSPHINCS key
generations (`sKeygen`), then the rest of the game at those keys (`gameRest`: the adversary with
the game's oracles, then V_I recorded), each translated. Both reductions of T5 run the parts they
do not delegate exactly so.
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

variable {nx ns : ℕ}

/-- The game's leanXMSS key generation, translated. -/
theorem tw_xKeygen (st : SignState nx ns) :
    tw ((Vector.replicate nx ()).mapM fun _ ↦ do
        xmssRun (LeanXmss.Seeded.keygenFromSeed (← coins LeanXmss.sampleMasterSeed)) :
        GameM nx ns _) st =
      (fun f ↦ (Vector.ofFn f, st)) <$>
        LeanXmss.Concrete.sequenceFin fun _ : Fin nx ↦ LeanXmss.MultiUser.keygen := by
  rw [vector_mapM_replicate, tw_map, tw_sequenceFin st _ (fun _ ↦ LeanXmss.MultiUser.keygen)]
  · rw [Functor.map_map]; rfl
  · intro i
    rw [tw_bind, tw_coins, bind_map_left]
    simp only [tw_xmssRun, LeanXmss.MultiUser.keygen, map_bind]

/-- The game's leanSPHINCS key generation, translated. -/
theorem tw_sKeygen [Sphincs.Params] (st : SignState nx ns) :
    tw ((Vector.replicate ns ()).mapM fun _ ↦ do
        sphincsRun (Sphincs.Seeded.keygenFromSeed (← coins Sphincs.sampleMasterSeed)) :
        GameM nx ns _) st =
      (fun f ↦ (Vector.ofFn f, st)) <$> LeanXmss.Concrete.sequenceFin fun _ : Fin ns ↦ sKeygen := by
  rw [vector_mapM_replicate, tw_map, tw_sequenceFin st _ (fun _ ↦ sKeygen)]
  · rw [Functor.map_map]; rfl
  · intro i
    rw [tw_bind, tw_coins, bind_map_left]
    simp only [tw_sphincsRun, sKeygen, map_bind]

/-- **The rest of the game at the keys `keys`**, translated: the adversary with the game's
oracles, then V_I recorded; the outcome and V_I's trace. -/
noncomputable def gameRest [Sphincs.Params] (guest : Program) (fuel budget : ℕ)
    (A : GameAdversary nx ns) (keys : Keys nx ns) : OracleComp OW (GameOutcome nx ns × Log) :=
  tw (simulateQ (advImpl keys) (A (fun j ↦ (keys.xmss j).1) (fun j ↦ (keys.sphincs j).1)))
      (SignState.init nx ns) >>= fun q ↦
    tw (viRec budget guest q.1.2 fuel q.1.1) q.2 >>= fun q' ↦
      pure (⟨keys, q.1.1, q.1.2, (q'.1.map Prod.fst).getD false, q'.2⟩, (q'.1.map Prod.snd).getD [])

/-- **The game with V_I's trace, translated**: the leanXMSS keys, the leanSPHINCS keys, then the
rest of the game. -/
theorem toW_gameCompRec [Sphincs.Params] (guest : Program) (fuel budget : ℕ)
    (A : GameAdversary nx ns) :
    simulateQ toW (gameCompRec guest fuel budget A) =
      LeanXmss.Concrete.sequenceFin (fun _ : Fin nx ↦ LeanXmss.MultiUser.keygen) >>= fun mk ↦
        LeanXmss.Concrete.sequenceFin (fun _ : Fin ns ↦ sKeygen) >>= fun ss ↦
          gameRest guest fuel budget A ⟨mk, ss⟩ := by
  unfold gameCompRec gameRest
  rw [simulateQ_bind]
  change tw _ (SignState.init nx ns) >>= _ = _
  unfold keygen
  simp only [tw_bind, tw_xKeygen, tw_sKeygen, bind_map_left, bind_assoc, tw_pure, pure_bind,
    simulateQ_pure, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]

end
end LeanVM.E2E
