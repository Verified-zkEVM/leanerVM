/-
  LeanVM.E2E.Vis.PerKey.SphincsRest

  W-vis, P7b: after the keys, the per-key leanSPHINCS reduction's run under the single-key game's
  oracles is the class-routed game, when no other key's parameter is key `j`'s.
-/

module

public import LeanVM.E2E.Vis.PerKey.SphincsRun
public import LeanVM.E2E.Vis.PerKey.XmssRest

/-!
# The reduction's rest is the class-routed game (W-vis, P7b, leanSPHINCS)

The leanSPHINCS counterpart of `Vis/PerKey/XmssRest.lean`. For keys whose other parameters are not
key `j`'s (`GoodJS`):

* every input of another key's signer is in the private class (`privJ_of_schemeInputN`), so the
  reduction's private signing is the class-routed signing;
* every input of key `j`'s signer is outside it (`not_privJ_of_schemeInput`), so the class-routed
  signing of key `j` is its signer (`route_sLift_sign_jS`), which is what the single-key game's
  signing oracle runs.

Hence the reduction's answers to the adversary, under the game's oracles, are the class-routed
game's (`stMap_ΦJS_advImplJS`), and so is the reduction's whole run after the keys
(`map_ΦJS_restJS`), the keys in its outcome holding key `j`'s place by `holeKeyS`.
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

namespace PerKeyS

open PerKeyX (PM gAdv run_gAdv withKeys length_bytesLE16_s advImpl_inl_inl advImpl_xmss
  advImpl_sphincs route_tw_xmssSign_priv route_tw_sphincsSign_priv)

variable {nx ns : ℕ} [Sphincs.Params]

/-- **Good keys for reduction `j`**: no other key's parameter is `pj`. -/
def GoodJS (pj : Bytes) (j : Fin ns) (keys : Keys nx ns) : Prop :=
  (∀ i, LeanXmss.bytesLE 16 (keys.xmss i).2.parameter ≠ pj) ∧
    ∀ i, i ≠ j → Sphincs.bytesLE 16 (keys.sphincs i).2.parameter ≠ pj

/-- Key `j`'s forwarded request, run. -/
theorem run_sphincsFwdJ (j : Fin ns) (msg : Sphincs.Message) (st : SignState nx ns) :
    (sphincsFwdJ j msg).run st =
      if Sphincs.signatureLimit ≤ (st.slog j).length then pure (none, st)
      else (fun σ ↦ (σ, { st with slog := Function.update st.slog j (st.slog j ++ [(msg, σ)]) })) <$>
        (liftM (liftM (RSs.query (.inr msg)) : OracleComp RSs (Option Sphincs.Signature)) :
          RMs (Option Sphincs.Signature)) := by
  by_cases h : Sphincs.signatureLimit ≤ (st.slog j).length
  · simp [sphincsFwdJ, h]
  · simp only [sphincsFwdJ, h, ↓reduceIte, StateT.run_bind, StateT.run_get,
      pure_bind, OracleComp.liftM_run_StateT, bind_assoc, StateT.run_modify, StateT.run_pure,
      map_eq_bind_pure_comp]
    rfl

/-- **Key `j`'s signer is forwarded** by the class-routed game: its inputs are `pj`'s. -/
theorem route_sLift_sign_jS (sk : Sphincs.Seeded.SecretKey) (m : Sphincs.Message) :
    simulateQ (routeImpl (PrivJ (Sphincs.bytesLE 16 sk.parameter)))
        (sLift (Sphincs.Seeded.sign sk m : OracleComp Sphincs.HashSpec _)) =
      liftM (sLift (Sphincs.Seeded.sign sk m : OracleComp Sphincs.HashSpec _)) := by
  refine simulateQ_routeImpl_of_off _ ?_
  refine (allQueriesSatisfy_sLift ((queriesSat_iff _ _).mp
    (sphincs_sign_queries sk m))).mono fun t ht x hx ↦ not_privJ_of_schemeInput (ht x hx)

theorem advImplJS_inl_inl (pj : Bytes) (j : Fin ns) (keys : Keys nx ns)
    (t : (unifSpec + HashSpec).Domain) :
    advImplJS pj j keys (.inl (.inl t)) =
      StateT.mk fun st ↦ rcS pj (tw (advImpl keys (.inl (.inl t))) st) := rfl

theorem advImplJS_xmss (pj : Bytes) (j : Fin ns) (keys : Keys nx ns) (i : Fin nx)
    (req : XmssRequest) :
    advImplJS pj j keys (.inl (.inr (i, req))) =
      StateT.mk fun st ↦ rpS (tw (xmssSign keys i req) st) :=
  rfl

theorem advImplJS_sphincs_self (pj : Bytes) (j : Fin ns) (keys : Keys nx ns)
    (msg : Sphincs.Message) :
    advImplJS pj j keys (.inr (j, msg)) = sphincsFwdJ j msg := by
  simp [advImplJS]

theorem advImplJS_sphincs_ne (pj : Bytes) (j : Fin ns) (keys : Keys nx ns) {i : Fin ns}
    (hij : i ≠ j) (msg : Sphincs.Message) :
    advImplJS pj j keys (.inr (i, msg)) =
      StateT.mk fun st ↦ rpS (tw (sphincsSign keys i msg) st) := by
  simp [advImplJS, hij, advImpl_sphincs]

/-- **The reduction's answers, under the game's oracles, are the class-routed game's**, for good
keys: the reduction's keys `keysR` are the game's `keysG` but for key `j`'s secret key, which the
game's signing oracle holds. -/
theorem stMap_ΦJS_advImplJS (sk : Sphincs.Seeded.SecretKey) (j : Fin ns) (keysR keysG : Keys nx ns)
    (hs : ∀ i, i ≠ j → keysR.sphincs i = keysG.sphincs i) (hx : keysR.xmss = keysG.xmss)
    (hj : (keysG.sphincs j).2 = sk) (hgood : GoodJS (Sphincs.bytesLE 16 sk.parameter) j keysG)
    (t : (AdvSpec nx ns).Domain) :
    stMap (fun {β : Type} (y : RMs β) ↦ ΦJS sk y)
        (advImplJS (Sphincs.bytesLE 16 sk.parameter) j keysR t) =
      gAdv (Sphincs.bytesLE 16 sk.parameter) keysG t := by
  have hpj : (Sphincs.bytesLE 16 sk.parameter).length = 16 := length_bytesLE16_s _
  refine StateT.ext fun st ↦ ?_
  rw [run_stMap, run_gAdv]
  rcases t with (t | ⟨i, req⟩) | ⟨i, msg⟩
  · rw [advImplJS_inl_inl, StateT.run_mk, ΦJS_rcS, advImpl_inl_inl keysR keysG]
  · rw [advImpl_xmss, advImplJS_xmss, StateT.run_mk, ΦJS_rpS]
    have hkey : xmssSign keysR i req = xmssSign keysG i req := by
      unfold xmssSign; rw [hx]
    rw [hkey]
    exact route_tw_xmssSign_priv _ hpj keysG i (hgood.1 i) req st
  · rw [advImpl_sphincs]
    by_cases hij : i = j
    · subst hij
      rw [advImplJS_sphincs_self, run_sphincsFwdJ, tw_sphincsSign_eq, hj]
      split
      · rw [ΦJS_pure, simulateQ_pure]
      · rw [ΦJS_map, simulateQ_map, ΦJS_signQuery, route_sLift_sign_jS]
    · rw [advImplJS_sphincs_ne _ _ _ hij, StateT.run_mk, ΦJS_rpS]
      have hkey : sphincsSign keysR i msg = sphincsSign keysG i msg := by
        unfold sphincsSign; rw [hs i hij]
      rw [hkey]
      exact route_tw_sphincsSign_priv _ hpj keysG i (hgood.2 i hij) msg st

/-- **The reduction's adversary phase, under the game's oracles, is the class-routed game's.** -/
theorem ΦJS_adv (sk : Sphincs.Seeded.SecretKey) (j : Fin ns) (keysR keysG : Keys nx ns)
    (hs : ∀ i, i ≠ j → keysR.sphincs i = keysG.sphincs i) (hx : keysR.xmss = keysG.xmss)
    (hj : (keysG.sphincs j).2 = sk) (hgood : GoodJS (Sphincs.bytesLE 16 sk.parameter) j keysG)
    {α : Type} (oa : OracleComp (AdvSpec nx ns) α) (st : SignState nx ns) :
    ΦJS sk ((simulateQ (advImplJS (Sphincs.bytesLE 16 sk.parameter) j keysR) oa).run st) =
      simulateQ (routeImpl (PrivJ (Sphincs.bytesLE 16 sk.parameter)))
        (tw (simulateQ (advImpl keysG) oa) st) := by
  have h1 := simulateQ_morph (isMorphism_stMap (σ := SignState nx ns) (isMorphism_ΦJS sk))
    (advImplJS (Sphincs.bytesLE 16 sk.parameter) j keysR) oa
  have h2 := congrArg (fun x ↦ StateT.run x st) h1
  simp only [run_stMap] at h2
  rw [← h2, route_tw_simulateQ]
  have hh : (fun t ↦ stMap (fun {β : Type} (y : RMs β) ↦ ΦJS sk y)
      (advImplJS (Sphincs.bytesLE 16 sk.parameter) j keysR t)) =
      gAdv (Sphincs.bytesLE 16 sk.parameter) keysG :=
    funext fun t ↦ stMap_ΦJS_advImplJS sk j keysR keysG hs hx hj hgood t
  rw [hh]
  rfl

/-- **The reduction's run after the keys, under the game's oracles, is the class-routed game's
rest**, its outcome's keys the reduction's. -/
theorem map_ΦJS_restJS (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns)
    (sk : Sphincs.Seeded.SecretKey) (j : Fin ns) (keysR keysG : Keys nx ns)
    (hs : ∀ i, i ≠ j → keysR.sphincs i = keysG.sphincs i) (hx : keysR.xmss = keysG.xmss)
    (hj : (keysG.sphincs j).2 = sk) (hpk : (keysR.sphincs j).1 = (keysG.sphincs j).1)
    (hgood : GoodJS (Sphincs.bytesLE 16 sk.parameter) j keysG) :
    outJS <$> ΦJS sk (restJS guest fuel budget A (Sphincs.bytesLE 16 sk.parameter) j keysR) =
      (fun z ↦ (withKeys keysR z.1, z.2)) <$>
        simulateQ (routeImpl (PrivJ (Sphincs.bytesLE 16 sk.parameter)))
          (gameRest guest fuel budget A keysG) := by
  have hpub : (fun i ↦ (keysR.sphincs i).1) = fun i ↦ (keysG.sphincs i).1 := by
    funext i
    by_cases hij : i = j
    · subst hij; exact hpk
    · rw [hs i hij]
  unfold restJS gameRest
  rw [ΦJS_bind, ΦJS_adv sk j keysR keysG hs hx hj hgood, hpub, hx]
  simp only [simulateQ_bind, map_bind]
  refine bind_congr fun q ↦ ?_
  rw [ΦJS_bind, rcS, ΦJS_rImpl, map_bind]
  refine bind_congr fun q' ↦ ?_
  rw [ΦJS_pure, simulateQ_pure, map_pure, map_pure]
  rfl

end PerKeyS

end
end LeanVM.E2E
