/-
  LeanVM.E2E.Vis.PerKey.SphincsRun

  W-vis, P7b: the per-key leanSPHINCS reduction's run under the single-key game's oracles, as a
  computation of the schemes' world with the private cache.
-/

module

public import LeanVM.E2E.Vis.PerKey.Sphincs
public import LeanVM.E2E.Vis.PerKey.XmssRun

/-!
# The reduction's run, in the schemes' world (W-vis, P7b, leanSPHINCS)

The leanSPHINCS counterpart of `Vis/PerKey/XmssRun.lean`. The single-key game
(`Sphincs.Security.Det.gameCoreDet`) answers the reduction's world `OW + SigningSpec` by passing
the schemes' world through and signing with key `j`'s secret key `sk` (`signingOracleDet sk`;
`σJS sk`, the log forgotten). Under it, the reduction's monad maps to `PerKeyX.PM`, computations
with the private cache over the schemes' world (`ΦJS sk`, a monad morphism):

* class-routed computations to the routed oracle `routeImpl (PrivJ pj)` (`ΦJS_rcS`);
* private computations to `routeImpl (fun _ ↦ True)` (`ΦJS_rpS`);
* key `j`'s signing request to its signer (`ΦJS_signQuery`).
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

namespace PerKeyS

open PerKeyX (PM)

variable [Sphincs.Params]

/-- **The single-key game's oracles, the log forgotten**: the schemes' world passed through, a
signing request signed with `sk`. -/
noncomputable def σJS (sk : Sphincs.Seeded.SecretKey) : QueryImpl RSs (OracleComp OW) :=
  QueryImpl.ofLift OW (OracleComp OW) +
    (fun msg : Sphincs.Message ↦ sLift (Sphincs.Seeded.sign sk msg :
      OracleComp Sphincs.HashSpec (Option Sphincs.Signature)) :
      QueryImpl Sphincs.SigningSpec (OracleComp OW))

/-- The game's signing oracle, the log forgotten, is `σJS`'s signer. -/
theorem fst_signingOracleDet (sk : Sphincs.Seeded.SecretKey) (msg : Sphincs.Message) :
    (Prod.fst <$> (Sphincs.Security.Det.signingOracleDet sk msg).run : OracleComp OW _) =
      σJS sk (.inr msg) := by
  have h : Prod.fst <$> (Sphincs.Security.Det.signingOracleDet sk msg).run =
      (liftM (Sphincs.Seeded.sign sk msg : OracleComp Sphincs.HashSpec _) :
        OracleComp Sphincs.OracleWorld _) := by
    rw [Sphincs.Security.Det.signingOracleDet, QueryImpl.run_withLogging_apply]
    simp
  exact h

/-- The schemes' world lifted and answered by the game's oracles is itself. -/
theorem simulateQ_σJS_liftSig (sk : Sphincs.Seeded.SecretKey) {α : Type} (oa : OracleComp OW α) :
    simulateQ (σJS sk) (liftSig Sphincs.SigningSpec oa) = oa := by
  unfold liftSig
  rw [← QueryImpl.simulateQ_compose]
  conv_rhs => rw [← simulateQ_ofLift_eq_self oa]
  congr 1

/-- **The reduction's monad, under the game's oracles.** -/
noncomputable def ΦJS (sk : Sphincs.Seeded.SecretKey) {α : Type} (x : RMs α) : PM α :=
  stMap (fun {β : Type} (y : OracleComp RSs β) ↦ simulateQ (σJS sk) y) x

/-- `ΦJS` is a monad morphism. -/
theorem isMorphism_ΦJS (sk : Sphincs.Seeded.SecretKey) :
    IsMorphism (fun {α : Type} (x : RMs α) ↦ ΦJS sk x) :=
  isMorphism_stMap (isMorphism_simulateQ (σJS sk))

/-- A routed computation, under the game's oracles, is the routed run. -/
theorem ΦJS_rImpl (sk : Sphincs.Seeded.SecretKey) (Pr : List UInt8 → Prop) [DecidablePred Pr]
    {α : Type} (oa : OracleComp OW α) :
    ΦJS sk (simulateQ (rImpl Sphincs.SigningSpec Pr) oa) = simulateQ (routeImpl Pr) oa := by
  refine StateT.ext fun c ↦ ?_
  simp only [ΦJS, run_stMap, run_simulateQ_rImpl, simulateQ_σJS_liftSig]

/-- **Class-routed computations map to the class-routed run.** -/
theorem ΦJS_rcS (sk : Sphincs.Seeded.SecretKey) (pj : Bytes) {α : Type} (oa : OracleComp OW α) :
    ΦJS sk (rcS pj oa) = simulateQ (routeImpl (PrivJ pj)) oa :=
  ΦJS_rImpl sk _ oa

/-- **Private computations map to the private run.** -/
theorem ΦJS_rpS (sk : Sphincs.Seeded.SecretKey) {α : Type} (oa : OracleComp OW α) :
    ΦJS sk (rpS oa) = simulateQ (routeImpl (fun _ ↦ True)) oa :=
  ΦJS_rImpl sk _ oa

/-- **Key `j`'s signing request maps to its signer**, which does not touch the private cache. -/
theorem ΦJS_signQuery (sk : Sphincs.Seeded.SecretKey) (msg : Sphincs.Message) :
    ΦJS sk (liftM (liftM (RSs.query (.inr msg)) : OracleComp RSs (Option Sphincs.Signature)) :
      RMs (Option Sphincs.Signature)) =
      liftM (sLift (Sphincs.Seeded.sign sk msg :
        OracleComp Sphincs.HashSpec (Option Sphincs.Signature))) := by
  refine StateT.ext fun c ↦ ?_
  simp only [ΦJS, run_stMap, OracleComp.liftM_run_StateT, simulateQ_bind, simulateQ_pure]
  rw [simulateQ_spec_query]
  rfl

/-- `ΦJS` of a pure computation. -/
theorem ΦJS_pure (sk : Sphincs.Seeded.SecretKey) {α : Type} (a : α) :
    ΦJS sk (pure a : RMs α) = pure a := (isMorphism_ΦJS sk).pure a

/-- `ΦJS` of a bind. -/
theorem ΦJS_bind (sk : Sphincs.Seeded.SecretKey) {α β : Type} (x : RMs α) (f : α → RMs β) :
    ΦJS sk (x >>= f) = ΦJS sk x >>= fun a ↦ ΦJS sk (f a) := (isMorphism_ΦJS sk).bind x f

/-- `ΦJS` of a map. -/
theorem ΦJS_map (sk : Sphincs.Seeded.SecretKey) {α β : Type} (f : α → β) (x : RMs α) :
    ΦJS sk (f <$> x) = f <$> ΦJS sk x := by
  rw [map_eq_bind_pure_comp, ΦJS_bind, map_eq_bind_pure_comp]
  exact bind_congr fun a ↦ ΦJS_pure sk _

end PerKeyS

end
end LeanVM.E2E
