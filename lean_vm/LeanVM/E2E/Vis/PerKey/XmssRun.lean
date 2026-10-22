/-
  LeanVM.E2E.Vis.PerKey.XmssRun

  W-vis, P7b: the per-key leanXMSS reduction's run under the single-key game's oracles, as a
  computation of the schemes' world with the private cache.
-/

module

public import LeanVM.E2E.Vis.PerKey.Xmss
public import LeanVM.E2E.Vis.PerKey.Morph

/-!
# The reduction's run, in the schemes' world (W-vis, P7b)

The single-key game answers the reduction's world `OW + SigningSpec` by passing the schemes' world
through and signing with key `j`'s secret key `sk` (`σJ sk`, the log forgotten). Under it, the
reduction's monad maps to `PM`, computations with the private cache over the schemes' world
(`ΦJ sk`, a monad morphism):

* class-routed computations to the routed oracle `routeImpl (PrivJ pj)` (`ΦJ_rc`);
* private computations to `routeImpl (fun _ ↦ True)` (`ΦJ_rp`);
* key `j`'s signing request to its signer (`ΦJ_signQuery`).
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

namespace PerKeyX

variable {nx ns : ℕ}

/-- **The single-key game's oracles, the log forgotten**: the schemes' world passed through, a
signing request signed with `sk`. -/
noncomputable def σJ (sk : LeanXmss.Seeded.SecretKey) : QueryImpl RS (OracleComp OW) :=
  QueryImpl.ofLift OW (OracleComp OW) +
    (fun req : LeanXmss.SignRequest ↦ (liftM (LeanXmss.Seeded.sign sk req.leafIndex req.message :
      OracleComp LeanXmss.HashSpec _) : OracleComp OW (Option LeanXmss.Signature)) :
      QueryImpl LeanXmss.SigningSpec (OracleComp OW))

/-- The schemes' world lifted and answered by the game's oracles is itself. -/
theorem simulateQ_σJ_liftSig (sk : LeanXmss.Seeded.SecretKey) {α : Type} (oa : OracleComp OW α) :
    simulateQ (σJ sk) (liftSig LeanXmss.SigningSpec oa) = oa := by
  unfold liftSig
  rw [← QueryImpl.simulateQ_compose]
  conv_rhs => rw [← simulateQ_ofLift_eq_self oa]
  congr 1

/-- Computations with the private cache over the schemes' world. -/
abbrev PM : Type → Type := StateT (QueryCache LeanXmss.HashSpec) (OracleComp OW)

/-- **The reduction's monad, under the game's oracles.** -/
noncomputable def ΦJ (sk : LeanXmss.Seeded.SecretKey) {α : Type} (x : RM α) : PM α :=
  stMap (fun {β : Type} (y : OracleComp RS β) ↦ simulateQ (σJ sk) y) x

/-- `ΦJ` is a monad morphism. -/
theorem isMorphism_ΦJ (sk : LeanXmss.Seeded.SecretKey) :
    IsMorphism (fun {α : Type} (x : RM α) ↦ ΦJ sk x) :=
  isMorphism_stMap (isMorphism_simulateQ (σJ sk))

/-- A routed computation, under the game's oracles, is the routed run. -/
theorem ΦJ_rImpl (sk : LeanXmss.Seeded.SecretKey) (Pr : List UInt8 → Prop) [DecidablePred Pr]
    {α : Type} (oa : OracleComp OW α) :
    ΦJ sk (simulateQ (rImpl LeanXmss.SigningSpec Pr) oa) = simulateQ (routeImpl Pr) oa := by
  refine StateT.ext fun c ↦ ?_
  simp only [ΦJ, run_stMap, run_simulateQ_rImpl, simulateQ_σJ_liftSig]

/-- **Class-routed computations map to the class-routed run.** -/
theorem ΦJ_rc (sk : LeanXmss.Seeded.SecretKey) (pj : Bytes) {α : Type} (oa : OracleComp OW α) :
    ΦJ sk (rc pj oa) = simulateQ (routeImpl (PrivJ pj)) oa :=
  ΦJ_rImpl sk _ oa

/-- **Private computations map to the private run.** -/
theorem ΦJ_rp (sk : LeanXmss.Seeded.SecretKey) {α : Type} (oa : OracleComp OW α) :
    ΦJ sk (rp oa) = simulateQ (routeImpl (fun _ ↦ True)) oa :=
  ΦJ_rImpl sk _ oa

/-- **Key `j`'s signing request maps to its signer**, which does not touch the private cache. -/
theorem ΦJ_signQuery (sk : LeanXmss.Seeded.SecretKey) (req : LeanXmss.SignRequest) :
    ΦJ sk (liftM (liftM (RS.query (.inr req)) : OracleComp RS (Option LeanXmss.Signature)) :
      RM (Option LeanXmss.Signature)) =
      liftM (liftM (LeanXmss.Seeded.sign sk req.leafIndex req.message :
        OracleComp LeanXmss.HashSpec _) : OracleComp OW (Option LeanXmss.Signature)) := by
  refine StateT.ext fun c ↦ ?_
  simp only [ΦJ, run_stMap, OracleComp.liftM_run_StateT, simulateQ_bind, simulateQ_pure]
  rw [simulateQ_spec_query]
  rfl

end PerKeyX

end
end LeanVM.E2E
