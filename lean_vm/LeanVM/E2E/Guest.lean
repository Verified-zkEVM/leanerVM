/-
  LeanVM.E2E.Guest

  T2 and T4 without hypotheses: the guest's open callees are sound over every hash model.
-/

module

public import LeanVM.Guest.Located.RootWhirM
public import LeanVM.Guest.B1.Tables.GuestHypsM
public import LeanVM.E2E.Knowledge

/-!
# The guest's callees over every hash model, and T2 and T4 unconditional

`Guest.Located.GuestHypsM M` collects the five callee facts T2 was assembled over (the batch
sumcheck, GKR, the tables, Flock, the stacked opening at every frame chooser); each is proved for
every hash model (`Located.batchSumcheckM_model`, `VerifySub.guestHypsM_gkr`, `…_tables`,
`…_flock`, `Located.openStacked_model`), so `guestHypsM_model` holds for every `M`. Hence T2
(`guest_knowledge_model_all`: every execution valid under a model's semantics decodes to a
statement of its input's digest and a witness of `NodeRelWith M.H`) and T4
(`aggregate_knowledge`, `prEvent_game_aggregate`) hold without hypotheses.
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Guest LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Blind LeanVM.Protocol.EndToEnd.Sound LeanVM.Protocol.Rom
open OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

/-- **The guest's open callees are sound over every hash model.** -/
theorem guestHypsM_model (M : HashModel) : Located.GuestHypsM M where
  batch_sumcheck := Located.batchSumcheckM_model M
  gkr := B1.VerifySub.guestHypsM_gkr M
  tables := B1.VerifySub.guestHypsM_tables M
  flock := B1.VerifySub.guestHypsM_flock M
  open_stacked := fun fr {_} L h1 h2 ↦ Located.openStacked_model M fr L h1 h2

/-- **T2, unconditional**: for every hash model and every frame chooser, every execution of the
guest valid under the model's semantics decodes to a statement of its input's digest and a
witness of `NodeRelWith M.H` with the baked batching start and padding digests. -/
theorem guest_knowledge_model_all (M : HashModel) (fr : String → List E → Option ℕ) :
    ∀ input (t : Trace guest), ValidExecutionB M.sem guest input t →
      End.DecodesOnWith M B1.Main.aggSeedD B1.Main.daPadCell B1.Main.daPadRow guest input
        (End.decodeAt M.sem fr t.image) :=
  End.guest_knowledge_model_at M (guestHypsM_model M) fr

/-- **T4, unconditional (cache form)**: on a log without the chain's bad events, V_I accepting
with every hash answered by the log means every root leanXMSS and leanSPHINCS claim has a
signature valid under the log and every root DA claim is backed by codeword rows. -/
theorem aggregate_knowledge {ℓ : Log} (hbad : ¬ AggBad ℓ) {ip : IdealProof} {fuel : ℕ}
    {s : NodeStatement} (hv : idealVerify (look ℓ) Guest.guest ip fuel s = some true) :
    (∀ c ∈ s.claims.xmss, ∃ σ, xmssVerifyWith (look ℓ) c.1 c.2 σ = some true) ∧
    (∀ c ∈ s.claims.sphincs, ∃ σ, sphincsVerifyWith (look ℓ) c.1 c.2 σ = some true) ∧
    ∀ c ∈ s.claims.da, DaBacked ℓ deployedPads.1 deployedPads.2 c :=
  aggregate_knowledge_cache (fun _ _ ↦ guestHypsM_model _) hbad hv

variable {nx ns : ℕ} [Sphincs.Params]

/-- **T4, unconditional (in the game)**: V_I accepting under the game's final log while some root
claim is not known has probability at most the sum of T1's, W6's, E5's and T3's terms. -/
theorem prEvent_game_aggregate (fuel budget : ℕ) (A : GameAdversary nx ns) (Q : ℕ)
    (hQ : IsQueryBoundP (gameComp Guest.guest fuel budget A) IsHash Q) :
    Pr{let z ← game Guest.guest fuel budget A}[
        idealVerify (look z.2) Guest.guest z.1.proof fuel z.1.statement = some true ∧
          ¬ ClaimsKnown z.2 z.1.statement] ≤
      Q * (εLean + failBound leanVmSeeds Q) + Q * (2 / 2 ^ 192 + 4 * (Q + 1) / 2 ^ 256) +
        Q * (14 / 2 ^ 192 + 4 * Q / 2 ^ 256) + Q * (Q + 1) / 2 ^ 193 :=
  prEvent_game_aggregate_le (fun _ _ _ ↦ guestHypsM_model _) fuel budget A Q hQ

end
end LeanVM.E2E
