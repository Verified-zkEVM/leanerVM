/-
  LeanVM.E2E.Complete.Rom.Comp

  T6-prob: the H-oblivious honest prover with the hash a parameter in any monad — at the random
  oracle's queries, the honest prover of the random-oracle model.
-/

module

public import LeanVM.E2E.Complete.Rom.ProverN
public import LeanVM.E2E.Complete.Rom.MonadicM

/-!
# The honest prover as an oracle computation

`docs/roadmap/t6-prob.md` §3. `honestProverM H ρ pfuel T` is `honestOutN` (`ProverN.lean`) with
every hash a call of `H : Bytes → m Digest`, in `ExceptT ProverFail m`: the children first, then
the batching (`honestBatchM`, `batchWith`), the node's log (`nodeLogPairsM`), the execution chosen
from it (`execOf`), V°'s honest proof (`proveM`), the fresh claims (`freshRunM`). At
`m := OracleComp HashSpec`, `H := queryH` it is the honest prover of the random-oracle model
(`honestProverComp`); every choice is a function of answers it received.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Node LeanVM.Guest
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd LeanVM.Protocol.Whir.Complete
open LeanVM.Protocol.Compile.Rom OracleComp

@[expose] public section

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest) (ρ pfuel : ℕ)

/-- The children's claims, by calls of `H` (`childClaimsOf`). -/
def claimsOfM (cs : List Child) : m (List ChildClaims) :=
  cs.mapM fun c ↦ do
    let d ← digestOfM H c.statement
    pure ⟨d, c.fresh, c.statement.defer⟩

open Classical in
/-- **The deferred claim and hints** (`honestDeferN`), by calls of `H`. -/
noncomputable def honestDeferM (cs : List Child) : ExceptT ProverFail m (BatchHints × DeferredClaim) :=
  if cs = [] then pure (noHints, leafDefer) else do
  let ccs ← (claimsOfM H cs : m _)
  let wh ← (honestBatchM H B1.Main.aggSeedD End.bytecode ccs : m _)
  if wh.1 = (0, 0) then throw (.weights ccs) else do
  let r ← (batchWith H B1.Main.aggSeedD ccs wh.2 : m _)
  match r with
  | some d => if d.BytecodeHolds End.bytecode then pure (wh.2, d) else throw .stuck
  | none => throw .stuck

/-- **A node's proof** (`proveNode`), by calls of `H`. -/
noncomputable def proveNodeM (s : NodeStatement) (w : NodeWitness) (kos : List HonestOutN) :
    ExceptT ProverFail m HonestOutN := do
  let pi ← (digestOfM H s : m _)
  let L ← (nodeLogPairsM H s w : m _)
  match execOf L pi w with
  | none => throw .stuck
  | some e =>
    let seed ← (seedWith H End.bytecode (publicDigest (End.publicInputOf pi)) : m _)
    let r ← (proveM H (progOf pi) (stratOf ρ e) seed pfuel : m _)
    match r with
    | none => throw (.grind (progOf pi) (stratOf ρ e) seed)
    | some π =>
      let c? ← (freshRunM H (stratOf ρ e) pfuel End.bytecode
        (publicDigest (End.publicInputOf pi)) seed : m _)
      match c? with
      | none => throw .stuck
      | some c =>
        let kids ← (kos.mapM fun ko ↦ do
          let d ← digestOfM H ko.stmt
          pure (d, ko.proof) : m _)
        pure ⟨s, c, π,
          ((pi, π), stackWord (leanIsaμ guest e.1.sz) e.1.q, e.1.fr, kids,
            1 + (kos.map HonestOutN.size).sum) :: kos.flatMap HonestOutN.entries,
          1 + (kos.map HonestOutN.size).sum⟩

/-- **The node step** (`honestStepN`), by calls of `H`. -/
noncomputable def honestStepM (claims : Claims) (xs : List (Holder LeanXmss.Signature))
    (ss : List (Holder Sphincs.Signature)) (ds : List (Holder Da.Witness))
    (kos : List HonestOutN) : ExceptT ProverFail m HonestOutN := do
  let hd ← honestDeferM H (kos.map HonestOutN.child)
  proveNodeM H ρ pfuel ⟨claims, hd.2⟩ ⟨kos.map HonestOutN.child, xs, ss, ds, hd.1⟩ kos

/-- **The H-oblivious honest prover, the hash a parameter** (`honestOutN`). -/
noncomputable def honestProverM : HonestTree → ExceptT ProverFail m HonestOutN
  | .node claims xs ss ds kids => do
    let kos ← kids.attach.mapM fun k ↦ honestProverM k.1
    honestStepM H ρ pfuel claims xs ss ds kos
termination_by T => sizeOf T
decreasing_by
  have := List.sizeOf_lt_of_mem k.2
  simp_wf
  omega

/-- **The honest prover of the random-oracle model**: every hash a query. -/
noncomputable def honestProverComp (T : HonestTree) :
    OracleComp HashSpec (Except ProverFail HonestOutN) :=
  (honestProverM queryH ρ pfuel T).run

end
end LeanVM.E2E.Complete
