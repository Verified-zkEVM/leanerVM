/-
  LeanVM.E2E.KS.Prefix

  The deployed game before verification (decision E2E-15): the keys, the adversary with its
  oracles and its transcript recorded. The forgery events the reductions bound read only it.
-/

module

public import LeanVM.E2E.KS.Game

/-!
# The deployed game before verification

* `pGameComp`, `pGame`: the deployed game without the verifier: key generation and the adversary
  with the game's oracles, its hash queries recorded (`record`).
* `KnownForgedX`, `KnownForgedS`: a claim of the root statement for an honest key on a message no
  request to that key was answered for, with a signature valid under the adversary's own hash
  answers. The leanXMSS and leanSPHINCS reductions bound them over `pGame`.
* `prEvent_dGame_pre`: an event of the outcome before verification has the same probability in
  the deployed game as in `pGame` (`KS/Marginal.lean`).
-/

namespace LeanVM.E2E.KS

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom
open LeanVM.E2E OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

variable {nx ns : ℕ}

/-- What the deployed game reaches before verification. -/
structure POutcome (nx ns : ℕ) [Sphincs.Params] where
  /-- The honest keys. -/
  keys : Keys nx ns
  /-- The root statement. -/
  statement : NodeStatement
  /-- The deployed proof. -/
  proof : Proof
  /-- The adversary's hash queries and their answers, in order. -/
  trace : Log
  /-- The signers' final state. -/
  state : SignState nx ns

variable [Sphincs.Params]

/-- The outcome before verification. -/
def DOutcome.pre (z : DOutcome nx ns) : POutcome nx ns :=
  ⟨z.keys, z.statement, z.proof, z.trace, z.state⟩

/-- **The deployed game before verification, as an oracle computation**: key generation and the
adversary with the game's oracles, its transcript recorded. -/
noncomputable def pGameComp (A : DAdversary nx ns) : OracleComp GameSpec (POutcome nx ns) := do
  let (out, st) ← (do
      let keys ← keygen
      let ((s, π), tr) ← simulateQ (advImpl keys)
        (record (A (fun j ↦ (keys.xmss j).1) (fun j ↦ (keys.sphincs j).1)))
      pure (keys, s, π, tr) : GameM nx ns _).run (SignState.init nx ns)
  pure ⟨out.1, out.2.1, out.2.2.1, out.2.2.2, st⟩

/-- **The deployed game before verification**, against the lazily sampled random oracle. -/
noncomputable def pGame (A : DAdversary nx ns) : ProbComp (POutcome nx ns × Log) :=
  (simulateQ (coinImpl + (Rom.loggedRO : QueryImpl HashSpec (StateT Log ProbComp)))
    (pGameComp A) : StateT Log ProbComp (POutcome nx ns)).run []

/-- **A known leanXMSS forgery**: a leanXMSS claim of the root statement for an honest key on a
message no request to that key was answered for, with a signature valid under the adversary's own
hash answers. -/
def KnownForgedX (z : POutcome nx ns) : Prop :=
  ∃ j : Fin nx, ∃ msg σ, ((z.keys.xmss j).1, msg) ∈ z.statement.claims.xmss ∧
    (∀ e ∈ z.state.xlog j, e.1.2 = msg → e.2 = none) ∧
    xmssVerifyWith (look z.trace) (z.keys.xmss j).1 msg σ = some true

/-- **A known leanSPHINCS forgery**: a leanSPHINCS claim of the root statement for an honest key
on a message no request to that key was answered for, with a signature valid under the
adversary's own hash answers. -/
def KnownForgedS (z : POutcome nx ns) : Prop :=
  ∃ j : Fin ns, ∃ msg σ, ((z.keys.sphincs j).1, msg) ∈ z.statement.claims.sphincs ∧
    (∀ e ∈ z.state.slog j, e.1 = msg → e.2 = none) ∧
    sphincsVerifyWith (look z.trace) (z.keys.sphincs j).1 msg σ = some true

/-- The deployed game's hash evaluations before verification. -/
def preQueries (nx ns qH sX sS : ℕ) : ℕ :=
  nx * xmssKeygenBound + ns * sphincsKeygenBound + (qH + sX * xmssSignBound + sS * sphincsSignBound)

end
end LeanVM.E2E.KS
