/-
  LeanVM.E2E.KS.Game

  The deployed game (decision E2E-15 of `docs/roadmap/e2e-security.md`): the deployed outer
  verifier `verifyAggregate`, run with the random oracle, against an adversary that outputs a root
  statement and a deployed proof; the knowledge-soundness assumption on it, and the forgery event.
-/

module

public import LeanVM.E2E.Engine
public import LeanVM.E2E.Reduction.XmssBound
public import LeanVM.E2E.Reduction.SphincsBound

/-!
# The deployed game

* **The verifier.** `verifyAggregateWith H guest s π` is the deployed outer verifier
  (`Node.verifyAggregate`) with the hash `H`: the IV, the statement's digest and the leanVM
  verifier with `H`, every DA claim's vector digest with `H`, and the deferred claim (hash-free).
  At `Id` and BLAKE2s it is `verifyAggregate` (`verifyAggregateWith_blake2s`).
* **The adversary** (`DAdversary`): from the honest public keys, with coins, the hash and the
  signing oracles, a root statement and a deployed proof `π`. Its hash queries and their answers
  are recorded, in order (`record`, `DOutcome.trace`): what a straight-line extractor reads.
* **The game** (`dGameComp`, `dGame`): the honest keys, the adversary with the game's oracles
  (`advImpl`, as in `game`), then `verifyAggregateWith` with the oracle, against one lazily sampled
  random oracle shared by every party.
* **Knowledge soundness** (`KnowledgeSound guest A ε`, the assumption): except with probability
  `ε`, whenever the verifier accepts, every signature claim `(pk, m)` of the root statement has a
  signature `σ` valid under the adversary's own hash answers (`ClaimsKnown`).
* **The event** (`DForged`): a claim of the root statement for an honest key on a message no
  request to that key was answered for (`Forged`'s condition).
-/

namespace LeanVM.E2E.KS

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom
open LeanVM.E2E OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

/-! ## The deployed verifier with any hash -/

section Verify

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest)

open Classical in
/-- **The deployed outer verifier with the hash `H`** (`Node.verifyAggregate`): the leanVM verifier
on the statement's digest under the guest's IV, every DA claim's vector digest its root's, and the
deferred claim. -/
noncomputable def verifyAggregateWith (guest : Program) (s : NodeStatement) (π : Proof) :
    m Bool := do
  let iv ← fiatShamirIvWith H (bytecodeWords guest)
  let pi ← statementDigestWith H iv s
  let ok ← verifyWith H (bytecodeWords guest) pi π
  let da ← s.claims.da.allM fun c ↦ do
    pure (decide (Da.toBytes c.2 = (← Da.vectorDigestOfWith H c.1)))
  pure (ok && da && decide (s.defer.Holds (bytecodeWords guest)))

end Verify

/-- The DA checks at BLAKE2s. -/
theorem allM_da_blake2s (l : List DaClaim) :
    Id.run (l.allM fun c ↦ do
      pure (decide (Da.toBytes c.2 = (← Da.vectorDigestOfWith (m := Id) blake2sBytes c.1))) :
        Id Bool) = l.all fun c ↦ decide (Da.toBytes c.2 = Da.vectorDigestOf c.1) := by
  induction l with
  | nil => rw [List.allM_nil, List.all_nil]; rfl
  | cons c l ih =>
    rw [List.allM_cons, List.all_cons, ← Da.vectorDigestOfWith_id]
    change (if decide (Da.toBytes c.2 = Id.run (Da.vectorDigestOfWith (m := Id) blake2sBytes c.1))
      = true then Id.run (List.allM _ l) else false) = _
    rw [ih]
    by_cases h : Da.toBytes c.2 = Id.run (Da.vectorDigestOfWith (m := Id) blake2sBytes c.1)
    · simp [h]
    · simp [h]

/-- **At BLAKE2s it is the deployed verifier.** -/
theorem verifyAggregateWith_blake2s (guest : Program) (s : NodeStatement) (π : Proof) :
    Id.run (verifyAggregateWith (m := Id) blake2sBytes guest s π) = true ↔
      verifyAggregate guest s π := by
  classical
  have e : Id.run (verifyAggregateWith (m := Id) blake2sBytes guest s π) =
      (Id.run (verifyWith (m := Id) blake2sBytes (bytecodeWords guest)
          (Id.run (statementDigestWith (m := Id) blake2sBytes
            (Id.run (fiatShamirIvWith (m := Id) blake2sBytes (bytecodeWords guest))) s)) π) &&
        s.claims.da.all (fun c ↦ decide (Da.toBytes c.2 = Da.vectorDigestOf c.1)) &&
        decide (s.defer.Holds (bytecodeWords guest))) := by
    rw [← allM_da_blake2s]
    rfl
  rw [e, verifyAggregate, OuterChecks, verifyWith_blake2sBytes, statementDigestWith_id]
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  tauto


/-! ## The game -/

variable {nx ns : ℕ}

/-- **An adversary of the deployed game**: from the honest public keys, with coins, the hash and
the signing oracles, a root statement and a deployed proof. -/
abbrev DAdversary (nx ns : ℕ) : Type :=
  (Fin nx → LeanXmss.PublicKey) → (Fin ns → Sphincs.PublicKey) →
    OracleComp (AdvSpec nx ns) (NodeStatement × Proof)

/-- The adversary's oracles with its hash queries recorded: every query forwarded, each hash
query's input and answer appended to the log. -/
def recordImpl : QueryImpl (AdvSpec nx ns) (StateT Log (OracleComp (AdvSpec nx ns)))
  | .inl (.inl (.inr x)) => do
    let u ← (liftM ((AdvSpec nx ns).query (.inl (.inl (.inr x)))) :
      OracleComp (AdvSpec nx ns) Digest)
    modify (· ++ [(x, u)])
    pure u
  | t => liftM ((AdvSpec nx ns).query t)

/-- **The adversary with its transcript**: its output and its hash queries with their answers, in
order. -/
def record {α : Type} (oa : OracleComp (AdvSpec nx ns) α) : OracleComp (AdvSpec nx ns) (α × Log) :=
  (simulateQ recordImpl oa).run []

/-- What the deployed game outputs. -/
structure DOutcome (nx ns : ℕ) [Sphincs.Params] where
  /-- The honest keys. -/
  keys : Keys nx ns
  /-- The root statement. -/
  statement : NodeStatement
  /-- The deployed proof. -/
  proof : Proof
  /-- The adversary's hash queries and their answers, in order. -/
  trace : Log
  /-- The deployed verifier accepted. -/
  accepted : Bool
  /-- The signers' final state. -/
  state : SignState nx ns

variable [Sphincs.Params]

/-- **The deployed game, as an oracle computation**: key generation, the adversary with the game's
oracles and its transcript recorded, then the deployed verifier with the oracle. -/
noncomputable def dGameComp (guest : Program) (A : DAdversary nx ns) :
    OracleComp GameSpec (DOutcome nx ns) := do
  let (out, st) ← (do
      let keys ← keygen
      let ((s, π), tr) ← simulateQ (advImpl keys)
        (record (A (fun j ↦ (keys.xmss j).1) (fun j ↦ (keys.sphincs j).1)))
      let b ← verifyAggregateWith hashQuery guest s π
      pure (keys, s, π, tr, b) : GameM nx ns _).run (SignState.init nx ns)
  pure ⟨out.1, out.2.1, out.2.2.1, out.2.2.2.1, out.2.2.2.2, st⟩

/-- **The deployed game**: `dGameComp` against one random oracle, lazily sampled over the ordered
log of its fresh queries, from the empty log; the outcome and the final log. -/
noncomputable def dGame (guest : Program) (A : DAdversary nx ns) :
    ProbComp (DOutcome nx ns × Log) :=
  (simulateQ (coinImpl + (Rom.loggedRO : QueryImpl HashSpec (StateT Log ProbComp)))
    (dGameComp guest A) : StateT Log ProbComp (DOutcome nx ns)).run []

/-! ## Knowledge soundness and the event -/

/-- **The adversary knows every signature claim**: each leanXMSS and leanSPHINCS claim `(pk, m)`
of the root statement has a signature valid under the answers of the adversary's own hash
queries. -/
def ClaimsKnown (z : DOutcome nx ns) : Prop :=
  (∀ c ∈ z.statement.claims.xmss, ∃ σ, xmssVerifyWith (look z.trace) c.1 c.2 σ = some true) ∧
    ∀ c ∈ z.statement.claims.sphincs, ∃ σ, sphincsVerifyWith (look z.trace) c.1 c.2 σ = some true

/-- **Knowledge soundness of the deployed aggregation against `A`, with error `ε`** (the
assumption): the deployed verifier accepts a root statement with a signature claim the adversary
does not know a signature for with probability at most `ε`. -/
def KnowledgeSound (guest : Program) (A : DAdversary nx ns) (ε : ℝ≥0∞) : Prop :=
  Pr{let z ← dGame guest A}[z.1.accepted = true ∧ ¬ ClaimsKnown z.1] ≤ ε

/-- **A forgery**: a claim of the root statement for an honest key of its scheme on a message
no request to that key was answered for. -/
def DForged (z : DOutcome nx ns) : Prop :=
  (∃ j : Fin nx, ∃ msg, ((z.keys.xmss j).1, msg) ∈ z.statement.claims.xmss ∧
    ∀ e ∈ z.state.xlog j, e.1.2 = msg → e.2 = none) ∨
  (∃ j : Fin ns, ∃ msg, ((z.keys.sphincs j).1, msg) ∈ z.statement.claims.sphincs ∧
    ∀ e ∈ z.state.slog j, e.1 = msg → e.2 = none)

/-- **What the adversary may do**: at most `qH` hash queries, `sX` leanXMSS and `sS` leanSPHINCS
signing requests, whatever the honest public keys. -/
structure DAdvBounds (A : DAdversary nx ns) (qH sX sS : ℕ) : Prop where
  hash : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH
  xmss : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX
  sphincs : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS

/-- **The deployed game against `A` makes at most `q` hash evaluations before verification**: the
honest key generations, `A`'s at most `qH` hash queries, and the `sX` leanXMSS and `sS`
leanSPHINCS signatures it requests at their proved worst-case costs. -/
def DHashEvals (A : DAdversary nx ns) (q : ℕ) : Prop :=
  ∃ qH sX sS, DAdvBounds A qH sX sS ∧
    nx * xmssKeygenBound + ns * sphincsKeygenBound +
      (qH + sX * xmssSignBound + sS * sphincsSignBound) ≤ q

end
end LeanVM.E2E.KS
