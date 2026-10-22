/-
  LeanVM.Guest.Value.NodeSome

  The node relation's hashing functions over a hash that answers every input: `some` of the
  deployed ones.
-/

module

public import LeanVM.Guest.Value.RunSome
public import LeanVM.Spec.NodeWith

/-!
# The node's digests over a hash that answers everything

`Spec/NodeWith.lean` gives each hashing function of `NodeRel` over a hash in any monad, and
recovers the deployed one at `Id`. Over `Option` with the hash `fun x ↦ some (blake2sBytes x)`
(`HashModel.deployed.H`) each is `some` of the deployed one: `statementDigestWith_some`,
`childClaimsWith_some`, `verifyDeferredWith_some`, and `batchWith_some` (the chain in `StateT`:
its `for` loops by `forIn_some`, its rounds by induction). These are the bridges from the guest's conclusions over a hash model
(`NodeRelWith M.H`) to the deployed ones at `HashModel.deployed`; the signature schemes' and the
DA openings' are separate (`docs/roadmap/w2-guest-model.md` (removed; in git at `6ffa1d1f`), package W2-S).
-/

namespace LeanVM.Guest.Value

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-- The deployed hash, answering every input. -/
abbrev someBlake (x : Bytes) : Option Digest := some (blake2sBytes x)

theorem statementDigestWith_some (seed : Digest) (s : NodeStatement) :
    statementDigestWith (m := Option) someBlake seed s = some (statementDigest seed s) := rfl

theorem childClaimsWith_some (seed : Digest) (children : List Child) :
    childClaimsWith someBlake seed children =
      some (children.map fun c ↦ ⟨statementDigest seed c.statement, c.fresh, c.statement.defer⟩) := by
  induction children with
  | nil => rfl
  | cons c cs ih =>
    simp only [childClaimsWith, List.mapM_cons, statementDigestWith_some] at ih ⊢
    rw [ih]
    rfl

theorem verifyDeferredWith_some (bytecode : List K) (iv publicInput : Digest) (c : FixedClaims)
    (π : Proof) :
    verifyDeferredWith (m := Option) someBlake bytecode iv publicInput c π =
      some (verifyDeferred bytecode iv publicInput c π) := by
  simp only [verifyDeferredWith, Option.bind_eq_bind, Option.bind_some, runProof_some]
  rfl

theorem observeWith_some (x : E) (cv : Digest) :
    (observeWith (m := Option) someBlake x).run cv = some ((Node.observe x).run cv) := rfl

theorem squeezeWith_some (cv : Digest) :
    (squeezeWith (m := Option) someBlake).run cv = some (Node.squeeze.run cv) := rfl

theorem batchRoundsWith_some : ∀ (claim : E) (rounds : List (E × E)) (cv : Digest),
    (batchRoundsWith (m := Option) someBlake claim rounds).run cv =
      some ((batchRounds claim rounds).run cv)
  | _, [], _ => rfl
  | claim, (g1, gInf) :: rest, cv => by
    simp only [batchRoundsWith, batchRounds, StateT.run_bind, observeWith_some, squeezeWith_some,
      Option.bind_eq_bind, Option.bind_some]
    rw [batchRoundsWith_some]
    rfl

/-- A `for` loop of the chain whose body over `Option` is `some` of one over `Id` is `some` of
that loop. -/
theorem forIn_some {β σ : Type} (f : β → σ → StateT Digest Option (ForInStep σ))
    (g : β → σ → StateT Digest Id (ForInStep σ))
    (h : ∀ b s cv, (f b s).run cv = some ((g b s).run cv)) :
    ∀ (l : List β) (init : σ) (cv : Digest),
      (forIn l init f).run cv = some ((forIn l init g).run cv)
  | [], _, _ => rfl
  | b :: l, init, cv => by
    simp only [List.forIn_cons, StateT.run_bind, h, Option.bind_eq_bind, Option.bind_some]
    show _ = some ((g b init).run cv >>= fun p => _)
    rcases hh : (g b init).run cv with ⟨r, cv'⟩
    cases r with
    | done x => rfl
    | yield x => exact forIn_some f g h l x cv'

/-- `observeWith_some`, as the batching's `do` blocks state it. -/
theorem observeWith_run_some (x : E) (cv : Digest) :
    StateT.run (observeWith (m := Option) someBlake x) cv = some ((Node.observe x).run cv) := rfl

/-- `squeezeWith_some`, as the batching's `do` blocks state it. -/
theorem squeezeWith_run_some (cv : Digest) :
    StateT.run (squeezeWith (m := Option) someBlake) cv = some (Node.squeeze.run cv) := rfl

/-- **The batching over the deployed hash answering everything**, from the label's hash: `some`
of the deployed batching. -/
theorem batchWith_some (children : List ChildClaims) (hints : BatchHints) :
    batchWith (m := Option) someBlake (blake2sBytes batchLabel) children hints =
      some (batch children hints) := by
  simp only [batchWith, batch, batchWith.go, batch.go, StateT.run'_eq, StateT.run_bind,
    observeWith_run_some, Option.bind_eq_bind, Option.bind_some]
  rw [forIn_some _ _ ?h1]
  case h1 =>
    intro b s cv
    simp only [StateT.run_bind, observeWith_run_some, Option.bind_eq_bind, Option.bind_some]
    rw [forIn_some _ _ ?h2]
    case h2 =>
      intro b s cv
      simp only [StateT.run_bind, observeWith_run_some, Option.bind_eq_bind, Option.bind_some]
      rfl
    rfl
  simp only [Option.bind_some]
  rw [forIn_some _ _ ?h3]
  case h3 =>
    intro b s cv
    simp only [StateT.run_bind, squeezeWith_run_some, Option.bind_eq_bind, Option.bind_some]
    rfl
  simp only [Option.bind_some, batchRoundsWith_some]
  rw [forIn_some _ _ ?h4]
  case h4 =>
    intro b s cv
    simp only [StateT.run_bind, squeezeWith_run_some, Option.bind_eq_bind, Option.bind_some]
    rfl
  simp only [Option.bind_some, id_bind]
  split_ifs with h1 h2 h2 <;> first | rfl | exact absurd h1 h2 | exact absurd h2 h1

end
end LeanVM.Guest.Value
