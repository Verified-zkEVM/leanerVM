/-
  LeanVM.E2E.Statement

  The end-to-end security statement of the leanVM aggregation: the idealized verifier V_I, the
  honest-signer game in the random-oracle model, and the forgery and data-availability events.
-/

module

public import LeanVM.Guest.EndKnow
public import LeanVM.Spec.NodeWith
public import LeanVM.Spec.Ideal.Blind
public import LeanVM.Spec.Ideal.Table
public import LeanVM.Protocol.EndToEnd.Sound.Theorem
public import LeanVM.Protocol.Compile.Rom.Prover
public import LeanVM.Protocol.Compile.Rom.Log
public import LeanVM.Protocol.ToVCVio.Rom.LoggedOracle

/-!
# End-to-end security: the statement

The design is `docs/roadmap/e2e-security.md`; this module states its §0 to §3 in Lean.

**The idealized verifier** `idealVerify` (V_I, §2) is an algorithm with a hash `H` in any monad,
not succinct: an idealized proof (`IdealProof`) is the root's proof with the level-0 word of
every commitment root. It checks the root statement's proof with the Flock-blind verifier V°
(`Verifier.verifyBlindWith`) and the outer checks, then closes the set of nodes under the
children decoded from every candidate the committed words allow: for every node, the word under
its stack root has that root, and every candidate satisfying the leanISA relation without Flock
(`M3HoldsBlind`) is an execution under the Flock-blind semantics (`haltingRunB blakeFree`) whose
`BLAKE2S` rows pass the precheck and the table check (`tableOKWith`); its decoded children are
nodes. The closure runs in `fuel` steps. V_I decodes with the deployed guest's decoder
(`LeanVM.Guest.End.decode`), so the end theorem is about the deployed guest (`prog := guest`).

**The game** (`game`, §3, with decision E2E-1 of the design's §7): one random oracle
`H : Bytes → Digest`, lazily sampled over the ordered log of its fresh queries (`Rom.loggedRO`),
which every party queries (`hashQuery`): the adversary, the honest signers, V_I. The game is an
oracle computation over coins and the hash (`gameComp`), the signers' requests its state, run
against the logged oracle (`game`); its outcome carries the oracle's final log. A static set of
`nx` leanXMSS and `ns` leanSPHINCS honest keys is generated first. The adversary, with private
coins, the hash and signing oracles, outputs a root statement and an idealized proof. A signing oracle refuses a
leanXMSS leaf already used and a leanSPHINCS key's requests past its `signatureLimit`. V_I then
runs, rejecting past `budget` queries.

**The events** (`Breaks`): V_I accepts, and either the root statement has a claim of an honest
key on a message no request to that key was answered for (`Forged`), or a root DA claim is not
backed by codeword rows whose commitment and vector digest the oracle's final log answers
(`DaBacked`). The data the guest bakes as constants (the DA padding digests, the batching's start)
enter as data (D5): `DaBacked` takes the deployed padding digests.
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Protocol.LeanIsa
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Sound
open LeanVM.Protocol.Compile.Rom OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

/-! ## Executions under a `BLAKE2S` semantics -/

open Classical in
/-- The execution of `prog` on a memory image under the semantics `S`: run from `(1, 1)` for the
least number of steps after which it halts; `none` if it never does (`LeanVM.haltingRun` under
`S`). -/
noncomputable def haltingRunB (S : BlakeSem) (prog : Program) {κ : ℕ} (image : MemImage κ) :
    Option (Trace prog) :=
  if h : ∃ n, runB S prog image n Regs.initial = some (Regs.final prog) then
    some ⟨κ, image, Nat.find h⟩
  else none

/-! ## The relation V° extracts -/

/-- **`M3Holds` without Flock's R1CS**: the constraints, the bus, the counts and the public lines;
not the Flock region's predicate (`M3Instance.aux`). -/
def M3HoldsBlind (I : M3Instance) (input : I.Stmt) (q : Column I.μ) : Prop :=
  I.ConstraintsVanish q ∧ I.Balanced q ∧ I.CountsNonzero q ∧ I.PublicLinesHold input q

/-- The public input whose digest is `d` (`publicDigest`'s inverse): lane `i` of words `2i` and
`2i + 1`. -/
def inputOf (d : Digest) : PublicInput :=
  ⟨fun i ↦ K.ofBits (d[2 * i.val].toNat + 2 ^ 32 * d[2 * i.val + 1].toNat)⟩

open Classical in
/-- The sizes whose verifier layout is `layout` (a classical choice; unique,
`verifierLayout_injective`). -/
noncomputable def sizesOf (prog : Program) (layout : Verifier.Layout) : Option Sizes :=
  if h : ∃ s : Sizes, verifierLayout prog s = layout ∧ s.Admissible prog then some h.choose
  else none

/-- The stack's root a proof announces: the two scalars after the announced sizes. -/
def stackRoot (π : Proof) : Option (E × E) := do
  let a ← π.stream[2 + tables.length]?
  let b ← π.stream[3 + tables.length]?
  pure (a, b)

/-- The height and width of the stack's commitment at a layout and rate (`commitStack`). -/
def stackShape (layout : Verifier.Layout) (ρ : ℕ) : Option (ℕ × ℕ) :=
  match deriveConfig layout.stackLog ρ with
  | some (level :: _) => some (levelShape layout.stackLog level (2 ^ level.fold))
  | _ => none

/-- **The candidates V_I follows**: the stacks within level 0's Johnson radius of the word `W`
satisfying the relation without Flock, for the guest at sizes `s` on the input of the digest
`pi`. -/
def blindCandidates (prog : Program) (s : Sizes) (ρ : ℕ) (pi : Digest) (W : Word) :
    Set (Column (leanIsaμ prog s)) :=
  {q | q ∈ Candidates (leanIsaμ prog s) ρ (thrOf (leanIsaμ prog s) ρ) W ∧
    M3HoldsBlind (leanIsaInstance F₀ prog s) (inputOf pi) q}

/-- The execution a candidate's memory image runs, under the Flock-blind semantics. -/
noncomputable def candidateRun (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s)) :
    Option (Trace prog) :=
  haltingRunB blakeFree prog (Arithmetization.imageOf (witnessOf F₀ prog s q).data).2

/-! ## The table check, as V_I computes it -/

/-- A row's inputs: its message, chaining value and metadata cells. -/
def rowInput (r : BlakeRow) : (Fin 4 → E) × E × E × E := (r.m, r.cv0, r.cv1, r.md)

/-- A row with the last-block flag. -/
def RowFinal (r : BlakeRow) : Prop := (unpackMetadata r.md).2.1 = lastBlock

/-- **The precheck** (D4): no two non-final rows with distinct inputs have equal outputs. -/
def Precheck (rows : List BlakeRow) : Prop :=
  ∀ r₁ ∈ rows, ∀ r₂ ∈ rows, ¬ RowFinal r₁ → ¬ RowFinal r₂ → r₁.out = r₂.out →
    rowInput r₁ = rowInput r₂

/-- The byte strings with a standard chain among the rows. -/
def chainInputs (rows : List BlakeRow) : Set (List UInt8) :=
  {x | ∃ c : List BlakeRow, 0 < c.length ∧ (∀ r ∈ c, r ∈ rows) ∧ StdChain x c}

/-- Every standard chain of `x` among the rows ends at `d`. -/
def ChainsEndAt (rows : List BlakeRow) (x : List UInt8) (d : Digest) : Prop :=
  ∀ (c : List BlakeRow) (hc : 0 < c.length), (∀ r ∈ c, r ∈ rows) → StdChain x c →
    (c[c.length - 1]'(by omega)).out = d

open Classical in
/-- **The table check with the hash `H`** (`TableOK`): the precheck, then for every byte string
with a standard chain among the rows, its hash, which every such chain must end at. -/
noncomputable def tableOKWith {m : Type → Type} [Monad m] (H : Bytes → m Digest)
    (rows : List BlakeRow) : m Bool :=
  if Precheck rows then
    if h : (chainInputs rows).Finite then
      h.toFinset.toList.allM fun x ↦ do
        let d ← H x
        pure (decide (ChainsEndAt rows x d))
    else pure false
  else pure false

/-! ## The idealized verifier -/

/-- **The deferred claim's bytecode part is true** of the bytecode `bytecode`: the shape, and the
bytecode's multilinear extension at the bytecode point (`DeferredClaim.Holds` without the matrix
values). -/
def _root_.LeanVM.Node.DeferredClaim.BytecodeHolds (bytecode : List K) (c : DeferredClaim) : Prop :=
  c.Shaped bytecode ∧ 2 ^ c.bytecodePoint.length = bytecode.length ∧
    multilinearEval (bytecode.map ofK) c.bytecodePoint = c.bytecodeValue

/-- A true deferred claim's bytecode part is true. -/
theorem _root_.LeanVM.Node.DeferredClaim.bytecodeHolds_of_holds {bytecode : List K}
    {c : DeferredClaim} (h : c.Holds bytecode) : c.BytecodeHolds bytecode :=
  ⟨h.1, h.2.1, h.2.2.1⟩

/-- **An idealized proof**: the root's proof, and the level-0 word of every commitment root,
by its two scalars. -/
structure IdealProof where
  /-- The root statement's proof. -/
  proof : Proof
  /-- The level-0 words, by root. -/
  words : List ((E × E) × Word)

/-- The word an idealized proof gives a root. -/
def IdealProof.word (ip : IdealProof) (r : E × E) : Option Word :=
  (ip.words.find? (·.1 = r)).map (·.2)

/-- A node of V_I: a statement digest and a proof. -/
abbrev Node : Type := Digest × Proof

section Verify

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest) (prog : Program) (seed : Digest)
  (ip : IdealProof)

open Classical in
/-- **One node of V_I**: its announced sizes and stack root; the word `ip` gives that root, well
shaped, with that Merkle root; every candidate of it satisfying the relation without Flock
runs under the Flock-blind semantics and passes the table check; the nodes of the children each
decodes. `none` rejects. -/
noncomputable def nodeStep (ν : Node) : m (Option (List Node)) := do
  let (pi, π) := ν
  let some (layout, ρ) := Verifier.announced (bytecodeWords prog) π.stream | pure none
  let some s := sizesOf prog layout | pure none
  let some r := stackRoot π | pure none
  let some (ht, w) := stackShape layout ρ | pure none
  let some W := ip.word r | pure none
  if ¬ WellShaped w W then return none
  let root ← treeRootM H ht W
  if digestScalars root ≠ r then return none
  if h : (blindCandidates prog s ρ pi W).Finite then
    let mut kids : List Node := []
    for q in h.toFinset.toList do
      let some t := candidateRun prog s q | return none
      if !(← tableOKWith H (t.blakeRows blakeFree)) then return none
      for c in (LeanVM.Guest.End.decode t.image).witness.children do
        let pc ← statementDigestWith H seed c.statement
        kids := kids ++ [(pc, c.proof)]
    return some kids
  else return none

open Classical in
/-- The closure of the nodes `todo` under `nodeStep`, in at most `fuel` steps (a revisit is a
step); `done` the nodes already checked. A node whose word has no candidate satisfying the
relation has no children: V° on the root, and the children's in-circuit verification, make
such a word improbable (T1). -/
noncomputable def closure : ℕ → List Node → List Node → m Bool
  | _, [], _ => pure true
  | 0, _ :: _, _ => pure false
  | fuel + 1, ν :: todo, done =>
    if ν ∈ done then closure fuel todo done else do
      match ← nodeStep H prog seed ip ν with
      | none => pure false
      | some kids => closure fuel (todo ++ kids) (ν :: done)

open Classical in
/-- **The outer checks without the proof, with the hash `H`** (`OuterChecks°`, design D3): every
DA claim's vector digest is its root's, and the deferred claim's bytecode part holds
(`DeferredClaim.BytecodeHolds`). The matrix part is not checked: V° does not bind the `BLAKE2S`
rows to Flock's R1CS, so honest children hint their matrix values, which the batching carries to
the root. -/
noncomputable def outerChecksWith (s : NodeStatement) : m Bool := do
  let ok ← s.claims.da.allM fun c ↦ do
    pure (decide (Da.toBytes c.2 = (← Da.vectorDigestOfWith H c.1)))
  pure (ok && decide (s.defer.BytecodeHolds (bytecodeWords prog)))

/-- **The idealized verifier V_I** with the hash `H`, on `fuel` nodes: V° on the root statement's
digest under the deployed seed, the outer checks, then the closure from the root. -/
noncomputable def idealVerify (fuel : ℕ) (s : NodeStatement) : m Bool := do
  let seed ← fiatShamirIvWith H (bytecodeWords prog)
  let pi ← statementDigestWith H seed s
  if !(← verifyBlindWith H (bytecodeWords prog) pi ip.proof) then return false
  if !(← outerChecksWith H prog s) then return false
  closure H prog seed ip fuel [(pi, ip.proof)] []

end Verify

/-! ## The honest-signer game -/

/-- A leanXMSS signing request: a leaf index and a message (`LeanXmss.SignRequest`). -/
abbrev XmssRequest : Type := LeanXmss.LeafIndex × LeanXmss.Message

/-- A leanXMSS signing request to honest key `j`. -/
abbrev XmssSignSpec (nx : ℕ) := (Fin nx × XmssRequest) →ₒ Option LeanXmss.Signature

/-- A leanSPHINCS signing request to honest key `j`. -/
abbrev SphincsSignSpec (ns : ℕ) := (Fin ns × Sphincs.Message) →ₒ Option Sphincs.Signature

/-- What the adversary queries: private coins, the hash, the signers. -/
abbrev AdvSpec (nx ns : ℕ) := unifSpec + HashSpec + XmssSignSpec nx + SphincsSignSpec ns

/-- **An adversary of the game**: from the honest public keys, a root statement and an idealized
proof. -/
abbrev GameAdversary (nx ns : ℕ) : Type :=
  (Fin nx → LeanXmss.PublicKey) → (Fin ns → Sphincs.PublicKey) →
    OracleComp (AdvSpec nx ns) (NodeStatement × IdealProof)

/-- What the game queries: coins and the hash. -/
abbrev GameSpec := unifSpec + HashSpec

/-- The signers' state: every forwarded request and its answer, per key (refused requests are not
recorded), and the queries V_I made. -/
structure SignState (nx ns : ℕ) where
  /-- Every forwarded leanXMSS request and its answer, per key. -/
  xlog : Fin nx → List (XmssRequest × Option LeanXmss.Signature)
  /-- Every forwarded leanSPHINCS request and its answer, per key. -/
  slog : Fin ns → List (Sphincs.Message × Option Sphincs.Signature)
  /-- The queries V_I made. -/
  spent : ℕ

/-- The initial state. -/
def SignState.init (nx ns : ℕ) : SignState nx ns := ⟨fun _ ↦ [], fun _ ↦ [], 0⟩

/-- The game's monad: the signers' state over coins and the hash. -/
abbrev GameM (nx ns : ℕ) := StateT (SignState nx ns) (OracleComp GameSpec)

variable {nx ns : ℕ}

/-- **A hash query**, of any party: the adversary, the signers, V_I. -/
def hashQuery (x : Bytes) : GameM nx ns Digest :=
  liftM (liftM (HashSpec.query x) : OracleComp GameSpec Digest)

/-- Coins. -/
def coins {α : Type} (p : ProbComp α) : GameM nx ns α :=
  liftM (liftM p : OracleComp GameSpec α)

/-- A leanXMSS computation run against the hash (`Digest ≃ BitVec 256` by `digestBits`). -/
def xmssRun {α : Type} (oa : OracleComp LeanXmss.HashSpec α) : GameM nx ns α :=
  simulateQ (fun x ↦ digestBits <$> hashQuery x : QueryImpl LeanXmss.HashSpec (GameM nx ns)) oa

/-- A leanSPHINCS computation run against the hash. -/
def sphincsRun {α : Type} (oa : OracleComp Sphincs.HashSpec α) : GameM nx ns α :=
  simulateQ (fun x ↦ digestBits <$> hashQuery x : QueryImpl Sphincs.HashSpec (GameM nx ns)) oa

/-- The honest keys. -/
structure Keys (nx ns : ℕ) [Sphincs.Params] where
  /-- The leanXMSS keys. -/
  xmss : Fin nx → LeanXmss.PublicKey × LeanXmss.Seeded.SecretKey
  /-- The leanSPHINCS keys. -/
  sphincs : Fin ns → Sphincs.PublicKey × Sphincs.Seeded.SecretKey

variable [Sphincs.Params]

/-- **Key generation**: every key from a uniform seed. -/
noncomputable def keygen : GameM nx ns (Keys nx ns) := do
  let xs ← (Vector.replicate nx ()).mapM fun _ ↦ do
    xmssRun (LeanXmss.Seeded.keygenFromSeed (← coins LeanXmss.sampleMasterSeed))
  let ss ← (Vector.replicate ns ()).mapM fun _ ↦ do
    sphincsRun (Sphincs.Seeded.keygenFromSeed (← coins Sphincs.sampleMasterSeed))
  pure ⟨fun j ↦ xs[j], fun j ↦ ss[j]⟩

/-- **The leanXMSS signing oracle** of key `j`: a used leaf refused; otherwise the signer, the
request and its answer recorded. -/
def xmssSign (keys : Keys nx ns) (j : Fin nx) (req : XmssRequest) :
    GameM nx ns (Option LeanXmss.Signature) := do
  if ((← get).xlog j).any (·.1.1 = req.1) then return none
  let σ ← xmssRun (LeanXmss.Seeded.sign (keys.xmss j).2 req.1 req.2 :
    OracleComp LeanXmss.HashSpec _)
  modify fun st ↦ { st with xlog := Function.update st.xlog j (st.xlog j ++ [(req, σ)]) }
  pure σ

/-- **The leanSPHINCS signing oracle** of key `j`: past `signatureLimit` requests refused;
otherwise the signer, the request and its answer recorded. -/
def sphincsSign (keys : Keys nx ns) (j : Fin ns) (msg : Sphincs.Message) :
    GameM nx ns (Option Sphincs.Signature) := do
  if Sphincs.signatureLimit ≤ ((← get).slog j).length then return none
  let σ ← sphincsRun (Sphincs.Seeded.sign (keys.sphincs j).2 msg : OracleComp Sphincs.HashSpec _)
  modify fun st ↦ { st with slog := Function.update st.slog j (st.slog j ++ [(msg, σ)]) }
  pure σ

/-- The adversary's oracles: coins, the hash, the signers. -/
def advImpl (keys : Keys nx ns) : QueryImpl (AdvSpec nx ns) (GameM nx ns) :=
  (((fun n ↦ coins ($ᵗ Fin (n + 1)) : QueryImpl unifSpec (GameM nx ns)) +
      (fun x ↦ hashQuery x : QueryImpl HashSpec (GameM nx ns))) +
    (fun q ↦ xmssSign keys q.1 q.2 : QueryImpl (XmssSignSpec nx) (GameM nx ns))) +
    (fun q ↦ sphincsSign keys q.1 q.2 : QueryImpl (SphincsSignSpec ns) (GameM nx ns))

/-- V_I's hash: a query while fewer than `budget` were made, else rejection. -/
def budgetedQuery (budget : ℕ) (x : Bytes) : OptionT (GameM nx ns) Digest := do
  if budget ≤ (← get).spent then failure
  modify fun st ↦ { st with spent := st.spent + 1 }
  liftM (hashQuery x : GameM nx ns Digest)

/-- What the game outputs: the keys, the adversary's statement and proof, V_I's verdict, and the
signers' final state. -/
structure GameOutcome (nx ns : ℕ) [Sphincs.Params] where
  /-- The honest keys. -/
  keys : Keys nx ns
  /-- The root statement. -/
  statement : NodeStatement
  /-- The idealized proof. -/
  proof : IdealProof
  /-- V_I accepted. -/
  accepted : Bool
  /-- The signers' final state. -/
  state : SignState nx ns

/-- **The game, as an oracle computation**: key generation, the adversary with its oracles,
then V_I on `fuel` nodes with at most `budget` queries, a run past the budget rejected. -/
noncomputable def gameComp (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) :
    OracleComp GameSpec (GameOutcome nx ns) := do
  let (out, st) ← (do
      let keys ← keygen
      let (s, ip) ← simulateQ (advImpl keys)
        (A (fun j ↦ (keys.xmss j).1) (fun j ↦ (keys.sphincs j).1))
      let v ← (idealVerify (budgetedQuery budget) guest ip fuel s).run
      pure (keys, s, ip, v.getD false) : GameM nx ns _).run (SignState.init nx ns)
  pure ⟨out.1, out.2.1, out.2.2.1, out.2.2.2, st⟩

/-- The coins, forwarded. -/
noncomputable def coinImpl : QueryImpl unifSpec (StateT Log ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT Log ProbComp)

/-- **The game**: `gameComp` against one random oracle, lazily sampled over the ordered log of
its fresh queries (`Rom.loggedRO`), from the empty log; the outcome and the final log. -/
noncomputable def game (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) :
    ProbComp (GameOutcome nx ns × Log) :=
  (simulateQ (coinImpl + (Rom.loggedRO : QueryImpl HashSpec (StateT Log ProbComp)))
    (gameComp guest fuel budget A) : StateT Log ProbComp (GameOutcome nx ns)).run []

/-! ## The events -/

/-- **A forgery**: a claim of the root statement for an honest key of its scheme on a message
no request to that key was answered for. -/
def Forged (z : GameOutcome nx ns) : Prop :=
  (∃ j : Fin nx, ∃ msg, ((z.keys.xmss j).1, msg) ∈ z.statement.claims.xmss ∧
    ∀ e ∈ z.state.xlog j, e.1.2 = msg → e.2 = none) ∨
  (∃ j : Fin ns, ∃ msg, ((z.keys.sphincs j).1, msg) ∈ z.statement.claims.sphincs ∧
    ∀ e ∈ z.state.slog j, e.1 = msg → e.2 = none)

/-- **A DA claim backed by the log `ℓ`**: codeword rows (each the Reed-Solomon encoding
`LeanDa.encodeRow` of a payload, of the length `Witness.Opens` asks) whose
commitment, with the padding digests `pc` and `pr`, every hash answered by the log, is the root,
and the root's vector digest, every hash answered by the log, is the claim's. -/
def DaBacked (ℓ : Log) (pc pr : LeanDa.Digest) (c : DaClaim) : Prop :=
  ∃ rows : List (List K), 1 ≤ rows.length ∧ rows.length ≤ LeanDa.maxRows ∧
    (∀ row ∈ rows, row.length = 2 ^ LeanDa.logM ∧
      ∃ p : LeanDa.Payload, (fun b : Fin (2 ^ LeanDa.logM) ↦ row.getD b 0) = LeanDa.encodeRow p) ∧
    Da.commitCodewordsWith (Da.daHash (look ℓ)) pc pr rows = some (Da.toBytes c.1) ∧
    Da.vectorDigestOfWith (look ℓ) c.1 = some (Da.toBytes c.2)

/-- The deployed padding digests: BLAKE2s of a zero cell and of a zero row, which the guest bakes
as constants. -/
def deployedPads : LeanDa.Digest × LeanDa.Digest :=
  (LeanDa.paddingCell Da.blake2s, LeanDa.paddingRow Da.blake2s)

/-- **The adversary wins**: V_I accepts, and the root statement has a forged claim or a DA claim
the oracle's final log `ℓ` does not back. -/
def Breaks (z : GameOutcome nx ns) (ℓ : Log) : Prop :=
  z.accepted = true ∧
    (Forged z ∨ ∃ c ∈ z.statement.claims.da, ¬ DaBacked ℓ deployedPads.1 deployedPads.2 c)

end
end LeanVM.E2E
