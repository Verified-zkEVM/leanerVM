/-
  LeanVM.Guest.Limits

  Where `NodeRel` admits witnesses the deployed guest cannot run: the deployed limits, the
  children's openings agreeing in the guest's Merkle caps, and no zero Fiat-Shamir challenge where
  the guest divides. The hypotheses of the guest's completeness.
-/

module

public import LeanVM.Guest.Hints
public import LeanVM.Protocol.Verifier.DeferredShape

/-!
# The limits of the guest's completeness

`NodeRel bytecode seed s w` (`Spec/Node.lean`) admits witnesses on which the deployed guest
(`crates/rec_aggregation/guests/lean_ethereum.py` at leanVM `3375f7a13`, `G:N` its lines) does
not run to completion. Completeness assumes three hypotheses beside `NodeRel`, each a precise
predicate on the witness:

* **`Limits s w`, the deployed limits**: the guest's fixed capacities and range checks, which the
  Spec does not have (a child's stack log at least `22`, its proof stream at most `8192` scalars,
  at most `16` children, ...; listed at the structure). They are the triage's findings (the
  README's "The guest's triage"): an honest prover within them is never refused, and
  `aggregate_with_stats` refuses to aggregate outside most of them.
* **`CapsAgree bytecode seed w`, the openings agree in the caps**: the guest writes each level's
  Merkle cap once (write-once memory), so two openings of one query step meeting at a node of the
  tree must give it one digest; the Spec checks each opening alone against the root. One tree's
  openings agree; two that disagree at a node give a Keccak-256 collision (the root's
  preimages). Stated, as `B1.Whir.CapsAgree` is for one opening, at every node of the tree, which
  is stronger than the cap levels alone and fails on the same collisions.
* **`NoZeroChallenge bytecode seed w`, no zero challenge where the guest divides** (new at
  `keccak-gkr`): the guest computes `μ = 1/λ` for each WHIR level's batching challenge `λ`
  (`opening_queries`, G:1253) and the basis coefficients `(1 + c)/(c·inv)` for the fold and tail
  challenges `c` (`open_stacked`, G:1560, G:1565), so a zero challenge there makes it reject a
  child the Spec accepts. Stated as: every child's proof is accepted by the deferring verifier
  whose stacked opening also rejects a zero fold, tail or level batching challenge
  (`verifyDeferredNZ`). Each challenge is a squeeze of Keccak-f[1600] (three lanes, `2^192`
  values), so in the random-permutation model an honest child's proof meets one with probability
  about `(number of those challenges)·2^-192`.

`NoZeroChallenge` is the node-level form of `B1.Whir.NoZeroChallenge` (the opening's run from a
sponge state, `B1/Whir/CompleteIface.lean`); `verifyDeferredNZ`'s opening is `whirLevelsNZ`, the
Spec's `whirLevels` with exactly that program's three `require`s (`foldRoundsNZ`,
`tailRoundsNZ`, `lam ≠ 0`).

The coverage table's size (`coverage`) is `Hints.plan`'s, as an honest run lays it out.
-/

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

namespace Limits

/-! ## The deferring verifier refusing a zero challenge where the guest divides -/

/-- `foldRounds` refusing a zero challenge. -/
def foldRoundsNZ : ℕ → WhirState → List E → Prog (WhirState × List E)
  | 0, s, levelFolds => return (s, levelFolds)
  | n + 1, s, levelFolds => do
    let challenge ← Prog.sampleE
    Prog.require (challenge ≠ 0)
    let target := polyEval s.quad challenge
    let quad ← sumcheckRoundPoly 3 target none
    foldRoundsNZ n { s with target, quad, folds := s.folds ++ [challenge] }
      (levelFolds ++ [challenge])

/-- `tailRounds` refusing a zero challenge. -/
def tailRoundsNZ : ℕ → E → List E → Prog (List E × E)
  | 0, target, _ => return ([], target)
  | n + 1, _, quad => do
    let challenge ← Prog.sampleE
    Prog.require (challenge ≠ 0)
    let target := polyEval quad challenge
    if n = 0 then return ([challenge], target)
    else do
      let quad ← sumcheckRoundPoly 3 target none
      let (rest, target) ← tailRoundsNZ n target quad
      return (challenge :: rest, target)

/-- `whirLevels` refusing a zero fold, tail or level batching challenge. -/
def whirLevelsNZ (logN laneFolds : ℕ) (evaluateBasis : List E → E) :
    ℕ → List Whir.Level → WhirState → Prog Unit
  | _, [], _ => Prog.fail
  | index, level :: rest, s => do
    let (s, levelFolds) ← foldRoundsNZ level.fold s []
    let messageLog := logN - s.folds.length
    let (residual, pending) ← match rest with
      | [] => do
        let residual ← Prog.readN (2 ^ messageLog)
        pure (residual, ([] : List (E × List E × (List E → E))))
      | next :: _ => do
        let (height, width) := levelShape messageLog next (3 * 2 ^ next.fold)
        Prog.commitP height width
        let oodPoint ← Prog.sampleN messageLog
        let oodValue ← Prog.readE
        let intro ← sumcheckRoundPoly 3 oodValue none
        pure ([], [(oodValue, intro, fun x ↦ eqEval oodPoint x)])
    Prog.grindP Whir.queryGrindingBits
    let queries ← sampleQueries (messageLog + level.logInvRate) level.queries
    let lam ← Prog.sampleE
    Prog.require (lam ≠ 0)
    let queryWeights := powers lam queries.length
    let words ← Prog.queryP index queries
    let rows : List (List E) :=
      if index = 0 then words.map fun row ↦ row.reverse.map ofK else words.map extRow
    let enforced := enforcedSum rows levelFolds queryWeights
    let intro ← sumcheckRoundPoly 3 enforced none
    let pending := pending ++
      [(enforced, intro, fun x ↦ inducedWeight messageLog queries queryWeights x)]
    let s := glue lam s pending
    match rest with
    | [] => do
      let (tailFolds, target) ← tailRoundsNZ messageLog s.target s.quad
      let point := s.folds ++ tailFolds
      let weight := s.glued.foldl
        (fun weight claim ↦
          weight + claim.scalar * claim.weightAt (s.folds.drop claim.foldStart ++ tailFolds))
        (evaluateBasis (point.drop laneFolds ++ point.take laneFolds))
      let terminal := weight * multilinearEval residual tailFolds
      Prog.require (terminal = target)
    | _ :: _ => whirLevelsNZ logN laneFolds evaluateBasis (index + 1) rest s

/-- `verifyWhir` refusing a zero fold, tail or level batching challenge. -/
def verifyWhirNZ (logN logInvRate : ℕ) (target : E) (evaluateBasis : List E → E) : Prog Unit := do
  let config ← liftOption (deriveConfig logN logInvRate)
  let quad ← sumcheckRoundPoly 3 target none
  whirLevelsNZ logN ((config.head?.map (·.fold)).getD 0) evaluateBasis 0 config
    ⟨target, quad, [], []⟩

/-- `verifyStackedOpening` refusing a zero fold, tail or level batching challenge. -/
def verifyStackedOpeningNZ (stackLog logInvRate : ℕ) (claims : List StackClaim) : Prog Unit := do
  let scales := powers (← Prog.sampleE) claims.length
  verifyWhirNZ stackLog logInvRate (dot scales (claims.map (·.2)))
    fun point ↦ dot scales (claims.map fun c ↦ c.1 point)

/-- `verifyExecution` whose stacked opening refuses a zero fold, tail or level batching
challenge. -/
def verifyExecutionNZ (ev : Evaluations) (bytecode : List K) (publicInput : Digest) :
    Prog Unit := do
  let (layout, logInverseRate) ← readSizes bytecode
  commitStack layout.stackLog logInverseRate
  let bus ← verifyBusBalance ev layout
  let claims ← tablePhase layout bus
  let publicClaims ← publicInputPhase layout publicInput
  let claims := claims ++ publicClaims
  let (claims, keccakPoint, keccakSlices) ← keccakPhase layout claims
  let (ringTarget, ringWeight) ← ringSwitch keccakPoint keccakSlices
  verifyStackedOpeningNZ layout.stackLog logInverseRate
    (ringSwitchClaim layout ringTarget ringWeight :: claims.map (·.onStack layout))

/-- `deferredProgram` whose stacked opening refuses a zero fold, tail or level batching
challenge. -/
def deferredProgramNZ (c : FixedClaims) (bytecode : List K) (publicInput : Digest) :
    Prog Bool := do
  verifyExecutionNZ (.claimed c) bytecode publicInput
  return true

/-- **The deployed deferring verifier refusing a zero challenge where the guest divides**:
`verifyDeferred` with `deferredProgramNZ`. -/
def verifyDeferredNZ (bytecode : List K) (iv publicInput : Digest) (c : FixedClaims)
    (π : Proof) : Bool :=
  Id.run (runProof (m := Id) keccak256 keccakF (deferredProgramNZ c bytecode publicInput)
    (keccakF (seedInput iv publicInput)) π)

/-! ## The query steps of a run, and openings that agree -/

/-- **The query steps of a run** of the compiled verifier (Keccak-256, Keccak-f[1600]): each
`query` step as its tree's height and its positions, each with the opening it consumes. -/
def queriesOf {α : Type} : Prog α → St → List (ℕ × List (ℕ × Opening))
  | .ret _, _ => []
  | .fail, _ => []
  | .read k, s => match s.stream with
    | [] => []
    | x :: xs =>
      queriesOf (k x) { s with sponge := Id.run (absorb keccakF s.sponge x dsObserve), stream := xs }
  | .sample k, s =>
    let (c, sp) := Id.run (squeeze keccakF s.sponge)
    queriesOf (k c) { s with sponge := sp }
  | .grind bits k, s => match s.stream with
    | [] => []
    | n :: xs =>
      let (c, sp) := Id.run (squeeze keccakF (Id.run (absorb keccakF s.sponge n dsPowNonce)))
      if powOk bits n c then queriesOf k { s with sponge := sp, stream := xs } else []
  | .commit height width k, s => match s.stream with
    | x0 :: x1 :: xs =>
      match digestOfScalars (x0, x1) with
      | some root =>
        queriesOf k { s with
          sponge := Id.run (absorb keccakF (Id.run (absorb keccakF s.sponge x0 dsObserve)) x1 dsObserve)
          stream := xs
          roots := s.roots ++ [(root, height, width)] }
      | none => []
    | _ => []
  | .query i ps k, s => match s.roots[i]? with
    | none => []
    | some (root, height, width) =>
      match Id.run (openAll (m := Id) keccak256 root height width ps s.openings) with
      | some (rows, rest) =>
        (height, ps.zip s.openings) :: queriesOf (k rows) { s with openings := rest }
      | none => []

/-- The heap index of the node at level `l` (the leaves at `0`) above the leaf `q` of a tree of
height `depth`. -/
def heapNode (depth q l : ℕ) : ℕ := 2 ^ (depth - l) + q / 2 ^ l

/-- The heap index of the sibling of the node at level `l < depth` above the leaf `q`. -/
def sibNode (depth q l : ℕ) : ℕ := 2 * heapNode depth q (l + 1) + (!q.testBit l).toNat

/-- The digest an opening's climb reaches from `node` at position `q` over `path`. -/
def climbTo (node : Digest) (q : ℕ) (path : List Digest) : Digest :=
  Id.run (climb (m := Id) keccak256 node q path)

/-- **The opening `o` at `q` gives the heap node `v` the digest `d`**: `v` is on its climb, with
the climb's digest there, or is the sibling it carries at a level. -/
def NodeIs (depth : ℕ) (a : ℕ × Opening) (v : ℕ) (d : Digest) : Prop :=
  (∃ l ≤ depth, v = heapNode depth a.1 l ∧ d = climbTo (hashWords a.2.leaf) a.1 (a.2.path.take l)) ∨
    ∃ l < depth, v = sibNode depth a.1 l ∧ d = a.2.path.getD l default

/-- The openings of one query step agree wherever they meet. -/
def BatchAgrees (depth : ℕ) (qs : List (ℕ × Opening)) : Prop :=
  ∀ a ∈ qs, ∀ b ∈ qs, ∀ v d d', NodeIs depth a v d → NodeIs depth b v d' → d = d'

end Limits

open Limits

/-! ## The three hypotheses -/

/-- **No zero challenge where the guest divides** (`G:1253, 1560, 1565`): every child's proof is
accepted by the deferring verifier whose stacked opening also refuses a zero fold challenge, a
zero tail challenge and a zero level batching challenge `λ`, under the node's seed. -/
def NoZeroChallenge (bytecode : List K) (seed : Digest) (w : NodeWitness) : Prop :=
  ∀ c ∈ w.children,
    verifyDeferredNZ bytecode seed (statementDigest seed c.statement) c.fresh c.proof = true

/-- **A child's openings agree in the guest's Merkle caps**: at every query step of each child's
deferring verifier, run under the node's seed, the step's openings agree wherever they meet. One
tree's openings, the honest prover's, agree. -/
def CapsAgree (bytecode : List K) (seed : Digest) (w : NodeWitness) : Prop :=
  ∀ c ∈ w.children, ∀ b ∈ queriesOf
      (deferredProgram c.fresh bytecode (statementDigest seed c.statement)) (Hints.childStart seed c),
    BatchAgrees b.1 b.2

open Hints in
/-- The coverage table's slots (`n_total`, G:4135): each region's declared claims and its
duplicates, as `honestPushes` plans them. -/
def coverage (s : NodeStatement) (w : NodeWitness) : ℕ :=
  let ch := w.children
  s.claims.xmss.length + (plan s.claims.xmss ((direct s.claims.xmss w.xmss).map (·.1))
      (ch.map (·.statement.claims.xmss))).dups.length +
    s.claims.sphincs.length + (plan s.claims.sphincs ((direct s.claims.sphincs w.sphincs).map (·.1))
      (ch.map (·.statement.claims.sphincs))).dups.length +
    s.claims.da.length + (plan s.claims.da ((direct s.claims.da w.da).map (·.1))
      (ch.map (·.statement.claims.da))).dups.length

open Hints in
/-- **The deployed limits** (the triage's findings), where `NodeRel` admits witnesses the guest
cannot run. Implied by these, with `NodeRel`, and so not limits of their own: a child's stack log
at most `28` and rate in `[1, 4]` (`readSizes`), the duplicate DA slots below `258` (G:4127-4129),
every count of `meta` below `2^16` (G:4114-4119), the bus depth at most `32` (G:1630), the tables'
heights at most `28` (G:2010). -/
structure Limits (bytecode : List K) (s : NodeStatement) (w : NodeWitness) : Prop where
  /-- 1. A child's stack log is at least `MU_MIN = 22`: the guest has one opening arm per stack
  log in `[22, 28]` (G:3314-3316); the Spec admits `15`. -/
  stackLog : ∀ c ∈ w.children, ∀ layout r, announced bytecode c.proof.stream = some (layout, r) →
    muMin ≤ layout.stackLog
  /-- 2. A child's proof stream is at most `STREAM_CAP = 8192` scalars (G:3165). -/
  stream : ∀ c ∈ w.children, c.proof.stream.length ≤ streamCap
  /-- 3. At most one DA claim is held directly (G:4121). -/
  directDa : (direct s.claims.da w.da).length ≤ 1
  /-- 4. A claim declared `n` times is held `n` times, by witnesses or by distinct entries of the
  children's lists: each coverage slot is written once (G:3871-3872, 4080-4081, 4262), where
  `NodeRel` lets two equal claims share one holder. -/
  xmssHeld : ∀ x, s.claims.xmss.count x ≤ ((direct s.claims.xmss w.xmss).map (·.1)).count x +
    (w.children.map fun c ↦ c.statement.claims.xmss.count x).sum
  sphincsHeld : ∀ x, s.claims.sphincs.count x ≤ ((direct s.claims.sphincs w.sphincs).map (·.1)).count x +
    (w.children.map fun c ↦ c.statement.claims.sphincs.count x).sum
  daHeld : ∀ x, s.claims.da.count x ≤ ((direct s.claims.da w.da).map (·.1)).count x +
    (w.children.map fun c ↦ c.statement.claims.da.count x).sum
  /-- 5. At most `MAX_RECURSIONS = 16` children (G:4120). -/
  children : w.children.length ≤ 16
  /-- 5. At most `MAX_DA_ROOTS = 16` DA claims in the statement and in each child (G:4126,
  4246). -/
  daRoots : s.claims.da.length ≤ 16 ∧ ∀ c ∈ w.children, c.statement.claims.da.length ≤ 16
  /-- 5. Every child's signature list below `2^16` (G:4233-4234). -/
  lists : ∀ c ∈ w.children, c.statement.claims.xmss.length < 2 ^ 16 ∧
    c.statement.claims.sphincs.length < 2 ^ 16
  /-- 5. The coverage table below `2^16` (G:4135-4136). -/
  coverage : coverage s w < 2 ^ 16
  /-- 6. At least one declared claim (G:4174). -/
  nonempty : 0 < s.claims.xmss.length + s.claims.sphincs.length + s.claims.da.length


/-! ## What `NodeRel` gives of the children's fresh claims -/

/-- **Every child's fresh claim has the bytecode's shape**: the deferring verifier accepts each
child's proof (`NodeRel`), and an accepted proof claims the bytecode at the verifier's own bus
point, `bytecodeLow ++ alphas`, of the bytecode's log-length (`verifyDeferred_shaped`). Not a
hypothesis: `NodeRel` implies it. -/
theorem fresh_shaped_of_nodeRel {bytecode : List K} {seed : Digest} {s : NodeStatement}
    {w : NodeWitness} (h : NodeRel bytecode seed s w) :
    ∀ c ∈ w.children, c.fresh.bytecodePoint.length = Nat.log2 bytecode.length :=
  fun c hc => verifyDeferred_shaped (h.2.1 c hc).2

/-- **At the deployed guest's `2^23` words, every child's fresh point has 23 coordinates**
(B1-f's `FreshShaped w`). -/
theorem fresh_shaped_23 {bytecode : List K} {seed : Digest} {s : NodeStatement}
    {w : NodeWitness} (h : NodeRel bytecode seed s w) (hb : bytecode.length = 2 ^ 23) :
    ∀ c ∈ w.children, c.fresh.bytecodePoint.length = 23 := fun c hc => by
  rw [fresh_shaped_of_nodeRel h c hc, hb, Nat.log2_two_pow]

end
end LeanVM.Guest
