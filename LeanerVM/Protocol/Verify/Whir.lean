/-
  LeanerVM.Protocol.Verify.Whir

  The executable verifier's opening: WHIR's chain walk (fold rounds, commitments, out-of-domain
  samples, grinding, query positions), the Merkle openings of every level against its root, and
  the algebra on them, which replays WHIR's sumcheck and makes its terminal check.
-/

module

public import LeanerVM.Protocol.Verify.Flock
public import LeanerVM.Protocol.Whir.Open
public import LeanerVM.Protocol.Opening

/-!
# WHIR in the verifier

Written from Annex B, Protocol 1 (the oracle reduction `Whir.whirOpen` and its levels,
`LeanerVM.Protocol.Whir.Level` and `Whir.Final`) and transcribed for the stream order from the
pinned leanVM (`a386121f84292f6fa663aaa3e570c15bc0240ea2`): `crates/pcs/src/whir.rs:2046-2330`
(`recursive_verifier_with_basis_succinct`), `:1175-1193` (`sample_queries_ordered`), as the
second verifier writes it out (`python-verifier/verifier.py:900-1086`, `verify_whir`).

**The levels' shapes** (`levelShapes`): the ladder of the stack size and rate; level `i` folds
`ℓ_i` variables, leaving `κ_i`, its word has `2 ^ (κ_i + R_i)` positions, and its Merkle leaves
are `2 ^ ℓ_i` words at level 0 (the stack is `K`-valued), `3 · 2 ^ ℓ_i` after; the level-0
rows store only the `nLanes` committed lanes, the rest of the leaf image being zero.

**The walk** (`walkWhir`): the opening claim's first round polynomial (two wire coefficients of
a quadratic, `c_1` dropped); per level, `ℓ_i` fold rounds, each a challenge and then the next
round polynomial; on a level with a successor, the next root, the `κ_i` out-of-domain
coordinates, the value there and its round polynomial; on the last, the `2 ^ κ_i` residual
values; then the grinding nonce, checked for 17 bits and absorbed (`Reader.checkPow`); the query
positions, `⌊192/(κ_i + R_i)⌋` to a squeeze, low bits first (`walkPositions`); the level's
batching challenge; the query batch's round polynomial; on the last level, the tail rounds, each
a challenge and, but for the last, the next round polynomial. `walkOpenings` reads every level's
pruned opening after the walk and checks it against the level's root at its positions
(`merkleVerifyWith`); openings are not absorbed, so their place in the reader's order changes
no challenge.

**The algebra** (`whirCheck`): the running claim and round polynomial, from the opening claim
on; each fold challenge evaluates the polynomial into the next claim; the query values are the
rows folded by the level's challenges (`Whir.foldRow`; level 0's row is its leaf image in
reverse, one lane a word, a later level's three words a lane), batched by the powers of the
level's challenge; the out-of-domain and query claims are glued on with the scalars `λ, λ²`
(`λ` alone on the last level), their round polynomials likewise (`Whir.batchMessage`), and the
weight becomes the oracle reduction's glued weight (`Whir.foldWeight`, `Whir.gluedWeight`,
`Whir.queryWeight`, the column weights of `lem:colweight`); the terminal check is the final
weight's extension at the tail challenges times the residual's, against the running claim.
The opening weight enters through the lane relayout (`relayoutWeight`), the stack's lanes being
its top coordinates.

**Differences from the Rust.** None in what is accepted. The Rust opens each level's commitment
between the level's batching challenge and its query message (`recv_level_rows`,
`whir.rs:2125, 2214, 2334`); here every opening is checked after the whole walk, which changes no
challenge, since openings are not absorbed. The number and shapes of the openings are checked
before any hash (`openingsOk`); a proof that fails them fails the Rust's opening of the same
level. The terminal weight is the oracle reduction's glued weight evaluated at the tail
challenges, where the Rust evaluates each level's closed form
(`induce_sumcheck_evaluate_at_residual`, `whir.rs:2264-2308`); on the Rust proof of the fixture
the two agree.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics Blake2sHash LeanIsa CompPoly CMlPolynomialEval

@[expose] public section

namespace Verify

/-! ## The levels' shapes -/

/-- A level of the opening as the verifier walks it. -/
structure LevelShape where
  /-- The variables the level folds. -/
  fold : ℕ
  /-- The variables left after its folds. -/
  msgLog : ℕ
  /-- The rate exponent of its word. -/
  rate : ℕ
  /-- The number of positions queried. -/
  queries : ℕ
  /-- The last level: its residual is sent in the clear. -/
  final : Bool
  deriving Inhabited

/-- The levels' shapes of a ladder on `μ` variables. -/
def levelShapes (μ : ℕ) : List Whir.Level → List LevelShape
  | [] => []
  | [l] => [⟨l.fold, μ - l.fold, l.logInvRate, l.queries, true⟩]
  | l :: ls => ⟨l.fold, μ - l.fold, l.logInvRate, l.queries, false⟩ :: levelShapes (μ - l.fold) ls

/-- The words a level's Merkle leaf has: one per lane at level 0, three after. -/
def leafWordsOf (first : Bool) (sh : LevelShape) : ℕ :=
  if first then 2 ^ sh.fold else 3 * 2 ^ sh.fold

/-- The words a level's stored row has: the committed lanes at level 0, the whole leaf after. -/
def rowWordsOf (nLanes : ℕ) (first : Bool) (sh : LevelShape) : ℕ :=
  if first then nLanes else leafWordsOf first sh

/-- The openings have the number and shapes the levels fix, checked before any hash: one phase
per level, at most one row per query, every row of the level's width, and at most as many
siblings as the queries' paths have nodes. -/
def openingsOk (nLanes : ℕ) : Bool → List LevelShape → List PrunedMerklePaths → Bool
  | _, [], [] => true
  | first, sh :: shs, p :: ps =>
    decide (p.leafData.length ≤ sh.queries) &&
      p.leafData.all (·.length = rowWordsOf nLanes first sh) &&
      decide (p.siblingHashes.length ≤ sh.queries * (sh.msgLog + sh.rate)) &&
      openingsOk nLanes false shs ps
  | _, _, _ => false

/-! ## The wire -/

/-- A round of WHIR whose challenge comes first: the challenge, then the wire of the next round
polynomial (empty after the last tail round). -/
structure Fold where
  /-- The challenge. -/
  chal : E
  /-- The next round polynomial's wire coefficients. -/
  wire : List E
  deriving Inhabited

/-- A level of the opening as read. -/
structure WhirLevel where
  /-- The fold rounds. -/
  folds : List Fold
  /-- The next commitment, on a level with a successor. -/
  root : Option Digest
  /-- The out-of-domain point. -/
  ood : List E
  /-- The value at the out-of-domain point. -/
  oodValue : E
  /-- The out-of-domain claim's round polynomial. -/
  oodWire : List E
  /-- The residual, on the last level. -/
  residual : List E
  /-- The grinding nonce. -/
  nonce : E
  /-- The query positions. -/
  positions : List ℕ
  /-- The level's batching challenge. -/
  lam : E
  /-- The query batch's round polynomial. -/
  queryWire : List E
  /-- The tail rounds, on the last level. -/
  tail : List Fold
  deriving Inhabited

/-! ## The walk -/

section Walk

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest)

/-- `n` fold rounds: a challenge, then two wire coefficients. -/
def walkFolds : ℕ → Walk m (List Fold)
  | 0 => pure []
  | n + 1 => do
    let c ← Reader.sample H
    let w ← Reader.nextScalars H 2
    let rest ← walkFolds n
    return ⟨c, w⟩ :: rest

/-- `n` tail rounds: a challenge, then two wire coefficients but after the last. -/
def walkTail : ℕ → Walk m (List Fold)
  | 0 => pure []
  | n + 1 => do
    let c ← Reader.sample H
    let w ← if n = 0 then pure [] else Reader.nextScalars H 2
    let rest ← walkTail n
    return ⟨c, w⟩ :: rest

/-- The integer of a challenge's 192 bits, limb 0 lowest. -/
def chalBits (x : E) : ℕ :=
  (x.limb 0).toBitVec.toNat + 2 ^ 64 * (x.limb 1).toBitVec.toNat +
    2 ^ 128 * (x.limb 2).toBitVec.toNat

/-- `need` positions of `depth` bits: each squeeze gives `⌊192/depth⌋` of them, low bits first
(`sample_queries_ordered`). -/
def walkPositions (depth : ℕ) : (fuel need : ℕ) → Walk m (List ℕ)
  | 0, _ => pure []
  | _, 0 => pure []
  | fuel + 1, need + 1 => do
    let x ← Reader.sample H
    let k := min (192 / depth) (need + 1)
    let ps := (List.range k).map fun c ↦ chalBits x / 2 ^ (c * depth) % 2 ^ depth
    let rest ← walkPositions depth fuel (need + 1 - k)
    return ps ++ rest

/-- A level's reads. -/
def walkLevel (sh : LevelShape) : Walk m WhirLevel := do
  let folds ← walkFolds H sh.fold
  let residual ← if sh.final then Reader.nextScalars H (2 ^ sh.msgLog) else pure []
  let root ← if sh.final then pure none else some <$> Reader.nextRoot H
  let ood ← if sh.final then pure [] else samples H sh.msgLog
  let oodValue ← if sh.final then pure 0 else Reader.nextScalar H
  let oodWire ← if sh.final then pure [] else Reader.nextScalars H 2
  let nonce := ((← get).stream.headD 0)
  Reader.checkPow H Whir.queryGrindingBits
  let positions ← walkPositions H (sh.msgLog + sh.rate) sh.queries sh.queries
  let lam ← Reader.sample H
  let queryWire ← Reader.nextScalars H 2
  let tail ← if sh.final then walkTail H sh.msgLog else pure []
  return ⟨folds, root, ood, oodValue, oodWire, residual, nonce, positions, lam, queryWire, tail⟩

/-- The levels' reads. -/
def walkLevels : List LevelShape → Walk m (List WhirLevel)
  | [] => pure []
  | sh :: shs => do
    let l ← walkLevel H sh
    let ls ← walkLevels shs
    return l :: ls

/-- The opening's reads: the first round polynomial's wire, then the levels. -/
def walkWhir (shs : List LevelShape) : Walk m (List E × List WhirLevel) := do
  let first ← Reader.nextScalars H 2
  let levels ← walkLevels H shs
  return (first, levels)

/-- Every level's pruned opening, checked against its root at its positions: the commitment
root at level 0, the root the previous level sent after. The rows, level by level, in query
order. -/
def walkOpenings (nLanes : ℕ) : Bool → Digest → List LevelShape → List WhirLevel →
    Walk m (List (List (List K)))
  | first, root, sh :: shs, l :: ls => do
    let rows ← Reader.nextOpening (merkleVerifyWith H root (sh.msgLog + sh.rate)
      (rowWordsOf nLanes first sh) (leafWordsOf first sh) l.positions)
    let rest ← walkOpenings nLanes false (l.root.getD root) shs ls
    return rows :: rest
  | _, _, _, _ => pure []

end Walk

/-! ## The algebra -/

/-- A weight on `n` variables read on `n'`, when `n = n'`. -/
def castWeight {n n' : ℕ} (h : n = n') (W : Weight E n) : Weight E n' := h ▸ W

/-- Fold rounds replayed from a claim and its round polynomial: each challenge evaluates the
polynomial into the next claim, whose round polynomial is decoded from the wire when there is
one. The final claim and polynomial and the challenges. -/
def replayFolds : E → Vector E 3 → List Fold → Option (E × Vector E 3 × List E)
  | claim, quad, [] => some (claim, quad, [])
  | _, quad, f :: fs => do
    let claim := RoundPoly.eval quad f.chal
    let quad ← if f.wire = [] then pure quad else RoundPoly.decode 2 claim none f.wire
    let (c, q, cs) ← replayFolds claim quad fs
    return (c, q, f.chal :: cs)

/-- A stored row's lanes as elements of `E`: level 0's leaf image in reverse, one word a lane;
a later level's three words a lane. -/
def laneRow (first : Bool) (ℓ : ℕ) (image : List K) : Option (Vector E (2 ^ ℓ)) :=
  if first then vec? (2 ^ ℓ) (image.reverse.map ofK)
  else vec? (2 ^ ℓ) ((List.range (2 ^ ℓ)).map fun i ↦
    E.ofLimbs (image.getD (3 * i) 0) (image.getD (3 * i + 1) 0) (image.getD (3 * i + 2) 0))

/-- The positions as indices of a word of `2 ^ b` positions. -/
def positionsOf (t b : ℕ) (ps : List ℕ) : Fin t → Fin (2 ^ b) :=
  fun q ↦ ⟨ps.getD q 0 % 2 ^ b, Nat.mod_lt _ (Nat.two_pow_pos b)⟩

/-- WHIR's algebra from a level on: the running claim, its round polynomial and the weight on the
level's `n` variables, the levels' shapes, wires and rows. -/
def whirLevels : Bool → (n : ℕ) → Weight E n → E → Vector E 3 → List LevelShape →
    List WhirLevel → List (List (List K)) → Bool
  | first, n, W, claim, quad, sh :: shs, l :: ls, rows :: rs =>
    match replayFolds claim quad l.folds with
    | none => false
    | some (claim, quad, r) =>
      if h : sh.fold + sh.msgLog = n ∧ r.length = sh.fold ∧ rows.length = sh.queries then
        let rv : Vector E sh.fold := ⟨r.toArray, by simpa using h.2.1⟩
        let W' := Whir.foldWeight (castWeight h.1.symm W) rv
        let pos := positionsOf sh.queries (sh.msgLog + sh.rate) l.positions
        match (rows.mapM (laneRow first sh.fold)) with
        | none => false
        | some lanes =>
          let cq : Fin sh.queries → E :=
            fun q ↦ Whir.foldRow rv (lanes.getD q (Vector.replicate _ 0))
          let enforced := powerBatch cq l.lam
          match RoundPoly.decode 2 enforced none l.queryWire with
          | none => false
          | some p3 =>
            if sh.final then
              let claim := claim + l.lam * enforced
              let quad := Whir.batchMessage ![quad, p3] l.lam
              let W'' := Weight.batch ![W', Whir.queryWeight sh.msgLog sh.rate pos l.lam] l.lam
              match replayFolds claim quad l.tail, vec? (2 ^ sh.msgLog) l.residual with
              | some (claim, _, tail), some f =>
                match vec? sh.msgLog tail with
                | some t => decide (W''.mle t * evalMle f t = claim)
                | none => false
              | _, _ => false
            else
              match vec? sh.msgLog l.ood, RoundPoly.decode 2 l.oodValue none l.oodWire with
              | some z, some p2 =>
                whirLevels false sh.msgLog (Whir.gluedWeight W' z pos l.lam)
                  (powerBatch ![claim, l.oodValue, enforced] l.lam)
                  (Whir.batchMessage ![quad, p2, p3] l.lam) shs ls rs
              | _, _ => false
      else false
  | _, _, _, _, _, _, _, _ => false

/-- WHIR's algebra for an opening claim `⟨W, f⟩ = target` on the `μ`-variable stack: the first
round polynomial decoded against the target, the stack's lanes moved to the low coordinates, and
the levels. -/
def whirCheck (μ : ℕ) (shs : List LevelShape) (W : Weight E μ) (target : E) (first : List E)
    (ls : List WhirLevel) (rows : List (List (List K))) : Bool :=
  match shs, RoundPoly.decode 2 target none first with
  | sh :: _, some quad =>
    if h : (μ - sh.fold) + sh.fold = μ then
      whirLevels true (sh.fold + (μ - sh.fold)) (relayoutWeight (castWeight h.symm W)) target
        quad shs ls rows
    else false
  | _, _ => false

end Verify

end
end LeanerVM.Protocol
