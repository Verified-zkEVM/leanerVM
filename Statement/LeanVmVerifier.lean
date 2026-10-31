module

public import Statement.LeanIsa
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The leanVM verifier

Transcribed from `python-verifier/verifier.py` at the pin (`../leanvm-rev`); every citation
`verifier.py:N` is a line of that file, and the sections follow the Python's: the WHIR constants
(Part 1), the transcript (Part 2: a program `Prog` of a small language, which `runProof` reads on a
proof over a permutation `F : KeccakState → m KeccakState` in any monad `m`, Keccak-256 the sponge
over `F`, `keccak256With F`), and the verifier (Part 3), ending with
`verifyWith F bytecode publicInput proof`.

The verifier takes the value of the polynomial the statement fixes (the bytecode's multilinear
extension) from a parameter `ev : List K → List E → Prog E`. The deployed verifier computes it. The deferring
verifier (`verifyDeferred`), which has no counterpart in the Python, takes it from a claim, as an
aggregate's in-circuit verifier of its children does
(`crates/rec_aggregation/guests/lean_ethereum.py`, `verify_sub`).
-/

@[expose] public section

/-! # Part 1: the constants

### The WHIR parameters

The constants are transcribed from `crates/pcs/src/whir_config.rs:38-86`, the ladder geometry from
its `derive_ladder` and `derive_ladder_shape` (`:252-301`), the stacking window from
`crates/leanvm_core/src/pcs.rs:49-51`, and the query counts from `verifier.py:1019-1054`
(`WHIR_QUERIES`, `derive_config`), which the portable Rust verifier carries verbatim
(`crates/verifier/src/whir.rs:10-56`). The specification describes the protocol these
parameters instantiate (Annex B, Protocol B.1, `doc/leanvm/body/b-polynomial-commitment-scheme.tex`)
and gives no numbers.

An opening of a stack of `2^μ` elements of `K` at rate `2^-R` runs a *ladder* of levels. Level 0
folds `initialFold = 6` variables; every later level folds `subsequentFold = 4`, or what remains,
until at most `residualMaxLog = 5` variables remain, which are sent in the clear. The rate
exponent of a level is the previous one plus the previous fold minus a domain reduction,
`initialReduction = 3` after level 0 and `subsequentReduction = 1` after every later level. Each
level opens `queries` positions after `queryGrindingBits = 17` bits of grinding; from level 1 on,
one out-of-domain sample binds the level's commitment (`whir_config.rs:107-114`;
`verifier.py:1148-1154`).

The query counts are the Rust's *output*, not its derivation: `optimize_johnson_level`
(`whir_config.rs:607-675`) minimises the queries of each level subject to the 128-bit
round-by-round targets of Annex B's Theorem B.2 under a floating-point MCA formula
(`paper_thm_ca_johnson_log_a`, `whir_config.rs:431-447`), and this module does not restate that
search. The table is the one the Python verifier carries, indexed by rate exponent `1..4` and
stack size `15..28`; outside that window `ladder` is `none`, as both verifiers reject
(`validate_log_inv_rate`, `whir_config.rs:48-56`; `verifier.py:1042`). `ladder` takes the stack
size `μ`, as the Python `derive_config` does (the Rust API takes `m = μ + LOG_PACKING`,
`crates/pcs/src/pack.rs:5`), and the rate exponent is announced with the sizes.
-/

namespace LeanVM.Parameters.Whir

/-- Variables folded at level 0: the lane fold (`INITIAL_FOLDING_FACTOR`, `whir_config.rs:67`). -/
def initialFold : ℕ := 6

/-- Variables folded at every later level (`SUBSEQUENT_FOLDING_FACTOR`, `whir_config.rs:68`). -/
def subsequentFold : ℕ := 4

/-- Bits the Reed-Solomon domain shrinks by after level 0, so that the rate exponent rises by
`initialFold - initialReduction` (`RS_DOMAIN_INITIAL_REDUCTION_FACTOR`, `whir_config.rs:73`). -/
def initialReduction : ℕ := 3

/-- Bits the domain shrinks by after every later level (`RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR`,
`whir_config.rs:78`). -/
def subsequentReduction : ℕ := 1

/-- Folding stops once at most this many variables remain; the residual multilinear is sent in
the clear (`RESIDUAL_MAX_LOG`, `whir_config.rs:86`). -/
def residualMaxLog : ℕ := 5

/-- Grinding bits before each level's query positions are sampled (`QUERY_GRINDING_BITS`,
`whir_config.rs:60`). -/
def queryGrindingBits : ℕ := 17

/-- The smallest stack the PCS commits, a smaller witness padded up to it: `MIN_MU`
(`pcs.rs:49`; `MIN_STACKED_LOG`, `verifier.py:1026`). -/
def minLogStack : ℕ := 15

/-- The largest stack the PCS commits: `MAX_MU` (`pcs.rs:51`; `MAX_STACKED_LOG`,
`verifier.py:1027`). -/
def maxLogStack : ℕ := 28

/-- The smallest rate exponent of level 0 (`MIN_LOG_INV_RATE`, `whir_config.rs:44`). -/
def minLogInvRate : ℕ := 1

/-- The largest rate exponent of level 0 (`MAX_LOG_INV_RATE`, `whir_config.rs:45`). -/
def maxLogInvRate : ℕ := 4

/-- One level of an opening: the number of sumcheck rounds it folds (`ℓ_i`), the rate exponent
of the code its commitment is in (`R_i`), and the number of positions queried (`t_i`), in the
notation of Annex B. -/
structure Level where
  fold : ℕ
  logInvRate : ℕ
  queries : ℕ
  deriving DecidableEq

/-- The levels after the first, as pairs (fold, rate exponent): while more than `residualMaxLog`
variables remain, fold `subsequentFold` of them (or all that remain) at the rate exponent the
previous level's fold and the pending domain reduction give (`derive_ladder`,
`whir_config.rs:252-289`, with `derive_ladder_shape`'s rate rule, `:292-301`). `fuel` bounds the
recursion; every level folds at least one variable, so `remaining` fuel is enough. -/
def levelsFrom : (fuel remaining prevFold prevRate reduction : ℕ) → List (ℕ × ℕ)
  | 0, _, _, _, _ => []
  | fuel + 1, remaining, prevFold, prevRate, reduction =>
    if remaining ≤ residualMaxLog then []
    else
      let rate := prevRate + prevFold - reduction
      let fold := min subsequentFold remaining
      (fold, rate) :: levelsFrom fuel (remaining - fold) fold rate subsequentReduction

/-- The ladder geometry of a `μ`-variable stack at rate exponent `logInvRate`: level 0 folds
`initialFold` at that rate, then `levelsFrom` (`derive_config`, `verifier.py:1039-1054`). -/
def shape (μ logInvRate : ℕ) : List (ℕ × ℕ) :=
  (initialFold, logInvRate) ::
    levelsFrom μ (μ - initialFold) initialFold logInvRate initialReduction

/-- The query counts `WHIR_QUERIES` of `verifier.py:1029`, verbatim: row `R - 1` for the rate
exponent `R`, entry `μ - 15` for the stack size `μ`, one count per level. -/
def queryTable : List (List (List ℕ)) := [
  [[222, 55], [223, 56, 30], [223, 56, 31], [223, 56, 32], [223, 56, 32], [223, 56, 32, 22],
   [223, 56, 32, 22], [224, 56, 32, 23], [224, 56, 32, 23], [224, 56, 32, 23, 17],
   [224, 56, 32, 23, 17], [224, 56, 32, 23, 18], [225, 56, 32, 23, 18], [225, 56, 32, 23, 18, 14]],
  [[111, 45], [112, 45, 27], [112, 45, 28], [112, 45, 28], [112, 45, 28], [112, 45, 28, 20],
   [112, 45, 28, 20], [112, 45, 28, 21], [112, 45, 28, 21], [112, 45, 28, 21, 16],
   [112, 45, 28, 21, 16], [112, 45, 28, 21, 16], [112, 45, 28, 21, 16], [112, 45, 28, 21, 16, 13]],
  [[75, 37], [75, 37, 24], [75, 37, 25], [75, 38, 25], [75, 38, 25], [75, 38, 25, 18],
   [75, 38, 25, 19], [75, 38, 25, 19], [75, 38, 25, 19], [75, 38, 25, 19, 15],
   [75, 38, 25, 19, 15], [75, 38, 25, 19, 15], [75, 38, 25, 19, 15], [75, 38, 25, 19, 15, 13]],
  [[56, 32], [56, 32, 22], [56, 32, 22], [56, 32, 23], [56, 32, 23], [56, 32, 23, 17],
   [56, 32, 23, 17], [56, 32, 23, 18], [56, 32, 23, 18], [56, 32, 23, 18, 14],
   [56, 32, 23, 18, 14], [56, 32, 23, 18, 14], [56, 32, 23, 18, 15], [56, 32, 23, 18, 15, 12]]]

/-- The window the parameters are defined on: the stacking window and the rate range
(`verifier.py:1042`; `crates/verifier/src/whir.rs:33-36`; `whir_config.rs:48-56` the rate). -/
def Admissible (μ logInvRate : ℕ) : Prop :=
  minLogStack ≤ μ ∧ μ ≤ maxLogStack ∧ minLogInvRate ≤ logInvRate ∧ logInvRate ≤ maxLogInvRate

instance {μ logInvRate : ℕ} : Decidable (Admissible μ logInvRate) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The ladder of an admissible stack size and rate (`derive_config(log_n, log_inv_rate)`,
`verifier.py:1039-1054`): the geometry of `shape` paired with the
tabulated query counts, level by level. `none` outside the window, and `none` if the table did
not have one count per level (`verifier.py:1053`), so that no level is silently dropped. -/
def ladder (μ logInvRate : ℕ) : Option (List Level) :=
  if Admissible μ logInvRate then
    let geometry := shape μ logInvRate
    let queries := (queryTable.getD (logInvRate - minLogInvRate) []).getD (μ - minLogStack) []
    if geometry.length = queries.length then
      some (List.zipWith (fun (g : ℕ × ℕ) q ↦ ⟨g.1, g.2, q⟩) geometry queries)
    else none
  else none

end LeanVM.Parameters.Whir

/-! # Part 2: the transcript

The Python verifier touches the proof through five operations of its `Transcript`
(`verifier.py:336-458`), and computes everything else from their results; `Prog α` is the free
monad over them, run (`run`, `runProof`) as the deployed non-interactive verifier: the challenges
squeezed out of a duplex sponge and the rows authenticated by Merkle paths.

The sponge is the Rust's (`crates/verifier/src/transcript.rs:34-91`, `Sponge`; the prover's
`crates/fiat_shamir/src/lib.rs`): a duplex over Keccak-f[1600] in overwrite mode, the rate lanes
`0..16`, the capacity lanes `16..25`, and up to four absorbed scalars waiting, each with a tag,
`1` for a scalar the prover sent (`DS_OBSERVE`) and `4` for a proof-of-work nonce
(`DS_POW_NONCE`). A permutation writes waiting scalar `i` over lanes `4i..4i+4` (its three limbs,
then its tag), zeroes the rest of the rate, keeps the capacity, and empties the queue; absorbing a
fifth scalar permutes the four waiting first. Merkle openings come from a separate channel that
the sponge does not absorb: the leaf's words, hashed as bytes, then one sibling per level, the
position's bit at the level choosing the side. The sponge starts at Keccak-f of the IV's and the
public input's words, the other lanes zero (`Transcript.__init__`, `verifier.py:379-384`).

**Deviation from the Python verifier.** The Python reads the Merkle openings from one byte string,
and checks the leaf's width and the path's height implicitly by reading exactly that many bytes;
`Proof.openings` is that string already cut into leaves and paths. A byte string that does not cut
into the lengths the verifier asks for is rejected by the Python, and has no `Proof` here; nothing
else differs.
-/

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash

/-- The verifier language: a program returns a value of type `α` after reading scalars,
sampling challenges, checking proofs of work, reading commitments and opening rows, or fails. -/
inductive Prog (α : Type) : Type where
  | ret (a : α)
  | fail
  /-- Read the next prover scalar, absorbed into the sponge (`next_scalar`). -/
  | read (k : E → Prog α)
  /-- Sample a challenge, squeezed from the sponge (`sample`). -/
  | sample (k : E → Prog α)
  /-- Check a proof of work of `bits` bits, the nonce read and absorbed (`grind_check`). -/
  | grind (bits : ℕ) (k : Prog α)
  /-- Read a Merkle root as two scalars (`Digest.from_halves(*next_scalars(2))`), the committed
  matrix being `2^height` rows of `width` words. -/
  | commit (height width : ℕ) (k : Prog α)
  /-- Open rows of the `i`-th commitment at `positions`, each with its authentication path
  (`merkle`); continue with the rows. -/
  | query (i : ℕ) (positions : List ℕ) (k : List (List K) → Prog α)

namespace Prog

variable {α β γ : Type}

/-- Sequencing. -/
def bind : Prog α → (α → Prog β) → Prog β
  | ret a, f => f a
  | fail, _ => fail
  | read k, f => read fun x ↦ (k x).bind f
  | sample k, f => sample fun x ↦ (k x).bind f
  | grind b k, f => grind b (k.bind f)
  | commit h w k, f => commit h w (k.bind f)
  | query i ps k, f => query i ps fun r ↦ (k r).bind f

instance : Monad Prog where
  pure := ret
  bind := bind

/-- Read one prover scalar. -/
def readScalar : Prog E := read ret

/-- Read `n` prover scalars, in order. -/
def readScalars : ℕ → Prog (List E)
  | 0 => ret []
  | n + 1 => do
    let x ← readScalar
    let xs ← readScalars n
    return x :: xs

/-- Sample one challenge. -/
def sampleChallenge : Prog E := sample ret

/-- Sample `n` challenges, in order. -/
def sampleChallenges : ℕ → Prog (List E)
  | 0 => ret []
  | n + 1 => do
    let x ← sampleChallenge
    let xs ← sampleChallenges n
    return x :: xs

/-- Check a proof of work of `bits` bits. -/
def grindProofOfWork (bits : ℕ) : Prog Unit := grind bits (ret ())

/-- Read a commitment to a matrix of `2^height` rows of `width` words. -/
def readCommitment (height width : ℕ) : Prog Unit := commit height width (ret ())

/-- Open rows of the `i`-th commitment. -/
def queryOpenings (i : ℕ) (positions : List ℕ) : Prog (List (List K)) := query i positions ret

/-- Reject unless `c` holds (the Python verifier's `require`). -/
def require (c : Prop) [Decidable c] : Prog Unit := if c then ret () else fail

end Prog

/-- Byte strings, the hash's inputs. -/
abbrev Bytes : Type := List UInt8

/-! ## The sponge (`verifier.py:348-401`) -/

/-- `DS_OBSERVE`: the tag of a scalar the prover sent (`verifier.py:354`). -/
def dsObserve : ℕ := 1

/-- `DS_POW_NONCE`: the tag of a proof-of-work nonce (`verifier.py:355`). -/
def dsPowNonce : ℕ := 4

/-- `RATE_SCALARS`: the scalars that wait to be absorbed, four lanes each (`verifier.py:356`). -/
def rateScalars : ℕ := 4

/-- The duplex sponge: the Keccak state, and the scalars waiting to be absorbed (at most
`rateScalars`), each with its tag (`Transcript.state`, `Transcript.pending`). -/
structure Sponge where
  state : KeccakState
  pending : List (E × ℕ)

/-- The rate lanes of the waiting scalars: each its three limbs, then its tag
(`verifier.py:387`). -/
def pendingLanes (pending : List (E × ℕ)) : List UInt64 :=
  pending.flatMap fun (x, tag) ↦ [(x.limb 0).lane, (x.limb 1).lane, (x.limb 2).lane, tag.toUInt64]

/-- The input of a permutation: the waiting scalars' lanes, zeros up to lane `16`, then the
capacity, lanes `16..25` of the state (`_duplex`, `verifier.py:386-389`). -/
def duplexInput (sp : Sponge) : KeccakState :=
  Vector.ofFn fun i ↦
    if i.val < 16 then (pendingLanes sp.pending).getD i 0 else Keccak.lane sp.state i

/-- The challenge squeezed into a state: its first three lanes (`sample`, `verifier.py:401`). -/
def challengeOf (state : KeccakState) : E :=
  E.ofLimbs (K.ofLane (Keccak.lane state 0)) (K.ofLane (Keccak.lane state 1))
    (K.ofLane (Keccak.lane state 2))

/-- The proof-of-work predicate on the challenge sampled after the nonce: at `bits = 0` the nonce
is `0`; otherwise the low `bits` bits of the challenge's first limb are zero
(`verifier.py:424`). -/
def powOk (bits : ℕ) (nonce challenge : E) : Bool :=
  if bits = 0 then decide (nonce.limb 0 = 0 ∧ nonce.limb 1 = 0 ∧ nonce.limb 2 = 0)
  else decide ((challenge.limb 0).lane.toNat % 2 ^ bits = 0)

/-- The initial state's input: the IV's four words, the public input's four words, then zeros
(`Transcript.__init__`, `verifier.py:381`). -/
def seedInput (iv publicInput : Digest) : KeccakState :=
  Vector.ofFn fun i ↦
    if h : i.val < 4 then iv[i.val] else if h' : i.val < 8 then publicInput[i.val - 4] else 0

/-! ## Proofs and the run -/

/-- One Merkle opening: the leaf's words and the siblings from the leaf up. -/
structure Opening where
  leaf : List K
  path : List Digest

/-- A proof: the scalar stream and the Merkle openings, in the order the verifier reads them
(`verifier.py:336-345`). -/
structure Proof where
  stream : List E
  openings : List Opening

/-- The compiled verifier's state: the sponge, the scalars and openings not yet read, and the
roots read so far, each with its height and width. -/
structure ProgState where
  sponge : Sponge
  stream : List E
  openings : List Opening
  roots : List (Digest × ℕ × ℕ)

section Run

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- A permutation: the waiting scalars over the rate, the capacity kept, then Keccak-f; the queue
empties (`_duplex`, `verifier.py:386-389`). -/
def duplex (sp : Sponge) : m Sponge := do
  let state ← F (duplexInput sp)
  pure ⟨state, []⟩

/-- Absorb a scalar with a tag: a full queue is permuted first (`_absorb`,
`verifier.py:391-394`). -/
def absorb (sp : Sponge) (x : E) (tag : ℕ) : m Sponge := do
  let sp ← if sp.pending.length = rateScalars then duplex F sp else pure sp
  pure { sp with pending := sp.pending ++ [(x, tag)] }

/-- Squeeze a challenge: a permutation, then the new state's first three lanes (`sample`,
`verifier.py:399-401`). -/
def squeeze (sp : Sponge) : m (E × Sponge) := do
  let sp ← duplex F sp
  pure (challengeOf sp.state, sp)

/-- Climb a Merkle path from `node` at position `q`: at each level the position's low bit says
whether `node` is the left child (`verifier.py:439-442`). -/
def climb : Digest → ℕ → List Digest → m Digest
  | node, _, [] => pure node
  | node, q, s :: ss => do
    let parent ← if q % 2 = 0 then keccak256With F (digestBytes node ++ digestBytes s)
      else keccak256With F (digestBytes s ++ digestBytes node)
    climb parent (q / 2) ss

/-- Check one opening against a root of the given shape at position `q`
(`verifier.py:436-443`). -/
def openOne (root : Digest) (height width q : ℕ) (o : Opening) : m Bool :=
  if o.leaf.length = width ∧ o.path.length = height then do
    let leafDigest ← keccak256With F (o.leaf.flatMap kBytes)
    let top ← climb F leafDigest q o.path
    pure (decide (top.toList = root.toList))
  else pure false

/-- Open every position in order, consuming one opening each; the leaves, and the openings
left. -/
def openAll (root : Digest) (height width : ℕ) :
    List ℕ → List Opening → m (Option (List (List K) × List Opening))
  | [], os => pure (some ([], os))
  | _ :: _, [] => pure none
  | q :: qs, o :: os => do
    if ← openOne F root height width q o then
      let rest ← openAll root height width qs os
      pure (rest.map fun r ↦ (o.leaf :: r.1, r.2))
    else pure none

/-- The compiled reading of a program: run it on the state, every challenge squeezed out of the
sponge and every opening authenticated; `none` on rejection. -/
def run {α : Type} : Prog α → ProgState → m (Option (α × ProgState))
  | .ret a, s => pure (some (a, s))
  | .fail, _ => pure none
  | .read k, s => match s.stream with
    | [] => pure none
    | x :: xs => do
      let sp ← absorb F s.sponge x dsObserve
      run (k x) { s with sponge := sp, stream := xs }
  | .sample k, s => do
    let (c, sp) ← squeeze F s.sponge
    run (k c) { s with sponge := sp }
  | .grind bits k, s => match s.stream with
    | [] => pure none
    | n :: xs => do
      let sp ← absorb F s.sponge n dsPowNonce
      let (c, sp) ← squeeze F sp
      if powOk bits n c then run k { s with sponge := sp, stream := xs } else pure none
  | .commit height width k, s => match s.stream with
    | x0 :: x1 :: xs => do
      let sp ← absorb F s.sponge x0 dsObserve
      let sp ← absorb F sp x1 dsObserve
      match digestOfScalars (x0, x1) with
      | some root =>
        run k { s with sponge := sp, stream := xs, roots := s.roots ++ [(root, height, width)] }
      | none => pure none
    | _ => pure none
  | .query i ps k, s => match s.roots[i]? with
    | none => pure none
    | some (root, height, width) => do
      match ← openAll F root height width ps s.openings with
      | some (rows, rest) => run (k rows) { s with openings := rest }
      | none => pure none

/-- Run a program on a proof from a seed state, and accept when it returns `true` with the
stream and the openings fully consumed (`verifier.py:456-458`, `finish`). -/
def runProof (P : Prog Bool) (seed : KeccakState) (π : Proof) : m Bool := do
  match ← run F P ⟨⟨seed, []⟩, π.stream, π.openings, []⟩ with
  | some (true, s) => pure (s.stream.isEmpty && s.openings.isEmpty)
  | _ => pure false

end Run

/-- A run with every permutation answered by `default`, for the steps that only read scalars: what
they read does not depend on the sponge. -/
def runPure {α : Type} (P : Prog α) (s : ProgState) : Option (α × ProgState) :=
  Id.run (run (m := Id) (fun _ ↦ default) P s)

end LeanVM.Protocol.Compile

/-! # Part 3: the verifier -/

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters hiding gpow
open LeanVM.Semantics

/-!
## Verifier arithmetic (`verifier.py:179-331`)

Every function has the Python's name in `lowerCamelCase` and computes the same value on the inputs
the verifier gives it; the products and sums are taken in the Python's order where it is visible
(`foldl` from `1` or `0`), although `E` is a field and the order does not change a value. The
Python's `E(n)` for an integer `n < 2^64` is `eOfNat n`: the natural-number cast of `E` is the
characteristic-two one (`(2 : E) = 0`) and is never used for a wire integer. A `K` value that the
Python lifts into `E` (`E.lift`) is `ofK`.

**Preconditions the Python checks and the verifier always meets.** `multilinear_eval` requires a
table of `2^|point|` entries and `eq_eval`/`dot` zip strictly. At every call site of the verifier
the lengths agree by construction (the table sizes are `2^k` for the `k` coordinates the caller
passes), so these functions are total here: an excess entry is ignored, as `zip` ignores it.
-/

/-- The Python `E(n)`: the 64-bit word `n` in limb `0` (`verifier.py:97-100`). -/
def eOfNat (n : ℕ) : E := ofK (K.ofBits n)

/-- The integer value of a `K` word (`K.__index__`). -/
def kToNat (a : K) : ℕ := a.toBitVec.toNat

/-- `int(e)`: the three limbs of `e` as one 192-bit integer, limb `0` lowest
(`verifier.py:124-125`). -/
def eToNat (e : E) : ℕ :=
  kToNat (e.limb 0) + 2 ^ 64 * kToNat (e.limb 1) + 2 ^ 128 * kToNat (e.limb 2)

/-- `GEN = E(2)`, the generator `x` whose powers index the bytecode and the memory
(`verifier.py:181`): `Field.lean`'s `g` in limb `0`. -/
def gen : E := eOfNat 2

/-- `_gpow(index) = GEN ** index` (`verifier.py:724-725`): `Parameters.gpow index`, the same
power in `K`, in limb `0` (this file opens `Parameters` without its `gpow`). -/
def gpow (index : ℕ) : E := gen ^ index

/-- `E.sum(values)`: the sum from `ZERO`, left to right (`verifier.py:120-122`). -/
def sumE (values : List E) : E := values.foldl (· + ·) 0

/-- `reduce(mul, values)` with the product of the empty list `1`. -/
def prodE (values : List E) : E := values.foldl (· * ·) 1

/-- `acc, acc·base, acc·base², …`, `count` terms. -/
def powersFrom (acc base : E) : ℕ → List E
  | 0 => []
  | count + 1 => acc :: powersFrom (acc * base) base count

/-- `powers(base, count) = [1, base, base², …]`, `count` terms (`verifier.py:184-186`). -/
def powers (base : E) (count : ℕ) : List E := powersFrom 1 base count

/-- `eq_kernel(point)`: the `2^|point|` equality weights, the first coordinate the lowest bit
(`verifier.py:242-246`). -/
def eqKernel (point : List E) : List E :=
  point.foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) [1]

/-- One fold of `multilinear_eval`: adjacent pairs `(a, b)` become `a·(1 + r) + b·r`. -/
def foldPairs (r : E) : List E → List E
  | a :: b :: rest => (a * (1 + r) + b * r) :: foldPairs r rest
  | _ => []

/-- `multilinear_eval(mle, point)`: the multilinear extension of the table at the point, the
first coordinate folding adjacent entries (`verifier.py:249-254`). A table of the wrong size, which
the Python rejects, never reaches it (see the module note); `0` for an empty result. -/
def multilinearEval (mle point : List E) : E :=
  (point.foldl (fun cur r ↦ foldPairs r cur) mle).headD 0

/-- Python's `int.bit_length` on a natural number. -/
def bitLength (n : ℕ) : ℕ := if n = 0 then 0 else Nat.log2 n + 1

/-- `log2_ceil(value) = (max(value, 1) - 1).bit_length()` (`verifier.py:257-258`): `0` at
`value = 0`, the height of a table with no row. -/
def log2Ceil (value : ℕ) : ℕ := bitLength (value - 1)

/-- `log2_strict(value)`: the exponent of a power of two, `none` otherwise
(`verifier.py:261-263`). -/
def log2Strict (value : ℕ) : Option ℕ :=
  if 0 < value ∧ value &&& (value - 1) = 0 then some (bitLength value - 1) else none

/-- `eq_eval(left, right) = Π (1 + x + y)` (`verifier.py:266-270`). -/
def eqEval (left right : List E) : E :=
  (List.zipWith (fun x z ↦ 1 + x + z) left right).foldl (· * ·) 1

/-- `dot(left, right) = Σ x·y` (`verifier.py:273-277`). -/
def dot (left right : List E) : E :=
  (List.zipWith (· * ·) left right).foldl (· + ·) 0

/-- `padding_weight(point, n)`: `pad_n(point)`, the multilinear extension of `[z ≥ n]` for
`n ≤ 2^|point|`, unrolled from the low bit (`verifier.py:280-286`; `doc/leanvm`, Lemma
`lem:suffix`). -/
def paddingWeight (point : List E) (n : ℕ) : E :=
  (1 + eOfNat ((n >>> point.length) % 2)) *
    point.zipIdx.foldl (fun pad (r, k) ↦
      let b := eOfNat ((n >>> k) % 2)
      (1 + b) * r + (1 + b + r) * pad) 1

/-- `index_mle(point)`: the multilinear extension of `[1, g, g², …]` at an LSB-first point,
`Π (1 + r_i·(1 + g^(2^i)))` (`verifier.py:289-296`). -/
def indexMleFrom (generatorPower : E) : List E → E → E
  | [], acc => acc
  | r :: rs, acc => indexMleFrom (generatorPower ^ 2) rs (acc * (1 + r * (1 + generatorPower)))

/-- `index_mle(point)` (`verifier.py:289-296`). -/
def indexMle (point : List E) : E := indexMleFrom gen point 1

/-- `poly_eval(coefficients, point)`: Horner's rule over the coefficients, constant first
(`verifier.py:299-301`). -/
def polyEval (coefficients : List E) (point : E) : E :=
  coefficients.foldr (fun c acc ↦ acc * point + c) 0

/-- `_selector_point(selector, length)`: the low `length` bits of `selector` as `0/1` elements,
lowest first (`verifier.py:329-330`). -/
def selectorPoint (selector length : ℕ) : List E :=
  (List.range length).map fun bit ↦ eOfNat ((selector >>> bit) % 2)

/-!
## The verifier's layout (`verifier.py:304-331, 500-578, 687-1014`)

* A `Form` is the Python's `dict` from monomials to coefficients, as an association list in
  insertion order: `addScaled` adds into an existing monomial's coefficient and appends a new
  one, as the `dict` does. A monomial is the sorted list of its column indices (`()`, `(i,)`,
  `(i, j)`).
* The Python's column-name lookups `_cols` are `colIdx`, `List.idxOf` on the column-name list;
  every name the tables use is in its list, as the Python's `assert` checks.
* `Table.constraints` is a function of the row's evaluations, as in the Python; only `jump` has
  any (`_jump_constraints`).
* A placement is `none` where the Python's is `None`: a `KECCAK` output lane, which nothing
  commits or opens.
* `build_layout` returns `none` exactly where the Python raises: a bytecode whose length is not
  a power of two (`log2_strict`), a bytecode shorter than `2^BUS_BITS` (negative
  `log_bytecode`), the size window, and a list of heights not one per table (the strict `zip`).
-/

/-! ### Constants (`verifier.py:570, 686-703, 926, 971`), each the Python's of that name -/

/-- `BUS_BITS`: the bus communicates tuples of `2^BUS_BITS` field elements. -/
def busBits : ℕ := 4

/-- The columns no instruction table owns, first in the global numbering. -/
def numGlobalColumns : ℕ := 6

-- The global columns `MEMORY_0`, `MEMORY_1`, `MEMORY_2`, `MEMORY_FINAL_COUNTERS`,
-- `BYTECODE_FINAL_COUNTERS`.
def memory0 : ℕ := 0
def memory1 : ℕ := 1
def memory2 : ℕ := 2
def memoryFinalCounters : ℕ := 3
def bytecodeFinalCounters : ℕ := 4
/-- Global column `QKECCAK`, the Keccak reduction's committed column: per step, its input state's
lanes and the state after every `KECCAK_DEPTH` rounds but the last, a lane per slot, and in the
slots left over the `KECCAK` table's own first committed columns (`keccakSlot`). -/
def qkeccak : ℕ := 5

def kBits : ℕ := 64

/-- `KECCAK_DEPTH`: the reduction commits a step's state every `12` rounds. -/
def keccakDepth : ℕ := 12

/-- `KECCAK_SEGMENTS = ROUNDS // KECCAK_DEPTH`, `ROUNDS = 24`. -/
def keccakSegments : ℕ := 24 / keccakDepth

/-- `KECCAK_SEGMENT_BITS = log2_ceil(KECCAK_SEGMENTS)`. -/
def keccakSegmentBits : ℕ := log2Ceil keccakSegments

/-- `QKECCAK_SLOT_BITS = log2_ceil(STATE_LANES * KECCAK_SEGMENTS)`, `STATE_LANES = 25`: lane `l`
of the state after `KECCAK_DEPTH · m` rounds is slot `25m + l`; the `2^6 - 50` slots above the
states carry `KECCAK` columns (`keccakSlot`). -/
def qkeccakSlotBits : ℕ := log2Ceil (25 * keccakSegments)

/-- `KECCAK_MIN_STEPS_LOG`: the reduction is sized for at least one block of `512` steps. -/
def keccakMinStepsLog : ℕ := 9

/-- `KECCAK_BITS = 64 * STATE_LANES`: a state's bits. -/
def keccakBits : ℕ := 1600

/-- `KECCAK_LOCAL_BITS`: a bit position is `z + 64 · lane`, in a cube of `2^11`. -/
def keccakLocalBits : ℕ := 11

def keccakLaneBits : ℕ := 5

/-- `SEP_STATE = ONE`. -/
def sepState : E := 1
/-- `SEP_MEM = GEN`. -/
def sepMem : E := gen
/-- `SEP_BYTECODE = GEN²`. -/
def sepBytecode : E := gen ^ 2

-- The opcodes `XOR`, `MUL`, `SET`, `DEREF`, `JUMP`, `KECCAK`.
def opXor : ℕ := 0
def opMul : ℕ := 1
def opSet : ℕ := 2
def opDeref : ℕ := 3
def opJump : ℕ := 4
def opKeccak : ℕ := 5

/-! ### Placements (`verifier.py:304-331`) -/

/-- Where something sits in the stacked cube: a claim's point fills the `vars` coordinates
above `low`, the bits of the selector `index` fixing the rest.

The pin's `Placement` has no `low` (`verifier.py:304-317`): `stack_point` is
`point ++ _selector_point(index >> variables, stack_log - variables)` and `eq_above` weighs
`point[variables:]` against `_selector_point(index >> variables, len(point) - variables)`. The two
are the same verifier: every placement the verifier builds has `low = 0` (`busLayout`,
`placementsOf`, the default), and at `low = 0`, `bits.drop vars` of `selectorPoint index stackLog`
is `selectorPoint (index >>> vars) (stackLog - vars)`, `_selector_point` writing the selector's
bits lowest first. -/
structure Placement where
  vars : ℕ
  index : ℕ
  low : ℕ := 0
  deriving Inhabited, DecidableEq

/-- `Placement.stack_point`: the point on the stacked cube. -/
def Placement.stackPoint (p : Placement) (point : List E) (stackLog : ℕ) : List E :=
  let bits := selectorPoint p.index stackLog
  bits.take p.low ++ point ++ bits.drop (p.low + p.vars)

/-- `Placement.eq_above`: the equality weight of the coordinates above the window. -/
def Placement.eqAbove (p : Placement) (point : List E) : E :=
  let bits := selectorPoint (p.index >>> (p.low + p.vars))
    (point.length - p.low - p.vars)
  eqEval bits (point.drop (p.low + p.vars))

/-- `stack_offsets(sizes)`: blocks of `2^size` laid end to end, largest first, ties by index;
their offsets, and the log-size of the total (`verifier.py:320-326`). -/
def stackOffsets (sizes : List ℕ) : List ℕ × ℕ :=
  let size := fun i ↦ sizes.getD i 0
  let order := (List.range sizes.length).mergeSort fun i j ↦
    decide (size j < size i) || (decide (size i = size j) && decide (i ≤ j))
  let placed := order.foldl (fun (acc : List ℕ × ℕ) i ↦
    (acc.1.set i acc.2, acc.2 + 2 ^ size i)) (List.replicate sizes.length 0, 0)
  (placed.1, log2Ceil placed.2)

/-! ### Forms (`verifier.py:500-522`) -/

/-- A polynomial of degree at most two in a table's columns: monomial (sorted column indices) to
coefficient, in insertion order. -/
structure Form where
  terms : List (List ℕ × E) := []
  deriving Inhabited

/-- Add `c` into the coefficient of `m`, appending the monomial if it is new (the `dict`
update). -/
def addTerm : List (List ℕ × E) → List ℕ → E → List (List ℕ × E)
  | [], m, c => [(m, 0 + c)]
  | (m', c') :: rest, m, c =>
    if m' = m then (m', c' + c) :: rest else (m', c') :: addTerm rest m c

/-- `Form.add_scaled`: add `weight · other`. -/
def Form.addScaled (f other : Form) (weight : E) : Form :=
  ⟨other.terms.foldl (fun acc t ↦ addTerm acc t.1 (weight * t.2)) f.terms⟩

/-- `Form.__add__`. -/
def Form.add (f g : Form) : Form := f.addScaled g 1

/-- `Form.sum`: the empty sum is the zero polynomial. -/
def Form.sum (forms : List Form) : Form := forms.foldl Form.add {}

/-- `Form.evaluate`: `Σ c · Π column(i)` over the terms. -/
def Form.evaluate (f : Form) (column : ℕ → E) : E :=
  sumE (f.terms.map fun t ↦ t.1.foldl (fun acc i ↦ acc * column i) t.2)

/-- `_const(value)`. -/
def Form.const (value : E) : Form := ⟨[([], value)]⟩

/-- `_col(index, exponent)`: `g^exponent · x_index`. -/
def Form.col (index : ℕ) (exponent : ℕ := 0) : Form := ⟨[([index], gpow exponent)]⟩

/-- `_prod(a, b, exponent)`: `g^exponent · x_a · x_b`. -/
def Form.prod (a b : ℕ) (exponent : ℕ := 0) : Form := ⟨[([min a b, max a b], gpow exponent)]⟩

/-! ### Flushes (`verifier.py:745-770`) -/

/-- A table's bus flushes: the tuples it pushes and pulls, in pairs. -/
structure Flushes where
  push : List (List Form) := []
  pull : List (List Form) := []
  deriving Inhabited

namespace Flushes

/-- `Flushes.pair`. -/
def pair (f : Flushes) (push pull : List Form) : Flushes := ⟨f.push ++ [push], f.pull ++ [pull]⟩

/-- `Flushes.state_derived`. -/
def stateDerived (f : Flushes) (pc fp : ℕ) (npc nfp : Form) : Flushes :=
  f.pair [Form.const sepState, npc, nfp] [Form.const sepState, Form.col pc, Form.col fp]

/-- `Flushes.state_step`. -/
def stateStep (f : Flushes) (pc fp : ℕ) : Flushes :=
  f.stateDerived pc fp (Form.col pc 1) (Form.col fp)

/-- `Flushes._counted`. -/
def counted (f : Flushes) (pre : List Form) (count : ℕ) (suffix : List Form) : Flushes :=
  f.pair (pre ++ [Form.col count 1] ++ suffix) (pre ++ [Form.col count] ++ suffix)

/-- `Flushes.bytecode`. -/
def bytecode (f : Flushes) (pc count opcode : ℕ) (operands : List Form) : Flushes :=
  f.counted [Form.const sepBytecode, Form.col pc] count (Form.const (gpow opcode) :: operands)

/-- `Flushes.memory`. -/
def memory (f : Flushes) (address : Form) (count : ℕ) (values : List Form) : Flushes :=
  f.counted [Form.const sepMem, address] count values

/-- `Flushes.memory_cols`: the columns, padded with zeros to three limbs. -/
def memoryCols (f : Flushes) (address : Form) (count : ℕ) (columns : List ℕ) : Flushes :=
  f.memory address count
    (columns.map (Form.col ·) ++ List.replicate (3 - columns.length) (Form.const 0))

end Flushes

/-! ### The instruction tables (`verifier.py:776-968`) -/

/-- `_cols(columns, name)`: the index of a column by name. -/
def colIdx (columns : List String) (name : String) : ℕ := columns.idxOf name

/-- `ARITH_COLUMNS`. -/
def arithColumns : List String :=
  ["pc", "fp", "o_a", "o_b", "o_c", "va_0", "va_1", "va_2", "vb_0", "vb_1", "vb_2", "cnt_a",
    "cnt_b", "cnt_c", "cnt_bc"]

/-- `SET_COLUMNS`. -/
def setColumns : List String := ["pc", "fp", "o", "k_0", "k_1", "k_2", "cnt", "cnt_bc"]

/-- `DEREF_COLUMNS`. -/
def derefColumns : List String :=
  ["pc", "fp", "o1", "o2", "o3", "f_pc", "f_fp", "ptr", "v3_0", "v3_1", "v3_2", "cnt_ptr",
    "cnt_target", "cnt_local", "cnt_bc"]

/-- `JUMP_COLUMNS`. -/
def jumpColumns : List String :=
  ["pc", "fp", "o_c", "o_d", "o_f", "v_cond", "v_pc", "v_fp", "cnt_c", "cnt_d", "cnt_f", "cnt_bc",
    "w", "b"]

/-- The decimal numeral of `n` (`f"{n}"`): its digits below `100`, the column names' numbers
(`toString` past them). -/
def decimal (n : ℕ) : String :=
  if n < 10 then (Char.ofNat (48 + n)).toString
  else if n < 100 then (Char.ofNat (48 + n / 10)).toString ++ (Char.ofNat (48 + n % 10)).toString
  else toString n

/-- The names of the `25` lanes of a state, with a prefix: `prefix_0, …, prefix_24`. -/
def laneNames (pre : String) : List String := (List.range 25).map fun l ↦ pre ++ "_" ++ decimal l

/-- `KECCAK_COLUMNS` (`verifier.py:932-941`): the operands, the layout flags, the read limb that
holds no lane (`free`), the fifty value lanes (`in_l`, one of `q_keccak`'s slots each; `out_l`,
claimed by the Keccak reduction, committed nowhere), then the read counts. The first
`QKECCAK_SPARE` (`14`) committed columns, `pc` through `free` and `cnt_0`, ride `q_keccak`'s spare
slots `50…63` (`keccakSlotOf`). -/
def keccakColumns : List String :=
  ["pc", "fp", "o_m0", "o_m1", "o_m2", "o_m3", "o_tail", "o_b8", "o_cap", "o_out", "odd_in",
    "odd_out", "free"] ++ laneNames "in" ++ laneNames "out" ++
    (List.range 26).map (fun c ↦ "cnt_" ++ decimal c) ++ ["cnt_bc"]

/-- `KECCAK_IN` (`verifier.py:942`): the local column of input lane `0`. -/
def keccakIn : ℕ := colIdx keccakColumns "in_0"

/-- `KECCAK_CNT` (`verifier.py:942`): the local column of the first read count. -/
def keccakCnt : ℕ := colIdx keccakColumns "cnt_0"

/-- `QKECCAK_SLOTS = STATE_LANES * KECCAK_SEGMENTS` (`verifier.py:946`): the slots of `q_keccak`
the states take. -/
def qkeccakSlots : ℕ := 25 * keccakSegments

/-- `QKECCAK_SPARE = 2**QKECCAK_SLOT_BITS - QKECCAK_SLOTS` (`verifier.py:947`): the slots of
`q_keccak` left over, which carry `KECCAK` columns. -/
def qkeccakSpare : ℕ := 2 ^ qkeccakSlotBits - qkeccakSlots

/-- `_KECCAK_COMMITTED` (`verifier.py:948`): the local `KECCAK` columns outside the value lanes,
`KECCAK_IN ≤ local < KECCAK_CNT`, in order. -/
def keccakCommitted : List ℕ :=
  (List.range keccakColumns.length).filter fun l ↦ ¬ (keccakIn ≤ l ∧ l < keccakCnt)

/-- `KECCAK_SLOT_OF` (`verifier.py:952-954`): the `q_keccak` slot of a local `KECCAK` column, if
it has one: input lane `l` (local column `KECCAK_IN + l`) is slot `l`, and the first
`QKECCAK_SPARE` committed columns take the slots from `QKECCAK_SLOTS` on, in order. The two
parts of the Python's dictionary union have disjoint keys (`keccakSlotOf_disjoint`), so the order
in which they are tried does not matter. -/
def keccakSlotOf (l : ℕ) : Option ℕ :=
  if keccakIn ≤ l ∧ l < keccakIn + 25 then some (l - keccakIn)
  else ((keccakCommitted.take qkeccakSpare).idxOf? l).map (qkeccakSlots + ·)

/-- `TOWER_LANES`: the limb products of `E` multiplication folded by `y³ = y + 1`. -/
def towerLanes : List (List (ℕ × ℕ)) :=
  [[(0, 0), (1, 2), (2, 1)], [(0, 1), (1, 0), (1, 2), (2, 1), (2, 2)],
    [(0, 2), (1, 1), (2, 0), (2, 2)]]

/-- `_flushes_arith(opcode, multiply)` (`verifier.py:807-822`). -/
def flushesArith (opcode : ℕ) (multiply : Bool) : Flushes :=
  let c := colIdx arithColumns
  let va := [c "va_0", c "va_1", c "va_2"]
  let vb := [c "vb_0", c "vb_1", c "vb_2"]
  let result : List Form :=
    if multiply then
      towerLanes.map fun lane ↦
        Form.sum (lane.map fun (j, k) ↦ Form.prod (va.getD j 0) (vb.getD k 0))
    else (List.range 3).map fun i ↦ (Form.col (va.getD i 0)).add (Form.col (vb.getD i 0))
  let f : Flushes := {}
  let f := f.stateStep (c "pc") (c "fp")
  let f := f.bytecode (c "pc") (c "cnt_bc") opcode
    [Form.col (c "o_a"), Form.col (c "o_b"), Form.col (c "o_c"), Form.const 0, Form.const 0]
  let f := f.memoryCols (Form.prod (c "fp") (c "o_a")) (c "cnt_a") va
  let f := f.memoryCols (Form.prod (c "fp") (c "o_b")) (c "cnt_b") vb
  f.memory (Form.prod (c "fp") (c "o_c")) (c "cnt_c") result

/-- `_flushes_set()` (`verifier.py:825-832`). -/
def flushesSet : Flushes :=
  let c := colIdx setColumns
  let k := [c "k_0", c "k_1", c "k_2"]
  let f : Flushes := {}
  let f := f.stateStep (c "pc") (c "fp")
  let f := f.bytecode (c "pc") (c "cnt_bc") opSet
    (Form.col (c "o") :: k.map (Form.col ·) ++ [Form.const 0])
  f.memoryCols (Form.prod (c "fp") (c "o")) (c "cnt") k

/-- `_flushes_deref()` (`verifier.py:835-851`). -/
def flushesDeref : Flushes :=
  let c := colIdx derefColumns
  let pc := c "pc"
  let fp := c "fp"
  let fPc := c "f_pc"
  let fFp := c "f_fp"
  let v3 := [c "v3_0", c "v3_1", c "v3_2"]
  let gated := fun lane ↦ [Form.col lane, Form.prod fPc lane, Form.prod fFp lane]
  let store : List Form :=
    [Form.sum (gated (v3.getD 0 0) ++ [Form.prod fPc pc 2, Form.prod fFp fp]),
      Form.sum (gated (v3.getD 1 0)), Form.sum (gated (v3.getD 2 0))]
  let f : Flushes := {}
  let f := f.stateStep pc fp
  let f := f.bytecode pc (c "cnt_bc") opDeref
    [Form.col (c "o1"), Form.col (c "o2"), Form.col (c "o3"), Form.col fPc, Form.col fFp]
  let f := f.memoryCols (Form.prod fp (c "o1")) (c "cnt_ptr") [c "ptr"]
  let f := f.memory (Form.prod (c "ptr") (c "o2")) (c "cnt_target") store
  f.memoryCols (Form.prod fp (c "o3")) (c "cnt_local") v3

/-- `_flushes_jump()` (`verifier.py:854-864`): `next_pc = b·dest + (b + 1)·g·pc`,
`next_fp = b·frame + (b + 1)·fp`. -/
def flushesJump : Flushes :=
  let c := colIdx jumpColumns
  let pc := c "pc"
  let fp := c "fp"
  let b := c "b"
  let f : Flushes := {}
  let f := f.stateDerived pc fp
    (((Form.prod b (c "v_pc")).add (Form.prod b pc 1)).add (Form.col pc 1))
    (((Form.prod b (c "v_fp")).add (Form.prod b fp)).add (Form.col fp))
  let f := f.bytecode pc (c "cnt_bc") opJump
    [Form.col (c "o_c"), Form.col (c "o_d"), Form.col (c "o_f"), Form.const 0, Form.const 0]
  let f := f.memoryCols (Form.prod fp (c "o_c")) (c "cnt_c") [c "v_cond"]
  let f := f.memoryCols (Form.prod fp (c "o_d")) (c "cnt_d") [c "v_pc"]
  f.memoryCols (Form.prod fp (c "o_f")) (c "cnt_f") [c "v_fp"]

/-- `_jump_constraints(columns)`: `b + cond·w` and `cond·(b + 1)` (`verifier.py:867-869`). -/
def jumpConstraints (columns : List E) : List E :=
  let c := colIdx jumpColumns
  let condition := columns.getD (c "v_cond") 0
  let inverse := columns.getD (c "w") 0
  let flag := columns.getD (c "b") 0
  [flag + condition * inverse, condition * (flag + 1)]

/-- `_layout_limb(even, odd, flag, missing)` (`verifier.py:887-893`): a cell limb holding the
column `even` in the even layout and `odd` in the odd one, as the column `flag` selects,
`a + flag·(a + b)`; a missing column is `missing`. -/
def layoutLimb (even odd : Option ℕ) (flag : ℕ) (missing : Option ℕ) : Form :=
  let a := even.orElse fun _ ↦ missing
  let b := odd.orElse fun _ ↦ missing
  if a = b then
    match a with
    | none => Form.const 0
    | some a => Form.col a
  else
    Form.sum ((match a with
      | some a => [Form.col a, Form.prod flag a]
      | none => []) ++
      (match b with
      | some b => [Form.prod flag b]
      | none => []))

/-- `_flushes_keccak()` (`verifier.py:896-923`): the state step, the bytecode read, then the
thirteen cells read (four addressed ones, the tail run, `b8`, the cap run) and the thirteen
written, each holding its lanes in the layout its flag names (`_keccak_cell_lanes`, which is
`cellLanes`, `LeanIsa.lean`): a read cell's free limb is the column `free`, a written one's zero.
The pin finds a lane's column and a cell's count by index,
`KECCAK_IN + lane`, `KECCAK_OUT + lane` and `KECCAK_CNT + 13 · side + cell`; this reads them by
name, `in_l`, `out_l` and `cnt_c`, the same columns (`keccakColumns`). -/
def flushesKeccak : Flushes :=
  let c := colIdx keccakColumns
  let oM := ["o_m0", "o_m1", "o_m2", "o_m3"].map c
  let fp := c "fp"
  let f : Flushes := {}
  let f := f.stateStep (c "pc") fp
  let f := f.bytecode (c "pc") (c "cnt_bc") opKeccak
    ((oM ++ ["o_tail", "o_b8", "o_cap", "o_out", "odd_in", "odd_out"].map c).map (Form.col ·))
  let address := fun (cell : ℕ) ↦
    if cell < 4 then Form.prod fp (oM.getD cell 0)
    else if cell < 8 then Form.prod fp (c "o_tail") (cell - 4)
    else if cell = 8 then Form.prod fp (c "o_b8")
    else Form.prod fp (c "o_cap") (cell - 9)
  let sides : List (String × ℕ × Option ℕ) := [("in", c "odd_in", some (c "free")),
    ("out", c "odd_out", none)]
  sides.zipIdx.foldl (fun f ((pre, flag, missing), side) ↦
    let lane := fun (l : Option ℕ) ↦ l.map fun l ↦ c (pre ++ "_" ++ decimal l)
    (List.range 13).foldl (fun f cell ↦
      let values := ([0, 1] : List ℕ).map (fun h ↦
        let pick := fun (p : Option ℕ × Option ℕ) ↦ if h = 0 then p.1 else p.2
        layoutLimb (lane (pick (cellLanes false cell)))
          (lane (pick (cellLanes true cell))) flag missing) ++ [Form.const 0]
      f.memory (if side = 0 then address cell else Form.prod fp (c "o_out") cell)
        (c ("cnt_" ++ decimal (13 * side + cell))) values) f) f

/-- One instruction's table: its columns, its bus flushes, its constraints
(`verifier.py:776-796`). -/
structure Table where
  /-- Its opcode, also its index in `TABLES`. -/
  opcode : ℕ
  columns : List String
  flushes : Flushes
  /-- Its constraints, as a function of a row's evaluations. -/
  constraints : List E → List E := fun _ ↦ []
  deriving Inhabited

/-- `Table.width`. -/
def Table.width (t : Table) : ℕ := t.columns.length

/-- `Table.n_constraints`: the number of constraints, read off the zero row. -/
def Table.nConstraints (t : Table) : ℕ := (t.constraints (List.replicate t.width 0)).length

/-- `Table.count_columns`: the columns whose name starts with `cnt`. -/
def Table.countColumns (t : Table) : List ℕ :=
  (t.columns.zipIdx.filter fun (name, _) ↦ name.startsWith "cnt").map (·.2)

/-- `TABLES`, in opcode order (`verifier.py:957-964`; their names, unused, are omitted). -/
def tables : List Table :=
  [⟨opXor, arithColumns, flushesArith opXor false, fun _ ↦ []⟩,
    ⟨opMul, arithColumns, flushesArith opMul true, fun _ ↦ []⟩,
    ⟨opSet, setColumns, flushesSet, fun _ ↦ []⟩,
    ⟨opDeref, derefColumns, flushesDeref, fun _ ↦ []⟩,
    ⟨opJump, jumpColumns, flushesJump, jumpConstraints⟩,
    ⟨opKeccak, keccakColumns, flushesKeccak, fun _ ↦ []⟩]

/-- The names of the output state's lanes, `KECCAK_COLUMNS[KECCAK_OUT : KECCAK_OUT +
STATE_LANES]` (`verifier.py:803, 1001, 1506`), which have no slot. -/
def keccakOutputs : List String := laneNames "out"

/-- `Table.padding` (`verifier.py:798-804`): the row a padding row holds, zero but for `KECCAK`'s
output lanes, a padding row permuting zeros. The pin writes `keccak_f([0] * 25)` into the columns
`KECCAK_OUT …` by index; lane `l` of it lands in column `out_l` either way. -/
def Table.padding (t : Table) : List E :=
  if t.opcode = opKeccak then
    let output := keccakF1600 (Vector.replicate 25 0)
    t.columns.map fun name ↦
      if name ∈ keccakOutputs then eOfNat (Keccak.lane output (keccakOutputs.idxOf name)).toNat
      else 0
  else t.columns.map fun _ ↦ 0

/-- `TABLE_WIDTHS`. -/
def tableWidths : List ℕ := tables.map Table.width

/-- `GLOBAL_COLUMN_BASES`: each table's first global column. -/
def globalColumnBases : List ℕ :=
  (List.range tables.length).map fun t ↦ numGlobalColumns + (tableWidths.take t).sum

/-- `TABLE_LOG_FLOORS` (`verifier.py:971`): each table's least log-height, `0` but for
`KECCAK`, the Keccak reduction's block of steps. -/
def tableLogFloors : List ℕ := [0, 0, 0, 0, 0, keccakMinStepsLog]

/-! ### The bus layout (`verifier.py:524-578`) -/

/-- One block of a bus side, owned by a table. -/
structure BusBlock where
  /-- The owner's log-height: the block spans `2 ^ logRows` rows. -/
  logRows : ℕ
  /-- The owner's row count: the first `rows` rows flush, the others are padding rows, whose
  leaves are `1`. -/
  rows : ℕ
  /-- The tuple flushed, over the owner's local columns. -/
  coordinates : List Form
  /-- The owner's opcode. -/
  owner : ℕ
  deriving Inhabited

/-- Where a side's blocks sit in the stacked leaf cube: its log-size, the framework blocks'
placements, and the table blocks', in the side's block order. -/
structure BusLayout where
  depth : ℕ
  framework : List Placement
  tables : List Placement

/-- `bus_layout(framework_log_rows, blocks)` (`verifier.py:547-552`). -/
def busLayout (frameworkLogRows : List ℕ) (blocks : List BusBlock) : BusLayout :=
  let sizes := frameworkLogRows ++ blocks.map (·.logRows)
  let (offsets, depth) := stackOffsets sizes
  let placements := List.zipWith (fun size offset ↦ ({ vars := size, index := offset } :
    Placement)) sizes offsets
  ⟨depth, placements.take frameworkLogRows.length, placements.drop frameworkLogRows.length⟩

/-- A column claim: the global column's multilinear extension at `point` (over the column's own
variables) is `value`. -/
structure ColumnClaim where
  column : ℕ
  point : List E
  value : E
  deriving Inhabited

/-- A claim on the stack: the weight it puts on the stack, and the value it claims for it. -/
abbrev StackClaim : Type := (List E → E) × E

/-! ### `build_layout` (`verifier.py:706-716, 974-1014`) -/

/-- The layout the verifier derives from the bytecode and the announced sizes. -/
structure Layout where
  logMemory : ℕ
  /-- The bytecode's log-size, in tuples of `2^BUS_BITS` words. -/
  logBytecode : ℕ
  bytecode : List K
  push : List BusBlock
  pull : List BusBlock
  count : List BusBlock
  /-- Every global column's placement; `none` for a `KECCAK` output lane. -/
  placements : List (Option Placement)
  stackLog : ℕ
  /-- The tables' log-heights, each the least `h` with `rows ≤ 2 ^ h`, at least its floor. -/
  tableLogHeights : List ℕ

/-- The placement of a committed column (`layout.placements[column]`), which the verifier reads
of `MEMORY_0` and `QKECCAK`. -/
def Layout.placement (layout : Layout) (column : ℕ) : Placement :=
  (layout.placements.getD column none).getD default

/-- `ColumnClaim.on_stack` (`verifier.py:561-567`): the claim as an equality weight on the
stack; `none` for a column nothing commits (a `KECCAK` output lane), whose claim never reaches
the stack. -/
def ColumnClaim.onStack (c : ColumnClaim) (layout : Layout) : Option StackClaim :=
  (layout.placements.getD c.column none).map fun placement ↦
    (fun x ↦ eqEval (placement.stackPoint c.point layout.stackLog) x, c.value)

/-- The bus blocks of every table, side by side: pushes, pulls, counts, each block at its
table's log-height and row count (`verifier.py:980-990`). -/
def busBlocks (tableLogHeights tableRows : List ℕ) :
    List BusBlock × List BusBlock × List BusBlock :=
  let rows := List.zip tables (List.zip tableLogHeights tableRows)
  (rows.flatMap fun (t, h, n) ↦ t.flushes.push.map fun c ↦ ⟨h, n, c, t.opcode⟩,
    rows.flatMap fun (t, h, n) ↦ t.flushes.pull.map fun c ↦ ⟨h, n, c, t.opcode⟩,
    rows.flatMap fun (t, h, n) ↦ t.countColumns.map fun l ↦ ⟨h, n, [Form.col l], t.opcode⟩)

/-- The `q_keccak` slot of a global column (`slots`, `verifier.py:1002`,
`KECCAK_SLOT_OF.get(column - base)`): a `KECCAK` input lane's, or a spare slot's column's; `none`
for every other column, those of the other tables (whose `column - base` is negative, no key of
`KECCAK_SLOT_OF`) among them. -/
def keccakSlot (column : ℕ) : Option ℕ :=
  if globalColumnBases.getD opKeccak 0 ≤ column then
    keccakSlotOf (column - globalColumnBases.getD opKeccak 0)
  else none

/-- The global columns of the `KECCAK` output lanes, in lane order (`outputs`,
`verifier.py:1001`; the columns of `values[KECCAK_OUT : KECCAK_OUT + STATE_LANES]`,
`verifier.py:1506`). -/
def keccakOutputColumns : List ℕ :=
  keccakOutputs.map fun name ↦ globalColumnBases.getD opKeccak 0 + colIdx keccakColumns name

/-- Every column's log-size, in global order: the framework's, `q_keccak`'s, then each table's
block (`verifier.py:992-996`). -/
def columnKappas (logMemory logBytecode : ℕ) (tableLogHeights : List ℕ) : List ℕ :=
  let qkeccakKappa := tableLogHeights.getD opKeccak 0 + qkeccakSlotBits
  [logMemory, logMemory, logMemory, logMemory, logBytecode, qkeccakKappa] ++
    tables.flatMap fun t ↦ List.replicate t.width (tableLogHeights.getD t.opcode 0)

/-- The placements of every column, and the stack's log-size (`verifier.py:998-1013`): the
committed columns (every column but those with a `q_keccak` slot, the `KECCAK` input lanes and
the table's first fourteen committed columns, and the `KECCAK` output lanes: `99` of `163`)
stacked by `stack_offsets`, a column with a slot at `q_keccak`'s offset plus its slot's `2^κ`
words, an output lane nowhere. -/
def placementsOf (kappas : List ℕ) : List (Option Placement) × ℕ :=
  let blockCols := (List.range kappas.length).filter fun c ↦
    (keccakSlot c).isNone ∧ c ∉ keccakOutputColumns
  let (blockOffsets, totalLog) := stackOffsets (blockCols.map (kappas.getD · 0))
  let offsetOf := fun c ↦ blockOffsets.getD (blockCols.idxOf c) 0
  let placements := kappas.zipIdx.map fun (kappa, column) ↦
    match keccakSlot column with
    | some slot => some ({ vars := kappa, index := offsetOf qkeccak + slot * 2 ^ kappa } : Placement)
    | none =>
      if column ∈ keccakOutputColumns then none else some { vars := kappa, index := offsetOf column }
  (placements, max Whir.minLogStack totalLog)

/-- `build_layout(bytecode, log_memory, table_rows)` (`verifier.py:974-1014`); `none` where the
Python raises. A table's log-height is the least `h` with `rows ≤ 2^h` (`log2Ceil`), and at least
its floor (`tableLogFloors`). -/
def buildLayout (bytecode : List K) (logMemory : ℕ) (tableRows : List ℕ) : Option Layout :=
  match log2Strict bytecode.length with
  | none => none
  | some logLength =>
    if busBits ≤ logLength ∧ 16 ≤ logMemory ∧ logMemory ≤ 32 ∧
        tableRows.all (· ≤ 2 ^ 32) ∧ logLength - busBits ≤ 32 ∧
        tableRows.length = tables.length then
      let logBytecode := logLength - busBits
      let tableLogHeights := List.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) tableRows
        tableLogFloors
      let (push, pull, count) := busBlocks tableLogHeights tableRows
      let (placements, stackLog) :=
        placementsOf (columnKappas logMemory logBytecode tableLogHeights)
      some ⟨logMemory, logBytecode, bytecode, push, pull, count, placements, stackLog,
        tableLogHeights⟩
    else none

open LeanVM.Protocol.Compile

/-!
## Sumcheck rounds (`verifier.py:447-468`)

A round polynomial of `count` coefficients is sent with one coefficient left out, which the
verifier derives from the running claim: in plain mode (`eq_factor = None`) `q(0) + q(1) = claim`
fixes `c1`; in equality mode (`eq_factor = r`) `(1 + r)·q(0) + r·q(1) = claim` fixes `c0`
(characteristic two).
-/

/-- Fail on `none`: a pure step the Python performs with a `require` inside. -/
def liftOption {α : Type} : Option α → Prog α
  | none => Prog.fail
  | some a => Prog.ret a

/-- `Transcript.sumcheck_round_poly(count, claim, eq_factor)`: read a round polynomial of `count`
coefficients, deriving the one the claim fixes; its coefficients, constant first
(`verifier.py:447-454`). -/
def sumcheckRoundPoly (count : ℕ) (claim : E) : Option E → Prog (List E)
  | none => do
    let constant ← Prog.readScalar
    let tail ← Prog.readScalars (count - 2)
    return constant :: (claim + sumE tail) :: tail
  | some eqFactor => do
    let tail ← Prog.readScalars (count - 1)
    return (claim + eqFactor * sumE tail) :: tail

/-- `sumcheck(transcript, claim, count, equalities)`: one round per entry of `equalities`, each
reading its polynomial and sampling its challenge; the challenges in order, and the final claim
(`verifier.py:461-468`). -/
def sumcheck (claim : E) (count : ℕ) : List (Option E) → Prog (List E × E)
  | [] => return ([], claim)
  | equality :: equalities => do
    let message ← sumcheckRoundPoly count claim equality
    let challenge ← Prog.sampleChallenge
    let (point, final) ← sumcheck (polyEval message challenge) count equalities
    return (challenge :: point, final)

/-!
## The bus phase (`verifier.py:474-497, 573-643`)

The three GKR trees (push, pull, count) are batched, their roots read as `shared, count` (push and
pull share their root, which is the balance), the layers walked two at a time, one first when the
depth is odd. The leaf decomposition is pure (`accumulateSide`): every side's framework blocks are
evaluated outright, its table blocks accumulate into the owner's form for that side, and the
side's total is the GKR value less the framework and the padding.
-/

/-- The state of the GKR walk: the push, pull and count trees' values at `point`. -/
structure GkrState where
  values : List E
  point : List E

/-- One step of `step` levels of the GKR walk (`verifier.py:483-494`). -/
def gkrStep (step : ℕ) (s : GkrState) : Prog GkrState := do
  let combiner ← Prog.sampleChallenge
  let claim := polyEval s.values combiner
  let (x, claim) ← sumcheck claim (2 ^ step + 1) (s.point.map some)
  let child0 ← Prog.readScalars (2 ^ step)
  let child1 ← Prog.readScalars (2 ^ step)
  let child2 ← Prog.readScalars (2 ^ step)
  let children := [child0, child1, child2]
  let products := children.map prodE
  Prog.require (claim = polyEval products combiner)
  let y ← Prog.sampleChallenges step
  let values := children.map (multilinearEval · y)
  return ⟨values, y ++ x⟩

/-- The `while layer > 0` loop: one level when the remaining depth is odd, two otherwise. -/
def gkrLayers : ℕ → GkrState → Prog GkrState
  | 0, s => return s
  | 1, s => do
    let s ← gkrStep 1 s
    gkrLayers 0 s
  | n + 2, s =>
    if n % 2 = 1 then do
      let s ← gkrStep 1 s
      gkrLayers (n + 1) s
    else do
      let s ← gkrStep 2 s
      gkrLayers n s

/-- `verify_gkr_grand_products(depth)`: the count root, the GKR point, and the three trees'
values there (`verifier.py:474-497`). -/
def verifyGkrGrandProducts (depth : ℕ) : Prog (E × List E × List E) := do
  let shared ← Prog.readScalar
  let count ← Prog.readScalar
  let s ← gkrLayers depth ⟨[shared, shared, count], []⟩
  return (count, s.point, s.values)

/-- `BusResult`: the framework columns' claims, the GKR point (which the table sumcheck reuses),
each table's form per side (`forms[table][side]`), and the three sides' totals. -/
structure BusResult where
  claims : List ColumnClaim
  point : List E
  forms : List (List Form)
  totals : List E

/-- The three framework fingerprints of a side (`verifier.py:603-615`, `fingerprints`; the
Python hoists `memory_index` and `bytecode_index`, pure values inlined here; `bytecode_value` is
the bytecode's value, from `ev`). -/
def fingerprints (weights memory memoryLow bytecodeLow : List E) (bytecodeValue : E)
    (pc memoryCount bytecodeCount : E) : List E :=
  [dot (weights.take 3) [sepState, pc, gpow 0],
    dot (weights.take 6) ([sepMem, indexMle memoryLow, memoryCount] ++ memory),
    dot (weights.take 3) [sepBytecode, indexMle bytecodeLow, bytecodeCount] + bytecodeValue]

/-- One table block's form on a side: `side_beta` plus the block's fingerprint, one tuple slot at
a time (`verifier.py:633-635`). -/
def blockForm (block : BusBlock) (sideWeights : List E) (sideBeta : E) : Form :=
  block.coordinates.zipIdx.foldl
    (fun form (coordinate, slot) ↦ form.addScaled coordinate (sideWeights.getD slot 0))
    (Form.const sideBeta)

/-- One side of the leaf decomposition (`verifier.py:626-641`): the forms with the side's table
blocks added, and the side's total. A table's form is summed over its padding rows too, whose
leaves hold `1` instead: the difference, `padding_rows`, is public. -/
def accumulateSide (forms : List (List Form)) (side : ℕ) (blocks : List BusBlock)
    (sideLayout : BusLayout) (frameworkFingerprints sideWeights : List E) (sideBeta : E)
    (point : List E) (treeValue : E) : List (List Form) × E :=
  let frameworkSelectors := sideLayout.framework.map (·.eqAbove point)
  let tableSelectors := sideLayout.tables.map (·.eqAbove point)
  let known := dot frameworkSelectors (frameworkFingerprints.map (sideBeta + ·))
  let (forms, paddingRows) := (List.zip tableSelectors blocks).foldl
    (fun (forms, paddingRows) (selector, block) ↦
      let form := blockForm block sideWeights sideBeta
      let padding := (tables.getD block.owner default).padding
      (forms.modify block.owner fun row ↦ row.modify side fun f ↦ f.addScaled form selector,
        paddingRows + selector * paddingWeight (point.take block.logRows) block.rows *
          (form.evaluate (padding.getD · 0) + 1))) (forms, 0)
  let onesPadding := sumE (frameworkSelectors ++ tableSelectors) + 1
  (forms, treeValue + known + onesPadding + paddingRows)

/-- `verify_bus_balance(layout)` (`verifier.py:581-643`). **Where the verifier gets the value of the
fixed polynomial**, the stacked bytecode's multilinear extension at the bus point (`verifier.py:605`),
which the statement fixes and the proof does not: from `ev`, which the deployed verifier computes
(`computedValue`) and the verifier inside an aggregate takes from a claim it hands on
(`claimedValue`). -/
def verifyBusBalance (ev : List K → List E → Prog E) (layout : Layout) : Prog BusResult := do
  let frameworkLogRows := [0, layout.logMemory, layout.logBytecode]
  let pushLayout := busLayout frameworkLogRows layout.push
  let pullLayout := busLayout frameworkLogRows layout.pull
  let countLayout := busLayout [] layout.count
  let alphas ← Prog.sampleChallenges busBits
  let weights := eqKernel alphas
  let beta ← Prog.sampleChallenge
  let (countRoot, point, treeValues) ← verifyGkrGrandProducts pushLayout.depth
  Prog.require (countRoot ≠ 0)
  let memoryLow := point.take layout.logMemory
  let bytecodeLow := point.take layout.logBytecode
  let memory ← Prog.readScalars 3
  let memoryFinal ← Prog.readScalar
  let bytecodeFinal ← Prog.readScalar
  let claims : List ColumnClaim :=
    (List.zipWith (fun column value ↦ ⟨column, memoryLow, value⟩) [memory0, memory1, memory2]
      memory) ++
    [⟨memoryFinalCounters, memoryLow, memoryFinal⟩, ⟨bytecodeFinalCounters, bytecodeLow,
      bytecodeFinal⟩]
  let bytecodeValue ← ev layout.bytecode (bytecodeLow ++ alphas)
  let fp := fingerprints weights memory memoryLow bytecodeLow bytecodeValue
  let pcFinal := gpow (2 ^ layout.logBytecode - 1)
  let forms0 : List (List Form) := tables.map fun _ ↦ [{}, {}, {}]
  let (forms1, total0) := accumulateSide forms0 0 layout.push pushLayout (fp (gpow 0) 1 1)
    weights beta point (treeValues.getD 0 0)
  let (forms2, total1) := accumulateSide forms1 1 layout.pull pullLayout
    (fp pcFinal memoryFinal bytecodeFinal) weights beta point (treeValues.getD 1 0)
  let (forms3, total2) := accumulateSide forms2 2 layout.count countLayout [] [1] 0 point
    (treeValues.getD 2 0)
  return ⟨claims, point, forms3, [total0, total1, total2]⟩

/-!
## The table sumcheck (`verifier.py:649-678`)

One plain-mode sumcheck over `max` of the tables' log-heights, its challenges reversed the point;
the terminal claim is `Σ weight · (constraints + forms)`, and a table of log-height `h` has its
evaluations at the point's first `h` coordinates.
-/

/-- The tables' weights at the point (`verifier.py:662-666`): coordinate `v` contributes
`1 + equality_point[v] + r_v` to a table taller than `v`, and `r_v` to the others. -/
def tableWeights (heights : List ℕ) (equalityPoint point : List E) : List E :=
  point.zipIdx.foldl (fun weights (challenge, coord) ↦
    let equality := 1 + equalityPoint.getD coord 0 + challenge
    List.zipWith (fun weight height ↦ weight * if coord < height then equality else challenge)
      weights heights) (heights.map fun _ ↦ 1)

/-- The per-table loop of `table_sumcheck` (`verifier.py:668-676`): read each table's row
evaluations, add its weighted terms to `final`, and collect its point and evaluations. -/
def tableTerms (constraintPowers formPowers point : List E) :
    List (Table × ℕ × List Form × E) → ℕ → E → Prog (E × List (List E × List E))
  | [], _, final => return (final, [])
  | (table, height, forms, weight) :: rest, cursor, final => do
    let evaluations ← Prog.readScalars table.width
    let summand := dot ((constraintPowers.drop cursor).take table.nConstraints)
      (table.constraints evaluations)
    let final := final +
      weight * (summand + dot formPowers (forms.map (·.evaluate (evaluations.getD · 0))))
    let (final, rows) ← tableTerms constraintPowers formPowers point rest
      (cursor + table.nConstraints) final
    return (final, (point.take height, evaluations) :: rows)

/-- `table_sumcheck(table_log_heights, bus_forms, constraint_powers, form_powers,
equality_point, target)` (`verifier.py:649-678`): each table's point and its columns'
evaluations there. -/
def tableSumcheck (heights : List ℕ) (busForms : List (List Form))
    (constraintPowers formPowers equalityPoint : List E) (target : E) :
    Prog (List (List E × List E)) := do
  let nRounds := heights.foldl max 0
  let (challenges, claim) ← sumcheck target 4 (List.replicate nRounds none)
  let point := challenges.reverse
  let weights := tableWeights heights equalityPoint point
  let rows := List.zip tables (List.zip heights (List.zip busForms weights))
  let (final, evaluations) ← tableTerms constraintPowers formPowers point rows 0 0
  Prog.require (final = claim)
  return evaluations

/-!
## The WHIR opening (`verifier.py:1017-1203, 1454-1460`)

**Commitments.** The Python reads a Merkle root as two scalars (`Digest.from_halves(*next_scalars(2))`) and opens
it a level later with `merkle(root, block_length, queries, leaf_words)`. The language's
`commit height width` fixes the matrix shape when the root is read, so the shape is computed from
the ladder there:

* the stack's root (commitment `0`, read by `verify_execution` before the bus phase,
  `commitStack`) is opened at level `0`: `2^(log_n − folds[0] + rate_0)` leaves of
  `2^folds[0]` words;
* the root read at level `ℓ` (commitment `ℓ + 1`) is opened at level `ℓ + 1`:
  `2^(message_log_ℓ − folds[ℓ+1] + rate_{ℓ+1})` leaves of `3 · 2^folds[ℓ+1]` words.

Level `ℓ` therefore opens commitment `ℓ` (`Prog.queryOpenings ℓ`). The rows come back as raw words;
the level-0 reversal and the regrouping of deeper rows into `E` (`_ext_row`) are the program's.

**Interpretation.**

* `derive_config` is `LeanVM.Parameters.Whir.ladder`, whose `shape` is the Python's loop and
  whose table is `WHIR_QUERIES` verbatim; the tests compare all 56 admissible pairs with the
  Python.
* `sample_queries` takes the block's log-length `depth` (the Python takes the length and recovers
  `depth` by `log2_strict`, which cannot fail: the length is `2^depth`). Its loop is bounded by
  `count` rounds of fuel; each round yields `min(192 / depth, remaining) ≥ 1` positions since
  `depth ≤ 64`.
* `_induced_weight` requires `len(point) == message_log`. Every glued claim is evaluated at
  `folds[fold_start:] + tail_folds`, of length `log_n − fold_start = message_log`, so the check
  always holds; it is not repeated.
* The `raise` after the level loop (no terminal level) is `Prog.fail` on an empty ladder, which
  `derive_config` never returns.
-/

/-- The loop of `sample_queries`: each sample yields up to `192 / depth` positions of `depth`
bits, low bits first (`verifier.py:1062-1070`). -/
def sampleQueriesAux (depth : ℕ) : ℕ → ℕ → Prog (List ℕ)
  | 0, _ => return []
  | fuel + 1, remaining =>
    if remaining = 0 then return []
    else do
      let bits := eToNat (← Prog.sampleChallenge)
      let n := min (192 / depth) remaining
      let chunk := (List.range n).map fun c ↦ (bits >>> (c * depth)) % 2 ^ depth
      let rest ← sampleQueriesAux depth fuel (remaining - n)
      return chunk ++ rest

/-- `sample_queries(transcript, 2^depth, count)` (`verifier.py:1062-1070`). -/
def sampleQueries (depth count : ℕ) : Prog (List ℕ) := sampleQueriesAux depth count count

/-- `_ext_row(words)`: a deeper level's leaf words regrouped into the `E` values they encode,
three per lane (`verifier.py:1057-1059`). -/
def extRow : List K → List E
  | c0 :: c1 :: c2 :: rest => E.ofLimbs c0 c1 c2 :: extRow rest
  | [c0, c1] => [E.ofLimbs c0 c1 0]
  | [c0] => [E.ofLimbs c0 0 0]
  | [] => []

/-- `_enforced_sum(rows, folds, query_weights)`: `Σ_q w_q · ⟨row_q, eq(folds, ·)⟩`
(`verifier.py:1073-1078`). -/
def enforcedSum (rows : List (List E)) (folds queryWeights : List E) : E :=
  let laneWeights := eqKernel folds
  (List.zip queryWeights rows).foldl (fun total (w, row) ↦ total + w * dot row laneWeights) 0

/-- The layers of `_subspace_roots`: square-and-shift the layer by the last root, pop the next
root (`verifier.py:1084-1086`). -/
def subspaceRootsAux : ℕ → E → List E → List E
  | 0, _, _ => []
  | n + 1, last, layer =>
    match layer.map fun value ↦ value ^ 2 + last * value with
    | [] => []
    | root :: rest => root :: subspaceRootsAux n root rest

/-- `_subspace_roots(log_n)`: `1`, then the `log_n` subspace polynomial values
(`verifier.py:1081-1087`). -/
def subspaceRoots (logN : ℕ) : List E :=
  1 :: subspaceRootsAux logN 1 ((List.range logN).map fun i ↦ eOfNat (2 ^ (i + 1)))

/-- `_induced_weight(message_log, queries, query_weights, point)`: the level's batched query
claims as one weight at `point`, `Σ_q w_q Π_k (1 + p_k (1 + Ŵ_k(x_q)))`
(`verifier.py:1090-1108`). -/
def inducedWeight (messageLog : ℕ) (queries : List ℕ) (queryWeights point : List E) : E :=
  let roots := subspaceRoots messageLog
  let inverses := roots.map fun value ↦ if value = 0 then 0 else value⁻¹
  (List.zip queryWeights queries).foldl (fun total (weight, query) ↦
    let product := point.zipIdx.foldl (fun (acc : E × E) (challenge, coordinate) ↦
      (acc.1 * (1 + challenge * (1 + acc.2 * inverses.getD coordinate 0)),
        acc.2 ^ 2 + roots.getD coordinate 0 * acc.2)) (weight, eOfNat query)
    total + product.1) 0

/-- `GluedClaim`: a claim folded into the running sumcheck, and the weight it owes back
(`verifier.py:1111-1122`). -/
structure GluedClaim where
  /-- The power of the level's `λ` it was glued with. -/
  scalar : E
  /-- How many fold challenges preceded the level. -/
  foldStart : ℕ
  /-- Its weight at the terminal point, restricted to the level's message coordinates. -/
  weightAt : List E → E

/-! ### The level loop (`verifier.py:1125-1203`) -/

/-- The running state of `verify_whir`: `running_quad`, every fold challenge so far, and the glued
claims so far (`running_target` is the final level's tail rounds', `tailRounds`). -/
structure WhirState where
  quad : List E
  folds : List E
  glued : List GluedClaim

/-- A level's fold rounds: sample, fold the running claim, read the next quadratic
(`verifier.py:1137-1141`). Returns the state and the level's own challenges. -/
def foldRounds : ℕ → WhirState → List E → Prog (WhirState × List E)
  | 0, s, levelFolds => return (s, levelFolds)
  | n + 1, s, levelFolds => do
    let challenge ← Prog.sampleChallenge
    let quad ← sumcheckRoundPoly 3 (polyEval s.quad challenge) none
    foldRounds n { s with quad, folds := s.folds ++ [challenge] } (levelFolds ++ [challenge])

/-- The final level's tail rounds: sample, fold, and read the next quadratic unless it is the
last round (`verifier.py:1184-1190`). The tail challenges and the final running claim, which no
round leaves unset: the Python then raises at the terminal check. -/
def tailRounds : ℕ → List E → Prog (List E × E)
  | 0, _ => Prog.fail
  | n + 1, quad => do
    let challenge ← Prog.sampleChallenge
    let target := polyEval quad challenge
    if n = 0 then return ([challenge], target)
    else do
      let quad ← sumcheckRoundPoly 3 target none
      let (rest, target) ← tailRounds n quad
      return (challenge :: rest, target)

/-- Glue a level's pending claims, each an intro message and a weight, into the running sumcheck
with powers of `λ`, the running claim keeping `λ⁰` (`verifier.py:1175-1179`). -/
def glue (lam : E) (s : WhirState) (pending : List (List E × (List E → E))) : WhirState :=
  (pending.foldl (fun (acc : WhirState × E) (intro, weightAt) ↦
    let scalar := acc.2 * lam
    let s := acc.1
    ({ s with quad := List.zipWith (fun q i ↦ q + scalar * i) s.quad intro,
              glued := s.glued ++ [⟨scalar, s.folds.length, weightAt⟩] }, scalar)) (s, 1)).1

/-- The shape of the commitment a level opens: `2^(message_log + rate)` leaves of `width`
words, the message log being the one after the level's folds. -/
def levelShape (messageLogBefore : ℕ) (level : Whir.Level) (width : ℕ) : ℕ × ℕ :=
  (messageLogBefore - level.fold + level.logInvRate, width)

/-- One level of `verify_whir` and every level after it (`verifier.py:1135-1203`). `index` is
the level's index, which is also the index of the commitment it opens; `laneFolds` is
`config.folds[0]`. -/
def whirLevels (logN laneFolds : ℕ) (evaluateBasis : List E → E) :
    ℕ → List Whir.Level → WhirState → Prog Unit
  | _, [], _ => Prog.fail
  | index, level :: rest, s => do
    let (s, levelFolds) ← foldRounds level.fold s []
    let messageLog := logN - s.folds.length
    -- The level's claims: the residual on the final level; otherwise the next commitment and
    -- its out-of-domain claim.
    let (residual, pending) ← match rest with
      | [] => do
        let residual ← Prog.readScalars (2 ^ messageLog)
        pure (residual, ([] : List (List E × (List E → E))))
      | next :: _ => do
        let (height, width) := levelShape messageLog next (3 * 2 ^ next.fold)
        Prog.readCommitment height width
        let oodPoint ← Prog.sampleChallenges messageLog
        let oodValue ← Prog.readScalar
        let intro ← sumcheckRoundPoly 3 oodValue none
        pure ([], [(intro, fun x ↦ eqEval oodPoint x)])
    Prog.grindProofOfWork Whir.queryGrindingBits
    let queries ← sampleQueries (messageLog + level.logInvRate) level.queries
    let lam ← Prog.sampleChallenge
    let queryWeights := powers lam queries.length
    let words ← Prog.queryOpenings index queries
    let rows : List (List E) :=
      if index = 0 then words.map fun row ↦ row.reverse.map ofK else words.map extRow
    let enforced := enforcedSum rows levelFolds queryWeights
    let intro ← sumcheckRoundPoly 3 enforced none
    let pending := pending ++ [(intro, fun x ↦ inducedWeight messageLog queries queryWeights x)]
    let s := glue lam s pending
    match rest with
    | [] => do
      let (tailFolds, target) ← tailRounds messageLog s.quad
      let point := s.folds ++ tailFolds
      let weight := s.glued.foldl
        (fun weight claim ↦
          weight + claim.scalar * claim.weightAt (s.folds.drop claim.foldStart ++ tailFolds))
        (evaluateBasis (point.drop laneFolds ++ point.take laneFolds))
      let terminal := weight * multilinearEval residual tailFolds
      Prog.require (terminal = target)
    | _ :: _ => whirLevels logN laneFolds evaluateBasis (index + 1) rest s

/-- `verify_whir(log_n, log_inv_rate, target, root, evaluate_basis)`, the root being commitment
`0` (`verifier.py:1125-1203`). -/
def verifyWhir (logN logInvRate : ℕ) (target : E) (evaluateBasis : List E → E) : Prog Unit := do
  let config ← liftOption (Whir.ladder logN logInvRate)
  let quad ← sumcheckRoundPoly 3 target none
  whirLevels logN ((config.head?.map (·.fold)).getD 0) evaluateBasis 0 config ⟨quad, [], []⟩

/-- Read the stack's root (`verify_execution`, step 2, `verifier.py:1478`): commitment `0`, the
shape level `0` opens it at. -/
def commitStack (logN logInvRate : ℕ) : Prog Unit := do
  let config ← liftOption (Whir.ladder logN logInvRate)
  match config with
  | [] => Prog.fail
  | level :: _ =>
    let (height, width) := levelShape logN level (2 ^ level.fold)
    Prog.readCommitment height width

/-- `verify_stacked_opening(root, stack_log, log_inv_rate, claims)`: batch the claims with powers
of one challenge into one WHIR opening (`verifier.py:1454-1460`). -/
def verifyStackedOpening (stackLog logInvRate : ℕ) (claims : List StackClaim) : Prog Unit := do
  let scales := powers (← Prog.sampleChallenge) claims.length
  verifyWhir stackLog logInvRate (dot scales (claims.map (·.2)))
    fun point ↦ dot scales (claims.map fun c ↦ c.1 point)

/-!
## Keccak, by GKR over its rounds (`verifier.py:1206-1406`)

The protocol is `doc/leanvm/body/c-keccak-gkr.tex`; `KECCAK_RC`, `KECCAK_RHO`, `KECCAK_PI` are
`keccakRC`, `keccakRho`, `keccakPi` of `RandomPermutation.lean`. A claim is a weighted sum of the
bits of one state per segment, the weight of bit `j` of instance `i` of pack `y` (sixteen
consecutive steps) in segment `m` being `eq(point, (y, m)) · weights[j] · mu[i]`; each layer turns
a claim on the states after a round into one on the states before it.

**Representation.**

* The Python's integer polynomials over `GF(2)` (`_carryless`, `_carryless_divmod`, `_rmfe`) are
  natural numbers, bit `i` the coefficient of `x^i`, as in the Python. Their loops are bounded by
  fuel: `carryless a b` by `b` (each step halves `b`), `carrylessDivmod a f` by the bit length of
  `a` plus one (each step lowers the bit length of the remainder when `f ≠ 0`; the Python loops
  forever at `f = 0`, which it never passes).
* The Python's `next(g for g in range(1, 2**degree) if …)` is `List.find?`, `0` if none (the
  Python raises; every factor of `RMFE_FACTORS` is irreducible, so one is found).
* The mutable arrays of `keccak_linear_transpose` and of `_keccak_open`'s slot weights are arrays here,
  set where the Python sets them.
-/

/-! ### Constants (`verifier.py:1224-1228`) -/

/-- `EMBED_BITS`: a pack's bits embed in a polynomial of `24` coefficients. -/
def embedBits : ℕ := 24

/-- `PRODUCT_BITS = 2 · EMBED_BITS − 1`: the product of two embeddings has `47` coefficients. -/
def productBits : ℕ := 2 * embedBits - 1

/-- `RMFE_FACTORS`: the moduli the embedding is glued from, with the bits each holds. -/
def rmfeFactors : List (ℕ × ℕ) :=
  [(0b10, 1), (0b11, 1), (0b1011, 2), (0b1101, 2), (0b100101, 3), (0b101001, 3), (0b101111, 3)]

/-! ### The embedding (`verifier.py:1231-1275`) -/

/-- The loop of `_carryless`: while `b`, add `a` if `b`'s low bit is set, then shift. -/
def carrylessAux : (fuel a b out : ℕ) → ℕ
  | 0, _, _, out => out
  | fuel + 1, a, b, out =>
    if b = 0 then out
    else carrylessAux fuel (a <<< 1) (b >>> 1) (if b % 2 = 1 then out ^^^ a else out)

/-- `_carryless(a, b)`: the product of two binary polynomials (`verifier.py:1231-1237`). -/
def carryless (a b : ℕ) : ℕ := carrylessAux b a b 0

/-- The loop of `_carryless_divmod`: while the remainder is nonzero and no shorter than `f`,
subtract `f` shifted under its leading bit. -/
def carrylessDivmodAux : (fuel f quotient a : ℕ) → ℕ × ℕ
  | 0, _, quotient, a => (quotient, a)
  | fuel + 1, f, quotient, a =>
    if a ≠ 0 ∧ bitLength f ≤ bitLength a then
      let shift := bitLength a - bitLength f
      carrylessDivmodAux fuel f (quotient ||| (1 <<< shift)) (a ^^^ (f <<< shift))
    else (quotient, a)

/-- `_carryless_divmod(a, f)`: the quotient and remainder of binary polynomials
(`verifier.py:1240-1246`). -/
def carrylessDivmod (a f : ℕ) : ℕ × ℕ := carrylessDivmodAux (bitLength a + 1) f 0 a

/-- `int.bit_count() & 1`: the parity of the set bits. -/
def bitParity (n : ℕ) : ℕ := ((List.range (bitLength n)).countP fun i ↦ n.testBit i) % 2

/-- The product of the moduli, `reduce(_carryless, (f for f, _ in RMFE_FACTORS))`
(`verifier.py:1253`). -/
def rmfeModulus : ℕ :=
  match rmfeFactors.map Prod.fst with
  | [] => 0
  | f :: fs => fs.foldl carryless f

/-- One factor's share of `_rmfe` (`verifier.py:1255-1270`): its bits' embeddings (the residues,
lifted through the Chinese remainder theorem), and per bit the projection's mask, the product
coefficients whose parity is the bit. -/
def rmfeFactor (modulus f bits : ℕ) : List ℕ × List ℕ :=
  let cofactor := (carrylessDivmod modulus f).1
  let degree := bitLength f - 1
  let inverse := (((List.range (2 ^ degree)).drop 1).find? fun g ↦
    (carrylessDivmod (carryless (carrylessDivmod cofactor f).2 g) f).2 = 1).getD 0
  let lift := (carrylessDivmod (carryless cofactor inverse) modulus).2
  -- A residue is the polynomial taking the bits as its values at 0, 1 and infinity.
  let residues : List ℕ := if bits = 1 then [1] else if bits = 2 then [0b11, 0b10]
    else [0b011, 0b010, 0b110]
  let embed := residues.map fun r ↦ (carrylessDivmod (carryless lift r) modulus).2
  let masks := (List.range productBits).foldl (fun masks c ↦
    let g := (carrylessDivmod (1 <<< c) f).2
    let atZero := g % 2
    let atOne := bitParity g
    let values : List ℕ := if bits = 1 then [if f = 0b10 then atZero else atOne]
      else if bits = 2 then [atZero, atOne] else [atZero, atOne, g >>> 4]
    List.zipWith (fun mask value ↦ mask ||| (value <<< c)) masks values)
    (List.replicate bits 0)
  (embed, masks)

/-- `_rmfe()` (`verifier.py:1249-1272`): sixteen bits embed in a binary polynomial of degree at
most `23`, and a product of two embeddings projects to the AND of what they embed. Each unit
vector's embedding, and per bit of the projection the product coefficients it is the parity of;
the last bit rides the leading coefficient, which the residues do not see. -/
def rmfe : List ℕ × List ℕ :=
  let (embed, project) := rmfeFactors.foldl (fun (acc : List ℕ × List ℕ) (f, bits) ↦
    let (e, p) := rmfeFactor rmfeModulus f bits
    (acc.1 ++ e, acc.2 ++ p)) ([], [])
  (embed ++ [rmfeModulus], project ++ [1 <<< (productBits - 1)])

/-- `RMFE_EMBED` (`verifier.py:1275`). -/
def rmfeEmbed : List ℕ := rmfe.1

/-- `RMFE_PROJECT` (`verifier.py:1275`). -/
def rmfeProject : List ℕ := rmfe.2

/-! ### Claims and the round's linear map (`verifier.py:1278-1309`) -/

/-- `KeccakClaim`: a claim's value, the weight of each instance of a pack, its point (a pack
index, then a segment index), and the weight of each bit position. -/
structure KeccakClaim where
  value : E
  mu : List E
  point : List E
  weights : List E
  deriving Inhabited

/-- `keccak_along(j, k)`: the position `k` columns along from `j`, in the same row and slice
(`verifier.py:1286-1289`). -/
def keccakAlong (j k : ℕ) : ℕ :=
  let lane := j / 64
  let z := j % 64
  64 * ((lane % 5 + k) % 5 + 5 * (lane / 5)) + z

/-- `keccak_linear_transpose(w)` (`verifier.py:1292-1303`): the transpose of θ, ρ, π on weight
vectors, `⟨w, L(a)⟩ = ⟨Lᵀ(w), a⟩`. `g` is the weight each position of θ's output carries. -/
def keccakLinearTranspose (w : List E) : List E :=
  let w := w.toArray
  let g : Array E := (List.range 25).foldl (fun g lane ↦ (List.range 64).foldl (fun g z ↦
    g.setIfInBounds (64 * lane + z)
      (w.getD (64 * keccakPi lane + (z + keccakRho.getD lane 0) % 64) 0)) g)
    (Array.replicate keccakBits 0)
  let columns : Array E := ((List.range 5).flatMap fun x ↦ (List.range 64).map fun z ↦
    sumE ((List.range 5).map fun y ↦ g.getD (64 * (x + 5 * y) + z) 0)).toArray
  (List.range 25).flatMap fun lane ↦ (List.range 64).map fun z ↦
    g.getD (64 * lane + z) 0 + columns.getD (64 * ((lane % 5 + 1) % 5) + z) 0 +
      columns.getD (64 * ((lane % 5 + 4) % 5) + (z + 1) % 64) 0

/-- `keccak_instance_weights(s)` (`verifier.py:1306-1309`): the instance weights of a claim made
at the polynomial point `s`, each unit vector's embedding at `s`. -/
def keccakInstanceWeights (s : E) : List E :=
  let sPowers := powers s embedBits
  rmfeEmbed.map fun e ↦
    sumE ((List.range embedBits).filterMap fun b ↦
      if e.testBit b then some (sPowers.getD b 0) else none)

/-! ### A layer (`verifier.py:1312-1355`) -/

/-- Step 3 of a layer, the pack and the segment (`verifier.py:1333-1340`): an equality-mode round
per coordinate of the claim's point, the value scaled by `1 + r + challenge`. The new value, the
product of the scales, and the challenges. -/
def keccakPackRounds : List E → E → E → Prog (E × E × List E)
  | [], value, scale => return (value, scale, [])
  | r :: rs, value, scale => do
    let message ← sumcheckRoundPoly 3 value (some r)
    let challenge ← Prog.sampleChallenge
    let (value, scale, point) ← keccakPackRounds rs
      ((1 + r + challenge) * polyEval message challenge) (scale * (1 + r + challenge))
    return (value, scale, challenge :: point)

/-- `verify_keccak_layer(log_steps, step, claim)` (`verifier.py:1312-1355`): a claim on the
states `step` layers below the committed outputs becomes one on the states a layer further
down. -/
def verifyKeccakLayer (logSteps step : ℕ) (claim : KeccakClaim) : Prog KeccakClaim := do
  let packBits := logSteps - 4
  -- 1] The product polynomial: the claim's weighted sum of the packs' unprojected chi.
  let product ← Prog.readScalars productBits
  let projected := sumE ((List.range productBits).map fun c ↦
    sumE ((List.zip claim.mu rmfeProject).filterMap fun (m, mask) ↦
      if mask.testBit c then some m else none) * product.getD c 0)
  -- iota flips known positions of lane 0 in every instance.
  let segments := eqKernel (claim.point.drop packBits)
  let iota := sumE ((List.range keccakSegments).map fun segment ↦
    let constant := keccakRC.getD (keccakDepth * (segment + 1) - step - 1) 0
    segments.getD segment 0 * sumE ((List.range 64).filterMap fun z ↦
      if constant.toNat.testBit z then some (claim.weights.getD z 0) else none))
  Prog.require (projected + iota * sumE claim.mu = claim.value)
  -- 2] At a random point a pack is one field element, and the polynomial's value a sumcheck
  -- claim.
  let s ← Prog.sampleChallenge
  let mu := keccakInstanceWeights s
  let kappa := sumE mu
  -- 3] The pack and the segment.
  let (value, scale, point) ← keccakPackRounds claim.point (polyEval product s) 1
  -- 4] The bit position: `Σ_j w[j] (κ T[j] + (κ + T[j + 1]) T[j + 2])`.
  let (localPoint, value) ← sumcheck value 4 (List.replicate keccakLocalBits none)
  let t ← Prog.readScalars 3
  let eq := eqKernel localPoint
  let t0 := t.getD 0 0
  let t1 := t.getD 1 0
  let t2 := t.getD 2 0
  Prog.require
    (scale * dot (eq.take keccakBits) claim.weights * (kappa * t0 + (kappa + t1) * t2) = value)
  -- 5] `t[k] = Σ_j eq[j] T[j + k]`: one claim on the state before chi, then on the round's
  -- input through the linear map.
  let beta ← Prog.sampleChallenge
  let weights := (List.range keccakBits).map fun j ↦
    eq.getD j 0 + beta * (eq.getD (keccakAlong j 4) 0 + beta * eq.getD (keccakAlong j 3) 0)
  return ⟨t0 + beta * (t1 + beta * t2), mu, point, keccakLinearTranspose weights⟩

/-- The layers, `for step in range(KECCAK_DEPTH)` (`verifier.py:1391-1392`). -/
def keccakLayers (logSteps : ℕ) : List ℕ → KeccakClaim → Prog KeccakClaim
  | [], claim => return claim
  | step :: steps, claim => do
    let claim ← verifyKeccakLayer logSteps step claim
    keccakLayers logSteps steps claim

/-! ### Opening `q_keccak` (`verifier.py:1358-1406`) -/

/-- The weights of `_keccak_open` (`verifier.py:1363-1367`): the weight a claim puts on each
`(slot, z)`, its position weights on the slots of the states it speaks of, scaled by the segment; `first` is the state segment `0` claims, and only the first `count`
segments' states are committed. The slots above the states (`qkeccakSlots …`), which carry
`KECCAK` columns, weigh nothing. -/
def keccakSlotWeights (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ) : List (List E) :=
  let segments := eqKernel (claim.point.drop (logSteps - 4))
  let weights := claim.weights.toArray
  let rows : Array (Array E) := (List.range count).foldl (fun rows segment ↦
    (List.range keccakBits).foldl (fun rows j ↦
      rows.modify (25 * (first + segment) + j / 64) fun row ↦
        row.setIfInBounds (j % 64) (segments.getD segment 0 * weights.getD j 0)) rows)
    (Array.replicate (2 ^ qkeccakSlotBits) (Array.replicate 64 0))
  rows.toList.map Array.toList

/-- `_keccak_open(log_steps, claim, first, count, value)` (`verifier.py:1358-1370`): a sumcheck
over the slot; the point it ends on, the weight the claim puts on each slice there, and what is
left to match. The sumcheck draws nothing from the weights, so computing them after it, as the
pin does, or before is the same. -/
def keccakOpen (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ) (value : E) :
    Prog (List E × List E × E) := do
  let (slot, value) ← sumcheck value 3 (List.replicate qkeccakSlotBits none)
  let rows := slot.foldl (fun rows challenge ↦
    (List.range (rows.length / 2)).map fun i ↦
      List.zipWith (fun lo hi ↦ lo + challenge * (lo + hi)) (rows.getD (2 * i) [])
        (rows.getD (2 * i + 1) [])) (keccakSlotWeights logSteps claim first count)
  return (slot, rows.headD [], value)

/-- `verify_keccak(log_steps, instance, output)` (`verifier.py:1373-1406`): the reduction, a
random claim on every segment's output at `instance`, `KECCAK_DEPTH` layers down to the committed
inputs. The last segment's output is the permutation's, claimed by the table's lanes `output` at
`instance`; the others are committed. It leaves openings of `q_keccak`: the committed outputs as
words at one point (column claims), and the column's 64 slices at another (the point and the
slices, for ring switching). -/
def verifyKeccak (logSteps : ℕ) (inst output : List E) :
    Prog (List ColumnClaim × List E × List E) := do
  let packBits := logSteps - 4
  let rLow := inst.take 4
  let segment ← Prog.sampleChallenges keccakSegmentBits
  let point := inst.drop 4 ++ segment
  -- The first claim combines the output lanes as words: bit `z` of a word weighs `x^z`.
  let lanes := eqKernel (← Prog.sampleChallenges keccakLaneBits)
  let weights := (List.range keccakBits).map fun j ↦ lanes.getD (j / 64) 0 * eOfNat (2 ^ (j % 64))
  let last := (eqKernel segment).getD (keccakSegments - 1) 0 * dot (lanes.take 25) output
  let committed ← if 1 < keccakSegments then Prog.readScalar else pure 0
  let first : KeccakClaim := ⟨committed + last, eqKernel rLow, point, weights⟩
  let claim ← keccakLayers logSteps (List.range keccakDepth) first
  -- The committed outputs, whose instance weights are an eq already: slice 0 holds the slot's
  -- weight, the others `x^z` times it.
  let outputs ← if 1 < keccakSegments then do
      let (slot, weights, value) ← keccakOpen logSteps first 1 (keccakSegments - 1) committed
      let word ← Prog.readScalar
      Prog.require (weights.headD 0 * word = value)
      pure [(⟨qkeccak, rLow ++ inst.drop 4 ++ slot, word⟩ : ColumnClaim)]
    else pure []
  -- The inputs: the instances of a pack first, then the slot.
  let (low, value) ← sumcheck claim.value 3 (List.replicate 4 none)
  let (slot, weights, value) ← keccakOpen logSteps claim 0 keccakSegments value
  let slices ← Prog.readScalars kBits
  Prog.require (multilinearEval claim.mu low * dot weights slices = value)
  return (outputs, low ++ claim.point.take packBits ++ slot, slices)

/-!
## Ring switching (`verifier.py:1409-1445`)

The 64 claims `s[i] = z(i, point)` on `q_keccak`'s bit slices become one dense claim
`Σ_u W(u) q_keccak(u) = target` on the committed column.
-/

/-- `RING_MAP_SHIFTS` (`verifier.py:1412`; `COMPOSITION_SHIFTS`, `crates/pcs/src/ring_switch.rs:80`):
the Frobenius shifts of the six stages composing `Φ`, one challenge each. -/
def ringMapShifts : List ℕ := [32, 16, 8, 4, 2, 1]

/-- `_phi(value, challenges)`: `a ↦ a + f_p · a^(2^shift)`, stage by stage
(`verifier.py:1415-1419`). -/
def phiMap (value : E) (challenges : List E) : E :=
  (List.zip challenges ringMapShifts).foldl
    (fun value (challenge, shift) ↦ value + challenge * value ^ (2 ^ shift)) value

/-- `_ring_weight(r, r_prime, coefficients)`: `Σ_k c_k Π_n (1 + r_n^(2^k) + r'_n)`
(`verifier.py:1422-1433`). -/
def ringWeight (r rPrime coefficients : List E) : E :=
  (coefficients.foldl (fun (acc : E × List E) c ↦
    let product := (List.zip acc.2 rPrime).foldl
      (fun product (value, challenge) ↦ product * (1 + value + challenge)) c
    (acc.1 + product, acc.2.map (· ^ 2))) (0, r)).1

/-- The Frobenius coefficients of the drawn map, `Φ(a) = Σ_{k < 64} c_k a^(2^k)`
(`verifier.py:1443`). -/
def ringCoefficients (challenges : List E) : List E :=
  (List.range kBits).map fun k ↦
    ((List.zip challenges ringMapShifts).filter fun (_, s) ↦ k &&& s ≠ 0).foldl
      (fun acc (f, s) ↦ acc * f ^ (2 ^ (k % s))) 1

/-- `ring_switch(point, s)` (`verifier.py:1436-1445`): draw the map, and return the target
`Σ_i g^i Φ(s_i)` and the weight `W(u) = Φ(eq(point, u))` as a function of the opening point. -/
def ringSwitch (point s : List E) : Prog (E × (List E → E)) := do
  let challenges ← Prog.sampleChallenges ringMapShifts.length
  let coefficients := ringCoefficients challenges
  let target := polyEval (s.map (phiMap · challenges)) gen
  return (target, fun rPrime ↦ ringWeight point rPrime coefficients)

open LeanVM.Semantics LeanVM.Protocol.KeccakHash

/-!
## The leanVM verifier (`verifier.py:684, 1463-1517, 379-384`)

`leanVmProgram bytecode publicInput` is `verify_execution` in the verifier language, one `Prog`
function per phase of the Python (the steps of `verifyExecution`). The program returns `true` where
the Python returns; `Transcript.finish`, the check that the proof is consumed, is `runProof`'s.

**The seed.** The sponge starts at Keccak-f of `IV ‖ public_input ‖ 0^17`, `IV` the Keccak-256
hash of `TAG ‖ bytecode`, the tag `"leanvm-v1"` naming the proof system's version and the bytecode
as its little-endian words. The seed's input has the capacity lanes zero, Keccak-256's initial state, and
nothing separates its domain from a Keccak-256 block: in the random-permutation model the
transcript's duplex calls and Keccak-256's sponge calls query the one permutation from states of
the same kind. This is harmless for the end statements, which are proved for exactly this
experiment.
-/

/-- The announced sizes, read and checked, and the layout they give
(`verifier.py:1467-1475`): the layout and the WHIR rate exponent. -/
def readSizes (bytecode : List K) : Prog (Layout × ℕ) := do
  let announced ← Prog.readScalars (2 + tables.length)
  Prog.require (announced.all fun value ↦ value.limb 1 = 0 ∧ value.limb 2 = 0)
  let logMemory := kToNat ((announced.headD 0).limb 0)
  let tableRows := ((announced.drop 1).take tables.length).map fun value ↦ kToNat (value.limb 0)
  let logInverseRate := kToNat ((announced.getLastD 0).limb 0)
  Prog.require (1 ≤ logInverseRate ∧ logInverseRate ≤ 4)
  let layout ← liftOption (buildLayout bytecode logMemory tableRows)
  Prog.require (Whir.minLogStack ≤ layout.stackLog ∧ layout.stackLog ≤ Whir.maxLogStack)
  return (layout, logInverseRate)

/-- Step 4, the table sumcheck at the bus point (`verifier.py:1483-1489`): each table's point and
evaluations. -/
def tablePhase (layout : Layout) (bus : BusResult) : Prog (List (List E × List E)) := do
  let xi ← Prog.sampleChallenge
  let nConstraints := (tables.map Table.nConstraints).sum
  let xiPowers := powers xi (nConstraints + 3)
  let constraintPowers := xiPowers.take nConstraints
  let formPowers := xiPowers.drop nConstraints
  let target := dot formPowers bus.totals
  tableSumcheck layout.tableLogHeights bus.forms constraintPowers formPowers bus.point target

/-- Step 5, binding the public input (`verifier.py:1495-1501`): a challenge, and claims on the
three memory columns at `(challenge, 0, …, 0)`, each limb's claim the line through that limb of
the public input's two halves, evaluated at the challenge by the verifier itself. The prover sends
nothing. -/
def publicInputPhase (layout : Layout) (publicInput : Digest) : Prog (List ColumnClaim) := do
  let publicChallenge ← Prog.sampleChallenge
  let halves := digestScalars publicInput
  let publicLimbs := ([0, 1, 2] : List (Fin 3)).map fun limb ↦
    multilinearEval [ofK (halves.1.limb limb), ofK (halves.2.limb limb)] [publicChallenge]
  let publicPoint := publicChallenge ::
    List.replicate ((layout.placement memory0).vars - 1) 0
  return List.zipWith (fun column value ↦ ⟨column, publicPoint, value⟩)
    [memory0, memory1, memory2] publicLimbs

/-- Step 6, `KECCAK`'s validity (`verifier.py:1503-1507`): the `KECCAK` table's point and its
output lanes' evaluations, `values[KECCAK_OUT : KECCAK_OUT + STATE_LANES]`, are the Keccak
reduction's claim on the permutation's output. The reduction's column claims, and the point and
slices of `q_keccak` it leaves for ring switching. -/
def keccakPhase (layout : Layout) (evaluations : List (List E × List E)) :
    Prog (List ColumnClaim × List E × List E) :=
  let (point, values) := evaluations.getD opKeccak ([], [])
  verifyKeccak (layout.tableLogHeights.getD opKeccak 0) point
    (keccakOutputs.map fun name ↦ values.getD (colIdx keccakColumns name) 0)

/-- Step 7's ring-switching claim on the stack: supported on `q_keccak`'s region, its weight
carries the placement's selector (`verifier.py:1512-1514`). -/
def ringSwitchClaim (layout : Layout) (target : E) (weight : List E → E) : StackClaim :=
  let qkeccakPlacement := layout.placement qkeccak
  (fun x ↦ qkeccakPlacement.eqAbove x * weight (x.take qkeccakPlacement.vars), target)

/-- `verify_execution(bytecode, public_input, proof)` without its `finish`
(`verifier.py:1463-1516`), the fixed polynomial's value from `ev`. -/
def verifyExecution (ev : List K → List E → Prog E) (bytecode : List K) (publicInput : Digest) :
    Prog Unit := do
  -- 1] memory log-size, table row counts, and the WHIR rate
  let (layout, logInverseRate) ← readSizes bytecode
  -- 2] the stack's commitment
  commitStack layout.stackLog logInverseRate
  -- 3] the bus
  let bus ← verifyBusBalance ev layout
  -- 4] the table sumcheck, and the tables' column claims
  let evaluations ← tablePhase layout bus
  let claims := bus.claims ++ (globalColumnBases.zip evaluations).flatMap fun (base, point, values) ↦
    values.zipIdx.map fun (value, column) ↦ ⟨base + column, point, value⟩
  -- 5] the public input
  let publicClaims ← publicInputPhase layout publicInput
  let claims := claims ++ publicClaims
  -- 6] KECCAK validity, by GKR over the rounds
  let (outputs, keccakPoint, keccakSlices) ← keccakPhase layout evaluations
  let claims := claims ++ outputs
  -- 7] ring switching, then one opening of the stack for every claim with a placement
  let (ringTarget, ringWeight) ← ringSwitch keccakPoint keccakSlices
  verifyStackedOpening layout.stackLog logInverseRate
    (ringSwitchClaim layout ringTarget ringWeight :: claims.filterMap (·.onStack layout))

/-! ### The fixed polynomial's value -/

/-- The deployed verifier computes the fixed polynomial's value. -/
def computedValue (words : List K) (point : List E) : Prog E :=
  pure (multilinearEval (words.map ofK) point)

/-- What a proof claims of the fixed polynomial, for a verifier that does not evaluate it: the
bytecode's value at its point. -/
structure BytecodeClaim where
  bytecodePoint : List E
  bytecodeValue : E

/-- The value claimed by `c`, at the point of `c` only: the run fails where the verifier asks
elsewhere. -/
def claimedValue (c : BytecodeClaim) (_ : List K) (point : List E) : Prog E := do
  Prog.require (point = c.bytecodePoint)
  return c.bytecodeValue

/-- The claim is true of `bytecode`. -/
def BytecodeClaim.Holds (bytecode : List K) (c : BytecodeClaim) : Prop :=
  multilinearEval (bytecode.map ofK) c.bytecodePoint = c.bytecodeValue

/-! ### The programs -/

/-- **The leanVM verifier program**: `verify_execution` in the verifier language, accepting
where the Python returns. -/
def leanVmProgram (bytecode : List K) (publicInput : Digest) : Prog Bool := do
  verifyExecution computedValue bytecode publicInput
  return true

/-- The verifier program with the fixed polynomial's value claimed by `c`. -/
def deferredProgram (c : BytecodeClaim) (bytecode : List K) (publicInput : Digest) : Prog Bool := do
  verifyExecution (claimedValue c) bytecode publicInput
  return true

/-! ### The seed and the compiled verifier -/

/-- `TAG`, the proof system's version (`verifier.py:684`, `crates/verifier/src/layout.rs:68`), as
bytes. -/
def versionTag : Bytes := "leanvm-v1".toUTF8.toList

section Hash

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- The IV over the permutation `F`: Keccak-256 over `F` of the tag, then the bytecode as its
little-endian words (`verifier.py:1464`). -/
def fiatShamirIvWith (bytecode : List K) : m Digest :=
  keccak256With F (versionTag ++ bytecode.flatMap kBytes)

/-- The sponge's initial state over the permutation `F`: `F` of the IV's and the public input's
words, the other lanes zero (`verifier.py:1464-1465`, `Transcript.__init__`). -/
def seedWith (bytecode : List K) (publicInput : Digest) : m KeccakState := do
  let fiatShamirIv ← fiatShamirIvWith F bytecode
  F (seedInput fiatShamirIv publicInput)

/-- The compiled verifier over the permutation `F`: the program run on the proof from the seed. -/
def verifyWith (bytecode : List K) (publicInput : Digest) (π : Proof) : m Bool := do
  let seed ← seedWith F bytecode publicInput
  runProof F (leanVmProgram bytecode publicInput) seed π

/-- **The deferring verifier** over the permutation `F`, as an aggregate runs it on a child's proof
(`verify_sub`): the IV is given rather than hashed from the bytecode, and the fixed polynomial's
value is the one claimed by `c`. Only the bytecode's length is read. -/
def verifyDeferredWith (bytecode : List K) (iv publicInput : Digest) (c : BytecodeClaim)
    (π : Proof) : m Bool := do
  let seed ← F (seedInput iv publicInput)
  runProof F (deferredProgram c bytecode publicInput) seed π

end Hash

/-- The deployed IV, over Keccak-f[1600]. -/
def fiatShamirIv (bytecode : List K) : Digest :=
  Id.run (fiatShamirIvWith (m := Id) keccakF1600 bytecode)

/-- The deployed deferring verifier, over Keccak-f[1600]. -/
def verifyDeferred (bytecode : List K) (iv publicInput : Digest) (c : BytecodeClaim) (π : Proof) :
    Bool :=
  Id.run (verifyDeferredWith (m := Id) keccakF1600 bytecode iv publicInput c π)

/-- The announced layout and rate exponent of a stream, read by the program's own `readSizes`
(reads only absorb: no hash or permutation is consulted for a value). -/
def announced (bytecode : List K) (stream : List E) : Option (Layout × ℕ) :=
  (runPure (readSizes bytecode) ⟨⟨default, []⟩, stream, [], []⟩).map (·.1)

end LeanVM.Protocol.Verifier

end
