import LeanerVM.Protocol.Verify
import LeanerVMTests.Protocol.RustProof

/-!
# The verifier on the Rust proof, and its mutations

`verify` accepts the proof the pinned Rust prover made of the division program
(`scripts/dump-proof-rust.sh`, leanVM `a386121f84292f6fa663aaa3e570c15bc0240ea2`): the setup's
checks, the chain walk, the four Merkle openings, the stream and openings consumed, and the
algebra of every phase, WHIR's terminal check last.

**Where a proof is rejected.** `outcome` reruns `verify`'s stages on the fixture's program and
input and names the first that rejects: the setup, the openings' shapes, a read of the chain walk
or of the openings (with the reader's error), or a phase of the algebra. `mutations` lists the
mutations of the proof with the outcome each must have, and `statementMutations` the proof
against a changed input lane or instruction. A scalar changed before a level's
grinding nonce moves the chain, so that level's grinding check rejects it before any algebra
runs; only the last level's query message and tail rounds, read after the last grinding check,
reach the algebra through the stream. The phases' own checks are exercised on the honest wire
instead: `VerifyBus.lean`, `VerifyTables.lean`, `VerifyFlock.lean`, and `whirChecks` below for
WHIR, at the last level and at the levels before it.

Interpreted, a run of `verify` that hashes the whole proof takes over a minute, so this module
checks the honest proof and the mutations rejected before the chain walk passes its setup's
reads (`cheap`); the `leanervm-verify` executable (`bench/LeanerVMVerify.lean`) runs every
mutation compiled, checks its outcome, and runs `whirChecks`.
-/

namespace LeanerVMTests.Protocol.Verify

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Protocol LeanerVM.Protocol.Blake2sHash
open LeanerVM.Protocol.LeanIsa LeanerVM.Protocol.Verify LeanerVMTests.Protocol.RustProof

/-- `verify` on the fixture's program and input, the proof changed by `f`. -/
def verifies (f : Proof PrunedMerklePaths → Proof PrunedMerklePaths) : Bool :=
  let fx := fx
  verify fx.prog fx.input (f fx.proof)

/-! ## Where `verify` rejects -/

/-- The stage of `verify` that rejects a proof, or acceptance. -/
inductive Outcome where
  /-- The announced sizes, the caps and the windows. -/
  | setup
  /-- The number and shapes of the openings. -/
  | openings
  /-- A read of the chain walk or of the openings, or the stream and openings consumed. -/
  | read (e : ReadError)
  /-- The bus phase's algebra. -/
  | bus
  /-- The table sumcheck's algebra. -/
  | table
  /-- The public input's check. -/
  | pub
  /-- The Flock phase's algebra. -/
  | flock
  /-- WHIR's algebra and terminal check. -/
  | whir
  /-- Accepted. -/
  | accepted
  deriving DecidableEq, Repr

/-- `algebra`'s phases, naming the first that rejects. -/
def algebraOutcome (prog : Program) (s : Sizes) (input : PublicInput) (shs : List LevelShape)
    (w : Wire) (rows : List (List (List K))) : Outcome :=
  let I := leanVm prog s
  match leanVmBus prog s input w.bus with
  | none => .bus
  | some b =>
    match tableStep I b w.table with
    | none => .table
    | some t =>
      match pubStep I t w.pub with
      | none => .pub
      | some p =>
        match flockStep I (flockRegion prog s Blake2sFlock.blake2sFlockSpec) rfl blake2sRows
          p w.flock with
        | none => .flock
        | some f =>
          let (W, target) := openingClaim I f w.lam
          if whirCheck I.μ shs W target w.whirFirst w.whir rows then .accepted else .whir

/-- `verify`'s stages on the program `prog` and the input `input`, naming the first that rejects
`p`. -/
def outcomeAt (prog : Program) (input : PublicInput) (p : Proof PrunedMerklePaths) : Outcome :=
  match setup? prog p with
  | none => .setup
  | some (s, ρ) =>
    match ladderOf prog s ρ with
    | none => .setup
    | some levels =>
      let shs := levelShapes (stackMu prog s) levels
      if !openingsOk (nLanes prog s) true shs p.merkle then .openings
      else
        match ((do
            let x ← walkProof (readerOps blake2sBytes) prog s input shs
            Reader.finish
            return x : Walk Id (Wire × List (List (List K)))).run'
          ⟨FsState.seed prog input, p.stream, p.merkle⟩).run with
        | .error e => .read e
        | .ok (w, rows) => algebraOutcome prog s input shs w rows

/-- `verify`'s stages on the fixture's program and input, naming the first that rejects `p`. -/
def outcome (p : Proof PrunedMerklePaths) : Outcome := outcomeAt fx.prog fx.input p

/-! ## The mutations -/

/-- The proof with stream scalar `i` changed by `g`. -/
def scalar (i : ℕ) (g : E → E) (p : Proof PrunedMerklePaths) : Proof PrunedMerklePaths :=
  ⟨p.stream.modify i g, p.merkle⟩

/-- The proof with opening phase `i` changed by `g`. -/
def opening (i : ℕ) (g : PrunedMerklePaths → PrunedMerklePaths) (p : Proof PrunedMerklePaths) :
    Proof PrunedMerklePaths :=
  ⟨p.stream, p.merkle.modify i g⟩

/-- One added. -/
def bump (x : E) : E := x + 1

/-- A nonzero third limb added. -/
def topLimb (x : E) : E := x + E.ofLimbs 0 0 1

/-- A digest with its first word changed. -/
def flipDigest (d : Digest) : Digest := d.set 0 (d[0] ^^^ 1)

/-- The honest proof's wire transcript. -/
def wire : Option Wire :=
  let f := fx
  match setup? f.prog f.proof with
  | none => none
  | some (s, ρ) =>
    let shs := levelShapes (stackMu f.prog s) ((ladderOf f.prog s ρ).getD [])
    match ((walkChain (readerOps (m := Id) blake2sBytes) f.prog s f.input shs).run'
      ⟨FsState.seed f.prog f.input, f.proof.stream, f.proof.merkle⟩).run with
    | .ok w => some w
    | .error _ => none

/-- The offset of the first of `xs` that occurs once in the honest stream, `0` if none does. -/
def firstOnce (xs : List E) : ℕ :=
  let st := fx.proof.stream
  ((xs.filter (st.count · == 1)).map st.idxOf).headD 0

/-- The stream offsets the mutations change, off the honest wire: a grand-product round's
coefficient, a table column value, a public value, a Flock slice, level 1's out-of-domain value,
the last level's residual value, its query message's coefficient and the last round's
coefficient; the four grinding nonces; the top half of level 0's next root. Each is a scalar that
occurs once in the stream. -/
def offsets : List ℕ :=
  match wire with
  | none => []
  | some w =>
    let last := w.whir.getD 3 default
    let rootHi := ((w.whir.headD default).root.map fun d ↦ (digestScalars d).2).getD 0
    [firstOnce ((w.bus.layers.getD 4 default).rounds.flatMap (·.wire)),
      firstOnce w.table.finals, firstOnce w.pub.values, firstOnce w.flock.slices,
      firstOnce [(w.whir.getD 1 default).oodValue], firstOnce last.residual,
      firstOnce last.queryWire, firstOnce [(last.tail.headD default).wire.getD 1 0]] ++
    w.whir.map (fun l ↦ firstOnce [l.nonce]) ++ [firstOnce [rootHi]]

/-- A mutation of the proof: what it changes, the change, and where `verify` must reject it. -/
structure Mutation where
  /-- What it changes. -/
  name : String
  /-- The change. -/
  change : Proof PrunedMerklePaths → Proof PrunedMerklePaths
  /-- Where `verify` rejects it. -/
  expected : Outcome

/-- The mutations rejected before the chain walk passes its setup's reads. -/
def cheap : List Mutation := [
  ⟨"a nonzero upper limb in an announced size", scalar 3 (· + E.ofLimbs 0 1 0), .setup⟩,
  ⟨"a size above its cap", scalar 1 fun _ ↦ sizeScalar 33, .setup⟩,
  ⟨"a rate outside its window", scalar 7 fun _ ↦ sizeScalar 5, .setup⟩,
  ⟨"a level-0 row of the wrong width",
    opening 0 fun o ↦ { o with leafData := o.leafData.modify 5 (· ++ [0]) }, .openings⟩,
  ⟨"a later level's row of the wrong width",
    opening 2 fun o ↦ { o with leafData := o.leafData.modify 0 (·.dropLast) }, .openings⟩,
  ⟨"more rows than queries", opening 3 fun o ↦
    { o with leafData := o.leafData ++ List.replicate 1 (o.leafData.headD []) }, .openings⟩,
  ⟨"a missing opening", fun p ↦ ⟨p.stream, p.merkle.dropLast⟩, .openings⟩,
  ⟨"a surplus opening", fun p ↦ ⟨p.stream, p.merkle ++ [p.merkle.headD ⟨[], []⟩]⟩, .openings⟩,
  ⟨"a nonzero third limb in a half of the commitment root", scalar 9 topLimb,
    .read .nonCanonicalEncoding⟩]

/-- Every mutation, the cheap ones first. -/
def mutations : List Mutation := cheap ++ [
  ⟨"a grand-product round coefficient", scalar (offsets.getD 0 0) bump, .read .powFailed⟩,
  ⟨"a table column value", scalar (offsets.getD 1 0) bump, .read .powFailed⟩,
  ⟨"a public value", scalar (offsets.getD 2 0) bump, .read .powFailed⟩,
  ⟨"a Flock slice", scalar (offsets.getD 3 0) bump, .read .powFailed⟩,
  ⟨"level 1's out-of-domain value", scalar (offsets.getD 4 0) bump, .read .powFailed⟩,
  ⟨"a residual value", scalar (offsets.getD 5 0) bump, .read .powFailed⟩,
  ⟨"the last query message's coefficient", scalar (offsets.getD 6 0) bump, .whir⟩,
  ⟨"the last round's coefficient", scalar (offsets.getD 7 0) bump, .whir⟩,
  ⟨"level 0's grinding nonce", scalar (offsets.getD 8 0) bump, .read .powFailed⟩,
  ⟨"level 1's grinding nonce", scalar (offsets.getD 9 0) bump, .read .powFailed⟩,
  ⟨"level 2's grinding nonce", scalar (offsets.getD 10 0) bump, .read .powFailed⟩,
  ⟨"level 3's grinding nonce", scalar (offsets.getD 11 0) bump, .read .powFailed⟩,
  ⟨"a nonzero third limb in a half of level 0's next root", scalar (offsets.getD 12 0) topLimb,
    .read .nonCanonicalEncoding⟩,
  ⟨"a wrong Merkle sibling",
    opening 1 fun o ↦ { o with siblingHashes := o.siblingHashes.modify 3 flipDigest },
    .read .invalidMerkleOpening⟩,
  ⟨"a truncated path",
    opening 2 fun o ↦ { o with siblingHashes := o.siblingHashes.dropLast },
    .read .invalidMerkleOpening⟩,
  ⟨"a surplus sibling",
    opening 0 fun o ↦
      { o with siblingHashes := o.siblingHashes ++ [o.siblingHashes.headD default] },
    .read .invalidMerkleOpening⟩,
  ⟨"a duplicated position, its row stored twice",
    opening 0 fun o ↦ { o with leafData := o.leafData.take 4 ++ o.leafData.drop 3 },
    .read .invalidMerkleOpening⟩,
  ⟨"a missing row", opening 2 fun o ↦ { o with leafData := o.leafData.dropLast },
    .read .invalidMerkleOpening⟩,
  ⟨"a stored word changed", opening 0 fun o ↦
    { o with leafData := o.leafData.modify 7 (·.modify 2 (· + 1)) }, .read .invalidMerkleOpening⟩,
  ⟨"two rows of level 1 exchanged", opening 1 fun o ↦ { o with leafData := match o.leafData with
    | r₀ :: r₁ :: rest => r₁ :: r₀ :: rest
    | rs => rs }, .read .invalidMerkleOpening⟩,
  ⟨"a trailing scalar", fun p ↦ ⟨p.stream ++ [0], p.merkle⟩, .read .notFullyConsumed⟩,
  ⟨"a truncated stream", fun p ↦ ⟨p.stream.dropLast, p.merkle⟩, .read .exceededStream⟩]

/-- A change of the statement, the proof kept: what it changes, the program and input, and where
`verify` must reject the fixture's proof of the original statement. -/
structure StatementMutation where
  /-- What it changes. -/
  name : String
  /-- The program. -/
  prog : Program
  /-- The public input. -/
  input : PublicInput
  /-- Where `verify` rejects. -/
  expected : Outcome

/-- The statement changed: an input lane, an instruction. The seed moves, so the first grinding
check rejects. -/
def statementMutations : List StatementMutation := [
  ⟨"an input lane bumped", fx.prog,
    ⟨fun i ↦ if i = 0 then fx.input.lanes 0 + 1 else fx.input.lanes i⟩, .read .powFailed⟩,
  ⟨"an instruction changed",
    { fx.prog with code := fun i ↦ if i.val = 0 then .xor 1 1 1 else fx.prog.code i }, fx.input,
    .read .powFailed⟩]

/-! ## The honest proof and the cheap mutations -/

#guard verifies id

#guard cheap.all fun m ↦ !verifies m.change && outcome (m.change fx.proof) == m.expected

-- The offsets are past the sizes and the commitment root, distinct, and the last round's
-- coefficient is the stream's last scalar.
#guard offsets.length == 13 && offsets.all (fun i ↦ 10 ≤ i && i < fx.proof.stream.length) &&
  decide offsets.Nodup && offsets.getD 7 0 + 1 == fx.proof.stream.length

/-! ## The same walk, logged -/

/-- The honest proof's reads in their stages, on the proof reader with every step logged
(`ChainOps.logged`). -/
def loggedWalk : Array ChainEvent :=
  let f := fx
  match setup? f.prog f.proof with
  | none => #[]
  | some (s, ρ) =>
    let shs := levelShapes (stackMu f.prog s) ((ladderOf f.prog s ρ).getD [])
    match ((((walkProof (readerOps (m := Id) blake2sBytes).logged f.prog s f.input shs).run
        #[]).run' ⟨FsState.seed f.prog f.input, f.proof.stream, f.proof.merkle⟩).run) with
    | .ok (_, log) => log
    | .error _ => #[]

/-- The stream scalars a logged step read. -/
def scalarsRead : ChainEvent → ℕ
  | .scalar _ => 1
  | .root _ => 2
  | .nonce _ _ => 1
  | _ => 0

/-- A logged grinding check. -/
def isNonce : ChainEvent → Bool
  | .nonce _ _ => true
  | _ => false

/-- A logged opening. -/
def isOpening : ChainEvent → Bool
  | .opening .. => true
  | _ => false

-- The logged walk reads the whole stream, checks four grinding nonces, and opens the four
-- commitments last, after every step of the chain.
#guard (loggedWalk.toList.map scalarsRead).sum == fx.proof.stream.length &&
  (loggedWalk.toList.filter isNonce).length == 4 &&
  (loggedWalk.toList.drop (loggedWalk.size - 4)).all isOpening &&
  !(loggedWalk.toList.take (loggedWalk.size - 4)).any isOpening

/-! ## WHIR's algebra on the honest transcript -/

/-- A change of WHIR's honest inputs: the stored rows, the level at an index, and the first
round polynomial's wire. -/
abbrev WhirMutation : Type :=
  (List (List (List K)) → List (List (List K))) × ℕ × (WhirLevel → WhirLevel) × (List E → List E)

/-- WHIR's check on the honest wire, with the rows and a level changed by each of `muts`, the
phases before it run once. -/
def whirChecks (muts : List WhirMutation) : List Bool :=
  let f := fx
  match setup? f.prog f.proof with
  | none => []
  | some (s, ρ) =>
    let shs := levelShapes (stackMu f.prog s) ((ladderOf f.prog s ρ).getD [])
    match ((walkProof (readerOps (m := Id) blake2sBytes) f.prog s f.input shs).run'
      ⟨FsState.seed f.prog f.input, f.proof.stream, f.proof.merkle⟩).run with
    | .error _ => []
    | .ok (w, rows) =>
      let I := leanVm f.prog s
      let fo := do
        let b ← leanVmBus f.prog s f.input w.bus
        let t ← tableStep I b w.table
        let p ← pubStep I t w.pub
        flockStep I (flockRegion f.prog s Blake2sFlock.blake2sFlockSpec) rfl blake2sRows p
          w.flock
      match fo with
      | none => []
      | some fo =>
        let (W, target) := openingClaim I fo w.lam
        muts.map fun (fr, i, fl, ff) ↦
          whirCheck I.μ shs W target (ff w.whirFirst) (w.whir.modify i fl) (fr rows)

/-- A fold round with its challenge changed. -/
def bumpFold (f : Fold) : Fold := { f with chal := f.chal + 1 }

/-- The honest transcript, then changes at the last level and at the levels before it, each with
the verdict `whirCheck` must give: a stored word of level 2 and of level 0, the last level's
residual value and batching challenge; level 1's out-of-domain value, coordinate and round
polynomial, level 0's fold challenge, level 2's batching challenge and query message, and the
first round polynomial's coefficient. -/
def whirMutations : List (WhirMutation × Bool) := [
  ((id, 3, id, id), true),
  ((fun rs ↦ rs.modify 2 (·.modify 4 (·.modify 7 (· + 1))), 3, id, id), false),
  ((fun rs ↦ rs.modify 0 (·.modify 3 (·.modify 40 (· + 1))), 3, id, id), false),
  ((id, 3, fun l ↦ { l with residual := l.residual.modify 1 (· + 1) }, id), false),
  ((id, 3, fun l ↦ { l with lam := l.lam + 1 }, id), false),
  ((id, 1, fun l ↦ { l with oodValue := l.oodValue + 1 }, id), false),
  ((id, 1, fun l ↦ { l with ood := l.ood.modify 0 (· + 1) }, id), false),
  ((id, 1, fun l ↦ { l with oodWire := l.oodWire.modify 0 (· + 1) }, id), false),
  ((id, 0, fun l ↦ { l with folds := l.folds.modify 2 bumpFold }, id), false),
  ((id, 2, fun l ↦ { l with lam := l.lam + 1 }, id), false),
  ((id, 2, fun l ↦ { l with queryWire := l.queryWire.modify 1 (· + 1) }, id), false),
  ((id, 3, id, fun ws ↦ ws.modify 0 (· + 1)), false)]

end LeanerVMTests.Protocol.Verify
