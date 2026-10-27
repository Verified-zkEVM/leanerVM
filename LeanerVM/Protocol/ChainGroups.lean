/-
  LeanerVM.Protocol.ChainGroups

  The groups of Fiat–Shamir queries that fix one challenge: the squeezes from the state before the
  challenge, and the proof of work before it when it has one. A group's status in a log of fresh
  queries, the flip it closes on, the probability over its unasked queries that it closes on one,
  and what one more query changes.
-/

module

public import LeanerVM.Protocol.RandomOracleGame

/-!
# The groups of a chain's challenges

A challenge of the Fiat–Shamir chain is fixed by a group of hash queries. A plain challenge is the
`m` squeezes from the state before it; a challenge a proof of work precedes (a *marked* one) is the
grinding check of a nonce against the base of the state before the nonce, the nonce's absorption,
and the `m` squeezes from the state it leads to. A `Group` names one: the state before it and, for
a marked one, the nonce.

**Where histories start** (`ChainStarts`). A reader reads off the log the statement a digest
opens (`stmtAt`); the digests that open one are the starts the chain walks back to
(`ChainStarts.isStart`). One more clean query opens or closes no statement but at its answer, and
deduplication changes none. `ChainStarts.startAt seed` is the reader of one fixed seed.

**Reading a history** (`SlotReader`). How a history of the chain is read as a prefix of a
protocol's transcript is a parameter: where histories start, the announcement a history opens
with at the statement its start opens, the protocol at it, the longest prefix of its transcript a
history reads (`decodePrefix`), each challenge as a `SqueezeSlot` (the number of squeezes, the
challenge their digests give, and that uniform digests give a uniform challenge), the marked
challenges, and the bad challenges at each prefix. It carries the facts about the decoder that
tie a group's challenge to the protocol's: the words of the oracle messages depend on the log only
under the roots the history absorbs, a challenge reads its squeezes, no slot reads the state an
observe or a nonce step leads to, a marked challenge follows a nonce, and a challenge reads a
squeeze at least.

**A group's status in a log** of fresh queries, read through first occurrences (`logAnswer`):
`groupSlot` reads the group's challenge off the history of its state from a start and the
statement the start opens, with the group's nonce step for a group with a nonce, and keeps it
when the challenge is marked exactly when the group has a nonce; `Group.run` is the digests of the
group's squeezes so far, `Group.check?` the answer to its check; `isOpen` says some query of the
group is logged and not all; `isClosed` that all are. `Flips` says the group is closed on a bad
challenge, its proof of work passing (`PowPasses`); `FlipAt` that some group flips; `π` is the
probability, over fresh uniform answers to its unasked queries, that the group closes on a bad
challenge, `1` on a group that flips (`π_eq_one_of_flips`).

**One more query** (`CleanLog`, `CleanStep`): a fresh query whose answer is no logged answer, not
in play and not a half of the query. Then the history of every other state and the words read
under it do not change, nor does the challenge a group fixes (`chainHistory_append`,
`SlotReader.groupSlot_append`). `touched` lists the groups the query may advance or open; every
other group, and every closed group, keeps its challenge, its check and its squeezes
(`Group.run_append`), so whether it is open and whether it flips. The open groups after the query
are open before it or opened by it (`openGroups_append_subset`), and a flip after the query, with
none before, is a group open before it or opened by it, at probability `1` after it
(`flipAt_append`).
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics Blake2sHash OracleComp OracleSpec ProtocolSpec
open MerkleTree (logAnswer)
open scoped ENNReal

@[expose] public section

/-! ## The queries of a group -/

/-- The grinding base from the state `cv`. -/
def baseInput (cv : Digest) : List UInt8 := FsState.stepBytes cv 0 FsState.powBaseTag

/-- The grinding check of the nonce `n` against the base `base`. -/
def checkInput (base : Digest) (n : E) : List UInt8 :=
  FsState.stepBytes base n FsState.powNonceTag

/-- The absorption of the nonce `n` from the state `cv`. -/
def absorbInput (cv : Digest) (n : E) : List UInt8 := Block.input cv (.nonce n)

/-- The squeeze from the state `x`. -/
def squeezeInput (x : Digest) : List UInt8 := Block.input x .squeeze

/-- The digests of up to `m` consecutive squeezes from `x` that the log answers. -/
def squeezeRun (l : hashSpec.QueryLog) (x : Digest) : ℕ → List Digest
  | 0 => []
  | m + 1 =>
    match logAnswer l (squeezeInput x) with
    | none => []
    | some d => d :: squeezeRun l d m

/-- The readings of consecutive squeezes answered by `ds`. -/
def squeezeBlocks (ds : List Digest) : List (Block × Digest) := ds.map fun d ↦ (.squeeze, d)

/-- The digests a history absorbs as two consecutive observes: every root its commitments
read. -/
def historyRoots : List (Block × Digest) → List Digest
  | [] => []
  | r :: rest =>
    (match r, rest with
      | (.observe x₁, _), (.observe x₂, _) :: _ => (digestOfScalars (x₁, x₂)).toList
      | _, _ => []) ++ historyRoots rest

/-- A challenge read off consecutive squeezes: their number, the challenge their digests give, and
the law that uniform digests give a uniform challenge. -/
structure SqueezeSlot (C : Type) [SampleableType C] where
  /-- The number of squeezes. -/
  m : ℕ
  /-- The challenge the squeezes' digests give. -/
  assemble : (Fin m → Digest) → C
  /-- Uniform digests give a uniform challenge. -/
  uniform : ∀ p : C → Prop,
    Pr{let d ← $ᵗ (Fin m → Digest)}[p (assemble d)] = Pr{let c ← $ᵗ C}[p c]

/-! ## Clean logs and where histories start -/

/-- A log of fresh queries, each input once, with no collision and no hit on the digests in play
from `roots`. -/
structure CleanLog (roots : List Digest) (l : hashSpec.QueryLog) : Prop where
  /-- Each input once. -/
  nodup : (l.map (·.1)).Nodup
  /-- No collision. -/
  noCollision : ¬ QueryLog.HasCollision l
  /-- No hit. -/
  noHit : ¬ QueryLog.HasHit (inPlay roots) l

/-- **One more clean query**: fresh, answered by a digest that answers no logged query, is not in
play, and is not a half of the query. -/
structure CleanStep (roots : List Digest) (l : hashSpec.QueryLog) (t : List UInt8) (u : Digest) :
    Prop where
  /-- The query is fresh. -/
  fresh : QueryLog.Fresh l t
  /-- No logged query has the answer. -/
  notAnswer : ∀ e ∈ l, e.2 ≠ u
  /-- The answer is not in play. -/
  notInPlay : u ∉ inPlay roots l
  /-- The answer is not a half of the query. -/
  notHalf : u ∉ halves t

/-- A log clean from some roots is clean from none. -/
theorem CleanLog.toNil {roots : List Digest} {l : hashSpec.QueryLog} (hl : CleanLog roots l) :
    CleanLog [] l :=
  ⟨hl.nodup, hl.noCollision, fun ⟨i, hfr, hin⟩ ↦ hl.noHit ⟨i, hfr, by
    simp only [inPlay, List.nil_append, List.mem_append] at hin ⊢
    exact hin.imp_left .inr⟩⟩

/-- **Where a reader's histories start**: the statement a digest opens, read off the log, a
start being a digest that opens one. One more clean query opens or closes no statement at another
digest, and deduplicating a consistent log changes none. -/
structure ChainStarts where
  /-- The statements a history may open. -/
  Stmt : Type
  /-- The statement a digest opens in a log; `none` off the starts. -/
  stmtAt : hashSpec.QueryLog → Digest → Option Stmt
  /-- One more clean query changes the statement at no digest but its answer. -/
  stmtAt_append : ∀ l t u d, CleanLog [] (l ++ [⟨t, u⟩]) → d ≠ u →
    stmtAt (l ++ [⟨t, u⟩]) d = stmtAt l d
  /-- The statements of a consistent log are those of its deduplication. -/
  stmtAt_dedupKeys : ∀ l, QueryLog.Consistent l → ∀ d, stmtAt (List.dedupKeys l) d = stmtAt l d

namespace ChainStarts

/-- The start test of a log: the digests that open a statement. -/
def isStart (S : ChainStarts) (l : hashSpec.QueryLog) (d : Digest) : Bool := (S.stmtAt l d).isSome

/-- **One fixed start**: `seed` opens the one statement in every log, and no other digest opens
one. -/
def startAt (seed : Digest) : ChainStarts where
  Stmt := Unit
  stmtAt _ d := if d = seed then some () else none
  stmtAt_append _ _ _ _ _ _ := rfl
  stmtAt_dedupKeys _ _ _ := rfl

/-- The start test of one fixed start is the test of that seed. -/
@[simp] theorem isStart_startAt (seed : Digest) (l : hashSpec.QueryLog) :
    (startAt seed).isStart l = HashChain.isSeed seed := by
  funext d
  by_cases h : d = seed <;> simp [isStart, startAt, HashChain.isSeed, h]

/-- The seed of one fixed start opens its statement. -/
@[simp] theorem stmtAt_startAt (seed : Digest) (l : hashSpec.QueryLog) :
    (startAt seed).stmtAt l seed = some () := by
  simp [startAt]

end ChainStarts

/-! ## Reading a history -/

/-- **A reader of chain histories**: where histories start and the statement a start opens, the
protocol a history of the chain is a transcript prefix of, how a history is read, and the facts
about the reading that tie a group's challenge to the protocol's. -/
structure SlotReader extends ChainStarts where
  /-- The low zero bits a proof of work asks for. -/
  powBits : ℕ
  /-- The announcements a history may open with. -/
  Ann : Type
  /-- The announcement a history from a start opening a statement opens with. -/
  announcementOf : Stmt → List (Block × Digest) → Option Ann
  /-- The number of rounds at an announcement. -/
  n : Ann → ℕ
  /-- The protocol at an announcement. -/
  spec : (a : Ann) → ProtocolSpec (n a)
  /-- The challenges are sampled uniformly. -/
  sampleable : ∀ a (i : (spec a).ChallengeIdx), SampleableType ((spec a).Challenge i)
  /-- The words filling the oracle messages, which the chain does not carry. -/
  Words : Ann → Type
  /-- The words read off a log, under the roots a history absorbs. -/
  wordsAt : (a : Ann) → hashSpec.QueryLog → List (Block × Digest) → Words a
  /-- The longest prefix of the transcript a history reads exactly. -/
  decodePrefix : (a : Ann) → Words a → List (Block × Digest) →
    Option (Σ k : Fin (n a + 1), (spec a).Transcript k)
  /-- How each challenge is read off squeezes. -/
  slot : (a : Ann) → (i : (spec a).ChallengeIdx) →
    @SqueezeSlot ((spec a).Challenge i) (sampleable a i)
  /-- The challenges a proof of work precedes. -/
  mark : (a : Ann) → (spec a).ChallengeIdx → Bool
  /-- The bad challenges at a prefix ending before a challenge. -/
  Bad : (a : Ann) → (i : (spec a).ChallengeIdx) → (spec a).Transcript i.1.castSucc →
    Set ((spec a).Challenge i)
  /-- The words depend on the log only through the rows under the roots the history absorbs:
  the reader takes its roots off the history, and fills the words of a commitment the history has
  not absorbed yet without the log. The rows under a root are fixed once the root is absorbed;
  under a root to come, they may still change. -/
  wordsAt_congr : ∀ a (l l' : hashSpec.QueryLog) (hs : List (Block × Digest)),
    (∀ root ∈ historyRoots hs, ∀ depth rowWords leafWords p,
      extractRows l' root depth rowWords leafWords p =
        extractRows l root depth rowWords leafWords p) →
    wordsAt a l' hs = wordsAt a l hs
  /-- A challenge reads its squeezes: a history decoded past the challenge has, at it, the
  challenge its squeezes' digests give. -/
  squeezeSlot_read : ∀ a W hs (i : (spec a).ChallengeIdx) tr,
    decodePrefix a W hs = some ⟨i.1.castSucc, tr⟩ →
    ∀ (ds : Fin (slot a i).m → Digest) rest k tr',
      decodePrefix a W (hs ++ squeezeBlocks (List.ofFn ds) ++ rest) = some ⟨k, tr'⟩ →
      ∃ h : i.1.succ.val ≤ k.val,
        FullTranscript.take i.1.succ.val h tr' = tr.concat ((slot a i).assemble ds)
  /-- No slot reads the state an observe or a nonce step leads to. -/
  decodePrefix_digest_indep : ∀ a W hs (b : Block) (d d' : Digest) rest, b ≠ .squeeze →
    decodePrefix a W (hs ++ (b, d) :: rest) = decodePrefix a W (hs ++ (b, d') :: rest)
  /-- A marked challenge follows a nonce step. -/
  mark_afterNonce : ∀ a W hs (i : (spec a).ChallengeIdx) tr,
    decodePrefix a W hs = some ⟨i.1.castSucc, tr⟩ → mark a i = true →
    ∃ hs₀ n d, hs = hs₀ ++ [(.nonce n, d)]
  /-- Every challenge reads a squeeze at least: a reader's instance checks it over its window of
  announcements. -/
  slot_pos : ∀ a i, 0 < (slot a i).m

attribute [instance] SlotReader.sampleable

/-- A prefix of `k` rounds, as the prefix before a challenge when round `k` is one. -/
def asChallenge {n : ℕ} {pSpec : ProtocolSpec n} :
    (Σ k : Fin (n + 1), pSpec.Transcript k) →
      Option (Σ i : pSpec.ChallengeIdx, pSpec.Transcript i.1.castSucc)
  | ⟨k, tr⟩ =>
    if h : k.val < n then
      if hd : pSpec.dir ⟨k.val, h⟩ = .V_to_P then some ⟨⟨⟨k.val, h⟩, hd⟩, tr⟩ else none
    else none

/-! ## Groups -/

/-- A group of queries fixing one challenge: the state before it and, for a challenge a proof of
work precedes, the nonce, the group then starting at the state before the nonce step. -/
structure Group where
  /-- The state the group starts from. -/
  cv : Digest
  /-- The nonce of a group with a proof of work. -/
  nonce : Option E
  deriving DecidableEq

namespace Group

variable (l : hashSpec.QueryLog) (G : Group)

/-- The nonce step a group's history continues with, its state immaterial. -/
def nonceBlock : List (Block × Digest) := G.nonce.toList.map fun n ↦ (.nonce n, default)

/-- The answer to the group's grinding check, against the answer to its grinding base. -/
def check? : Option Digest :=
  G.nonce.bind fun n ↦ (logAnswer l (baseInput G.cv)).bind fun b ↦ logAnswer l (checkInput b n)

/-- The state the group's squeezes start from: its own, or the answer to its nonce step. -/
def start? : Option Digest :=
  match G.nonce with
  | none => some G.cv
  | some n => logAnswer l (absorbInput G.cv n)

/-- The digests of the group's first `m` squeezes the log answers. -/
def run (m : ℕ) : List Digest :=
  match G.start? l with
  | none => []
  | some x => squeezeRun l x m

/-- Some query of the group is logged: its check, its nonce step, or a squeeze. -/
def asked (m : ℕ) : Bool :=
  (G.check? l).isSome || (G.nonce.isSome && (G.start? l).isSome) || !(G.run l m).isEmpty

/-- Every query of the group is logged: its check if it has a nonce, and its `m` squeezes. -/
def complete (m : ℕ) : Bool :=
  (G.nonce.isNone || (G.check? l).isSome) && (G.run l m).length == m

end Group

/-- The proof of work of the nonce `n` from the state `cv` passes in the log: its base and check
are answered, the check with `bits` low zero bits. For `0 < bits` this is the verifier's
`FsState.checkPow`; at `bits = 0` the verifier asks no check and accepts the nonce `0` alone. -/
def PowPasses (bits : ℕ) (l : hashSpec.QueryLog) (cv : Digest) (n : E) : Prop :=
  ∃ base d, logAnswer l (baseInput cv) = some base ∧ logAnswer l (checkInput base n) = some d ∧
    FsState.lowBitsZero d bits = true

namespace SlotReader

variable (R : SlotReader) (l : hashSpec.QueryLog)

/-- **The challenge a group fixes**, read off the log: the history of its state from a start, the
statement the start opens, the announcement the history opens with, and the prefix the history,
with the group's nonce step, reads, when the next round is a challenge, marked exactly when the
group has a nonce. -/
def groupSlot (G : Group) :
    Option (Σ a : R.Ann, Σ i : (R.spec a).ChallengeIdx, (R.spec a).Transcript i.1.castSucc) := do
  let h ← chainHistory l (R.isStart l) ⟨G.cv⟩
  let st ← R.stmtAt l h.1
  let a ← R.announcementOf st h.2
  let p ← R.decodePrefix a (R.wordsAt a l h.2) (h.2 ++ G.nonceBlock)
  let ⟨i, tr⟩ ← asChallenge p
  if R.mark a i = G.nonce.isSome then some ⟨a, i, tr⟩ else none

/-- The number of squeezes of a group's challenge; `0` when the group fixes none. -/
def size (G : Group) : ℕ :=
  match R.groupSlot l G with
  | none => 0
  | some ⟨a, i, _⟩ => (R.slot a i).m

/-- A group is open: it fixes a challenge, some of its queries are logged, and not all. -/
def isOpen (G : Group) : Bool :=
  (R.groupSlot l G).isSome && G.asked l (R.size l G) && !G.complete l (R.size l G)

/-- A group is closed: it fixes a challenge and all its queries are logged. -/
def isClosed (G : Group) : Bool := (R.groupSlot l G).isSome && G.complete l (R.size l G)

/-- **A group flips**: its squeezes are all logged, its proof of work passes, and the challenge
its squeezes give is bad at the prefix before it. -/
def Flips (G : Group) : Prop :=
  match R.groupSlot l G with
  | none => False
  | some ⟨a, i, tr⟩ =>
    (G.run l (R.slot a i).m).length = (R.slot a i).m ∧
      (∀ n, G.nonce = some n → PowPasses R.powBits l G.cv n) ∧
      (R.slot a i).assemble (fun j ↦ (G.run l (R.slot a i).m).getD j default) ∈ R.Bad a i tr

/-- **A flip at the end of a log**: some group flips. -/
def FlipAt : Prop := ∃ G, R.Flips l G

/-- A flip on a run of the game: one at the end of its joint log. -/
def Flip (g : Run) : Prop := R.FlipAt g.log

/-- **The probability a group closes on a bad challenge**, over fresh uniform answers to its check
(ignored when logged, or for a plain group) and to its unasked squeezes, the logged ones fixed. -/
noncomputable def π (G : Group) : ℝ≥0∞ :=
  match R.groupSlot l G with
  | none => 0
  | some ⟨a, i, tr⟩ =>
    Pr{let z ← $ᵗ (Digest × (Fin ((R.slot a i).m - (G.run l (R.slot a i).m).length) → Digest))}[
      (G.nonce.isSome = true → FsState.lowBitsZero ((G.check? l).getD z.1) R.powBits = true) ∧
      (R.slot a i).assemble (fun j ↦ (G.run l (R.slot a i).m ++ List.ofFn z.2).getD j default) ∈
        R.Bad a i tr]

end SlotReader

/-! ## The groups a log or a query touches -/

/-- The states the log's squeezes start from. -/
def squeezeStates (l : hashSpec.QueryLog) : List Digest :=
  l.filterMap fun e ↦
    match Block.parse? e.1 with
    | some (x, .squeeze) => some x
    | _ => none

/-- The groups of the log's nonce steps, read as absorptions. -/
def nonceGroups (l : hashSpec.QueryLog) : List Group :=
  l.filterMap fun e ↦
    match Block.parse? e.1 with
    | some (cv, .nonce n) => some ⟨cv, some n⟩
    | _ => none

/-- The states whose grinding base the log answers by `y`. -/
def baseStates (l : hashSpec.QueryLog) (y : Digest) : List Digest :=
  l.filterMap fun e ↦
    if e.2 = y ∧ e.1 = baseInput (digestOfBytes e.1) then some (digestOfBytes e.1) else none

/-- The groups of the log's nonce steps, read as grinding checks. -/
def checkGroups (l : hashSpec.QueryLog) : List Group :=
  l.flatMap fun e ↦
    match Block.parse? e.1 with
    | some (y, .nonce n) => (baseStates l y).map fun cv ↦ ⟨cv, some n⟩
    | _ => []

/-- The groups that may have a query in the log: the plain group of every input's state, and the
groups of its nonce steps, read as absorptions and as checks. -/
def candidates (l : hashSpec.QueryLog) : List Group :=
  (l.map fun e ↦ (⟨digestOfBytes e.1, none⟩ : Group)) ++ nonceGroups l ++ checkGroups l

namespace SlotReader

variable (R : SlotReader) (l : hashSpec.QueryLog)

/-- The squeeze from `x` is the group's next query: the group fixes a challenge and its squeezes
so far end at `x`, short of all of them. -/
def awaits (G : Group) (x : Digest) : Bool :=
  match G.start? l with
  | none => false
  | some s =>
    decide ((G.run l (R.size l G)).length < R.size l G) &&
      decide ((G.run l (R.size l G)).getLastD s = x)

/-- **The groups a query may advance or open**: for the squeeze from `x`, the groups awaiting it
among the plain group at `x`, the plain groups of the log's squeezes and the groups of its nonce
steps; for the nonce step `n` from `y`, the group absorbing `n` from `y` and those checking `n`
against a base the log answers by `y`; none for another query. -/
def touched (t : List UInt8) : List Group :=
  match Block.parse? t with
  | some (x, .squeeze) =>
    (((x :: squeezeStates l).map fun y ↦ (⟨y, none⟩ : Group)) ++ nonceGroups l).filter
      fun G ↦ R.awaits l G x
  | some (y, .nonce n) => ⟨y, some n⟩ :: (baseStates l y).map fun cv ↦ ⟨cv, some n⟩
  | _ => []

/-- The open groups of a log. -/
def openGroups : Finset Group := ((candidates l).filter (R.isOpen l)).toFinset

/-- The groups a query opens: those it touches with no query in the log. -/
def openedBy (t : List UInt8) : Finset Group :=
  ((R.touched l t).filter fun G ↦ !G.asked l (R.size l G)).toFinset

end SlotReader

/-! ## Inputs -/

private theorem powBaseTag_ne : FsState.powBaseTag ≠ FsState.observeTag ∧
    FsState.powBaseTag ≠ FsState.squeezeTag ∧ FsState.powBaseTag ≠ FsState.powNonceTag := by
  decide +kernel

/-- The state a 64-byte hash of the chain starts from is its first half. -/
private theorem digestOfBytes_stepBytes (cv : Digest) (x : E) (tag : K) :
    digestOfBytes (FsState.stepBytes cv x tag) = cv :=
  digestOfBytes_append cv _

/-- The grinding base is not a step. -/
theorem parse?_baseInput (cv : Digest) : Block.parse? (baseInput cv) = none := by
  have ht : Blake2sHash.kOfBytes (kBytes FsState.powBaseTag) = FsState.powBaseTag := by
    simpa using Blake2sHash.kOfBytes_append FsState.powBaseTag []
  have hk : ∀ a n, 8 ≤ n → (kBytes a).drop n = [] := fun _ _ h ↦ List.drop_eq_nil_of_le h
  have hlen : (baseInput cv).length = 64 := by
    simp [baseInput, FsState.stepBytes, FsState.block, length_digestBytes, length_kBytes]
  simp only [Block.parse?, hlen, ↓reduceIte]
  simp only [baseInput, FsState.stepBytes, FsState.block, List.append_assoc, List.drop_append,
    length_digestBytes, length_kBytes, List.drop_eq_nil_of_le, Nat.reduceLeDiff, Nat.reduceSub,
    List.drop_zero, List.nil_append, hk, Blake2sHash.kOfBytes_append, ht]
  simp [powBaseTag_ne]

/-- A step's input determines the state and the block. -/
theorem input_inj {x y : Digest} {b c : Block} (h : Block.input x b = Block.input y c) :
    x = y ∧ b = c := by
  have := Block.parse?_input x b
  rw [h, Block.parse?_input] at this
  simpa [eq_comm] using this

/-- The grinding check of a nonce against a base is the nonce's step from the base. -/
theorem checkInput_eq (base : Digest) (n : E) : checkInput base n = Block.input base (.nonce n) :=
  rfl

/-- A step from a state has the state as a half. -/
private theorem mem_halves_input (cv : Digest) (b : Block) : cv ∈ halves (Block.input cv b) :=
  mem_halves_stepBytes cv b.elem b.tag

/-- The grinding base from a state has the state as a half. -/
private theorem mem_halves_baseInput (cv : Digest) : cv ∈ halves (baseInput cv) :=
  mem_halves_stepBytes cv 0 _

/-! ## The answers of a log -/

/-- A log answers no query it never asks. -/
theorem logAnswer_eq_none_iff {l : hashSpec.QueryLog} {q : List UInt8} :
    logAnswer l q = none ↔ QueryLog.Fresh l q := by
  simp [logAnswer, QueryLog.Fresh, List.find?_eq_none]

/-- An answer stays the log's when the log grows. -/
theorem logAnswer_append_of_eq_some {l l' : hashSpec.QueryLog} {q : List UInt8} {d : Digest}
    (h : logAnswer l q = some d) : logAnswer (l ++ l') q = some d := by
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
  simp [logAnswer, List.find?_append, he]

/-- One more query changes the answer to no other. -/
theorem logAnswer_append_of_ne {l : hashSpec.QueryLog} {t q : List UInt8} {u : Digest}
    (h : q ≠ t) : logAnswer (l ++ [⟨t, u⟩]) q = logAnswer l q := by
  simp only [logAnswer, List.find?_append, List.find?_cons, List.find?_nil]
  cases h' : l.find? (fun e ↦ decide (e.1 = q)) with
  | none => simp [Ne.symm h]
  | some e => simp

/-- One more fresh query is answered by its answer. -/
theorem logAnswer_append_self {l : hashSpec.QueryLog} {t : List UInt8} {u : Digest}
    (h : QueryLog.Fresh l t) : logAnswer (l ++ [⟨t, u⟩]) t = some u := by
  have h₀ := logAnswer_eq_none_iff.mpr h
  simp only [logAnswer, Option.map_eq_none_iff] at h₀
  simp [logAnswer, List.find?_append, h₀]

/-- The halves of an answered query are in play. -/
theorem mem_inPlay_of_logAnswer {roots : List Digest} {l : hashSpec.QueryLog} {q : List UInt8}
    {d : Digest} (h : logAnswer l q = some d) {x : Digest} (hx : x ∈ halves q) :
    x ∈ inPlay roots l :=
  mem_inPlay_of_mem_halves (MerkleTree.mem_of_logAnswer_eq_some h) hx

/-! ## Clean logs and one more clean query -/

variable {roots : List Digest} {l : hashSpec.QueryLog} {t : List UInt8} {u : Digest}

/-- A log with each input once is consistent. -/
theorem CleanLog.consistent (hl : CleanLog roots l) : QueryLog.Consistent l :=
  fun _ h₁ _ h₂ h ↦ by rw [List.inj_on_of_nodup_map hl.nodup h₁ h₂ h]

/-- One more clean query keeps the log clean. -/
theorem CleanLog.append (hl : CleanLog roots l) (hs : CleanStep roots l t u) :
    CleanLog roots (l ++ [⟨t, u⟩]) := by
  refine ⟨?_, fun ⟨e₁, h₁, e₂, h₂, hne, heq⟩ ↦ ?_, fun ⟨⟨i, hi⟩, hfresh, hin⟩ ↦ ?_⟩
  · rw [List.map_append, List.nodup_append]
    refine ⟨hl.nodup, by simp, fun a ha b hb hab ↦ ?_⟩
    obtain rfl : b = t := by simpa using hb
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
    exact hs.fresh e he hab
  · simp only [List.mem_append, List.mem_singleton] at h₁ h₂
    rcases h₁ with h₁ | rfl <;> rcases h₂ with h₂ | rfl
    · exact hl.noCollision ⟨e₁, h₁, e₂, h₂, hne, heq⟩
    · exact hs.notAnswer e₁ h₁ heq
    · exact hs.notAnswer e₂ h₂ heq.symm
    · exact hne rfl
  · simp only [List.length_append, List.length_singleton] at hi
    simp only [Fin.getElem_fin] at hfresh hin
    by_cases hil : i < l.length
    · refine hl.noHit ⟨⟨i, hil⟩, ?_, ?_⟩
      · simpa [List.take_append_of_le_length hil.le, List.getElem_append_left hil] using hfresh
      · simpa [List.take_append_of_le_length hil.le, List.getElem_append_left hil] using hin
    · obtain rfl : i = l.length := by omega
      simp only [List.take_left', List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem_cons_zero] at hin
      exact hs.notInPlay hin

/-- A clean log's part before its last query is clean. -/
theorem CleanLog.of_append (hl : CleanLog roots (l ++ [⟨t, u⟩])) : CleanLog roots l := by
  refine ⟨?_, fun h ↦ hl.noCollision (h.mono fun e he ↦ List.mem_append_left _ he),
    fun ⟨⟨i, hi⟩, hfresh, hin⟩ ↦ hl.noHit ⟨⟨i, by simp; omega⟩, ?_, ?_⟩⟩
  · exact (List.nodup_append.mp (by simpa using hl.nodup)).1
  · simpa [List.take_append_of_le_length hi.le, List.getElem_append_left hi] using hfresh
  · simpa [List.take_append_of_le_length hi.le, List.getElem_append_left hi] using hin

/-- A clean log's last query is fresh before it. -/
private theorem CleanLog.fresh_of_append (hl : CleanLog roots (l ++ [⟨t, u⟩])) :
    QueryLog.Fresh l t :=
  fun e he het ↦ by
    have := hl.nodup
    rw [List.map_append, List.nodup_append] at this
    exact this.2.2 _ (List.mem_map_of_mem he) t (by simp) het

/-- A clean log's last answer is not in play before it. -/
theorem CleanLog.notInPlay_of_append (hl : CleanLog roots (l ++ [⟨t, u⟩])) :
    u ∉ inPlay roots l := fun h ↦ hl.noHit ⟨⟨l.length, by simp⟩, by
  simpa using hl.fresh_of_append, by simpa using h⟩

/-- The roots are in play from the start. -/
theorem mem_inPlay_of_mem_roots {r : Digest} (hr : r ∈ roots) : r ∈ inPlay roots l := by
  simp [inPlay, hr]

/-! ## Histories and words after one more query -/

/-- The state after the first `j + 1` steps of a chain is the state of step `j`. -/
private theorem last_take_succ {α : Type} : ∀ (cv : Digest) (hs : List (α × Digest)) (j : ℕ)
    (hj : j < hs.length), HashChain.last cv (hs.take (j + 1)) = hs[j].2
  | _, (_, c) :: rest, 0, _ => by simp [HashChain.last]
  | _, (_, c) :: rest, j + 1, hj => by
    simp only [List.take_succ_cons, HashChain.last, List.getElem_cons_succ]
    exact last_take_succ c rest j (by simpa using hj)

/-- Two consecutive observes of a history, and the root they absorb. -/
private theorem mem_historyRoots :
    ∀ {hs : List (Block × Digest)} {r : Digest}, r ∈ historyRoots hs →
    ∃ (j : ℕ) (hj : j + 1 < hs.length) (x₁ x₂ : E), hs[j].1 = .observe x₁ ∧
      hs[j + 1].1 = .observe x₂ ∧ digestOfScalars (x₁, x₂) = some r
  | [], _, h => by simp [historyRoots] at h
  | (b, d) :: rest, r, h => by
    simp only [historyRoots, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨x₁, x₂, d₂, rest', rfl, rfl, hr⟩ : ∃ x₁ x₂ d₂ rest', b = .observe x₁ ∧
          rest = (.observe x₂, d₂) :: rest' ∧ digestOfScalars (x₁, x₂) = some r := by
        rcases b with x₁ | _ | _ <;> rcases rest with _ | ⟨⟨b₂, d₂⟩, rest'⟩ <;> (try simp at h)
        rcases b₂ with x₂ | _ | _ <;> (try simp at h)
        exact ⟨x₁, x₂, d₂, rest', rfl, rfl, h⟩
      exact ⟨0, by simp, x₁, x₂, rfl, rfl, hr⟩
    · obtain ⟨j, hj, x₁, x₂, h₁, h₂, h₃⟩ := mem_historyRoots h
      exact ⟨j + 1, by simp; omega, x₁, x₂, h₁, h₂, h₃⟩

/-- A search that finds one value or nothing along a list, and finds it somewhere, finds it. -/
private theorem findSome?_eq_some_of {α γ : Type} {f : α → Option γ} {y : γ} {l : List α}
    (hall : ∀ a ∈ l, f a = none ∨ f a = some y) (h : ∃ a ∈ l, f a = some y) :
    l.findSome? f = some y := by
  obtain ⟨a, ha, hfa⟩ := h
  have : (l.findSome? f).isSome := List.findSome?_isSome_iff.mpr ⟨a, ha, by simp [hfa]⟩
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp this
  obtain ⟨b, hb, hfb⟩ := List.exists_of_findSome?_eq_some hz
  rcases hall b hb with h | h <;> simp_all

/-- **The roots a history absorbs are rebuilt by the log**: on a log with no collision, two
consecutive observes of a history are logged steps, the second from the state the first leads
to, so the root they encode is one the log rebuilds. -/
private theorem historyRoots_subset_rebuiltRoots (hcoll : ¬ QueryLog.HasCollision l)
    {isStart : Digest → Bool} {s : FsState} {σ : Digest} {hs : List (Block × Digest)}
    (h : chainHistory l isStart s = some (σ, hs)) :
    ∀ r ∈ historyRoots hs, r ∈ rebuiltRoots l := by
  intro r hr
  obtain ⟨j, hj, x₁, x₂, h₁, h₂, hr⟩ := mem_historyRoots hr
  obtain ⟨e₁, he₁, ha₁, hp₁⟩ := HashChain.step_of_history h j (by omega)
  obtain ⟨e₂, he₂, -, hp₂⟩ := HashChain.step_of_history h (j + 1) hj
  rw [last_take_succ _ _ _ (by omega), h₂] at hp₂
  rw [h₁] at hp₁
  have hobs : observedInto l hs[j].2 = some x₁ := by
    refine findSome?_eq_some_of (fun e he ↦ ?_) ⟨e₁, he₁, by simp [ha₁, observed?, hp₁]⟩
    by_cases hc : e.2 = hs[j].2
    · have he₁' : e.1 = e₁.1 :=
        by_contra fun hne ↦ hcoll ⟨e, he, e₁, he₁, hne, hc.trans ha₁.symm⟩
      exact .inr (by simp [hc, observed?, he₁', hp₁])
    · exact .inl (by simp [hc])
  refine List.mem_filterMap.mpr ⟨e₂, he₂, ?_⟩
  simp [observed?, hp₂, hobs, hr]

/-- **The words read under a history do not change** with one more clean query: the history's
roots are in play, so no fresh hit reaches them, and the rows under them are those of the log
before the query. -/
private theorem SlotReader.wordsAt_append (R : SlotReader) (hl : CleanLog roots (l ++ [⟨t, u⟩]))
    {s : FsState} {σ : Digest} {h' : List (Block × Digest)}
    (h : chainHistory l (R.isStart l) s = some (σ, h')) (a : R.Ann) :
    R.wordsAt a (l ++ [⟨t, u⟩]) h' = R.wordsAt a l h' := by
  have hcons := hl.consistent
  refine R.wordsAt_congr a l _ h' fun root hr depth rowWords leafWords p ↦ ?_
  have hin : root ∈ inPlay roots l := by
    simp only [inPlay, List.mem_append]
    exact .inr (historyRoots_subset_rebuiltRoots hl.of_append.noCollision h root hr)
  exact extractRows_determined l [⟨t, u⟩] [root] root (List.mem_singleton_self _) hcons
    (not_freshHit_of_not_hasHit hcons hl.noHit hin) depth rowWords leafWords p

/-- **The challenge a group fixes does not change** with one more clean query, unless the group
starts from its answer. -/
theorem SlotReader.groupSlot_append (R : SlotReader) (hl : CleanLog roots (l ++ [⟨t, u⟩]))
    {G : Group} (hG : G.cv ≠ u) : R.groupSlot (l ++ [⟨t, u⟩]) G = R.groupSlot l G := by
  have hst : ∀ d, d ≠ u → R.stmtAt (l ++ [⟨t, u⟩]) d = R.stmtAt l d :=
    fun d hd ↦ R.stmtAt_append l t u d hl.toNil hd
  have hu := hl.notInPlay_of_append
  unfold SlotReader.groupSlot
  rw [chainHistory_append (e := ⟨t, u⟩) hu (isStart := R.isStart l)
    (fun d hd ↦ by simp only [ChainStarts.isStart, hst d hd]) (s := ⟨G.cv⟩) hG]
  rcases h : chainHistory l (R.isStart l) ⟨G.cv⟩ with _ | ⟨σ, h'⟩
  · rfl
  · have hσ : σ ≠ u := by
      rcases (start_of_chainHistory h roots).2 with h₁ | h₁
      · exact h₁ ▸ hG
      · exact fun h₂ ↦ hu (h₂ ▸ h₁)
    simp only [Option.bind_eq_bind, Option.bind_some, hst σ hσ, R.wordsAt_append hl h]

/-! ## A group's queries after one more query -/

/-- A log asked no squeeze from `x` has no squeezes from it. -/
theorem squeezeRun_eq_nil {x : Digest} (h : logAnswer l (squeezeInput x) = none) (m : ℕ) :
    squeezeRun l x m = [] := by
  cases m <;> simp [squeezeRun, h]

/-- A run of all its squeezes is the same in a longer log. -/
private theorem squeezeRun_append_of_length {l' : hashSpec.QueryLog} :
    ∀ {m : ℕ} {x : Digest}, (squeezeRun l x m).length = m →
      squeezeRun (l ++ l') x m = squeezeRun l x m
  | 0, _, _ => rfl
  | m + 1, x, h => by
    cases hx : logAnswer l (squeezeInput x) with
    | none => simp [squeezeRun, hx] at h
    | some d =>
      simp only [squeezeRun, hx, List.length_cons, Nat.add_right_cancel_iff] at h ⊢
      rw [logAnswer_append_of_eq_some hx]
      simp only [squeezeRun_append_of_length h]

/-- After one more clean query, the log answers no query having its answer as a half. -/
private theorem CleanStep.logAnswer_eq_none (hs : CleanStep roots l t u) {q : List UInt8}
    (hq : u ∈ halves q) : logAnswer (l ++ [⟨t, u⟩]) q = none := by
  have hqt : q ≠ t := fun h ↦ hs.notHalf (h ▸ hq)
  rw [logAnswer_append_of_ne hqt]
  cases h : logAnswer l q with
  | none => rfl
  | some d => exact absurd (mem_inPlay_of_logAnswer h hq) hs.notInPlay

/-- **Squeezes after one more query**: the squeezes from `x` the log answers, then the new
answer when the new query is the next squeeze, and nothing after it when no squeeze from the
answer is logged. -/
theorem squeezeRun_append (hu : logAnswer (l ++ [⟨t, u⟩]) (squeezeInput u) = none)
    (hfresh : QueryLog.Fresh l t) : ∀ (m : ℕ) (x : Digest),
    squeezeRun (l ++ [⟨t, u⟩]) x m = squeezeRun l x m ++
      (if (squeezeRun l x m).length < m ∧ t = squeezeInput ((squeezeRun l x m).getLastD x)
        then [u] else [])
  | 0, x => by simp [squeezeRun]
  | m + 1, x => by
    cases hx : logAnswer l (squeezeInput x) with
    | some d =>
      simp only [squeezeRun, logAnswer_append_of_eq_some hx, hx,
        squeezeRun_append hu hfresh m d, List.length_cons, List.getLastD_cons,
        Nat.add_lt_add_iff_right, List.cons_append]
    | none =>
      by_cases hxt : squeezeInput x = t
      · subst hxt
        rw [squeezeRun, logAnswer_append_self hfresh]
        simp [squeezeRun, hx, squeezeRun_eq_nil hu]
      · simp [squeezeRun, logAnswer_append_of_ne hxt, hx, Ne.symm hxt]

/-- After one more clean query, no squeeze from its answer is logged. -/
theorem CleanStep.logAnswer_squeezeInput (hs : CleanStep roots l t u) :
    logAnswer (l ++ [⟨t, u⟩]) (squeezeInput u) = none :=
  hs.logAnswer_eq_none (mem_halves_input u .squeeze)

/-- A log's answer is the answer of the query's first occurrence, a search along the log. -/
private theorem logAnswer_eq_findSome? (l : hashSpec.QueryLog) (q : List UInt8) :
    logAnswer l q = l.findSome? fun e ↦ if e.1 = q then some e.2 else none := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    by_cases h : e.1 = q
    · simp [logAnswer, h]
    · simpa [logAnswer, h] using ih

/-- On a consistent log, the answers are those of its deduplication. -/
theorem logAnswer_dedupKeys (hcons : QueryLog.Consistent l) (q : List UInt8) :
    logAnswer (List.dedupKeys l) q = logAnswer l q := by
  rw [logAnswer_eq_findSome?, logAnswer_eq_findSome?, QueryLog.findSome?_dedupKeys hcons]

/-- Squeezes read off two logs with the same answers are the same. -/
private theorem squeezeRun_congr {l' : hashSpec.QueryLog}
    (h : ∀ q, logAnswer l' q = logAnswer l q) : ∀ (m : ℕ) (x : Digest),
    squeezeRun l' x m = squeezeRun l x m
  | 0, _ => rfl
  | m + 1, x => by simp only [squeezeRun, h, squeezeRun_congr h m]

/-- A logged nonce step's group is among the log's absorptions. -/
private theorem mem_nonceGroups {cv s : Digest} {n : E}
    (h : logAnswer l (absorbInput cv n) = some s) :
    (⟨cv, some n⟩ : Group) ∈ nonceGroups l :=
  List.mem_filterMap.mpr ⟨_, MerkleTree.mem_of_logAnswer_eq_some h, by
    simp [absorbInput, Block.parse?_input]⟩

/-- A state whose grinding base the log answers by `b` is among the base states of `b`. -/
private theorem mem_baseStates {cv b : Digest} (h : logAnswer l (baseInput cv) = some b) :
    cv ∈ baseStates l b :=
  List.mem_filterMap.mpr ⟨_, MerkleTree.mem_of_logAnswer_eq_some h, by
    simp [baseInput, digestOfBytes_stepBytes]⟩

/-- A logged grinding check's group is among the log's checks. -/
private theorem mem_checkGroups {cv b d : Digest} {n : E} (hb : logAnswer l (baseInput cv) = some b)
    (hc : logAnswer l (checkInput b n) = some d) : (⟨cv, some n⟩ : Group) ∈ checkGroups l :=
  List.mem_flatMap.mpr ⟨_, MerkleTree.mem_of_logAnswer_eq_some hc, by
    simp only [checkInput_eq, Block.parse?_input, List.mem_map]
    exact ⟨cv, mem_baseStates hb, rfl⟩⟩

/-- A logged squeeze's state is among the log's squeeze states. -/
private theorem mem_squeezeStates {x d : Digest} (h : logAnswer l (squeezeInput x) = some d) :
    x ∈ squeezeStates l :=
  List.mem_filterMap.mpr ⟨_, MerkleTree.mem_of_logAnswer_eq_some h, by
    simp [squeezeInput, Block.parse?_input]⟩

namespace Group

/-- The proof of work of a group's nonce passes exactly when its check is answered with the low
zero bits. -/
private theorem powPasses_iff (bits : ℕ) (G : Group) :
    (∀ n, G.nonce = some n → PowPasses bits l G.cv n) ↔
      (G.nonce.isSome = true → ∃ d, G.check? l = some d ∧ FsState.lowBitsZero d bits = true) := by
  rcases hn : G.nonce with _ | n
  · simp
  · simp only [Option.isSome_some, forall_const, Option.some.injEq, forall_eq', PowPasses, check?,
      hn, Option.bind_some, Option.bind_eq_some_iff]
    exact ⟨fun ⟨b, d, hb, hd, hz⟩ ↦ ⟨d, ⟨b, hb, hd⟩, hz⟩,
      fun ⟨d, ⟨b, hb, hd⟩, hz⟩ ↦ ⟨b, d, hb, hd, hz⟩⟩

/-- A group with a logged query has its check, its nonce step or, with no nonce, its first
squeeze logged. -/
private theorem asked_cases {G : Group} {m : ℕ} (h : G.asked l m = true) :
    (∃ n b d, G.nonce = some n ∧ logAnswer l (baseInput G.cv) = some b ∧
      logAnswer l (checkInput b n) = some d) ∨
    (∃ n s, G.nonce = some n ∧ logAnswer l (absorbInput G.cv n) = some s) ∨
    (G.nonce = none ∧ ∃ d, logAnswer l (squeezeInput G.cv) = some d) := by
  rcases hn : G.nonce with _ | n
  · cases hx : logAnswer l (squeezeInput G.cv) with
    | none => simp [asked, check?, run, start?, hn, squeezeRun_eq_nil hx] at h
    | some d => exact .inr (.inr ⟨rfl, d, rfl⟩)
  · cases hs : logAnswer l (absorbInput G.cv n) with
    | some s => exact .inr (.inl ⟨n, s, rfl, hs⟩)
    | none =>
      simp only [asked, check?, run, start?, hn, hs, Option.bind_some, Option.isSome_some,
        Option.isSome_none, Bool.and_false, Bool.or_false, List.isEmpty_nil, Bool.not_true,
        Option.isSome_iff_exists, Option.bind_eq_some_iff] at h
      obtain ⟨d, b, hb, hd⟩ := h
      exact .inl ⟨n, b, d, rfl, hb, hd⟩

/-- A group with a logged query starts from a half of a logged query. -/
theorem exists_query_of_asked {G : Group} {m : ℕ} (h : G.asked l m = true) :
    ∃ q d, logAnswer l q = some d ∧ G.cv ∈ halves q := by
  rcases asked_cases h with ⟨-, b, -, -, hb, -⟩ | ⟨n, s, -, hs⟩ | ⟨-, d, hd⟩
  · exact ⟨_, b, hb, mem_halves_baseInput G.cv⟩
  · exact ⟨_, s, hs, mem_halves_input G.cv (.nonce n)⟩
  · exact ⟨_, d, hd, mem_halves_input G.cv .squeeze⟩

/-- A group with a logged query is a candidate of the log. -/
private theorem mem_candidates_of_asked {G : Group} {m : ℕ} (h : G.asked l m = true) :
    G ∈ candidates l := by
  obtain ⟨cv, nonce⟩ := G
  simp only [candidates, List.mem_append, List.mem_map]
  rcases asked_cases h with ⟨n, b, d, hn, hb, hd⟩ | ⟨n, s, hn, hs⟩ | ⟨hn, d, hd⟩ <;>
    cases hn
  · exact .inr (mem_checkGroups hb hd)
  · exact .inl (.inr (mem_nonceGroups hs))
  · exact .inl (.inl ⟨_, MerkleTree.mem_of_logAnswer_eq_some hd,
      by simp [squeezeInput, Block.input, digestOfBytes_stepBytes]⟩)

/-- The answer to a group's check does not change with one more clean query that is not the
check. -/
theorem check?_append (hs : CleanStep roots l t u) {G : Group}
    (ht : ∀ n b, G.nonce = some n → logAnswer l (baseInput G.cv) = some b → t ≠ checkInput b n) :
    G.check? (l ++ [⟨t, u⟩]) = G.check? l := by
  rcases hn : G.nonce with _ | n
  · simp [check?, hn]
  · simp only [check?, hn, Option.bind_some]
    by_cases htb : t = baseInput G.cv
    · subst htb
      rw [logAnswer_append_self hs.fresh, logAnswer_eq_none_iff.mpr hs.fresh, Option.bind_some,
        Option.bind_none]
      exact hs.logAnswer_eq_none (q := checkInput u n) (mem_halves_input u (.nonce n))
    · rw [logAnswer_append_of_ne (Ne.symm htb)]
      cases hb : logAnswer l (baseInput G.cv) with
      | none => rfl
      | some b => exact logAnswer_append_of_ne (Ne.symm (ht n b hn hb))

/-- The state a group's squeezes start from does not change with one more query that is not its
nonce step. -/
theorem start?_append {G : Group} (ht : ∀ n, G.nonce = some n → t ≠ absorbInput G.cv n) :
    G.start? (l ++ [⟨t, u⟩]) = G.start? l := by
  rcases hn : G.nonce with _ | n
  · simp [start?, hn]
  · simp only [start?, hn]
    exact logAnswer_append_of_ne (Ne.symm (ht n hn))

/-- A group's squeezes do not change with one more clean query that is not its next squeeze. -/
theorem run_append (hs : CleanStep roots l t u) {G : Group} {m : ℕ}
    (ht : ∀ s, G.start? l = some s → (squeezeRun l s m).length < m →
      t ≠ squeezeInput ((squeezeRun l s m).getLastD s)) :
    G.run (l ++ [⟨t, u⟩]) m = G.run l m := by
  by_cases hC : ∃ n, G.nonce = some n ∧ t = absorbInput G.cv n
  · obtain ⟨n, hn, rfl⟩ := hC
    simp only [run, start?, hn, logAnswer_append_self hs.fresh,
      logAnswer_eq_none_iff.mpr hs.fresh, squeezeRun_eq_nil hs.logAnswer_squeezeInput]
  · rw [run, start?_append fun n hn h ↦ hC ⟨n, hn, h⟩, run]
    cases hs₀ : G.start? l with
    | none => rfl
    | some s₀ =>
      simp only [squeezeRun_append hs.logAnswer_squeezeInput hs.fresh]
      split
      · exact absurd ‹_ ∧ _›.2 (ht s₀ hs₀ ‹_ ∧ _›.1)
      · exact List.append_nil _

/-- A logged start stays the group's in a longer log. -/
private theorem start?_append_of_eq_some {G : Group} {l' : hashSpec.QueryLog} {s : Digest}
    (h : G.start? l = some s) : G.start? (l ++ l') = some s := by
  rcases hn : G.nonce with _ | n <;> simp only [start?, hn] at h ⊢
  exacts [h, logAnswer_append_of_eq_some h]

/-- A logged check stays the group's in a longer log. -/
private theorem check?_append_of_eq_some {G : Group} {l' : hashSpec.QueryLog} {d : Digest}
    (h : G.check? l = some d) : G.check? (l ++ l') = some d := by
  simp only [check?, Option.bind_eq_some_iff] at h ⊢
  obtain ⟨n, hn, b, hb, hd⟩ := h
  exact ⟨n, hn, b, logAnswer_append_of_eq_some hb, logAnswer_append_of_eq_some hd⟩

end Group

/-- After one more clean query, a group with a logged query does not start from its answer. -/
private theorem CleanStep.cv_ne_of_asked (hs : CleanStep roots l t u) {G : Group} {m : ℕ}
    (h : G.asked (l ++ [⟨t, u⟩]) m = true) : G.cv ≠ u := by
  obtain ⟨q, d, hq, hcv⟩ := Group.exists_query_of_asked h
  rintro rfl
  by_cases hqt : q = t
  · subst hqt
    exact hs.notHalf hcv
  · rw [logAnswer_append_of_ne hqt] at hq
    exact hs.notInPlay (mem_inPlay_of_logAnswer hq hcv)

namespace SlotReader

variable (R : SlotReader)

/-! ## The groups a query touches -/

/-- A group's check touches it. -/
private theorem mem_touched_of_check {G : Group} {n : E} {b : Digest} (hn : G.nonce = some n)
    (hb : logAnswer l (baseInput G.cv) = some b) : G ∈ R.touched l (checkInput b n) := by
  obtain ⟨cv, nonce⟩ := G
  simp only at hn hb
  subst hn
  simp only [touched, checkInput_eq, Block.parse?_input, List.mem_cons, List.mem_map]
  exact .inr ⟨cv, mem_baseStates hb, rfl⟩

/-- A group's nonce step touches it. -/
private theorem mem_touched_of_absorb {G : Group} {n : E} (hn : G.nonce = some n) :
    G ∈ R.touched l (absorbInput G.cv n) := by
  obtain ⟨cv, nonce⟩ := G
  simp only at hn
  subst hn
  simp [touched, absorbInput, Block.parse?_input]

/-- A group's next squeeze touches it. -/
private theorem mem_touched_of_awaits {G : Group} {x : Digest} (h : R.awaits l G x = true) :
    G ∈ R.touched l (squeezeInput x) := by
  simp only [touched, squeezeInput, Block.parse?_input, List.mem_filter, h, and_true,
    List.mem_append, List.map_cons, List.mem_cons, List.mem_map]
  unfold awaits at h
  split at h
  · cases h
  · rename_i s hs
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨cv, nonce⟩ := G
    rcases nonce with _ | n
    · simp only [Group.start?, Option.some.injEq] at hs
      subst hs
      cases hx : logAnswer l (squeezeInput cv) with
      | none =>
        simp only [Group.run, Group.start?, squeezeRun_eq_nil hx, List.getLastD_nil] at h
        exact .inl (.inl (by rw [h.2]))
      | some d => exact .inl (.inr ⟨cv, mem_squeezeStates hx, rfl⟩)
    · exact .inr (mem_nonceGroups hs)

/-! ## What one more query changes -/

/-- A longer log leaves a group where it was: its challenge, its check, its start and its
squeezes. -/
private def Stays (l l' : hashSpec.QueryLog) (G : Group) : Prop :=
  R.groupSlot l' G = R.groupSlot l G ∧ G.check? l' = G.check? l ∧ G.start? l' = G.start? l ∧
    G.run l' (R.size l G) = G.run l (R.size l G)

/-- **One more clean query moves an untouched group nowhere**: a group the query does not touch,
not starting from its answer, stays where it was. -/
private theorem unmoved (hl : CleanLog roots l) (hs : CleanStep roots l t u) {G : Group}
    (hG : G.cv ≠ u) (hnot : G ∉ R.touched l t) : R.Stays l (l ++ [⟨t, u⟩]) G :=
  ⟨R.groupSlot_append (hl.append hs) hG,
    Group.check?_append hs fun n b hn hb h ↦ hnot (h ▸ R.mem_touched_of_check hn hb),
    Group.start?_append fun n hn h ↦ hnot (h ▸ R.mem_touched_of_absorb hn),
    Group.run_append hs fun s hs' hlen h ↦
      hnot (h ▸ R.mem_touched_of_awaits (by simp [awaits, hs', Group.run, hlen]))⟩

/-- **One more clean query moves a closed group nowhere**: all its queries are logged, so it
stays where it was. -/
private theorem unmoved_of_complete (hl : CleanLog roots (l ++ [⟨t, u⟩])) {G : Group}
    (hG : G.cv ≠ u) (hslot : (R.groupSlot l G).isSome = true)
    (hc : G.complete l (R.size l G) = true) : R.Stays l (l ++ [⟨t, u⟩]) G := by
  have hm : 0 < R.size l G := by
    obtain ⟨⟨a, i, tr⟩, hg⟩ := Option.isSome_iff_exists.mp hslot
    simpa [size, hg] using R.slot_pos a i
  simp only [Group.complete, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
  obtain ⟨hchk, hlen⟩ := hc
  obtain ⟨s, hs⟩ : ∃ s, G.start? l = some s := by
    cases h : G.start? l with
    | none => simp [Group.run, h] at hlen; omega
    | some s => exact ⟨s, rfl⟩
  have hst := Group.start?_append_of_eq_some (l' := [⟨t, u⟩]) hs
  refine ⟨R.groupSlot_append hl hG, ?_, hst.trans hs.symm, ?_⟩
  · rcases hchk with hn | hd
    · simp [Group.check?, Option.isNone_iff_eq_none.mp hn]
    · obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hd
      rw [hd, Group.check?_append_of_eq_some hd]
  · simp only [Group.run, hst, hs] at hlen ⊢
    exact squeezeRun_append_of_length hlen

/-- A group that stays where it was keeps whether it is open. -/
private theorem isOpen_eq_of_stays {l' : hashSpec.QueryLog} {G : Group} (h : R.Stays l l' G) :
    R.isOpen l' G = R.isOpen l G := by
  obtain ⟨hg, hc, hst, hr⟩ := h
  have hsize : R.size l' G = R.size l G := by simp only [size, hg]
  simp only [isOpen, Group.asked, Group.complete, hg, hsize, hc, hst, hr]

/-- A group that stays where it was keeps whether it flips. -/
private theorem flips_iff_of_stays {l' : hashSpec.QueryLog} {G : Group} (h : R.Stays l l' G) :
    R.Flips l' G ↔ R.Flips l G := by
  obtain ⟨hg, hc, -, hr⟩ := h
  unfold Flips
  rw [hg]
  cases hgs : R.groupSlot l G with
  | none => exact Iff.rfl
  | some x =>
    obtain ⟨a, i, tr⟩ := x
    simp only [size, hgs] at hr
    simp only [Group.powPasses_iff, hc, hr]

/-- A group that flips is closed, with a logged query. -/
theorem complete_of_flips {G : Group} (h : R.Flips l G) :
    (R.groupSlot l G).isSome = true ∧ G.complete l (R.size l G) = true ∧
      G.asked l (R.size l G) = true := by
  unfold Flips at h
  cases hgs : R.groupSlot l G with
  | none => simp [hgs] at h
  | some x =>
    obtain ⟨a, i, tr⟩ := x
    simp only [hgs, Group.powPasses_iff] at h
    obtain ⟨hlen, hpow, -⟩ := h
    have hne : G.run l (R.slot a i).m ≠ [] :=
      List.ne_nil_of_length_pos (by rw [hlen]; exact R.slot_pos a i)
    refine ⟨rfl, ?_, by simp [Group.asked, size, hgs, hne]⟩
    rcases hn : G.nonce with _ | n
    · simp [Group.complete, size, hgs, hn, hlen]
    · obtain ⟨d, hd, -⟩ := hpow (by simp [hn])
      simp [Group.complete, size, hgs, hlen, hd]

/-- **A group that flips has probability `1`** of closing on a bad challenge: nothing of it is
left to draw. -/
theorem π_eq_one_of_flips {G : Group} (h : R.Flips l G) : R.π l G = 1 := by
  unfold Flips at h
  unfold π
  cases hgs : R.groupSlot l G with
  | none => simp [hgs] at h
  | some x =>
    obtain ⟨a, i, tr⟩ := x
    simp only [hgs] at h ⊢
    obtain ⟨hlen, hpow, hbad⟩ := h
    rw [Group.powPasses_iff] at hpow
    refine (SampleableType.prEvent_uniformSample_eq_one_iff _).mpr fun z ↦ ⟨fun hn ↦ ?_, ?_⟩
    · obtain ⟨d, hd, hz⟩ := hpow hn
      simpa [hd] using hz
    · have hnil : List.ofFn z.2 = [] :=
        List.eq_nil_of_length_eq_zero (by rw [List.length_ofFn, hlen, Nat.sub_self])
      simpa [hnil] using hbad

/-- The open groups of a log are exactly its groups that are open. -/
theorem mem_openGroups_iff {G : Group} : G ∈ R.openGroups l ↔ R.isOpen l G = true := by
  simp only [openGroups, List.mem_toFinset, List.mem_filter]
  refine ⟨And.right, fun h ↦ ⟨Group.mem_candidates_of_asked (m := R.size l G) ?_, h⟩⟩
  simp only [isOpen, Bool.and_eq_true] at h
  exact h.1.2

/-- The groups a query opens are those it touches with no logged query. -/
theorem mem_openedBy_iff {G : Group} :
    G ∈ R.openedBy l t ↔ G ∈ R.touched l t ∧ G.asked l (R.size l G) = false := by
  simp [openedBy, List.mem_toFinset]

/-- After one more clean query, a group with a logged query that fixes a challenge is open
before it, opened by it, or stays where it was. -/
private theorem mem_or_stays (hl : CleanLog roots l) (hs : CleanStep roots l t u) {G : Group}
    {m : ℕ} (hask : G.asked (l ++ [⟨t, u⟩]) m = true)
    (hslot : (R.groupSlot (l ++ [⟨t, u⟩]) G).isSome = true) :
    G ∈ R.openGroups l ∪ R.openedBy l t ∨ R.Stays l (l ++ [⟨t, u⟩]) G := by
  have hcv : G.cv ≠ u := hs.cv_ne_of_asked hask
  rw [R.groupSlot_append (hl.append hs) hcv] at hslot
  rw [Finset.mem_union, mem_openGroups_iff, mem_openedBy_iff]
  by_cases ht : G ∈ R.touched l t
  · cases ha : G.asked l (R.size l G) with
    | false => exact .inl (.inr ⟨ht, rfl⟩)
    | true =>
      cases hc : G.complete l (R.size l G) with
      | false => exact .inl (.inl (by simp [isOpen, hslot, ha, hc]))
      | true => exact .inr (R.unmoved_of_complete (hl.append hs) hcv hslot hc)
  · exact .inr (R.unmoved hl hs hcv ht)

/-- **The open groups after one more clean query** are open before it or opened by it. -/
theorem openGroups_append_subset (hl : CleanLog roots l) (hs : CleanStep roots l t u) :
    R.openGroups (l ++ [⟨t, u⟩]) ⊆ R.openGroups l ∪ R.openedBy l t := by
  intro G hG
  rw [mem_openGroups_iff] at hG
  have h := hG
  simp only [isOpen, Bool.and_eq_true] at h
  rcases R.mem_or_stays hl hs h.1.2 h.1.1 with h | h
  · exact h
  · exact Finset.mem_union_left _
      ((R.mem_openGroups_iff).mpr ((R.isOpen_eq_of_stays h).symm.trans hG))

/-- A flip stays one when the log grows by a query and stays clean. -/
theorem flipAt_append_of_flipAt (hl : CleanLog roots (l ++ [⟨t, u⟩])) (h : R.FlipAt l) :
    R.FlipAt (l ++ [⟨t, u⟩]) := by
  obtain ⟨G, hG⟩ := h
  obtain ⟨hslot, hc, ha⟩ := R.complete_of_flips hG
  obtain ⟨q, d, hq, hcv⟩ := Group.exists_query_of_asked ha
  have hne : G.cv ≠ u := fun h ↦
    hl.notInPlay_of_append (h ▸ mem_inPlay_of_logAnswer (roots := roots) hq hcv)
  exact ⟨G, (R.flips_iff_of_stays (R.unmoved_of_complete hl hne hslot hc)).mpr hG⟩

/-- A group a query touches starts from a half of the query or from a digest in play. -/
theorem cv_mem_of_mem_touched {G : Group} (h : G ∈ R.touched l t) :
    G.cv ∈ halves t ∨ G.cv ∈ inPlay roots l := by
  unfold touched at h
  split at h
  · rename_i x hx
    simp only [List.mem_filter, List.mem_append, List.map_cons, List.mem_cons, List.mem_map,
      squeezeStates, nonceGroups, List.mem_filterMap] at h
    obtain ⟨(rfl | ⟨y, ⟨e, he, hy⟩, rfl⟩) | ⟨e, he, hg⟩, -⟩ := h
    · exact .inl (mem_halves_of_parse? hx)
    · split at hy <;> cases hy
      exact .inr (mem_inPlay_of_mem_halves he (mem_halves_of_parse? ‹_›))
    · split at hg <;> cases hg
      exact .inr (mem_inPlay_of_mem_halves he (mem_halves_of_parse? ‹_›))
  · rename_i y n hy
    simp only [List.mem_cons, List.mem_map, baseStates, List.mem_filterMap,
      Option.ite_none_right_eq_some, Option.some.injEq] at h
    rcases h with rfl | ⟨cv, ⟨e, he, ⟨-, hb⟩, rfl⟩, rfl⟩
    · exact .inl (mem_halves_of_parse? hy)
    · exact .inr (mem_inPlay_of_mem_halves he
        (by rw [congrArg halves hb]; exact mem_halves_baseInput _))
  · simp at h

/-- **A flip after one more clean query** is a group open before it or opened by it, which flips
after it, at probability `1`. -/
theorem flipAt_append (hl : CleanLog roots l) (hs : CleanStep roots l t u) (hno : ¬ R.FlipAt l)
    (h : R.FlipAt (l ++ [⟨t, u⟩])) :
    ∃ G ∈ R.openGroups l ∪ R.openedBy l t,
      R.Flips (l ++ [⟨t, u⟩]) G ∧ R.π (l ++ [⟨t, u⟩]) G = 1 := by
  obtain ⟨G, hG⟩ := h
  obtain ⟨hslot, -, hask⟩ := R.complete_of_flips hG
  refine ⟨G, ?_, hG, R.π_eq_one_of_flips hG⟩
  exact (R.mem_or_stays hl hs hask hslot).resolve_right fun h ↦
    hno ⟨G, (R.flips_iff_of_stays h).mp hG⟩

/-! ## The log with each query at its first occurrence -/

/-- On a consistent log, the challenge a group fixes is the one it fixes in the deduplicated
log. -/
theorem groupSlot_dedupKeys (hcons : QueryLog.Consistent l) (G : Group) :
    R.groupSlot (List.dedupKeys l) G = R.groupSlot l G := by
  have hst := R.stmtAt_dedupKeys l hcons
  have hS : R.isStart (List.dedupKeys l) = R.isStart l := funext fun d ↦ by
    simp only [ChainStarts.isStart, hst d]
  unfold groupSlot
  rw [hS, chainHistory_dedupKeys hcons]
  cases h : chainHistory l (R.isStart l) ⟨G.cv⟩ with
  | none => rfl
  | some hs =>
    simp only [Option.bind_eq_bind, Option.bind_some, hst,
      R.wordsAt_congr _ l _ hs.2 fun root _ depth rowWords leafWords p ↦
        extractRows_dedupKeys hcons root depth rowWords leafWords p]

/-- **A flip of a consistent log is one of its deduplication**, the log of a lazy random
oracle's fresh queries: the groups read the log through its histories, its rows and its answers,
which deduplication keeps. -/
theorem flipAt_dedupKeys (hcons : QueryLog.Consistent l) (h : R.FlipAt l) :
    R.FlipAt (List.dedupKeys l) := by
  obtain ⟨G, hG⟩ := h
  have ha := logAnswer_dedupKeys hcons
  have hst : R.Stays l (List.dedupKeys l) G :=
    ⟨R.groupSlot_dedupKeys hcons G, by simp only [Group.check?, ha],
      by cases hn : G.nonce <;> simp only [Group.start?, hn, ha],
      by simp only [Group.run, Group.start?, ha, squeezeRun_congr ha]⟩
  exact ⟨G, (R.flips_iff_of_stays hst).mpr hG⟩

end SlotReader

end
end LeanerVM.Protocol
