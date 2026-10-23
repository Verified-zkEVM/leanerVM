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

**Reading a history** (`SlotReader`). How a history of the chain is read as a prefix of a
protocol's transcript is a parameter: the announcement a history opens with, the protocol at it,
the longest prefix of its transcript a history reads (`decodePrefix`), each challenge as a
`SqueezeSlot` (the number of squeezes, the challenge their digests give, and that uniform digests
give a uniform challenge), the marked challenges, and the bad challenges at each prefix. It
carries the facts about the decoder that tie a group's challenge to the protocol's: the words of
the oracle messages depend on the log only under the roots the history absorbs, a history decodes
at its own announcement, a challenge reads its squeezes, no slot reads the state an observe or a
nonce step leads to, a marked challenge follows a nonce, and a challenge reads a squeeze at least.

**A group's status in a log** of fresh queries, read through first occurrences (`logAnswer`):
`groupSlot` reads the group's challenge off the history of its state, with the group's nonce step
for a group with a nonce, and keeps it when the challenge is marked exactly when the group has a
nonce; `Group.run` is the digests of the group's squeezes so far, `Group.check?` the answer to its
check; `isOpen` says some query of the group is logged and not all; `isClosed` that all are.
`Flips` says the group is closed on a bad challenge, its proof of work passing (`PowPasses`);
`FlipAt` that some group flips; `π` is the probability, over fresh uniform answers to its unasked
queries, that the group closes on a bad challenge, `1` on a group that flips
(`π_eq_one_of_flips`).

**One more query** (`CleanLog`, `CleanStep`): a fresh query whose answer is no logged answer, not
in play and not a half of the query. Then the history of every other state and the words read
under it do not change (`chainHistory_append`, `SlotReader.wordsAt_append`,
`SlotReader.groupSlot_append`). `touched` lists the groups the query may advance or open; every
other group (`unmoved`), and every closed group (`unmoved_of_complete`), keeps its challenge, its
check and its squeezes, so its status, its flip and its probability (`status_of_unmoved`). The
open groups after the query are open before it or opened by it (`openGroups_append_subset`), and a
flip after the query, with none before, is a group open before it or opened by it, at probability
`1` after it (`flipAt_append`).
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

/-! ## Reading a history -/

/-- **A reader of chain histories**: the protocol a history of the chain is a transcript prefix
of, how a history is read, and the facts about the reading that tie a group's challenge to the
protocol's. -/
structure SlotReader where
  /-- The chain's first state. -/
  seed : Digest
  /-- The low zero bits a proof of work asks for. -/
  powBits : ℕ
  /-- The announcements a history may open with. -/
  Ann : Type
  /-- The announcement a history opens with. -/
  announcementOf : List (Block × Digest) → Option Ann
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
  /-- The words depend on the log only through the rows under the roots the history absorbs. -/
  wordsAt_congr : ∀ a (l l' : hashSpec.QueryLog) (hs : List (Block × Digest)),
    (∀ root ∈ historyRoots hs, ∀ depth rowWords leafWords p,
      extractRows l' root depth rowWords leafWords p = extractRows l root depth rowWords leafWords p) →
    wordsAt a l' hs = wordsAt a l hs
  /-- A history decodes at its own announcement only. -/
  decodePrefix_announcement : ∀ a W hs x, decodePrefix a W hs = some x → announcementOf hs = some a
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
  /-- Every challenge reads a squeeze at least. -/
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
are answered, the check with `bits` low zero bits. -/
def PowPasses (bits : ℕ) (l : hashSpec.QueryLog) (cv : Digest) (n : E) : Prop :=
  ∃ base d, logAnswer l (baseInput cv) = some base ∧ logAnswer l (checkInput base n) = some d ∧
    FsState.lowBitsZero d bits = true

namespace SlotReader

variable (R : SlotReader) (l : hashSpec.QueryLog)

/-- **The challenge a group fixes**, read off the log: the history of its state, the announcement
the history opens with, and the prefix the history, with the group's nonce step, reads, when the
next round is a challenge, marked exactly when the group has a nonce. -/
def groupSlot (G : Group) :
    Option (Σ a : R.Ann, Σ i : (R.spec a).ChallengeIdx, (R.spec a).Transcript i.1.castSucc) := do
  let hs ← chainHistory l ⟨R.seed⟩ ⟨G.cv⟩
  let a ← R.announcementOf hs
  let p ← R.decodePrefix a (R.wordsAt a l hs) (hs ++ G.nonceBlock)
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

private theorem powBaseTag_ne_observeTag : FsState.powBaseTag ≠ FsState.observeTag := by
  decide +kernel

private theorem powBaseTag_ne_squeezeTag : FsState.powBaseTag ≠ FsState.squeezeTag := by
  decide +kernel

private theorem powBaseTag_ne_powNonceTag : FsState.powBaseTag ≠ FsState.powNonceTag := by
  decide +kernel

/-- The state a 64-byte hash of the chain starts from is its first half. -/
theorem digestOfBytes_stepBytes (cv : Digest) (x : E) (tag : K) :
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
  simp [powBaseTag_ne_observeTag, powBaseTag_ne_squeezeTag, powBaseTag_ne_powNonceTag]

/-- The grinding base is no step's input. -/
theorem baseInput_ne_input (cv x : Digest) (b : Block) : baseInput cv ≠ Block.input x b :=
  fun h ↦ by simpa [h, Block.parse?_input] using parse?_baseInput cv

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
theorem mem_halves_input (cv : Digest) (b : Block) : cv ∈ halves (Block.input cv b) :=
  mem_halves_stepBytes cv b.elem b.tag

/-- The grinding base from a state has the state as a half. -/
theorem mem_halves_baseInput (cv : Digest) : cv ∈ halves (baseInput cv) :=
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
    x ∈ inPlay roots l := by
  simp only [inPlay, List.mem_append, List.mem_flatMap]
  exact .inl (.inr ⟨⟨q, d⟩, MerkleTree.mem_of_logAnswer_eq_some h, hx⟩)

/-! ## Clean logs and one more clean query -/

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

variable {roots : List Digest} {l : hashSpec.QueryLog} {t : List UInt8} {u : Digest}

/-- A log with each input once is consistent. -/
theorem CleanLog.consistent (hl : CleanLog roots l) : QueryLog.Consistent l := by
  intro e₁ h₁ e₂ h₂ h
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp h₁
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp h₂
  have : i = j := (hl.nodup.getElem_inj_iff (hi := by simpa using hi)
    (hj := by simpa using hj)).mp (by simpa using h)
  subst this
  rfl

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
theorem CleanLog.fresh_of_append (hl : CleanLog roots (l ++ [⟨t, u⟩])) : QueryLog.Fresh l t :=
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
theorem last_take_succ {α : Type} : ∀ (cv : Digest) (hs : List (α × Digest)) (j : ℕ)
    (hj : j < hs.length), HashChain.last cv (hs.take (j + 1)) = hs[j].2
  | _, (_, c) :: rest, 0, _ => by simp [HashChain.last]
  | _, (_, c) :: rest, j + 1, hj => by
    simp only [List.take_succ_cons, HashChain.last, List.getElem_cons_succ]
    exact last_take_succ c rest j (by simpa using hj)

/-- Two consecutive observes of a history, and the root they absorb. -/
theorem mem_historyRoots : ∀ {hs : List (Block × Digest)} {r : Digest}, r ∈ historyRoots hs →
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
private theorem findSome?_eq_some_of {α γ : Type} {f : α → Option γ} {y : γ} :
    ∀ {l : List α}, (∀ a ∈ l, f a = none ∨ f a = some y) → (∃ a ∈ l, f a = some y) →
      l.findSome? f = some y
  | [], _, ⟨_, ha, _⟩ => nomatch ha
  | a :: l, hall, ⟨b, hb, hfb⟩ => by
    rw [List.findSome?_cons]
    rcases hall a List.mem_cons_self with ha | ha
    · rw [ha]
      rcases List.mem_cons.mp hb with rfl | hb
      · rw [ha] at hfb; cases hfb
      · exact findSome?_eq_some_of (fun c hc ↦ hall c (List.mem_cons_of_mem _ hc)) ⟨b, hb, hfb⟩
    · rw [ha]

/-- **The roots a history absorbs are rebuilt by the log**: on a log with no collision, two
consecutive observes of a history are logged steps, the second from the state the first leads
to, so the root they encode is one the log rebuilds. -/
theorem historyRoots_subset_rebuiltRoots (hcoll : ¬ QueryLog.HasCollision l) {seed s : FsState}
    {hs : List (Block × Digest)} (h : chainHistory l seed s = some hs) :
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
theorem SlotReader.wordsAt_append (R : SlotReader) (hl : CleanLog roots (l ++ [⟨t, u⟩]))
    {s : FsState} {h' : List (Block × Digest)} (h : chainHistory l ⟨R.seed⟩ s = some h')
    (a : R.Ann) : R.wordsAt a (l ++ [⟨t, u⟩]) h' = R.wordsAt a l h' := by
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
  unfold SlotReader.groupSlot
  rw [chainHistory_append (e := ⟨t, u⟩) hl.notInPlay_of_append ⟨R.seed⟩ (s := ⟨G.cv⟩) hG]
  rcases h : chainHistory l ⟨R.seed⟩ ⟨G.cv⟩ with _ | h'
  · rfl
  · simp only [Option.bind_eq_bind, Option.bind_some, R.wordsAt_append hl h]

/-- The size of a group's challenge does not change with one more clean query, unless the group
starts from its answer. -/
theorem SlotReader.size_append (R : SlotReader) (hl : CleanLog roots (l ++ [⟨t, u⟩]))
    {G : Group} (hG : G.cv ≠ u) : R.size (l ++ [⟨t, u⟩]) G = R.size l G := by
  simp only [SlotReader.size, R.groupSlot_append hl hG]

/-! ## A group's queries after one more query -/

/-- A log asked no squeeze from `x` has no squeezes from it. -/
theorem squeezeRun_eq_nil {x : Digest} (h : logAnswer l (squeezeInput x) = none) (m : ℕ) :
    squeezeRun l x m = [] := by
  cases m <;> simp [squeezeRun, h]

/-- A run of all its squeezes is the same in a longer log. -/
theorem squeezeRun_append_of_length {l' : hashSpec.QueryLog} :
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
theorem CleanStep.logAnswer_eq_none (hs : CleanStep roots l t u) {q : List UInt8}
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

/-- A logged nonce step's group is among the log's absorptions. -/
theorem mem_nonceGroups {cv s : Digest} {n : E} (h : logAnswer l (absorbInput cv n) = some s) :
    (⟨cv, some n⟩ : Group) ∈ nonceGroups l :=
  List.mem_filterMap.mpr ⟨_, MerkleTree.mem_of_logAnswer_eq_some h, by
    simp [absorbInput, Block.parse?_input]⟩

/-- A state whose grinding base the log answers by `b` is among the base states of `b`. -/
theorem mem_baseStates {cv b : Digest} (h : logAnswer l (baseInput cv) = some b) :
    cv ∈ baseStates l b :=
  List.mem_filterMap.mpr ⟨_, MerkleTree.mem_of_logAnswer_eq_some h, by
    simp [baseInput, digestOfBytes_stepBytes]⟩

/-- A logged grinding check's group is among the log's checks. -/
theorem mem_checkGroups {cv b d : Digest} {n : E} (hb : logAnswer l (baseInput cv) = some b)
    (hc : logAnswer l (checkInput b n) = some d) : (⟨cv, some n⟩ : Group) ∈ checkGroups l :=
  List.mem_flatMap.mpr ⟨_, MerkleTree.mem_of_logAnswer_eq_some hc, by
    simp only [checkInput_eq, Block.parse?_input, List.mem_map]
    exact ⟨cv, mem_baseStates hb, rfl⟩⟩

/-- A logged squeeze's state is among the log's squeeze states. -/
theorem mem_squeezeStates {x d : Digest} (h : logAnswer l (squeezeInput x) = some d) :
    x ∈ squeezeStates l :=
  List.mem_filterMap.mpr ⟨_, MerkleTree.mem_of_logAnswer_eq_some h, by
    simp [squeezeInput, Block.parse?_input]⟩

namespace Group

/-- The proof of work of a group's nonce passes exactly when its check is answered with the low
zero bits. -/
theorem powPasses_iff (bits : ℕ) (G : Group) :
    (∀ n, G.nonce = some n → PowPasses bits l G.cv n) ↔
      (G.nonce.isSome = true → ∃ d, G.check? l = some d ∧ FsState.lowBitsZero d bits = true) := by
  rcases hn : G.nonce with _ | n
  · simp
  · simp only [Option.isSome_some, forall_const, Option.some.injEq, forall_eq', PowPasses, check?,
      hn, Option.bind_some, Option.bind_eq_some_iff]
    exact ⟨fun ⟨b, d, hb, hd, hz⟩ ↦ ⟨d, ⟨b, hb, hd⟩, hz⟩,
      fun ⟨d, ⟨b, hb, hd⟩, hz⟩ ↦ ⟨b, d, hb, hd, hz⟩⟩

/-- A group with a logged query starts from a half of a logged query. -/
theorem exists_query_of_asked {G : Group} {m : ℕ} (h : G.asked l m = true) :
    ∃ q d, logAnswer l q = some d ∧ G.cv ∈ halves q := by
  simp only [asked, Bool.or_eq_true, Bool.and_eq_true, Option.isSome_iff_exists] at h
  rcases hn : G.nonce with _ | n
  · rcases h with (⟨d, hd⟩ | ⟨⟨_, h⟩, -⟩) | h
    · simp [check?, hn] at hd
    · simp [hn] at h
    · simp only [run, start?, hn] at h
      cases hx : logAnswer l (squeezeInput G.cv) with
      | none => simp [squeezeRun_eq_nil hx] at h
      | some d => exact ⟨_, d, hx, mem_halves_input G.cv .squeeze⟩
  · have habs : (G.start? l).isSome = true → ∃ q d, logAnswer l q = some d ∧ G.cv ∈ halves q :=
      fun h ↦ by
        obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp h
        simp only [start?, hn] at hs
        exact ⟨_, s, hs, mem_halves_input G.cv (.nonce n)⟩
    rcases h with (⟨d, hd⟩ | ⟨-, ⟨s, hs⟩⟩) | h
    · simp only [check?, hn, Option.bind_some, Option.bind_eq_some_iff] at hd
      obtain ⟨b, hb, -⟩ := hd
      exact ⟨_, b, hb, mem_halves_baseInput G.cv⟩
    · exact habs (by simp [hs])
    · refine habs ?_
      simp only [run] at h
      split at h
      · simp at h
      · rename_i s hs
        simp [hs]

/-- A group with a logged query is a candidate of the log. -/
theorem mem_candidates_of_asked {G : Group} {m : ℕ} (h : G.asked l m = true) :
    G ∈ candidates l := by
  simp only [asked, Bool.or_eq_true, Bool.and_eq_true, Option.isSome_iff_exists] at h
  obtain ⟨cv, nonce⟩ := G
  simp only [candidates, List.mem_append, List.mem_map]
  rcases nonce with _ | n
  · rcases h with (⟨d, hd⟩ | ⟨⟨_, h⟩, -⟩) | h
    · simp [check?] at hd
    · simp at h
    · simp only [run, start?] at h
      cases hx : logAnswer l (squeezeInput cv) with
      | none => simp [squeezeRun_eq_nil hx] at h
      | some d =>
        exact .inl (.inl ⟨_, MerkleTree.mem_of_logAnswer_eq_some hx,
          by simp [squeezeInput, Block.input, digestOfBytes_stepBytes]⟩)
  · have habs : (Group.start? l ⟨cv, some n⟩).isSome = true →
        ((∃ a ∈ l, (⟨digestOfBytes a.1, none⟩ : Group) = ⟨cv, some n⟩) ∨
          ⟨cv, some n⟩ ∈ nonceGroups l) ∨ ⟨cv, some n⟩ ∈ checkGroups l := fun h ↦ by
      obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp h
      exact .inl (.inr (mem_nonceGroups hs))
    rcases h with (⟨d, hd⟩ | ⟨-, ⟨s, hs⟩⟩) | h
    · simp only [check?, Option.bind_some, Option.bind_eq_some_iff] at hd
      obtain ⟨b, hb, hc⟩ := hd
      exact .inr (mem_checkGroups hb hc)
    · exact habs (by simp [hs])
    · refine habs ?_
      simp only [run] at h
      split at h
      · simp at h
      · rename_i s hs
        simp [hs]

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

end Group

/-- After one more clean query, a group with a logged query does not start from its answer. -/
theorem CleanStep.cv_ne_of_asked (hs : CleanStep roots l t u) {G : Group} {m : ℕ}
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
theorem mem_touched_of_check {G : Group} {n : E} {b : Digest} (hn : G.nonce = some n)
    (hb : logAnswer l (baseInput G.cv) = some b) : G ∈ R.touched l (checkInput b n) := by
  obtain ⟨cv, nonce⟩ := G
  simp only at hn hb
  subst hn
  simp only [touched, checkInput_eq, Block.parse?_input, List.mem_cons, List.mem_map]
  exact .inr ⟨cv, mem_baseStates hb, rfl⟩

/-- A group's nonce step touches it. -/
theorem mem_touched_of_absorb {G : Group} {n : E} (hn : G.nonce = some n) :
    G ∈ R.touched l (absorbInput G.cv n) := by
  obtain ⟨cv, nonce⟩ := G
  simp only at hn
  subst hn
  simp [touched, absorbInput, Block.parse?_input]

/-- A group's next squeeze touches it. -/
theorem mem_touched_of_awaits {G : Group} {x : Digest} (h : R.awaits l G x = true) :
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

/-- **One more clean query moves an untouched group nowhere**: a group the query does not touch,
not starting from its answer, keeps its challenge, its check, its start and its squeezes. -/
theorem unmoved (hl : CleanLog roots l) (hs : CleanStep roots l t u) {G : Group}
    (hG : G.cv ≠ u) (hnot : G ∉ R.touched l t) :
    R.groupSlot (l ++ [⟨t, u⟩]) G = R.groupSlot l G ∧ G.check? (l ++ [⟨t, u⟩]) = G.check? l ∧
      G.start? (l ++ [⟨t, u⟩]) = G.start? l ∧
      G.run (l ++ [⟨t, u⟩]) (R.size l G) = G.run l (R.size l G) := by
  have hst : G.start? (l ++ [⟨t, u⟩]) = G.start? l :=
    Group.start?_append fun n hn h ↦ hnot (h ▸ R.mem_touched_of_absorb hn)
  refine ⟨R.groupSlot_append (hl.append hs) hG,
    Group.check?_append hs fun n b hn hb h ↦ hnot (h ▸ R.mem_touched_of_check hn hb), hst, ?_⟩
  unfold Group.run
  rw [hst]
  split
  · rfl
  · rename_i s hs'
    rw [squeezeRun_append hs.logAnswer_squeezeInput hs.fresh]
    split
    · rename_i hc
      refine absurd ?_ hnot
      rw [hc.2]
      refine R.mem_touched_of_awaits ?_
      simp [awaits, hs', Group.run, hc.1]
    · simp

/-- **One more clean query moves a closed group nowhere**: all its queries are logged, so it
keeps its challenge, its check, its start and its squeezes. -/
theorem unmoved_of_complete (hl : CleanLog roots (l ++ [⟨t, u⟩])) {G : Group}
    (hG : G.cv ≠ u) (hslot : (R.groupSlot l G).isSome = true)
    (hc : G.complete l (R.size l G) = true) :
    R.groupSlot (l ++ [⟨t, u⟩]) G = R.groupSlot l G ∧ G.check? (l ++ [⟨t, u⟩]) = G.check? l ∧
      G.start? (l ++ [⟨t, u⟩]) = G.start? l ∧
      G.run (l ++ [⟨t, u⟩]) (R.size l G) = G.run l (R.size l G) := by
  have hm : 0 < R.size l G := by
    obtain ⟨⟨a, i, tr⟩, hg⟩ := Option.isSome_iff_exists.mp hslot
    simpa [size, hg] using R.slot_pos a i
  simp only [Group.complete, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
  obtain ⟨hchk, hlen⟩ := hc
  have hst : G.start? (l ++ [⟨t, u⟩]) = G.start? l := by
    rcases hn : G.nonce with _ | n
    · simp [Group.start?, hn]
    · have hsome : (G.start? l).isSome = true := by
        cases h : G.start? l with
        | none => simp [Group.run, h] at hlen; omega
        | some s => rfl
      obtain ⟨s, hs'⟩ := Option.isSome_iff_exists.mp hsome
      simp only [Group.start?, hn] at hs' ⊢
      rw [logAnswer_append_of_eq_some hs', hs']
  refine ⟨R.groupSlot_append hl hG, ?_, hst, ?_⟩
  · rcases hn : G.nonce with _ | n
    · simp [Group.check?, hn]
    · rw [hn] at hchk
      simp only [Option.isNone_some, Bool.false_eq_true, false_or] at hchk
      obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hchk
      simp only [Group.check?, hn, Option.bind_some, Option.bind_eq_some_iff] at hd ⊢
      obtain ⟨b, hb, hcd⟩ := hd
      rw [logAnswer_append_of_eq_some hb, Option.bind_some, logAnswer_append_of_eq_some hcd,
        hb, Option.bind_some, hcd]
  · unfold Group.run at hlen ⊢
    rw [hst]
    split
    · rfl
    · rename_i s hs'
      rw [hs'] at hlen
      exact squeezeRun_append_of_length hlen

/-- **A group unmoved by a log's growth keeps its status**: the size of its challenge, whether
it has a logged query, whether it is open or closed, whether it flips, and its probability. -/
theorem status_of_unmoved {l' : hashSpec.QueryLog} {G : Group}
    (h : R.groupSlot l' G = R.groupSlot l G ∧ G.check? l' = G.check? l ∧
      G.start? l' = G.start? l ∧ G.run l' (R.size l G) = G.run l (R.size l G)) :
    R.size l' G = R.size l G ∧ G.asked l' (R.size l' G) = G.asked l (R.size l G) ∧
      R.isOpen l' G = R.isOpen l G ∧ R.isClosed l' G = R.isClosed l G ∧
      (R.Flips l' G ↔ R.Flips l G) ∧ R.π l' G = R.π l G := by
  obtain ⟨hg, hc, hst, hr⟩ := h
  have hsize : R.size l' G = R.size l G := by simp only [size, hg]
  have hasked : G.asked l' (R.size l' G) = G.asked l (R.size l G) := by
    simp only [Group.asked, hsize, hc, hst, hr]
  have hcomp : G.complete l' (R.size l' G) = G.complete l (R.size l G) := by
    simp only [Group.complete, hsize, hc, hr]
  refine ⟨hsize, hasked, ?_, ?_, ?_, ?_⟩
  · simp only [isOpen, hg, hasked, hcomp]
  · simp only [isClosed, hg, hcomp]
  · unfold Flips
    rw [hg]
    cases hgs : R.groupSlot l G with
    | none => exact Iff.rfl
    | some x =>
      obtain ⟨a, i, tr⟩ := x
      have hm : R.size l G = (R.slot a i).m := by simp [size, hgs]
      rw [hm] at hr
      simp only
      rw [Group.powPasses_iff, Group.powPasses_iff, hc, hr]
  · unfold π
    rw [hg]
    cases hgs : R.groupSlot l G with
    | none => rfl
    | some x =>
      obtain ⟨a, i, tr⟩ := x
      have hm : R.size l G = (R.slot a i).m := by simp [size, hgs]
      rw [hm] at hr
      simp only
      rw [hc, hr]

/-- A group that flips is closed, with a logged query. -/
theorem complete_of_flips {G : Group} (h : R.Flips l G) :
    (R.groupSlot l G).isSome = true ∧ G.complete l (R.size l G) = true ∧
      G.asked l (R.size l G) = true := by
  unfold Flips at h
  cases hgs : R.groupSlot l G with
  | none => simp [hgs] at h
  | some x =>
    obtain ⟨a, i, tr⟩ := x
    simp only [hgs] at h
    obtain ⟨hlen, hpow, -⟩ := h
    have hm : R.size l G = (R.slot a i).m := by simp [size, hgs]
    have hpos := R.slot_pos a i
    rw [Group.powPasses_iff] at hpow
    refine ⟨rfl, ?_, ?_⟩
    · simp only [Group.complete, hm, hlen, beq_self_eq_true, Bool.and_true, Bool.or_eq_true]
      rcases hn : G.nonce with _ | n
      · simp
      · obtain ⟨d, hd, -⟩ := hpow (by simp [hn])
        simp [hd]
    · simp only [Group.asked, hm, Bool.or_eq_true]
      right
      cases hr : G.run l (R.slot a i).m with
      | nil => rw [hr] at hlen; simp at hlen; omega
      | cons _ _ => rfl

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

/-- **The open groups after one more clean query** are open before it or opened by it. -/
theorem openGroups_append_subset (hl : CleanLog roots l) (hs : CleanStep roots l t u) :
    R.openGroups (l ++ [⟨t, u⟩]) ⊆ R.openGroups l ∪ R.openedBy l t := by
  intro G hG
  rw [mem_openGroups_iff] at hG
  have hG' := hG
  simp only [isOpen, Bool.and_eq_true, Bool.not_eq_true'] at hG'
  obtain ⟨⟨hslot', hask'⟩, hcomp'⟩ := hG'
  have hcv : G.cv ≠ u := hs.cv_ne_of_asked hask'
  have hslot : (R.groupSlot l G).isSome = true := by
    rwa [R.groupSlot_append (hl.append hs) hcv] at hslot'
  rw [Finset.mem_union, mem_openGroups_iff, mem_openedBy_iff]
  by_cases ht : G ∈ R.touched l t
  · cases ha : G.asked l (R.size l G) with
    | false => exact .inr ⟨ht, rfl⟩
    | true =>
      refine .inl ?_
      cases hc : G.complete l (R.size l G) with
      | false => simp [isOpen, hslot, ha, hc]
      | true =>
        have := (R.status_of_unmoved (R.unmoved_of_complete (hl.append hs) hcv hslot hc)).2.2.1
        rw [hG] at this
        simp [isOpen, hc] at this
  · exact .inl ((R.status_of_unmoved (R.unmoved hl hs hcv ht)).2.2.1 ▸ hG)

/-- A flip stays one when the log grows by a query and stays clean. -/
theorem flipAt_append_of_flipAt (hl : CleanLog roots (l ++ [⟨t, u⟩])) (h : R.FlipAt l) :
    R.FlipAt (l ++ [⟨t, u⟩]) := by
  obtain ⟨G, hG⟩ := h
  obtain ⟨hslot, hc, ha⟩ := R.complete_of_flips hG
  obtain ⟨q, d, hq, hcv⟩ := Group.exists_query_of_asked ha
  have hne : G.cv ≠ u := fun h ↦
    hl.notInPlay_of_append (h ▸ mem_inPlay_of_logAnswer (roots := roots) hq hcv)
  exact ⟨G, (R.status_of_unmoved (R.unmoved_of_complete hl hne hslot hc)).2.2.2.2.1.mpr hG⟩

/-- A group a query touches starts from a half of the query or from a digest in play. -/
theorem cv_mem_of_mem_touched {G : Group} (h : G ∈ R.touched l t) :
    G.cv ∈ halves t ∨ G.cv ∈ inPlay roots l := by
  unfold touched at h
  have hlog : ∀ e ∈ l, ∀ y b, Block.parse? e.1 = some (y, b) → y ∈ inPlay roots l :=
    fun e he y b hp ↦ by
      simp only [inPlay, List.mem_append, List.mem_flatMap]
      exact .inl (.inr ⟨e, he, mem_halves_of_parse? hp⟩)
  split at h
  · rename_i x hx
    simp only [List.mem_filter, List.mem_append, List.map_cons, List.mem_cons, List.mem_map] at h
    obtain ⟨(rfl | ⟨y, hy, rfl⟩) | hn, -⟩ := h
    · exact .inl (mem_halves_of_parse? hx)
    · obtain ⟨e, he, hy⟩ := List.mem_filterMap.mp hy
      split at hy
      · rename_i y' hp
        cases hy
        exact .inr (hlog e he _ _ hp)
      · cases hy
    · obtain ⟨e, he, hg⟩ := List.mem_filterMap.mp hn
      split at hg
      · rename_i cv n hp
        cases hg
        exact .inr (hlog e he _ _ hp)
      · cases hg
  · rename_i y n hy
    simp only [List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨cv, hcv, rfl⟩
    · exact .inl (mem_halves_of_parse? hy)
    · obtain ⟨e, he, hb⟩ := List.mem_filterMap.mp hcv
      split at hb
      · rename_i hcond
        cases hb
        refine .inr ?_
        simp only [inPlay, List.mem_append, List.mem_flatMap]
        refine .inl (.inr ⟨e, he, ?_⟩)
        rw [show halves e.1 = halves (baseInput (digestOfBytes e.1)) from congrArg _ hcond.2]
        exact mem_halves_baseInput _
      · cases hb
  · simp at h

/-- After one more clean query, no group it touches starts from its answer. -/
theorem CleanStep.cv_ne_of_mem_touched (hs : CleanStep roots l t u) {G : Group}
    (h : G ∈ R.touched l t) : G.cv ≠ u := by
  rintro rfl
  rcases R.cv_mem_of_mem_touched (roots := roots) h with h | h
  · exact hs.notHalf h
  · exact hs.notInPlay h

/-- **A flip after one more clean query** is a group open before it or opened by it, which flips
after it, at probability `1`. -/
theorem flipAt_append (hl : CleanLog roots l) (hs : CleanStep roots l t u) (hno : ¬ R.FlipAt l)
    (h : R.FlipAt (l ++ [⟨t, u⟩])) :
    ∃ G ∈ R.openGroups l ∪ R.openedBy l t,
      R.Flips (l ++ [⟨t, u⟩]) G ∧ R.π (l ++ [⟨t, u⟩]) G = 1 := by
  obtain ⟨G, hG⟩ := h
  obtain ⟨hslot', -, hask'⟩ := R.complete_of_flips hG
  have hcv : G.cv ≠ u := hs.cv_ne_of_asked hask'
  have hslot : (R.groupSlot l G).isSome = true := by
    rwa [R.groupSlot_append (hl.append hs) hcv] at hslot'
  refine ⟨G, ?_, hG, R.π_eq_one_of_flips hG⟩
  rw [Finset.mem_union, mem_openGroups_iff, mem_openedBy_iff]
  by_cases ht : G ∈ R.touched l t
  · cases ha : G.asked l (R.size l G) with
    | false => exact .inr ⟨ht, rfl⟩
    | true =>
      refine .inl ?_
      cases hc : G.complete l (R.size l G) with
      | false => simp [isOpen, hslot, ha, hc]
      | true =>
        exact absurd ⟨G, (R.status_of_unmoved
          (R.unmoved_of_complete (hl.append hs) hcv hslot hc)).2.2.2.2.1.mp hG⟩ hno
  · exact absurd ⟨G, (R.status_of_unmoved (R.unmoved hl hs hcv ht)).2.2.2.2.1.mp hG⟩ hno

end SlotReader

end
end LeanerVM.Protocol
