import LeanerVM.Protocol.ChainGroups

/-!
# The groups of a chain's challenges: tests

A toy reader of two rounds, a nonce message and then a challenge of one squeeze that a proof of
work precedes: a history reads its nonce step and its squeeze, at one announcement, from any
starts. The reader's facts hold of it, so `SlotReader` has an inhabitant.

On logs of hash queries answered by hand-picked digests (the answers of a random oracle, so no
hashing is needed), from the seed:

* the grinding base opens nothing; the grinding check of a nonce touches and opens that nonce's
  group, which the log then shows open, and leaves the group of another nonce unopened; the
  absorption of the nonce and the squeeze from its answer close it;
* asked in the other order, the absorption first, the group opens at the absorption;
* the challenge's squeeze is the next query of the group once the nonce is absorbed, and closes
  it on a bad challenge: the group flips, at probability `1`, and did not before the squeeze;
* the flip is on the chain of the statement the seed opens (`FlipAtFor`), and a flip on a
  statement's chain is a flip; with a second start opening a second statement, the log has no
  flip on that statement's chain (`not_flipAtFor_true`): the start is not in play;
* with the challenge unmarked, the nonce's group fixes nothing, and the plain group at the
  nonce's answer fixes it, opened and closed by its one squeeze;
* a log whose base is answered by the seed has a hit, and a check answered by its own base is a
  query answered by one of its halves, which `CleanStep` excludes;
* the roots a history absorbs are its consecutive pairs of observes.
-/

namespace LeanerVMTests.Protocol.ChainGroups

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Protocol LeanerVM.Protocol.Blake2sHash
open OracleComp OracleSpec ProtocolSpec
open LeanerVM.Protocol.MerkleTree (logAnswer)

/-! ## A toy reader -/

/-- A nonce message, then a challenge digest. -/
def toySpec : ProtocolSpec 2 := ⟨![.P_to_V, .V_to_P], ![E, Digest]⟩

/-- A reading with its state kept only for a squeeze, the one reading whose state a slot reads. -/
def readingView : Block × Digest → Block × Option Digest
  | (.squeeze, d) => (.squeeze, some d)
  | (b, _) => (b, none)

/-- The toy's prefixes, read off the viewed readings: nothing, the nonce, the nonce and the
challenge. -/
def toyDecodeView : List (Block × Option Digest) → Option (Σ k : Fin 3, toySpec.Transcript k)
  | [] => some ⟨0, fun i ↦ i.elim0⟩
  | [(.nonce n, _)] => some ⟨1, fun i ↦ match i with | ⟨0, _⟩ => (n : E)⟩
  | [(.nonce n, _), (.squeeze, some d)] =>
    some ⟨2, fun i ↦ match i with | ⟨0, _⟩ => (n : E) | ⟨1, _⟩ => (d : Digest)⟩
  | _ => none

/-- The toy's decoder. -/
def toyDecode (hs : List (Block × Digest)) : Option (Σ k : Fin 3, toySpec.Transcript k) :=
  toyDecodeView (hs.map readingView)

/-- The toy's one challenge index. -/
def chal : toySpec.ChallengeIdx := ⟨⟨1, by decide⟩, rfl⟩

theorem eq_chal : ∀ i : toySpec.ChallengeIdx, i = chal
  | ⟨⟨0, _⟩, h⟩ => absurd h (by simp [toySpec])
  | ⟨⟨1, _⟩, _⟩ => rfl

/-- The challenge is a digest. -/
instance toySampleable (i : toySpec.ChallengeIdx) : SampleableType (toySpec.Challenge i) :=
  match i with
  | ⟨⟨0, _⟩, h⟩ => absurd h (by simp [toySpec])
  | ⟨⟨1, _⟩, _⟩ => inferInstanceAs (SampleableType Digest)

/-- A digest challenge read off one squeeze. -/
def oneSqueeze : SqueezeSlot Digest :=
  ⟨1, fun ds ↦ ds 0, SampleableType.prEvent_uniformSample_equiv (Equiv.funUnique (Fin 1) Digest)⟩

/-- The challenge is its one squeeze's digest. -/
def toySlot : (i : toySpec.ChallengeIdx) → @SqueezeSlot (toySpec.Challenge i) (toySampleable i)
  | ⟨⟨0, _⟩, h⟩ => absurd h (by simp [toySpec])
  | ⟨⟨1, _⟩, _⟩ => oneSqueeze

/-- The bad challenges: those with a low zero bit. -/
def toyBad (i : toySpec.ChallengeIdx) : Set (toySpec.Challenge i) :=
  match i with
  | ⟨⟨0, _⟩, h⟩ => absurd h (by simp [toySpec])
  | ⟨⟨1, _⟩, _⟩ => {c : Digest | FsState.lowBitsZero c 1 = true}

/-- A reading other than a squeeze does not show its state. -/
theorem readingView_indep {b : Block} (d d' : Digest) (hb : b ≠ .squeeze) :
    readingView (b, d) = readingView (b, d') := by
  cases b
  exacts [rfl, absurd rfl hb, rfl]

/-- The toy reads `hs` to the challenge exactly when `hs` is one nonce step. -/
theorem toyDecode_one {hs : List (Block × Digest)} {tr : toySpec.Transcript 1}
    (h : toyDecode hs = some ⟨1, tr⟩) : ∃ n d, hs = [(.nonce n, d)] := by
  rcases hs with _ | ⟨⟨b, d⟩, _ | ⟨⟨b', d'⟩, rest⟩⟩
  · simp [toyDecode, toyDecodeView] at h
  · cases b <;> simp [toyDecode, toyDecodeView, readingView] at h
    exact ⟨_, d, rfl⟩
  · cases b <;> cases b' <;> (try cases rest) <;>
      simp [toyDecode, toyDecodeView, readingView] at h

/-- The toy reader, its histories starting where `S` says. -/
def toyReaderOn (S : ChainStarts) : SlotReader where
  toChainStarts := S
  powBits := 1
  Ann := Unit
  announcementOf _ _ := some ()
  n _ := 2
  spec _ := toySpec
  sampleable _ i := toySampleable i
  Words _ := Unit
  wordsAt _ _ _ := ()
  decodePrefix _ _ hs := toyDecode hs
  slot _ i := toySlot i
  mark _ _ := true
  Bad _ i _ := toyBad i
  wordsAt_congr _ _ _ _ _ := rfl
  squeezeSlot_read := by
    intro _ _ hs i tr h ds rest k tr' h'
    obtain rfl := eq_chal i
    obtain ⟨n, d, rfl⟩ := toyDecode_one h
    have hds : List.ofFn ds = [ds ⟨0, by decide⟩] := List.ofFn_succ ..
    rcases rest with _ | ⟨r, rest⟩
    · simp only [toyDecode, toyDecodeView, squeezeBlocks, hds, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, List.append_nil, readingView, Option.some.injEq] at h h'
      obtain ⟨rfl, htr'⟩ := Sigma.mk.inj h'
      obtain ⟨-, htr⟩ := Sigma.mk.inj h
      subst htr'
      subst htr
      refine ⟨le_rfl, funext fun i ↦ ?_⟩
      rcases i with ⟨_ | _ | _, hi⟩
      · rfl
      · rfl
      · omega
    · rcases r with ⟨b, e⟩
      cases b <;> simp [toyDecode, toyDecodeView, squeezeBlocks, hds, readingView] at h'
  decodePrefix_digest_indep _ _ _ _ d d' _ hb := by simp [toyDecode, readingView_indep d d' hb]
  mark_afterNonce := by
    intro _ _ hs i tr h _
    obtain rfl := eq_chal i
    obtain ⟨n, d, rfl⟩ := toyDecode_one h
    exact ⟨[], n, d, rfl⟩
  slot_pos _ i := by
    obtain rfl := eq_chal i
    decide

/-- The toy reader from one seed. -/
abbrev toyReader (seed : Digest) : SlotReader := toyReaderOn (.startAt seed)

/-- The toy reader with its challenge unmarked: no proof of work precedes it. -/
def plainReader (seed : Digest) : SlotReader :=
  { toyReader seed with
    mark := fun _ _ ↦ false
    mark_afterNonce := fun _ _ _ _ _ _ h ↦ absurd h Bool.false_ne_true }

/-! ## A proof of work's group -/

/-- A digest with first word `k`. -/
def d (k : UInt32) : Digest := #v[k, 0, 0, 0, 0, 0, 0, 0]

/-- The chain's seed. -/
def s₀ : Digest := d 100

/-- The toy reader from the seed. -/
abbrev R : SlotReader := toyReader s₀

/-- Two nonces. -/
def n₁ : E := FsState.nonceOf 7

/-- Two nonces. -/
def n₂ : E := FsState.nonceOf 8

/-- The groups of the two nonces from the seed. -/
def G₁ : Group := ⟨s₀, some n₁⟩

/-- The groups of the two nonces from the seed. -/
def G₂ : Group := ⟨s₀, some n₂⟩

/-- The base, answered by `d 1`. -/
def log₀ : hashSpec.QueryLog := [⟨baseInput s₀, d 1⟩]

/-- Then the check of `n₁` against the base, answered by `d 2`, with a low zero bit. -/
def log₁ : hashSpec.QueryLog := log₀ ++ [⟨checkInput (d 1) n₁, d 2⟩]

/-- Then the absorption of `n₁`, answered by `d 3`. -/
def log₂ : hashSpec.QueryLog := log₁ ++ [⟨absorbInput s₀ n₁, d 3⟩]

/-- Then the squeeze from `d 3`, answered by `d 4`. -/
def log₃ : hashSpec.QueryLog := log₂ ++ [⟨squeezeInput (d 3), d 4⟩]

-- Each nonce's group fixes the challenge, one squeeze; the base opens nothing.
#guard (R.groupSlot log₀ G₁).isSome && (R.groupSlot log₀ G₂).isSome
#guard R.size log₀ G₁ = 1
#guard R.touched [] (baseInput s₀) = []
#guard !R.isOpen log₀ G₁ && R.openGroups log₀ = ∅

-- The check of `n₁` touches and opens `G₁`, not `G₂`; the log then shows `G₁` open.
#guard G₁ ∈ R.touched log₀ (checkInput (d 1) n₁)
#guard G₁ ∈ R.openedBy log₀ (checkInput (d 1) n₁)
#guard G₂ ∉ R.touched log₀ (checkInput (d 1) n₁)
#guard R.isOpen log₁ G₁ && !R.isOpen log₁ G₂
#guard R.openGroups log₁ = {G₁}
#guard G₁.check? log₁ = some (d 2)

-- The absorption keeps it open, and the squeeze from its answer is the group's next query,
-- which it touches without opening it.
#guard R.isOpen log₂ G₁
#guard R.awaits log₂ G₁ (d 3)
#guard G₁ ∈ R.touched log₂ (squeezeInput (d 3))
#guard G₁ ∉ R.openedBy log₂ (squeezeInput (d 3))

-- The squeeze closes it: its challenge is `d 4`, bad, and its proof of work passes, so it flips.
#guard !R.isOpen log₃ G₁ && R.isClosed log₃ G₁
#guard G₁.run log₃ 1 = [d 4]
#guard FsState.lowBitsZero (d 2) 1 && FsState.lowBitsZero (d 4) 1
#guard R.openGroups log₃ = ∅

-- Asked in the other order, the absorption first, the group opens at the absorption.
#guard G₁ ∈ R.touched log₀ (absorbInput s₀ n₁)
#guard R.isOpen (log₀ ++ [⟨absorbInput s₀ n₁, d 3⟩]) G₁

-- The check's own base, read as a state, starts no history: its absorption reading fixes
-- nothing.
#guard R.groupSlot log₀ ⟨d 1, some n₁⟩ = none

/-! ## Two statements -/

/-- Another statement's seed. -/
def s₁ : Digest := d 50

/-- Two starts: the seed opens the statement `false`, and `s₁` the statement `true`. -/
def twoStarts : ChainStarts where
  Stmt := Bool
  stmtAt _ x := if x = s₀ then some false else if x = s₁ then some true else none
  stmtAt_append _ _ _ _ _ _ := rfl
  stmtAt_dedupKeys _ _ _ := rfl

/-- The toy reader from the two starts. -/
abbrev R₂ : SlotReader := toyReaderOn twoStarts

/-- The group of `n₁` flips at the two starts as at one. -/
theorem flips₃' : R₂.Flips log₃ G₁ := by
  unfold SlotReader.Flips
  rw [show R₂.groupSlot log₃ G₁ = some ⟨(), chal, fun i ↦ match i with | ⟨0, _⟩ => n₁⟩ from rfl]
  refine ⟨rfl, fun n hn ↦ ?_, rfl⟩
  obtain rfl : n = n₁ := (Option.some.inj hn).symm
  exact ⟨d 1, d 2, rfl, rfl, rfl⟩

-- Its history starts at the seed: a flip on the chain of the statement `false`.
example : R₂.FlipAtFor log₃ false := ⟨G₁, flips₃', (s₀, []), rfl, rfl⟩

/-- **No flip on the chain of the other statement**, though the log has a flip: a flipping group
has a logged query, so its history starts in play, and `s₁` is not in play. -/
theorem not_flipAtFor_true : ¬ R₂.FlipAtFor log₃ true := by
  rintro ⟨G, hG, ⟨σ, hs⟩, hch, hst⟩
  have hin : σ ∈ inPlay [] log₃ := by
    rcases (start_of_chainHistory hch []).2 with h | h
    · obtain ⟨q, x, hq, hcv⟩ := Group.exists_query_of_asked (R₂.complete_of_flips hG).2.2
      exact h ▸ mem_inPlay_of_logAnswer hq hcv
    · exact h
  change (if σ = s₀ then some false else if σ = s₁ then some true else none) = some true at hst
  split_ifs at hst with h₀ h₁
  · cases hst
  · subst h₁
    exact absurd hin (by decide)

/-! ## A plain group -/

/-- The toy reader with its challenge unmarked, from the seed. -/
abbrev P : SlotReader := plainReader s₀

-- Unmarked, the nonce's group fixes nothing; the plain group at the nonce's answer fixes the
-- challenge once the absorption is logged, and its one squeeze opens and closes it.
#guard (P.groupSlot log₂ G₁).isNone
#guard (P.groupSlot log₁ ⟨d 3, none⟩).isNone
#guard (P.groupSlot log₂ ⟨d 3, none⟩).isSome
#guard ⟨d 3, none⟩ ∈ P.openedBy log₂ (squeezeInput (d 3))
#guard P.isClosed log₃ ⟨d 3, none⟩

/-! ## Mutations -/

-- A base answered by the seed is a hit on the digests in play.
#guard decide (QueryLog.HasHit (inPlay [s₀]) [⟨baseInput s₀, s₀⟩])
-- A squeeze answered by its own state answers a half of it, which `CleanStep` excludes.
#guard d 3 ∈ halves (squeezeInput (d 3))
-- A check without a low zero bit: the group closes, but its proof of work fails.
#guard !FsState.lowBitsZero (d 5) 1

/-! ## The roots a history absorbs -/

/-- A root. -/
def root : Digest := d 77

#guard historyRoots [(.observe (digestScalars root).1, d 1), (.observe (digestScalars root).2, d 2),
  (.squeeze, d 3)] = [root]
#guard historyRoots [(.observe (digestScalars root).1, d 1), (.squeeze, d 3),
  (.observe (digestScalars root).2, d 2)] = []

/-- The group's challenge in the full log: the toy's one challenge, after the nonce. -/
theorem groupSlot₃ :
    R.groupSlot log₃ G₁ = some ⟨(), chal, fun i ↦ match i with | ⟨0, _⟩ => n₁⟩ := by
  rfl

/-- **The group flips** on the full log: its squeeze is logged, its proof of work passes, and its
challenge is bad. -/
theorem flips₃ : R.Flips log₃ G₁ := by
  unfold SlotReader.Flips
  rw [groupSlot₃]
  refine ⟨rfl, fun n hn ↦ ?_, rfl⟩
  obtain rfl : n = n₁ := (Option.some.inj hn).symm
  exact ⟨d 1, d 2, rfl, rfl, rfl⟩

-- So the log has a flip, at probability `1`.
example : R.FlipAt log₃ := ⟨G₁, flips₃⟩
example : R.π log₃ G₁ = 1 := R.π_eq_one_of_flips flips₃

-- The group's history is the empty one from the seed, which opens the one statement: the flip is
-- on that statement's chain. A flip on a statement's chain is a flip.
example : R.FlipAtFor log₃ () := ⟨G₁, flips₃, (s₀, []), rfl, rfl⟩
example (st : Unit) (g : Run) (h : R.FlipFor st g) : R.Flip g := R.flip_of_flipFor h

-- Before the squeeze the group is not closed, so it does not flip.
example : ¬ R.Flips log₂ G₁ := fun h ↦ by
  have := (R.complete_of_flips h).2.1
  revert this
  decide

/-! ## Interleaved groups and readings of one query -/

-- A Merkle node whose right child is the squeeze block is the squeeze from its left child, and
-- with tag `4` a nonce step: a node can be a group's query.
/-- A right child equal to the squeeze block. -/
def sqBlock : Digest := #v[0, 0, 0, 0, 0, 0, 2, 0]

/-- A right child equal to the nonce block of the nonce `0`. -/
def nonceBlock0 : Digest := #v[0, 0, 0, 0, 0, 0, 4, 0]

#guard decide (Block.parse? (nodeBytes (d 5) sqBlock) = some (d 5, .squeeze))
#guard decide (nodeBytes (d 5) sqBlock = squeezeInput (d 5))
#guard decide (Block.parse? (nodeBytes (d 5) nonceBlock0) = some (d 5, .nonce 0))

-- A grinding check is the nonce step from the base: one query, two readings.
#guard checkInput (d 1) n₁ = absorbInput (d 1) n₁

-- A squeeze answered by its own state is neither a hit nor a collision; `CleanStep` excludes it.
/-- A squeeze answered by its own state. -/
def selfLog : hashSpec.QueryLog := [⟨squeezeInput (d 3), d 3⟩]

#guard !decide (QueryLog.HasHit (inPlay [s₀]) selfLog)
#guard !decide (QueryLog.HasCollision selfLog)

-- With the challenge marked, the plain group at the nonce's answer fixes nothing.
#guard (R.groupSlot log₂ ⟨d 3, none⟩).isNone
-- A squeeze from a state with no history touches and opens nothing.
#guard R.touched log₀ (squeezeInput (d 42)) = []
#guard R.openedBy log₀ (squeezeInput (d 42)) = ∅
-- A squeeze straight from the seed, skipping the nonce: the plain group at the seed fixes
-- nothing.
#guard (R.groupSlot log₀ ⟨s₀, none⟩).isNone
#guard R.openedBy log₀ (squeezeInput s₀) = ∅

/-- Both nonces checked and absorbed, interleaved. -/
def logI : hashSpec.QueryLog :=
  log₀ ++ [⟨checkInput (d 1) n₁, d 2⟩, ⟨checkInput (d 1) n₂, d 6⟩, ⟨absorbInput s₀ n₂, d 7⟩,
    ⟨absorbInput s₀ n₁, d 3⟩]

-- Both groups are open; the squeeze of one touches it alone, closes it, and leaves the other
-- open.
#guard R.openGroups logI = {G₁, G₂}
#guard G₁ ∈ R.touched logI (squeezeInput (d 3)) && G₂ ∉ R.touched logI (squeezeInput (d 3))
#guard R.isOpen (logI ++ [⟨squeezeInput (d 3), d 4⟩]) G₂
#guard R.isClosed (logI ++ [⟨squeezeInput (d 3), d 4⟩]) G₁

/-! ## Consecutive challenges -/

/-- A nonce message, then two challenge digests in a row. -/
def pairSpec : ProtocolSpec 3 := ⟨![.P_to_V, .V_to_P, .V_to_P], ![E, Digest, Digest]⟩

/-- The prefixes of the two-challenge protocol, read off the viewed readings. -/
def pairDecodeView : List (Block × Option Digest) → Option (Σ k : Fin 4, pairSpec.Transcript k)
  | [] => some ⟨0, fun i ↦ i.elim0⟩
  | [(.nonce n, _)] => some ⟨1, fun i ↦ match i with | ⟨0, _⟩ => (n : E)⟩
  | [(.nonce n, _), (.squeeze, some d)] =>
    some ⟨2, fun i ↦ match i with | ⟨0, _⟩ => (n : E) | ⟨1, _⟩ => (d : Digest)⟩
  | [(.nonce n, _), (.squeeze, some d), (.squeeze, some d')] =>
    some ⟨3, fun i ↦ match i with
      | ⟨0, _⟩ => (n : E) | ⟨1, _⟩ => (d : Digest) | ⟨2, _⟩ => (d' : Digest)⟩
  | _ => none

/-- The two-challenge decoder. -/
def pairDecode (hs : List (Block × Digest)) : Option (Σ k : Fin 4, pairSpec.Transcript k) :=
  pairDecodeView (hs.map readingView)

/-- Both challenges are digests. -/
instance pairSampleable (i : pairSpec.ChallengeIdx) : SampleableType (pairSpec.Challenge i) :=
  match i with
  | ⟨⟨0, _⟩, h⟩ => absurd h (by simp [pairSpec])
  | ⟨⟨1, _⟩, _⟩ => inferInstanceAs (SampleableType Digest)
  | ⟨⟨2, _⟩, _⟩ => inferInstanceAs (SampleableType Digest)

/-- Each challenge is its one squeeze's digest. -/
def pairSlot : (i : pairSpec.ChallengeIdx) →
    @SqueezeSlot (pairSpec.Challenge i) (pairSampleable i)
  | ⟨⟨0, _⟩, h⟩ => absurd h (by simp [pairSpec])
  | ⟨⟨1, _⟩, _⟩ => oneSqueeze
  | ⟨⟨2, _⟩, _⟩ => oneSqueeze

/-- The two challenge indices. -/
def chal₁ : pairSpec.ChallengeIdx := ⟨⟨1, by decide⟩, rfl⟩

/-- The two challenge indices. -/
def chal₂ : pairSpec.ChallengeIdx := ⟨⟨2, by decide⟩, rfl⟩

theorem pair_cases : ∀ i : pairSpec.ChallengeIdx, i = chal₁ ∨ i = chal₂
  | ⟨⟨0, _⟩, h⟩ => absurd h (by simp [pairSpec])
  | ⟨⟨1, _⟩, _⟩ => .inl rfl
  | ⟨⟨2, _⟩, _⟩ => .inr rfl

/-- No challenge is bad. -/
def pairBad (i : pairSpec.ChallengeIdx) : Set (pairSpec.Challenge i) := ∅

/-- The prefixes ending before a challenge: the nonce step, then one squeeze more. -/
theorem pairDecode_start {hs : List (Block × Digest)} {k : Fin 4} {tr : pairSpec.Transcript k}
    (h : pairDecode hs = some ⟨k, tr⟩) (hk : k = 1 ∨ k = 2) :
    (k = 1 ∧ ∃ n d, hs = [(.nonce n, d)]) ∨
      (k = 2 ∧ ∃ n d e, hs = [(.nonce n, d), (.squeeze, e)]) := by
  rcases hs with _ | ⟨⟨b, d⟩, _ | ⟨⟨b', d'⟩, _ | ⟨⟨b'', d''⟩, rest⟩⟩⟩
  · simp only [pairDecode, pairDecodeView, List.map_nil, Option.some.injEq] at h
    obtain ⟨rfl, -⟩ := Sigma.mk.inj h
    simp at hk
  · cases b <;> simp [pairDecode, pairDecodeView, readingView] at h
    obtain ⟨rfl, -⟩ := h
    exact .inl ⟨rfl, _, d, rfl⟩
  · cases b <;> cases b' <;> simp [pairDecode, pairDecodeView, readingView] at h
    obtain ⟨rfl, -⟩ := h
    exact .inr ⟨rfl, _, d, d', rfl⟩
  · cases b <;> cases b' <;> cases b'' <;> (try cases rest) <;>
      simp [pairDecode, pairDecodeView, readingView] at h
    obtain ⟨rfl, -⟩ := h
    simp at hk

/-- The two-challenge reader, both challenges unmarked. -/
def pairReader (seed : Digest) : SlotReader where
  toChainStarts := .startAt seed
  powBits := 1
  Ann := Unit
  announcementOf _ _ := some ()
  n _ := 3
  spec _ := pairSpec
  sampleable _ i := pairSampleable i
  Words _ := Unit
  wordsAt _ _ _ := ()
  decodePrefix _ _ hs := pairDecode hs
  slot _ i := pairSlot i
  mark _ _ := false
  Bad _ i _ := pairBad i
  wordsAt_congr _ _ _ _ _ := rfl
  squeezeSlot_read := by
    intro _ _ hs i tr h ds rest k tr' h'
    rcases pair_cases i with rfl | rfl
    · obtain (⟨-, n, d, rfl⟩ | ⟨h2, -⟩) := pairDecode_start h (.inl rfl)
      · have hds : List.ofFn ds = [ds ⟨0, by decide⟩] := List.ofFn_succ ..
        rcases rest with _ | ⟨⟨b, e⟩, _ | ⟨r, rest⟩⟩
        · simp only [pairDecode, pairDecodeView, squeezeBlocks, hds, List.map_cons,
            List.map_nil, List.cons_append, List.nil_append, List.append_nil, readingView,
            Option.some.injEq] at h h'
          obtain ⟨rfl, htr'⟩ := Sigma.mk.inj h'
          obtain ⟨-, htr⟩ := Sigma.mk.inj h
          subst htr' htr
          refine ⟨le_rfl, funext fun i ↦ ?_⟩
          rcases i with ⟨_ | _ | _, hi⟩
          · rfl
          · rfl
          · simp [chal₁] at hi
        · cases b <;> simp [pairDecode, pairDecodeView, squeezeBlocks, hds, readingView] at h'
          obtain ⟨rfl, htr'⟩ := h'
          simp only [pairDecode, pairDecodeView, List.map_cons, List.map_nil, readingView,
            Option.some.injEq] at h
          obtain ⟨-, htr⟩ := Sigma.mk.inj h
          subst htr' htr
          refine ⟨by decide, funext fun i ↦ ?_⟩
          rcases i with ⟨_ | _ | _, hi⟩
          · rfl
          · rfl
          · simp [chal₁] at hi
        · rcases r with ⟨b', e'⟩
          cases b <;> cases b' <;>
            simp [pairDecode, pairDecodeView, squeezeBlocks, hds, readingView] at h'
      · simp [chal₁] at h2
    · obtain (⟨h1, -⟩ | ⟨-, n, d, e, rfl⟩) := pairDecode_start h (.inr rfl)
      · simp [chal₂] at h1
      · have hds : List.ofFn ds = [ds ⟨0, by decide⟩] := List.ofFn_succ ..
        rcases rest with _ | ⟨⟨b, e'⟩, rest⟩
        · simp only [pairDecode, pairDecodeView, squeezeBlocks, hds, List.map_cons,
            List.map_nil, List.cons_append, List.nil_append, List.append_nil, readingView,
            Option.some.injEq] at h h'
          obtain ⟨rfl, htr'⟩ := Sigma.mk.inj h'
          obtain ⟨-, htr⟩ := Sigma.mk.inj h
          subst htr' htr
          refine ⟨le_rfl, funext fun i ↦ ?_⟩
          rcases i with ⟨_ | _ | _ | _, hi⟩
          · rfl
          · rfl
          · rfl
          · omega
        · cases b <;> simp [pairDecode, pairDecodeView, squeezeBlocks, hds, readingView] at h'
  decodePrefix_digest_indep _ _ _ _ d d' _ hb := by simp [pairDecode, readingView_indep d d' hb]
  mark_afterNonce _ _ _ _ _ _ h := absurd h Bool.false_ne_true
  slot_pos _ i := by
    rcases pair_cases i with rfl | rfl <;> decide

/-- The two-challenge reader from the seed. -/
abbrev P₂ : SlotReader := pairReader s₀

/-- The plain groups of the two challenges, at the nonce's answer and at the first squeeze's. -/
def A : Group := ⟨d 3, none⟩

/-- The plain groups of the two challenges, at the nonce's answer and at the first squeeze's. -/
def B : Group := ⟨d 4, none⟩

/-- The nonce step, then the first challenge's squeeze. -/
def logC : hashSpec.QueryLog := [⟨absorbInput s₀ n₁, d 3⟩, ⟨squeezeInput (d 3), d 4⟩]

-- The two challenges share one squeeze chain: the squeeze from `d 4` ends the first group's run
-- and starts the second's. The first is closed and does not await it; the second does, and the
-- squeeze touches and opens the second alone.
#guard (P₂.groupSlot logC A).isSome && (P₂.groupSlot logC B).isSome
#guard P₂.isClosed logC A
#guard !P₂.awaits logC A (d 4) && P₂.awaits logC B (d 4)
#guard P₂.touched logC (squeezeInput (d 4)) = [B]
#guard P₂.openedBy logC (squeezeInput (d 4)) = {B}
#guard P₂.isClosed (logC ++ [⟨squeezeInput (d 4), d 6⟩]) B
-- Before the first squeeze, the second group fixes no challenge: its state has no history.
#guard (P₂.groupSlot (logC.take 1) B).isNone

end LeanerVMTests.Protocol.ChainGroups
