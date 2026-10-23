import LeanerVM.Protocol.RandomOracle
import LeanerVM.Parameters.Whir

/-!
# Hash oracle tests

The two runs of the hash oracle: BLAKE2s answers a query by its digest and a chain step by the
deployed step; the random oracle answers a fresh query by a uniform digest and a repeated query
from its cache. The distributions on a uniform digest: a challenge is any given element with
probability `2^-192`, a 17-bit grinding check passes with probability `2^-17`. The challenges of
two fresh digests are a given pair with probability `2^-384`; query positions read the challenge
bits low first, nine positions of `20` bits to a challenge, a position across two limbs as the
Rust reads it; ten positions from two fresh squeezes are a given tuple with probability
`2^-200`, while from one squeeze the tenth is always `0`.

Then the chain read off a log: the log of an honest chain (two observes, a squeeze, the grinding
base, a nonce and a squeeze, every query answered by BLAKE2s) gives back its blocks and states,
also with a Merkle node that parses as a step beside it, and already before the last squeeze and
before the grinding base; the byte decoders invert the encoders, and the step parser rejects the
grinding base, a squeeze with an element and a 65-byte input. Then one mutation per hypothesis:
a collision makes a step ambiguous, an answer equal to the seed cuts the history short, and a
state produced after the query that uses it leaves the history out of the log before that query.
A root absorbed as two observes is in play, so a fresh node answered by it is a hit.

Deduplication: the honest log asked twice deduplicates to the honest log, with the same history
and digests in play; a query asked again with another answer is inconsistent, and deduplication
keeps the first answer; a hit survives deduplication. One more query answered by a digest not in
play leaves the last state's history as it was; the late log, whose second answer is in play,
makes a history appear.
-/

namespace LeanerVMTests.Protocol.RandomOracle

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Protocol LeanerVM.Protocol.Blake2sHash
open OracleComp OracleSpec
open scoped ENNReal

/-! ## The two runs of the oracle -/

-- BLAKE2s answers a query by its digest.
example (t : List UInt8) : runBlake2s (hashQuery t) = pure (blake2sBytes t) := by
  simp [runBlake2s, hashQuery]

-- A chain step run on BLAKE2s is the deployed step.
example (s : FsState) (x : E) :
    runBlake2s (s.observe hashQuery x) = pure (Deployed.observe s x) := by
  simp [runBlake2s, hashQuery, FsState.observe, Deployed.observe, Id.run]
  rfl

/-- The random oracle answers a fresh query by a uniform digest, which it caches. -/
theorem runRandom_hashQuery (t : List UInt8) :
    runRandom (hashQuery t) =
      (fun u ↦ (u, (∅ : hashSpec.QueryCache).cacheQuery t u)) <$> ($ᵗ Digest) := by
  simp [runRandom, hashQuery, map_eq_bind_pure_comp]

-- A fresh query's answer is uniform on `Digest`.
example (t : List UInt8) (p : Digest → Prop) :
    Pr{let z ← runRandom (hashQuery t)}[p z.1] = Pr{let u ← $ᵗ Digest}[p u] := by
  rw [runRandom_hashQuery, prEvent_map]

example (t : List UInt8) (d : Digest) :
    Pr{let z ← runRandom (hashQuery t)}[z.1 = d] = (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  rw [runRandom_hashQuery, prEvent_map, SampleableType.prEvent_uniformSample_eq_singleton,
    card_digest, Nat.cast_pow, Nat.cast_ofNat]

-- A repeated query is answered from the cache: its two answers agree.
example (t : List UInt8) :
    Pr{let z ← runRandom (do let a ← hashQuery t; let b ← hashQuery t; return (a, b))}[
      z.1.1 = z.1.2] = 1 := by
  have h : runRandom (do let a ← hashQuery t; let b ← hashQuery t; return (a, b)) =
      (fun u ↦ ((u, u), (∅ : hashSpec.QueryCache).cacheQuery t u)) <$> ($ᵗ Digest) := by
    simp [runRandom, hashQuery, map_eq_bind_pure_comp]
  rw [h, prEvent_map]
  exact (SampleableType.prEvent_uniformSample_eq_one_iff _).mpr fun _ ↦ rfl

/-! ## Challenges and grinding checks of a uniform digest -/

example : Pr{let d ← $ᵗ Digest}[FsState.challengeOf d = 0] = (2 ^ 192 : ℝ≥0∞)⁻¹ := by
  rw [prEvent_challengeOf_eq, card_E]
  norm_num

example : Pr{let d ← $ᵗ Digest}[FsState.lowBitsZero d 17 = true] = (2 ^ 17 : ℝ≥0∞)⁻¹ :=
  prEvent_lowBitsZero (by norm_num)

/-! ## Tuples of challenges and query positions -/

-- The challenges of two fresh digests are a given pair with probability `2^-384`.
example :
    Pr{let d ← $ᵗ (Fin 2 → Digest)}[(fun i ↦ FsState.challengeOf (d i)) = ![0, 1]] =
      (2 ^ 384 : ℝ≥0∞)⁻¹ := by
  refine (prEvent_challengeOf_tuple 2 (· = ![0, 1])).trans ?_
  rw [SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_fun, card_E,
    Fintype.card_fin, ← pow_mul, Nat.cast_pow, Nat.cast_ofNat]

-- Positions of `4` bits, low bits first: the nibbles of the low limb.
example : challengePositions 4 4 [E.ofLimbs (K.ofBits 0x4321) 0 0] = ![1, 2, 3, 4] := by
  decide

-- Positions of `20` bits, nine to a challenge: position `3` is bits `60..79`, the top nibble of
-- limb `0` and the low bits of limb `1`, as the Rust's two-limb read
-- (`limbs[0] >> 60 | limbs[1] << 4`, masked to `20` bits) gives; position `9` is the next
-- challenge's low bits.
example :
    challengePositions 20 10 [E.ofLimbs (K.ofBits 0xF000000000000000) (K.ofBits 0xF) 0,
      E.ofLimbs (K.ofBits 0xABCDE) 0 0] 3 = 0xFF ∧
    challengePositions 20 10 [E.ofLimbs (K.ofBits 0xF000000000000000) (K.ofBits 0xF) 0,
      E.ofLimbs (K.ofBits 0xABCDE) 0 0] 9 = 0xABCDE := by
  decide

-- Every deployed level's positions have `1 ≤ b < 64` bits, `b = κ_i + R_i` (`blockLogs`), where
-- `challengePositions` reads the Rust's chunks: over the whole window, every ladder.
#guard (List.range (Whir.maxLogStack + 1)).all fun μ ↦
  (List.range (Whir.maxLogInvRate + 1)).all fun r ↦
    match Whir.ladder μ r with
    | some ls => (Whir.blockLogs μ ls).all fun b ↦ 1 ≤ b && b < 64
    | none => !decide (Whir.Admissible μ r)
-- The widest, at `(μ, R) = (28, 4)`: `22 + 4`, then per level `κ` down by the fold `4` and `R`
-- up by `3` (the previous fold less the domain reduction).
#guard (Whir.ladder Whir.maxLogStack Whir.maxLogInvRate).map (Whir.blockLogs Whir.maxLogStack) =
  some [26, 25, 24, 23, 22, 21]

-- Ten positions of `20` bits from two fresh squeezes are a given tuple with probability
-- `2^-200`.
example :
    Pr{let d ← $ᵗ (Fin 2 → Digest)}[
      challengePositions 20 10 (List.ofFn fun i ↦ FsState.challengeOf (d i)) = fun _ ↦ 0] =
      (2 ^ 200 : ℝ≥0∞)⁻¹ := by
  refine (prEvent_positions_uniform (by norm_num) (· = fun _ ↦ 0)).trans ?_
  rw [SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin]
  norm_num

-- One squeeze is not enough for ten positions of `20` bits: the tenth reads past the one
-- challenge and is `0` on every digest, where a uniform position is `0` with probability
-- `2^-20`.
example :
    Pr{let d ← $ᵗ (Fin 1 → Digest)}[
      challengePositions 20 10 (List.ofFn fun i ↦ FsState.challengeOf (d i)) 9 = 0] = 1 :=
  (SampleableType.prEvent_uniformSample_eq_one_iff _).mpr fun _ ↦ Fin.ext (by
    simp only [challengePositions]
    rw [List.getD_eq_default _ _ (by rw [List.length_ofFn]; decide)]
    decide)

/-! ## Bytes -/

/-- A digest with distinct words. -/
def sample : Digest :=
  #v[0x03020100, 0x07060504, 0x0b0a0908, 0x0f0e0d0c, 0x13121110, 0x17161514, 0x1b1a1918,
    0xfffefdfc]

#guard digestBytes sample = (List.range 28).map Nat.toUInt8 ++ [0xfc, 0xfd, 0xfe, 0xff]
#guard digestOfBytes (digestBytes sample) = sample
#guard digestOfBytes (digestBytes sample ++ [1, 2, 3]) = sample
#guard kOfBytes (kBytes (K.ofBits 0x0123456789abcdef)) = K.ofBits 0x0123456789abcdef

/-! ## The chain read off a log -/

/-- A log of hash queries. -/
abbrev Log := List ((_ : List UInt8) × Digest)

/-- BLAKE2s-256, logging each query with its answer. -/
def loggedHash (t : List UInt8) : StateM Log Digest := do
  let d := blake2sBytes t
  modify (· ++ [⟨t, d⟩])
  return d

/-- The test chain's seed. -/
def seed : FsState := ⟨blake2sBytes [1, 2, 3]⟩

/-- The observed elements. -/
def x : E := E.ofLimbs (K.ofBits 5) (K.ofBits 6) (K.ofBits 7)

/-- The second observed element. -/
def y : E := E.ofLimbs (K.ofBits 11) 0 0

/-- An honest chain from the seed: two observes, a squeeze, the grinding base, a nonce, a
squeeze. -/
def honest : StateM Log FsState := do
  let s ← seed.observe loggedHash x
  let s ← s.observe loggedHash y
  let (_, s) ← s.sample loggedHash
  let _ ← s.powBase loggedHash
  let s ← s.absorbNonce loggedHash (FsState.nonceOf 262)
  let (_, s) ← s.sample loggedHash
  return s

/-- The honest chain's log. -/
def honestLog : Log := (honest.run []).2

/-- The honest chain's last state. -/
def final : FsState := (honest.run []).1

/-- The honest chain's blocks. -/
def blocks : List Block :=
  [.observe x, .observe y, .squeeze, .nonce (FsState.nonceOf 262), .squeeze]

-- Six queries, the fourth the grinding base, which is not a step.
#guard honestLog.length = 6
#guard (honestLog.map fun e ↦ (Block.parse? e.1).isSome) = [true, true, true, false, true, true]

-- The log is consistent, with no collision and no hit on the seed or a half of an earlier input.
#guard decide (QueryLog.Consistent honestLog)
#guard !decide (QueryLog.HasCollision honestLog)
#guard !decide (QueryLog.HasHit (inPlay [seed.cv]) honestLog)

-- The history of the last state is the chain: its blocks, and the answers of its step queries.
#guard (chainHistory honestLog seed final).map (·.map (·.1)) = some blocks
#guard (chainHistory honestLog seed final).map (·.map (·.2)) =
  some ((honestLog.eraseIdx 3).map (·.2))

-- Before the last squeeze is asked, the history of the state it squeezes is the chain so far.
#guard (chainHistory (honestLog.take 5) seed ⟨honestLog[4]!.2⟩).map (·.map (·.1)) =
  some (blocks.take 4)

-- The grinding base is not a step but starts from the state after the first squeeze: before it
-- is asked, that state's history is the chain so far.
#guard honestLog[2]!.2 ∈ halves honestLog[3]!.1
#guard (chainHistory (honestLog.take 3) seed ⟨honestLog[2]!.2⟩).map (·.map (·.1)) =
  some (blocks.take 3)

/-- A digest whose last 64-bit lane is the observe tag. -/
def right : Digest := #v[9, 9, 9, 9, 9, 9, 1, 0]

/-- A Merkle node over the state after the first squeeze and `right`: its input parses as an
observe step from that state. -/
def node : (_ : List UInt8) × Digest :=
  ⟨digestBytes honestLog[2]!.2 ++ digestBytes right, hashPair honestLog[2]!.2 right⟩

#guard (Block.parse? node.1).map (·.1) = some honestLog[2]!.2

/-- The honest log with the node asked in the middle. -/
def sharedLog : Log := honestLog.take 3 ++ [node] ++ honestLog.drop 3

-- The node is one more entry: the chain's history is unchanged, and the node's own history is
-- the chain to the first squeeze and one more step.
#guard !decide (QueryLog.HasCollision sharedLog)
#guard chainHistory sharedLog seed final = chainHistory honestLog seed final
#guard (chainHistory sharedLog seed ⟨node.2⟩).map (·.map (·.1)) =
  some (blocks.take 3 ++ ((Block.parse? node.1).map (·.2)).toList)

/-! ## The step parser -/

#guard Block.parse? (Block.input seed.cv (.observe x)) = some (seed.cv, .observe x)
#guard Block.parse? (Block.input seed.cv .squeeze) = some (seed.cv, .squeeze)
-- The grinding base, a squeeze carrying an element, and a 65-byte input are not steps.
#guard Block.parse? (FsState.stepBytes seed.cv 0 FsState.powBaseTag) = none
#guard Block.parse? (FsState.stepBytes seed.cv x FsState.squeezeTag) = none
#guard Block.parse? (Block.input seed.cv .squeeze ++ [0]) = none

/-! ## One mutation per hypothesis -/

/-- A digest with first word `n`. -/
def d (n : UInt32) : Digest := #v[n, 0, 0, 0, 0, 0, 0, 0]

-- A collision: a second step query answered by the state after the first observe. The step into
-- that state is ambiguous, and the history is lost.
/-- The honest log with a colliding step query. -/
def collidingLog : Log := honestLog ++ [⟨Block.input seed.cv (.observe y), honestLog[0]!.2⟩]

#guard decide (QueryLog.HasCollision collidingLog)
#guard chainHistory collidingLog seed final = none

-- An answer equal to the seed: the chain's first state is the seed, and the history stops there.
/-- A chain whose first step leads back to the seed. -/
def seedSteps : List (Block × Digest) := [(.observe x, seed.cv), (.squeeze, d 2)]

#guard !decide (QueryLog.HasCollision (HashChain.queries Block.input seed.cv seedSteps))
#guard chainHistory (HashChain.queries Block.input seed.cv seedSteps) seed ⟨d 2⟩ =
  some [(.squeeze, d 2)]
-- The same chain with a fresh first state is recovered.
#guard chainHistory (HashChain.queries Block.input seed.cv [(.observe x, d 1), (.squeeze, d 2)])
  seed ⟨d 2⟩ = some [(.observe x, d 1), (.squeeze, d 2)]

-- A hit on a half of an earlier input: the query from `d 1` is asked before the query that
-- produces `d 1`. The whole log has the history; the log before the query from `d 1` does not.
/-- The chain's next query, then the chain's one step. -/
def lateLog : Log :=
  [⟨Block.input (d 1) .squeeze, d 2⟩, ⟨Block.input seed.cv (.observe x), d 1⟩]

#guard decide (QueryLog.Consistent lateLog)
#guard !decide (QueryLog.HasCollision lateLog)
#guard decide (QueryLog.HasHit (inPlay [seed.cv]) lateLog)
#guard chainHistory lateLog seed ⟨d 1⟩ = some [(.observe x, d 1)]
#guard chainHistory (lateLog.take 0) seed ⟨d 1⟩ = none

-- A root absorbed as two observes is in play: a fresh node answered by it is a hit, which the
-- halves of the inputs alone do not show.
/-- The test's root. -/
def root : Digest := d 77

/-- A chain absorbing `root` as its two scalars and squeezing, then a fresh node answered by
`root`. -/
def rootLog : Log :=
  [⟨Block.input seed.cv (.observe (digestScalars root).1), d 1⟩,
    ⟨Block.input (d 1) (.observe (digestScalars root).2), d 2⟩,
    ⟨Block.input (d 2) .squeeze, d 3⟩,
    ⟨digestBytes (d 4) ++ digestBytes (d 5), root⟩]

#guard rebuiltRoots rootLog = [root]
#guard decide (QueryLog.Consistent rootLog)
#guard !decide (QueryLog.HasCollision rootLog)
#guard decide (QueryLog.HasHit (inPlay [seed.cv]) rootLog)
#guard !decide (QueryLog.HasHit (fun l ↦ seed.cv :: l.flatMap fun e ↦ halves e.1) rootLog)

/-! ## Each query at its first occurrence -/

/-- The honest log, asked twice. -/
def doubledLog : Log := honestLog ++ honestLog

-- Deduplication keeps the first occurrences, which on a consistent log changes neither a
-- history nor the digests in play.
#guard decide (QueryLog.Consistent doubledLog)
#guard QueryLog.dedupKeys doubledLog = honestLog
#guard chainHistory doubledLog seed final = chainHistory (QueryLog.dedupKeys doubledLog) seed final
#guard (inPlay [seed.cv] doubledLog).all (· ∈ inPlay [seed.cv] (QueryLog.dedupKeys doubledLog))

-- A repeated query with a second answer: the log is not consistent, and deduplication keeps
-- the first answer, so the second is lost.
/-- The honest log with its first query asked again, answered otherwise. -/
def reansweredLog : Log := honestLog ++ [⟨honestLog[0]!.1, d 9⟩]

#guard !decide (QueryLog.Consistent reansweredLog)
#guard QueryLog.dedupKeys reansweredLog = honestLog

-- A hit is at a first occurrence: the late log asked twice keeps its hit after deduplication.
#guard decide (QueryLog.HasHit (inPlay [seed.cv]) (lateLog ++ lateLog))
#guard decide (QueryLog.HasHit (inPlay [seed.cv]) (QueryLog.dedupKeys (lateLog ++ lateLog)))

-- At most two halves and one absorbed root per entry are in play.
#guard (inPlay [seed.cv] honestLog).length ≤ 1 + 3 * honestLog.length
#guard (inPlay [seed.cv] rootLog).length = 1 + 2 * 4 + 1

/-! ## One more query -/

-- A query answered by a digest not in play leaves every other history as it was, here with a
-- squeeze from the last state.
#guard !(d 99 ∈ inPlay [seed.cv] honestLog)
#guard chainHistory (honestLog ++ [⟨Block.input final.cv .squeeze, d 99⟩]) seed final =
  chainHistory honestLog seed final

-- The mutation: the late log's second query is answered by `d 1`, a half of the first, in play.
-- The history of `d 2` appears.
#guard d 1 ∈ inPlay [seed.cv] (lateLog.take 1)
#guard chainHistory (lateLog.take 1) seed ⟨d 2⟩ = none
#guard chainHistory lateLog seed ⟨d 2⟩ = some [(.observe x, d 1), (.squeeze, d 2)]

end LeanerVMTests.Protocol.RandomOracle
