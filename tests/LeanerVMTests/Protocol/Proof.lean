import LeanerVM.Protocol.Proof

/-!
# Proof object and transcript tests

**The Rust transcript.** `scripts/dump-fs-chain-rust.sh` (leanVM
`a386121f84292f6fa663aaa3e570c15bc0240ea2`) runs the pinned prover on the seed of a
four-instruction program and a public input: a squeeze, a scalar, a root, a cubic plain round
polynomial, a quartic round with its equality weight factored out, an 8-bit grind and a squeeze;
the pinned verifier reads it back. The writer here writes the Rust's eleven scalars, and the
reader reads the Rust's stream back to the same values, the derived coefficients included, and
the same challenges. The round-polynomial encoding drops `c_1` of a plain round and `c_0` of the
other; a quadratic reading of the three scalars is rejected.

**The announced sizes.** An admissible announcement reads back; each setup check rejects its
mutation: a nonzero upper limb, the memory above its window, a height above its cap, the
`BLAKE2S` table below its floor, the rate outside its window.

**Each reader check rejects its mutation:** a nonzero third limb in a root half, a wrong
grinding nonce, a nonzero nonce at 0 bits, a truncated stream, a trailing scalar, an unconsumed
opening, a missing opening, an opening that fails authentication, and a round polynomial of
degree `0`.
-/

namespace LeanerVMTests.Protocol.Proof

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Protocol LeanerVM.Protocol.Blake2sHash
open LeanerVM.Protocol.LeanIsa

/-- An element of `E` from its three limbs. -/
def e3 (a b c : ℕ) : E := E.ofLimbs (K.ofBits a) (K.ofBits b) (K.ofBits c)

/-- The dump's program (`tests/LeanerVMTests/Protocol/Transcript.lean`). -/
def program : Program where
  logSize := 2
  logSize_le := by decide
  code := ![
    .xor (gpow 1) (gpow 2) (gpow 3),
    .setConstant (gpow 4) (e3 0x1111 0x2222 0x3333),
    .deref (gpow 5) (gpow 6) (gpow 7) .pc,
    .jump (gpow 8) (gpow 9) (gpow 10)]

/-- The dump's public input. -/
def input : PublicInput := ⟨![K.ofBits 7, K.ofBits 11, K.ofBits 13, K.ofBits 17]⟩

/-- The seeded chain. -/
def s0 : FsState := FsState.seed program input

/-- The dump's scalar. -/
def x : E := e3 0x0123456789abcdef 0xfedcba9876543210 0x1111222233334444

/-- The dump's root, the bytes `3i + 1`. -/
def rootBytes : List UInt8 := (List.range 32).map fun i ↦ (3 * i + 1).toUInt8

/-- The digest of 32 bytes. -/
def digestOf (b : List UInt8) : Digest :=
  Vector.ofFn fun j : Fin 8 ↦
    leWord (b.getD (4 * j) 0) (b.getD (4 * j + 1) 0) (b.getD (4 * j + 2) 0) (b.getD (4 * j + 3) 0)

/-- The root. -/
def root : Digest := digestOf rootBytes

#guard digestBytes root = rootBytes

/-- The plain round's coefficients. -/
def plain : Vector E 4 := #v[e3 1 2 3, e3 4 5 6, e3 7 8 9, e3 10 11 12]

/-- The second round's coefficients. -/
def eqp : Vector E 5 := #v[e3 21 22 23, e3 24 25 26, e3 27 28 29, e3 30 31 32, e3 33 34 35]

/-- The second round's equality weight. -/
def r : E := e3 0x99 0x98 0x97

/-- The Rust's running claims: `c_1 + c_2 + c_3` and `c_0 + r·(c_1 + … + c_4)`. -/
def plainClaim : E := e3 9 6 3

/-- See `plainClaim`. -/
def eqClaim : E := e3 0x141 0x1d5a 0x31b

-- The claims are the round's checks at the coefficients, in Lean's arithmetic.
#guard plain[1] + plain[2] + plain[3] = plainClaim
#guard eqp[0] + r * (eqp[1] + eqp[2] + eqp[3] + eqp[4]) = eqClaim
#guard decide (RoundPoly.Check plainClaim none plain)
#guard decide (RoundPoly.Check eqClaim (some r) eqp)

/-- The Rust's stream. -/
def rustStream : List E :=
  [x, e3 0x1613100d0a070401 0x2e2b2825221f1c19 0, e3 0x4643403d3a373431 0x5e5b5855524f4c49 0,
    e3 1 2 3, e3 7 8 9, e3 10 11 12,
    e3 24 25 26, e3 27 28 29, e3 30 31 32, e3 33 34 35,
    e3 33 0 0]

/-- The Rust's two challenges. -/
def rustSamples : E × E :=
  (e3 0x63f0a4a9c30f242a 0x1eb9474962693c6f 0xacd540924c825f73,
    e3 0x4bb90b07d10f9a94 0x4beab46ed5678d04 0x634e9bf61f6e31c0)

/-! ## Round polynomials -/

-- A plain round drops `c_1`, the other round `c_0`.
#guard RoundPoly.encode none plain = [plain[0], plain[2], plain[3]]
#guard RoundPoly.encode (some r) eqp = [eqp[1], eqp[2], eqp[3], eqp[4]]
#guard RoundPoly.decode 3 plainClaim none ((rustStream.drop 3).take 3) = some plain
#guard RoundPoly.decode 4 eqClaim (some r) ((rustStream.drop 6).take 4) = some eqp
-- A quadratic reading of the three plain scalars is rejected, and a degree of `0` too.
#guard RoundPoly.decode 2 plainClaim none ((rustStream.drop 3).take 3) = none
#guard RoundPoly.decode 0 plainClaim (some r) [] = none
-- Another claim decodes another polynomial, which fails the check at the true claim.
#guard (RoundPoly.decode 3 (plainClaim + 1) none ((rustStream.drop 3).take 3)).map
    (fun c ↦ decide (RoundPoly.Check plainClaim none c)) = some false
-- Reading the plain round as the other kind decodes another polynomial.
#guard RoundPoly.decode 3 plainClaim (some r) ((rustStream.drop 3).take 3) ≠ some plain

/-! ## The Rust transcript -/

/-- The prover of the dump. -/
def honest : WriteM Id Unit (E × E) := do
  let p1 ← Writer.sample blake2sBytes
  Writer.addScalar blake2sBytes x
  Writer.addRoot blake2sBytes root
  Writer.addRoundPoly blake2sBytes none plain
  Writer.addRoundPoly blake2sBytes (some r) eqp
  Writer.grind blake2sBytes 1024 8
  let p2 ← Writer.sample blake2sBytes
  return (p1, p2)

/-- The verifier of the dump. -/
def check : ReadM Id Unit (E × E × Digest × Vector E 4 × Vector E 5 × E) := do
  let p1 ← Reader.sample blake2sBytes
  let y ← Reader.nextScalar blake2sBytes
  let d ← Reader.nextRoot blake2sBytes
  let c ← Reader.nextRoundPoly blake2sBytes 3 plainClaim none
  let c' ← Reader.nextRoundPoly blake2sBytes 4 eqClaim (some r)
  Reader.checkPow blake2sBytes 8
  let p2 ← Reader.sample blake2sBytes
  return (p1, y, d, c, c', p2)

/-- The verifier's rejection, if any. -/
def errorOf {α : Type} : Except ReadError α → Option ReadError
  | .ok _ => none
  | .error e => some e

/-- The written proof. -/
def written : Option (Proof Unit) := (Id.run (runWrite honest s0)).map (·.2.proof)

-- The writer writes the Rust's stream and draws the Rust's challenges.
#guard written.map (·.stream) = some rustStream
#guard (Id.run (runWrite honest s0)).map (·.1) = some rustSamples

/-- The verifier on a stream and openings. -/
def verdict (stream : List E) (merkle : List Unit := []) :
    Except ReadError ((E × E × Digest × Vector E 4 × Vector E 5 × E) × FsState) :=
  Id.run (runRead check s0 ⟨stream, merkle⟩)

-- The reader reads the Rust's stream back: the values, the derived coefficients, the
-- challenges, and the writer's final chain state.
#guard match verdict rustStream with
  | .ok ((p1, y, d, c, c', p2), fs) =>
    p1 = rustSamples.1 && y = x && d.toList = root.toList && c = plain && c' = eqp &&
      p2 = rustSamples.2 &&
      (Id.run (runWrite honest s0)).any (fun w ↦ w.2.fs.cv.toList = fs.cv.toList)
  | .error _ => false

/-! ## Each reader check rejects its mutation -/

/-- The Rust stream with scalar `i` replaced. -/
def mutate (i : ℕ) (v : E) : List E := rustStream.set i v

-- A nonzero third limb in either half of the root.
#guard errorOf (verdict (mutate 1 (e3 0x1613100d0a070401 0x2e2b2825221f1c19 1))) =
  some .nonCanonicalEncoding
#guard errorOf (verdict (mutate 2 (e3 0x4643403d3a373431 0x5e5b5855524f4c49 1))) =
  some .nonCanonicalEncoding
-- A nonce below the smallest that clears 8 bits.
#guard errorOf (verdict (mutate 10 (e3 32 0 0))) = some .powFailed
-- The stream truncated, extended, or with an opening left over.
#guard errorOf (verdict rustStream.dropLast) = some .exceededStream
#guard errorOf (verdict (rustStream ++ [0])) = some .notFullyConsumed
#guard errorOf (verdict rustStream [()]) = some .notFullyConsumed
-- A scalar changed under the plain round changes every later challenge, so the grind fails.
#guard errorOf (verdict (mutate 4 (e3 7 8 10))) = some .powFailed

-- Openings: missing, and failing authentication.
#guard errorOf (Id.run (runRead (Reader.nextOpening (M := Unit) (α := Unit)
    (m := Id) fun _ ↦ some ()) s0 ⟨[], []⟩)) = some .missingHint
#guard errorOf (Id.run (runRead (Reader.nextOpening (M := Unit) (α := Unit)
    (m := Id) fun _ ↦ none) s0 ⟨[], [()]⟩)) = some .invalidMerkleOpening
#guard errorOf (Id.run (runRead (Reader.nextOpening (M := Unit) (α := Unit)
    (m := Id) fun _ ↦ some ()) s0 ⟨[], [()]⟩)) = none

-- A round polynomial of degree `0`, rejected before anything is read.
#guard errorOf (Id.run (runRead (Reader.nextRoundPoly (M := Unit) blake2sBytes 0 plainClaim none)
    s0 ⟨[], []⟩)) = some .roundDegree
#guard errorOf (Id.run (runRead (Reader.nextRoundPoly (M := Unit) blake2sBytes 0 eqClaim (some r))
    s0 ⟨[plainClaim], []⟩)) = some .roundDegree

-- At 0 bits only the nonce `0` passes the reader's check.
#guard errorOf (Id.run (runRead (Reader.checkPow (M := Unit) blake2sBytes 0) s0 ⟨[0], []⟩)) =
  none
#guard errorOf (Id.run (runRead (Reader.checkPow (M := Unit) blake2sBytes 0) s0 ⟨[1], []⟩)) =
  some .powFailed
#guard errorOf (Id.run (runRead (Reader.checkPow (M := Unit) blake2sBytes 0) s0
    ⟨[e3 0 1 0], []⟩)) = some .powFailed

/-! ## The announced sizes -/

/-- Admissible sizes for the program. -/
def sizes : Sizes := ⟨16, by decide, ![16, 3, 16, 4, 16, 16]⟩

#guard setupOk program sizes 1

/-- The reader of the announcement, as `read_public` runs it. -/
def readSizesOn (stream : List E) : Except ReadError ((Sizes × ℕ) × FsState) :=
  Id.run (runRead (Reader.readSizes (M := Unit) blake2sBytes program) s0 ⟨stream, []⟩)

/-- The announcement the writer sends. -/
def announced : Option (List E) :=
  (Id.run (runWrite (Writer.announce (M := Unit) blake2sBytes sizes 1) s0)).map
    (·.2.proof.stream)

#guard announced = some (announcement sizes 1)
#guard (announcement sizes 1).length = 8
#guard (⟨announcement sizes 1, []⟩ : Proof Unit).sizes?.map (fun s ↦ (s.logMem, List.ofFn s.τ)) =
  some (16, [16, 3, 16, 4, 16, 16])
#guard match readSizesOn (announcement sizes 1) with
  | .ok ((s, ρ), _) => s.logMem = 16 && List.ofFn s.τ = [16, 3, 16, 4, 16, 16] && ρ = 1
  | .error _ => false

/-- The announcement with scalar `i` replaced. -/
def mutateSize (i : ℕ) (v : E) : List E := (announcement sizes 1).set i v

-- A nonzero upper limb: in the memory's size, in a table's, in the rate's.
#guard errorOf (readSizesOn (mutateSize 0 (e3 16 1 0))) = some .publicInput
#guard errorOf (readSizesOn (mutateSize 3 (e3 16 0 1))) = some .publicInput
#guard errorOf (readSizesOn (mutateSize 7 (e3 1 1 0))) = some .publicInput
#guard (⟨mutateSize 0 (e3 16 1 0), []⟩ : Proof Unit).sizes?.isNone
-- The memory outside `[16, 32]`, a height above `32`, `BLAKE2S` below `3`, the rate outside
-- `[1, 4]`.
#guard errorOf (readSizesOn (mutateSize 0 (e3 33 0 0))) = some .publicInput
#guard errorOf (readSizesOn (mutateSize 0 (e3 15 0 0))) = some .publicInput
#guard errorOf (readSizesOn (mutateSize 1 (e3 33 0 0))) = some .publicInput
#guard errorOf (readSizesOn (mutateSize 6 (e3 2 0 0))) = some .publicInput
#guard errorOf (readSizesOn (mutateSize 7 (e3 5 0 0))) = some .publicInput
#guard errorOf (readSizesOn (mutateSize 7 (e3 0 0 0))) = some .publicInput
-- A stacked size above `2^28`.
#guard !setupOk program ⟨28, by decide, ![16, 3, 16, 4, 16, 16]⟩ 1
#guard errorOf (readSizesOn (mutateSize 0 (e3 28 0 0))) = some .publicInput
-- A short announcement.
#guard errorOf (readSizesOn (announcement sizes 1).dropLast) = some .exceededStream

/-! ## The round trip, stated -/

example (H : List UInt8 → Id Digest) (prog : Program) (s : Sizes) (ρ : ℕ)
    (hs : setupOk prog s ρ = true) (fs : FsState) (w : WriterState Unit)
    (hw : Id.run (runWrite (Writer.announce H s ρ) fs) = some ((), w)) :
    Id.run (runRead (Reader.readSizes H prog) fs w.proof) = Except.ok ((s, ρ), w.fs) := by
  obtain ⟨b, rfl, hb⟩ := runRead_runWrite (readsBack_announce H hs) hw
  exact hb

end LeanerVMTests.Protocol.Proof
