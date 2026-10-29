import LeanerVM.Protocol.ToArkLib.DecodeSteps

/-!
# Transcript decoding tests

A toy two-phase schedule decoded from a list of natural numbers: the first phase is a message read
off one reading and a challenge read as the sum of the next two, the second a message read as its
reading less the first message, rejected below it. Every prefix of an input decodes to a prefix of
what the input decodes to (`decodePrefix_mono`), every cut where a round begins decodes to at
least that round (`decodePrefix_of_run_append`), and the full decoding is the first phase's run
followed by the second phase's decoding (`decode_append`). Readings left over, a slot cut short and
a reading the second phase rejects decode to nothing. A schedule ending in a message of no reading
decodes to its longest prefix. Sumcheck rounds rebuild the dropped coefficient from the claim they
carry (`rounds`), and a list of steps decodes through `SeqDecoder`. Three reading functions break
the law every slot satisfies (`Slot.read_iff`): one that needs readings it does not consume, one
that leaves more readings than it was given, and one that reads the last reading.
-/

namespace LeanerVMTests.Protocol.DecodeTranscript

open ProtocolSpec LeanerVM.Protocol LeanerVM.Protocol.SlotDecoder LeanerVM.Protocol.StepSchedule

/-! ## A two-phase schedule -/

/-- The first phase: a message, then a challenge. -/
abbrev phaseSpec : ProtocolSpec 2 := say ℕ ++ₚ draw ℕ

/-- The toy schedule: the first phase, then a message. -/
abbrev toySpec : ProtocolSpec 3 := phaseSpec ++ₚ say ℕ

/-- One reading, as it is. -/
def reading : Slot ℕ ℕ := Slot.next some

/-- The sum of two readings. -/
def sumOfTwo : Slot ℕ ℕ := Slot.take 2 fun l ↦ some l.sum

/-- The first phase: the message off one reading, the challenge the sum of the next two. -/
def phaseDecoder : SlotDecoder ℕ phaseSpec :=
  (single (pSpec := say ℕ) reading).append fun _ ↦ single (pSpec := draw ℕ) sumOfTwo

/-- The first phase's message. -/
def firstMessage (t : phaseSpec.FullTranscript) : ℕ := t 0

/-- The second phase, given the first phase's transcript: its reading less the first message. -/
def secondDecoder (t : phaseSpec.FullTranscript) : SlotDecoder ℕ (say ℕ) :=
  single (Slot.next fun a ↦ if firstMessage t ≤ a then some (a - firstMessage t) else none)

/-- The toy decoder. -/
def toy : SlotDecoder ℕ toySpec := phaseDecoder.append secondDecoder

/-- The three values of a full transcript. -/
def vals (t : toySpec.FullTranscript) : ℕ × ℕ × ℕ := (t 0, t 1, t 2)

/-- The values of a prefix. -/
def prefixVals : (Σ i : Fin 4, toySpec.Transcript i) → List ℕ
  | ⟨i, tr⟩ => (if h : 0 < i.val then [(tr ⟨0, h⟩ : ℕ)] else []) ++
      (if h : 1 < i.val then [(tr ⟨1, h⟩ : ℕ)] else []) ++
      (if h : 2 < i.val then [(tr ⟨2, h⟩ : ℕ)] else [])

/-- The input of the tests: the message `3`, the challenge `4 + 5`, the message `10 - 3`. -/
def input : List ℕ := [3, 4, 5, 10]

example : (toy.decode input).map vals = some (3, 9, 7) := by decide

-- Every prefix of the input decodes to the prefix of the transcript it reads.
#guard (List.range 5).map (fun k ↦ (toy.decodePrefix (input.take k)).map prefixVals) =
  [some [], some [3], none, some [3, 9], some [3, 9, 7]]

example : (toy.decodePrefix [3, 4, 5]).map prefixVals = some [3, 9] := by decide

/-- Whether the prefix decoded from each prefix of `l` begins the one decoded from `l`, where both
decode. -/
def prefixesExtend (l : List ℕ) : Bool :=
  (List.range (l.length + 1)).all fun k ↦
    match (toy.decodePrefix (l.take k)).map prefixVals, (toy.decodePrefix l).map prefixVals with
    | some a, some b => a.isPrefixOf b
    | _, _ => true

#guard prefixesExtend input
#guard prefixesExtend [0, 0, 0, 0]

/-- Whether every cut of `l` where a round begins decodes to at least that round. -/
def cutsDecode (l : List ℕ) : Bool :=
  (List.range (l.length + 1)).all fun m ↦ (List.finRange 4).all fun i ↦
    match toy.run i.val (Nat.le_of_lt_succ i.isLt) l with
    | some (_, r) => r != l.drop m ||
        match toy.decodePrefix (l.take m) with
        | some p => i.val ≤ p.1.val
        | none => false
    | none => true

#guard cutsDecode input

-- The append law, on the input and on inputs the second phase rejects or that leave readings over.
#guard [input, [3, 4, 5, 1], [3, 4, 5, 10, 0], [3, 4]].all fun l ↦
  (toy.decode l).map vals = (phaseDecoder.runFull l).bind fun p ↦
    ((secondDecoder p.1).decode p.2).map fun t ↦ (firstMessage p.1, p.1 1, t 0)

/-! ## Inputs that decode to nothing -/

-- A reading left over.
example : toy.decode (input ++ [0]) = none := by decide
example : toy.decodePrefix (input ++ [0]) = none := by decide
-- The challenge's slot cut short.
example : toy.decodePrefix [3, 4] = none := by decide
example : ∀ i, toy.decodeAt i [3, 4] = none := by decide
-- A reading below the first message, which the second phase rejects.
example : toy.decode [3, 4, 5, 1] = none := by decide
example : (toy.decodePrefix [3, 4, 5, 1]).map prefixVals = none := by decide

/-! ## The longest prefix -/

/-- A message, then a message of no reading. -/
def trailing : SlotDecoder ℕ (say ℕ ++ₚ say Unit) :=
  (single (pSpec := say ℕ) reading).append fun _ ↦ single (pSpec := say Unit) (Slot.pure ())

-- One reading decodes both rounds, not only the first.
example : (trailing.decodePrefix [3]).map (·.1.val) = some 2 := by decide
example : (trailing.decodeAt ⟨1, by decide⟩ [3]).isSome = true := by decide

/-! ## A run of challenges -/

/-- Three challenges, one reading each. -/
def threeDraws : SlotDecoder ℕ (LeanerVM.Protocol.draws ℕ 3) := SlotDecoder.draws reading 3

/-- The three challenges. -/
def drawVals (t : (LeanerVM.Protocol.draws ℕ 3).FullTranscript) : ℕ × ℕ × ℕ :=
  (t ⟨0, by decide⟩, t ⟨1, by decide⟩, t ⟨2, by decide⟩)

example : (threeDraws.decode [1, 2, 3]).map drawVals = some (1, 2, 3) := by decide
example : (threeDraws.decodePrefix [1, 2]).map (·.1.val) = some 2 := by decide

/-! ## Sumcheck rounds carrying their claim -/

/-- A round's polynomial `c₀ + c₁ X` from its one reading `c₁`, with `c₀` the claim less `c₁`. -/
def poly (claim : ℕ) : Slot ℕ (Vector ℕ 2) :=
  Slot.next fun c₁ ↦ if c₁ ≤ claim then some #v[claim - c₁, c₁] else none

/-- The next claim: the round's polynomial at its challenge. -/
def nextClaim (_ : ℕ) (t : (roundSpec ℕ 1).FullTranscript) : ℕ :=
  let p : Vector ℕ 2 := t 0
  let r : ℕ := t 1
  p[0] + p[1] * r

/-- Two rounds from the claim `10`. -/
def twoRounds : SlotDecoder ℕ (roundsSpec ℕ 1 2) := rounds poly (fun _ ↦ reading) nextClaim 10 2

/-- The two polynomials' coefficients and the two challenges. -/
def roundVals (t : (roundsSpec ℕ 1 2).FullTranscript) : List ℕ × ℕ × List ℕ × ℕ :=
  (Vector.toList (n := 2) (t ⟨0, by decide⟩), t ⟨1, by decide⟩,
    Vector.toList (n := 2) (t ⟨2, by decide⟩), t ⟨3, by decide⟩)

-- The first round `6 + 4 X` at `2` leaves `14`; the second `9 + 5 X` at `1` leaves `14`.
example : (twoRounds.decode [4, 2, 5, 1]).map roundVals = some ([6, 4], 2, [9, 5], 1) := by
  decide
-- A coefficient above the claim is rejected.
example : twoRounds.decode [4, 2, 15, 1] = none := by decide

/-! ## A list of steps -/

/-- The steps: a message, a challenge in `Fin 16`, a message. -/
abbrev steps : List Step := [.msg ℕ, .chal (Fin 16) inferInstance, .msg ℕ]

/-- The challenge read off its reading modulo `16`, the last message as the first plus its
reading. -/
def stepsDecoder : SeqDecoder ℕ steps :=
  (single reading, fun t₁ ↦
    (single (Slot.next fun a ↦ some ⟨a % 16, Nat.mod_lt a (by decide)⟩), fun _ ↦
      (single (Slot.next fun a ↦ let x : ℕ := t₁ ⟨0, by decide⟩; some (x + a)), fun _ ↦ ⟨⟩)))

/-- The three values of a transcript of the steps. -/
def stepVals (t : (seqSpec steps).FullTranscript) : ℕ × ℕ × ℕ :=
  (t ⟨0, by decide⟩, Fin.val (n := 16) (t ⟨1, by decide⟩), t ⟨2, by decide⟩)

example : (stepsDecoder.toDecoder.decode [3, 20, 4]).map stepVals = some (3, 4, 7) := by decide

/-! ## Reading functions that are not slots -/

/-- The law of slots, for a bare reading function: it consumes a prefix, which read alone gives the
same value. -/
def ReadsPrefix (f : List ℕ → Option (ℕ × List ℕ)) : Prop :=
  ∀ l x r, f l = some (x, r) ↔ ∃ c, l = c ++ r ∧ f c = some (x, [])

/-- The first reading, when there are at least three. -/
def lookahead (l : List ℕ) : Option (ℕ × List ℕ) :=
  if 3 ≤ l.length then some (l.headD 0, l.tail) else none

-- It reads `1` off `[1, 2, 3]` consuming `[1]`, but not off `[1]` alone. A decoder through it
-- would decode `[1, 2, 3]` while its first round's reading `[1]` decodes to nothing.
example : ¬ ReadsPrefix lookahead := fun h ↦ by
  obtain ⟨c, hc, hr⟩ := (h [1, 2, 3] 1 [2, 3]).mp rfl
  obtain rfl : c = [1] := List.append_cancel_right (hc.symm.trans (rfl : [1, 2, 3] = [1] ++ [2, 3]))
  exact absurd hr (by decide)

/-- One reading, put back twice. -/
def duplicating : List ℕ → Option (ℕ × List ℕ)
  | [] => none
  | a :: l => some (a, a :: a :: l)

-- It leaves more readings than it was given: what is left is not a suffix of the input.
example : ¬ ReadsPrefix duplicating := fun h ↦ by
  obtain ⟨c, hc, -⟩ := (h [1] 1 [1, 1]).mp rfl
  have := congrArg List.length hc
  simp at this

/-- The last reading, consuming all of them. -/
def lastReading (l : List ℕ) : Option (ℕ × List ℕ) := l.getLast?.map (·, [])

-- It reads `3` off `[3]`, but a reading appended after changes the value.
example : ¬ ReadsPrefix lastReading :=
  fun h ↦ absurd ((h [3, 4] 3 [4]).mpr ⟨[3], rfl, rfl⟩) (by decide)

end LeanerVMTests.Protocol.DecodeTranscript
