import LeanerVM.Protocol.Whir.Cached
import LeanerVMTests.Protocol.WhirOpen

/-!
# Differential tests of WHIR's cached prover

The cached prover of WHIR's opening is proved to run as the honest one
(`Component.Cached.run_eq`); these `#guard`s check the compiled code on the opening tests' chain
of two levels, at challenge sequences a xorshift draws.

* **On words.** The transform on words (`fwdW`) against the transform over `K`, the encoder on
  words (`encodeE`) against `encode`, and the query weight's values on words (`queryCubeW`)
  against the batch of the column weights, with an encoding of another table and another batching
  challenge as mutations.
* **The stored word.** The stored rows of `wordRows` (the lanes encoded by the additive transform),
  read through `wordOfRows`, are `wordOf`'s at every position, on the first level's table.
* **The bound table.** The table bound on its lane coordinates to the fold point, renamed, is the
  folded table.
* **Runs.** At two seeds, the cached prover and the honest one send the same plain messages and
  the same round polynomials, hand on last words with the same rows, and are accepted by the
  verifier; runs at different seeds differ, and the cached prover with the stack's word replaced by
  another's is rejected.
-/

namespace LeanerVMTests.Protocol.WhirCached

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Whir CompPoly CMlPolynomialEval
open OracleComp OracleSpec ProtocolSpec StepSchedule
open LeanerVMTests.Protocol.WhirOpenToy

/-- A xorshift step. -/
private def xs (s : UInt64) : UInt64 :=
  let s := s ^^^ (s <<< 13)
  let s := s ^^^ (s >>> 7)
  s ^^^ (s <<< 17)

/-- Uniform samples read off the words of a xorshift. -/
private def xsImpl : QueryImpl unifSpec (StateM UInt64) :=
  fun n st ↦ (Fin.ofNat (n + 1) st.toNat, xs st)

/-- Run a prover at the challenges a xorshift draws from `seed`. -/
private def runAt {S W S' W' : Type} {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, SampleableType (pSpec.Challenge i)] (P : Prover []ₒ S W S' W' pSpec) (s : S) (w : W)
    (seed : UInt64) : pSpec.FullTranscript × S' × W' :=
  (simulateQ xsImpl
    (simulateQ (QueryImpl.add (fun t ↦ isEmptyElim t) challengeQueryImpl) (P.run s w))).run' seed

/-! ## The transform and the query weight on words -/

/-- A `K` element from a seed. -/
private def kOf (s : UInt64) : K := BF64.ofBitVec (xs s).toBitVec

/-- An `E` element from a seed. -/
private def eOf (s : UInt64) : E := E.ofLimbs (kOf s) (kOf (s + 1)) (kOf (s + 2))

/-- A table of `E` from a seed. -/
private def tabE (n : ℕ) (seed : UInt64) : CMlPolynomialEval E n :=
  Vector.ofFn fun i ↦ eOf (seed + 7 * i.val.toUInt64)

/-- Positions from a seed. -/
private def posOf (seed : UInt64) (q : Fin 5) : Fin (2 ^ (3 + 2)) :=
  Fin.ofNat _ (xs (seed + q.val.toUInt64)).toNat

-- The transform on words against the transform over `K`.
#guard
  let v : Vector K (2 ^ 4) := Vector.ofFn fun i ↦ kOf (13 + i.val.toUInt64)
  fwdW 4 (v.map FastBF64.toWord) (kOf 3) == (fwd (RingHom.id K) 4 v (kOf 3)).map FastBF64.toWord

-- The encoder on words against the definition, `2 ^ 3` coefficients on `2 ^ 5` positions.
#guard (List.finRange (2 ^ (3 + 2))).all fun y ↦
  (encodeE 3 2 (tabE 3 5))[y] == encode (algebraMap K E) 3 2 (tabE 3 5) y

-- The query weight's values on words against the batch of the column weights.
#guard queryCubeW 3 2 (posOf 17) (eOf 41) ==
  batchWeight (fun q ↦ (columnWeight (algebraMap K E) 3 2 (posOf 17 q)).onCube) (eOf 41)

-- Mutations: another table's encoding, another batching challenge.
#guard !(encodeE 3 2 (tabE 3 5) == encodeFast (algebraMap K E) 3 2 (tabE 3 6))
#guard !(queryCubeW 3 2 (posOf 17) (eOf 43) ==
  batchWeight (fun q ↦ (columnWeight (algebraMap K E) 3 2 (posOf 17 q)).onCube) (eOf 41))

/-! ## The stored word and the bound table -/

#guard (List.finRange (2 ^ (κ0 + sh0.R))).all fun y ↦
  (wordOfRows sh0.ℓ κ0 sh0.R sh0.t f0 (wordRows sh0.ℓ κ0 sh0.R f0)).row y ==
    (wordOf sh0.ℓ κ0 sh0.R sh0.t f0).row y

#guard castLanes (ProductSum.lowCache f0 sh0.ℓ r0) == foldTable f0 r0

/-! ## Runs -/

/-- The prover's messages in two transcripts of a step, compared where their type has `BEq`: the
plain messages and the round polynomials. Oracle messages and challenges are not compared. -/
private class StepEq (a : Step) where
  eq : a.spec.FullTranscript → a.spec.FullTranscript → Bool

private instance (M : Type) [BEq M] : StepEq (.msg M) :=
  ⟨fun T T' ↦
    let a : M := T ⟨0, Nat.one_pos⟩
    let b : M := T' ⟨0, Nat.one_pos⟩
    a == b⟩

private instance (M : Type) (i : OracleInterface M) : StepEq (.oracle M i) := ⟨fun _ _ ↦ true⟩

private instance (C : Type) (i : SampleableType C) : StepEq (.chal C i) := ⟨fun _ _ ↦ true⟩

private instance (C : Type) (i : SampleableType C) (k : ℕ) : StepEq (.chals C i k) :=
  ⟨fun _ _ ↦ true⟩

private instance : StepEq .skip := ⟨fun _ _ ↦ true⟩

/-- The round polynomials of two transcripts of `m` sumcheck rounds compared. -/
private def roundsEq (C : Type) [BEq C] (d : ℕ) : (m : ℕ) →
    (roundsSpec C d m).FullTranscript → (roundsSpec C d m).FullTranscript → Bool
  | 0, _, _ => true
  | m + 1, T, T' =>
    let r := FullTranscript.fst (pSpec₁ := roundSpec C d) (pSpec₂ := roundsSpec C d m) T
    let r' := FullTranscript.fst (pSpec₁ := roundSpec C d) (pSpec₂ := roundsSpec C d m) T'
    let a : Vector C (d + 1) := r ⟨0, Nat.two_pos⟩
    let b : Vector C (d + 1) := r' ⟨0, Nat.two_pos⟩
    a == b && roundsEq C d m (FullTranscript.snd (pSpec₁ := roundSpec C d) T)
      (FullTranscript.snd (pSpec₁ := roundSpec C d) T')

private instance (C : Type) [BEq C] (i : SampleableType C) (d m : ℕ) : StepEq (.rds C i d m) :=
  ⟨roundsEq C d m⟩

/-- The prover's messages in two transcripts of a list of steps, compared step by step. -/
private class SeqEq (l : List Step) where
  eq : (seqSpec l).FullTranscript → (seqSpec l).FullTranscript → Bool

private instance : SeqEq [] := ⟨fun _ _ ↦ true⟩

private instance (a : Step) (l : List Step) [StepEq a] [SeqEq l] : SeqEq (a :: l) :=
  ⟨fun T T' ↦
    StepEq.eq (FullTranscript.fst (pSpec₁ := a.spec) (pSpec₂ := seqSpec l) T)
        (FullTranscript.fst (pSpec₁ := a.spec) (pSpec₂ := seqSpec l) T') &&
      SeqEq.eq (FullTranscript.snd (pSpec₁ := a.spec) (pSpec₂ := seqSpec l) T)
        (FullTranscript.snd (pSpec₁ := a.spec) (pSpec₂ := seqSpec l) T')⟩

/-- The steps of the opening on the toy chain. -/
private abbrev toySteps : List Step :=
  .skip :: .msg (SumcheckRound.Message E 2) :: levelSteps sh0 sh1 (0 + 1) (finalSteps sh1 0)

/-- A run of the cached or the honest prover at a seed, on the statement and an oracle. -/
private def runOf (cached : Bool) (seed : UInt64) (o : ∀ i, OneW sh0 κ0 i := oracle0) :
    (seqSpec toySteps).FullTranscript × (Unit × ∀ i, OneW sh1 (0 + 1) i) × Unit :=
  if cached then runAt (whirOpenCached sh0 κ0 ladder).toProver (stmt0, o) stackQ seed
  else runAt (whirOpen sh0 κ0 ladder).red.prover (stmt0, o) stackQ seed

/-- Whether two runs send the same plain messages and round polynomials and hand on last words with
the same rows. -/
private def sameRuns (a b : (seqSpec toySteps).FullTranscript × (Unit × ∀ i, OneW sh1 (0 + 1) i) ×
    Unit) : Bool :=
  SeqEq.eq a.1 b.1 && (List.finRange _).all fun y ↦ (a.2.1.2 0).row y == (b.2.1.2 0).row y

#guard [3, 5].all fun seed ↦ sameRuns (runOf true seed) (runOf false seed)

-- Mutation: runs at different seeds draw other challenges and send other messages.
#guard !SeqEq.eq (l := toySteps) (runOf true 3).1 (runOf false 5).1

/-- Whether the verifier accepts a run of the cached or the honest prover at a seed, on the
statement and an oracle. -/
private def acceptsRun (cached : Bool) (seed : UInt64)
    (o : ∀ i, OneW sh0 κ0 i := oracle0) : Bool :=
  verifier.check (stmt0, o) (runOf cached seed o).1

#guard [3, 5].all fun seed ↦ acceptsRun true seed && acceptsRun false seed

/-- The honest word of another table. -/
private def otherWord : ∀ i, OneW sh0 κ0 i := fun _ ↦
  wordOf sh0.ℓ κ0 sh0.R sh0.t (relayout (Vector.ofFn fun i ↦ stackQ[i] + 1))

#guard [3, 5].all fun seed ↦ !acceptsRun true seed otherWord

end LeanerVMTests.Protocol.WhirCached
