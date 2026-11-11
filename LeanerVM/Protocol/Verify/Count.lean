/-
  LeanerVM.Protocol.Verify.Count

  The chain walk of the executable verifier counted: for a count of its primitives that adds up
  along `bind` (hash queries, scalars read), the count of every walk, in closed form in the
  sizes.
-/

module

public import LeanerVM.Protocol.Verify
public import LeanerVM.Protocol.ToVCVio.MonadRel

/-!
# The chain walk, counted

`StepCounts` gives a count to each of the chain walk's four primitives: read a scalar, squeeze a
challenge, read a root, check a nonce at a number of bits. `StepCounts.chain` is the count of the
whole chain walk (`walkChain`) at the sizes, in closed form, phase by phase (`StepCounts.bus`,
`StepCounts.whir`, ...).

For a property `𝓖 : MonadGrade n` of computations graded by a count additive along `bind`, and a
record of primitives each with its count (`ChainOps.Graded`), every walk has its count
(`walkChain_grade`), by induction on the walk as in `walkChain_rel`: no walk's count depends on
a value it reads, only on the sizes. Two instances: the hash queries of the walk on the proof
reader at the random oracle (`VerifierQueries`), and the scalars it reads off the stream.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics Blake2sHash LeanIsa

@[expose] public section

namespace Verify

/-- A count for each of the chain walk's primitives. -/
structure StepCounts where
  /-- Reading a scalar. -/
  scalar : ℕ
  /-- Squeezing a challenge. -/
  sample : ℕ
  /-- Reading a root. -/
  root : ℕ
  /-- Checking a nonce at a number of bits. -/
  pow : ℕ → ℕ

namespace StepCounts

variable (c : StepCounts)

/-- A round of `d` wire coefficients. -/
def round (d : ℕ) : ℕ := d * c.scalar + c.sample

/-- `k` rounds of `d` wire coefficients. -/
def rounds (d k : ℕ) : ℕ := k * c.round d

/-- The setup: eight scalars and the root. -/
def setup : ℕ := 8 * c.scalar + c.root

/-- A layer of radix `2 ^ ρ` at depth `j`. -/
def layer (ρ j : ℕ) : ℕ := c.rounds (2 ^ ρ) j + 3 * (2 ^ ρ * c.scalar) + ρ * c.sample + c.sample

/-- The layers of the given radix exponents from depth `j`. -/
def layers : List ℕ → ℕ → ℕ
  | [], _ => 0
  | ρ :: rest, j => c.layer ρ j + layers rest (j + ρ)

/-- The bus phase. -/
def bus (μBus nValues : ℕ) : ℕ :=
  4 * c.sample + c.sample + c.scalar + c.scalar + c.sample + c.layers (gkrRadices μBus) 0 +
    nValues * c.scalar

/-- The table sumcheck. -/
def tables (τmax nCols : ℕ) : ℕ := c.sample + c.rounds 3 τmax + nCols * c.scalar

/-- The public input. -/
def pub (nSent : ℕ) : ℕ := c.sample + nSent * c.scalar

/-- The Flock phase for `2 ^ k` compressions. -/
def flock (k : ℕ) : ℕ :=
  (k + 1) * c.sample + 2 ^ Flock.kSkip * c.scalar + c.sample + c.rounds 2 (Flock.kIn + k) +
    2 * c.scalar + c.sample + c.rounds 2 Flock.kIn + 2 ^ Flock.kSkip * c.scalar + 6 * c.sample

/-- `k` fold rounds. -/
def folds (k : ℕ) : ℕ := k * (c.sample + 2 * c.scalar)

/-- `k` tail rounds. -/
def tail : ℕ → ℕ
  | 0 => 0
  | k + 1 => c.sample + (if k = 0 then 0 else 2 * c.scalar) + tail k

/-- `need` positions of `depth` bits, with `fuel` squeezes at most. -/
def positions (depth : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | fuel + 1, need + 1 => c.sample + positions depth fuel (need + 1 - min (192 / depth) (need + 1))

/-- A level of WHIR's opening. -/
def level (sh : LevelShape) : ℕ :=
  c.folds sh.fold + (if sh.final then 2 ^ sh.msgLog * c.scalar else 0) +
    (if sh.final then 0 else c.root) + (if sh.final then 0 else sh.msgLog * c.sample) +
    (if sh.final then 0 else c.scalar) + (if sh.final then 0 else 2 * c.scalar) +
    c.pow Whir.queryGrindingBits + c.positions (sh.msgLog + sh.rate) sh.queries sh.queries +
    c.sample + 2 * c.scalar + (if sh.final then c.tail sh.msgLog else 0)

/-- The levels of WHIR's opening. -/
def levels : List LevelShape → ℕ
  | [] => 0
  | sh :: shs => c.level sh + levels shs

/-- WHIR's opening: the first round polynomial, then the levels. -/
def whir (shs : List LevelShape) : ℕ := 2 * c.scalar + c.levels shs

/-- **The chain walk** on the instance of `prog` at the sizes `s`, with the opening's levels
`shs`. -/
def chain (prog : Program) (s : Sizes) (input : PublicInput) (shs : List LevelShape) : ℕ :=
  c.setup + c.bus (leanVm prog s).μBus (leanVm prog s).busClaims +
    c.tables (leanVm prog s).τmax (leanVm prog s).tableColumns +
    c.pub (PublicInput.sentCount (leanVm prog s) ((leanVm prog s).publicLines input)) +
    c.flock (s.τ 5) + c.sample + c.whir shs

end StepCounts

variable {n : Type → Type} [Monad n]

/-- A record of primitives each with its count under a graded property. -/
structure ChainOps.Graded (𝓖 : MonadGrade n) (ops : ChainOps n) (c : StepCounts) : Prop where
  /-- Reading a scalar. -/
  nextScalar : 𝓖.P ops.nextScalar c.scalar
  /-- Squeezing a challenge. -/
  sample : 𝓖.P ops.sample c.sample
  /-- Reading a root. -/
  nextRoot : 𝓖.P ops.nextRoot c.root
  /-- Checking a nonce. -/
  checkPow : ∀ bits, 𝓖.P (ops.checkPow bits) (c.pow bits)

variable {𝓖 : MonadGrade n} {ops : ChainOps n} {c : StepCounts} (h : ChainOps.Graded 𝓖 ops c)

include h

theorem nextScalars_grade : ∀ k, 𝓖.P (ops.nextScalars k) (k * c.scalar)
  | 0 => 𝓖.of_eq (𝓖.pure _) (by simp)
  | k + 1 => 𝓖.of_eq (𝓖.bind h.nextScalar fun _ ↦ 𝓖.bind (nextScalars_grade k) fun _ ↦
      𝓖.pure _) (by ring)

theorem samples_grade : ∀ k, 𝓖.P (samples ops k) (k * c.sample)
  | 0 => 𝓖.of_eq (𝓖.pure _) (by simp)
  | k + 1 => 𝓖.of_eq (𝓖.bind h.sample fun _ ↦ 𝓖.bind (samples_grade k) fun _ ↦ 𝓖.pure _)
      (by ring)

theorem readRound_grade (d : ℕ) : 𝓖.P (readRound ops d) (c.round d) :=
  𝓖.of_eq (𝓖.bind (nextScalars_grade h d) fun _ ↦ 𝓖.bind h.sample fun _ ↦ 𝓖.pure _)
    (by simp [StepCounts.round])

theorem readRounds_grade (d : ℕ) : ∀ k, 𝓖.P (readRounds ops d k) (c.rounds d k)
  | 0 => 𝓖.of_eq (𝓖.pure _) (by simp [StepCounts.rounds])
  | k + 1 => 𝓖.of_eq (𝓖.bind (readRound_grade h d) fun _ ↦
      𝓖.bind (readRounds_grade d k) fun _ ↦ 𝓖.pure _) (by simp only [StepCounts.rounds]; ring)

theorem walkSetup_grade : 𝓖.P (walkSetup ops) c.setup :=
  𝓖.bind (nextScalars_grade h 8) fun _ ↦ h.nextRoot

theorem walkLayer_grade (ρ j : ℕ) : 𝓖.P (walkLayer ops ρ j) (c.layer ρ j) :=
  𝓖.of_eq (𝓖.bind (readRounds_grade h _ _) fun _ ↦ 𝓖.bind (nextScalars_grade h _) fun _ ↦
    𝓖.bind (nextScalars_grade h _) fun _ ↦ 𝓖.bind (nextScalars_grade h _) fun _ ↦
    𝓖.bind (samples_grade h _) fun _ ↦ 𝓖.bind h.sample fun _ ↦ 𝓖.pure _)
    (by simp only [StepCounts.layer]; ring)

theorem walkLayers_grade : ∀ (ρs : List ℕ) (j : ℕ), 𝓖.P (walkLayers ops ρs j) (c.layers ρs j)
  | [], _ => 𝓖.pure _
  | ρ :: rest, j => 𝓖.of_eq (𝓖.bind (walkLayer_grade h ρ j) fun _ ↦
      𝓖.bind (walkLayers_grade rest (j + ρ)) fun _ ↦ 𝓖.pure _) (by simp [StepCounts.layers])

theorem walkBus_grade (μBus nValues : ℕ) :
    𝓖.P (walkBus ops μBus nValues) (c.bus μBus nValues) :=
  𝓖.of_eq (𝓖.bind (samples_grade h 4) fun _ ↦ 𝓖.bind h.sample fun _ ↦
    𝓖.bind h.nextScalar fun _ ↦ 𝓖.bind h.nextScalar fun _ ↦ 𝓖.bind h.sample fun _ ↦
    𝓖.bind (walkLayers_grade h _ _) fun _ ↦ 𝓖.bind (nextScalars_grade h _) fun _ ↦ 𝓖.pure _)
    (by simp only [StepCounts.bus]; ring)

theorem walkTables_grade (τmax nCols : ℕ) :
    𝓖.P (walkTables ops τmax nCols) (c.tables τmax nCols) :=
  𝓖.of_eq (𝓖.bind h.sample fun _ ↦ 𝓖.bind (readRounds_grade h _ _) fun _ ↦
    𝓖.bind (nextScalars_grade h _) fun _ ↦ 𝓖.pure _) (by simp only [StepCounts.tables]; ring)

theorem walkPub_grade (nSent : ℕ) : 𝓖.P (walkPub ops nSent) (c.pub nSent) :=
  𝓖.of_eq (𝓖.bind h.sample fun _ ↦ 𝓖.bind (nextScalars_grade h _) fun _ ↦ 𝓖.pure _)
    (by simp [StepCounts.pub])

theorem walkFlock_grade (k : ℕ) : 𝓖.P (walkFlock ops k) (c.flock k) :=
  𝓖.of_eq (𝓖.bind (samples_grade h _) fun _ ↦ 𝓖.bind (nextScalars_grade h _) fun _ ↦
    𝓖.bind h.sample fun _ ↦ 𝓖.bind (readRounds_grade h _ _) fun _ ↦
    𝓖.bind (nextScalars_grade h _) fun _ ↦ 𝓖.bind h.sample fun _ ↦
    𝓖.bind (readRounds_grade h _ _) fun _ ↦ 𝓖.bind (nextScalars_grade h _) fun _ ↦
    𝓖.bind (samples_grade h _) fun _ ↦ 𝓖.pure _) (by simp only [StepCounts.flock]; ring)

theorem walkFolds_grade : ∀ k, 𝓖.P (walkFolds ops k) (c.folds k)
  | 0 => 𝓖.of_eq (𝓖.pure _) (by simp [StepCounts.folds])
  | k + 1 => 𝓖.of_eq (𝓖.bind h.sample fun _ ↦ 𝓖.bind (nextScalars_grade h 2) fun _ ↦
      𝓖.bind (walkFolds_grade k) fun _ ↦ 𝓖.pure _) (by simp only [StepCounts.folds]; ring)

theorem walkTail_grade : ∀ k, 𝓖.P (walkTail ops k) (c.tail k)
  | 0 => 𝓖.pure _
  | k + 1 => 𝓖.of_eq (𝓖.bind h.sample fun _ ↦
      𝓖.ite_bind (k = 0) (𝓖.pure _) (nextScalars_grade h 2) fun _ ↦
      𝓖.bind (walkTail_grade k) fun _ ↦ 𝓖.pure _) (by simp only [StepCounts.tail]; omega)

theorem walkPositions_grade (depth : ℕ) :
    ∀ fuel need, 𝓖.P (walkPositions ops depth fuel need) (c.positions depth fuel need)
  | 0, _ => 𝓖.pure _
  | _ + 1, 0 => 𝓖.pure _
  | fuel + 1, _ + 1 => 𝓖.of_eq (𝓖.bind h.sample fun _ ↦
      𝓖.bind (walkPositions_grade depth fuel _) fun _ ↦ 𝓖.pure _)
      (by simp [StepCounts.positions])

theorem walkLevel_grade [LawfulMonad n] (sh : LevelShape) :
    𝓖.P (walkLevel ops sh) (c.level sh) :=
  𝓖.of_eq (𝓖.bind (walkFolds_grade h _) fun _ ↦
    𝓖.ite_bind _ (nextScalars_grade h _) (𝓖.pure _) fun _ ↦
    𝓖.ite_bind _ (𝓖.pure _) (𝓖.map h.nextRoot _) fun _ ↦
    𝓖.ite_bind _ (𝓖.pure _) (samples_grade h _) fun _ ↦
    𝓖.ite_bind _ (𝓖.pure _) h.nextScalar fun _ ↦
    𝓖.ite_bind _ (𝓖.pure _) (nextScalars_grade h _) fun _ ↦
    𝓖.bind (h.checkPow _) fun _ ↦ 𝓖.bind (walkPositions_grade h _ _ _) fun _ ↦
    𝓖.bind h.sample fun _ ↦ 𝓖.bind (nextScalars_grade h _) fun _ ↦
    𝓖.ite_bind _ (walkTail_grade h _) (𝓖.pure _) fun _ ↦ 𝓖.pure _)
    (by simp only [StepCounts.level]; split <;> omega)

theorem walkLevels_grade [LawfulMonad n] :
    ∀ shs, 𝓖.P (walkLevels ops shs) (c.levels shs)
  | [] => 𝓖.pure _
  | sh :: shs => 𝓖.of_eq (𝓖.bind (walkLevel_grade h sh) fun _ ↦
      𝓖.bind (walkLevels_grade shs) fun _ ↦ 𝓖.pure _) (by simp [StepCounts.levels])

theorem walkWhir_grade [LawfulMonad n] (shs : List LevelShape) :
    𝓖.P (walkWhir ops shs) (c.whir shs) :=
  𝓖.of_eq (𝓖.bind (nextScalars_grade h 2) fun _ ↦ 𝓖.bind (walkLevels_grade h shs) fun _ ↦
    𝓖.pure _) (by simp [StepCounts.whir])

/-- **The chain walk, counted**: on a record of primitives each with its count, the chain walk
has the count `StepCounts.chain`. -/
theorem walkChain_grade [LawfulMonad n] (prog : Program) (s : Sizes) (input : PublicInput)
    (shs : List LevelShape) : 𝓖.P (walkChain ops prog s input shs) (c.chain prog s input shs) :=
  𝓖.of_eq (𝓖.bind (walkSetup_grade h) fun _ ↦ 𝓖.bind (walkBus_grade h _ _) fun _ ↦
    𝓖.bind (walkTables_grade h _ _) fun _ ↦ 𝓖.bind (walkPub_grade h _) fun _ ↦
    𝓖.bind (walkFlock_grade h _) fun _ ↦ 𝓖.bind h.sample fun _ ↦
    𝓖.bind (walkWhir_grade h shs) fun ⟨_, _⟩ ↦ 𝓖.pure _) (by simp only [StepCounts.chain]; ring)

end Verify

end

end LeanerVM.Protocol
