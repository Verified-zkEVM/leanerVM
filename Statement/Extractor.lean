module

public import Statement.LeanIsa
public import Statement.LeanVmVerifier
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.Floor.Ring

/-!
# The knowledge extractor

The fixed straight-line extractor of `KnowledgeSoundness` (`Statement/LeanVm.lean`): from the
announced sizes, the stack's Merkle root and the Keccak-256 evaluations it is given, the halting
run of the memory image of a stack in the Johnson list of the committed word.
-/

section

/-!
## The knowledge extractor

Knowledge soundness (`KnowledgeSoundness`, `LeanVm.lean`) is stated for the extractor
defined here, `extract`, through `LeanVM.extractorRpm` (`LeanVm.lean`), which applies it to the
program's bytecode and to the Keccak-256 evaluations of the adversary's transcript of queries to
the random permutation (`transcriptHashes`: the byte strings whose whole sponge path the
adversary queried, with their digests). It is straight-line: it reads the proof and those
evaluations (a partial function from byte strings to digests, `answers`), and nothing else. It
neither queries the permutation, nor sees the verifier's queries, nor runs the adversary again.
It does four things.

1. **The announced sizes and the stack's root** (`afterRoot`). It reads them off the proof as the
   verifier's first two steps do, `verify_execution` steps 1 and 2 (`verifier.py:1469-1480`):
   the announced sizes and the layout they build (`readSizes`), then the stack's Merkle root and
   the shape level 0 of the opening commits it at (`commitStack`). These steps read scalars and
   absorb them into the Fiat-Shamir sponge; what they read does not depend on the sponge, so the
   extractor does not compute it (it runs them with every hash and permutation answered by a
   constant, `fun _ ↦ default`).
2. **The committed word** (`commitment`, `committedWord`). It inverts the Merkle tree under the
   root through the adversary's answers: leaf `v` of the word is the leaf of an opening at
   position `v` that climbs to the root through the adversary's queries (`openOne`, the check of
   `Transcript.merkle`, `verifier.py:433-445`), if there is one, and the zero row otherwise.
   Without a collision among the answers, at most one leaf climbs to the root at a position.
3. **The candidates** (`Candidates`). Level 0 commits the stack (the committed columns, stacked,
   `2^μ` words of `K`) in `2^6` lanes: lane `u` is the stack's block `u`, its cells
   `j + 2^(μ−6)·u` for `j < 2^(μ−6)`, read as coefficients in the novel polynomial basis `X_j`,
   and column `v` of the word is the leaf holding the values of the `64` lanes at the domain point
   `x_v = K.ofBits v`, in reverse order (`verifier.py:1165-1166`, `tuple(reversed(row))`): the
   binary Reed–Solomon code of Annex B, §B.2 (`doc/leanvm/body/b-polynomial-commitment-scheme.tex`)
   and the encoder of Annex D, `def:enc` (`doc/leanvm/body/d-novel-basis.tex`). The candidates
   are the stacks whose encoding (`encode`) agrees with the word on at least the Johnson
   threshold of columns (`johnsonThreshold`): the stacks of the Johnson list of the word.
4. **The execution** (`extract`). For a candidate, the memory image its memory columns hold
   (`memoryImage`), run from the initial state `(pcInitial, fpInitial)` until it halts (`haltingRun`). The extractor
   returns such an execution that is a valid execution of the program on the public input, if a
   candidate gives one, and `none` otherwise. The choice among several is classical; it is
   information-theoretic, not an algorithm with a running time.

Every citation `verifier.py:N` is a line of `python-verifier/verifier.py` at leanVM
`94ee12ff6b2a3d42ba8328e22d09443692e4800b`, the commit `LeanVmVerifier.lean` transcribes; the
Annexes are cited at leanVM `127510d14c98ade4e8a97646c44fa7f1ff5e752d`.
-/

namespace LeanVM.Extraction

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Parameters.Whir

@[expose] public section

/-! ### 1. The announced sizes and the stack's root -/

/-- `verify_execution`'s steps 1 and 2 (`verifier.py:1469-1480`): read the announced sizes, then
the stack's root; the layout and the WHIR rate exponent. -/
def announceSizesAndRoot (bytecode : List K) : Prog (Layout × ℕ) := do
  let (layout, logInverseRate) ← readSizes bytecode
  commitStack layout.stackLog logInverseRate
  return (layout, logInverseRate)

/-- The verifier's state after its steps 1 and 2 on the proof `π`: the announced layout and rate
exponent, and the state, whose first root is the stack's. The steps only read scalars, so the
sponge is not computed: every hash and every permutation is taken to be `0`. `none` if the steps
reject. -/
def afterRoot (bytecode : List K) (π : Proof) : Option ((Layout × ℕ) × St) :=
  Id.run (run (m := Id) (fun _ ↦ default) (fun _ ↦ default) (announceSizesAndRoot bytecode)
    ⟨⟨default, []⟩, π.stream, π.openings, []⟩)

/-! ### 2. The committed word -/

open Classical in
/-- The word a Merkle root of `2^height` leaves of `width` words commits to under `answers`:
leaf `v` is the leaf of an opening at position `v` that `openOne` accepts against the root, the
hash being `answers` (its climb reaches the root through answered queries), if there is one (a
classical choice), and `width` zeros otherwise. -/
noncomputable def committedWord (answers : Bytes → Option Digest) (root : Digest)
    (height width : ℕ) : ℕ → List K := fun v ↦
  if h : ∃ o : Opening, openOne answers root height width v o = some true then h.choose.leaf
  else List.replicate width 0

/-- **The commitment a proof announces**: the layout and rate exponent of its announced sizes,
and the word its stack's root (the first root the verifier reads) commits to under `answers`.
`none` if the verifier's steps 1 and 2 reject the proof. -/
noncomputable def commitment (bytecode : List K) (answers : Bytes → Option Digest) (π : Proof) :
    Option (Layout × ℕ × (ℕ → List K)) := do
  let ((layout, logInverseRate), state) ← afterRoot bytecode π
  let (root, height, width) ← state.roots.head?
  return (layout, logInverseRate, committedWord answers root height width)

/-! ### 3. The encoding and the candidates -/

/-- The subspace polynomial `W_i(a) = ∏_{v < 2^i} (a + x_v)`, `x_v = K.ofBits v`: it vanishes
exactly on `U_i = {x_v | v < 2^i}`. -/
def subspacePoly (i : ℕ) (a : K) : K := ∏ v ∈ Finset.range (2 ^ i), (a + K.ofBits v)

/-- The normalized subspace polynomial `Ŵ_i(a) = W_i(a) / W_i(x_{2^i})`. -/
def normSubspacePoly (i : ℕ) (a : K) : K :=
  subspacePoly i a * (subspacePoly i (K.ofBits (2 ^ i)))⁻¹

/-- The novel basis polynomial `X_j(a) = ∏_{i < 64, bit i of j} Ŵ_i(a)`. -/
def novelBasis (j : ℕ) (a : K) : K :=
  ∏ i ∈ Finset.range 64, if j.testBit i then normSubspacePoly i a else 1

/-- **The encoding of a stack** of `2^μ` words, at lane `u` and column `v`: with `κ = μ − 6`,
lane `u` is the message of the `2^κ` cells `j + 2^κ·u`, `j < 2^κ`, as coefficients of the novel
basis, evaluated at the domain point `x_v`: `Σ_j q[j + 2^κ·u] · X_j(x_v)`. -/
def encode {μ : ℕ} (q : Vector K (2 ^ μ)) (u v : ℕ) : K :=
  ∑ j ∈ Finset.range (2 ^ (μ - initialFold)),
    q.getD (j + 2 ^ (μ - initialFold) * u) 0 * novelBasis j (K.ofBits v)

/-- The columns, among the `2^(μ − 6 + R)` of the code at rate `2^-R`, at which the word `W`
agrees with the encoding of `q` on every lane, a leaf holding lane `u` at word `63 − u`. -/
def agreement {μ : ℕ} (R : ℕ) (W : ℕ → List K) (q : Vector K (2 ^ μ)) : Finset ℕ :=
  (Finset.range (2 ^ (μ - initialFold + R))).filter fun v ↦
    ∀ u : Fin (2 ^ initialFold), (W v).reverse.getD u 0 = encode q u v

/-- **The candidates** of a committed word: the stacks of `2^μ` words whose encoding at rate
`2^-R` agrees with the word on at least `A` columns. -/
def Candidates (μ R A : ℕ) (W : ℕ → List K) : Set (Vector K (2 ^ μ)) :=
  {q | A ≤ (agreement R W q).card}

/-- Level 0's Johnson slacks, `η = e / 2^22`: entry `[R − 1][μ − 15]` for the stack size `μ` and
the rate exponent `R`. The soundness proof certifies the opening's `2^-128` per query at these
slacks (chosen offline to balance the fold and query groups); a larger slack means a smaller list
of candidates. The table is copied from the proof's certificates, and the proof checks the copy
against them for every admissible shape (`certOf_e_eq`, `thrOf_eq_johnsonThreshold` in
`LeanVM.Protocol.EndToEnd.Sound`). -/
def johnsonSlack : List (List ℕ) := [
  [34, 45, 55, 68, 85, 107, 134, 189, 237, 298, 375, 471, 663, 832],
  [34, 52, 65, 81, 102, 128, 161, 203, 255, 321, 404, 508, 639, 802],
  [51, 63, 79, 99, 124, 156, 196, 247, 311, 391, 492, 618, 776, 975],
  [49, 61, 77, 96, 121, 152, 191, 240, 303, 381, 478, 602, 756, 949]]

/-- **The Johnson threshold** of level 0 for a stack of `2^μ` words at rate `2^-R`: with
`κ = μ − 6` message variables, `n = 2^(κ+R)` columns and the degree bound `D = 2^κ − 1`, the
agreement `⌈(√(D/n) + η)·n⌉`, the Johnson radius `√(D/n)` plus the slack `η` (`johnsonSlack`).
The table's default `0` is never read: the extractor reaches the threshold only through
`commitment`, which is `none` unless `readSizes` accepted the sizes, so `1 ≤ R ≤ 4` and
`15 ≤ μ ≤ 28`, the table's range. -/
noncomputable def johnsonThreshold (μ R : ℕ) : ℕ :=
  let κ := μ - initialFold
  let n : ℕ := 2 ^ (κ + R)
  let D : ℕ := 2 ^ κ - 1
  let η : ℝ := ((johnsonSlack.getD (R - 1) []).getD (μ - minLogStack) 0 : ℝ) / (2 ^ 22 : ℕ)
  ⌈(√((D : ℝ) / n) + η) * n⌉₊

/-! ### 4. The execution -/

/-- **The memory image of a stack**: `2^logMemory` words, word `i` the three limbs at cell `i` of
the memory columns `MEMORY_0`, `MEMORY_1`, `MEMORY_2` (`verifier.py:687`), each at its placement's
offset on the stack. -/
def memoryImage (layout : Layout) {μ : ℕ} (q : Vector K (2 ^ μ)) : MemImage layout.logMemory :=
  fun i ↦
    let limb (column : ℕ) : K := q.getD ((layout.placement column).index + i) 0
    E.ofLimbs (limb memory0) (limb memory1) (limb memory2)

open Classical in
/-- The execution of `prog` on a memory image: the image, run from the initial state for the least number
of steps after which it halts in the final state `(pcFinal, fpFinal)`; `none` if it never does. -/
noncomputable def haltingRun (prog : Program) {κ : ℕ} (image : MemImage κ) : Option (Trace prog) :=
  if h : ∃ n, Semantics.run prog image n Regs.initial = some (Regs.final prog) then
    some ⟨κ, image, Nat.find h⟩
  else none

open Classical in
/-- **The extractor.** From the adversary's answers and the proof, with the bytecode's words as
the verifier reads them: the commitment the proof announces (the layout, the rate exponent and
the committed word), then an execution which is the halting run of the memory image of a
candidate at the Johnson threshold and a valid execution of `prog` on `input`, if there is one
(a classical choice); `none` otherwise. -/
noncomputable def extract (prog : Program) (input : PublicInput) (bytecode : List K)
    (answers : Bytes → Option Digest) (π : Proof) : Option (Trace prog) :=
  match commitment bytecode answers π with
  | none => none
  | some (layout, logInverseRate, word) =>
    if h : ∃ t : Trace prog, ValidExecution prog input t ∧
        ∃ q ∈ Candidates layout.stackLog logInverseRate
          (johnsonThreshold layout.stackLog logInverseRate) word,
          haltingRun prog (memoryImage layout q) = some t then
      some h.choose
    else none

end
end LeanVM.Extraction

end
