module

public import LeanVM.Protocol.Extraction.Fast.AfterRoot
public import LeanVM.Protocol.Extraction.Fast.RunVec
public import LeanVM.Protocol.Extraction.Fast.Transcript
public import LeanVM.Protocol.Extraction.Fast.DecodeAdmissible

/-!
# The extractor the cost machine runs

`extractorTop prog input qs π`: the statement's `transcriptExtractor` on the transcript's
permutation queries `qs` (the machine's input carries them, `Cost/Encoding.lean`), assembled from
the proved-equal fast pieces: the root without the verifier's free monad and with the layout cut to
the fields the extractor reads (`afterRootLite`: no bus blocks, no bytecode copy), the
replay and the preimages in sorted maps (`transcriptIndex`), the committed leaves through the
index (`subtreeLeavesWith`), the candidate run on a memory vector with its tables built once
(`candidateRunner`), and the fast decoder and fast path (`fastStacksFast`: the word's columns
reversed once, `laneTable`).

The decoder is `decodeStacksDistinct` (`Fast/DecodeAdmissible.lean`): the lanes by
`gsRunDistinctNF` only (`gsRunDistinct` with Roth–Ruckenstein's fallback removed,
`Fast/TruncNoFallback.lean`), with no branch to the full decoder. The replay returns only admissible layouts
(`admissible_of_afterRootDirect`), and at admissible shapes it is `decodeStacksFast`
(`decodeStacksDistinct_eq`): `extractorTop_eq_full`, `extractorTop` is `extractorTopFull`, the same
with `decodeStacksFast`.

* **`extractorTop_eq`**: `extractorTop prog input (permutationQueries T) π =
  transcriptExtractor prog input T π`.
-/

namespace LeanVM.Extraction.Fast

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash LeanVM.Extraction LeanVM Common

public section

/-- The candidate runs: the tables built once, then the fast path's stacks, then (only if none
gives an execution) the decoder's, `slow ()`. A function of its own so that the extractor passes it
the stacks as values: the compiled extractor's proof, with the tables and the fast path's stacks in
the same call, does not fit the kernel's check (the main session's log, §11). -/
@[expose] def runBoth (prog : Program) (input : PublicInput) (layout : LayoutLite)
    (fastSts : List (Vector K (2 ^ layout.stackLog)))
    (slow : Unit → List (Vector K (2 ^ layout.stackLog))) : Option (Execution prog) :=
  let tabs := runnerTables prog layout
  fastSts.findSome? (runWithTables tabs prog input layout) <|>
    (slow ()).findSome? (runWithTables tabs prog input layout)

/-- The fast path's stacks from the committed leaves (the word `leafAt leaves h w` built inside:
the extractor passes only data). -/
@[expose] def fastOf (μ R : ℕ) (leaves : Array (List K)) (h w : ℕ) : List (Vector K (2 ^ μ)) :=
  fastStacksFast μ R (leafAt leaves h w)

/-- The decoder's stacks from the committed leaves. -/
@[expose] def decOf (μ R : ℕ) (leaves : Array (List K)) (h w : ℕ) : List (Vector K (2 ^ μ)) :=
  decodeStacksDistinct μ R (leafAt leaves h w)

/-- The committed leaves: the transcript's index, then the subtree under the root. -/
@[expose] def leavesOf (qs : List (PermutationQuery KeccakState × KeccakState)) (w h : ℕ)
    (root : Digest) : Array (List K) :=
  subtreeLeavesWith (preimageIn (transcriptIndex qs (max 64 (8 * w)))) w h root

/-- The candidate runs from the committed leaves: the fast path's stacks, then the decoder's. -/
@[expose] def runFromLeaves (prog : Program) (input : PublicInput) (layout : LayoutLite) (R : ℕ)
    (leaves : Array (List K)) (h w : ℕ) : Option (Execution prog) :=
  runBoth prog input layout (fastOf layout.stackLog R leaves h w)
    fun _ ↦ decOf layout.stackLog R leaves h w

/-- The runs at a root `t = (root, height, width)`: the committed leaves, then the candidate runs. -/
@[expose] def stageT (prog : Program) (input : PublicInput) (layout : LayoutLite) (R : ℕ)
    (qs : List (PermutationQuery KeccakState × KeccakState)) (t : Digest × ℕ × ℕ) :
    Option (Execution prog) :=
  runFromLeaves prog input layout R (leavesOf qs t.2.2 t.2.1 t.1) t.2.1 t.2.2

/-- After the replay: the first root, then `stageT` at it. -/
@[expose] def afterRootStage (prog : Program) (input : PublicInput)
    (qs : List (PermutationQuery KeccakState × KeccakState))
    (r : (LayoutLite × ℕ) × ProgState) : Option (Execution prog) :=
  r.2.roots.head?.bind (stageT prog input r.1.1 r.1.2 qs)

/-- **The extractor the cost machine runs**, on the transcript's permutation queries. Each step a
function of its own, passed by partial application, the tuples read by projections: with a lambda
or a match around a heavy call (or the runs' pieces inline) at this level, the compiled extractor's
proof does not fit the kernel's check (the main session's log, §11). -/
@[expose] def extractorTop (prog : Program) (input : PublicInput)
    (qs : List (PermutationQuery KeccakState × KeccakState)) (π : Proof) :
    Option (Execution prog) :=
  (afterRootLite (bytecodeWords prog) π).bind (afterRootStage prog input qs)

/-- `extractorTop` on the full layout (`afterRootDirect`), with `decodeStacksFast` (whose lanes keep
the full decoder's branch). -/
@[expose] def extractorTopFull (prog : Program) (input : PublicInput)
    (qs : List (PermutationQuery KeccakState × KeccakState)) (π : Proof) :
    Option (Execution prog) := do
  let ((layout, logInverseRate), state) ← afterRootDirect (bytecodeWords prog) π
  let (root, height, width) ← state.roots.head?
  let idx := transcriptIndex qs (max 64 (8 * width))
  let leaves := subtreeLeavesWith (preimageIn idx) width height root
  let word := leafAt leaves height width
  let execution := candidateRunner prog input (layoutLite layout)
  (fastStacksFast layout.stackLog logInverseRate word).findSome? execution <|>
    (decodeStacksFast layout.stackLog logInverseRate word).findSome? execution

/-- `afterRootLite` is `afterRootDirect`, the layout cut to the fields the extractor reads
(`afterRootLite_eq`); the replay's layouts are admissible (`admissible_of_afterRootLite`), where
the decoder without the full decoder is the fast one (`decodeStacksDistinct_eq`). -/
theorem extractorTop_eq_full (prog : Program) (input : PublicInput)
    (qs : List (PermutationQuery KeccakState × KeccakState)) (π : Proof) :
    extractorTop prog input qs π = extractorTopFull prog input qs π := by
  unfold extractorTop extractorTopFull afterRootStage stageT runFromLeaves leavesOf runBoth fastOf decOf
  simp only [Option.bind_eq_bind]
  rw [afterRootLite_eq, ← afterRootDirect_eq, Option.bind_map]
  refine Option.bind_congr fun r h ↦ ?_
  obtain ⟨⟨layout, R⟩, st⟩ := r
  have hadm : Whir.Admissible layout.stackLog R := admissible_of_afterRootDirect h
  simp only [Function.comp_apply, liteResult]
  simp only [layoutLite_stackLog, decodeStacksDistinct_eq hadm, runWithTables_runnerTables]

/-- **The extractor the cost machine runs is the statement's.** -/
theorem extractorTop_eq (prog : Program) (input : PublicInput) (T : OracleQueryLog) (π : Proof) :
    extractorTop prog input (permutationQueries T) π = transcriptExtractor prog input T π := by
  rw [extractorTop_eq_full, ← transcriptExtractorFast_eq, transcriptExtractorFast, extractorTopFull,
    extractWith, afterRootDirect_eq_afterRoot]
  simp only [candidateRunner_eq, fastStacksFast_eq]
  rfl

end

end LeanVM.Extraction.Fast
