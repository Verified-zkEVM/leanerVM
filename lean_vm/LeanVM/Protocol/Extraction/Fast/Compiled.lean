module

public import LeanVM.Protocol.Extraction.Fast.AfterRoot
public import LeanVM.Protocol.Extraction.Fast.RunVec
public import LeanVM.Protocol.Extraction.Fast.Transcript
public import LeanVM.Protocol.Extraction.Fast.DecodeAdmissible

/-!
# The extractor the cost machine runs

`extractorTop prog input qs π`: the statement's `transcriptExtractor` on the transcript's
permutation queries `qs` (the machine's input carries them, `Cost/Encoding.lean`), assembled from
the proved-equal fast pieces: the root without the verifier's free monad (`afterRootDirect`), the
replay and the preimages in sorted maps (`transcriptIndex`), the committed leaves through the
index (`subtreeLeavesWith`), the candidate run on a memory vector with its tables built once
(`candidateRunner`), and the fast decoder and fast path (`fastStacksFast`: the word's columns
reversed once, `laneTable`).

The decoder is `decodeStacksDistinct` (`Fast/DecodeAdmissible.lean`): the lanes by `gsRunDistinct`
only, with no branch to the full decoder. The replay returns only admissible layouts
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

/-- **The extractor the cost machine runs**, on the transcript's permutation queries. -/
@[expose] def extractorTop (prog : Program) (input : PublicInput)
    (qs : List (PermutationQuery KeccakState × KeccakState)) (π : Proof) :
    Option (Execution prog) := do
  let ((layout, logInverseRate), state) ← afterRootDirect (bytecodeWords prog) π
  let (root, height, width) ← state.roots.head?
  let idx := transcriptIndex qs (max 64 (8 * width))
  let leaves := subtreeLeavesWith (preimageIn idx) width height root
  let word := leafAt leaves height width
  let execution := candidateRunner prog input layout
  (fastStacksFast layout.stackLog logInverseRate word).findSome? execution <|>
    (decodeStacksDistinct layout.stackLog logInverseRate word).findSome? execution

/-- `extractorTop` with `decodeStacksFast` (whose lanes keep the full decoder's branch). -/
@[expose] def extractorTopFull (prog : Program) (input : PublicInput)
    (qs : List (PermutationQuery KeccakState × KeccakState)) (π : Proof) :
    Option (Execution prog) := do
  let ((layout, logInverseRate), state) ← afterRootDirect (bytecodeWords prog) π
  let (root, height, width) ← state.roots.head?
  let idx := transcriptIndex qs (max 64 (8 * width))
  let leaves := subtreeLeavesWith (preimageIn idx) width height root
  let word := leafAt leaves height width
  let execution := candidateRunner prog input layout
  (fastStacksFast layout.stackLog logInverseRate word).findSome? execution <|>
    (decodeStacksFast layout.stackLog logInverseRate word).findSome? execution

/-- The replay's layouts are admissible (`admissible_of_afterRootDirect`), where the decoder
without the full decoder is the fast one (`decodeStacksDistinct_eq`). -/
theorem extractorTop_eq_full (prog : Program) (input : PublicInput)
    (qs : List (PermutationQuery KeccakState × KeccakState)) (π : Proof) :
    extractorTop prog input qs π = extractorTopFull prog input qs π := by
  unfold extractorTop extractorTopFull
  refine Option.bind_congr fun r h ↦ ?_
  obtain ⟨⟨layout, R⟩, st⟩ := r
  simp only [decodeStacksDistinct_eq (admissible_of_afterRootDirect h)]

/-- **The extractor the cost machine runs is the statement's.** -/
theorem extractorTop_eq (prog : Program) (input : PublicInput) (T : OracleQueryLog) (π : Proof) :
    extractorTop prog input (permutationQueries T) π = transcriptExtractor prog input T π := by
  rw [extractorTop_eq_full, ← transcriptExtractorFast_eq, transcriptExtractorFast, extractorTopFull,
    extractWith, afterRootDirect_eq_afterRoot]
  simp only [candidateRunner_eq, fastStacksFast_eq]

end

end LeanVM.Extraction.Fast
