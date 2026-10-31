module

public import Statement.Extractor
public import LeanVM.Protocol.Extraction.Fast.RothRuckenstein

/-!
# The extractor, fast

`extractFast` is the statement's extractor (`LeanVM.Extraction.extract`, `Statement/Extractor.lean`)
with the list decoder's Roth–Ruckenstein step on the fast substitution
(`Fast/RothRuckenstein.lean`): `gsContextFast` is `gsContext` with
`rothRuckensteinRootContextFast` for `rothRuckensteinRootContext`, and the definitions from the
lane decoder up to the extractor are copied with it. **`extractFast_eq`**: `extractFast = extract`.

A `@[csimp]` lemma acts where code is compiled, and the statement's definitions are compiled in
`Statement/`, so the chain is copied, not redirected: each copy is its original's text with the
fast context, proved equal by rewriting with `gsContextFast_eq`.
-/

namespace LeanVM.Extraction.Fast

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Parameters.Whir LeanVM.Protocol.KeccakHash LeanVM.Extraction
open CompPoly CompPoly.GuruswamiSudan

public section

/-- The list decoder's context with Roth–Ruckenstein's fast substitution. -/
@[expose] def gsContextFast : GSFilteredCoreContext K :=
  filteredCoreContextOfInterpRootContexts
    (LeeOSullivan.leeOSullivanInterpContext CPolynomial.VanishingPolynomialContext.direct
      (CPolynomial.BatchEvalContext.horner K)
      (PolynomialMatrix.muldersStorjohannFastReducerContext K))
    (rothRuckensteinRootContextFast fieldRootCtx)

theorem gsContextFast_eq : gsContextFast = gsContext := by
  rw [gsContextFast, rothRuckensteinRootContextFast_eq, gsContext]

/-- `gsLaneAt`, fast. -/
@[expose] def gsLaneAtFast (κ R A : ℕ) (W : ℕ → List K) (u : ℕ) : Array (CPolynomial K) :=
  GuruswamiSudan.decodeWithParams gsContextFast (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A)
    ⟨lanePoints (2 ^ (κ + R)) W u⟩

/-- `laneListAt`, fast. -/
@[expose] def laneListAtFast (κ R A : ℕ) (W : ℕ → List K) (u : ℕ) : List (Array K) :=
  ((gsLaneAtFast κ R A W u).toList.map (toNovel κ)).dedup

/-- `laneEncodedAt`, fast. -/
@[expose] def laneEncodedAtFast (κ R A : ℕ) (W : ℕ → List K) (u : ℕ) : List (Array K × Array K) :=
  (laneListAtFast κ R A W u).map fun c ↦ (c, novelFwd κ R c)

/-- `pruneUpTo`, fast. -/
@[expose] def pruneUpToFast (κ R A : ℕ) (W : ℕ → List K) (U : ℕ) :
    List (List (Array K) × List ℕ) :=
  (List.range U).foldl
    (fun st u ↦
      if st.isEmpty then [] else pruneStep A (laneSymbol W u) (laneEncodedAtFast κ R A W u) st)
    [([], List.range (2 ^ (κ + R)))]

/-- `decodeStacksAt`, fast. -/
@[expose] def decodeStacksAtFast (μ R A : ℕ) (W : ℕ → List K) : List (Vector K (2 ^ μ)) :=
  (pruneUpToFast (μ - initialFold) R A W (2 ^ initialFold)).map fun s ↦ stackOf μ s.1

/-- `decodeStacks`, fast. -/
@[expose] def decodeStacksFast (μ R : ℕ) (W : ℕ → List K) : List (Vector K (2 ^ μ)) :=
  decodeStacksAtFast μ R (johnsonThreshold μ R) W

/-- **The extractor, fast**: `extract` with `decodeStacksFast`. -/
@[expose] def extractFast (prog : Program) (input : PublicInput) (bytecode : List K)
    (answers : Bytes → Option Digest) (keys : List Bytes) (π : Proof) :
    Option (Execution prog) := do
  let ((layout, logInverseRate), state) ← afterRoot bytecode π
  let (root, height, width) ← state.roots.head?
  let leaves := committedLeaves answers keys root height width
  let word := leafAt leaves height width
  let memIdx := powIndex layout.logMemory
  let codeIdx := powIndex prog.logSize
  let execution := candidateExecutionIn memIdx codeIdx prog input layout
  (fastStacks layout.stackLog logInverseRate word).findSome? execution <|>
    (decodeStacksFast layout.stackLog logInverseRate word).findSome? execution

theorem gsLaneAtFast_eq : gsLaneAtFast = gsLaneAt := by
  funext κ R A W u
  rw [gsLaneAtFast, gsContextFast_eq, gsLaneAt]

theorem decodeStacksAtFast_eq : decodeStacksAtFast = decodeStacksAt := by
  funext μ R A W
  simp only [decodeStacksAtFast, pruneUpToFast, laneEncodedAtFast, laneListAtFast, gsLaneAtFast_eq,
    decodeStacksAt, pruneUpTo, laneEncodedAt, laneListAt]

theorem decodeStacksFast_eq : decodeStacksFast = decodeStacks := by
  funext μ R W
  rw [decodeStacksFast, decodeStacksAtFast_eq, decodeStacks]

/-- **The fast extractor is the statement's.** -/
theorem extractFast_eq : extractFast = extract := by
  funext prog input bytecode answers keys π
  simp only [extractFast, decodeStacksFast_eq, extract]

end

end LeanVM.Extraction.Fast
