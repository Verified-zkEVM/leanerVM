module

public import Statement.Extractor
public import LeanVM.Protocol.Extraction.Fast.RothRuckenstein
public import LeanVM.Protocol.Extraction.Lane

/-!
# The extractor, fast

`extractFast` is the statement's extractor (`LeanVM.Extraction.extract`, `Statement/Extractor.lean`)
with a faster lane decoder, `gsLaneAtFast`:

* Roth–Ruckenstein's substitution a Taylor shift (`Fast/RothRuckenstein.lean`): `gsContextFast` is
  `gsContext` with `rothRuckensteinRootContextFast`;
* without the final root check where the parameters make it redundant (`gsRunNoCheck`,
  `checkRedundant`: at most `2^64` columns and `W < m·(n − radius)`, as at every shape the
  statement decodes, `W = m·A − 1`, `radius = n − A`).

The definitions from the lane decoder up to the extractor are copied with it (a `@[csimp]` lemma
acts where code is compiled, and the statement's definitions are compiled in `Statement/`), each
proved equal to its original: **`extractFast_eq`**: `extractFast = extract`.
-/

namespace LeanVM.Extraction.Fast

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Parameters.Whir LeanVM.Protocol.KeccakHash LeanVM.Extraction
open CompPoly CompPoly.GuruswamiSudan

public section

/-- The list decoder's interpolation (`gsContext`'s): Lee–O'Sullivan, Mulders–Storjohann. -/
@[expose] def interpContext : GSInterpContext K :=
  LeeOSullivan.leeOSullivanInterpContext CPolynomial.VanishingPolynomialContext.direct
    (CPolynomial.BatchEvalContext.horner K)
    (PolynomialMatrix.muldersStorjohannFastReducerContext K)

/-- The list decoder's context with Roth–Ruckenstein's fast substitution. -/
@[expose] def gsContextFast : GSFilteredCoreContext K :=
  filteredCoreContextOfInterpRootContexts interpContext (rothRuckensteinRootContextFast fieldRootCtx)

theorem gsContextFast_eq : gsContextFast = gsContext := by
  rw [gsContextFast, rothRuckensteinRootContextFast_eq, gsContext, interpContext]

/-! ## The final root check, dropped

Roth–Ruckenstein's prefixes are filtered twice: by `isRootYDegreeLtBool` (degree `< k` and
`Q(X, p(X)) = 0`, a Horner evaluation of `Q` at `p`: about `ℓ·(W + ℓ·k)²` operations per
candidate), then by the distance filter (`passesCandidateDistance`: at most `radius` mismatches).
When `W < m·(n − radius)` and the points are distinct, a candidate of degree `< k` that passes the
distance filter matches on at least `n − radius` points, so `Q(X, p(X)) = 0` already
(`composeY_eq_zero_of_enough_matching_multiplicity_points`, CompPoly's Guruswami–Sudan lemma):
the root check is redundant, and `gsRunNoCheck` keeps the degree check and the distance filter. -/

/-- **The list decoder without the final root check**: the fast Roth–Ruckenstein prefixes of
the interpolated `Q` of degree `< k` that pass the distance filter. -/
@[expose] def gsRunNoCheck (points : Array (K × K)) (params : GSInterpParams) (radius : ℕ) :
    Array (CPolynomial K) :=
  match interpContext.interpolate points params with
  | none => #[]
  | some Q => (prefixesWithFuelFast fieldRootCtx params.messageDegree Q 0 default).filter fun p ↦
      degreeLtBool p params.messageDegree && passesCandidateDistance points radius p

theorem candidateMismatchCount_add_matchingPointCount (points : Array (K × K))
    (p : CPolynomial K) :
    candidateMismatchCount points p + matchingPointCount points p = points.size := by
  rw [candidateMismatchCount, matchingPointCount, ← Array.foldl_toList, ← Array.foldl_toList,
    ← Array.length_toList]
  generalize points.toList = l
  have h : ∀ a b : ℕ,
      l.foldl (fun count point ↦
          if CPolynomial.eval point.1 p == point.2 then count else count + 1) a +
        l.foldl (fun count point ↦
          if CPolynomial.eval point.1 p == point.2 then count + 1 else count) b =
        a + b + l.length := by
    induction l with
    | nil => simp
    | cons q l ih =>
      intro a b
      simp only [List.foldl_cons, List.length_cons]
      split <;> rw [ih] <;> omega
  simpa using h 0 0

theorem gsRunNoCheck_eq (points : Array (K × K)) (params : GSInterpParams) (radius : ℕ)
    (hdist : DistinctXCoordinates points)
    (hW : params.weightedDegreeBound < params.multiplicity * (points.size - radius)) :
    gsRunNoCheck points params radius =
      gsFilteredCore points interpContext (rothRuckensteinRootContext K fieldRootCtx) params
        radius := by
  rw [gsRunNoCheck, gsFilteredCore, gsCore]
  cases hQ : interpContext.interpolate points params with
  | none => rfl
  | some Q =>
    have hvalid := interpContext.sound points params Q hQ
    simp only [rothRuckensteinRootContext, rothRuckensteinRootsYDegreeLt,
      transformedRothRuckensteinRootsYDegreeLt, transformedRothRuckensteinRootPrefixes,
      prefixesWithFuelFast_eq, Array.filter_filter]
    rw [← Array.toList_inj, Array.toList_filter, Array.toList_filter]
    refine List.filter_congr fun p _ ↦ ?_
    simp only [isRootYDegreeLtBool]
    by_cases hd : degreeLtBool p params.messageDegree = true
    · by_cases hp : passesCandidateDistance points radius p = true
      · have hmis : candidateMismatchCount points p ≤ radius := by
          simpa [passesCandidateDistance] using hp
        have hsum := candidateMismatchCount_add_matchingPointCount points p
        have hmatches : params.weightedDegreeBound <
            params.multiplicity * matchingPointCount points p :=
          lt_of_lt_of_le hW (Nat.mul_le_mul_left _ (by omega))
        have hroot := composeYHorner_eq_zero_of_composeY
          (composeY_eq_zero_of_enough_matching_multiplicity_points hvalid
            (degreeLt_of_degreeLtBool hd) hdist hmatches)
        simp [hd, hp, hroot]
      · simp [hp]
    · simp [hd]

/-- The lane decoder's points are distinct below `2^64` columns. -/
theorem distinct_lanePoints (n : ℕ) (hn : n ≤ 2 ^ 64) (W : ℕ → List K) (u : ℕ) :
    DistinctXCoordinates (lanePoints n W u) := by
  rw [DistinctXCoordinates, lanePoints, Array.toList_ofFn, List.map_ofFn]
  exact List.nodup_ofFn.2 (LaneProofs.domainEmb n hn).injective

/-- Whether the final root check is redundant at a shape: at most `2^64` columns, and
`W < m·(n − radius)`. -/
@[expose] def checkRedundant (κ R : ℕ) (params : GSExecParams) : Bool :=
  decide (κ + R ≤ 64) &&
    decide (params.interp.weightedDegreeBound <
      params.interp.multiplicity * (2 ^ (κ + R) - params.radius))

/-- `gsLaneAt`, fast: without the final root check where it is redundant, and with the fast
substitution. -/
@[expose] def gsLaneAtFast (κ R A : ℕ) (W : ℕ → List K) (u : ℕ) : Array (CPolynomial K) :=
  let params := gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A
  let points := lanePoints (2 ^ (κ + R)) W u
  if checkRedundant κ R params then gsRunNoCheck points params.interp params.radius
  else GuruswamiSudan.decodeWithParams gsContextFast params ⟨points⟩

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
  split
  · rename_i h
    simp only [checkRedundant, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [decodeWithParams, gsRunNoCheck_eq _ _ _
      (distinct_lanePoints _ (Nat.pow_le_pow_right (by norm_num) h.1) W u)
      (by simpa [lanePoints] using h.2)]
    rfl
  · rfl

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
