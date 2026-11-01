module

public import Statement.Extractor
public import LeanVM.Protocol.Extraction.Fast.RothRuckenstein
public import LeanVM.Protocol.Extraction.Lane
public import LeanVM.Protocol.Extraction.Fast.Karatsuba
public import LeanVM.Protocol.Extraction.Fast.Truncate
public import LeanVM.Protocol.Extraction.Fast.Address
public import LeanVM.Protocol.Extraction.Fast.Order
public import CompPoly.Bivariate.GuruswamiSudan.Interpolation.ApproximantBasis.Correctness
public import CompPoly.LinearAlgebra.PolynomialMatrix.Approximant

/-!
# The extractor, fast

`extractFast` is the statement's extractor (`LeanVM.Extraction.extract`, `Statement/Extractor.lean`)
with a faster lane decoder, `gsLaneAtFast`:

* Roth–Ruckenstein's substitution a Taylor shift (`Fast/RothRuckenstein.lean`): `gsContextFast` is
  `gsContext` with `rothRuckensteinRootContextFast`;
* without the final root check where the parameters make it redundant (`gsRunNoCheck`,
  `checkRedundant`: at most `2^64` columns and `W < m·(n − radius)`, as at every shape the
  statement decodes, `W = m·A − 1`, `radius = n − A`);
* the interpolation: Lee–O'Sullivan's (`interpContext`) at every shape; CompPoly's
  approximant-basis interpolation on Karatsuba's products, `approxInterpContext`, is kept, proved,
  not used. Another interpolation may return another polynomial, so another list in another
  order: what the list holds does not depend on it (`mem_gsRunNoCheck`: the polynomials of
  degree `< k` within the radius), and the statement sorts each lane's list (`laneListAt`), so the
  sorted lists are equal (`laneListAtFast_eq`).

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
the interpolated `Q` (truncated, `prefixesTruncD`) of degree `< k` that pass the distance
filter. -/
@[expose] def gsRunNoCheck (I : GSInterpContext K) (points : Array (K × K))
    (params : GSInterpParams) (radius : ℕ) : Array (CPolynomial K) :=
  match I.interpolate points params with
  | none => #[]
  | some Q =>
    (prefixesTruncD fieldRootCtx params.messageDegree
        (CBivariate.truncateX Q params.messageDegree) params.messageDegree Q [] 0
        default).filter fun p ↦
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

theorem gsRunNoCheck_eq (I : GSInterpContext K) (points : Array (K × K))
    (params : GSInterpParams) (radius : ℕ) (hdist : DistinctXCoordinates points)
    (hW : params.weightedDegreeBound < params.multiplicity * (points.size - radius)) :
    gsRunNoCheck I points params radius =
      gsFilteredCore points I (rothRuckensteinRootContext K fieldRootCtx) params radius := by
  rw [gsRunNoCheck, gsFilteredCore, gsCore]
  cases hQ : I.interpolate points params with
  | none => rfl
  | some Q =>
    have hvalid := I.sound points params Q hQ
    dsimp only
    rw [prefixesTruncD_eq, prefixesTrunc_eq fieldRootCtx params.messageDegree Q params.messageDegree
      (fun _ ↦ replayPath Q []) 0 default rfl]
    simp only [replayPath, List.foldl_nil]
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

/-- **What the run lists does not depend on the interpolation**: the polynomials of degree `< k`
within the radius, if the points have an interpolation polynomial. -/
theorem mem_gsRunNoCheck (I : GSInterpContext K) (points : Array (K × K))
    (params : GSInterpParams) (radius : ℕ) (hdist : DistinctXCoordinates points)
    (hW : params.weightedDegreeBound < params.multiplicity * (points.size - radius))
    (p : CPolynomial K) :
    p ∈ (gsRunNoCheck I points params radius).toList ↔
      (∃ Q, ValidInterpolationWitness points params Q) ∧ degreeLt p params.messageDegree ∧
        candidateMismatchCount points p ≤ radius := by
  rw [gsRunNoCheck_eq I points params radius hdist hW]
  let C := filteredCoreContextOfInterpRootContexts I (rothRuckensteinRootContext K fieldRootCtx)
  change p ∈ (C.run points params radius).toList ↔ _
  constructor
  · intro h
    obtain ⟨Q, hv, hd, _, hm⟩ := C.sound h
    exact ⟨⟨Q, hv⟩, hd, hm⟩
  · rintro ⟨hex, hd, hm⟩
    have hsum := candidateMismatchCount_add_matchingPointCount points p
    exact C.complete hex hdist hd (lt_of_lt_of_le hW (Nat.mul_le_mul_left _ (by omega)))
      (by simpa [passesCandidateDistance] using hm)

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

/-- **The fast interpolation** (Chowdhury, Jeannerod, Neiger, Schost, Villard): CompPoly's
approximant-basis interpolation (PM-basis approximant bases solving the Guruswami–Sudan modular
equations), proved sound and complete, on Karatsuba's products and remainders. -/
@[expose] def approxInterpContext : GSInterpContext K :=
  ApproximantBasis.approximantBasisInterpContext CPolynomial.VanishingPolynomialContext.direct
    (CPolynomial.BatchEvalContext.horner K)
    (PolynomialMatrix.Approximant.modularSolutionBasisContextViaPMBasis karatsubaMulContext
      karatsubaModContext
      (PolynomialMatrix.Approximant.kernelLeafPMBasisContext karatsubaMulContext 8))

/-- `gsLaneAt`, fast: without the final root check where it is redundant, and with the fast
substitution. The interpolation is Lee–O'Sullivan's (Mulders–Storjohann) at every shape:
`approxInterpContext` is measured slower at every runnable size, and its code admits no cost bound
below Mulders–Storjohann's (the kernel leaf can raise degrees, the low products recompute each
product per coefficient). A choice of speed only: what the lane lists hold does not depend on it
(`mem_gsRunNoCheck`). -/
@[expose] def gsLaneAtFast (κ R A : ℕ) (W : ℕ → List K) (u : ℕ) : Array (CPolynomial K) :=
  let params := gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A
  let points := lanePoints (2 ^ (κ + R)) W u
  if checkRedundant κ R params then gsRunNoCheck interpContext points params.interp params.radius
  else GuruswamiSudan.decodeWithParams gsContextFast params ⟨points⟩

/-- `laneListAt`, fast. -/
@[expose] def laneListAtFast (κ R A : ℕ) (W : ℕ → List K) (u : ℕ) : List (Array K) :=
  (((gsLaneAtFast κ R A W u).toList.map (toNovel κ)).dedup).mergeSort coeffsLE

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
  let execution := candidateExecutionFast prog input layout
  (fastStacks layout.stackLog logInverseRate word).findSome? execution <|>
    (decodeStacksFast layout.stackLog logInverseRate word).findSome? execution

/-- **The lane decoder lists the same polynomials, fast.** -/
theorem mem_gsLaneAtFast (κ R A : ℕ) (W : ℕ → List K) (u : ℕ) (p : CPolynomial K) :
    p ∈ (gsLaneAtFast κ R A W u).toList ↔ p ∈ (gsLaneAt κ R A W u).toList := by
  rw [gsLaneAtFast, gsLaneAt, ← gsContextFast_eq]
  split
  · rename_i h
    simp only [checkRedundant, Bool.and_eq_true, decide_eq_true_eq] at h
    have hd := distinct_lanePoints _ (Nat.pow_le_pow_right (by norm_num) h.1) W u
    have hW : (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).interp.weightedDegreeBound <
        (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).interp.multiplicity *
          ((lanePoints (2 ^ (κ + R)) W u).size - (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).radius) := by
      simpa [lanePoints] using h.2
    rw [decodeWithParams, gsContextFast_eq,
      show gsContext.run _ _ _ = gsRunNoCheck interpContext _ _ _ from
        (gsRunNoCheck_eq _ _ _ _ hd hW).symm,
      mem_gsRunNoCheck _ _ _ _ hd hW]
  · rfl

theorem laneListAtFast_eq : laneListAtFast = laneListAt := by
  funext κ R A W u
  rw [laneListAtFast, laneListAt]
  refine mergeSort_dedup_eq fun x ↦ ?_
  simp only [List.mem_map, mem_gsLaneAtFast]

theorem decodeStacksAtFast_eq : decodeStacksAtFast = decodeStacksAt := by
  funext μ R A W
  simp only [decodeStacksAtFast, pruneUpToFast, laneEncodedAtFast, laneListAtFast_eq,
    decodeStacksAt, pruneUpTo, laneEncodedAt]

theorem decodeStacksFast_eq : decodeStacksFast = decodeStacks := by
  funext μ R W
  rw [decodeStacksFast, decodeStacksAtFast_eq, decodeStacks]

/-- **The fast extractor is the statement's.** -/
theorem extractFast_eq : extractFast = extract := by
  funext prog input bytecode answers keys π
  simp only [extractFast, decodeStacksFast_eq, candidateExecutionFast_eq, extract]

end

end LeanVM.Extraction.Fast
