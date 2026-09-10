# Prior work: the leanth formalization of leanVM-a

Before the leanISA redesign, leanVM ("leanVM-a" below: KoalaBear field, three AIR tables, a
logup bus, Poseidon transcript) was formalized end to end in the private repository
`Verified-zkEVM/leanth` (pull request #16, branch `leanth-project`, commit `23929f8c`,
2026-08-20). That work is about 80,000 lines of sorry-free Lean 4 in 35 modules, authored by
Aristotle (Harmonic) with Stefano Rocca and Elias Judin, and was audited adversarially by this
repository's maintainer (branch `scaraven/leanth-project-audit`, 2026-08-24). Because the
repository is private, this file is the public record of what it contains that the
[protocol roadmap](protocol-blueprint.md) can reuse, so that issues and the blueprint cite this
page and never the private tree. Every declaration below is cited at commit `23929f8c` as
`module:line`; `EX` marks the maintainer's later explore branch (`scaraven/proof-system-explore`)
where some of it was already re-derived on ArkLib and CompPoly.

The catalog is a survey, not an endorsement: each verdict was formed by reading the declaration's
statement and proof, not its docstring, and the audit's findings are reported as a reading to be
checked, not as facts about the code.

## Credit and licence

Both repositories are Apache-2.0. Anything in leanerVM that is substantially derived from the
leanth tree carries, in its module docstring, the line

```text
Derived from Verified-zkEVM/leanth `leanth-project` at 23929f8c (<module>:<lines>), by
Aristotle (Harmonic), Stefano Rocca and Elias Judin; ported to <target API>.
```

and every commit that introduces such material names the three authors as co-authors
(`Co-authored-by:` trailers). A port that keeps the statement and re-derives the proof is still
derived work; a statement written from the specification without reading the leanth proof is
not. The [port log](#port-log) records what has been carried over.

## What changed between leanVM-a and leanVM-b

The differences decide reusability more than anything in the Lean.

| Subject | leanVM-a (leanth) | leanVM-b (this roadmap) | Effect on reuse |
| --- | --- | --- | --- |
| Base field | KoalaBear `ZMod (2^31 - 2^24 + 1)`, degree-5 extension `X^5 + X^2 - 1` | `K = GF(2^64)`, `E = GF(2^192)`; characteristic 2 | Every lemma using `2⁻¹`, `char > N`, or `ZMod` dies; `1 - x` reads `1 + x` |
| Relation | Hand-written AIRs (21, 94 and 33 constraints) and a 57-role bus, decoded to a trace semantics | Clean `EnsembleWitness` of six components under leanISA `SatisfiedBy` | Arithmetization modules are not reusable; the *bridge shape* (polynomial statement ⇔ witness) is |
| Bus argument | Logup: `Σ m/(γ - π_β(σ))`, fractional-sum GKR of degree-3 rounds, Häbock's `char > N` | Fingerprinted grand product `∏ (β - π_α(t))`, radix-4 GKR of degree-5 rounds, unique factorization | Fingerprint algebra ports; logup identities do not |
| Constraint check | Merged zerocheck with a routing round, prefix mask, degree cap `d_max = 14` | One eq-weighted table sumcheck with back-loaded padding, degree 3 | Sumcheck core and degree-cap pattern port; the routing round does not exist |
| Commitment | WHIR over prime-field Reed–Solomon codes, two-adic domains, `y ↦ y²` folding | WHIR over binary Reed–Solomon codes in the novel basis, additive NTT, ring switching | Schedule and error bookkeeping port; folding maps and domains do not |
| Transcript | Poseidon-16 overwrite duplex sponge, `Q`-query duplex transfer certificate | BLAKE2s Merkle–Damgård chain with four numeric tags | Nothing hash-specific ports; the standard-model transfer is not the ROM statement wanted |
| Security framework | In-house `Leanth.Security.{Relation,Protocol,RBR}` on `PMF`: `MaliciousProver`, fixed-prefix `ClosedCertificate`, `ofPrefixCharges` | ArkLib `OracleReduction`, `perfectCompleteness`, `rbrKnowledgeSoundnessWorstCase`, `append` | Nothing framework-bound copies; the composition *proofs* are port sources for ledger A2 and A3 |
| Cube indexing | Big-endian selectors (paper order) in `Shift`, `Stacking`, `Residual`; little-endian in `Logup`, `Commitment`, `WHIR` | Little-endian, bit `k` = coordinate `k` (CompPoly) | Every stacking identity is re-anchored |
| Lean / ArkLib | Lean `v4.28.0`, ArkLib `2dbbe3a6` (only `ProtocolSpec` and `CommitmentScheme.Basic` imported), `import Mathlib` | Lean `v4.33.1` modules, ArkLib `dca90385`, narrow imports | No file compiles unchanged |

## Verdicts

- **copy**: statement and proof carry over with import and API renaming only;
- **port**: the statement and the proof architecture carry over, the proof is re-derived on
  CompPoly and ArkLib, in characteristic 2 and little-endian;
- **pattern**: only the design decision transfers (a statement shape, a hazard avoided);
- **drop**: leanVM-a-specific, framework-bound, or superseded.

Effort is a rough size: S (hours), M (days), L (weeks).

## The catalog, by roadmap layer

### Layer 1: tables, stacking, index and bytecode columns

Seven of the nine public declarations of `Polynomial/Multilinear.lean` are already in ArkLib at
`dca90385` (`eqTilde`, `eqTilde_eq_prod`, `eqTilde_append`, `MLE_eval`, `MLE_eq_zero_iff`,
`MLE_unique` as `eq_MLE_of_degreeOf_le_one_of_eval_zeroOne_eq`, the Schwartz–Zippel wrappers);
the file's own docstrings call them shims. `Shift.lean` (saturating shift, `nextPolynomial`,
`eval_nextPolynomial` :589) serves adjacent-row constraints, which leanISA does not have: drop,
recorded here in case a successor relation is ever needed (the carry-chain closed form is the
only non-trivial content, big-endian).

| Declaration | Source | Statement | Verdict | Target | Effort |
| --- | --- | --- | --- | --- | --- |
| `eqTilde_sum_cube` | `Polynomial/Multilinear.lean:213` | `Σ_c eq(x, c) = 1` over the cube, any `x` | port (done) | `sumCube_eqTable` | S |
| `sum_prod_cube_eq_one`, `sum_prefix_collapse` | `ProofSystem/ZeroCheck.lean:836-886` | `Σ_x ∏ x_i = 1`; a prefix-mask-weighted sum collapses to the sum over the suffix | port (done) | `sumCube_prodVars`, `sumCube_padHigh`, `evalMle_padHigh` | S |
| `AlignedLayout`, `offset`, `pow_height_dvd_offset`, window lemmas | `ProofSystem/Stacking.lean:48, 71, 388, 397, 409` | blocks largest first at prefix-sum offsets; alignment from the antitone order | port (done; EX `Blocks`, `Stacking.lean:41-149`) | `Blocks`, `offset`, `pow_size_dvd_offset` | S |
| `eval_MLE_stack_block` | `ProofSystem/Stacking.lean:603` | `P̃_b(z) = S̃(sel_b, z)`, the selection identity | port (done; EX `eval_stackPoly_sel`, `Stacking/MLE.lean:210`) | `stack_eval` | M |
| `eval_MLE_stack_ambient` | `LeanVM/Protocol.lean:9818` | `S̃(ζ) = Σ_b eq(sel_b, ζ_hi) · P̃_b(ζ_lo)` for a zero-padded stack; 500 lines of private bit lemmas | port; with pad `1` the pad term is `1 - Σ_b eq(sel_b, ζ_hi)` by the partition of unity | `stack_eval_pad` | M |
| `unstack`, `unstack_stack`, `weight_embedBits_of_ne`, `sum_weight_stack_unstack`, `isValid_unstack_iff` | `ProofSystem/Stacking.lean:724-777` | blocks read back from a flat vector; a claim's weight vanishes outside its block, so `q` and `stack (unstack q)` satisfy the same claims | port (unported on EX) | Layer 10 extractor reading `q`; `witnessOf_stackOf` | S |
| `bitPoint`, `bitPoint_eq_finFunctionFinEquiv_symm`, `sum_bitPoint` | `ProofSystem/Commitment.lean:419-460` | little-endian bit decomposition and the flat-sum = cube-sum bridge | copy if ArkLib's `MLE` is ever needed alongside CompPoly | `boolVec`, `sum_cube_split` | S |
| `Blocks.spliceBits`, `selBits`, `evalMle_eq_eval_MLE'`, `finFunctionFinEquiv_split` | EX `Stacking/MLE.lean`, `Poly/EvalBridge.lean:34`, `Poly/MLE.lean:32` | the little-endian cube-splitting API and the CompPoly-to-ArkLib evaluation bridge | copy when a proof needs ArkLib's `MLE'` | Layers 2, 5 | S |

Not present in either source: a stack padded with `1` (the bus trees), and `idxColumn`,
`bytecodeColumn`, which are leanVM-b's own.

### Layer 2: Clean components as polynomials

The generic core of `ProofSystem/ZeroCheck.lean` is the polynomial view of a constraint family;
`Arith/Residual.lean` is its three-table instance and is dropped.

| Declaration | Source | Statement | Verdict | Target | Effort |
| --- | --- | --- | --- | --- | --- |
| `AIR`, `Trace`, `Trace.Satisfies` | `ZeroCheck.lean:53-84` | a constraint family over `Fin width` variables; a trace as cube tables; row-wise satisfaction | pattern (`M3Table` is `AIR` with no shifted columns) | `M3Table` | — |
| `Trace.constraintRowPolynomial`, `eval_constraintRowPolynomial`, `_boolean`, `_eq_zero_on_cube` | `ZeroCheck.lean:99-148` | `Φ_j := bind₁ (MLE ∘ columns) C_j`; `Φ_j(z) = C_j(column MLEs at z)`; on the cube it is the row residual | port (substitution, not interpolation: the MLE of the residual table is the wrong object off the cube) | `Virtual.eval`, `tableSummand`, `toM3_constraints_iff` | M |
| `degreeOf_bind₁_le_totalDegree`, `degreeOf_constraintRowPolynomial_le`, `degreeOf_map_le`, `totalDegree_map_le`, `degreeOf_rename_le` | `ZeroCheck.lean:161-186, 297-334` | substituting individual-degree-≤1 polynomials bounds each `degreeOf` by the total degree; coefficient maps and injective renames keep bounds | copy (Mathlib only, `Nontrivial` for `X`) | `totalDegree_le_degreeBound`, the degree-3 round bound of Layer 7 | S |
| `eval_map_eq_zero_of_eval_eq_zero` | `Arith/Residual.lean:211-234` | a `K`-polynomial vanishing at a Boolean point vanishes there after `map (algebraMap K E)` | copy | Layer 7 (constraints over `K` hold over `E`) | S |

### Layer 3: the M3 instance

Everything here is leanVM-a's; only shapes transfer.

- `Assignment.Satisfies` (`Arith/Glue.lean:529-548`): constraints ∧ balanced bus ∧ public
  input ∧ boundary claims, the conjunct shape of `M3Holds`.
- `coreDecodedAssignment` (`LeanVM/Protocol.lean:17266`): every column read from the committed
  vector through the layout, access counts *derived* rather than read, the shape of `witnessOf`.
- `CanonicalAssignmentData` (`Arith/Refinement.lean:47-54`): `decode_eq` and `satisfies`, the
  pair `witnessOf_stackOf`, `m3Holds_stackOf`; leanth discharges it by `Classical.choice`
  (`fromSemantics`, :1383-1394), leanerVM by the explicit `stackOf`.
- `exists_satisfying_candidate` (`Glue.lean:5977`): the relation is inhabited, the test the
  roadmap asks of the one-row witness.
- `EventKindsHaveDisjointSeparators` (`Arith/Basic.lean:255-259`): the one fact about a merged
  bus that leanISA's `BalancedChannels` does not give, here `g^0 ≠ g^1 ≠ g^2` in `K`.
- Not transferable: `bus_fieldFaithful` (`Glue.lean:2012-2030`, `char > 190,840,832`),
  `flagPre` (`Glue.lean:100-108`, divides by 2), `Address.ofField` (`2^h < p`), the signed
  interaction lists.

### Layer 4: virtual sumcheck and batching (ledger A1)

`ProofSystem/ZeroCheck.lean` carries the generic sumcheck algebra twice (once inlined in the
sealed opaque `merged_worstCaseCertificate` :2952); port the clean copy. Round polynomials travel
as Mathlib `Polynomial F` with the degree cap as a conjunct of acceptance (:1120-1146, the
DR-101/DR-110 fix); ArkLib's `R⦃≤ d⦄[X]` and the roadmap's length-`d+1` coefficient list put the
cap in the type, which is the right place.

| Declaration | Source | Statement | Verdict | Target | Effort |
| --- | --- | --- | --- | --- | --- |
| `sumcheckFreeCube`, `sumcheckRoundPoly`, `sumcheck_roundPoly_initial/chain/terminal`, `sumcheck_natDegree_roundPoly_le`, `sumcheck_sum_freeCube_split` | `ZeroCheck.lean:3455-3675` | honest round polynomial `p_k(X) = Σ_{b} P(c_{<k}, X, b)`; `p_0(0)+p_0(1) = Σ P`; `p_{k+1}(0)+p_{k+1}(1) = p_k(c_k)`; `p_{m-1}(c) = P(c)`; `deg p_k ≤ degreeOf k P` (`CommRing` only) | copy | `sumcheck_perfectCompleteness`, the A1 leaf | S |
| `card_rho_root_le` | `ZeroCheck.lean:2925-2950` | `#{c : deg g ≤ d, p ≠ g, p(c) = g(c)} ≤ d_max` | copy (replace the certificate by `Polynomial.card_roots'`) | the single-round bound `d/|F|` | S |
| `scalarBatch_rejection`, `scalarBatch_eq_zero`, `constraintBatch_rejection` | `ZeroCheck.lean:340-416, 670-697` | some `e_j ≠ 0` ⇒ `#{μ : Σ μ^j e_j = 0} ≤ J - 1` | copy | `batchClaims_rbrKnowledgeSoundness` `(k-1)/|F|` | S |
| `RbrStateInvariant` and the backward laws | `ZeroCheck.lean:2010-2024, 2064-2306` | "checked rounds are capped and chained, the honest partial sum equals the running claim"; prover messages propagate it for free | pattern for the `KnowledgeStateFunction` | `sumcheck_rbrKnowledgeSoundness` | M |
| `exists_eqTilde_update_affine`, `exists_sum_cubic` and neighbours | `ProofSystem/GKR.lean:588-640` | updating one coordinate makes eq and an MLE affine; sums of affine/cubic stay so | port, generalized to a product of `d` affine factors | "the round polynomial has degree ≤ d" | M |
| `individualDegreeAtMost_of_airDegree` | `ZeroCheck.lean:1795-1822` | constraint degree `d` ⇒ merged individual degree `≤ d + 2` (prefix mask + eq) | port and sharpen to `d + 1` (needs disjoint variable blocks, :1811-1813) | the degree-3 pin of Layer 7 | M |
| `batch_rejection`, `batch_complete`; EX `batch_sound`, `batch_complete` | `Stacking.lean:883, 909`; EX `Stacking/Claims.lean:151, 142` | leanth uses `λ^{j+1}` and bound `J`; EX uses `λ^j` and `J - 1`, the roadmap's convention | copy EX | `batchClaims` | S |
| `honestRound` | `GKR.lean:725` | the honest round polynomial chosen by `Classical.choose` | drop: the roadmap's honest prover must compute | — | — |
| `SumcheckCertificate`, `DegreeThreeSumcheckCertificate` | `ZeroCheck.lean:1826`, `GKR.lean:1072` | structures whose one field is `Polynomial.card_roots'` | drop: a hypothesis that is a theorem, never instantiated in the tree, threaded to `Main` | — | — |

### Layer 5: fingerprints, the grand product, GKR (ledger A6)

`ProofSystem/Logup.lean` indexes the 16 coordinates by `Fin (2^4)` with bit `j` via
`Nat.testBit`, the roadmap's order, and its tuples are already in the challenge field. No unique
factorization exists anywhere in leanth; the two ingredients Lemma 5.2 needs do.

| Declaration | Source | Statement | Verdict | Target | Effort |
| --- | --- | --- | --- | --- | --- |
| `fingerprint`, `eval_fingerprintPoly_snoc` | `Logup.lean:90, 713` | `π_β(σ) = Σ_i σ_i · eq(β, bits i)`; the symbolic and evaluated forms agree | copy | `fingerprint` | S |
| `fingerprintPoly`, `eval_fingerprintPoly`, `fingerprintPoly_injective`, `totalDegree_fingerprintPoly`, `aeval_fingerprintPoly` | `Logup.lean:275-444` | `π` with symbolic `β` in `MvPolynomial (Fin 5)`; distinct tuples give distinct polynomials (evaluate at the Boolean point of a differing coordinate); degree ≤ 4 | port (make `_injective` public) | half of `sideProduct_poly_eq_iff`: the factors `X - π_A(t)` are pairwise distinct | S |
| `unbalanced_rejected` counting skeleton | `Logup.lean:804-831` | accepting `(β, γ)` pairs inject by `Fin.snoc` into roots of a 5-variable polynomial; `card_eval_zero_le` with exponent 4 | port with `commonNumerator` replaced by `Π_P - Π_Q` | `sideProduct_collision`, `4·2^μ/|E|` (joint sampling is what gives the constant) | M |
| `fingerprint_collision`, `diffPoly_*` | `Logup.lean:100-230` | `σ ≠ τ ⇒ #{β : π_β σ = π_β τ} ≤ 4·|F|^3` | port (private helper) | Layer 5 | S |
| `eqTilde_cons`, `eval_MLE_cons` | `GKR.lean:439, 447` | eq splits off coordinate 0; an MLE is affine in one coordinate | copy | the radix-2 odd layer | S |
| ξ-round argument `gkrState_xi_poly_ne_zero`, `_eval_eq`, `_bad_xi_le` | `GKR.lean:3596-3713` | false claim ⇒ sent polynomial ≠ honest one ⇒ the challenge is a root of a nonzero degree-`d` difference | port at degree 5 with four corners | `gkr_rbrKnowledgeSoundness`, `5/|E|` per round | M |
| δ bound `gkrState_delta_fold_eq`, `endpoint_pair_ne` | `GKR.lean:3753-3830, 3387` | a dishonest endpoint quadruple survives the fold at ≤ 1 value of δ | pattern: leanVM-b's pair `(δ₁, δ₂)` is bilinear, use `card_eval_zero_le` on two variables for `2/|E|` | the combination challenges | M |
| η bound | `GKR.lean:3508-3578` | numerator-vs-denominator batching, `1/|F|` | pattern for the fresh combiner `λ`, degree `nside - 1` | `(nside-1)/|E|` | S |
| `GkrState`, `gkrState_descend` | `GKR.lean:2696-2734, 3846` | "the running claim is true", reverse induction to the root | pattern | the state function | — |
| `gkrScalarError_sum_le`, `two_mul_sum_three_mul_add_two` | `LeanVM/Protocol.lean:3407-3450` | per-layer charges summed in the doubled form `2·Σ(3r+2) = m(3m+1)` | pattern (redo per radix-4 layer: `(nside-1) + 5k + 2`) | `gkrError` closed form | S |
| `accepts_false_positive_of_checks` | `GKR.lean:1713` | acceptance carries no validity conjunct | pattern: the non-vacuity test for `busPhase` | acceptance tests | S |
| `Accepts` ratio check `base₁ ≠ 0` | `GKR.lean:1706` | reject before dividing | pattern | `R_c ≠ 0` | — |
| `IsFieldFaithful`, `cast_aggregateMultiplicity_ne_zero`, `commonNumerator*`, `balanced_logDerivative_sum`, `undefined_denominators_card_le`, `completeness` | `Logup.lean:85-700` | Häbock's `char > N`, the logarithmic-derivative identity, poles | drop: in characteristic 2 the hypothesis forces every count into `{-1, 0, 1}` and a tuple pushed twice passes; this is why the bus is a product | — | — |
| `FractionalClaim`, `fold`, schedule plumbing, `gkrFill`, `Agreement` | `GKR.lean:63-155, 1084-2746` | radix-2 fractional tower to dimension 0 (Rust cuts at 32 pairs, audit PS-3) | drop | — | — |

Porter tip for Lemma 5.2: view `Π_P` as `(P.map fun t ↦ X - C (π_A t)).prod` in
`Polynomial (MvPolynomial (Fin 4) K)` and use Mathlib's `Polynomial.roots_multiset_prod_X_sub_C`
with `Multiset.map_injective` and `fingerprintPoly_injective`; no unique-factorization argument
and no characteristic hypothesis.

### Layer 6: the bus phase

- `CoreLogupCharge` (`LeanVM/Protocol.lean:6582-6660`): the knowledge state after the bus
  challenge is "unbalanced ∧ the identity holds at the challenge", charged once for the joint
  `(β, γ)` message (decision DR-112). The roadmap's "pushed and pulled multisets differ ∨ some
  count is zero ∨ a boundary claim is false" is the product analogue; "some count is zero" has
  no leanVM-a counterpart.
- `eval_MLE_stack_ambient` (`LeanVM/Protocol.lean:9818`) is the port source for
  `leaf_decomposition` once `stack_eval_pad` exists.
- Completeness in leanVM-a is `K/q + ε_whir` because of logup poles
  (`interactive_hasCompletenessError`, :13817); the grand product has no poles, so perfect
  completeness at the oracle level is consistent.

### Layer 7: the table sumcheck phase

| Declaration | Source | Statement | Verdict | Target | Effort |
| --- | --- | --- | --- | --- | --- |
| `suffixPoint`, `prefixMask`, `itemSummand`, `mergedSummand`, `itemPoly`, `mergedPoly` | `ZeroCheck.lean:725-804, 1013-1087` | item `j` of height `h_j` in the high coordinates, padded by `∏_{i < h_max - h_j} X_i`, eq-weighted at `r`; the roadmap's lift `∏_{k ≥ τ_j} X_k` under `i ↦ n-1-i` | port | `tableSummand` | M |
| `merged_equivalence`, `sum_cube_eval_mergedPoly_residual` | `ZeroCheck.lean:941-965, 1833-1910` | `Σ_b mergedSummand = Σ_j μ^j · (W̃_j(r) - t_j)`; the subtracted target contributes `-t_j` by the partition of unity | port with the target on the right | `tableSummand_target` | M |
| `terminalValue`, `eval_mergedPoly` | `ZeroCheck.lean:1089-1108, 1833` | the verifier computes eq at the point and the running weight `∏` of the challenges a table sat out, from transcript data only | port | the final check of `tableSumcheck` | S |
| `exists_air_witness_poly`, `point_rejection`, `common_charge_ratio_le` | `ZeroCheck.lean:2857-2901, 627` | not satisfied ⇒ some violated item's extension is a nonzero polynomial of total degree `≤ h_max`; `≤ h_max·|F|^{h_max-1}` points kill it | copy (ArkLib has `MLE_eq_zero_iff`, `card_zeros_le_of_totalDegree_le_fin`) | the zerocheck step | S |
| `honestProver_accepts_aux`, `honestSumcheckAccepts` | `ZeroCheck.lean:3679-3942` | on a satisfied instance every coin vector passes the five checks | port the pointwise lemma | `tableSumcheck_perfectCompleteness` | S |
| routing round `CoreRoutingOracle`, `airRoutingCollision_card_le` | `LeanVM/Protocol.lean:5269-5558` | prover-supplied residuals agree with reconstructions at a fresh point | drop: the deployed protocol has no such round (audit PS-2); leanVM-b's verifier evaluates the constraint itself | — | — |
| degree-cap remark | `LeanVM/Protocol.lean:17079-17108` | without a public individual-degree cap a Boolean-vanishing residual buys `(|F|-1)/|F|` | pattern: never accept a prover-supplied residual polynomial | — | — |

Two things the port should change. leanth charges the recycled point *once*, `h_max/|F|` for the
whole family, because one violated item suffices (:3202-3239); the roadmap's Layer 7 text charges
`τ_max/|E|` per constraint, an over-estimate. And leanth's `r` is a fresh first-round challenge;
leanVM-b's `ζ` is recycled from Layer 6, so the algebra transfers and the position of the charge
moves.

### Layer 8: the public-input phase

`PublicPrefixCheck`, `publicPrefix_rejection` (`LeanVM/Protocol.lean:156, 224`): two different
cube tables agree at a random point with probability `≤ h/|F|`, by `MLE_sub` and
`point_rejection`. leanVM-b's check is the line `(1 + r)·w + r·w'` and three pooled claims; the
lemma is a one-liner from ArkLib's `MLE_eq_zero_iff` and Schwartz–Zippel. Pattern only.

### Layer 10: the claim pool, the opening sumcheck, the composition (ledger A2, A3)

| Declaration | Source | Statement | Verdict | Target | Effort |
| --- | --- | --- | --- | --- | --- |
| `Claim`, `Claim.IsValid`, `Claim.weight`, `claim_iff_innerProduct` | `Stacking.lean:627-705`; EX `claim_iff_normal`, `Claims.lean:82` | a claim `(block, point, target)`; valid iff the inner product of the stack with the eq-weight hits the target | pattern; copy EX for the eq-weight case | `Claim`, `Weight`, `Claim.toWeighted` | S |
| `batchDifference_card_le`, `card_batch_collision_le`, `openingRelation_holds_batched` | `LeanVM/Protocol.lean:15960`; `Commitment.lean:650-724, 894` | families that differ agree under `Σ λ^{j+1}(-)` at ≤ `J` values of `λ`; a true family is true batched | port (exponents `λ^j`, bound `J - 1`); copy the completeness half | `openingPhase_rbrKnowledgeSoundness` | S |
| `splitError`, `splitError_sum`, `splitCharge` | `LeanVM/Protocol.lean:2490-2520` | a per-challenge function over `s₁ ++ₚ s₂` via `ChallengeIdx.sumEquiv`; sum is the sum | copy | `piopError` | S |
| the charge mirror `coreChargeOf`, `corePrefixChargeOf_kernel_le`, `coreClosedCertificate` | `LeanVM/Protocol.lean:23262, 23908, 23940` | the charge family is built by the same nesting as the error family, so round-disjointness is definitional | pattern: the recipe for assembling `piopError` and the state function together | Layer 10 | — |
| `ClosedCertificate.ofPrefixCharges` | `Security/RBR.lean:2370-2413` | from per-challenge charge predicates with fresh-kernel bounds, "charge-free accepting ⇒ valid", and a terminal witness: a worst-case knowledge certificate; hidden hypotheses `steps_pos` and `challenge_pos` (no challenge at round 0) | port as a `KnowledgeStateFunction.ofCharges` on ArkLib | every phase's state function | L |
| `isRBRKnowledgeSound_append`, `appendError`, `appendError_sum`, `toOuterMeasure_le_of_heq`, the seam design `RightBlockWitness`, `seam_state_iff` | `Security/RBR.lean:5042, 2463-2478, 5024, 4087, 2580-2621` | worst-case knowledge certificates compose over `++ₚ` with errors concatenated, **no purity hypothesis** (accepts and residual are functions of the transcript, no shared oracle); the right-block witness stores the first full transcript and asserts the first verifier accepts it | port: the knowledge twin of ArkLib's proved `append_rbrSoundnessWorstCase_of_pure_first`; what ArkLib lacks is `KnowledgeStateFunction.append` and two bad-set transports | ledger A2 | L (3–6 weeks; 60% of RBR.lean is `HEq` bookkeeping ArkLib's `FullTranscript.fst/snd` avoids) |
| `closed_isKnowledgeSound`, `actualBad_mass_eq`, `run_factorization_apply` | `Security/RBR.lean:2422-2453, 2051`; `Security/Protocol.lean:1053` | per-round bad events cover extraction failure; union bound; per-round mass equals the worst-case bound via a prefix factorization of the run | port on `OracleComp`/`probEvent` (the factorization of `Prover.run` against `runToRound` is the missing piece) | ledger A3 | L |
| `coreSelectedAssignment`, `coreReduction.good` | `LeanVM/Protocol.lean:2208, 2471-2487` | the extractor is `Classical.choose` on satisfiability; the terminal relation is `True` | drop: this is soundness, not extraction (audit FW-1); leanerVM's extractor is `witnessOf` on the oracle message | — | — |
| `ChallengeReuseCondition`, `reuseCoreRoundErrorOf`, `reuseReindexedError_sum` | `LeanVM/Protocol.lean:24767, 24746, 25043` | point recycling charged `1/q` per recycled coordinate at the round that draws it; total unchanged; the condition is **never discharged** | pattern for charging `ζ` to Layer 6's rounds; copy the 40-line `Finset` reindexing lemma | Layer 7's point recycling | S |
| `InteractiveErrorData`, `InteractiveConfig` | `LeanVM/Protocol.lean:269-335, 694-785` | the error as a separate record with 13 coherence equations | negative pattern: keep the closed form a `def` next to the theorem | `piopError_le` | — |

### Layer 11: WHIR and Merkle (ledger A7, A8)

ArkLib at `dca90385` has no `ProofSystem/Whir/` directory (the blueprint's `whir.tex` marks every
declaration "not formalized"), which confirms ledger row A7. `ProofSystem/WHIR.lean` proves no
security property: Theorem 5.2 is the field `closed` of `WHIRCertificate` (:1056) and completeness
the field `completeness` (:1061); its `CodingHypotheses` (:100-146) is consumed by no theorem.

| Declaration | Source | Statement | Verdict | Target | Effort |
| --- | --- | --- | --- | --- | --- |
| `ChallengeRole`, `index_bijective`, `exact_inventory` | `WHIR.lean:271-647, 1032` | five roles (initial fold, OOD, shift, main fold, final) in paper order; `K + 2M - 1` challenges | pattern for the schedule; unnecessary if `whirOpen` is an `append` of per-level reductions | `whirOpen` | M |
| `AcceptsView` | `WHIR.lean:928-960` | the verifier's check list: constraint recurrence, degree, initial sum, chain, OOD replies, new claim with `γ` powers, terminal identity, final queries | pattern: matches Protocol B.1 including one OOD sample from level 1 on | `whirOpen` verifier | M |
| `roleError`, `whirRoundError` | `WHIR.lean:655-684, 968` | per-role rational error terms in the paper's index conventions (`ℓ_{0,s}` with `err*_{0,s+1}`; shift batches of `τ - 1` points) | port as the *shape* of `whirError`; constants re-derived for the binary code | `whirError` | S |
| `foldedDimension`, `stageDistance` | `WHIR.lean:66, 86` | `m_i = n - Σ k_j`; relative distance | copy | parameters | S |
| `closeList_spec`, `closeList_bound` | `WHIR.lean:114-118` | list decoding per stage: at most `ℓ` codewords within distance `< δ` | pattern for stating `McaJohnson`'s list-decoding half | `McaJohnson` | — |
| `reduction_eq` pinning | `WHIR.lean:1050, 1054` | a certificate field forcing the certified reduction to be the operational one | optional pattern: an interface whose fields name `whirOpen params` is already pinned | — | — |
| `poweredDomain`, `pullback`, `foldedValue`, `powVector`, `mcaBad`, `oodQuery`, `initialOracle` | `WHIR.lean:70-96, 192, 828, 57, 120-162` | squaring domains and fiber bijections; the fold; `(z, z², …, zⁿ)` | drop: `pullback` is uninhabitable in characteristic 2 (Frobenius is injective); `powVector` should be `(z^{2^i})` and `foldedValue` is not WHIR's `Fold_f` (two transcription deviations the file cannot detect); `mcaBad` is neither ArkLib's `IsMCA` nor list-decoding preservation | — | — |
| `WHIRCertificate.closed`, `terminal` | `WHIR.lean:1056`; `RBR.lean:2093-2104` | soundness as a field; a terminal witness for *every* accepting transcript (needs a surjective `commit`) | drop | — | — |

The audit branch adds `CodingHypotheses.false_of_production_pins`: at rate `2^-7` with `δ = 1/2`
and `ℓ = 1` the list-decoding pin is false (a word within distance `< 1/2` of two codewords),
so `ProductionParameterCertificate` is empty and the flagship `≤ 2^-124` theorem is vacuous. The
lesson for Layer 11 is an acceptance test: every pinned coding parameter must come with an
achievability witness, and `McaJohnson` must say whether it is the affine-line case (ArkLib's
admitted `rs_mcaError_le_in_johnson_range`) or the powers-generator case (ArkLib proves
`linear_mcaError_powers_le` only in a generalized radius); WHIR batches with powers.

### Layer 12: compilation, transcript, `verify` (ledger A5)

`ProofSystem/Transcript.lean` is standard-model Fiat–Shamir: `squeeze` is a fixed function with
no oracle and no query log (:88, :138), so its `Q` is attached to no adversary, and at the pins
`Q = t = 1`, `ε_model = 0`. Nothing there is a port source for `FsState`, and its error is
`Q · Σ_i ε_i` (:214-247), not the roadmap's `Q · max_i ε_i`.

| Declaration | Source | Statement | Verdict | Target | Effort |
| --- | --- | --- | --- | --- | --- |
| `Codec.injective` | `Transcript.lean:96-102` | `decode ∘ encode = some` ⇒ `encode` injective | pattern; leanerVM's decoder is lossy by design, so the law is relative to the running claim | `RoundPoly.decode` | S |
| `PublicBCSProof`, `QueryLocalCompiler`, `query_eq_of_accepts` | `Transcript.lean:258-340` | the proof carries commitment, verifier-derived queries, responses, local openings; queries are derived from the checked public prefix | pattern (drop the extractor log from the public proof) | `Proof`, `verify` | — |
| `IsBindingAndStraightlineExtractable` two-clause bad event; `FamilyOutcome.Failure` | `Transcript.lean:398-410, 503-537`; `Commitment.lean:158` | for every compiled prover an IOP prover whose transcript is the pushforward under `extract`, except when no datum is consistent with all accepted claims (binding pays) or the extracted datum is wrong (extraction pays); one datum for every accepted claim | pattern for the fields of `BcsSecurity`, with the adversary an `OracleComp` under VCVio `IsQueryBound` and the error a function of the budget | `BcsSecurity` | M |
| `bcs_isStraightlineKnowledgeSound` | `Transcript.lean:669-720` | composition shape: FS transfer ∘ commitment extraction, union bound | pattern | `verify_knowledgeSound` | M |
| `BindingCertificate`, `FamilyStraightlineExtractionCertificate`, `SchemeInstantiation`, `InnerProductScheme.binding` | `Commitment.lean:208-302`; `Transcript.lean:441-489` | games over query-unbounded `OracleComp` adversaries; perfect binding | drop: no hash-based scheme satisfies them (audit F-3); leanVM-b is list binding | — | — |
| `DuplexFSCertificate`, `HasRBRKnowledgeError` | `Transcript.lean:205-247` | the transfer theorem as a field, sum-form error | drop; the interface shape (structure with docstring) is the roadmap's own | — | — |
| `DerivedFiatShamir` | `DerivedFiatShamir.lean` | "completeness in the compiled game": the derived-challenge prover is `Derived` by construction; the two rejection bounds are fields never instantiated | drop: proves nothing about the transform; `baseProver_complete` needs only perfect completeness plus chain determinism | — | — |
| `Main.error`, `isKnowledgeSound`, `Config` | `LeanVM/Main.lean:332-600` | `Q·ε_iop + ε_bind + ε_extract + ε_model + C·t²/p^8`; 27-field configuration, **never inhabited** (audit F-8), compiled prover carrier a free field (FW-4), `hwhir` a hypothesis that is always true | drop | — | — |

### Layer 13: T4 and fixtures

- `Refinement`, `knowledgeSound_mapRelation`, `straightlineKnowledgeSound_mapRelation`
  (`Security/Relation.lean:48-52`; `Security/Protocol.lean:1170-1211`): knowledge soundness
  transports along a total validity-preserving witness map at the same error. Port as one lemma on
  ArkLib's `Extractor.Straightline`; it is `baseVerifier_extractsExecution` with the map
  `q ↦ witnessOf prog s q` and `map_valid := satisfiedBy_witnessOf`. Requirement it imposes:
  `witnessOf` must be total on every `Column μ`.
- `LeanVM/ParameterSearch.lean`: the closed form of the error reflected to `ℚ≥0` (`coreError`
  :81), an equality lemma to the live `def` (:103-113), a cast lemma to `ℝ≥0`
  (`nnratError_cast` :393), and `decide +kernel` (:631). Pattern for acceptance test 23 if the
  roadmap's `norm_num` at `2^192` times out; the certificate itself is empty at the pins.

### Beyond this roadmap

- `Aggregation/Core.lean`: the forwarding sumcheck (`ForwardingConfig` :342, `SumcheckAccepts`
  :640, `forwarding_rejection` :2153 with error `(2 n_rec + 2 h')/q`, `forwarding_complete`
  :2353) is an instance of Layer 4's eq-weighted sumcheck with a batched kernel; the tree
  extraction (`stochasticExtractTree_failure_le` :3178, `isKnowledgeSound_of_core` :3286) is
  scheme-generic but assumes transparent recursion (child proofs read off the root proof). Port for
  T6 with "the level-ℓ extractor produces an accepting level-(ℓ-1) transcript" in place of
  `childProofs`. RBR knowledge soundness of forwarding is an assumed field, not proved.
- `XMSS/*`: out of scope; the audit's F-6 (the verification relation cannot denote the deployed
  scheme) stands.

## Lessons that bind the roadmap

Patterns worth adopting, each with the leanth evidence.

1. **Fixed-prefix worst-case round-by-round only.** leanth's averaged notion
   (`IsRBRKnowledgeSoundWith`, `RBR.lean:1840`) was abandoned (decision DR-113) yet still
   consumed by the transcript layer; a rare prefix satisfies an averaged bound while violating
   the per-prefix one, and no upgrade exists. The roadmap's `rbrKnowledgeSoundnessWorstCase`
   everywhere is the right choice.
2. **The degree cap lives in the message type**, not in an acceptance conjunct
   (`ZeroCheck.lean:1120-1146` needed the conjunct because its wire type was unrestricted).
3. **The verifier computes constraints itself.** Prover-supplied residuals need a routing
   round and a degree cap (`LeanVM/Protocol.lean:17079-17108`); the roadmap's `Virtual` avoids
   both.
4. **A hypothesis that is a theorem is a hazard.** `SumcheckCertificate`,
   `DegreeThreeSumcheckCertificate`, `hwhir : WHIRCertificate.IsValid` (`Main.lean:87-89`,
   proved for every certificate) look like assumptions and are not; a reader cannot tell which
   fields carry content. The roadmap forbids assumed hypotheses and this is one more reason.
5. **`Classical.choose` extraction is soundness.** `coreSelectedAssignment`
   (`Protocol.lean:2208`) and `fromSemantics` (`Refinement.lean:1383`) make "knowledge" the
   satisfiability of the statement (audit FW-1). Acceptance test 19 (the extractor reads the
   stack) is the roadmap's guard.
6. **Pins need achievability witnesses** (audit F-1): a parameter certificate whose equalities
   force a false coding hypothesis is empty and every theorem under it is vacuous. Acceptance
   test 23 should include the witness, and `McaJohnson` its regime.
7. **Negative controls and non-vacuity theorems are tests.** `accepts_false_positive_of_checks`
   (`GKR.lean:1713`), `averagedCoreExtraction_forces_satisfiable` (`Protocol.lean:3323`),
   `Control.directOpeningReduction` (`Protocol.lean:13869`): each shows a definition is not
   trivially inhabited. The roadmap's mutation tests play this role; keep them.
8. **Build the charge family by the same nesting as the error family** (`Protocol.lean:
   23188-23200`), so that round-disjointness is definitional and the closed form is next to the
   theorem.
9. **A message-first schedule is a hidden hypothesis of the charge constructor**
   (`ofPrefixCharges`'s `challenge_pos`, `RBR.lean:2374`): leanth pads with `PUnit` messages. A
   port to ArkLib's `KnowledgeStateFunction` need not.
10. **Transcription deviations are invisible when soundness is a field.** `powVector` and
    `foldedValue` (`WHIR.lean:57, 828`) are wrong relative to WHIR and nothing in the tree can
    notice, because the theorems about them are certificate fields. This is the reason the
    roadmap requires every protocol theorem proved, not assumed.
11. **Characteristic 2 changes three things and no more**: `eq`'s factor `1 - x` becomes
    `1 + x`; Häbock's condition is unusable (hence the product bus); separators `0/1/2` collapse
    (hence `g^0/g^1/g^2`). No leanth proof divides by 2 except `flagPre` and WHIR's fold.

## What not to reuse

The arithmetization (`Arith/*`, 17k lines), the composed protocol's decode, charge and honest
layers (`LeanVM/Protocol.lean`, 25k lines), the security carriers (`Security/*`, 6.4k lines,
except as port sources for A2 and A3), the WHIR parameter object and certificates, the
commitment and Fiat–Shamir certificates, `Main`, `ParameterSearch`'s pins, aggregation's
`Config`, and XMSS. The reasons are in the tables: prime field, logup, three tables, a framework
on `PMF`, and certificates whose fields are the theorems.

## Port log

What this repository has carried over, with the derived-from lines in each module docstring.

| leanerVM declaration | Module | Source | Ported by |
| --- | --- | --- | --- |
| `sumCube_eqTable` | `LeanerVM/Protocol/Multilinear.lean` | `Polynomial/Multilinear.lean:213` | this branch |
| `sumCube_prodVars`, `padHigh`, `sumCube_padHigh`, `evalMle_padHigh` | `LeanerVM/Protocol/Multilinear.lean` | `ProofSystem/ZeroCheck.lean:836-886` | this branch |
| `cubeIndex`, `sum_cube_split`, `lagrangeBasis_cubeIndex`, `boolVec`, `slice`, `evalMle_split`, `evalMle_append_boolVec` | `LeanerVM/Protocol/Multilinear.lean` | `ProofSystem/Stacking.lean:271-366, 603` and EX `Stacking/MLE.lean` | this branch (new proofs on CompPoly) |
| `Blocks`, `offset`, `pow_size_dvd_offset`, `offset_add_pow_le_offset`, `stackAt`, `selector`, `stack_eval` | `LeanerVM/Protocol/Stacking.lean` | `ProofSystem/Stacking.lean:48-133, 388-479, 603` and EX `Stacking.lean`, `Stacking/MLE.lean` | this branch |

Next port candidates, in order of value per effort: the `unstack` lemmas (Layer 10, S);
`scalarBatch_rejection` (Layer 4, S); the `sumcheck_*` core (Layer 4, S); the fingerprint
lemmas (Layer 5, S); `stack_eval_pad` from `eval_MLE_stack_ambient` (Layer 1, M); the
`ofPrefixCharges` and `append` designs (A2, L).

## Upstream candidates

Where a leanth proof is the port source for an ArkLib ledger item.

| Ledger | ArkLib gap at `dca90385` | leanth port source |
| --- | --- | --- |
| A1 sumcheck round-by-round knowledge soundness | `Sumcheck.Spec.SingleRound.verifier_rbrKnowledgeSoundness` admitted | `ZeroCheck.lean:3455-3675` (algebra), `:2925` (root count), `:2010` (state) |
| A2 knowledge-soundness composition | `append_rbrKnowledgeSoundness`, `seqCompose_rbrKnowledgeSoundness` admitted | `RBR.lean:5042` and the seam design `:2580-2621`; `Protocol.lean:2490-2520` for the error split |
| A3 round-by-round implies plain | `rbrKnowledgeSoundness_implies_knowledgeSoundness` admitted | `RBR.lean:2422-2453, 2051`; `Security/Protocol.lean:1053` |
| A6 grand product, GKR, batching, stacking | absent | `Logup.lean:275-444, 804-831`; `GKR.lean:439-640, 3596-3830`; `Stacking.lean` (stacking, done here); `ZeroCheck.lean:670-697` (batching) |
| A7 WHIR, Merkle | absent | `WHIR.lean:271-684, 928-960` as the reference shape only |
| A8 mutual correlated agreement | `rs_mcaError_le_in_johnson_range` admitted (affine lines) | none; `WHIR.lean:120-133` shows what not to state |
