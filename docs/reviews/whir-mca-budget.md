# Record: ArkLib's proved Johnson bound meets Annex B's budget

A probe of 2026-10-19, against ArkLib `7653a901` and leanVM `a386121f` (the pins). It answers the
question the protocol status left open: does `ReedSolomon.mcaError_affineLine_johnson_le`, the
proved mutual-correlated-agreement bound, meet the per-level budget of Annex B's `thm:rbr` at the
deployed WHIR parameters, or must the admitted `rs_mcaError_le_in_johnson_range` be named as an
obligation? The numbers are reproduced by `scripts/whir-mca-budget.py`, which uses only Python's
standard library, and the deployed `η` dumped from the pinned Rust by
`scripts/dump-whir-eta-rust.sh`. The Lean evidence was checked with `lake env lean` against ArkLib alone, and its
source is in the description of the pull request that added this record. It is not production
code; Layer 11 builds `mcaJohnson_annexB` from it.

## Verdict

The proved theorem suffices at every level of all 56 admissible `(μ, R)` pairs, with no change of
parameters, and by a theorem rather than by a table.

- ArkLib's `johnsonComparisonEstimate n D η` (`FiniteBounds.lean:137`) is Annex B's `a` of
  `thm:mca-johnson`, symbol for symbol: `ρ = D/n`, `θ = max ⌈√ρ/η⌉ 3`, `γ = 1 − √ρ − η`,
  `a = (2(θ + ½)^5 + 3(θ + ½)γρ)/(3ρ^{3/2})·n + (θ + ½)/√ρ`. ArkLib proves its own exception
  count `E₀` strictly below `(16/49)·a` (`johnsonExceptionCount_div_comparisonEstimate_lt`,
  `FiniteBounds.lean:756`, and its corollary `johnsonExceptionCount_le_comparisonEstimate`,
  `:849`). So the proved theorem gives the printed [BCHKS25] bound at every
  `(n, D, η)` in the Johnson range, over every finite field.
- At the deployed levels `E₀` is 10.0 to 20.8 bits below `a`. The least margin of the MCA share of
  `thm:rbr`'s fold row (`2^{ℓ−1}·ε ≤ 2^{−128}`) is 128.19 bits with `a` (level 0 of `(27, 3)`) and
  143.16 bits with `E₀` (level 5 of `(28, 4)`).
- The admitted theorem is not needed. Its statement at index type `Fin n` follows from the proved
  one.

`#print axioms` reports `[propext, Classical.choice, Quot.sound]` for every probe theorem and for
the upstream theorems it uses.

## The numbers

The script reproduces the Rust's per-level `η` search (`whir_config.rs:445-707`) in IEEE doubles,
including `johnson_eta_for_m`'s ulp stepping and the evaluation order of `powi(5)`. It re-derives
the whole table: all 56 rows of `WHIR_QUERIES` (`verifier.py:910`) come out exactly, 224 levels
and no mismatch. The Rust's own `η`, dumped by `scripts/dump-whir-eta-rust.sh`, agree with the
reproduction bit for bit at all 224 levels, with the same query counts (`--rust-eta FILE`);
Layer 11 transcribes them from the dump. Each level's `η` is then the exact dyadic rational the
double denotes, and every verdict below is decided in exact rationals; 80-digit decimals serve
only for `√ρ` and logarithms.

| Check over the 224 levels | Result |
| --- | --- |
| the theorem's hypotheses `1 ≤ D`, `D ≤ n − 2`, `0 < η`, `√ρ + η ≤ 1` | all hold |
| `E₀ ≤ a` | all |
| `E₀ ≤ (16/49)·a` | all |
| `2^{ℓ−1}·E₀ ≤ 2^{64}`, that is the MCA share of the fold row at most `2^{−128}` | all |
| `log₂(a/E₀)` | from 10.03 to 20.78 |
| least margin with `a`, `192 − log₂(2^{ℓ−1}·a)` | 128.185 bits, `(27, 3)` level 0 |
| least margin with `E₀` | 143.162 bits, `(28, 4)` level 5 |
| the whole fold row `(2L + 2^{ℓ−1}·a)/|E|`, least margin | 128.185 bits (`2L` is negligible) |
| levels whose fold row is below 128 bits | none, with either constant |

The worst level per rate exponent, by least margin with `E₀` (`θ` is Annex B's parameter, `M`
ArkLib's `max ⌈√ρ/(2η)⌉ 3`):

| R | (μ, level) | n | D | θ | M | log₂ a | log₂ E₀ | margin with a | margin with E₀ |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | (28, 0) | 2^23 | 4194303 | 111 | 56 | 57.920 | 42.587 | 129.080 | 144.413 |
| 2 | (28, 0) | 2^24 | 4194303 | 82 | 41 | 58.247 | 43.090 | 128.753 | 143.910 |
| 3 | (27, 0) | 2^24 | 2097151 | 72 | 36 | 58.815 | 43.387 | 128.185 | 143.613 |
| 4 | (28, 5) | 2^21 | 3 | 4 | 3 | 60.387 | 45.839 | 128.613 | 143.161 |

The two levels instantiated in Lean:

- `(15, 1)` level 0: `n = 1024`, `D = 511`, `η = 8247514870967899·2^{−62}`, `θ = 396`, `M = 198`,
  `⌈(√ρ + η)·n⌉ = 726`, `E₀ = 7730470227742/215 ≈ 2^{35.07}`, `log₂ a = 54.08`; 223 queries;
  budget `ε ≤ 2^{−133}` (`ℓ = 6`).
- `(28, 4)` level 5, the worst: `n = 2^21`, `D = 3`, `η = 7354347395230781·2^{−64}`, `θ = 4`,
  `M = 3`, `⌈(√ρ + η)·n⌉ = 3345`, `E₀ = 105135228284935607/1671 ≈ 2^{45.84}`, `log₂ a = 60.39`;
  budget `ε ≤ 2^{−131}` (`ℓ = 4`).

`--full` prints every level and `--json FILE` dumps them.

**Re-choosing `η` with ArkLib's constant** (`--rechoose`) reruns the Rust's search with `E₀` in
place of `a`. The total query count over the 56 pairs drops from 11442 to 11381, by one or two
queries at one or two levels of 37 pairs. With `E₀` the MCA term stops binding, and the list-size
terms of `thm:rbr` (`L_i = 1/(2η_i√ρ_i)`) bind instead. The sharper constant buys margin, not
queries; the deployed `η` need not change.

**The weighted variant** (`mcaError_affineLine_weightedJohnson_le`, `--weighted`) gains 0.3 bits at
`(15, 1)` level 0 and has no certificate at the worst level in the searched range. It is not worth
its hypotheses.

## The Rust's doubles

`johnson_eta_for_m` (`whir_config.rs:624-633`) sets `η = fl(√ρ)/m` and steps it up by ulps until
the double `⌈fl(√ρ)/η⌉` equals `m`. The exact ratio `√ρ/η` then lies within `10^{−16}` of `m`, and
whether the exact ceiling is `m` or `m + 1` is a rounding accident. At 108 of the 224 levels it is
`m + 1`, so Annex B's exact `a` exceeds the Rust's estimate by `((m + 1.5)/(m + 0.5))^5`, up to
1.81 bits (`m = 3`, at `(28, 4)` level 5: 130.43 bits by the Rust, 128.61 exactly). The least
exact margin, 128.185 bits, falls at a level where the two agree, so the deployed table survives
exact arithmetic. A Lean transcription computes `θ` from `η` and never takes it to be `m`. ArkLib's
`M` sits on the same boundary (`θ − 2M ∈ {0, 1, 2, 3}` across the levels). The finding is recorded
in [leanvm-target.md](../leanvm-target.md#known-discrepancies-at-the-pin).

## Definitional checks

- **The event.** ArkLib's `IsMCA G MC x U δ` (`ProximityGenerator/Basic.lean:119-125`) asks for a
  set `T` with `|T| ≥ n(1 − δ)` on which the combined word agrees with the code while some row
  does not. That is Annex B's event in `thm:mca-johnson` and `lem:fold-list`: a pair agrees with
  the interleaved code on `A` exactly when each row has a codeword extension on `A`. `mcaError` is
  the supremum over word families of the probability over a uniform `x`, which is
  `thm:mca-johnson`'s "for every two-row word". It is a step function on the `1/n` grid
  (`mcaError_eq_of_floor_eq`), hence the threshold `⌈(√ρ + η)·n⌉` in the proved theorem.
- **The generator.** ArkLib's line is `x ↦ (1, x)`, the combination `u₀ + x·u₁`; Annex B folds
  `(1 − z)·u₀ + z·u₁ = u₀ + z·(u₁ − u₀)`. The map `(u₀, u₁) ↦ (u₀, u₁ − u₀)` is a bijection on
  pairs that keeps "both rows extend to codewords on `T`", since the projected code is a submodule.
  `mcaError_foldLine_eq_affineLine` proves the two generators' errors equal at every radius, for
  every linear code over a field, with no characteristic hypothesis.
- **The rate.** `johnsonRhoMinus n D = D/n` with `D` the degree bound (dimension `D + 1`). At
  `D = 2^κ − 1` and `n = 2^{κ+R}` it is Annex B's reduced rate `(k − 1)/n` and the Rust's
  `reduced_rate` (`whir_config.rs:426-429`). The theorem's radius `1 − √ρ − η` is the Rust's `γ`.
  `D ≤ n − 2` holds at every level, since `R ≥ 1`.
- **The field.** The theorem needs `[Field F] [Fintype F] [SampleableType F]`, and `|F|` enters
  only as `Fintype.card F`. `E` has all three (`instSampleableTypeE`, `card_E : Fintype.card E =
  2^192`, `LeanerVM/Protocol/Field.lean`).

## The Lean evidence

Five theorems, each checked with `lake env lean` against the ArkLib oleans of the pin:

1. `mcaError_affineLine_le_annexB`: for `1 ≤ D ≤ n − 2`, `0 < η`, `√ρ + η ≤ 1`,
   `mcaError (AffineLineGenerator F) (code domain (D + 1)) (1 − (√ρ + η)) ≤ min 1 (ofReal
   (johnsonComparisonEstimate n D η / |F|))`, Annex B's constant, over any finite field.
2. `level_15_1_0_budget`: at `n = 1024`, `D = 511` and the deployed `η`, over any `F` with
   `|F| = 2^192`, the error is at most `2^{−133}`. The ceilings are proved from exact rational
   bounds on `√ρ`, and `E₀` by `norm_num`.
3. `level_28_4_5_budget`: the worst level, at most `2^{−131}`, the same way.
4. `mcaError_foldLine_eq_affineLine`: the generator bridge above.
5. `johnsonRange_of_proved`: the statement of `rs_mcaError_le_in_johnson_range`
   (`CapacityBounds.lean:203`) at `ι := Fin n`, from the proved theorem, its comparison lemma and
   the full-code case.

None uses `sorry`, `axiom`, `native_decide` or an option override.

## Not verified

- `thm:rbr`'s other rows (batching, out-of-domain, the queries with grinding, the final level)
  were not re-derived beyond what the search checks; they do not involve the MCA constant.
- `mcaError` was not transported from a general index type to `Fin n`, the one step between the
  probe and the admitted theorem's exact shape.

## Upstream pull requests that bear on this (2026-10-19)

- ArkLib #1297 (open) removes two unused admitted declarations from the Johnson chain's imports;
  no statement changes. The axioms above confirm the chain is clean at the pin.
- ArkLib #776 (open): `_of_budget` wrappers for the proved bounds; it predates the Johnson theorem,
  so `mcaError_affineLine_le_annexB` is leanerVM's own wrapper.
- ArkLib #792 (open): the Johnson list size of an interleaved code, the `L_i` of
  `thm:johnson-interleaved`, not the MCA bound.
- ArkLib #1311 (open): BCIKS20 Theorem 6.1 in the unique-decoding regime, not the Johnson range.
