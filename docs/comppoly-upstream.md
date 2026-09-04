# Upstreaming the binary field tower to CompPoly

This page is a handoff. It describes what `LeanerVM/Parameters/Field/` contains, which
parts are generic enough to belong in [CompPoly](https://github.com/Verified-zkEVM/CompPoly),
and what a porting agent needs to know to open that pull request.

Everything described here builds and passes `./scripts/validate.sh`. No declaration uses
`sorry`, `admit`, `axiom`, `unsafe`, or `native_decide`; every result reports the kernel
footprint `[propext, Classical.choice, Quot.sound]`.

## What was built

Two finite fields, matching the leanVM specification and its pinned Rust implementation:

```text
K = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)      |K| = 2^64
E = K[y]/(y^3 + y + 1)                        |E| = 2^192
```

Source revision: leanVM [`a386121f84292f6fa663aaa3e570c15bc0240ea2`](https://github.com/leanEthereum/leanVM/commit/a386121f84292f6fa663aaa3e570c15bc0240ea2),
`doc/leanvm/body/02-vm-specification.tex` lines 5-12 and
`crates/primitives/src/field/{gf2_64,gf2_64x3}.rs`.

Both fields are **computable**: `#guard` checks in `tests/LeanerVMTests/Parameters/Field.lean`
run the compiled arithmetic and agree with the reference vectors in the pinned Rust.

### Why this is not CompPoly's binary tower

CompPoly's `Fields/Binary/Tower/` builds `GF(2^64)` as an iterated quadratic extension
(`X^2 + Z_{k-1} X + 1` at each rung). leanVM's `K` is the *flat* quotient by a single
degree-64 polynomial. The two are abstractly isomorphic but use different bases, so their
bit-level encodings disagree — on the same bit patterns, `2 * 3` is `6` in `K` and `1` in the
tower's rung. Since the encoding appears in the hypotheses of leanVM's soundness theorems,
the tower instances are not a substitute. A polynomial-basis `GF(2^64)` does not currently
exist in CompPoly.

## Module map

| Module | Lines | Upstream disposition |
| --- | --- | --- |
| `Field/CarryLess.lean` | 132 | **Fully generic.** Upstream as-is. |
| `Field/BaseCertificate.lean` | 240 | Generated data; regenerate upstream. |
| `Field/Base.lean` | 171 | leanVM-specific modulus; generalisable. |
| `Field/Reduce.lean` | 193 | Partly generic; see below. |
| `Field/Carrier.lean` | 437 | Mostly generic pattern, leanVM constants. |
| `Field/Extension.lean` | 163 | leanVM-specific; thin over CompPoly. |

### `CarryLess.lean` — the cleanest upstream candidate

Width-generic carry-less multiplication over `GF(2)`. CompPoly's
`Fields/Binary/Common.lean` already supplies the `BitVec`-to-polynomial bridge
`BinaryField.toPoly` generically in the width, but fixes its own `clMul` at 128 bits for
`BF128Ghash`. This module lifts that restriction:

* `zeroExtendTo`, `toNat_zeroExtendTo`, `toPoly_zeroExtendTo` — widening preserves the
  denoted polynomial;
* `carryLessMul {v w}` — the product at an arbitrary result width;
* `toPoly_carryLessMul` — it denotes the product of the denoted polynomials, given
  `v + v ≤ w`;
* `toPoly_eq_range`, `toPoly_split` — `toPoly` as an `ℕ`-indexed sum, and splitting it at a
  bit position.

None of these mention leanVM. `toPoly_split` in particular is a much shorter proof than
`BF128Ghash`'s hardcoded `toPoly_split_256`, and could replace it.

**Suggested home:** `CompPoly/Fields/Binary/Common.lean`, or a sibling module.

### `Reduce.lean` — generic with one specialisation

The fold-based reduction of a double-width product back into the field. The structure is
generic; only the width (128 to 64) and the reduction constant are fixed.

Generic in substance:

* `highHalf`, `lowHalf`, their `testBit` lemmas, `toPoly_halves`, `highHalf_lt`;
* `carryLessMul_lt` — a degree bound on the product;
* `foldStep_mod` — a fold preserves the residue modulo the modulus;
* `foldStep_lt` — a fold shrinks the value;
* `reduce`, `toPoly_reduce` — two folds and a truncation compute the remainder.

To upstream, generalise over the width and take the modulus tail as a parameter. The pattern
mirrors `BF128Ghash`'s `fold_step` / `reduce_clMul` closely enough that a single generic
version could serve both.

### `Carrier.lean` — the pattern, with leanVM constants

The computable `BitVec 64` carrier and its algebraic structure. What is reusable here is the
*assembly pattern*, which follows `CompPoly.Extension.Ext`:

* `toQuot : Base → AdjoinRoot basePoly`, with `toQuot_add`, `toQuot_mul`, `toQuot_injective`,
  `toQuot_surjective`;
* `CommRing Base` written out **field-by-field**, each law proved by
  `toQuot_injective (by simp only [...])`;
* `Field Base` assembled around an explicit inverse.

`invItohTsujii` is the Itoh-Tsujii addition chain `1, 2, 3, 6, 7, 14, 15, 30, 31, 62, 63`,
transcribed from `gf2_64.rs`. `toQuot_invItohTsujii` proves it computes `a^(2^64 - 2)` and
`mul_invItohTsujii` that it inverts. `BF128Ghash` has the analogous chain for degree 128;
the two could share a generic skeleton parameterised by the chain.

### `Base.lean` and `Extension.lean` — the leanVM instances

`Base.lean` holds the modulus and its irreducibility. `Extension.lean` instantiates
CompPoly's `ExtensionParams` at degree 3 with lower coefficients `#v[1, 1, 0]`.

These are the parts that stay leanVM-specific. Upstream they would become a new concrete
field alongside `BF128Ghash`, in the shape of `CompPoly/Fields/Binary/BF64LeanVM/` or
similar.

## Load-bearing results

A reviewer should check these independently of whether the proofs compile.

| Result | Claim |
| --- | --- |
| `basePoly_irreducible` | `x^64 + x^4 + x^3 + x + 1` is irreducible over `GF(2)` |
| `card_K` | `Fintype.card K = 2 ^ 64` |
| `toPoly_carryLessMul` | the bit product denotes the polynomial product |
| `toPoly_reduce` | the fold-based reduction denotes the polynomial remainder |
| `Base.toQuot_mul` | carrier multiplication agrees with the quotient's |
| `Base.toQuot_injective` | distinct carrier values denote distinct field elements |
| `Base.mul_invItohTsujii` | the addition chain really inverts |
| `extensionPoly_irreducible` | `y^3 + y + 1` is irreducible over `K` |
| `extensionParams_poly` | the coefficient vector `#v[1, 1, 0]` denotes that cubic |
| `card_extension` | `Fintype.card E = 2 ^ 192` |

### Highest-risk items

Two are **transcriptions**, where a wrong constant compiles cleanly and silently yields a
different field. Audit them against the Rust and the specification rather than re-deriving:

1. `extensionParams_poly` — the `#v[1, 1, 0]` encoding of `y^3 + y + 1`.
2. `toPoly_reductionConstant` — `0x1B` denoting `x^4 + x^3 + x + 1`.

The third is a short characteristic-two calculation inside `extensionPoly_no_root`:
`a^7 = (a^3)^2 * a = (a+1)^2 * a = (a^2+1) * a = a^3 + a = (a+1) + a = 1`. The
`(a+1)^2 = a^2+1` step uses `CharTwo.add_sq`.

### How irreducibility is established

*Base modulus, degree 64.* Rabin's test via CompPoly's
`Polynomial.irreducible_of_rabin`, with both conditions discharged by a 96-step
square-and-multiply chain that the kernel replays (64 trace steps, 32 coprimality steps plus
a Bézout certificate). The data is generated by CompPoly's `scripts/gen_rabin_certificate.py`;
the exact command is recorded in `BaseCertificate.lean`'s module docstring. Nothing in the
certificate is trusted — wrong data fails to compile.

Note the composite-degree subtlety: `irreducible_of_rabin_prime_degree` is **unsound** at
degree 64, because a product of equal-degree factors would pass its collapsed condition. The
general `irreducible_of_rabin` is used, with `primeFactors_sixtyFour : (64 : ℕ).primeFactors = {2}`.

*Extension modulus, degree 3.* No certificate needed. A cubic is irreducible exactly when it
has no root; a root satisfies `a^7 = 1`, so its order divides both `7` and `|K^×| = 2^64 - 1`,
which are coprime, forcing `a = 1` — and `1` is not a root.

## Two traps worth carrying upstream

Both cost real time here and are easy to hit again.

**Module opacity blocks kernel reduction.** Under Lean's module system, a definition is
opaque across module boundaries unless marked `@[expose]`. Arithmetic that reduces fine in a
standalone file gets stuck under `decide` once it is imported. Every computable definition in
these modules carries `@[expose]` for this reason. CompPoly sidesteps it by putting
`@[expose] public section` at the top of each file.

**Transport instances silently destroy computability.** `Function.Injective.commRing` takes
the bridge map as *data*, so the resulting structure is noncomputable, and — because
`Monoid.toNatPow` then outranks the computable `Pow` — compiled arithmetic breaks. This
propagates: `Ext.mul` reaches through the base `Field`, so a noncomputable base field takes
the extension down with it, even though the base's own `*` still evaluates through its
standalone `Mul` instance. The fix is to write the instances out field-by-field, as
`Extension/Bridge.lean` documents and as `Carrier.lean` now does. The `#guard` tests exist
specifically to catch a regression here.

## Testing convention

`tests/LeanerVMTests/Parameters/Field.lean` follows `CompPolyTests.Fields.Extension`: base
vectors are checked with `decide +kernel`, extension vectors with `#guard` under
`public meta import`. `#guard` runs the *compiled* arithmetic, so it fails the build if an
instance ever regresses to noncomputable — which is the point.

Vectors are transcribed from `gf2_64.rs` lines 271-275 (three base triples) and
`gf2_64x3.rs` lines 990-1016 and 1026 (extension quadruples and the modulus check).

## Known gaps

* **`orderOf g = 2^64 - 1`** is not proved. leanVM addresses memory and bytecode by powers of
  the generator `g = x`, so this underpins the addressing model, and spec Lemma `lem:invcnt`
  (bus count soundness) also rests on `|K^×| = 2^64 - 1`. The arithmetic is verified
  numerically — `2^64 - 1 = 3 · 5 · 17 · 257 · 641 · 65537 · 6700417`, and `g^((2^64-1)/p) ≠ 1`
  for each `p` — and Mathlib's `orderOf_eq_of_pow_and_pow_div_prime` has the right shape, but
  the kernel cost of eight exponentiations is unmeasured. CompPoly has no certificate
  infrastructure for element order in a binary field.
* **E's limb API** — `limbs`, `ofBase`, and the Frobenius `x ↦ x^(2^64)` — is not built. The
  Frobenius should be *defined* semantically and the Rust's coefficient shuffle
  `(c0, c2, c1 + c2)` proved as a theorem, not taken as the definition.
* **The φ₈ embedding** `GF(2^8) ↪ K` (`phi8_tower.rs`) is deliberately out of scope: it is
  Flock-protocol-specific, not VM field structure.

## Dependency note

This work pins CompPoly to `2aa593725644fb0fe7c578be68cc5ec96bbc8dd2` on `main` rather than
the `v4.33.1` tag, because the tag predates the fast binary-tower commit
(`8e84a81`). ArkLib currently pins the tag, so the two will need reconciling if both enter a
build. Once this work lands upstream, the leanerVM side becomes a plain dependency bump.
