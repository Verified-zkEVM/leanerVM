**The claim to review: every irreducibility criterion in the library takes the field size as a
numeral, and there is exactly one form of each.** A concrete field supplies `ZMod.card _` and
states its conditions at the numeral its certificates were generated for; an abstract caller
passes `rfl` and gets the `Fintype.card F` statement back verbatim.

```lean
theorem irreducible_of_rabin {f : F[X]} {d q : ℕ} (hcard : Fintype.card F = q)
    (h_deg : f.natDegree = d) (h_pos : 0 < d)
    (h_trace : f ∣ X ^ (q ^ d) - X)
    (h_coprime : ∀ ℓ ∈ d.primeFactors, IsCoprime f (X ^ (q ^ (d / ℓ)) - X)) :
    Irreducible f
```

## Why

PR #306 gave the two KoalaBear Rabin certificates an `_of_card` wrapper so a concrete field
states its conditions at a numeral instead of casting each one with `rw [hcard]`; #307 corrected
the rationale, and #308 recorded the mechanism that does hold — a transport left around a
certificate whose type carries a huge exponent sent a cold replay into
`Polynomial.pow → npowRec → Nat.rec`, unfolding `X ^ (fieldSize ^ 6)` one exponent step at a time
until the deep-recursion guard fired.

That left the convention applied at two call sites and documented on a wiki page, with the
discoverable name — `irreducible_of_rabin` — still being the unsafe one: calling it with
`rw [ZMod.card 2]` elaborates, builds and tests clean, and surfaces only as a pathological cold
replay. **This PR removes the unsafe name rather than guarding it.** With one
numeral-parameterized form, the cast has no occasion to appear — for us, or for a downstream
author writing their own extension field, whom no linter of ours would ever have seen.

## The surface

| Criterion | File |
|---|---|
| `irreducible_of_rabin`, `rabin_of_irreducible`, `irreducible_iff_rabin` | `Data/Polynomial/Rabin.lean` |
| `irreducible_of_rabin_prime_degree`, `..._prime_power` (**new**), `..._two_prime_factors`, `..._degree_six` | `Data/Polynomial/RabinCertificate.lean` |
| `irreducible_X_pow_sub_C{,_iff}`, `irreducible_X_pow_four_sub_C{,_iff}` | `Fields/Extension/Binomial.lean` |
| `irreducible_dvd_X_pow_sub_X_iff_natDegree_dvd`, `..._add_X_...` (**new**, characteristic two) | `Data/Polynomial/Frobenius.lean` |

Thirteen names, not twenty-six: the `Fintype.card F`-only variants are gone, and so is the
`ERR_PCARD` lint rule that an earlier revision of this branch added to police them.

Two are new mathematics rather than restatements:

- **`irreducible_of_rabin_prime_power`.** `d = ℓ^k` has the single prime factor `ℓ`, so one trace
  plus one coprimality check at `q^(d/ℓ)` suffices — and unlike the prime-degree collapse it is
  *sound* at composite `d`, because every proper divisor of `ℓ^k` divides `ℓ^(k-1)`. It covers 4,
  8, 16, 64 and 128: every binary-field degree here and most binomial ones. `d` stays a separate
  parameter tied to `ℓ^k` by `hd_eq`, so conditions read at the caller's numeral (`q ^ 64`, not
  `q ^ 2 ^ 6`).
- **`irreducible_dvd_X_pow_add_X_iff_natDegree_dvd`.** The `+ X` spelling a binary field actually
  has, absorbing `CharTwo.sub_eq_add` at a statement generic in `c` and `n`. This is the same
  hazard one level down: rewriting *at a hypothesis* whose type carries a large exponent. The
  `Eq.mpr` is now kernel-checked once at variables and never instantiated at `2 ^ 128`.

Also filled in: `irreducible_of_rabin_two_prime_factors` and the general-degree binomial
criterion, which previously had no numeral form at all (the wiki recipe told composite-degree
callers to cast with `rw [hcard]`).

## Callers

- `Aes.modulus_irreducible` (`8 = 2^3`) and `BF64.basePoly_irreducible` (`64 = 2^6`) move onto the
  prime-power wrapper, each dropping its own `Nat.primeFactors` lemma and `intro ℓ hℓ; rw […];
  subst` enumeration.
- `BF128Ghash`'s degree-128 Rabin lemma applies the characteristic-two Frobenius form as a term in
  both directions, removing two rewrites at hypotheses typed `X ^ 2 ^ 128` and `X ^ 2 ^ 64`.
- The KoalaBear, BabyBear and Hachi extensions and the end-to-end certificate tests move to the
  single names.

`Extension/Binomial.lean` calls the Rabin layer with `rfl`, which is the abstract path exercised
in anger.

## Nothing is weakened

`rfl` for `hcard` must give back the `Fintype.card F` statement *verbatim*, so parameterizing by
`q` costs an abstract caller nothing and a later edit cannot quietly add a hypothesis or shift an
exponent. Pinned as `CardRflInstance` in
`tests/CompPolyTests/Data/Polynomial/{Rabin,RabinCertificate,Frobenius}.lean` and
`tests/CompPolyTests/Fields/Extension/Binomial.lean`, alongside a concrete `ZMod 5` caller that
needs no cast and a general-degree `X^2 - 2` case.

## Breaking change, and what is deprecated instead

Four `_of_card` names shipped in v4.33.1 and v4.34.0 —
`irreducible_of_rabin_prime_degree_of_card`, `irreducible_of_rabin_degree_six_of_card`,
`irreducible_X_pow_four_sub_C_of_card` and `irreducible_X_pow_four_sub_C_iff_of_card`. Each has a
signature identical to the plain name it collapsed into, so each survives as an
`@[deprecated (since := "2026-09-18")] alias`, per the deprecation policy in `CONTRIBUTING.md`.
Existing callers keep compiling, with a warning.

The one genuine break: the released `Fintype.card F`-only *signatures* of the plain names, whose
callers now gain one `hcard` argument (`rfl` for an abstract caller). No shim is possible or
wanted — an alias cannot express a signature change, and a deprecated old-signature theorem would
restore the spelling this PR removes and `AGENTS.md` now forbids. Checked before doing this: no repository outside CompPoly
references any of these names — ArkLib imports `CompPoly.Fields.KoalaBear.Ext6`, the field, not
the criteria, and a GitHub-wide search for `CompPoly.RabinCert`,
`irreducible_of_rabin_prime_degree` and the `_of_card` names returns nothing outside this repo.
Other consumers (`clean`, `z-lean`, `AeneasCompPoly`) pin tags and do not touch this surface.

## Docs

`docs/wiki/field-extensions.md` gains "The Field Size Enters As A Numeral": the surface table,
what each kind of caller passes, why no `Fintype.card F`-only variant exists, the
rewrite-at-a-hypothesis variant of the same hazard, and the #306 → #307 → #308 → #369 history.
Both "adding a new extension" recipes route through the single form; the composite-degree
`rw [hcard]` workaround the recipe used to recommend is gone. `AGENTS.md` states the rule as
design guidance ("state a new criterion at a numeral, and do not add a `Fintype.card F`-only
variant"); `binary-fields-and-ntt.md` and `scripts/README.md` follow.

## Validation

`lake build`, `lake test`, `lake exe axiomsweep --check` (10226 declarations, no sorry or
non-standard-axiom taint), `./scripts/check-imports.sh`, `./scripts/lint-style.sh` and
`scripts/check-docs-integrity.py` all pass.

## How this arrived at one form

Worth recording, because the discarded design is the one a reader might expect. The first attempt
kept the `Fintype.card F` statements and added a parallel `_of_card` wrapper beside each, plus a
`lint-style.py` rule (`ERR_PCARD`) banning the plain names under `CompPoly/Fields/` and
`tests/CompPolyTests/Fields/`. That works, and it is what #306 started, but it doubles the API and
polices a trap instead of removing it — and the policing stops at our repo boundary, so a
downstream author writing their own extension field still meets the unsafe spelling first.

Collapsing to one form was rejected at that point on the belief that it would break ArkLib.
Checking rather than assuming showed otherwise: ArkLib's 54 `import CompPoly` lines reach
`Fields.KoalaBear`, `Fields.BN254` and the univariate and multilinear surfaces, never
`Data.Polynomial.Rabin`, `RabinCertificate`, `Frobenius` or `Fields.Extension.*`, and its own
`irreducible_X_pow_sub_C_r` in `Data/Lattices/CyclotomicRing/` is an unrelated lemma. With that
premise gone, thirteen names and no enforcement machinery beat twenty-six names and a linter.

Both steps are separate commits on the branch while it is open, in case the intermediate state is
useful to look at; the description above is the design as merged.

🤖 Generated with [Claude Code](https://claude.com/claude-code)
