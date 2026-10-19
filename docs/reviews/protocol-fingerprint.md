# Review: the fingerprint and the collision bound

> An archive of the review of two commits on the branch `feat/protocol-fingerprint-collision`,
> `4a4e563` (Elias Judin's grand-product polynomial, carried from his fork commit `a932010`) and
> `63750a3` (the leanVM half), against their base `a100d8b` on `main`. Names, paths and line
> numbers are those of `63750a3`. What is accepted from it is text of the
> [protocol blueprint](../roadmap/protocol-blueprint.md), which is the specification, or of the
> pull request that met it.

**Disposition**:

| Finding | Disposition |
| --- | --- |
| 1. nothing shows that the factor 4 cannot be lowered | met: `SideProduct.lean` shows `{0}` and `{e₁₅}` collide at more than `3·|E|⁴` challenges (`fingerprint_e15`, `collide_iff`) |
| 2. the generic module cites the leanVM specification and uses protocol words | met: the citation and the `n = 4` remarks of `ToCompPoly/Fingerprint.lean` moved to `Fingerprint.lean`; `optionEquivLeft_rename_some` worded generically |
| 3. three public declarations with no production consumer | met: `natDegree_grandProductUnivariate` and `mapped_grandProduct_difference_ne_zero` deleted with their tests, `optionEquivLeft_rename_some` private |
| 4. test documentation left stale by the port, and the dropped tightness witness | met: both test headers rewritten, the dimension-zero count shown equal to its bound, the docstring and the comment fixed |
| 5. the bit order's authority is not cited, and the line range is off | met: `Fingerprint.lean` cites `:22-59`, Annex B `:278`, §8 `:9` and `leaf.rs:89-98` |
| 6. status page and reuse catalog short of the new results | met: the axioms sentence, the reuse catalog's two lines, and the owed blueprint edit recorded in the status |

Reviewed with the `adversarial-review` skill in three passes. Order of reading: the
specification first (`doc/leanvm/body/05-arithmetization.tex:18-59`, `03-proving-primitives.tex`
for `eq`, Schwartz–Zippel and Corollary `cor:idtest`, Annex B
line 278 and §8 line 9 for the bit order), then the pinned Rust (`crates/lean_vm/src/leaf.rs`:
`fingerprint_weights` :84-98, `build_leaves` :187-262, the challenge draws :673-680 and
:877-882, `soundness_degree_bound` :104-113), both with `git show a386121f:…` from the object
store of `/home/scaraven/Documents/leanEthereum/leanVM`, whose working tree is past the pin; then
the blueprint's Layer 5 and Layer 6 sections, the holes table, the conventions *Generic code*,
*Load-bearing checks*, *Trusted surface*, *Extractors*, *Errors*, acceptance tests 1 and 5;
then the Lean. Every changed Lean file was read in full from the branch with `git show`, with
`ToCompPoly/Fingerprint.lean`, `ToArkLib/SampleChallenge.lean`, `Spine/Errors.lean`,
`Spine/Instance.lean` and `Spine/Seams.lean` (the consumer's side), and Elias's original
`a932010` for the port diff. `audit-lean.sh`, `check-layers.sh` and `check-docs.py` pass;
`check-imports.sh` fails in the worktree only on the author's untracked `LeanerVM/Protocol/Bus.lean`
(later work, not on the branch). Three Lean processes were run, one at a time under the shared
`flock`, peak 3.4 GB: the branch's `SideProduct.lean` (every `#guard` and `example` passes), and a
probe (below) printing the axioms and checking the consumer's arithmetic. Nothing in the
repository was edited.

Target classification: no pull request exists yet and neither commit message classifies the
work. When it opens, the description should say: artifact, the bus fingerprint `π_α`, one side's
product, Lemma 5.2 (both directions) and Theorem 5.1 (the soundness direction of the product
check; its completeness is `congrArg`); Category A, written from §5.2, with the weights'
bit order cross-checked against `leaf.rs`; contribution to T4 through the bus phase's knowledge
soundness (`busSecurity`), which takes `card_sideProduct_collision_le` at the slot's first
challenge.

## Verdict in one paragraph

No theorem is wrong, vacuous or tautological, and the statements fit their consumer.
`fingerprint` is §5.2's `π_α(t) = Σ_{i<16} eq(α, i)·t_i` with `α_k` paired to bit `k` of `i`, low
bit first, which is exactly `fingerprint_weights` at the pin (`alphas[bit]` against
`(x >> bit) & 1`, `α + 1` for a clear bit); `sideProduct` is the product of `β − π_α(t)` over the
multiset, padding leaves of `1` contributing nothing. `sideProduct_poly_eq_iff` is Lemma 5.2 in
the blueprint's shape (`MvPolynomial (Option (Fin 4)) K`), and the substitution test bites: with
a sum in place of the product the lemma is false in characteristic two, which the test file
shows (`{t, t}` and `∅` both sum to `0`). `card_sideProduct_collision_le` is Theorem 5.1 counted:
`Nat.card {(α, β) // products equal} ≤ 4·N·|E|⁴` for `P ≠ Q` of at most `N` tuples each, the
multisets quantified outside the count, the two sizes allowed to differ. It is the shape
`Component.sampleChallengeSecurity` consumes (`Nat.card` of a subtype of the challenge type
`(Fin 4 → E) × E`, which is `busSpec`'s first challenge in the same order), the oracle (the
stack) fixes `P` and `Q` before the draw since the seams' witness is trivial
(`Spine/Seams.lean:152-168`), and the step from the count to the slot's error
`overE (4 * 2 ^ μBus)` is five lines (probe below). Every new result has the kernel's three
axioms and no `sorryAx`. The findings are all Low: the factor 4, which acceptance test 1 is
about, is pinned from above only (finding 1); the generic module still speaks the protocol's
language in its docstring (finding 2); a small audit-surface trim (finding 3); and documentation
left behind by the port (findings 4–6). Dropping Elias's probability and rational forms was
right (see Pass C).

## Findings, most severe first

### Low

**1. Nothing shows that the factor 4 cannot be lowered.** *Acceptance test 1; test quality.*
`card_sideProduct_collision_le` and `sideProduct_collision` (`Fingerprint.lean:94-133`) carry the
4, as acceptance test 1 asks, but the tests only instantiate the hypotheses
(`SideProduct.lean:75-84`) and `tests/…/GrandProductPoly.lean:60-64` pins the degree bound from
above. The nearby false reading the acceptance test names, error `2^μ/|E|`, is rejected by no
witness; so is the Rust's conservative `5·2^μ` (`leaf.rs:104-113`), which a later edit could
adopt without any test noticing (the slot's `overE (4 * 2 ^ μBus)` would then stop matching, but
only in Layer 6). The witness is cheap and shows the 4 is essentially tight: take `P = {0}` and
`Q = {e₁₅}` (one tuple each, `N = 1`, `e₁₅` the tuple with `1` at coordinate 15). Then
`π_α(e₁₅) = α₀α₁α₂α₃` and the colliding challenges are exactly `{(α, β) | α₀α₁α₂α₃ = 0}`, of
size `|E|·(|E|⁴ − (|E| − 1)⁴) = 4|E|⁴ − 6|E|³ + 4|E|² − |E|`, which exceeds `3·|E|⁴` once
`|E| ≥ 6`. Fix: a test that this count exceeds `3 * 1 * Nat.card E ^ 4` (so no constant below 4
holds for every pair), through `{α // ∀ i, α i ≠ 0} ≃ (Fin 4 → {e : E // e ≠ 0})` and `card_E`;
or, more cheaply but weaker, over `ZMod 2` with the generic theorem, where the same pair collides
at 30 of the 32 points against `1·1·2⁴ = 16`. Not run here.

**2. The generic module cites the leanVM specification and uses protocol words.** *The
*Generic code* convention.* `ToArkLib/GrandProductPoly.lean:33-38`: "Category A: leanVM
specification §5.2, Lemma 5.2 and Theorem 5.1, at `a386121f…` … whose proof of Lemma 5.2 is
`TODO`". The convention (`protocol-blueprint.md:324`) says a generic module carries no protocol
vocabulary and that "the special case is derived in a leanVM module, which cites the
specification"; it is the only `To*` module that cites leanVM (`git grep` over `To*/`), and
"Category A" is this repository's own classification, meaningless to ArkLib.
`Fingerprint.lean:20-40` already carries the citation, the `TODO` remark and the authoring note.
The lemma `optionEquivLeft_rename_some` (`:59-67`) is a fact about any `MvPolynomial`, but its
docstring speaks of "fingerprint variables" and "the product variable". Pre-existing, from #39 and
outside this diff, but completed by it: `ToCompPoly/Fingerprint.lean:34-37` ("At `n = 4`, the
input has sixteen coordinates…") and `:129-130` ("For sixteen-coordinate tuples, this remains
four") are the leanVM reading, which now has its own module. Fix: keep in `GrandProductPoly.lean`
the generic description, the pointer to `ToCompPoly/Fingerprint.lean` for the leanth derivation,
and ArkLib #901; move the §5.2 sentence to `Fingerprint.lean` (it is there); word the lemma's
docstring generically ("renaming by `some` lands in the constant coefficients"); move the two
`n = 4` remarks to `Fingerprint.lean`.

**3. Three public declarations with no production consumer.** *Audit surface.*
`GrandProductPoly.lean` has thirteen public declarations and no private one. Two are used only by
tests: `natDegree_grandProductUnivariate` (`:112-117`, `tests/…/GrandProductPoly.lean:66-71`) and
`mapped_grandProduct_difference_ne_zero` (`:148-157`, a two-line composition of
`grandProduct_difference_ne_zero` and `map_tupleMultiset_injective`, used at
`tests/…:113-116`). `optionEquivLeft_rename_some` (`:59-67`) is a Mathlib-level lemma (Mathlib
has `optionEquivLeft_X_some`, `optionEquivLeft_C`, but not this one) published as
`LeanerVM.Protocol.optionEquivLeft_rename_some`; under `open MvPolynomial` it would become
ambiguous the day Mathlib adds the same name. The remaining helpers (`grandProductUnivariate`,
`optionEquivLeft_grandProductPoly`, `roots_grandProductUnivariate`, the degree lemmas) are the
reusable API an upstream library wants and should stay. Fix: delete the two test-only
declarations (or make them `private` and drop their tests), and make
`optionEquivLeft_rename_some` private.

**4. Test documentation left stale by the port, and the dropped tightness witness.** *Hygiene;
test quality.* (a) `tests/LeanerVMTests/Protocol/GrandProductPoly.lean:4` ("joint-challenge
collision bounds") and `:15-18` ("the probability bound concerns a fresh uniform joint point")
describe Elias's probability theorem, which the port removed, and the file now tests no collision
count. (b) The test removed with it (`a932010`, the dimension-zero `{#v[0]}` against `0` over
`ZMod 2`) was the one witness that the generic bound is attained: `max 1 0 · 1 · 2⁰ = 1`
collision, and the pair collides at exactly the point `x none = 1`. Its count-form replacement
is two lines on `card_grandProduct_collision_le`. The example at `:27-31`, which shows that
collision at the point, has no comment. (c) `card_grandProduct_collision_le`'s docstring
(`GrandProductPoly.lean:172`) still says "Counting form of …", naming a sibling that is gone.
(d) `SideProduct.lean:11-13` cites "acceptance test 5", a roadmap reference in a Lean comment,
and overstates: the acceptance test's witness is the leanISA instance's flush polynomials (Layer
3); this test pins that the fingerprint reads coordinate 0, which is necessary for it. Fix:
rewrite the GrandProductPoly test header for what it tests, restore the dimension-zero witness as
an equality of the count with `1`, drop "Counting form of", and say "coordinate 0, the
separator, enters the fingerprint" without the acceptance-test number.

**5. The bit order's authority is not cited, and the line range is off.** *Fidelity
citations.* `Fingerprint.lean:20-24` and `:50-51` assert "low bit first" and cite only §5.2,
whose `eq(α, i)` with an integer `i` does not fix the order; the specification fixes it
elsewhere (Annex B, `b-polynomial-commitment-scheme.tex:278`, `⟨u⟩ := Σ u_i 2^i`; §8,
`08-end-to-end-protocol.tex:9`, "bits low first"), and the deployed verifier computes it in
`leaf.rs:89-98`. The weights are wire-level: the compiled verifier must rebuild the same leaves
as the Rust, so the order is Category B even though the security statement is Category A. The
two agree (checked; the `#guard`s at `SideProduct.lean:46-48` pin it, and would catch a
high-bit-first or complemented mutation). The cited range `05-arithmetization.tex:23-62` starts
one line after the fingerprint sentence (line 22) and runs past the section's end (59; 61 is
§5.3). Fix: cite `:22-59`, Annex B's line for the order, and `crates/lean_vm/src/leaf.rs:89-98`
as the implementation the order matches.

**6. Status page and reuse catalog short of the new results.** *Documentation.*
(a) `docs/roadmap/protocol-status.md:35-37`: the `#print axioms` sentence lists the master
theorems, the commit phase and the public-input phase; add `sideProduct_poly_eq_iff`,
`card_sideProduct_collision_le` and `sideProduct_collision` (verified here: `propext`,
`Classical.choice`, `Quot.sound`). (b) `docs/roadmap/leanth-reuse.md:446-448` (the sentence ending at :448) still lists "the
fingerprint lemmas (Layer 5, S; #39)" as a next port candidate; #39 is merged and this branch
completes the hole, and the Layer 5 table's `unbalanced_rejected` row (`:147`) should say the
count was written new on ArkLib's Schwartz–Zippel rather than ported. (c) The blueprint's
Interfaces list (`protocol-blueprint.md:1473`) and Layer 5 file line (`:843`) are behind the
built work (`card_sideProduct_collision_le` is the interface the bus phase uses; the leanVM
reading is in `Fingerprint.lean`, not `ToArkLib/GrandProduct.lean`); the status entry at
`:209-216` records the deviation, which is the right place until a `docs(protocol)` pull request
edits the blueprint; say there that the blueprint edit is owed.

### Observations

- **Consumer bridge.** The bus slot needs `((4 * 2^μ * Nat.card E ^ 4 : ℕ) : ℝ≥0) /
  Nat.card ((Fin 4 → E) × E) = overE (4 * 2^μ)` to turn `sampleChallengeSecurity`'s error into
  `busError`'s first entry. It is five lines (`Nat.card_prod`, `Nat.card_fun`,
  `mul_div_mul_right`; probe below). It belongs in `Bus.lean`, which imports both
  `Spine/Errors.lean` and this module; nothing to add here.
- **The pull side's cap.** The theorem allows unequal sizes, which is the right shape: the
  push side's length is `pushLeaves ≤ 2^μBus` by `μBus`'s definition, but the pull side's is not
  bounded by the instance (`Spine/Instance.lean`, `μBus`'s docstring: "the bus phase assumes it").
  Layer 6 will have to supply `(I.tuples q .pull).length ≤ 2 ^ I.μBus`; the blueprint's
  `busPhase` signature carries only `h₁` and `h₂`.
- **Non-load-bearing tests.** The order example (`SideProduct.lean:70-73`) proves
  `↑[u, v] = ↑[v, u]` as multisets and says nothing about `sideProduct`; the guard
  `fingerprint α t + fingerprint α t = 0` (`:62`) holds of any element of `E`. Both document a
  point (a product of a multiset; why a sum would not do) rather than test a definition. Harmless.
- **Test file names.** The tests of `Protocol/Fingerprint.lean` are in `SideProduct.lean`, while
  `tests/…/Protocol/Fingerprint.lean` tests `ToCompPoly/Fingerprint.lean`. A reader looking for
  the leanVM module's tests by name finds the generic ones.
- **Credit.** Elias Judin is the author of `4a4e563`, and the port is faithful: the diff against
  `a932010` is the path and import change, the module docstring, and the deletion of the three
  probability and fraction theorems with their one test; every other line is his. If the pull
  request is squash-merged, the squash message should keep `Co-authored-by: Elias Judin
  <ejudin@gmail.com>`. `GrandProductPoly.lean` holds no leanth-derived code (`fingerprintPoly` is
  imported), so it needs no derived-source notice, and it has none.
- **Rust's `5·2^μ`.** `soundness_degree_bound` charges `(N_TUPLE_BITS + 1)·2^μ`, summing the
  degrees in `α` and `β`; the total degree is 4 and §5.2 says so. Already recorded in
  `docs/leanvm-target.md:132`; the Lean follows the specification, correctly.
- **Extractors.** `fingerprint` and `sideProduct` are computable (the `#guard`s run them), so the
  bus phase's verifier and its computable extraction are not obstructed; `grandProductPoly` is
  `noncomputable` but appears only in proofs and in the polynomial lemma.

## Pass A: the statements

Read against §5.2 and Corollary `cor:idtest` before the proofs.

- **`fingerprint α t`** (`Fingerprint.lean:52-53`): `Σ_{i<16} (lagrangeBasis (ofFn α))[i] ·
  ofK t[i]`. Through `fingerprint_eq_eval₂Mle` and `eval₂_fingerprintPoly`
  (`ToCompPoly/Fingerprint.lean:54-58`, by `lagrangeBasis_getElem_nat`), it is
  `Σ_i t_i · Π_k (testBit i k ? α_k : 1 − α_k)`, which is §5.2 with Definition `def:eq`'s
  `eq(X, Y) = Π (1 + X_k + Y_k)`. Trusted, one screen, cites §5.2.
- **`sideProduct α β P`** (`:65-66`): `Π_{t ∈ P} (β − π_α(t))` over a `Multiset`, so
  multiplicities count (guard `:58-59`), and order cannot (it is a multiset).
- **`sideProduct_poly_eq_iff P Q`** (`:81-83`): `grandProductPoly P = grandProductPoly Q ↔ P = Q`
  in `MvPolynomial (Option (Fin 4)) K`, `X` at `none`, `A_i` at `some i`; Lemma 5.2 with
  coefficients in `K` as the specification states it. No hypothesis, so nothing to make vacuous.
  The reverse direction is `congrArg`; the forward is `grandProductPoly_injective`: over a domain,
  `Π (X − C(π_A t))` is monic in `X` over `K[A]` with roots exactly the `π_A t`
  (`Polynomial.roots_multiset_prod_X_sub_C`), and `fingerprintPoly` is injective (Boolean
  evaluation). No characteristic hypothesis, as the specification needs in characteristic 2.
  Substitution test: with sums in place of products the statement is false (`{t, t}` and `∅`).
- **`card_sideProduct_collision_le hne hP hQ`** (`:94-115`): for `P ≠ Q`, `P.card ≤ N`,
  `Q.card ≤ N`, `Nat.card {ab : (Fin 4 → E) × E // sideProduct ab.1 ab.2 P = sideProduct ab.1
  ab.2 Q} ≤ 4 * N * Nat.card E ^ 4`. Direction right (an upper bound on the bad set), quantifiers
  right (the multisets before the challenge; the challenge joint and uniform in the probability
  form, as Theorem 5.1 says), the factor the total degree `max 1 4 = 4`, the cap per side. The
  proof maps both multisets to `E` (injective `algebraMap`), applies ArkLib's counting
  Schwartz–Zippel to `Π_P − Π_Q` of total degree `≤ 4N`, and transports along the private
  `(Fin 4 → E) × E ≃ (Option (Fin 4) → E)`. Non-vacuous: inhabited at `{t}`, `{t, t}`, `N = 2`
  (`SideProduct.lean:75-78`). Over-strengthening: none; the hypotheses are what the bus phase has
  (push side by `μBus`'s definition, pull side by the phase's assumption, see Observations).
- **`sideProduct_collision`** (`:119-133`): the same at VCVio's uniform `$ᵗ ((Fin 4 → E) × E)`,
  `Pr ≤ (4N : ℕ) / |E|`, by `prEvent_uniformSample_le_div_iff` in the direction that matters.
  This is the blueprint's bold name; the bus phase will use the counting form.
- **The generic half** (`GrandProductPoly.lean`): `card_grandProduct_collision_le` over any
  finite field at `max 1 n · cap · |F|ⁿ` of `|F|ⁿ⁺¹` points, the multisets fixed first, sizes
  allowed to differ, dimension zero included. Its test of a correlated `β` (`tests/…:51-58`,
  `β = α₀` makes `{(0,1)}` and `{(0,1),(0,1)}` collide everywhere) shows the independence
  hypothesis is doing work.
- **Coverage.** Lemma 5.2 both directions; Theorem 5.1 soundness (completeness is equal
  multisets give equal products, immediate). Nothing of the specification's §5.2 is left out.

## Pass B: fidelity

Category A for the statements, with the fingerprint's weights wire-level and so checked against
the Rust as a transcribed encoding. Read: §5.2 at `a386121f`
(`05-arithmetization.tex:18-59`), `leaf.rs` at `a386121f` as listed above.

| Item | Specification | Rust (`leaf.rs`) | Lean |
| --- | --- | --- | --- |
| tuple width | `m = 16`, zero-padded | `1 << N_TUPLE_BITS = 16` weights (:91, :102) | `Vector K 16`; padding is the instance's flush polynomials |
| challenges | `α ∈ E⁴`, then `β ∈ E` | `α₀ … α₃` squeezed, then `β` (:673-680, :877-882) | one joint challenge `(Fin 4 → E) × E`, `α` first (`busSpec`) |
| weight of slot `x` | `eq(α, x)` | `Π_bit (x>>bit)&1 ? α_bit : α_bit + 1` (:89-98) | `lagrangeBasis (ofFn α)[x]`, `α_k` with bit `k` |
| leaf | `β − π_α(t)` | `β + Σ w_i c_i` (:227, :246), equal in characteristic 2 | `β − fingerprint α t` |
| padding leaf | `1` | `F192::ONE` (:223) and implicit to `2^μ` | not a factor of the multiset product |
| error | `4·2^μ/|E|` (total degree 4) | `5·2^μ` grinding bound (:104-113) | `4·N/|E|`; the Rust's looser bound recorded at `leanvm-target.md:132` |

Counts: 16 weights on each side; 5 field challenges on each side (the joint draw is the spine's
decision, a Fiat–Shamir concern for Layer 12); one leaf form. No coordinate, weight or factor
present on one side and absent on the other. The only divergence is the Rust's conservative
degree, already recorded. The bit order agrees with the Rust and with the specification's global
convention; its citation is finding 5.

## Pass C: hygiene and policy

- **To-folder rule.** The code of `GrandProductPoly.lean` is generic (any `CommRing R`, any `n`,
  any finite field), names no protocol constant, and sits in `ToArkLib/` by its imports
  (ArkLib's Schwartz–Zippel counting over CompPoly's tables), as the destination criterion asks;
  the `n = 4`, `K`, `E` reading is in the leanVM module. The docstring is not (finding 2).
- **Dropping Elias's probability and rational forms.** Right. `prob_grandProduct_collision_le`
  used a `Pr_{let x ←$ᵖ …}` notation that no package at the current pins defines (no `$ᵖ`
  anywhere in `.lake/packages`; the commit message calls it Mathlib's, which it was not at these
  pins, a slip of no consequence); restating it on VCVio would need a sampler on
  `Option (Fin n) → F` that no consumer uses. `uniform_grandProduct_collision_fraction_le` is the
  counting form divided out in `ℚ`, with no consumer. `uniform_grandProduct16_collision_fraction_le`
  is the `n = 4` special case, which the convention forbids in a generic module. The consumer takes
  the count (`sampleChallengeSecurity`), and the blueprint's probability statement exists at the
  leanVM level (`sideProduct_collision`). What was lost is the dimension-zero tightness witness
  (finding 4b).
- **Comments.** Fingerprint.lean's docstrings are one or two lines, self-contained, cite the
  specification and no roadmap. One roadmap reference in a test comment (finding 4d).
- **Surface.** `Fingerprint.lean`: two definitions and five theorems public, the equivalence
  private; right. `GrandProductPoly.lean`: finding 3.
- **Aggregates.** Both new modules appear once each, in order, in `LeanerVM.lean` and
  `tests/LeanerVMTests.lean`. No line over 100 columns. `SideProduct.lean` is a plain file so its
  `#guard`s run compiled code, as `CONTRIBUTING.md` asks.
- **Status page.** The table's hashes (`24860c3`, `c9bd599`, `7d8252d`, `a100d8b`) match `main`;
  "what can start now" now lists the bus phase, which is right (its definition needs the GKR's
  definition, on `main`, and tables and stacking). Finding 6 for what is missing.

## Probe

Run with `flock /tmp/claude-1000/leanerVM-lean.lock lake env lean`, from the worktree at
`63750a3` (whose only difference from the branch is the author's later `Stacking.lean` and
untracked `Bus.lean`, neither imported here).

```lean
import LeanerVM.Protocol.Fingerprint
import LeanerVM.Protocol.Spine.Errors
open LeanerVM.Parameters LeanerVM.Protocol
open scoped NNReal

#print axioms LeanerVM.Protocol.sideProduct_poly_eq_iff        -- and the four below:
#print axioms LeanerVM.Protocol.card_sideProduct_collision_le  -- all [propext, Classical.choice,
#print axioms LeanerVM.Protocol.sideProduct_collision          --      Quot.sound]
-- (also fingerprint_eq_eval₂Mle, sideProduct_eq_eval₂, card_grandProduct_collision_le,
--  grandProductPoly_injective)

example (N : ℕ) :
    ((4 * N * Nat.card E ^ 4 : ℕ) : ℝ≥0) / (Nat.card ((Fin 4 → E) × E) : ℝ≥0) =
      overE (4 * N) := by
  have hE : (Nat.card E : ℝ≥0) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]; exact_mod_cast Fintype.card_ne_zero
  rw [overE, ← Nat.card_eq_fintype_card, Nat.card_prod, Nat.card_fun, Nat.card_fin]
  push_cast
  rw [mul_comm ((Nat.card E : ℝ≥0) ^ 4) (Nat.card E : ℝ≥0),
    mul_div_mul_right _ _ (pow_ne_zero 4 hE)]

example {P Q : Multiset (Vector K 16)} (hne : P ≠ Q) (μ : ℕ)
    (hP : P.card ≤ 2 ^ μ) (hQ : Q.card ≤ 2 ^ μ) :
    Nat.card {ab : (Fin 4 → E) × E // sideProduct ab.1 ab.2 P = sideProduct ab.1 ab.2 Q} ≤
      4 * 2 ^ μ * Nat.card E ^ 4 :=
  card_sideProduct_collision_le hne hP hQ

example (l₁ l₂ : List (Vector K 16)) (h : ¬ l₁.Perm l₂) :
    (l₁ : Multiset (Vector K 16)) ≠ l₂ := fun he ↦ h (Multiset.coe_eq_coe.mp he)
```

All three examples compile; the last is the step from the spine's `Balanced` (a `List.Perm`) to
the theorem's `P ≠ Q`.
