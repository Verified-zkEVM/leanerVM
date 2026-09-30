# Dossier lib-others: VCVio, CompPoly, Clean, Mathlib and Layer 0 of the proof system

Task: lib-others. Revisions: leanerVM `main` at `b435631`; VCVio `f9dc47d9`, CompPoly `3468b38c`,
Clean `93c9d1ef`, Mathlib `v4.33.1` (all under `.lake/packages/`); leanVM at `a386121f`.
Upstream `main` clones (for section F only) under `probes/lib-others/upstream/`.

**Two revisions.** The object is leanerVM `main` at `b435631` with the old pins above; every
Lean line number is at `b435631` and every library citation names its revision. On 2026-09-30 at
09:18 the owner merged `main` `144c5aa` ("chore(deps): upgrade to Lean 4.34.1 (#61)") into the
checkout, moving the pins to CompPoly `572f9973`, VCVio `a4232d08`, Clean `42fe4b26`, ArkLib
`7653a901`, Mathlib/Lean `v4.34.1` (brief §8). Old-pin sources were read with
`git -C .lake/packages/<pkg> show <old>:<path>`; what the upgrade changes is in E.1, E.3, E.4,
F.3 and G.5-G.10. Sections A-D describe the old pins; their new-pin differences are in F.3. All
seven probes (H) ran at the old pins; none could be re-run.

## Summary

**Examined.** The library objects the proof system's statements unfold to: VCVio's oracle
computations and probability (A), CompPoly's tables, polynomials and the two fields (B), Clean's
circuit/bus layer and its balance argument (C), Mathlib's notions and Lean's trusted base (D);
Layer 0 of the proof system (`Protocol/Field.lean`, `Basic.lean`, `ToArkLib/Oracles.lean`,
`ToVCVio/UniformSample.lean`, tests), declaration by declaration, against the blueprint (E);
upstream duplicates and what has landed since the pins (F). Seven probes (H).

**Conclusions.**
1. **The fields are leanVM's, bit for bit.** `K = GF(2)[x]/(x^64+x^4+x^3+x+1)` as 64-bit words
   (bit `i` = coefficient of `x^i`) and `E = K[y]/(y^3+y+1)` as limb triples `c0 + c1·y + c2·y²`
   agree with the specification, the Rust and the Python in modulus, encoding, limb order,
   embedding and generator; leanerVM's compiled arithmetic reproduces all eleven Rust reference
   products (probe `FieldFidelity`). Irreducibility, field laws and `|E| = 2^192` are proved in
   CompPoly on the standard axioms.
2. **Challenges are uniform by proof.** Uniformity is a law of VCVio's `SampleableType` class,
   so no instance can be non-uniform; both samplers are transports along bijections and probe
   `Layer0` derives `Pr[= x | $ᵗ E] = 2^-192`. The instance diamond on `K` (VCVio's `FinEnum`
   sampler) is definitionally the same term (probe `SamplerDiamond2`); `E` has one instance. The
   `K` sampler has no consumer (every leanVM challenge is in `E`).
3. **The column oracle answers the specification's evaluation**: query `r ∈ E^μ`, answer
   `q̃(r) = Σ_i ofK(q_i)·eq(r,i)`, in the specification's little-endian cube order; the counting
   bounds are correct, tight and load-bearing (probe `CountingBounds`), and their restatement on
   VCVio's new `Pr{…}[…]` is the same statement.
4. **Clean's balance is unsatisfiable, not merely unsound, over `K`**: the field sum accepts a
   tuple pushed twice and never pulled, and the side condition `length < ringChar K = 2` rejects
   every channel with two interactions, so `Ensemble.Statement` holds of no real ensemble (probe
   `CleanBalance`); unchanged at Clean `42fe4b26`. leanISA's `BalancedPair` (`List.Perm`, counted
   in ℕ) is the workaround, retired when Clean #464 (open) lands and leanerVM adopts directed
   channels.
5. **The trusted base is the kernel and the three standard axioms**, enforced lexically and
   transitively over both project namespaces with a negative control; `#guard` tests are
   compiled-code evidence, not proof. The old-pin `simp` hazard on `K` was caught by the kernel
   (probe `NumeralHazard`).
6. **The upgrade changes the meaning of numerals**: at CompPoly `572f9973` `BF64` is a structure
   and `(2 : K) = 0`; words are `K.ofBits n`. Old-pin probes and fixtures written with numerals
   mean something else there; #61 converted the fixtures. It also lifts the eager-`Fintype`
   blocker on executables (`Fintype K` is now proof-only).

**Findings by severity.** Critical: none. Major: none. Minor: the relation ladder conflates
Clean's field sum with its balance relation (G.1); `SampleableType K` is unused and the blueprint
disagrees with itself about it (G.2); `evalOracle_answer` takes `n` explicitly (G.3); the scalar
oracle interfaces are unlisted trusted surface (G.4); Layer 0 prose is stale after #61 (G.5).
Notes: the eager `Fintype` blocker, retired (G.6); `simp` misreading `K`, retired (G.7); numerals
changed meaning (G.8); ArkLib's MLE bridge likely clashes with CompPoly at the new pins,
unverified (G.9); the local counting bound is redundant upstream at the new pin (G.10).

---

## A. VCVio at the pin `f9dc47d9`: what a probability statement means

VCVio is the library of *oracle computations* on which ArkLib states every security notion.
All snippets below are copied from `.lake/packages/VCVio/` at `f9dc47d9`
(`git log -1`: "feat(complexity): add honest oracle-PPT foundations and measure-native OTP (#545)").

### A.1 `OracleSpec`: the list of oracles a computation may call

An oracle specification names a set of oracles by an index type `ι` and gives, for each index
(each possible query), the type of the answer. It is nothing more than a function to types.

`VCVio/OracleComp/OracleSpec.lean:27-30`
```lean
/-- An `OracleSpec ι` specifies a set of oracles indexed by `ι`.
Defined as a map from each input to the type of the oracle's output. -/
def OracleSpec (ι : Type u) : Type (max u (v + 1)) :=
  ι → Type v
```
`A →ₒ B` is the specification of one oracle with queries in `A` and answers in `B`
(`OracleSpec.lean:84-85`: `notation:25 (name := singletonSpec) A:25 " →ₒ " B:26 =>
OracleSpec.ofFn (ι := A) (fun _ => B)`). The empty specification (no oracle at all) is

`VCVio/OracleComp/OracleSpec.lean:215-217`
```lean
/-- Specifies access to no oracles, using the empty type as the indexing type. -/
@[reducible] def emptySpec : OracleSpec PEmpty := PEmpty →ₒ PEmpty
notation "[]ₒ" => emptySpec
```
and the source of all randomness is the specification of uniform choices from `Fin (n+1)`:

`VCVio/OracleComp/OracleSpec.lean:233-236`
```lean
/-- Access to oracles for uniformly selecting from `Fin (n + 1)` for arbitrary `n : ℕ`.
By adding `1` to the index we avoid selection from the empty type `Fin 0 ≃ empty`. -/
@[inline, reducible] def unifSpec : OracleSpec ℕ :=
  OracleSpec.ofFn fun n => Fin (n + 1)
```

### A.2 `OracleComp` and `ProbComp`: programs that call oracles

`OracleComp spec α` is a program returning an `α` that may call the oracles of `spec`. It is a
*free monad*: a syntax tree whose nodes are "query `t`, then continue with the answer". It has no
meaning by itself; a meaning is supplied by interpreting the queries (A.3, A.4).

`VCVio/OracleComp/OracleComp.lean:23-29`
```lean
/-- `OracleComp spec α` represents computations with oracle access to oracles in `spec`,
where the final return value has type `α`, represented as a free monad over the `PFunctor`
corresponding to `spec.` -/
@[reducible]
def OracleComp {ι : Type u} (spec : OracleSpec.{u, v} ι) :
    Type w → Type (max u v w) :=
  PFunctor.FreeM spec.toPFunctor
```
A *probabilistic* computation is one whose only oracle is the uniform-choice oracle:

`VCVio/OracleComp/ProbComp.lean:42-45`
```lean
/-- Simplified notation for computations with no oracles besides random inputs.
This specific case can be used with `#eval` to run a random program, see `OracleComp.runIO`.
NOTE: Need to decide if this should be more opaque than `abbrev`, seems like no as of now.. -/
abbrev ProbComp : Type → Type := OracleComp unifSpec
```
with the primitive coin `$[0..n]` (`ProbComp.lean:55-58`:
`def uniformFin (n : ℕ) : ProbComp (Fin (n + 1)) := unifSpec.query n`).

**Failure.** An `OracleComp` tree has no failure node: it always returns. Failure (a verifier
rejecting, a guard not met) is added by Lean's `OptionT` monad transformer, `OptionT m α =
m (Option α)`, where `none` means "failed". ArkLib's verifiers run in
`OptionT (OracleComp oSpec)`. VCVio sends `none` to the "missing mass" of a sub-distribution:

`ToMathlib/ProbabilityTheory/SPMF.lean:55-58`
```lean
/-- A subprobability mass function is a function `α → ℝ≥0∞` such that values have an infinite
sum at most `1` represented by applying an `OptionT` transformer to the `PMF` monad.
The new `failure`/`none` value holds the "missing" mass to reach the total sum of `1`. -/
def SPMF : Type u → Type u := OptionT PMF
```
`VCVio/EvalDist/Instances/OptionT.lean:126-131`
```lean
/-- Lift a `MonadLiftT m SPMF` instance to `MonadLiftT (OptionT m) SPMF`. Failure in `OptionT`
contributes to the failure mass of the resulting `SPMF`. -/
noncomputable instance instMonadLiftTSPMF (m : Type u → Type v) [Monad m]
    [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] :
    MonadLiftT (OptionT m) SPMF where
  monadLift x := OptionT.mapM' (MonadHom.ofLift m SPMF) x
```
(`PMF` is Mathlib's type of probability mass functions: a function `α → ℝ≥0∞` summing to 1.)

### A.3 `QueryImpl` and `simulateQ`: answering the queries

A `QueryImpl spec m` answers every query of `spec` by a computation in another monad `m`;
`simulateQ impl oa` replaces every query node of `oa` by its answer. This is how ArkLib's
challenger answers "give me challenge `i`" by a uniform sample, and how an oracle is implemented
from the message it stands for.

`VCVio/OracleComp/SimSemantics/QueryImpl/Basic.lean:30-37`
```lean
/-- A monadic handler for the polynomial interface induced by `spec`.

Concretely, this maps every oracle input `x` to a computation returning an
answer of type `spec.Range x`. It extends first to `OracleQuery spec` by
applying the continuation, then to `OracleComp spec` by preserving `pure` and
`bind`; see `QueryImpl.mapQuery` and `simulateQ`. -/
@[reducible] def QueryImpl {ι} (spec : OracleSpec ι) (m : Type u → Type v) :=
  (x : spec.Domain) → m (spec.Range x)
```
`VCVio/OracleComp/SimSemantics/SimulateQ.lean:27-31`
```lean
/-- Given an implementation of `spec` in the monad `r`, convert an `OracleComp spec α` to a
implementation in `r α` by substituting `impl t` for `query t` throughout. -/
def simulateQ {ι} {spec : OracleSpec ι} {r : Type u → Type _} [Monad r]
    (impl : QueryImpl spec r) {α : Type u} (mx : OracleComp spec α) : r α :=
  PFunctor.FreeM.liftM impl mx
```

### A.4 The distribution of a computation, `Pr[…]`, and the support

The **distribution** of an `OracleComp` is obtained by `simulateQ` with every query answered by a
fixed distribution on its answers. For `unifSpec` (hence every `ProbComp`) that distribution is
the uniform distribution on `Fin (n+1)`, declared once:

`VCVio/OracleComp/EvalDist.lean:71-80`
```lean
@[reducible] noncomputable def IsUniformSpec.ofFintypeInhabited
    {ι : Type u} (spec : OracleSpec ι)
    [hF : spec.Fintype] [hI : spec.Inhabited] : IsUniformSpec spec where
  toPMF t := PMF.uniformOfFintype (spec.Range t)
  fintype := hF
  inhabited := hI
  toPMF_eq_uniform _ := rfl

noncomputable instance : IsUniformSpec unifSpec := IsUniformSpec.ofFintypeInhabited _
```
`VCVio/OracleComp/EvalDist.lean:146-147`
```lean
lemma evalSPMF_eq_simulateQ [IsProbabilitySpec spec] (mx : OracleComp spec α) :
    𝒮[mx] = simulateQ IsProbabilitySpec.toPMF mx := rfl
```
The probabilities are then read off that sub-distribution:

`VCVio/EvalDist/Defs/Basic.lean:114-140`
```lean
def probOutput [MonadLiftT m SPMF] (mx : m α) (x : α) : ℝ≥0∞ :=
  evalSPMF mx x
...
noncomputable def probEvent [MonadLiftT m SPMF] (mx : m α) (p : α → Prop) : ℝ≥0∞ :=
  (evalSPMF mx).run.toOuterMeasure (some '' {x | p x})

/-- Probability that a computation `mx` will fail to return a value. -/
def probFailure [MonadLiftT m SPMF] (mx : m α) : ℝ≥0∞ :=
  (evalSPMF mx).run none

/-- Probability that a computation returns a particular output. -/
notation "Pr[= " x " | " mx "]" => probOutput mx x

/-- Probability that a computation returns a value satisfying a predicate. -/
macro (name := probEventNotation) "Pr[ " p:term " | " mx:term "]" : term =>
  `(probEvent $mx $p)

/-- Probability that a computation fails to return a value. -/
notation "Pr[⊥" " | " mx "]" => probFailure mx
```
So `Pr[= x | mx]` is the probability that `mx` returns `x`, `Pr[p | mx]` the probability that it
returns a value satisfying `p` (failure never satisfies an event), `Pr[⊥ | mx]` the probability
that it fails; all are extended non-negative reals (`ℝ≥0∞`). The **support** is the set of
values a computation can return, computed syntactically (every answer allowed at every query):

`VCVio/EvalDist/Defs/Support.lean:42-44`
```lean
/-- The set of possible outputs of running the monadic computation `mx`. -/
def support [MonadLiftT m SetM] {α : Type u} (mx : m α) : Set α :=
  SetM.run (liftM mx)
```

### A.5 `SampleableType` and `$ᵗ`: uniform sampling, with uniformity as a law

`VCVio/OracleComp/Constructions/SampleableType.lean:37-53`
```lean
/-- A `SampleableType β` instance means that `β` is a finite inhabited type,
with a computation `selectElem` that selects uniformly at random from the type.
...
class SampleableType (β : Type) where
  selectElem : ProbComp β
  mem_support_selectElem (x : β) : x ∈ support selectElem
  probOutput_selectElem_eq (x y : β) : Pr[= x | selectElem] = Pr[= y | selectElem]

/-- Select uniformly from the type `β` using a type-class provided definition.
NOTE: naming is somewhat strange now that `Fintype` isn't explicitly required. -/
def uniformSample (β : Type) [h : SampleableType β] : ProbComp β := h.selectElem

notation:90 "$ᵗ " α:91 => uniformSample α
```
**Uniformity is part of the structure.** An instance carries a sampler *and two proofs*: every
element is reachable, and any two elements have equal probability. Because a `ProbComp` never
fails, the probabilities sum to one, and VCVio derives the uniform law for every instance:

`SampleableType.lean:57-66`
```lean
/-- Every element of a uniform sample over a `Fintype` has output probability `card⁻¹`. -/
@[simp, grind =]
lemma probOutput_uniformSample [Fintype α] (x : α) :
    Pr[= x | $ᵗ α] = (Fintype.card α : ℝ≥0∞)⁻¹ := by
```
`SampleableType.lean:224-228`
```lean
@[simp, grind =]
lemma probEvent_uniformSample [Fintype α] (p : α → Prop) [DecidablePred p] :
    Pr[ p | $ᵗ α] = (Finset.univ.filter p).card / Fintype.card α := by
```
Consequently **no instance of `SampleableType` can be non-uniform**, and two instances on the
same finite type have the same distribution (proved in the probe `SamplerDiamond`,
`sampler_unique`, section E.1). The constructors used by leanerVM:

`SampleableType.lean:232-239` (the base case: a uniform `Fin n` is the primitive coin)
```lean
@[reducible] def SampleableType.Fin (n : ℕ) : SampleableType (Fin (n + 1)) where
  selectElem := $[0..n]
  mem_support_selectElem := by simp
  probOutput_selectElem_eq := by simp

instance (n : ℕ) [hn : NeZero n] : SampleableType (Fin n) :=
  match n, hn with
  | _ + 1, _ => SampleableType.Fin _
```
`SampleableType.lean:260-267` (transport along a bijection; the laws are re-proved)
```lean
/-- A type equivalent to a `SampleableType` is also `SampleableType`. -/
@[reducible] def SampleableType.ofEquiv {α β : Type} [SampleableType α] (e : α ≃ β) :
    SampleableType β where
  selectElem := e <$> ($ᵗ α)
  mem_support_selectElem x := by simp
  probOutput_selectElem_eq x y := by
    rw [probOutput_map_equiv, probOutput_map_equiv]
    exact probOutput_uniformSample_inj α (e.symm x) (e.symm y)
```
`SampleableType.lean:313-316` (vectors: independent coordinates; laws proved at `:317-336`)
```lean
/-- Select a uniform element from `Vector α n` by independently selecting `α` at each index. -/
instance (α : Type) (n : ℕ) [SampleableType α] : SampleableType (Vector α n) where
  selectElem := by induction n with
  | zero => exact pure #v[]
  | succ m ih => exact Vector.push <$> ih <*> ($ᵗ α)
```
`SampleableType.lean:269-273` (any `FinEnum` type, i.e. a type with a computable enumeration
`α ≃ Fin n`, is sampleable; this instance matters for the diamond on `K`, E.1)
```lean
instance FinEnum.SampleableType (α : Type)
    [h : FinEnum α] [Nonempty α] : SampleableType α := by
  have : NeZero (FinEnum.card α) := NeZero.mk FinEnum.card_ne_zero
  exact SampleableType.ofEquiv h.equiv.symm
```
ArkLib's challenger answers the challenge query of round `i` by exactly this sampler
(`.lake/packages/Arklib/ArkLib/OracleReduction/ProtocolSpec/Basic.lean:732-734`, ArkLib pin
`dca90385`):
```lean
def challengeQueryImpl {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)] :
    QueryImpl ([pSpec.Challenge]ₒ'challengeOracleInterface) ProbComp :=
  fun q => $ᵗ (pSpec.Challenge q.1)
```

### A.6 What a reader trusts when a theorem is a VCVio probability bound

A statement `Pr[bad | game] ≤ ε` in VCVio unfolds to: interpret the program `game` (a free-monad
tree) by answering each uniform-choice query `n` with Mathlib's `PMF.uniformOfFintype (Fin (n+1))`
and each `OptionT` failure by the missing mass, compose these distributions by Mathlib's `PMF`
bind, and measure the event. The reader trusts:

1. that the **program** `game` is the intended experiment (for the proof system, that ArkLib's
   round-by-round knowledge-soundness game is the right game; that is the ArkLib dossier's
   subject);
2. the **three definitions** above (`IsUniformSpec unifSpec` answers with the uniform
   distribution; `evalSPMF = simulateQ toPMF`; `probEvent` measures `some '' {x | p x}`), which
   are short and standard; and Mathlib's `PMF` (bind, `uniformOfFintype`, `toOuterMeasure`);
3. that each **challenge type's** `SampleableType` instance is the intended sampler. By A.5 any
   instance is uniform, so what remains to trust is only that the challenge *type* is right
   (`E`, not a subtype or a smaller field). `Fintype.card E = 2^192` (`card_E`, E.3) fixes it.

Nothing else in VCVio is on the trusted path of a statement: its many lemmas are proofs, checked
by the kernel. (VCVio at the pin also has a measure-theoretic semantics `𝒟[…]`; the `Pr[…]`
notation used by ArkLib and leanerVM is the discrete `SPMF` one quoted above,
`Defs/Basic.lean:110-125`.)

---

## B. CompPoly at the pin `3468b38c`: tables, polynomials and the two fields

CompPoly is the library of *computable* polynomials: representations that run (`#eval`,
compiled code) and are proved equal to Mathlib's non-computable ones. Snippets are from
`.lake/packages/CompPoly/` at `3468b38c` ("feat(fields): add polynomial-basis GF(2^64) and its
cubic extension (#321)"), read with `git show 3468b38c:<path>`.

### B.1 `CMlPolynomialEval`: a multilinear polynomial as its table of values

`CompPoly/Multilinear/Basic.lean:42-48`
```lean
/-- `CMlPolynomialEval n R` is the type of multilinear polynomials in `n` variables over a ring `R`.
  It is represented by its evaluations over the Boolean hypercube `{0,1}^n`,
  i.e. Lagrange basis coefficients.
  The indexing is **little-endian** (i.e. the least significant bit is the first bit). -/
@[reducible]
def CMlPolynomialEval (R : Type*) (n : ℕ) := Vector R (2 ^ n) -- coefficient of Lagrange basis
```
A table of `2^n` values; entry `i` is the value at the cube point whose coordinate `j` is bit `j`
of `i` (**bit 0 is variable 0**). Being `@[reducible]`, it *is* a `Vector` to instance search,
which is why leanerVM wraps it in a structure `Column` (E, item 2). The multilinear extension is
defined by the Lagrange (equality) basis:

`CompPoly/Multilinear/Basic.lean:401-411`
```lean
/-- Lagrange (hypercube) basis at point `w`.

Returns the length-`2^n` vector `v` such that for any `x ∈ {0,1}^n`, letting
`i = ∑_{j=0}^{n-1} x_j · 2^j` (little‑endian indexing), we have
`v[i] = ∏_{j < n} (x_j · w[j] + (1 - x_j) · (1 - w[j]))`.
Equivalently, for `i : Fin (2^n)`,
`v[i] = ∏_{j < n}, (if the j-th bit of i is 1 then w[j] else 1 - w[j])`.
-/
def lagrangeBasis (w : Vector R n) : Vector R (2 ^ n) :=
  Vector.ofFn (fun i => ∏ j : Fin n, if (BitVec.ofFin i).getLsb j then w[j] else 1 - w[j])
```
`CompPoly/Multilinear/Basic.lean:523-544`
```lean
/-- Evaluate a `CMlPolynomialEval` at a point -/
def eval (p : CMlPolynomialEval R n) (x : Vector R n) : R :=
  Vector.dotProduct p (lagrangeBasis x)
...
/-- Evaluate a `CMlPolynomialEval` at a point using a ring homomorphism -/
def eval₂ (p : CMlPolynomialEval R n) (f : R →+* S) (x : Vector S n) : S := eval (map f p) x

/-- Evaluate the multilinear equality kernel `eq̃(w, x)`. -/
@[inline] def eqTilde (w x : Vector R n) : R :=
  eval (lagrangeBasis w) x
```
So `eval p x = Σ_i p[i] · ∏_j (bit_j(i) ? x_j : 1 − x_j)`, the multilinear extension `p̃(x)`,
and `eqTilde w x = Σ_i eq(w,i)·eq(x,i) = ∏_j (w_j x_j + (1−w_j)(1−x_j))`. The fast evaluator
folds one variable at a time (variable 0 first) and is proved equal to the dot product:

`CompPoly/Multilinear/Basic.lean:497-521`
```lean
/-- Evaluate a `CMlPolynomialEval` by recursive multilinear-extension interpolation. -/
@[inline, specialize]
def evalMle (p : CMlPolynomialEval R n) (x : Vector R n) : R :=
  evalMleValues p x
...
/-- Evaluate a `CMlPolynomialEval` through a ring homomorphism using multilinear-extension
interpolation. -/
@[inline, specialize]
def eval₂Mle (p : CMlPolynomialEval R n) (f : R →+* S) (x : Vector S n) : S :=
  evalMle (map f p) x
```
(`evalMleStep`, `:467-471`: entry `j` of the folded table is `(1 − x₀)·values[2j] + x₀·values[2j+1]`.)
`map f p` applies a ring homomorphism `f : R →+* S` to every entry (`:461-463`); with
`f = algebraMap K E` it lifts a `K`-table to an `E`-table, so `eval₂Mle q (algebraMap K E) r`
evaluates the `K`-multilinear `q̃` at a point `r ∈ E^n`. The two agreement theorems:

`CompPoly/Multilinear/Basic.lean:585-586` and `:638-640`
```lean
theorem eval_mle_eq_eval (p : CMlPolynomialEval R n) (x : Vector R n) :
    evalMle p x = eval p x := by
...
theorem eval₂_mle_eq_eval₂ (p : CMlPolynomialEval R n) (f : R →+* S) (x : Vector S n) :
    eval₂Mle p f x = eval₂ p f x := by
```
**Bridge to Mathlib.** At the CompPoly pin there is a conversion `CMlPolynomialEval.toMvPolynomial`
(`Multilinear/Equiv.lean:337`) but **no theorem that `eval` is Mathlib's evaluation of it**; that
bridge is ArkLib's (`ArkLib/ToCompPoly/Multilinear/Basic.lean:56`, ArkLib pin `dca90385`):
```lean
theorem eval_eq_MvPolynomial_MLE (evals : (Fin n → Fin 2) → R) (x : Fin n → R) :
    eval
        (Vector.ofFn fun i => evals (finFunctionFinEquiv.symm i))
        (Vector.ofFn x) =
      MvPolynomial.eval x (MvPolynomial.MLE evals) := by
```
The blueprint cites it correctly as ArkLib's (`protocol-blueprint.md:246`). For a reader the
definition `eval` above is self-explanatory and needs no bridge to be trusted.

**Bit order against leanVM.** The specification fixes "`⟨u⟩ := Σ_i u_i 2^i` … (bit `0` first)"
(`doc/leanvm/body/b-polynomial-commitment-scheme.tex:278`) and places each table's selector in the
*high* bits of its offset (`04-committing-the-witness.tex:10`, "`sel_i ∈ {0,1}^{M−κ_i}` for the
high bits of that offset"). CompPoly's little-endian order agrees: the low variables of the stack
index the position inside a block.

### B.2 `CMvPolynomial`: computable multivariate polynomials

The spine states its constraint and flush polynomials in CompPoly's sparse multivariate type
(`LeanerVM/Protocol/Spine/Instance.lean:123-132`, `Seams.lean:77`).

`CompPoly/Multivariate/CMvPolynomial.lean:47-48` and `Multivariate/Lawful.lean:33-36`
```lean
/-- A computable multivariate polynomial in `n` variables with coefficients in `R`. -/
abbrev CMvPolynomial (n : ℕ) (R : Type*) [Zero R] : Type _ := Lawful n R
...
/-- The subtype of polynomials with no zero coefficients. -/
@[implicit_reducible]
def Lawful (n : ℕ) (R : Type*) [Zero R] : Type _ :=
  {p : Unlawful n R // p.isNoZeroCoef}
```
(`Unlawful n R` is a finite map from monomials, exponent vectors `Vector ℕ n`, to coefficients.)
`CMvPolynomial.lean:131-135`, `:216-218`, `:229-233`
```lean
def eval₂ {R S : Type*} {n : ℕ} [Semiring R] [CommSemiring S] :
    (R →+* S) → (Fin n → S) → CMvPolynomial n R → S :=
  fun f vs p => ExtTreeMap.foldl (fun s m c => (f c * MonoR.evalMonomial vs m) + s) 0 p.1
...
def eval {R : Type*} {n : ℕ} [CommSemiring R] : (Fin n → R) → CMvPolynomial n R → R :=
  eval₂ (RingHom.id _)
...
def totalDegree {R : Type*} {n : ℕ} [Zero R] : CMvPolynomial n R → ℕ :=
  fun p => Finset.sup (List.toFinset (List.map CMvMonomial.toFinsupp (Lawful.monomials p)))
    (fun s => Finsupp.sum s (fun _ e => e))
```
The bridge to Mathlib's `MvPolynomial` (the standard, non-computable multivariate polynomial
type) and its two transfer lemmas:

`CompPoly/Multivariate/MvPolyEquiv/Core.lean:35-39`
```lean
def fromCMvPolynomial  (p : CMvPolynomial n R) : MvPolynomial (Fin n) R :=
  let support : List (Fin n →₀ ℕ) := p.monomials.map CMvMonomial.toFinsupp
  let toFun (f : Fin n →₀ ℕ) : R := p[CMvMonomial.ofFinsupp f]?.getD 0
  let mem_support_fun {a : Fin n →₀ ℕ} : a ∈ support ↔ toFun a ≠ 0 := by grind
  AddMonoidAlgebra.ofCoeff <| Finsupp.mk support.toFinset toFun (by simp [mem_support_fun])
```
`CompPoly/Multivariate/MvPolyEquiv/Eval.lean:53-61`
```lean
lemma eval_equiv {p : CMvPolynomial n R} {vals : Fin n → R} :
    p.eval vals = (fromCMvPolynomial p).eval vals := by
...
lemma totalDegree_equiv {S : Type*} {p : CMvPolynomial n R} [CommSemiring S] :
    p.totalDegree = (fromCMvPolynomial p).totalDegree := by rfl
```
and `polyEquiv : CMvPolynomial n R ≃ MvPolynomial (Fin n) R` (`Core.lean:134`). So a degree bound
`C.totalDegree ≤ d` in the spine is Mathlib's total degree, and Schwartz–Zippel from Mathlib
applies through `eval_equiv`. Building polynomials (`C`, `X`, ring operations) needs
`[BEq R] [LawfulBEq R]` (`CMvPolynomial.lean:55-62`); `K` has it (instance search finds
`instLawfulBEq` from `DecidableEq`; probe `FieldFidelity`, last lines), **`E` has none at the pin**
(the same probe: `failed to synthesize LawfulBEq E`), so the spine cannot build a `CMvPolynomial`
over `E`. The blueprint records this (`protocol-blueprint.md:570`) and keeps every polynomial over
`K`, which matches leanVM (constraints have `K` coefficients).

### B.3 The fields `K = GF(2^64)` and `E = GF(2^192)`

**`K` (`BF64`).** Specification object and computable carrier are separate, joined by a proved
bijective ring homomorphism.

`CompPoly/Fields/Binary/BF64/Basic.lean:100-102`, `:152-153`, `:199`
```lean
/-- The modulus `x^64 + x^4 + x^3 + x + 1` over `GF(2)`. Part of the specification only;
it is never evaluated. -/
noncomputable def basePoly : Polynomial (ZMod 2) := X ^ 64 + X ^ 4 + X ^ 3 + X + 1
...
theorem basePoly_irreducible : Irreducible basePoly := by
  refine Polynomial.irreducible_of_rabin (d := 64) ?_ (by norm_num) ?_ ?_
...
noncomputable abbrev BF64Quot : Type := AdjoinRoot basePoly
```
Irreducibility is proved by Rabin's test (CompPoly's `Polynomial.irreducible_of_rabin`) against
certificate chains that the kernel checks by `rfl` (`BF64/BaseCertificate.lean`, 552 lines); no
`native_decide` (axioms of `BF64.basePoly_irreducible`: `propext, Classical.choice, Quot.sound`,
probe `Layer0`). `AdjoinRoot basePoly` is Mathlib's quotient `GF(2)[x]/(basePoly)`, a field
because the modulus is irreducible.

`CompPoly/Fields/Binary/BF64/Impl.lean:52-71`
```lean
/-- `GF(2^64)` in its computable, machine representation: a 64-bit word whose bit `i` is
the coefficient of `x^i`. -/
abbrev BF64 : Type := BitVec 64

namespace BF64

instance : Zero BF64 := ⟨(0 : BitVec 64)⟩
instance : One BF64 := ⟨(1 : BitVec 64)⟩

/-- Addition in characteristic two is `xor`. -/
instance : Add BF64 := ⟨fun a b => a ^^^ b⟩
...
/-- Multiplication: the carry-less product, reduced modulo the modulus. -/
instance : Mul BF64 :=
  ⟨fun a b => reduce (carryLessMul (w := 128) a b)⟩
```
The carrier maps to the quotient by `toQuot a = AdjoinRoot.mk basePoly (toPoly a)` (`:77-79`),
proved a ring homomorphism (`toQuot_add :103`, `toQuot_mul :107`), injective (`:118`) and
surjective (`:398`). Every ring and field law of `BF64` is transported through it
(`CommRing :237-255`, `Field :442-450`); inversion is the Itoh–Tsujii chain, proved correct
(`mul_invItohTsujii :404`), with `0⁻¹ = 0`. Cardinality and the instances:

`CompPoly/Fields/Binary/BF64/Impl.lean:384-395`
```lean
/-- The carrier is in bijection with `Fin (2 ^ 64)`, by its underlying representation. -/
def equivFin : BF64 ≃ Fin (2 ^ 64) where
  toFun a := a.toFin
  invFun i := BitVec.ofFin i
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype BF64 := Fintype.ofEquiv _ equivFin.symm

/-- `BF64` has `2 ^ 64` elements. -/
theorem card_bf64 : Fintype.card BF64 = 2 ^ 64 := by
  rw [Fintype.card_congr equivFin, Fintype.card_fin]
```
`DecidableEq K` is `BitVec`'s (`instDecidableEqBitVec`, probe `Layer0`).

*Hazard of the eager `Fintype BF64`.* The instance is a closed computable term; compiled code
initialises it at program start by building `List.finRange (2^64)`, so any executable linking the
module is killed for lack of memory. leanerVM records this (`docs/roadmap/leanisa-status.md:753-769`
at `b435631`, finding "`instance : Fintype BF64` is evaluated at executable startup" (P3)): the test
driver had to become a library and no leanerVM executable may link the field. It cannot simply be
made `noncomputable` at this pin, because `ExtensionParams F` takes `[Fintype F]` and so every
`Ext` operation carries it at run time. Consequence for the blueprint: the executable verifier
`verify`, differential tests against the Rust, and any native target are **blocked at this pin**
until the CompPoly fix lands (F.3: it has).

*Hazard of `abbrev BF64 := BitVec 64`.* Because `BF64` is reducible, CompPoly's `Add`, `Mul`,
`Neg`, `Inv`, `NatCast`, `Fintype`, `CommRing`, `Field` instances are instances **on
`BitVec 64` itself** in every file that imports the field. Probe `FieldFidelity` (lines 85-100,
output lines 2-12) shows it:
```text
#eval u + v                -- u v : BitVec 64 := 3, 5   ⟹  6#64   (XOR, not 8)
#eval (u + v == 8, u + v == 6)                          ⟹  (false, true)
#synth Add (BitVec 64)                                  ⟹  BF64.instAdd
#synth Add (BitVec 32)                                  ⟹  BitVec.instAdd
```
and the numeral `(2 : K)` elaborates as `BitVec.instOfNat 64 2` (the bit pattern `x`), not the
cast of the natural number two (which is `0`): `#guard ((2 : ℕ) : K) = 0` and
`#guard (2 : K) ≠ 0` both pass. No current leanerVM declaration adds or multiplies a
`BitVec 64` meaning integers (`git grep "BitVec 64\|UInt64\|#64" b435631 -- LeanerVM tests`: only
`BitVec.ofNat 64`, `extractLsb'`, `++`, `<<<`, and `UInt64` in BLAKE2s, whose operations are
core's), so this is a hazard, not a defect. The companion hazard, core's `BitVec` simplification
procedures firing on `K`, is in G ("`simp` misreads `K` arithmetic").

**`E` (`BF64.Ext3`).** A generic extension framework `Ext P`, instantiated with the cubic.

`CompPoly/Fields/Binary/BF64/Ext3.lean:56-57`, `:125-127`, `:133-140`, `:165-168`, `:198-200`
```lean
noncomputable def ext3Poly : Polynomial BF64 := X ^ 3 + X + 1
...
theorem ext3Poly_irreducible : Irreducible ext3Poly :=
  Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    (by rw [ext3Poly_natDegree]; decide) ext3Poly_no_root
...
def ext3Params : ExtensionParams BF64 where
  d := 3
  two_le := by norm_num
  lower := #v[1, 1, 0]
  q := 2 ^ 64
  card_eq := card_bf64
...
abbrev Ext3 : Type := Ext ext3Params
...
@[simp] theorem card_ext3 : Fintype.card Ext3 = 2 ^ 192 := by
  rw [Ext.card_ext, ext3Params_q, ext3Params_d, ← pow_mul]
```
Irreducibility: a root `a` of `y³+y+1` has `a⁷ = 1`; `gcd(7, 2⁶⁴−1) = 1` (`decide +kernel`), so
`a = 1`, which is not a root (`Ext3.lean:78-122`). `ext3Params_poly` (`:148-160`) proves the
coefficient vector `#v[1, 1, 0]` denotes `y³ + y + 1` (the coefficients of `1, y, y²` below the
implicit leading `y³`). The framework:

`CompPoly/Fields/Extension/Defs.lean:132-136`, `:185`, `:188`
```lean
/--
The carrier of the extension `F[X] / f`: a dense coefficient vector of length `P.d`,
little-endian (index `i` is the coefficient of `X^i`).
-/
def Ext {F : Type*} [Field F] [Fintype F] (P : ExtensionParams F) : Type _ := Vector F P.d
...
@[inline] def ofBase (c : F) : Ext P := ofFn fun i => if (i : ℕ) = 0 then c else 0
...
def gen : Ext P := ofFn fun i => if (i : ℕ) = 1 then 1 else 0
```
`Ext` is a plain `def` (not reducible), so `Vector`'s instances do not leak onto `E`. Its
multiplication folds products by the reduced monomials `X^k mod f` (`Defs.lean:227-233`; the
compiled code uses the table version `mulTbl`, swapped in by a proved `@[csimp]` equation
`mul_eq_mulTbl`, `:267-272`). The ring laws are transported from `AdjoinRoot P.poly` through a
proved bijection (`Extension/Field.lean:73-107`, `ringEquivQuot`); inversion is Fermat,
`x⁻¹ = x^(q^d − 2)` (`Field.lean:127`), the `Field` instance needs `[Fact (Irreducible P.poly)]`
(`:159-166`), supplied by `Ext3.lean:162-163`. `Fintype (Ext P)` is by the coefficient
bijection (`Field.lean:54-63`), `card_ext : Fintype.card (Ext P) = P.q ^ P.d`. The embedding
`K → E` is `Ext.ofBase`, packaged as `algebraMap`:

`CompPoly/Fields/Extension/Bridge.lean:363-370`
```lean
/-- The extension is an `F`-algebra. -/
instance instAlgebra : Algebra F (Ext P) where
  algebraMap := ofBaseRingHom P
  commutes' _ _ := mul_comm _ _
  smul_def' c x :=
    toQuot_injective (by simp only [toQuot_smul, toQuot_mul, ofBaseRingHom_apply, toQuot_ofBase])

@[simp] theorem algebraMap_eq_ofBase (c : F) : algebraMap F (Ext P) c = ofBase c := rfl
```
`DecidableEq (Ext P)` and `BEq (Ext P)` are `Vector`'s (`Defs.lean:282-284`); there is no
`LawfulBEq (Ext P)` at the pin (B.2).

### B.4 Are these leanVM's fields? Yes, bit for bit

A formalization over another presentation of `GF(2^64)` would say nothing about the deployed
verifier's arithmetic. Checked on four sources:

| | Specification (`doc/leanvm/body/02-vm-specification.tex:6-9`) | Rust (`crates/primitives/src/field/`) | Python (`python-verifier/verifier.py`) | CompPoly / leanerVM |
|---|---|---|---|---|
| `K` modulus | `x^64+x^4+x^3+x+1` | `gf2_64.rs:2` "`K = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)`", reduction `R64 = 0x1B` (`gf2_64x3.rs:30`) | `:39` "`GF(2^64) = F2[x]/(x^64 + x^4 + x^3 + x + 1)`", fold `high ^ high<<1 ^ high<<3 ^ high<<4` (`:31`) | `basePoly` (`BF64/Basic.lean:102`) |
| `K` encoding | — | `gf2_64.rs:19` "`bit i = coefficient of x^i`", `F64(pub u64)` | `K(value: int)`, 64-bit (`:39-46`) | `BitVec 64`, bit `i` = coefficient of `x^i` (`Impl.lean:52-54`) |
| `K` addition | — | `self.0 ^ rhs.0` (`gf2_64.rs:75`) | `self.value ^ rhs.value` (`:67`) | `a ^^^ b` (`Impl.lean:62`) |
| `E` modulus | `K[y]/(y^3+y+1)` | `gf2_64x3.rs:3` "`F192 = K[y]/(y^3 + y + 1)`" | `:92` "`K[y]/(y^3 + y + 1)`" | `ext3Poly`, `lower := #v[1, 1, 0]` |
| `E` limbs | — | `F192 { c0, c1, c2 }`, "`c0 + c1·y + c2·y²`" (`gf2_64x3.rs:5,34-37`) | `E(c0, c1, c2)`, bytes `<3Q` (`:94-107`) | `Vector K 3`, index `i` = coefficient of `y^i` |
| `y` | — | `F192::Y = (0, 1, 0)` (`gf2_64x3.rs:44`) | `Y = E(0, 1)` (`:183`) | `Ext.gen` = limbs `(0,1,0)` |
| `K ↪ E` | — | limb `c0` | `E(lifted)` = `(k, 0, 0)` (`:111-115`) | `ofBase` = `(c, 0, 0)` |
| generator | "a generator of order `2^64 − 1`" (`:12`) | `F64::G = F64(2)` (`gf2_64.rs:28`) | `GEN = E(2)` (`:182`) | `g : K := 0x2` (`Parameters/Generator.lean:259`), order proved |

Beyond the matching definitions, probe `FieldFidelity` (full source in H) runs the Rust's own
reference vectors through leanerVM's compiled `K` and `E` arithmetic. All `#guard`s pass: the
three `(a, b, a·b)` vectors of `gf2_64.rs:271-275`, the four `(a, b, a·b, a·a)` vectors of
`gf2_64x3.rs:991-1016`, `y·y·y = y + 1` (`gf2_64x3.rs:1026`), `x^63 · x = 0x1B`, `0⁻¹ = 0`
(`gf2_64.rs:42`), and a mutated product and a mutated limb are rejected. The only error in its
output is the intended one (`LawfulBEq E`, line 103). Python's `E.__mul__` (`:145-152`) folds
`p0+p3, p1+p3+p4, p2+p4`, which is exactly leanerVM's `mul_limbs`
(`LeanerVM/Parameters/Field.lean:206-210`).

**Conclusion.** leanerVM's `K` and `E` are the specification's fields *with the Rust's and
Python's encodings*: the identification is the identity on 64-bit words and on limb triples.
(leanVM also uses `GF(2^8)` with the AES modulus and an embedding `φ₈ : GF(2^8) → K` inside Flock,
`crates/primitives/src/field/gf2_8.rs`, `phi8_tower.rs:15-24`, `c-flock-protocol.tex:35`; CompPoly
has no such field at the pin and the blueprint says so, `protocol-blueprint.md:281`. The
Flock/ring-switching dossier covers it.)

### B.5 leanerVM's `Parameters/Field.lean`, `Generator.lean`, `CleanField.lean` (at `b435631`)

`LeanerVM/Parameters/Field.lean:70-92`
```lean
/-- `K = GF(2^64)`, CompPoly's `BF64`: a `BitVec 64` with bit `i` the coefficient of `x^i`. -/
abbrev K : Type := BF64

/-- `E = K[y]/(y^3 + y + 1)`, CompPoly's `BF64.Ext3`: a `Vector K 3` in limb order
`c0 + c1·y + c2·y²`. -/
abbrev E : Type := BF64.Ext3

/-- The adjoined root `y` of `y^3 + y + 1`. -/
def y : E := BF64.ext3Gen

/-- The defining relation of `E`: `y^3 = y + 1`. -/
theorem y_pow_three : y ^ 3 = y + 1 := BF64.ext3Gen_pow_three
...
/-- The embedding `K ↪ E` as the `y^0` limb; it is `algebraMap K E` by `rfl`. -/
abbrev ofK (a : K) : E := Ext.ofBase a
...
/-- The word `c0 + c1·y + c2·y²`, as the literal limb vector. -/
def E.ofLimbs (c0 c1 c2 : K) : E := Ext.ofVector #v[c0, c1, c2]
```
`K` and `E` are *abbreviations* of CompPoly's types, so leanerVM adds no field of its own; `y`
is CompPoly's generator; `ofK` is `algebraMap K E` (probe `Layer0` line 109:
`example (a : K) : ofK a = algebraMap K E a := rfl` is accepted). The file's other declarations
are limb lemmas (`limb_add`, `mul_limbs`, `isInK_iff`, …), all proved.

`LeanerVM/Parameters/Generator.lean:258-311`: `g : K := 0x2`, and `orderOf_g : orderOf g = 2^64 − 1`
by Lagrange plus seven `decide +kernel` checks `g^((2^64−1)/p) ≠ 1` over the prime factors
`3·5·17·257·641·65537·6700417`. The generator is certified, not assumed.

`LeanerVM/Parameters/CleanField.lean:360-372` supplies Clean's field interface for `K`:
```lean
instance instFiniteFieldK : FiniteField K where
  val := BitVec.toNat
  fromNat n := BitVec.ofNat 64 n
  size := 2 ^ 64
  ...
theorem instFiniteFieldK_toField : (instFiniteFieldK.toField : Field K) = BF64.instField := rfl
```
so Clean's `K` has CompPoly's field structure (one field structure, by `rfl`). Note that Clean's
`val`/`fromNat` read `K` as the integers `0 … 2^64−1`, which is *not* a ring homomorphism in
characteristic two; the file's docstring records that Clean's core never consumes them.

---

## C. Clean at the pin `93c9d1ef`: circuits, tables, buses, and why its balance is vacuous over `K`

Clean is a library for writing zkVM circuits (AIR tables and the buses between them) with
proofs that the constraints imply a specification. leanISA (the arithmetization) is written in
it; the proof system consumes its *tables* through the spine's adaptor, not its soundness
statement. Snippets are from `.lake/packages/Clean` read with `git show 93c9d1ef:<path>`. At this
pin Clean is **not** a Lean `module` library, which is why `LeanerVM/Parameters/CleanField.lean`
is a plain file (B.5).

### C.1 The circuit language

`Clean/Utils/FiniteField.lean:23-45` — the field interface every circuit is generic over:
```lean
class FiniteField (F : Type) extends Field F where
  /-- Canonical embedding of field elements into natural numbers. -/
  val : F → ℕ
  /-- Inverse of `val`: interpret a natural number (below the field size) as a field
  element. For prime fields this is `Nat.cast`; for binary fields it interprets the
  binary digits as polynomial coefficients. Note that `Nat.cast` would be wrong there:
  it reduces via the characteristic, collapsing `GF(2^n)` to `{0, 1}`. -/
  fromNat : ℕ → F
  ...
  size : ℕ
```
`Clean/Circuit/Expression.lean:12-16` — a polynomial expression over the variables of a row:
```lean
inductive Expression (F : Type) where
  | var : Variable F -> Expression F
  | const : F -> Expression F
  | add : Expression F -> Expression F -> Expression F
  | mul : Expression F -> Expression F -> Expression F
```
`Clean/Circuit/Expression.lean:46-52` — an assignment of the variables (`get`) and the named
side tables a specification may mention (`data`, of type `ProverData F = String → (n : ℕ) → Array
(Vector F n)`, `:20-21`):
```lean
structure Environment (F : Type) where
  /-- Assignment of a circuit's variables to field elements -/
  get : ℕ → F
  ...
  data : ProverData F
```
`Clean/Circuit/Operations.lean:315-320` and `:355` — what a circuit emits: a fresh witness
variable, a polynomial asserted to be zero, a lookup, a bus interaction, or a nested circuit.
```lean
inductive Operation (F : Type) [FiniteField F] where
  | witness : (m : ℕ) → (compute : WitgenIR F m) → Operation F
  | assert : Expression F → Operation F
  | lookup : Lookup F → Operation F
  | interact : AbstractInteraction F → Operation F
  | subcircuit : {n : ℕ} → Subcircuit F n → Operation F
...
def Operations (F : Type) [FiniteField F] := List (Operation F)
```
`Clean/Circuit/Basic.lean:29` — a circuit is a state monad producing operations from a variable
offset:
```lean
def Circuit (F : Type) [FiniteField F] (α : Type) := ℕ → α × List (Operation F)
```

### C.2 Components, tables, ensembles

`Clean/Air/FlatComponent.lean:7-15` — a component is one circuit checked on every row
(`GeneralFormalCircuit` bundles the circuit with its assumptions, specification and soundness
proof):
```lean
structure Component (F : Type) [FiniteField F] where
  {Input : TypeMap} {Output : TypeMap}
  [provableInput : ProvableType Input] [provableOutput : ProvableType Output]
  circuit : GeneralFormalCircuit F Input Output
```
`Clean/Air/FlatComponent.lean:150-156` — a table is a component with its concrete rows:
```lean
structure Table (F : Type) [FiniteField F] where
  component : Component F
  width : ℕ
  table : List (Array F)
  data : ProverData F
  uniform_width : ∀ row ∈ table, row.size = width
```
`Clean/Air/FlatEnsemble.lean:11-25` — an ensemble is a list of components and the channels
(buses) between them; its witness is one table per component, the shared data and the public
input:
```lean
structure Ensemble (F : Type) [FiniteField F] (PublicIO : TypeMap) [ProvableType PublicIO] where
  tables : List (Component F)
  channels : List (RawChannel F)
  -- TODO: the verifier shouldn't be treated as a "circuit", and possibly shouldn't even be on here
  verifier : GeneralFormalCircuit F PublicIO unit := .empty F PublicIO
  ...
structure EnsembleWitness (ens : Ensemble F PublicIO) where
  tables : List (Table F)
  data : ProverData F
  publicInput : PublicIO F
  same_length : ens.tables.length = tables.length
  same_circuits : ∀ i (hi : i < ens.tables.length), ens.tables[i] = tables[i].component
  same_data : ∀ table ∈ tables, table.data = data
```
**Why `EnsembleWitness` lives in `Type 1`.** A `Table` stores its `Component`, which stores its
row types `Input Output : TypeMap`, and `TypeMap := Type → Type` (`Clean/Circuit/CircuitType.lean:10`)
is itself a `Type 1`. A structure with a field in `Type 1` is in `Type 1` (probe `CleanBalance`,
output lines 1-4: `Air.Flat.Component : (F : Type) → [FiniteField F] → Type 1`, likewise `Table`,
`Ensemble`, `EnsembleWitness`). ArkLib's statements and witnesses are in `Type`, so an
`EnsembleWitness` cannot be the proof system's witness; the blueprint draws exactly this
consequence (`protocol-blueprint.md:367-369`, `:582-586`) and makes the stack `q : Column μ`, a
`Type`, the witness, with a pointwise transport along the adaptor.

### C.3 Channels and interactions

`Clean/Circuit/Channel.lean:15-25` — a raw channel: a name, a message arity, and two
propositions indexed by the multiplicity, what a receiver may assume and what a sender must
prove:
```lean
structure RawChannel (F : Type) where
  name : String
  arity : ℕ
  Guarantees (mult : F) (message : Vector F arity) (data : ProverData F) : Prop
  Requirements (mult : F) (message : Vector F arity) (data : ProverData F) : Prop
```
`Channel.lean:35-45` — the typed channel reads the *direction from the sign* of the multiplicity:
```lean
def toRaw (channel : Channel F Message) : RawChannel F where
  name := channel.name
  arity := size Message
  Guarantees mult message data :=
    mult = -1 → channel.Guarantees (fromElements message) data
  Requirements mult message data :=
    mult ≠ -1 →
    mult ≠ 0 →
    channel.Guarantees (fromElements message) data
```
`Channel.lean:101-105` (in a circuit, symbolic) and `:305-310` (after evaluation on a row):
```lean
structure AbstractInteraction (F : Type) where
  channel : RawChannel F
  mult : Expression F
  msg : Vector (Expression F) channel.arity
  assumeGuarantees : Bool
...
structure Interaction (F : Type) where
  channel : RawChannel F
  mult : F
  msg : Array F
  same_size : msg.size = channel.arity
  assumeGuarantees : Bool
```

### C.4 Clean's ensemble statement and its soundness

`Clean/Air/Balance.lean:13-26`
```lean
/--
Balance of one element of an interaction list.
This is just multiplicity of the element when viewing the list as a multiset.
-/
def balanceOf (interactions : List (Interaction F)) (msg : Array F) : F :=
  interactions.filter (·.msg = msg) |>.map (·.mult) |>.sum

/--
Channel balance: for any message, the sum of multiplicities is 0.
We also require a side condition that ensures the interaction count does not overflow.
-/
def BalancedInteractions (interactions : List (Interaction F)) : Prop :=
  (interactions.length < ringChar F ∨ ringChar F = 0) ∧
  ∀ msg : Array F, balanceOf interactions msg = 0
```
`Clean/Air/FlatEnsemble.lean:334-337`, `:361-370`
```lean
abbrev BalancedChannel [DecidableEq F] {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens)
    (channel : RawChannel F) : Prop :=
  BalancedInteractions (witness.allTablesWitness.interactionsWith channel)
...
def Statement (ens : Ensemble F PublicIO) (publicInput : PublicIO F) : Prop :=
  ∃ witness : EnsembleWitness ens,
    witness.publicInput = publicInput ∧
    witness.Constraints ∧
    witness.BalancedChannels

/-- Soundness: assumptions plus the raw statement imply the spec. -/
def Soundness (ens : Ensemble F PublicIO) (Assumptions Spec : PublicIO F → Prop) : Prop :=
  ∀ publicInput, Assumptions publicInput → ens.Statement publicInput → Spec publicInput
```
`FlatEnsemble.lean:419-424` — the theorem that assembles per-table soundness into ensemble
soundness (its proof is plain logic; the bus argument is inside `TableSoundness` and the channel
lemmas of `Balance.lean`, e.g. `exists_push_of_pull`, `:155-157`: every pull has a matching push,
derived from balance *and* the side condition):
```lean
theorem soundness_of_tableSoundness_and_specConsistency (ens : Ensemble F PublicIO)
  (Assumptions Spec : PublicIO F → Prop) :
  ens.TableSoundness →
  ens.AssumptionsConsistency Assumptions →
  ens.SpecConsistency Spec →
    ens.Soundness Assumptions Spec := by
```

### C.5 Why the balance argument is vacuous over a field of characteristic two

The balance is a LogUp-style statement: multiplicities are **summed in the field**. That is
sound over a large prime field because a sum of at most `p − 1` terms `±1` vanishes only if the
counts match; the side condition `length < ringChar F` is that bound. Over `K`, `ringChar K = 2`:

1. **Without the side condition the sum is unsound.** A message pushed twice (multiplicity `1`,
   twice) and never pulled has `balanceOf = 1 + 1 = 0`. Probe `CleanBalance`:
   ```lean
   def pushedTwice : List (Interaction K) := [push 7, push 7]
   theorem pushedTwice_balance (msg : Array K) : balanceOf pushedTwice msg = 0
   theorem pushedTwice_not_perm :
       ¬ (pushedTwice.map (·.msg)).Perm ([] : List (Array K))
   ```
   Both are accepted (axioms: the standard three and `[propext]` respectively). In addition
   `-1 = 1` in `K` (`example : (-1 : K) = 1 := by decide`), so `Channel.toRaw` grants the pull
   guarantee to every multiplicity-`1` push and makes every `Requirements` vacuous (leanerVM
   issue #16, table row 1, with kernel-checked examples in
   `tests/LeanerVMTests/Arithmetization/Channels.lean`).
2. **With the side condition, the relation holds of no real bus.** `length < 2` admits at most one
   interaction per channel, and a balanced singleton has multiplicity `0`. Probe `CleanBalance`:
   ```lean
   theorem pushedTwice_not_balanced : ¬ BalancedInteractions pushedTwice
   theorem length_le_one_of_balanced {l : List (Interaction K)} (h : BalancedInteractions l) :
       l.length ≤ 1
   theorem mult_eq_zero_of_balanced_singleton {i : Interaction K}
       (h : BalancedInteractions [i]) : i.mult = 0
   theorem honest_pair_not_balanced : ¬ BalancedInteractions [push 7, pull 7]
   theorem statement_forces_at_most_one_interaction {PublicIO : TypeMap} [ProvableType PublicIO]
       (ens : Ensemble K PublicIO) (w : EnsembleWitness ens) (h : w.BalancedChannels)
       (c : RawChannel K) (hc : c ∈ ens.channels) :
       (w.allTablesWitness.interactionsWith c).length ≤ 1
   ```
   all accepted, on the standard axioms. So over `K` `Ensemble.Statement` is false for every
   ensemble whose honest witness puts two interactions on a channel, including the smallest
   honest bus (one push, one matching pull): Clean's `Soundness` is then *vacuously* true and
   its completeness false. That is the precise sense of "vacuous": the countermodel of item 1 is
   excluded, but only by excluding every real witness too.

The blueprint's relation-ladder row (`protocol-blueprint.md:359`) says "Over `K` the side
condition fails for every real ensemble and a tuple pushed twice and never pulled balances". The
first half is right; the second is true of the field sum, not of `BalancedInteractions` (which
rejects that list, `pushedTwice_not_balanced`). Recorded as the minor finding "the relation
ladder conflates the field sum with Clean's balance relation" (G).

### C.6 State of the tracking items (read with `gh` on 2026-09-30)

| Item | State | What it is |
| --- | --- | --- |
| leanerVM #16 | open (updated 2026-09-15) | "leanISA: Clean's bus argument is vacuous over K, PR Clean for direction tags and multiset balance" — the request; tabulates `Channel.toRaw`, `emit`, `BalancedInteractions`, and the `[Fact (ringChar F ≠ 2)]` lemmas as degenerate over `K`. |
| leanerVM #20 | open (updated 2026-09-24) | the Clean-side roadmap: opt-in `DirectedChannel` (direction as a tag in the message), `BalanceModel.multiset` (permutation, counted in `ℕ`), `Ensemble.StatementWith model`; Layers 0-4 on Clean #464, Layer 5 (leanerVM adoption) open. |
| leanerVM #23 | open (updated 2026-09-17) | fold the three named fixed-column hypotheses of `SatisfiedBy` into Clean fixed columns and proof-committed data once Clean #446 lands. |
| Clean #446 | open, **draft** (updated 2026-08-16) | "Add fixed columns and sound prover data to Flat AIR". |
| Clean #452 | open **issue** (not a pull request; `gh pr view 452` fails) | "Model verifier-checked interaction capacity in Flat AIR soundness". |
| Clean #464 | open, ready for review (updated 2026-09-24) | "Bus balance over binary fields: opt-in directed channels and explicit balance models"; legacy statements unchanged; includes `legacy_rejects_every_run` over `F 2`. |
| Clean #466 | open (updated 2026-09-24) | "interpret expressions as bounded-degree polynomials" (the spine's hole "Clean components as polynomials", `protocol-blueprint.md:604`). |
| Clean #474 | open (updated 2026-09-29) | "preserve balance proof across Lean 4.34 normalization": the **new pin `42fe4b26`** is this branch merged with Clean `main`; it ports proofs only. At `42fe4b26` `balanceOf` and `BalancedInteractions` are **unchanged** (`git show 42fe4b26:Clean/Air/Balance.lean:21-29`, identical text), so the vacuity stands at the new pin. |

### C.7 What leanISA does instead, and when the workaround retires

leanISA never consumes `Ensemble.Statement`. Its relation `SatisfiedBy` states balance as a
permutation of message lists, counted in `ℕ`, with direction given by *which channel of a pair*
an interaction is on:

`LeanerVM/Arithmetization/Statement.lean:227-231` (at `b435631`)
```lean
/-- Pushed and pulled messages of a channel pair form the same multiset (specification §5.1):
a permutation of message lists, counted in `ℕ`, never a field sum (acceptance test 14). -/
def BalancedPair (w : EnsembleWitness (leanIsaEnsemble prog)) (pull push : RawChannel K) :
    Prop :=
  (messagesOn w push).Perm (messagesOn w pull)
```
used three times in `SatisfiedBy` (`Statement.lean:320-324`: `state_balanced`, `mem_balanced`,
`bytecode_balanced`). Every interaction has multiplicity `1`, so the message multiset is the
interaction multiset (`Statement.lean:57-64`; `Channels.lean:58-72` for the channel pairs).
`List.Perm` (Mathlib/core: `l₁ ~ l₂`, one list is a reordering of the other) is exact multiset
equality with no characteristic condition.

**Retirement condition.** `BalancedPair` and the channel-pair encoding of direction
(`Direction`, `channelDir`) are deleted when (1) Clean #464 is merged into Clean `main`, (2)
leanerVM's pin reaches a Clean revision containing it, and (3) leanerVM's channels are rebuilt
as `DirectedChannel`s and `SatisfiedBy` is stated through
`Ensemble.StatementWith BalanceModel.multiset` (leanerVM #20, Layer 5, "a separate pull request";
`Channels.lean:71-72`). Until then the workaround is **a deviation forced by an upstream
library**, and its correctness is by inspection of a four-line definition. Neither #446 nor #452
is required for the balance repair (issue #20: "#446 (independent)").

---

## D. Mathlib and Lean itself: what the statements unfold to, and the trusted base

### D.1 Mathlib (and core) notions in the proof system's statements

Counted in the statements (not proofs) of `LeanerVM/Protocol/` at `b435631` and in the objects of
A-C. Mathlib at the old pin `v4.33.1` (`0df444a3`, read with `git show 0df444a3:<path>`), core at
Lean `v4.33.1`.

| Notion | What it is | Definition (old pin) | Where the proof system meets it |
|---|---|---|---|
| `ℝ≥0`, `ℝ≥0∞` | non-negative reals, and with `∞` | `def NNReal := { r : ℝ // 0 ≤ r }` (`Mathlib/Data/NNReal/Defs.lean:58`); `def ENNReal := WithTop ℝ≥0` (`Mathlib/Data/ENNReal/Basic.lean:101`) | error bounds: `piopError : … → ℝ≥0` (`Spine/Compose.lean:149`); every `Pr[…]` is an `ℝ≥0∞` (A.4) |
| `PMF`, `uniformOfFintype` | probability mass function; the uniform one | `def PMF (α) := { f : α → ℝ≥0∞ // HasSum f 1 }` (`Probability/ProbabilityMassFunction/Basic.lean:46-47`); `uniformOfFintype α := uniformOfFinset Finset.univ …` (`Probability/Distributions/Uniform.lean:285-286`) | the semantics of every coin (A.4) |
| `Set α` | a predicate on `α` | core/Mathlib `Set α := α → Prop` | ArkLib relations: `M3Rel I : Set ((I.Stmt × …) × Column I.μ)` (`Spine/Instance.lean:230`), `Seam.of` (`Seams.lean:166`), language sets in `Spine/Phase.lean` |
| `Fintype α`, `Fintype.card` | a finite type with its list of elements; its size | `class Fintype (α) where elems : Finset α; complete : ∀ x, x ∈ elems` (`Data/Fintype/Defs.lean:57-61`); `def card (α) [Fintype α] : ℕ := (@univ α _).card` (`Data/Fintype/Card.lean:39-41`) | the size of the challenge space, `card_E` (E.3); the counting bounds (E.4); `PublicInput.lean` |
| `Finset.sum` (`∑`), `Finset.prod` | finite sums and products | Mathlib `Finset.sum s f` (fold over the underlying multiset) | stacking and claim weights: `Seams.lean:113` (`∑ i : Fin (2 ^ μ), W.onCube.get i * ofK (q.values.get i)`), `Stack`, `Padding`, `ClaimWeights`, `FixedColumns` |
| `List.Perm` (`~`) | one list is a reordering of the other (multiset equality) | core `inductive Perm : List α → List α → Prop` with `nil`, `cons`, `swap`, `trans` (`Init/Data/List/Basic.lean:1858-1874`, Lean `v4.33.1`) | bus balance: `def Balanced (q) : Prop := (I.tuples q .push).Perm (I.tuples q .pull)` (`Spine/Instance.lean:201`), leanISA's `BalancedPair` (C.7) |
| `MvPolynomial σ R` | Mathlib's multivariate polynomials (non-computable, finitely supported coefficient maps) | `abbrev MvPolynomial (σ R) := AddMonoidAlgebra R (σ →₀ ℕ)` (`Algebra/MvPolynomial/Basic.lean:82-83`) | reached through `fromCMvPolynomial` (B.2) for `totalDegree` and Schwartz–Zippel |
| `Polynomial`, `AdjoinRoot`, `Irreducible` | univariate polynomials, the quotient `R[X]/(f)`, irreducibility | `def AdjoinRoot (f : R[X]) := Polynomial R ⧸ (span {f} : Ideal R[X])` (`RingTheory/AdjoinRoot.lean:62`) | the *definitions* of `K` and `E` (B.3), through the bijections `toQuot` |

A reader who knows these notions from mathematics can take them at face value: each is a short
definition whose meaning is the textbook one, and Mathlib's theory about them is proved.

### D.2 The trusted base of any Lean development

- **The kernel.** Lean's type checker for the dependent type theory. Every declaration, however
  produced (by hand, by tactics, by automation), is re-checked by it. Tactics are untrusted.
  (Probe `NumeralHazard` shows the kernel rejecting two ill-typed proof terms that `simp`
  produced: G, "`simp` misreads `K` arithmetic".)
- **Three standard axioms**: `propext` (logically equivalent propositions are equal),
  `Classical.choice` (choice; gives excluded middle), `Quot.sound` (equal-in-relation elements
  have equal classes; gives function extensionality). They are the axioms of Mathlib and are
  consistent relative to standard set theory.
- **What would enlarge it.** `sorryAx` (an admitted proof: it proves anything); `native_decide`,
  which adds the axiom `Lean.ofReduceBool` and so trusts the compiler, the interpreter and every
  `@[implemented_by]`/`@[extern]` replacement of a definition by native code; any user `axiom`.
- **How closed claims are checked.**
  - `decide`: the elaborator evaluates the `Decidable` instance, and the kernel re-checks the
    resulting term `of_decide_eq_true (Eq.refl true)` by its own reduction. Trusted: the kernel.
  - `decide +kernel`: skips the elaborator's evaluation and asks the kernel directly (the form
    leanerVM uses for `K` powers, `Parameters/Generator.lean:281-299`). Trusted: the kernel.
  - `#guard e`: evaluates `e` by the **compiler/interpreter** and fails the build if it is not
    `true`. It proves nothing to the kernel and trusts compiled code, including
    `@[csimp]` replacements (CompPoly's `mul_eq_mulTbl` swaps `Ext` multiplication for a
    table version; that equation is itself proved, `Extension/Defs.lean:267`) and core's native
    `Nat`/`BitVec` code. leanerVM uses `#guard` only in tests, as executable evidence.
  - `rfl`/`example … := rfl`: kernel definitional equality.

### D.3 What leanerVM's validation enforces (at `b435631`)

- `scripts/audit-lean.sh:8-21`: a lexical ban on `axiom`, `sorry`, `admit`, `unsafe`,
  `native_decide` in `LeanerVM`, `LeanerVM.lean`, `tests`, plus `check-lean-options.py` (no
  local override of linter or implicit-variable options).
- `scripts/audit-axioms.lean:17-29`: for **every** constant whose name starts with `LeanerVM` or
  `LeanerVMTests`, `collectAxioms` (recursive, through all imported libraries) must return only
  `propext`, `Classical.choice`, `Quot.sound`:
  ```lean
  for (name, _) in env.constants.toList do
    if (`LeanerVM).isPrefixOf name || (`LeanerVMTests).isPrefixOf name then
      count := count + 1
      for ax in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          unexpected := unexpected.push (name, ax)
  ```
  `scripts/test-axiom-audit.py:28-45` re-runs it with a planted `axiom AuditNegative.hidden :
  False` used by one production and one test theorem, and requires the audit to reject both (a
  negative control). CI runs the same audit through `lean-action`
  (`axiom-audit-root: LeanerVM`, `.github/workflows/ci.yml:40-43`) and the script
  (`:44-45`); `docs/ci.md:8-9` marks both workflows required.
- `scripts/validate.sh`: the above plus the import DAG, layer and docs checks, `lake build`,
  `lake test`, and the test root with warnings as errors.

Consequence: a leanerVM theorem cannot silently rest on one of ArkLib's admitted theorems
(ArkLib's `sorryAx` would appear in `collectAxioms`), nor on `native_decide` anywhere in its
dependency cone. What remains trusted is the kernel, the three axioms, and the *meaning of the
definitions* in the statements (A.6, B, C, D.1). `#guard` evidence in tests is compiled-code
evidence, never proof. (The audit covers the two project namespaces; an instance declared
outside them would escape it. None of Layer 0's is: `LeanerVM.Protocol.instSampleableTypeK`
etc., probe `Layer0` output.)

---

## E. Layer 0 of the proof system, audited (at `b435631`; changes at `144c5aa` noted)

### E.0 Catalogue

ArkLib's `OracleInterface` (ArkLib pin `dca90385`) is what makes a message an *oracle*: a query
type, and an implementation that answers a query by reading the message.

`.lake/packages/Arklib/ArkLib/OracleReduction/OracleInterface.lean:54-57`, `:75-78`, `:88-96` (at `dca90385`)
```lean
class OracleInterface (Message : Type u) where
  Query : Type v
  toOC : OracleContext Query (ReaderM Message)
...
def answer {Message : Type*} [O : OracleInterface Message]
    (m : Message) (q : O.Query) : O.Response q :=
  (O.toOC.impl q).run m
...
@[reducible]
def instDefault {Message : Type u} : OracleInterface Message where
  Query := Unit
  toOC.spec := fun _ => Message
  toOC.impl _ := read
```
(`OracleContext ι m` is VCVio's pair of an `OracleSpec ι` and a `QueryImpl` of it in `m`,
`VCVio/OracleComp/OracleContext.lean:25-27` at `f9dc47d9`.) ArkLib also registers
`instVector : OracleInterface (Vector α n)` answering *positions* (`OracleInterface.lean:333-337`),
and `instance (i : Fin 0) : OracleInterface i.elim0` (`:119`).

| Declaration (at `b435631`) | Snippet | Plain meaning | Depends on |
|---|---|---|---|
| `Column` (`Protocol/Field.lean:67-69`) | `structure Column (n : ℕ) where values : CMlPolynomialEval K n` | a committed column: a table of `2^n` values in `K`, a *structure* so that ArkLib's position-query `instVector` does not also apply | CompPoly `CMlPolynomialEval` (B.1) |
| `finEquivK` (`:74-78`) | `def finEquivK : Fin (2 ^ 64) ≃ K where toFun := BitVec.ofFin; invFun := BitVec.toFin; left_inv _ := rfl; right_inv _ := rfl` | `K` is the `2^64` bit patterns | core `BitVec` |
| `instSampleableTypeK` (`:81-83`) | `SampleableType.ofEquiv finEquivK` (with `NeZero (2^64)`) | uniform `K`: a uniform `Fin (2^64)` read as bits | VCVio `ofEquiv`, `SampleableType (Fin n)` (A.5) |
| `limbsEquiv` (`:86-90`) | `toFun := Ext.ofVector …; invFun := Ext.coeffs …; left_inv _ := rfl; right_inv _ := rfl` | `E` is its three limbs | CompPoly `Ext` (B.3) |
| `instSampleableTypeE` (`:93`) | `SampleableType.ofEquiv limbsEquiv` | uniform `E`: three independent uniform limbs | VCVio `Vector` instance, `instSampleableTypeK` |
| `card_E` (`:96`) | `theorem card_E : Fintype.card E = 2 ^ 192 := BF64.card_ext3` | the challenge space has `2^192` elements | CompPoly `card_ext3` |
| `evalOracle` (`:102-106`) | `Query := Vector E n`; `spec := (Vector E n) →ₒ E`; `impl := fun r ↦ do return CMlPolynomialEval.eval₂Mle (← read).values (algebraMap K E) r` | a column as an oracle: query a point `r ∈ E^n`, get `q̃(r)` | ArkLib `OracleInterface`, CompPoly `eval₂Mle` |
| `evalOracle_answer` (`:109-110`) | `(n : ℕ) (q : Column n) (r : Vector E n) : OracleInterface.answer q r = CMlPolynomialEval.eval₂Mle q.values (algebraMap K E) r := rfl` | the unfolding, for rewriting | — |
| `instOracleInterfaceE` (`:115`) | `OracleInterface.instDefault` | a scalar the prover sends: query `()`, answer the scalar | ArkLib `instDefault` |
| `instOracleInterfaceListE` (`:118`) | `OracleInterface.instDefault` | a list the prover sends: query `()`, answer the list | ArkLib `instDefault` |
| `NoOracle` (`ToArkLib/Oracles.lean:26`) | `abbrev NoOracle : Fin 0 → Type := fun i ↦ i.elim0` | the empty family of oracles (matches ArkLib's `Fin 0` instance above) | — |
| `OneOracle` (`:29`) | `abbrev OneOracle (M : Type) : Fin 1 → Type := fun _ ↦ M` | exactly one oracle, of type `M` | — |
| `noOracle_eq` (`:32`) | `theorem noOracle_eq (o o' : ∀ i, NoOracle i) : o = o' := funext fun i ↦ i.elim0` | the empty family has one inhabitant | — |
| `probEvent_uniformSample_le_of_card_le` (`ToVCVio/UniformSample.lean:35-40`) | E.4 | an event with `≤ k` witnesses has probability `≤ k/|α|` | VCVio `probEvent_uniformSample` |
| `probEvent_uniformSample_le_of_subsingleton` (`:44-51`) | E.4 | an event with at most one witness has probability `≤ 1/|α|` | the previous |
| `LeanerVM/Protocol/Basic.lean` | an empty `public section` in `namespace LeanerVM.Protocol` (18 lines) | nothing | — |

Axioms (probe `Layer0`, section 3): every declaration above depends on at most `propext`,
`Classical.choice`, `Quot.sound` (`noOracle_eq`: `Quot.sound` only; `finEquivK`: `propext` only).

Tests, `tests/LeanerVMTests/Protocol/Field.lean` (at `b435631`): a two-variable column
`⟨#v[1, 2, 3, 4]⟩` (`:27`); four `#guard`s that the oracle returns the table entry on the cube
(`:33-36`); one off the cube, `answer col #v[y, ofK 0] = ofK 1 + ofK 3 * y` (`:39`, where at this
pin `2`, `3` are bit patterns, so `1 + y·(1 ⊕ 2)`); agreement with `evalMle` of the lifted table
at `(y, y²)` (`:41-42`); a mutated column answers differently (`:44`); `sampleK`, `sampleE` as
compiled definitions (`:49`, `:52`: they fail to compile if a sampler has no compiler IR);
`#synth OracleInterface E`, `(List E)` (`:59-60`); `example : Fintype.card E = 2 ^ 192 := card_E`
(`:64`).

### E.1 The samplers: uniform, proved, and the diamond on `K`

**Uniformity is proved, by construction.** A `SampleableType` instance cannot be non-uniform
(A.5: the class carries `probOutput_selectElem_eq` and `mem_support_selectElem`, and VCVio derives
`Pr[= x | $ᵗ α] = |α|⁻¹` for every instance). Both instances are `SampleableType.ofEquiv` of a
Mathlib `Equiv` (`α ≃ β` bundles both inverse laws, so it is a bijection; here both laws are
`rfl`), and `ofEquiv` re-proves the two laws (`SampleableType.lean:260-267` at `f9dc47d9`). The
chain for `E` is: the primitive coin `$[0..2^64−1]` (`unifSpec.query`, uniform by
`IsUniformSpec unifSpec`, A.4) → `finEquivK` → three independent draws (VCVio's `Vector`
instance) → `limbsEquiv`. Probe `Layer0` (section 4, all accepted):
```lean
example : Function.Bijective finEquivK := finEquivK.bijective
example : Function.Bijective limbsEquiv := limbsEquiv.bijective
example (x : K) : Pr[= x | $ᵗ K] = (Fintype.card K : ℝ≥0∞)⁻¹ := probOutput_uniformSample K x
example (x : E) : Pr[= x | $ᵗ E] = (Fintype.card E : ℝ≥0∞)⁻¹ := probOutput_uniformSample E x
example (x : E) : Pr[= x | $ᵗ E] = ((2 ^ 192 : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [probOutput_uniformSample, card_E]
example : Pr[⊥ | $ᵗ E] = 0 := probFailure_uniformSample E
example : support ($ᵗ E) = Set.univ := support_uniformSample E
example : ($ᵗ E) = limbsEquiv <$> ($ᵗ (Vector K 3)) := rfl
example : ($ᵗ K) = finEquivK <$> ($ᵗ (Fin (2 ^ 64))) := rfl
```
Instance search (probe `Layer0`, section 1): `SampleableType K` → `instSampleableTypeK`,
`SampleableType E` → `instSampleableTypeE`, `SampleableType (Vector K 3)` →
`instSampleableTypeVector K 3`, `SampleableType (Fin (2 ^ 64))` →
`instSampleableTypeFinOfNeZeroNat (2 ^ 64)`.

**The diamond on `K` (old pins).** Because `K` is `BitVec 64` to instance search and Mathlib has
`FinEnum (BitVec n)`, VCVio's `FinEnum.SampleableType` already supplies a sampler on `K` *without*
leanerVM's instance. Probe `SamplerDiamond` (imports `LeanerVM.Parameters.Field` and VCVio only):
```text
#synth SampleableType K        ⟹  FinEnum.SampleableType K
#synth SampleableType (BitVec 64)  ⟹  FinEnum.SampleableType (BitVec 64)
#synth FinEnum K               ⟹  FinEnum.instBitVec 64
#synth SampleableType E        ⟹  error: failed to synthesize SampleableType E
```
With `LeanerVM.Protocol.Field` imported, leanerVM's instance is found (declared later, same
priority), and the two are **the same term up to unfolding**. Probe `SamplerDiamond2`, both
accepted (exit 0):
```lean
example :
    (instSampleableTypeK).selectElem = (FinEnum.SampleableType K).selectElem := rfl
example : (instSampleableTypeK : SampleableType K) = FinEnum.SampleableType K := rfl
```
and in any case any two samplers on a finite type give every element the same probability
(probe `SamplerDiamond`, accepted on the standard axioms):
```lean
theorem sampler_unique {α : Type} [Fintype α] (s t : SampleableType α) (x : α) :
    Pr[= x | @uniformSample α s] = Pr[= x | @uniformSample α t] := by
  rw [@probOutput_uniformSample α s, @probOutput_uniformSample α t]
```
So the diamond is harmless: no statement can depend on which instance is chosen. On `E` there is
exactly one instance in scope. **Conclusion: both samplers are uniform, proved; no distribution
question remains.**

**`SampleableType K` has no consumer.** No declaration outside `Protocol/Field.lean` mentions it
(`git grep "SampleableType K\|\$ᵗ K\|instSampleableTypeK\|finEquivK" b435631 -- LeanerVM tests
docs`: only the blueprint's Layer 0 sketch), and leanVM samples every challenge in `E`
(`crates/fiat_shamir/src/lib.rs:95-99`, `pub fn sample(&mut self) -> F192`; the module
docstring `crates/primitives/src/field/mod.rs:3-6`: "challenges, sumcheck/GKR values, and
transcript scalars are E-valued"). The blueprint's own dependency row says "Layer 0 supplies the
`E` instance" (`protocol-blueprint.md:251`). At the old pins the instance is moreover a
definitional duplicate of the library one. Minor finding "`SampleableType K` is unused audit
surface" (G). (It is still needed as a *building block* of `instSampleableTypeE`, through
VCVio's `Vector` instance; at the old pin the library `FinEnum` instance would serve.)

**At `144c5aa` (new pins).** `K` is a structure (B.3 → F.3), so `FinEnum (BitVec 64)` no longer
applies to it and the diamond disappears; `finEquivK` becomes
`toFun := fun i ↦ BF64.ofBitVec (BitVec.ofFin i)`, `invFun := fun x ↦ x.toBitVec.toFin`
(`git diff b435631 144c5aa -- LeanerVM/Protocol/Field.lean`); `instSampleableTypeK` is then the
only `K` sampler (by reading; not run). VCVio `a4232d08` states uniformity directly as a class
law, "the output measure is `uniformOn Set.univ`":
`VCVio/OracleComp/Constructions/SampleableType/Basic.lean:51-57` (at `a4232d08`)
```lean
class SampleableType (β : Type) where
  /-- The canonical sampler of `β`, written `$ᵗ β`. -/
  selectElem : ProbComp β
  /-- The canonical sampler denotes the uniform measure on `β`. -/
  evalDist_selectElem_eq_uniform :
    ∀ [MeasurableSpace β] [MeasurableSingletonClass β],
      𝒟[selectElem] = uniformOn Set.univ
```
and proves sampler irrelevance upstream (`SampleableType.prEvent_uniformSample_inst_irrel`,
`NativeMeasure.lean:280-284`), the statement of the probe's `sampler_unique`.

### E.2 The oracle interface of the stack

- **Query**: `Vector E n`, a point `r ∈ E^n`. **Answer**: `E`
  (`spec := (Vector E n) →ₒ E`). **Implementation**: read the column and return
  `eval₂Mle q.values (algebraMap K E) r`, which is `evalMle (map (algebraMap K E) q) r =
  Σ_i ofK(q_i) · ∏_j (bit_j(i) ? r_j : 1 − r_j)`, the multilinear extension `q̃(r)` of the
  `K`-table lifted to `E` (B.1). Probe `Layer0`, section 5, accepted:
  ```lean
  example (n : ℕ) : OracleInterface.Query (Column n) = Vector E n := rfl
  example (n : ℕ) (r : Vector E n) : OracleInterface.Response (Message := Column n) r = E := rfl
  example (n : ℕ) (q : Column n) (r : Vector E n) :
      OracleInterface.answer q r =
        CMlPolynomialEval.eval (CMlPolynomialEval.map (algebraMap K E) q.values) r := by
    rw [evalOracle_answer, CMlPolynomialEval.eval₂_mle_eq_eval₂]; rfl
  ```
- This is leanVM's oracle: "we commit to a `K`-valued multilinear, and opening claims are in `E`"
  (`doc/leanvm/body/b-polynomial-commitment-scheme.tex:4`).
- **Name**: the code calls it `evalOracle`, as the blueprint does (`protocol-blueprint.md:638`);
  its full name is `LeanerVM.Protocol.evalOracle` (probe `Layer0`: `#synth OracleInterface
  (Column 3)` ⟹ `evalOracle 3`).
- **Why a structure.** `CMlPolynomialEval K n` is `@[reducible]` `Vector K (2^n)` (B.1), and ArkLib
  has `instVector : OracleInterface (Vector α n)` with `Query := Fin n` (positions). Were `Column`
  an abbreviation, a column could be queried at positions. The structure prevents it; the
  justification is correct at `dca90385` (`OracleInterface.lean:333-337`).
- **Other instances.** `OracleInterface E` and `OracleInterface (List E)` are ArkLib's
  `instDefault`: query `Unit`, answer the whole message (probe `Layer0`:
  `OracleInterface.Query E = Unit := rfl`, `OracleInterface.answer x () = x := rfl`, the same for
  `List E`). They are the "the verifier reads what the prover sent" interface for scalars and
  coefficient lists; ArkLib registers no default instance for any type, at `dca90385` or at
  `7653a901` (`git grep` for `instDefault` instances: only two local ones in
  `ArkLib/ProofSystem/RingSwitching/Packing/Spec.lean:105-106` at `7653a901`), so no ambiguity yet.

No issue found with the oracle interface: the query space, the answer and the lift are those of
the specification, and the mutated-column test makes the answer depend on the column.

### E.3 `card_E`

`theorem card_E : Fintype.card E = 2 ^ 192 := BF64.card_ext3` (`Protocol/Field.lean:96`). The
`Fintype E` instance is CompPoly's `Ext.instFintype` (probe `Layer0`: `#synth Fintype E` ⟹
`Extension.Ext.instFintype`), and `card_ext3` is `(2^64)^3` by the coefficient bijection
(B.3). `Fintype.card` does not depend on the instance (all `Fintype α` instances are equal:
`Fintype` is a subsingleton), so the statement is robust. Correct. At `144c5aa` the proof is
unchanged in text; `Fintype K` is leanerVM's proof-only `Fintype.ofFinite K` and
`card_ext3 [Fintype Ext3]` accepts any instance (F.3).

### E.4 The counting bounds

`LeanerVM/Protocol/ToVCVio/UniformSample.lean:31-51` (at `b435631`)
```lean
variable {α : Type} [SampleableType α] [Fintype α]

/-- An event with at most `k` witnesses has probability at most `k/|α|` under a uniform
sample. -/
theorem probEvent_uniformSample_le_of_card_le (p : α → Prop) [DecidablePred p] {k : ℕ}
    (h : (Finset.univ.filter p).card ≤ k) :
    Pr[p | $ᵗ α] ≤ ((k / Fintype.card α : ℝ≥0) : ℝ≥0∞) := by
...
/-- An event any two of whose witnesses are equal has probability at most `1/|α|` under a
uniform sample. -/
theorem probEvent_uniformSample_le_of_subsingleton (p : α → Prop)
    (h : ∀ a b, p a → p b → a = b) :
    Pr[p | $ᵗ α] ≤ ((1 / Fintype.card α : ℝ≥0) : ℝ≥0∞) := by
```
**Correct.** The left side is `(filter p).card / |α|` exactly (VCVio `probEvent_uniformSample`,
A.5); the right side is the real `k/|α|` (division in `ℝ≥0`, then coerced; `|α| ≠ 0` because a
`SampleableType` is nonempty). **Not vacuous, and the hypotheses carry the weight.** Probe
`CountingBounds` (all accepted, standard axioms; the only messages are unused-variable warnings):
```lean
theorem one_witness : Pr[fun x : Fin 4 ↦ x = 2 | $ᵗ (Fin 4)] = 1 / 4
theorem one_witness_bound :
    Pr[fun x : Fin 4 ↦ x = 2 | $ᵗ (Fin 4)] ≤ ((1 / Fintype.card (Fin 4) : ℝ≥0) : ℝ≥0∞)
theorem rhs_eq : ((1 / Fintype.card (Fin 4) : ℝ≥0) : ℝ≥0∞) = 1 / 4          -- attained
theorem two_witnesses : Pr[fun x : Fin 4 ↦ x = 1 ∨ x = 2 | $ᵗ (Fin 4)] = 1 / 2
theorem two_witnesses_exceed :
    ¬ Pr[fun x : Fin 4 ↦ x = 1 ∨ x = 2 | $ᵗ (Fin 4)] ≤ 1 / 4               -- hypothesis needed
theorem two_witnesses_bound :
    Pr[fun x : Fin 4 ↦ x = 1 ∨ x = 2 | $ᵗ (Fin 4)]
      ≤ (((2 : ℕ) / Fintype.card (Fin 4) : ℝ≥0) : ℝ≥0∞)                     -- k = 2, attained
theorem one_bad_challenge (c : E) :
    Pr[fun x : E ↦ x = c | $ᵗ E] = ((2 ^ 192 : ℕ) : ℝ≥0∞)⁻¹
theorem one_bad_challenge_bound (c : E) :
    Pr[fun x : E ↦ x = c | $ᵗ E] ≤ ((1 / Fintype.card E : ℝ≥0) : ℝ≥0∞)
```
Consumers at `b435631`: `…_of_subsingleton` in the public-input phase
(`PublicInput.lean:362`); `…_of_card_le` only through it.

**At `144c5aa`.** Both statements were restated on VCVio's new probability API
(`git diff b435631 144c5aa -- LeanerVM/Protocol/ToVCVio/UniformSample.lean`): only the left side
changes, `Pr[p | $ᵗ α]` becomes `Pr{let sample ← $ᵗ α}[p sample]`; binders, hypotheses and right
sides are unchanged. At VCVio `a4232d08`, `Pr{…}[…]` is a macro for the measure of the event
`{True}` under the computation returning the proposition:
`VCVio/EvalDist/ProbabilityNotation.lean:65-69`
```lean
macro_rules (kind := prEvent)
  -- `doSeqBracketed`
  | `(Pr{{$items*}}[$t]) => `(𝒟[do $items:doSeqItem* return $t:term] {True})
  -- `doSeqIndent`
  | `(Pr{$items*}[$t]) => `(𝒟[do $items:doSeqItem* return $t:term] {True})
```
**The two statements are the same mathematical statement.** At each pin the left side equals the
same closed form by a library theorem: at `f9dc47d9`, `probEvent_uniformSample : Pr[ p | $ᵗ α] =
(Finset.univ.filter p).card / Fintype.card α` (`SampleableType.lean:224-226`); at `a4232d08`,
`SampleableType.prEvent_uniformSample : Pr{let x ← $ᵗ α}[p x] = (Finset.univ.filter p).card /
(Fintype.card α : ENNReal)` (`Constructions/SampleableType/NativeMeasure.lean:41-45`). And VCVio
`a4232d08` proves its measure semantics agrees with the old mass-function semantics on discrete
answer spaces (`OracleComp/EvalDist/UniformCompatibility.lean:47`,
`EvalDist/PFunctorMeasure.lean:96-106`, "Under an agreeing measure specification the free-monad
fold satisfies the façade bridge"). So the restated bounds bound the same number by the same
number. (Verified by reading; not re-run at the new pin.)

### E.5 Conformance with the blueprint's Layer 0 (`protocol-blueprint.md:625-650` at `b435631`)

| Blueprint | Code | Verdict |
|---|---|---|
| `instance : SampleableType K  -- a uniform Fin (2^64) read as a bit pattern` | `instSampleableTypeK := SampleableType.ofEquiv finEquivK` | agrees; unused (E.1) |
| `instance : SampleableType E  -- three independent limbs through Ext.ofVector; never enumerates` | `instSampleableTypeE := SampleableType.ofEquiv limbsEquiv` | agrees |
| `theorem card_E : Fintype.card E = 2 ^ 192` | identical | agrees |
| `instance evalOracle (n : ℕ) : OracleInterface (Column n) where Query := Vector E n … answer := eval₂Mle q (algebraMap K E)` | identical | agrees |
| `theorem evalOracle_answer (q : Column n) (r : Vector E n) : …` | `theorem evalOracle_answer (n : ℕ) (q : Column n) (r : Vector E n) : …` | **mismatch**: `n` explicit in the code, implicit (auto-bound) in the sketch; callers must write `evalOracle_answer n q r` although `n` is determined by `q` |
| "`SampleableType.ofEquiv` on the carrier views, as ArkLib's own `KoalaBear.Ext6.sampleableType`, and a test probes that it has compiler IR" | yes (`sampleK`, `sampleE`) | agrees |
| Tests: "`#guard`s that the oracle answers `evalMle` on a two-variable table, on and off the cube, with a mutated column; `example : Fintype.card E = 2 ^ 192 := card_E`" | yes (E.0) | agrees |
| — | `instOracleInterfaceE`, `instOracleInterfaceListE` in `Protocol/Field.lean` | **not in the Layer 0 sketch**, nor in the interface list `protocol-blueprint.md:1400` ("`instSampleableTypeE  evalOracle  card_E`"), which also omits `instSampleableTypeK` and `Column` (the latter is at `:666`) |
| `protocol-blueprint.md:251`: "Layer 0 supplies the `E` instance" | Layer 0 supplies `K` and `E` | internal inconsistency of the blueprint (E.1) |
| "Add ArkLib at `dca90385` … the root pin `3468b38c` wins" (`:629-631`; `:633-635` at `144c5aa`), "The sampler is the point at which a wrong `Fintype` would enumerate `2^64` or `2^192` elements (finding P3)" (`:645-646`; `:649-650` at `144c5aa`) | at `144c5aa` the pins moved and `Fintype K` is proof-only | stale after #61 (the added disclaimer at `144c5aa:protocol-blueprint.md:52-54` covers "dependency API tables and signatures", not this prose) |

`NoOracle`/`OneOracle` are specified in the spine section (`protocol-blueprint.md:472`,
`:1377`), and `ToVCVio/UniformSample.lean`'s bound is cited at `:1046`; both agree with the code.

---

## F. Duplicates and upstream

Revisions: old pins as in the header; new pins (at `144c5aa`, now in `.lake/packages/`): CompPoly
`572f9973`, VCVio `a4232d08`, Clean `42fe4b26`, ArkLib `7653a901`, Mathlib/Lean `v4.34.1`. The
`upstream/` clones: `CompPoly-main` is `572f9973` (the new pin itself); `VCVio-main` is
`f5119c64`, an ancestor of the new pin `a4232d08` (`git merge-base --is-ancestor`); `clean-main`
is `fba2a29f`, contained in the new pin `42fe4b26` (which is Clean #474's branch merged with
`main`). So "upstream `main`" and "new pin" coincide up to a few commits; statements below name
the revision read.

### F.1 `LeanerVM/Protocol/ToVCVio/UniformSample.lean`

- **At VCVio `f9dc47d9`**: no duplicate. VCVio has the equality `probEvent_uniformSample` and
  `probOutput_uniformSample` (A.5); the two local bounds are its two-line corollaries.
- **At VCVio `a4232d08`**: `…_of_card_le` is, up to a coercion, the `←` direction of
  ```lean
  theorem prEvent_uniformSample_le_div_iff {c : ℕ} :
      Pr{let x ← $ᵗ α}[p x] ≤ c / (Fintype.card α : ℝ≥0∞) ↔
        (Finset.univ.filter p).card ≤ c
  ```
  (`VCVio/OracleComp/Constructions/SampleableType/NativeMeasure.lean:126-130`, section variables
  `{α : Type} [SampleableType α] [Fintype α] (p : α → Prop) [DecidablePred p]`, `:117`); the local
  right side `((k / Fintype.card α : ℝ≥0) : ℝ≥0∞)` equals `k / (Fintype.card α : ℝ≥0∞)` by
  `ENNReal.coe_div`. For single-witness events VCVio has
  `prEvent_uniformSample_eq_singleton : Pr{let x ← $ᵗ α}[x = a] = (Fintype.card α : ℝ≥0∞)⁻¹`
  (`:110-111`), but no "at most one witness" form (`grep subsingleton\|card_le_one` in
  `SampleableType/` and `EvalDist/ProbabilityBounds.lean`: none). The probe's `sampler_unique` is
  upstream as `prEvent_uniformSample_inst_irrel` (`:280-284`). **Plan**: at the new pin
  `…_of_card_le` is redundant and can be replaced by the upstream `iff`; keep (or upstream)
  `…_of_subsingleton`.

### F.2 `LeanerVM/Protocol/ToCompPoly/{Multilinear,BitProductTable,Stacking,AmbientStacking}.lean`

Checked by name and by content keyword (`sumCube`, hypercube sums, `hadamard`/pointwise
products, `evalMle_eq_sum`, `evalMle_split`/append, `bitProductTable`/`powersTable`, stacking)
in CompPoly `3468b38c` and `572f9973` (`CompPoly/Multilinear/`) and ArkLib `dca90385` and
`7653a901` (`ArkLib/ToCompPoly/`): **no counterpart** of any of the four modules' 80-odd
declarations. What CompPoly added between the pins in `Multilinear/Basic.lean` is linearity
(`eval_add`, `eval_zero`, `eval_smul` for both representations, `map_eval`,
`evalWithProducts`; `git diff 3468b38c 572f9973 -- CompPoly/Multilinear/Basic.lean`), which the
local modules do not restate. The local modules remain CompPoly candidates.

**Name clash at the new pins (inferred, not run).** CompPoly `572f9973` now declares
`CompPoly.CMlPolynomialEval.eval_zero` (`CompPoly/Multilinear/Basic.lean:719`, in
`namespace CompPoly … namespace CMlPolynomialEval`), and ArkLib `7653a901` declares the same name
in `ArkLib/ToCompPoly/Multilinear/Basic.lean:35-45` (`namespace CompPoly.CMlPolynomialEval …
theorem eval_zero`). ArkLib builds against its own CompPoly pin `df591bb8` (its
`lake-manifest.json`), which lacks it; leanerVM's root pin `572f9973` wins the resolution. So a
leanerVM file importing `ArkLib.ToCompPoly.Multilinear.Basic` (or its importers
`ArkLib/ToCompPoly/Multilinear/NestedEvaluationTree.lean`,
`ArkLib/Commitments/Functional/Hachi/ZeroCheck/Completeness.lean`) would fail with a duplicate
declaration. leanerVM imports none of them today (`git grep "ArkLib.ToCompPoly" 144c5aa`: none),
but the blueprint names that module's `eval_eq_MvPolynomial_MLE` as *the* bridge from tables to
Mathlib multilinears (`protocol-blueprint.md:246`). Verify by elaborating a two-line file that
imports both modules after the rebuild. Recorded as a note (G).

### F.3 What has landed upstream since each pin, and what the blueprint should plan for

**CompPoly `3468b38c` → `572f9973`** (64 commits):
- *#329* "isolate the BF64 presentation" (`e5f87c8`): `BF64` is now a **structure**,
  `structure BF64 where toBitVec : BitVec 64 deriving DecidableEq, BEq`
  (`CompPoly/Fields/Binary/BF64/Impl.lean:57-61` at `572f9973`), with `ofBitVec`. Consequences:
  CompPoly's field instances no longer leak onto `BitVec 64` (B.3's hazard is gone); core's
  `BitVec` simplification procedures no longer see `K` (the `NumeralHazard` probe's hazard is gone,
  by reading); and `FinEnum (BitVec 64)` no longer gives a sampler on `K` (E.1).
- **Numerals change meaning.** There is no `OfNat BF64` instance; a numeral `n ≥ 2` elaborates
  through Mathlib's `NatCast` numeral instance, and the cast is by parity:
  ```lean
  /-- Cast a natural number by its parity in characteristic two. -/
  @[inline] def natCast (n : ℕ) : BF64 := if n % 2 = 0 then 0 else 1

  instance : NatCast BF64 := ⟨natCast⟩
  ```
  (`Impl.lean:223-227` at `572f9973`). So `(2 : K) = 0`, `(3 : K) = 1`, `(0x1B : K) = 1`: the
  characteristic-two meaning. Bit patterns are written `K.ofBits n`, which leanerVM defines at
  `144c5aa` (`LeanerVM/Parameters/Field.lean`):
  ```lean
  def K.ofBits (n : ℕ) : K := BF64.ofBitVec (BitVec.ofNat 64 n)
  ```
  **Effect on probes and fixtures.** Every numeral `≥ 2` in `K` written at the old pin *compiles
  at the new pin with another value*. The probe `FieldFidelity` at the new pin would read
  `(0x01090913877ed8ed : K) * 0x66ab35ac2768468f = 0x50c4519dc383744a` as `1 * 1 = 0` (parities of
  the three words) and fail; its `#guard (2 : K) ≠ 0` would fail, `#guard ((2 : ℕ) : K) = 0` would
  pass, `g = (2 : K)` would fail (`g` is `K.ofBits 0x2` at `144c5aa`). Its conclusions (B.4) are
  about the old pin and stand there; at the new pin the field and its encoding are the same
  (`ofBitVec` of the same words), so re-running it with `K.ofBits` on every literal would be the
  check (unverified: no run is possible now). The probe `NumeralHazard` is moot at the new pin.
  #61 rewrote leanerVM's fixtures with `K.ofBits` (e.g. `tests/LeanerVMTests/Protocol/Field.lean`
  at `144c5aa`: `⟨#v[1, K.ofBits 2, K.ofBits 3, K.ofBits 4]⟩`) and pins the new meaning
  (`tests/LeanerVMTests/Parameters/Field.lean:50-51` at `144c5aa`: `#guard (2 : K) = 0`,
  `#guard K.ofBits 2 ≠ (2 : K)`). A scan of `144c5aa` for `ofK n`, `(n : K)`, `(n : E)`,
  `: K := n`, `E.ofLimbs n` with `n ≥ 2` or a hex literal finds only those two intended lines and
  `E.ofLimbs 0x0000000000000000 …` (= 0) in `tests/LeanerVMTests/Semantics/Blake2s.lean:197`;
  numerals inside vectors and other shapes were not scanned (unverified).
- *#330* "separate extension arithmetic from finite certificates" (`cf340b2`):
  `ExtensionParams F` no longer takes `[Fintype F]`; its `q` is uncertified data ("Raw arithmetic
  does not certify this value. Field laws require a separate proof that `Nat.card F = q`",
  `CompPoly/Fields/Extension/Arithmetic.lean:57-61` at `572f9973`), supplied for `Ext3` by
  `instance : Fact (Nat.card BF64 = ext3Params.q) := ⟨nat_card_bf64⟩` (`Ext3.lean:143-144`).
- *#331* "avoid eager BF64 enumeration at native startup" (`290c351`): no `Fintype BF64`; there
  is `instance : Finite BF64` and `theorem card_bf64 [Fintype BF64] : Fintype.card BF64 = 2 ^ 64`
  (`Impl.lean:459-468`), likewise `card_ext3 [Fintype Ext3]` (`Ext3.lean:206-208`). leanerVM
  supplies, at `144c5aa`, `noncomputable instance : Fintype K := Fintype.ofFinite K` ("A
  proof-only enumeration of `K`; executable code uses its explicit bit coordinates"), from which
  CompPoly's `Ext.instFintype [Fintype F]` (`Extension/Cardinality.lean:52`) gives `Fintype E`.
  **So `Fintype K` is now proof-only**: `Fintype.card K` in statements is unchanged in meaning
  (a subsingleton class), no executable can evaluate it, and the startup OOM of the eager
  instance is gone. The blocker on executables (leanISA status finding P3) is lifted by the new
  pin; the blueprint's executable `verify` and the differential tests are unblocked on this
  count (other blockers not assessed here).
- leanerVM also adds, at `144c5aa`, its own `instDecidableEqK` (decided on `toBitVec`) beside
  CompPoly's derived `DecidableEq BF64`: two instances, equal as propositions (`Decidable` is a
  subsingleton), chosen for kernel reduction per its docstring. Harmless; one more trusted-surface
  line.
- `LawfulBEq (Ext P)` now exists (`Extension/Arithmetic.lean:380`, given `LawfulBEq F`), so
  `CMvPolynomial n E` gets `C`, `X` and ring operations at the new pin (B.2); the blueprint's
  "no `LawfulBEq E` at the pin" (`protocol-blueprint.md:570`) is stale after #61 (not re-checked by
  instance search: no run).
- New fields: the AES polynomial field `GF(2^8)`, modulus `X^8 + X^4 + X^3 + X + 1`
  (`CompPoly/Fields/Binary/Aes/Basic.lean`, #356), and its embedding into GHASH `GF(2^128)` (#357).
  leanVM's Flock uses the same `GF(2^8)` and an embedding `φ₈ : GF(2^8) → K`
  (`crates/primitives/src/field/gf2_8.rs`, `phi8_tower.rs:15-24`); CompPoly has the source field
  now but no embedding into `BF64`, so the blueprint's gap statement (`protocol-blueprint.md:281`,
  "no `GF(2^8) ↪ E` embedding") remains true but should say the field itself has landed.
- Serialization (#373-#376: byte codecs for every field carrier, "exact fiber counts and the
  bias bound of the challenge decoder"): relevant to the compiled verifier's transcript
  (Layer 12) and to modelling `sample() -> F192` from a hash output; not assessed further.

**VCVio `f9dc47d9` → `a4232d08`**: the primary semantics is a Mathlib `Measure` (`𝒟[mx]`), a
fold of the free monad with per-query measures, proved to agree with the old mass-function
semantics on discrete answer spaces (E.4); `probOutput`, `probEvent`, `probFailure` are
deprecated since 2026-09-13 (`VCVio/EvalDist/Defs/Basic.lean:90-110` at `a4232d08`,
`@[deprecated "VCVio retiring probability API: use 𝒟[mx] {x | p x}"]`) in favour of
`Pr{let x ← c}[P x]`; `SampleableType`'s law is now "the output measure is uniform" (E.1);
PolyFun is a separate pinned dependency (`upstreams.json` at `144c5aa`). The blueprint's
signatures (`Pr[α β ← uniform; …] ≤ …`, `protocol-blueprint.md:930` at `144c5aa`) are in the
old notation, covered by the disclaimer `144c5aa:protocol-blueprint.md:52-54`. What a reader
trusts (A.6) changes accordingly: the measure fold (`VCVio/EvalDist/PFunctorMeasure/Core.lean:226-229`,
`instEvalDistSemanticsFreeM`; a bind whose continuation is not almost-everywhere measurable
denotes `0`, `:102`, which cannot arise for discrete answer types) plus the compatibility proof.

**Clean `93c9d1ef` → `42fe4b26`**: Clean is a `module` library (#460), so
`LeanerVM/Parameters/CleanField.lean` became a `module` at `144c5aa` and the "Clean bridge is
plain" convention (leanISA status finding C8) retires; the balance proofs were ported (#474);
`balanceOf`/`BalancedInteractions` are unchanged, #464 (directed channels) is not in the pin
(`git grep DirectedChannel 42fe4b26`: none), so C.5 and C.7 stand.

**Lean `v4.33.1` → `v4.34.1`, Mathlib `v4.34.1`**: see `git show 144c5aa:docs/dependencies.md`.
The proof-system sources changed only in proofs and imports (brief §8); for Layer 0 the diff is
the `finEquivK` body, docstrings, and the two restated bounds (E.1, E.4).

---

## G. Findings

No critical or major finding: nothing in the libraries' objects or in Layer 0 lets an unsound
verifier be "proved". The fields are leanVM's bit for bit (B.4), the samplers are uniform by proof
(E.1), the oracle answers the specification's evaluation (E.2), the bounds are correct and
non-vacuous (E.4), and the trusted base is the kernel plus the three standard axioms, enforced
transitively (D.3).

### G.1 The relation ladder conflates the field sum with Clean's balance relation — minor

- **Evidence.** `protocol-blueprint.md:359` (at `b435631`; `:363` at `144c5aa`, same text): "Over `K` the side
  condition fails for every real ensemble and a tuple pushed twice and never pulled balances
  (#16)." Probe `CleanBalance` (C.5): `pushedTwice_balance` (the field sum of `[push 7, push 7]`
  is `0`) but `pushedTwice_not_balanced` (Clean's `BalancedInteractions` rejects it, through the
  side condition), and `length_le_one_of_balanced`, `honest_pair_not_balanced`,
  `statement_forces_at_most_one_interaction`.
- **Classification.** An error of the blueprint (imprecise wording; the conclusion "unusable
  here" is right).
- **Proposed change.** As it stands: "Over `K` the side condition fails for every real ensemble
  and a tuple pushed twice and never pulled balances (#16)." Proposed: "Over `K`
  (`ringChar K = 2`) the field sum alone accepts a tuple pushed twice and never pulled
  (`1 + 1 = 0`), and the side condition `length < ringChar K` that is meant to exclude it admits
  at most one interaction per channel, so `Ensemble.Statement` holds of no ensemble with a real
  bus: Clean's soundness is vacuous and its completeness false over `K` (#16)." Reason: the
  reader should see that Clean's relation is unsatisfiable, not unsound.

### G.2 `SampleableType K` is unused audit surface, and the blueprint disagrees with itself about it — minor

- **Evidence.** E.1: no consumer outside `Protocol/Field.lean`; leanVM samples only `E`
  (`crates/fiat_shamir/src/lib.rs:95-99`); at the old pins it is definitionally the library's
  `FinEnum.SampleableType K` (probe `SamplerDiamond2`). The blueprint's Layer 0 sketch declares it
  (`protocol-blueprint.md:634`) while its dependency table says "Layer 0 supplies the `E`
  instance" (`:251`) and its interface list names only `instSampleableTypeE` (`:1400`).
- **Classification.** Avoidable audit surface (not a divergence from leanVM).
- **Proposed change.** Keep the instance only as the building block of the `E` sampler (VCVio's
  `Vector` instance needs `SampleableType K`; at the new pins no library instance exists) and say
  so. Blueprint `:634`, as it stands: "`instance : SampleableType K          -- a uniform
  Fin (2^64) read as a bit pattern`". Proposed: "`instance : SampleableType K          -- a
  uniform Fin (2^64) read as a bit pattern; only the building block of the E sampler: every
  leanVM challenge is in E (fiat_shamir/src/lib.rs:95)`". Blueprint `:251`, proposed: "Challenge
  sampling; Layer 0 supplies the `E` instance (built from a `K` instance)". Same comment on the
  instance's docstring in `Protocol/Field.lean:80`.

### G.3 `evalOracle_answer` takes `n` explicitly — minor

- **Evidence.** Code `Protocol/Field.lean:109`: `theorem evalOracle_answer (n : ℕ) (q : Column n)
  (r : Vector E n)`; blueprint `:641`: `theorem evalOracle_answer (q : Column n) (r : Vector E n)`.
- **Classification.** Code/blueprint mismatch, cosmetic.
- **Proposed change.** Code: `theorem evalOracle_answer {n : ℕ} (q : Column n) (r : Vector E n) :`
  (`n` is determined by `q`); or blueprint: add `(n : ℕ)`. Prefer the code change.

### G.4 The scalar oracle interfaces are trusted surface the blueprint does not list — minor

- **Evidence.** `instOracleInterfaceE`, `instOracleInterfaceListE` (`Protocol/Field.lean:115`,
  `:118`) decide what a verifier may learn of a scalar or list the prover sends (the whole
  message, query `()`); they appear in neither the Layer 0 sketch (`protocol-blueprint.md:633-650`)
  nor the interface list (`:1400`).
- **Classification.** Omission in the blueprint.
- **Proposed change.** Add to the Layer 0 sketch after `evalOracle_answer`:
  "`instance : OracleInterface E := OracleInterface.instDefault        -- a scalar message is read
  whole`" and "`instance : OracleInterface (List E) := OracleInterface.instDefault  -- likewise a
  coefficient list`", with the sentence "ArkLib registers no default interface; delete these when
  it does (the test `#synth`s will turn ambiguous)." Add both names and `instSampleableTypeK` to
  `:1400`.

### G.5 Layer 0 prose is stale after the Lean 4.34.1 upgrade — minor (at `144c5aa`)

- **Evidence.** At `144c5aa`: `protocol-blueprint.md:633-635` still says "Add ArkLib at `dca90385`
  … ArkLib requires CompPoly at the `v4.33.1` tag; the root pin `3468b38c` wins"; `:649-650` "The
  sampler is the point at which a wrong `Fintype` would enumerate `2^64` or `2^192` elements
  (finding P3)" while `Fintype K` is now proof-only and the eager instance gone (F.3); `:574` "no
  `LawfulBEq E` at the pin" while CompPoly `572f9973` has `LawfulBEq (Ext P)`
  (`Extension/Arithmetic.lean:380`); `:285` says CompPoly has no `GF(2^8) ↪ E` embedding, true, but
  the AES field `GF(2^8)` itself has landed (`CompPoly/Fields/Binary/Aes/`). The disclaimer added
  at `:52-54` covers "dependency API tables and signatures", not these sentences.
- **Classification.** Stale text (a deviation forced by an upstream library that has since
  been lifted).
- **Proposed change.** `:633-635` → "ArkLib is the `Arklib` requirement; current pins in
  `upstreams.json` and `docs/dependencies.md`." `:649-650` → "At CompPoly `3468b38c` a sampler
  through `Fintype` would enumerate the field (leanISA finding P3); since CompPoly #331 `Fintype K`
  is proof-only (`Fintype.ofFinite`) and the samplers go through explicit equivalences." `:574` →
  re-check `LawfulBEq E` at the new pin and, if found, drop the restriction to `K`-coefficient
  polynomials or keep it deliberately with a reason. `:285` → "… no embedding `GF(2^8) ↪ K`
  (CompPoly now has the AES field `GF(2^8)`, #356, and its embedding into GHASH only)".

### G.6 The eager `Fintype BF64` blocked every executable at the old pins — note (retired)

- **Evidence.** B.3; `docs/roadmap/leanisa-status.md:753-769` at `b435631`; CompPoly #331
  (`290c351`), in the new pin.
- **Classification.** A deviation forced by an upstream library (no executable verifier, no
  differential tests, library-only test driver); retirement condition "CompPoly stops threading
  `[Fintype F]` through `Ext` and `Fintype BF64` is not evaluated at startup" is **met at
  `144c5aa`** (F.3). Whether `lake test` can again be an executable is for the owner to check.

### G.7 `simp` misreads `K` arithmetic (old pins) — note (retired)

- **Evidence.** Probe `NumeralHazard` (H): `example : (1 : K) + 1 = 0 := by simp` leaves `⊢ False`
  and the kernel rejects the term (`application type mismatch … (2#64 = 0#64) = False`);
  `theorem bad : ¬ ((1 : K) + 1 = 0) := by simp` and
  `theorem bad_mul : (2 : K) * 0x8000000000000000 = 0 := by simp` are *elaborated* by `simp` (core's
  `BitVec` simplification procedures read `K`'s `+`, which is XOR, as addition modulo `2^64`) and
  **rejected by the kernel** (`(kernel) declaration type mismatch`), exit 1. So a false statement
  about `K` was not proved: the kernel is the safety net, and the axiom audit is a second one
  (after the kernel error Lean adds `bad` as an axiom for error recovery, `'bad' depends on axioms:
  [bad, propext, Quot.sound]`, which `audit-axioms.lean` would reject). Recorded as leanISA status
  finding E6 at `b435631`. Companion: CompPoly's instances apply to every `BitVec 64` (probe
  `FieldFidelity`: `(3 : BitVec 64) + 5 = 6#64`); no leanerVM misuse (B.3).
- **Classification.** Forced by an upstream library (`abbrev BF64 := BitVec 64`); **retired** at
  the new pin by CompPoly #329 (`BF64` a structure). In its place: numerals in `K` now mean their
  characteristic-two value (G.8).

### G.8 Numerals in `K` changed meaning at the new pins — note (for every later probe and fixture)

- **Evidence.** F.3: `(2 : K)` is `x` at CompPoly `3468b38c` and `0` at `572f9973`; words are
  `K.ofBits n` at `144c5aa`. A literal written for the old pin compiles at the new one with another
  value. #61 converted leanerVM's fixtures (scan in F.3); one comment is left behind:
  `tests/LeanerVMTests/Protocol/Field.lean:25-26` and `:37-38` at `144c5aa` still say "The column
  `[1, 2, 3, 4]`" and "`1 + y·(1 + 2) = 1 + 3y` … with `-1 = 1` and `2 = x`" while `2 : K` is now `0`.
- **Classification.** Upstream change adopted; documentation hazard.
- **Proposed change.** In that test: "The column `[1, x, x + 1, x²]` (words `1, 2, 3, 4` as
  `K.ofBits`) …" and "at `(y, 0)` the value is `1 + y·(1 + x) `". Any future probe of this review
  run at the new pins must write words as `K.ofBits` (the probe `FieldFidelity` would otherwise
  fail spuriously).

### G.9 The ArkLib bridge `eval_eq_MvPolynomial_MLE` is likely unimportable at the new pins — note (unverified)

- **Evidence.** F.2: duplicate `CompPoly.CMlPolynomialEval.eval_zero` in CompPoly `572f9973`
  (`Multilinear/Basic.lean:719`) and ArkLib `7653a901` (`ToCompPoly/Multilinear/Basic.lean:45`),
  whose own CompPoly pin `df591bb8` lacks it. Not run (no Lean in this checkout).
- **Classification.** Forced by upstream version skew.
- **Proposed change.** Before a phase imports `ArkLib.ToCompPoly.Multilinear.Basic`, elaborate a
  file importing it and `CompPoly.Multilinear.Basic`; if it fails, file the clash upstream (ArkLib
  should drop its `eval_zero` once its CompPoly pin has one) and cite the blueprint's bridge
  (`:246`) with that caveat.

### G.10 The local counting bound is redundant with VCVio at the new pin — note

- **Evidence.** F.1: `SampleableType.prEvent_uniformSample_le_div_iff`
  (`NativeMeasure.lean:127` at `a4232d08`).
- **Classification.** Duplicate of upstream after the pin moved.
- **Proposed change.** Replace `probEvent_uniformSample_le_of_card_le` by the upstream `iff`
  (plus `ENNReal.coe_div`), keep `…_of_subsingleton` (no upstream form) as the one local lemma or
  upstream it, per the blueprint's generic-code rule (`protocol-blueprint.md:329`).

### Negative results (checked, no issue)

- `K`, `E`, `y`, `ofK`, `g` against the specification, the Rust and the Python: moduli, bit
  order, limb order, embedding, generator, product formula (B.4 table; probe `FieldFidelity`: 3 + 8
  reference vectors, the defining relation, inverses, two mutations).
- Irreducibility, field structure, cardinalities: proved in CompPoly without `native_decide`
  (Rabin certificate checked by `rfl`; axioms standard, probe `Layer0`).
- Uniformity of both samplers; the diamond on `K` is definitional (E.1).
- `evalOracle`: query, answer, lift, the reason for the structure (E.2); `card_E` (E.3);
  `NoOracle`/`OneOracle`/`noOracle_eq` (trivially correct; ArkLib's `Fin 0` interface instance
  matches `NoOracle` at both ArkLib pins).
- The counting bounds: correct, tight, hypotheses load-bearing (E.4); same statement before and
  after the probability-API port (E.4).
- Axiom enforcement: lexical and transitive, with a negative control (D.3).
- Clean's vacuity over `K` (C.5), leanISA's replacement (C.7), and its unchanged state at Clean
  `42fe4b26` (C.6).

---

## H. Probes (full sources and outputs)

All seven probes were run by the earlier agent of this task on 2026-09-29 between 17:45 and 17:59, **at the old pins** (leanerVM `b435631`, Lean `v4.33.1`, ArkLib `dca90385`, CompPoly `3468b38c`, Clean `93c9d1ef`, VCVio `f9dc47d9`), from the repository root, with

```sh
flock .claude/reports/blueprint-review/logs/lean.lock lake env lean .claude/reports/blueprint-review/probes/lib-others/<File>.lean
```

(the `real … / exit=` lines at the end of each output are the timing and exit status appended by the runner). None was re-run for this dossier: the checkout now holds the new pins and Lean cannot run until it is rebuilt (brief §8). Files: `probes/lib-others/<File>.lean` and `<File>.out`. Expected errors: `FieldFidelity.lean:103` (`LawfulBEq E`, a deliberate check), `SamplerDiamond.lean:29` (no `SampleableType E` without leanerVM's instance, deliberate), and the three `NumeralHazard` examples marked EXPECTED TO FAIL.

### H.1 `Layer0`: instances found, signatures, axioms, uniformity, the oracle interface (sections E.0-E.3)

```lean
import LeanerVM.Protocol.Field
import LeanerVM.Protocol.ToVCVio.UniformSample
import LeanerVM.Protocol.ToArkLib.Oracles

/-!
Probe `Layer0`: the declarations of the proof system's Layer 0, their axioms, the instances
instance search finds, and the uniformity of the two samplers.
-/

open LeanerVM.Parameters LeanerVM.Protocol CompPoly OracleComp
open scoped NNReal ENNReal

/-! ## 1. Which instances are found -/

#synth SampleableType K
#synth SampleableType E
#synth SampleableType (Vector K 3)
#synth SampleableType (Fin (2 ^ 64))
#synth Fintype K
#synth Fintype E
#synth DecidableEq K
#synth DecidableEq E
#synth OracleInterface (Column 3)
#synth OracleInterface E
#synth OracleInterface (List E)

/-! ## 2. Signatures as elaborated -/

#check @finEquivK
#check @limbsEquiv
#check @instSampleableTypeK
#check @instSampleableTypeE
#check @card_E
#check @evalOracle
#check @evalOracle_answer
#check @probEvent_uniformSample_le_of_card_le
#check @probEvent_uniformSample_le_of_subsingleton
#check @NoOracle
#check @OneOracle
#check @noOracle_eq
#print SampleableType
#print evalOracle
#print instSampleableTypeK
#print instSampleableTypeE

/-! ## 3. Axioms -/

#print axioms finEquivK
#print axioms limbsEquiv
#print axioms instSampleableTypeK
#print axioms instSampleableTypeE
#print axioms card_E
#print axioms evalOracle
#print axioms evalOracle_answer
#print axioms instOracleInterfaceE
#print axioms instOracleInterfaceListE
#print axioms probEvent_uniformSample_le_of_card_le
#print axioms probEvent_uniformSample_le_of_subsingleton
#print axioms noOracle_eq
-- the library facts Layer 0 rests on
#print axioms BF64.card_ext3
#print axioms BF64.card_bf64
#print axioms BF64.basePoly_irreducible
#print axioms BF64.ext3Poly_irreducible
#print axioms BF64.instField
#print axioms SampleableType.ofEquiv
#print axioms probOutput_uniformSample
#print axioms probEvent_uniformSample
#print axioms CMlPolynomialEval.eval_mle_eq_eval
#print axioms CMlPolynomialEval.eval₂_mle_eq_eval₂

/-! ## 4. The two equivalences are bijections, and the samplers are uniform -/

example : Function.Bijective finEquivK := finEquivK.bijective
example : Function.Bijective limbsEquiv := limbsEquiv.bijective

-- every element of `K` is drawn with probability `1 / |K|`
example (x : K) : Pr[= x | $ᵗ K] = (Fintype.card K : ℝ≥0∞)⁻¹ := probOutput_uniformSample K x
-- every element of `E` is drawn with probability `1 / |E|`
example (x : E) : Pr[= x | $ᵗ E] = (Fintype.card E : ℝ≥0∞)⁻¹ := probOutput_uniformSample E x
-- and `|E| = 2^192`
example (x : E) : Pr[= x | $ᵗ E] = ((2 ^ 192 : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [probOutput_uniformSample, card_E]
-- the samplers never fail and reach every element
example : Pr[⊥ | $ᵗ E] = 0 := probFailure_uniformSample E
example : support ($ᵗ E) = Set.univ := support_uniformSample E
-- the sampler of `E` is by definition the image of three independent limbs
example : ($ᵗ E) = limbsEquiv <$> ($ᵗ (Vector K 3)) := rfl
example : ($ᵗ K) = finEquivK <$> ($ᵗ (Fin (2 ^ 64))) := rfl

/-! ## 5. The oracle interface of a column -/

example (n : ℕ) : OracleInterface.Query (Column n) = Vector E n := rfl
example (n : ℕ) (r : Vector E n) : OracleInterface.Response (Message := Column n) r = E := rfl
example (n : ℕ) (q : Column n) (r : Vector E n) :
    OracleInterface.answer q r = CMlPolynomialEval.eval₂Mle q.values (algebraMap K E) r :=
  evalOracle_answer n q r
-- the answer is the dot product of the lifted table with the Lagrange basis at `r`
example (n : ℕ) (q : Column n) (r : Vector E n) :
    OracleInterface.answer q r =
      CMlPolynomialEval.eval (CMlPolynomialEval.map (algebraMap K E) q.values) r := by
  rw [evalOracle_answer, CMlPolynomialEval.eval₂_mle_eq_eval₂]; rfl
-- the scalar interfaces: query `Unit`, the answer is the message
example : OracleInterface.Query E = Unit := rfl
example (x : E) : OracleInterface.answer x () = x := rfl
example : OracleInterface.Query (List E) = Unit := rfl
example (l : List E) : OracleInterface.answer l () = l := rfl
-- `ofK` is `algebraMap K E`
example (a : K) : ofK a = algebraMap K E a := rfl
```

Output (`Layer0.out`):

```text
instSampleableTypeK
instSampleableTypeE
instSampleableTypeVector K 3
instSampleableTypeFinOfNeZeroNat (2 ^ 64)
BF64.instFintype
Extension.Ext.instFintype
instDecidableEqBitVec
fun a b => Extension.Ext.instDecidableEq a b
evalOracle 3
instOracleInterfaceE
instOracleInterfaceListE
finEquivK : Fin (2 ^ 64) ≃ K
limbsEquiv : Vector K 3 ≃ E
instSampleableTypeK : SampleableType K
instSampleableTypeE : SampleableType E
card_E : Fintype.card E = 2 ^ 192
evalOracle : (n : ℕ) → OracleInterface (Column n)
evalOracle_answer : ∀ (n : ℕ) (q : Column n) (r : Vector E n),
  OracleInterface.answer q r = q.values.eval₂Mle (algebraMap K E) r
@probEvent_uniformSample_le_of_card_le : ∀ {α : Type} [inst : SampleableType α] [inst_1 : Fintype α] (p : α → Prop)
  [inst_2 : DecidablePred p] {k : ℕ},
  (Finset.filter p Finset.univ).card ≤ k → probEvent ($ᵗ α) p ≤ ↑(↑k / ↑(Fintype.card α))
@probEvent_uniformSample_le_of_subsingleton : ∀ {α : Type} [inst : SampleableType α] [inst_1 : Fintype α]
  (p : α → Prop), (∀ (a b : α), p a → p b → a = b) → probEvent ($ᵗ α) p ≤ ↑(1 / ↑(Fintype.card α))
NoOracle : Fin 0 → Type
OneOracle : Type → Fin 1 → Type
noOracle_eq : ∀ (o o' : (i : Fin 0) → NoOracle i), o = o'
class SampleableType (β : Type) : Type
number of parameters: 1
fields:
  SampleableType.selectElem : ProbComp β
  SampleableType.mem_support_selectElem : ∀ (x : β), x ∈ support SampleableType.selectElem
  SampleableType.probOutput_selectElem_eq : ∀ (x y : β),
      Pr[= x | SampleableType.selectElem] = Pr[= y | SampleableType.selectElem]
constructor:
  SampleableType.mk {β : Type} (selectElem : ProbComp β) (mem_support_selectElem : ∀ (x : β), x ∈ support selectElem)
    (probOutput_selectElem_eq : ∀ (x y : β), Pr[= x | selectElem] = Pr[= y | selectElem]) : SampleableType β
@[instance_reducible] def LeanerVM.Protocol.evalOracle : (n : ℕ) → OracleInterface (Column n) :=
fun n =>
  { Query := Vector E n,
    toOC :=
      { spec := OracleSpec.ofFn fun x => E,
        impl := fun r => do
          let __do_lift ← read
          pure (__do_lift.values.eval₂Mle (algebraMap K E) r) } }
@[instance_reducible] def LeanerVM.Protocol.instSampleableTypeK : SampleableType K :=
SampleableType.ofEquiv finEquivK
@[instance_reducible] def LeanerVM.Protocol.instSampleableTypeE : SampleableType E :=
SampleableType.ofEquiv limbsEquiv
'LeanerVM.Protocol.finEquivK' depends on axioms: [propext]
'LeanerVM.Protocol.limbsEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.instSampleableTypeK' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.instSampleableTypeE' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.card_E' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.evalOracle' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.evalOracle_answer' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.instOracleInterfaceE' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.instOracleInterfaceListE' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.probEvent_uniformSample_le_of_card_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanerVM.Protocol.probEvent_uniformSample_le_of_subsingleton' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'LeanerVM.Protocol.noOracle_eq' depends on axioms: [Quot.sound]
'BF64.card_ext3' depends on axioms: [propext, Classical.choice, Quot.sound]
'BF64.card_bf64' depends on axioms: [propext, Classical.choice, Quot.sound]
'BF64.basePoly_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound]
'BF64.ext3Poly_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound]
'BF64.instField' depends on axioms: [propext, Classical.choice, Quot.sound]
'SampleableType.ofEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'probOutput_uniformSample' depends on axioms: [propext, Classical.choice, Quot.sound]
'probEvent_uniformSample' depends on axioms: [propext, Classical.choice, Quot.sound]
'CompPoly.CMlPolynomialEval.eval_mle_eq_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'CompPoly.CMlPolynomialEval.eval₂_mle_eq_eval₂' depends on axioms: [propext, Classical.choice, Quot.sound]

real	1m43.166s
user	0m3.411s
sys	0m1.938s
exit=0
```

### H.2 `FieldFidelity`: leanerVM `K`, `E` against the Rust reference vectors; numerals; instance leakage onto `BitVec 64` (B.3, B.4)

```lean
import LeanerVM.Parameters.Field
import LeanerVM.Parameters.Generator

/-!
Probe `FieldFidelity`: leanerVM's `K` and `E` compute the same products as the pinned Rust on
the Rust's own reference vectors (`crates/primitives/src/field/gf2_64.rs:271-275`,
`gf2_64x3.rs:991-1016`), and the numerals of `K` are bit patterns.
-/

open LeanerVM.Parameters

/-! ## Base field: the three `(a, b, a·b)` vectors of `gf2_64.rs:271-275` -/

#guard (0x01090913877ed8ed : K) * 0x66ab35ac2768468f = 0x50c4519dc383744a
#guard (0xa7715ae18f12a3b5 : K) * 0x05743059f43fa4f5 = 0xeb64cd9cd9cda6df
#guard (0xbd3efb4705e79ddd : K) * 0x3aff618604de4ae0 = 0xc3d7a95fa9cb59bb
-- a mutated product is rejected
#guard (0x01090913877ed8ed : K) * 0x66ab35ac2768468f ≠ 0x50c4519dc383744b
-- the reduction constant: x^63 · x = x^64 = x^4 + x^3 + x + 1 = 0x1B
#guard (0x8000000000000000 : K) * 0x2 = 0x1B
-- addition is XOR
#guard (0x01090913877ed8ed : K) + 0x66ab35ac2768468f = 0x01090913877ed8ed ^^^ 0x66ab35ac2768468f
-- inversion, and `0⁻¹ = 0` as in the Rust (`gf2_64.rs:42`, `:318`)
#guard (0x01090913877ed8ed : K) * (0x01090913877ed8ed : K)⁻¹ = 1
#guard (0 : K)⁻¹ = 0

/-! ## Extension: the four `(a, b, a·b, a·a)` vectors of `gf2_64x3.rs:991-1016` -/

def a1 : E := E.ofLimbs 0x950e87d7f5606615 0x2c61275c9e6b6cf8 0x1f00bca0042db923
def b1 : E := E.ofLimbs 0x6dbca290a9eab706 0x4c10a4fe30cffdda 0xf26fff4cc4fd394d
def c1 : E := E.ofLimbs 0x888a0fc35abaf5f6 0x68a84cbc132b0649 0x9fdeaf613003cabe
def s1 : E := E.ofLimbs 0x8fba131ad5d46b8c 0x1c170457f537a805 0x3632cc098ca15135
def a2 : E := E.ofLimbs 0x6814a2bc786a6d2d 0xa26b351e6c8042c5 0x54760e7fbc051c6c
def b2 : E := E.ofLimbs 0xd4c08880a5a4666d 0x29610ae0eed8f1e7 0xc34bd8e2fe5213e5
def c2 : E := E.ofLimbs 0x2ad322ebf2f9043b 0x8ac800aa67154c80 0x6d0f76651d3c4d0c
def s2 : E := E.ofLimbs 0xcf800ef2b83bb43a 0xefe1c6cd064dd44c 0x57dc5c7a60e2981b
def a3 : E := E.ofLimbs 0x6c50afb6e9fb123d 0x6f28d015a2aa0b9d 0x4e385994ebac94af
def b3 : E := E.ofLimbs 0x194f9545adba52ce 0xc675ce05588f882f 0x57de8c051d4b7ef2
def c3 : E := E.ofLimbs 0xea6b9f9d23d4a1ff 0xd82aa6058c431457 0x5fd4d8fda2f1e74a
def s3 : E := E.ofLimbs 0x8f30fe43aa05b396 0xe3593591eccd9efe 0x7c5a1b128788c51f
def a4 : E := E.ofLimbs 0xd998efd82733e933 0x6df216c33f8f3201 0x11dc6f3fcb57d5d8
def b4 : E := E.ofLimbs 0x8860a84722025e05 0x33176469aa6ef630 0x607507ebc5b864d7
def c4 : E := E.ofLimbs 0xfa3a0d66cdfbc1b3 0xbd47bd3343aad307 0xdaf50186477f6a77
def s4 : E := E.ofLimbs 0x69c8d8c24f416884 0x4b597d648a162147 0x95603a5d95c9512a

#guard a1 * b1 = c1
#guard a1 * a1 = s1
#guard a2 * b2 = c2
#guard a2 * a2 = s2
#guard a3 * b3 = c3
#guard a3 * a3 = s3
#guard a4 * b4 = c4
#guard a4 * a4 = s4
-- a mutated limb is rejected
def c1' : E := E.ofLimbs 0x888a0fc35abaf5f6 0x68a84cbc132b0649 0x9fdeaf613003cabf
#guard a1 * b1 ≠ c1'
-- the defining relation, as the Rust checks it (`gf2_64x3.rs:1026`)
#guard y * y * y = y + 1
-- `y` is the limb vector `(0, 1, 0)` (`F192::Y`, `gf2_64x3.rs:45`)
def yLimbs : E := E.ofLimbs 0 1 0
#guard y = yLimbs
-- the inverse in `E`
#guard a1 * a1⁻¹ = 1

/-! ## The generator -/

#guard g = (2 : K)
#guard g * g = (4 : K)

/-! ## Numerals of `K` are bit patterns, not casts of natural numbers -/

-- the numeral `2 : K` is the element `x`, and is not zero
#guard (2 : K) ≠ 0
-- whereas the cast of the natural number two is zero (characteristic two)
#guard ((2 : ℕ) : K) = 0
#guard (1 : K) + 1 = 0
#guard (2 : K) ≠ ((2 : ℕ) : K)
#guard (3 : K) = (2 : K) + 1
-- the numeral elaborates through `BitVec`'s instance
set_option pp.explicit true in
#check (2 : K)

/-! ## `K` is `BitVec 64` to instance search: which `+` does a `BitVec 64` get? -/

def u : BitVec 64 := 3
def v : BitVec 64 := 5
-- with CompPoly's field in scope, `+` on `BitVec 64` is XOR (3 + 5 = 6), not addition mod 2^64 (8)
#eval u + v
#eval (u + v == 8, u + v == 6)
#eval u * v
set_option pp.explicit true in
#check u + v
-- at another width the core instance is found
def u32 : BitVec 32 := 3
def v32 : BitVec 32 := 5
#eval u32 + v32

#synth Add (BitVec 64)
#synth Mul (BitVec 64)
#synth Add (BitVec 32)
#synth Fintype (BitVec 64)
#synth LawfulBEq K
#synth LawfulBEq E
```

Output (`FieldFidelity.out`):

```text
@OfNat.ofNat K (nat_lit 2)
  (@BitVec.instOfNat (@OfNat.ofNat Nat (nat_lit 64) (instOfNatNat (nat_lit 64))) (nat_lit 2)) : K
6#64
(false, true)
15#64
@HAdd.hAdd (BitVec (@OfNat.ofNat Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))
  (BitVec (@OfNat.ofNat Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))
  (BitVec (@OfNat.ofNat Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))
  (@instHAdd (BitVec (@OfNat.ofNat Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))) BF64.instAdd) u
  v : BitVec (@OfNat.ofNat Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))
8#32
BF64.instAdd
BF64.instMul
BitVec.instAdd
BF64.instFintype
instLawfulBEq
.claude/reports/blueprint-review/probes/lib-others/FieldFidelity.lean:103:0: error: failed to synthesize
  LawfulBEq E

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.

real	0m31.389s
user	0m5.433s
sys	0m1.650s
exit=1
```

### H.3 `CountingBounds`: the two counting bounds are correct, tight and non-vacuous (E.4)

```lean
import LeanerVM.Protocol.Field
import LeanerVM.Protocol.ToVCVio.UniformSample

/-!
Probe `CountingBounds`: the two counting bounds of `ToVCVio/UniformSample.lean` are correct
and not vacuous. On `Fin 4`, an event with exactly one witness has probability exactly `1/4`
(so the bound `1/|α|` is attained), and an event with two witnesses has probability `1/2`,
which exceeds `1/4` (so the hypothesis of the second bound is load-bearing).
-/

open LeanerVM.Protocol OracleComp
open scoped NNReal ENNReal

-- one witness: probability exactly 1/4
theorem one_witness : Pr[fun x : Fin 4 ↦ x = 2 | $ᵗ (Fin 4)] = 1 / 4 := by
  rw [probEvent_uniformSample]
  have h : (Finset.univ.filter fun x : Fin 4 ↦ x = 2).card = 1 := by decide
  rw [h]
  simp

-- the second bound, instantiated, gives `≤ 1/4`: it is attained
theorem one_witness_bound :
    Pr[fun x : Fin 4 ↦ x = 2 | $ᵗ (Fin 4)] ≤ ((1 / Fintype.card (Fin 4) : ℝ≥0) : ℝ≥0∞) :=
  probEvent_uniformSample_le_of_subsingleton (fun x : Fin 4 ↦ x = 2)
    (fun a b ha hb ↦ ha.trans hb.symm)

-- the right-hand side of the bound is the number 1/4
theorem rhs_eq : ((1 / Fintype.card (Fin 4) : ℝ≥0) : ℝ≥0∞) = 1 / 4 := by
  rw [Fintype.card_fin]
  rw [ENNReal.coe_div (by norm_num)]
  simp

-- two witnesses: probability exactly 1/2, which is not `≤ 1/4`
theorem two_witnesses : Pr[fun x : Fin 4 ↦ x = 1 ∨ x = 2 | $ᵗ (Fin 4)] = 1 / 2 := by
  rw [probEvent_uniformSample]
  have h : (Finset.univ.filter fun x : Fin 4 ↦ x = 1 ∨ x = 2).card = 2 := by decide
  rw [h]
  simp only [Fintype.card_fin, Nat.cast_ofNat]
  rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num]
  rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv (by simp) (by simp), mul_assoc,
    ENNReal.inv_mul_cancel (by simp) (by simp), mul_one, one_div]

theorem two_witnesses_exceed :
    ¬ Pr[fun x : Fin 4 ↦ x = 1 ∨ x = 2 | $ᵗ (Fin 4)] ≤ 1 / 4 := by
  rw [two_witnesses, not_le]
  rw [one_div, one_div]
  exact ENNReal.inv_lt_inv.mpr (by norm_num)

-- the first bound with `k = 2` on the same event
theorem two_witnesses_bound :
    Pr[fun x : Fin 4 ↦ x = 1 ∨ x = 2 | $ᵗ (Fin 4)]
      ≤ (((2 : ℕ) / Fintype.card (Fin 4) : ℝ≥0) : ℝ≥0∞) :=
  probEvent_uniformSample_le_of_card_le (fun x : Fin 4 ↦ x = 1 ∨ x = 2) (k := 2) (by decide)

-- over the challenge field: a single bad challenge has probability exactly `1 / 2^192`
open LeanerVM.Parameters in
theorem one_bad_challenge (c : E) :
    Pr[fun x : E ↦ x = c | $ᵗ E] = ((2 ^ 192 : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [probEvent_eq_eq_probOutput, probOutput_uniformSample, card_E]

open LeanerVM.Parameters in
theorem one_bad_challenge_bound (c : E) :
    Pr[fun x : E ↦ x = c | $ᵗ E] ≤ ((1 / Fintype.card E : ℝ≥0) : ℝ≥0∞) :=
  probEvent_uniformSample_le_of_subsingleton (fun x : E ↦ x = c)
    (fun a b ha hb ↦ ha.trans hb.symm)

#print axioms one_witness
#print axioms one_witness_bound
#print axioms rhs_eq
#print axioms two_witnesses
#print axioms two_witnesses_exceed
#print axioms two_witnesses_bound
#print axioms one_bad_challenge
#print axioms one_bad_challenge_bound
```

Output (`CountingBounds.out`):

```text
.claude/reports/blueprint-review/probes/lib-others/CountingBounds.lean:25:9: warning: Variable name `a` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _a

Note: This linter can be disabled with `set_option linter.unusedVariables false`
.claude/reports/blueprint-review/probes/lib-others/CountingBounds.lean:25:11: warning: Variable name `b` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _b

Note: This linter can be disabled with `set_option linter.unusedVariables false`
.claude/reports/blueprint-review/probes/lib-others/CountingBounds.lean:65:9: warning: Variable name `a` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _a

Note: This linter can be disabled with `set_option linter.unusedVariables false`
.claude/reports/blueprint-review/probes/lib-others/CountingBounds.lean:65:11: warning: Variable name `b` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _b

Note: This linter can be disabled with `set_option linter.unusedVariables false`
'one_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'one_witness_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'rhs_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'two_witnesses' depends on axioms: [propext, Classical.choice, Quot.sound]
'two_witnesses_exceed' depends on axioms: [propext, Classical.choice, Quot.sound]
'two_witnesses_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'one_bad_challenge' depends on axioms: [propext, Classical.choice, Quot.sound]
'one_bad_challenge_bound' depends on axioms: [propext, Classical.choice, Quot.sound]

real	5m18.923s
user	0m2.869s
sys	0m1.905s
exit=0
```

### H.4 `CleanBalance`: Clean balance over `K`: universes, countermodel, side condition (C.2, C.5)

```lean
import LeanerVM.Parameters.CleanField
import Clean.Air.FlatEnsemble

/-!
Probe `CleanBalance`: Clean's bus balance over `K = GF(2^64)`.

1. The universe of `EnsembleWitness`.
2. The countermodel: a tuple pushed twice and never pulled has field-sum balance zero at every
   message.
3. The side condition `interactions.length < ringChar F` rejects that list, and rejects every
   list of two or more interactions; a balanced singleton has multiplicity zero. So over `K`
   the relation `BalancedInteractions` holds of no bus with two interactions.
4. Hence `Ensemble.Statement` forces every channel of every ensemble over `K` to carry at most
   one interaction.
-/

open LeanerVM.Parameters

/-! ## 1. Universes -/

#check @Air.Flat.Component
#check @Air.Flat.Table
#check @Air.Flat.Ensemble
#check @Air.Flat.EnsembleWitness
#check @RawChannel
#check @Interaction
#check @ProverData
#check @TypeMap
#check @Air.Flat.Ensemble.Statement
#check @Air.Flat.Ensemble.Soundness
#check @BalancedInteractions
#check @balanceOf
#print axioms Air.Flat.Ensemble.soundness_of_tableSoundness_and_specConsistency
#print axioms exists_push_of_pull

/-! ## 2. The countermodel -/

theorem ringChar_K : ringChar K = 2 := ringChar.eq K 2

example : (-1 : K) = 1 := by decide
example : (1 : K) + 1 = 0 := by decide

/-- A channel with one coordinate and no guarantee. -/
def ch : RawChannel K where
  name := "bus"
  arity := 1
  Guarantees _ _ _ := True
  Requirements _ _ _ := True

/-- The tuple `(m)` pushed once: multiplicity `1`. -/
def push (m : K) : Interaction K where
  channel := ch
  mult := 1
  msg := #[m]
  same_size := rfl
  assumeGuarantees := false

/-- The tuple `(7)` pushed twice and never pulled. -/
def pushedTwice : List (Interaction K) := [push 7, push 7]

/-- Its field-sum balance is zero at every message: `1 + 1 = 0` in characteristic two. -/
theorem pushedTwice_balance (msg : Array K) : balanceOf pushedTwice msg = 0 := by
  -- no default `simp` here: core's `BitVec` simprocs would read `1 + 1` in `K` as `2#64`
  have h11 : (1 : K) + ((1 : K) + 0) = 0 := by decide
  by_cases h : (push 7).msg = msg
  · simp only [balanceOf, pushedTwice, List.filter_cons, List.filter_nil, decide_eq_true h,
      ↓reduceIte, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    exact h11
  · simp only [balanceOf, pushedTwice, List.filter_cons, List.filter_nil, decide_eq_false h,
      Bool.false_eq_true, ↓reduceIte, List.map_nil, List.sum_nil]

/-- As a multiset the same bus is not balanced: two pushes, no pull. -/
theorem pushedTwice_not_perm :
    ¬ (pushedTwice.map (·.msg)).Perm ([] : List (Array K)) := by
  intro h
  have := h.length_eq
  simp [pushedTwice] at this

/-! ## 3. The side condition -/

/-- Clean's relation rejects the countermodel, but only through the side condition. -/
theorem pushedTwice_not_balanced : ¬ BalancedInteractions pushedTwice := by
  rintro ⟨h, -⟩
  rw [ringChar_K] at h
  simp [pushedTwice] at h

/-- Over `K`, a balanced list has at most one interaction. -/
theorem length_le_one_of_balanced {l : List (Interaction K)} (h : BalancedInteractions l) :
    l.length ≤ 1 := by
  obtain ⟨h, -⟩ := h
  rw [ringChar_K] at h
  omega

/-- And that interaction has multiplicity zero. -/
theorem mult_eq_zero_of_balanced_singleton {i : Interaction K}
    (h : BalancedInteractions [i]) : i.mult = 0 := by
  have := h.2 i.msg
  simpa [balanceOf] using this

/-- A push and its matching pull, the smallest honest bus, are rejected. -/
def pull (m : K) : Interaction K where
  channel := ch
  mult := -1
  msg := #[m]
  same_size := rfl
  assumeGuarantees := true

theorem honest_pair_not_balanced : ¬ BalancedInteractions [push 7, pull 7] := fun h ↦ by
  have := length_le_one_of_balanced h
  simp at this

/-! ## 4. The ensemble statement -/

open Air.Flat in
/-- Whatever the ensemble over `K`, a witness of Clean's `Statement` has at most one
interaction on each of the ensemble's channels. -/
theorem statement_forces_at_most_one_interaction {PublicIO : TypeMap} [ProvableType PublicIO]
    (ens : Ensemble K PublicIO) (w : EnsembleWitness ens) (h : w.BalancedChannels)
    (c : RawChannel K) (hc : c ∈ ens.channels) :
    (w.allTablesWitness.interactionsWith c).length ≤ 1 :=
  length_le_one_of_balanced (h c hc)

#print axioms pushedTwice_balance
#print axioms pushedTwice_not_perm
#print axioms pushedTwice_not_balanced
#print axioms length_le_one_of_balanced
#print axioms mult_eq_zero_of_balanced_singleton
#print axioms honest_pair_not_balanced
#print axioms statement_forces_at_most_one_interaction
```

Output (`CleanBalance.out`):

```text
Air.Flat.Component : (F : Type) → [FiniteField F] → Type 1
Air.Flat.Table : (F : Type) → [FiniteField F] → Type 1
Air.Flat.Ensemble : (F : Type) → [FiniteField F] → (PublicIO : TypeMap) → [ProvableType PublicIO] → Type 1
@Air.Flat.EnsembleWitness : {F : Type} →
  [inst : FiniteField F] →
    {PublicIO : TypeMap} → [inst_1 : ProvableType PublicIO] → Air.Flat.Ensemble F PublicIO → Type 1
RawChannel : Type → Type
Interaction : Type → Type
ProverData : Type → Type
TypeMap : Type 1
@Air.Flat.Ensemble.Statement : {F : Type} →
  [inst : FiniteField F] →
    {PublicIO : TypeMap} →
      [inst_1 : ProvableType PublicIO] → [DecidableEq F] → Air.Flat.Ensemble F PublicIO → PublicIO F → Prop
@Air.Flat.Ensemble.Soundness : {F : Type} →
  [inst : FiniteField F] →
    {PublicIO : TypeMap} →
      [inst_1 : ProvableType PublicIO] →
        [DecidableEq F] → Air.Flat.Ensemble F PublicIO → (PublicIO F → Prop) → (PublicIO F → Prop) → Prop
@BalancedInteractions : {F : Type} → [FiniteField F] → [DecidableEq F] → List (Interaction F) → Prop
@balanceOf : {F : Type} → [FiniteField F] → [DecidableEq F] → List (Interaction F) → Array F → F
'Air.Flat.Ensemble.soundness_of_tableSoundness_and_specConsistency' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'exists_push_of_pull' depends on axioms: [propext, Classical.choice, Quot.sound]
'pushedTwice_balance' depends on axioms: [propext, Classical.choice, Quot.sound]
'pushedTwice_not_perm' depends on axioms: [propext]
'pushedTwice_not_balanced' depends on axioms: [propext, Classical.choice, Quot.sound]
'length_le_one_of_balanced' depends on axioms: [propext, Classical.choice, Quot.sound]
'mult_eq_zero_of_balanced_singleton' depends on axioms: [propext, Classical.choice, Quot.sound]
'honest_pair_not_balanced' depends on axioms: [propext, Classical.choice, Quot.sound]
'statement_forces_at_most_one_interaction' depends on axioms: [propext, Classical.choice, Quot.sound]

real	0m33.498s
user	0m3.000s
sys	0m1.989s
exit=0
```

### H.5 `SamplerDiamond`: the library sampler on `K` without leanerVM, and sampler uniqueness (E.1)

```lean
import LeanerVM.Parameters.Field
import VCVio.OracleComp.Constructions.SampleableType

/-!
Probe `SamplerDiamond`: without `LeanerVM.Protocol.Field`, instance search already finds a
sampler on `K`, because `K` unfolds to `BitVec 64` and Mathlib enumerates `BitVec n` as a
`FinEnum`. It is a different term from leanerVM's `instSampleableTypeK`. Both are lawful, so
they have the same distribution.
-/

open LeanerVM.Parameters OracleComp
open scoped ENNReal

#synth SampleableType K
#synth SampleableType (BitVec 64)
#synth FinEnum K

-- the library's sampler on `K` is uniform too (uniformity is a law of the class)
example (x : K) : Pr[= x | $ᵗ K] = (Fintype.card K : ℝ≥0∞)⁻¹ := probOutput_uniformSample K x

-- any two samplers on the same finite type give every element the same probability
theorem sampler_unique {α : Type} [Fintype α] (s t : SampleableType α) (x : α) :
    Pr[= x | @uniformSample α s] = Pr[= x | @uniformSample α t] := by
  rw [@probOutput_uniformSample α s, @probOutput_uniformSample α t]

#print axioms sampler_unique

-- no sampler is found on `E` without leanerVM's instance: `Ext` is not reducible
#synth SampleableType E
```

Output (`SamplerDiamond.out`):

```text
FinEnum.SampleableType K
FinEnum.SampleableType (BitVec 64)
FinEnum.instBitVec 64
'sampler_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
.claude/reports/blueprint-review/probes/lib-others/SamplerDiamond.lean:29:0: error: failed to synthesize
  SampleableType E

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.

real	0m22.446s
user	0m2.534s
sys	0m1.584s
exit=1
```

### H.6 `SamplerDiamond2`: leanerVM and library samplers on `K` are the same term (E.1)

```lean
import LeanerVM.Protocol.Field

/-!
Probe `SamplerDiamond2`: with `LeanerVM.Protocol.Field` imported, two samplers on `K` are in
scope, leanerVM's and the one instance search derives from Mathlib's `FinEnum (BitVec n)`.
Are they the same term up to definitional unfolding?
-/

open LeanerVM.Parameters LeanerVM.Protocol OracleComp

#synth SampleableType K

-- the computations are definitionally equal
example :
    (instSampleableTypeK).selectElem = (FinEnum.SampleableType K).selectElem := rfl

-- hence so are the instances (the law fields are proofs)
example : (instSampleableTypeK : SampleableType K) = FinEnum.SampleableType K := rfl
```

Output (`SamplerDiamond2.out`):

```text
instSampleableTypeK

real	0m3.660s
user	0m2.315s
sys	0m1.368s
exit=0
```

### H.7 `NumeralHazard`: `simp` misreads `K` arithmetic; the kernel rejects the result (G.7)

```lean
import LeanerVM.Parameters.Field

/-!
Probe `NumeralHazard`: `K` is an abbreviation of `BitVec 64`, so core's `BitVec` simprocs
fire on terms of `K`, reading the field's `+` (XOR) as addition modulo `2^64`. Does that let
`simp` prove a false statement about `K`? Each `example` below is run separately; the ones
marked EXPECTED TO FAIL must be rejected.
-/

open LeanerVM.Parameters

-- true in `K`: characteristic two
example : (1 : K) + 1 = 0 := by decide

-- EXPECTED TO FAIL: `simp` cannot prove the true statement (it rewrites `1 + 1` to `2#64`)
example : (1 : K) + 1 = 0 := by simp

-- EXPECTED TO FAIL (the soundness probe): the negation is false in `K`; if `simp` closes the
-- goal, the kernel must reject the proof term
theorem bad : ¬ ((1 : K) + 1 = 0) := by simp

-- EXPECTED TO FAIL: the same through a product, `x · x^63 = 0x1B` in `K`, not `0` (the low
-- 64 bits of `2^64`)
theorem bad_mul : (2 : K) * 0x8000000000000000 = 0 := by simp

#print axioms bad
#print axioms bad_mul
```

Output (`NumeralHazard.out`):

```text
.claude/reports/blueprint-review/probes/lib-others/NumeralHazard.lean:16:29: error: unsolved goals
⊢ False
.claude/reports/blueprint-review/probes/lib-others/NumeralHazard.lean:16:0: error: (kernel) application type mismatch
  id (eq_false_of_decide (Eq.refl false))
argument has type
  (2#64 = 0#64) = False
but function has type
  (1 + 1 = 0) = False → (1 + 1 = 0) = False
.claude/reports/blueprint-review/probes/lib-others/NumeralHazard.lean:20:8: error: (kernel) application type mismatch
  congrArg Not (eq_false_of_decide (Eq.refl false))
argument has type
  (2#64 = 0#64) = False
but function has type
  (1 + 1 = 0) = False → (¬1 + 1 = 0) = ¬False
.claude/reports/blueprint-review/probes/lib-others/NumeralHazard.lean:24:8: error: (kernel) declaration type mismatch, 'bad_mul' has type
  0#64 = 0#64
but it is expected to have type
  2 * 9223372036854775808 = 0
'bad' depends on axioms: [bad, propext, Quot.sound]
'bad_mul' depends on axioms: [bad_mul, propext, Quot.sound]

real	0m3.786s
user	0m2.526s
sys	0m1.322s
exit=1
```
