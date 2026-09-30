
## E. Are the adaptor's statements well formed and provable as sketched?

The Layer 3 sketch (`protocol-blueprint.md:794-820`), read as Lean to be written.

### E.1 `witnessOf` and `satisfiedBy_witnessOf`

`def witnessOf (prog) (s) (q : Column (leanIsaInstance prog s).μ) : EnsembleWitness
(leanIsaEnsemble prog)`, "total and computable". `EnsembleWitness` is in `Type 1` (probe
`Shapes`, output line 1-2); a computable definition may inhabit a type in `Type 1` (the
ensemble itself is a `def` that compiles), and the fields are constructible: eight `Table`s
with `component := (leanIsaEnsemble prog).tables[j]`, rows built by one pass over the columns
read through the layout, `data := fun name n ↦ if name = "mem" ∧ n = 3 then … else #[]`, the
public input off cells 0 and 1, and the three proof fields by `rfl`/`simp`. Total in `s`: for
an inadmissible `s` the tables are simply of the announced heights. Two things the sketch
omits: `witnessOf` has no `input` argument (B.1 (iii)), which is fine only if the lanes are
read off `q` (then `public_input_eq` needs the first two lines and `0 < logMem`); and the
instance must exist first (E.4, E.5, finding 7).

`theorem satisfiedBy_witnessOf (hs : s.Admissible prog) (h : M3Holds (leanIsaInstance prog s)
input q) : SatisfiedBy prog input (witnessOf prog s q)` typechecks as a statement provided
`(leanIsaInstance prog s).Stmt` reduces to `PublicInput`; with a `def` instance the elaborator
unfolds it (probe `DefInstance`, the `example` at line 34 elaborates), but instance search
does not, so `Decidable (M3Holds (leanIsaInstance prog s) input q)`, which every `#guard` of
the Layer 3 tests needs, is found only for an `abbrev` instance (probe `DefInstance`: the two
guards on `instA` pass, the two on `inst` fail with "Type mismatch … expected to have type
Bool"; the spine's toy is an `abbrev` for the same reason, `Spine/Toy.lean:94-95`). Provable
as sketched: yes, with the additions of A.4 (the boundary lemma, the count derivation, the
Flock consequence lemma).

### E.2 `stackOf`, `m3Holds_stackOf`, `witnessOf_stackOf`

`def stackOf (gen : FlockWitnessGen) (w) (hs : Sizes.ofWitness w = some s) : Column
(leanIsaInstance prog s).μ`: well formed (a `def` taking a proof to fix the index of its
result is ordinary Lean). `m3Holds_stackOf`: provable with the additions of A.6.

`theorem witnessOf_stackOf (hs) : witnessOf prog s (stackOf gen w hs) = w -- on the committed
fields` is not a Lean statement. As an equality of `EnsembleWitness`es it is false for
almost every `w`: `w.data : String → (n : ℕ) → Array (Vector K n)` is a function and
`witnessOf` rebuilds it with the `"mem"` table only; `Table.width` is a free field
(`FlatComponent.lean:151-156`) and `witnessOf` rebuilds rows of exactly the component's
width; the memory block's `idx` cells and the bytecode block's entry cells are rebuilt from
`gpow` and `prog`, so equality needs `index_columns` and `bytecode_rows` of `w`; and the
public input is rebuilt from cells 0 and 1, so it needs `public_input_eq` and the word
conjuncts. "On the committed fields" has to be spelled out; a statement that says what the
sketch means and is decidable on a small witness:

```lean
/-- The cells a component reads: the first `width` cells of a raw row, a missing cell `0`. -/
def rowCells (c : Component K) (row : Array K) : List K :=
  (List.range c.width).map fun j ↦ row[j]?.getD 0
theorem witnessOf_stackOf (h : SatisfiedBy prog input w) (hs : Sizes.ofWitness w = some s) :
    let w' := witnessOf prog s (stackOf gen w hs)
    (∀ j : Fin 8, (tableAt w' j).table.map (rowCells (tableAt w j).component) =
        (tableAt w j).table.map (rowCells (tableAt w j).component)) ∧
      memRows w'.data = memRows w.data ∧ w'.publicInput = w.publicInput
```

Neither T4 composition uses `witnessOf_stackOf` (soundness uses `satisfiedBy_witnessOf`,
completeness `m3Holds_stackOf`); its role is acceptance tests 19 and 24 (`:1320-1322,
1333-1340`), non-vacuity of `witnessOf`. `#guard witnessOf (stackOf w) = w` (`:1339`) cannot be
written, `EnsembleWitness` having no `DecidableEq`; the statement above can (finding 10).

### E.3 `Sizes.logInvRate`

The Rust announces `log_mem`, six `τ_j` and `log_inv_rate` (`announce_public`, `cpu/mod.rs
:118-124`; `read_public` `:144-149`); the Python reads the same `2 + 6` scalars
(`verifier.py:1372-1376`); the specification's Setup names `κ_mem` and the six `τ_j` only
(`08-end-to-end-protocol.tex:55`), a disagreement between the specification and both
implementations that the blueprint resolves the Rust's way (Category B, `:199`). So the rate
*is* announced with the sizes. It does not belong in the instance of the oracle protocol:
`leanIsaInstance prog s` reads `s.logMem` and `s.τ` (heights, `μ`, layout, lines) and nothing
of the rate, which parameterizes WHIR alone (Layer 11); `Sizes.ofWitness (w) : Option Sizes`
(`:799`) cannot produce a rate from a witness; and `Sizes.Admissible` would mix a check of
the oracle protocol's family index with a check of the commitment. `gt-bus.md` G4 reaches the
same point from the caps. Proposed: `Sizes` holds `logMem` and `τ`; the announcement of Layer
12 is `Sizes × logInvRate`; `Admissible prog s` (heights, `3 ≤ τ 5`, `μ_stack prog s ∈
[15, 28]`) and `validRate ρ` (`ρ ∈ [1, 4]`, `whir_config.rs:48-55`) are two predicates
(finding 5).

### E.4 The instance's tables, columns and blocks against `M3Instance` as built

Expressible, with one consequence:

- the six shared columns as tables of the instance: yes, as at least three tables (A.3), each
  with `constraints := []`, `flushes := []`, `counts := []`; `Shape.τ` is per table, so the
  memory columns' height `2^logMem` sits beside the six tables' heights;
- the finalize counts outside the count tree: `counts jMem = []`, `counts jBc = []`, as
  `layout.rs:412-414` (the count blocks are the tables' `count_columns()` only);
- the boundary blocks: `Coord.committed ⟨jMem, i⟩ rfl` at `κ = logMem`, `Coord.committed
  ⟨jBc, 0⟩ rfl` at `κ = prog.logSize`, the `known` and `const` coordinates of A.3; the
  `h : S.τ c.1 = κ` obligation is met by construction;
- the eighteen limb columns as strided slots of `q_flock`: the `Layout` law admits it
  (`Spine/Instance.lean:73-81`, a reading law), but no reader exists (`code-layer1.md` G.1)
  and the slot map is placed inside `FlockInterface (I)` (`gt-flock-ring.md` 8.2): finding 7;
- the three lines need `PublicLine.pos : 0 < τ`, i.e. `0 < s.logMem`; for a total
  `leanIsaInstance` the lines must be empty (or the instance junk) when `logMem = 0`, which is
  harmless because `verify` rejects such `s`, but must be written;
- **the consequence**: the generic table sumcheck (Layer 7) takes its rounds from
  `τ_max = max_j τ_j` over the instance's tables and sends "one value per column of every
  table" (`:987-989`, `08-end-to-end-protocol.tex:76-77`); with the shared columns as
  tables, a phase over the abstract `I` would run `max(τ_j, logMem, prog.logSize, τ_5 + 8)`
  rounds and send scalars for `mem_0, …, q_flock`, a transcript leanVM does not have
  (`constraints.rs:250`, the six tables; `gt-bus.md` G16). The instance needs a criterion the
  phase can read ("a table with a constraint, a flush or a count column takes part"), stated
  in the spine's conventions and used by Layer 7 (finding 9).

### E.5 Mathlib polynomials in Layer 2, CompPoly polynomials in the instance

Layer 2 produces `Expression.toMvPolynomial : Expression F → MvPolynomial ℕ F` and an
`M3Table F` whose constraints are `MvPolynomial (Fin width) F` (`:762-771`); `M3Instance`
holds `CMvPolynomial (width j) K` (`Spine/Instance.lean:123-125`). No conversion is named.
CompPoly's `toCMvPolynomial : MvPolynomial (Fin n) R → CMvPolynomial n R` is
`noncomputable def` at the pin `3468b38c` (`Multivariate/MvPolyEquiv/Core.lean:41`), so an
instance built through it is noncomputable: `M3Holds (leanIsaInstance prog s)` could not be
decided by evaluation (the Layer 3 tests, `:866-867`), the phases' verifiers, which evaluate
`I.constraints` at the claimed column values, would not compile, and `verify` (`:1230-1231`,
"total and computable") could not be defined from them. The degree bound travels the other
way without trouble: `totalDegree_equiv : p.totalDegree = (fromCMvPolynomial p).totalDegree`
(`MvPolyEquiv/Eval.lean:60-61`, `rfl`) and `eval_equiv` (`:53-57`) let Mathlib prove the
bound of a computable polynomial, as the toy does (`Spine/Toy.lean:68-74`). What Layer 2 must
produce is a *direct* computable translation `Expression K → CMvPolynomial n K` (structural
recursion on `var`, `const`, `add`, `mul`, `Expression.lean:12-16`, with `CMvPolynomial.X`,
`C`, `+`, `*`), and its bridge to Mathlib for the degree lemma. Probe `PolyBridge` (old pins,
exit 0) writes it in twelve lines, evaluates the `JUMP` residual `b + v_cond · w` on a row
and checks it against Clean's `Expression.eval` (`#guard polyValue = cleanValue`), checks
`totalDegree = 2`, and checks that a variable past the width reads `0` on both sides as
`Environment.fromArray` reads a missing cell (`Expression.lean:71-73`). At the new CompPoly
pin the probe's row numerals `3, 5, 7` read as `1, 1, 1`; the guards still hold but a re-run
should use `K.ofBits`. Finding 8. (The `Direction` of leanISA's `channelDir`,
`Channels.lean:262-272`, and the spine's `Side`, `Spine/Instance.lean:51-54`, are two
enumerations of the same two values; the translation is one match.)

### E.6 The T4 composition, arrow by arrow

"`T4 = verify_knowledgeSound ∘ Refinement.map_option_valid satisfiedBy_witnessOf ∘
constraintSoundness`" (`:407`, `:1253-1254`; the tracker's K4 section says
`knowledgeSound_of_refinement`, a name that exists nowhere).

- `verify_knowledgeSound (fs bcs mca flock)`: in ArkLib's shape it bounds, for a fixed
  `stmtIn = input` and every prover, the probability of the event "the compiled verifier
  accepts ∧ ∀ q ∈ (extracted slot), `(input, q) ∉ M3Rel (leanIsaInstance prog s)`" by
  `niError` (`Security/Basic.lean:299-323`, `knowledgeSoundnessWith`; the same event in the
  round-by-round form, `RoundByRound.lean:553`). The slot is an `Option (Column μ)`,
  `Column μ : Type`.
- `satisfiedBy_witnessOf`, made a `Refinement (M3Rel I) (SatRel prog)` with `SatRel prog :=
  {p | SatisfiedBy prog p.1.1 p.2}` on witnesses in `Type 1`: `Refinement`'s two universes
  are independent (probe `Shapes`, output lines 10-13), and the construction typechecks
  (probe `Transport`, example 1). `Refinement.map_option_valid` has the polarity "every
  witness in the slot is valid ⇒ every mapped witness is valid" (`Refinement.lean:55-57`),
  while the game's bad event is "no witness in the slot is valid" (an empty slot is bad);
  the transport of the bad event is `∀ w' ∈ w?.map f, (x, w') ∉ S → ∀ w ∈ w?, (x, w) ∉ R`,
  which follows from `map_valid` in one line (probe `Transport`, `bad_of_bad`), and
  `code-spine.md`'s probe `knowledge_transport` proves the probabilistic statement for
  ArkLib's game in the same way. `Extractor.Straightline.map` cannot serve: its `WitIn'` is in
  `Type` (probe `UniverseFail`: "`EnsembleWitness (leanIsaEnsemble prog)` has type `Type 1` …
  but is expected to have type `Type`").
- `constraintSoundness (hwf : WellFormedBytecode prog)`: pointwise.

The composition typechecks in principle as an inclusion of events (probe `Transport`,
examples 3 and 4): if `¬ ∃ t, ValidExecution prog input t`, then every extracted `q` is
outside `M3Rel`, so the game's bad event is "the verifier accepts", and `Pr[accepts] ≤
niError`. That is the correct form of T4's first half: **a soundness theorem for the
language `{(prog, input) | ∃ t, ValidExecution prog input t}`** (the conclusion is a
closed proposition, so "except with probability" attaches to acceptance, not to it), in the
random-oracle model, for each admissible `s` or with the family composition of B.3, and under
`WellFormedBytecode prog`. It is not, and cannot be, an ArkLib `knowledgeSoundness` of a
relation on `EnsembleWitness` (`WitIn : Type`), nor a statement about the concrete
`verify prog input proof = true` (a closed Boolean), and it does not need the round-by-round
implication if `FiatShamirSecurity` consumes the round-by-round form directly.
