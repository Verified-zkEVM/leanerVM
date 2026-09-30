## B. The audit surface, measured

### B.1 Method

"Load-bearing" is taken literally: a declaration is counted when the **statement** of a master
theorem mentions it or unfolds to it, transitively, down to library objects. Three sets:

- **C**: what `piop_perfectCompleteness` unfolds to (`Compose.lean:162-164`): `Phases`,
  `Phases.Complete` (so `Phase.Def`, `Phase.Complete`, `Component.Def`, `Component.Complete`),
  `leanVmPiop` (so `Phases.toDef`, `Def.append`, `commitDef`, the send-oracle reduction),
  `M3Rel` (so `M3Holds` and everything under it), the six seams (so every claim and its
  `Holds`), `TheOracle` and the evaluation oracle.
- **Kx**: what `piop_rbrKnowledgeSoundness_exists` adds (`:181-184`): `Phases.Security`,
  `Phase.Security`, `Component.Security`, `leanVmVerifier`, `piopError`.
- **K**: what `piop_rbrKnowledgeSoundness` adds by naming its extractor and state function
  (`:172-176`, `S.toDef.witMid`, `piopExtractor P S`, `S.toDef.kSF init impl`): the
  composition of securities (`Security.append`, `Complete.append` for its `guarded`,
  `guardedAppend`, `stateFunctionOfEq`), the ported state-function append
  (`KnowledgeAppend.state`, `left`, `right`, `Witness`, the two witness lemmas,
  `appendGuarded`) and the commit phase's security (`commitSecurity`, `commitComplete`,
  `commitExtractor`, `sendOracleSecurity`, `sendOracleComplete`, `sendVerifierPure`,
  `sendExtractor`, `sendWitMid`, `sendStateFunction`, `sendOracle_relOut`).

Counting rule: a declaration's lines from its head to the end of its data body, excluding blank
lines, comment-only lines and, for definitions, proof fields (`complete`, `rbr`,
`toFun_empty/next/full`, `verify_eq`, …); "with docstrings" adds the docstring block above it
and the field docstrings inside it. Proof bodies of theorems are never counted. The script is
`probes/code-spine/surface.py`, which reads every file with `git show b435631:` and finds each
declaration by name; its output is reproduced below. Structures' field docstrings are counted
as docstrings, so `M3Instance` is 14 lines of code and 31 with its docstrings.

### B.2 The count

```text
C    2   6  Field.lean             67-69   structure Column
C    5   6  Field.lean             86-90   def limbsEquiv
C    1   2  Field.lean             93-93   instance instSampleableTypeE
C    5   7  Field.lean            102-106  instance evalOracle
C    1   2  Oracles.lean           26-26   abbrev NoOracle
C    1   2  Oracles.lean           29-29   abbrev OneOracle
C    4   5  Instance.lean          51-54   inductive Side
C    4   8  Instance.lean          57-63   structure Shape
C    1   2  Instance.lean          66-66   abbrev Shape.ColumnId
C    6  14  Instance.lean          73-81   structure Layout
C    4   7  Instance.lean          86-89   inductive Coord
C    4   8  Instance.lean          92-98   structure BoundaryBlock
C    6  15  Instance.lean         102-114  structure PublicLine
C   14  31  Instance.lean         119-148  structure M3Instance
C    1   1  Instance.lean         150-150  attribute [instance] M3Instance.decAux
C    1   2  Instance.lean         157-157  abbrev κ
C    1   2  Instance.lean         160-160  def column
C    2   3  Instance.lean         163-164  def row
C    4   5  Instance.lean         167-170  def coordCell
C    4   6  Instance.lean         174-177  def flushTuples
C    3   4  Instance.lean         180-182  def boundaryTuples
C    2   3  Instance.lean         185-186  def tuples
C    2   3  Instance.lean         197-198  def ConstraintsVanish
C    1   2  Instance.lean         201-201  def Balanced
C    2   3  Instance.lean         204-205  def CountsNonzero
C    4   5  Instance.lean         208-211  def PublicLinesHold
C    2   4  Instance.lean         219-220  def M3Holds
C    1   2  Instance.lean         226-226  abbrev TheOracle
C    2   4  Instance.lean         230-231  def M3Rel
C    4   8  Seams.lean             57-63   structure ColumnClaim
C    2   3  Seams.lean             66-67   def ColumnClaim.Holds
C    5  11  Seams.lean             71-79   structure VirtualTerm
C    3   4  Seams.lean             82-84   def VirtualTerm.table
C    2   3  Seams.lean             87-88   def VirtualTerm.eval
C    3   6  Seams.lean             91-95   structure LinearClaim
C    2   3  Seams.lean             98-99   def LinearClaim.Holds
C    4   9  Seams.lean            103-109  structure Weight
C    2   3  Seams.lean            112-113  def Weight.pair
C    3   6  Seams.lean            116-120  structure WeightedClaim
C    2   3  Seams.lean            123-124  def WeightedClaim.Holds
C    3   7  Seams.lean            130-134  structure BusOut
C    2   4  Seams.lean            137-139  structure TableOut
C    2   4  Seams.lean            142-144  structure PubOut
C    3   6  Seams.lean            147-151  structure FlockOut
C    1   2  Seams.lean            159-159  abbrev theStack
C    2   3  Seams.lean            166-167  def of
C    1   3  Seams.lean            171-171  def commit
C    3   5  Seams.lean            175-177  def bus
C    2   3  Seams.lean            180-181  def table
C    1   2  Seams.lean            184-184  def pub
C    2   3  Seams.lean            187-188  def flock
C    1   2  Seams.lean            191-191  def done
C    9  17  Component.lean         52-66   structure Def
C    1   1  Component.lean         68-68   attribute [instance] Def.msgOracle
C    7  12  Component.lean         76-85   structure Complete
C    6   7  Component.lean        143-148  def Def.append
Kx  12  20  Component.lean         90-106  structure Security
K    8  13  Component.lean        110-120  def stateFunctionOfEq
K    4   5  Component.lean        156-159  def guardedAppend
K    4   9  Component.lean        162-169  def Complete.append
K    8  14  Component.lean        174-184  def Security.append
K    2   3  KnowledgeAppend.lean   55-56   abbrev Witness
K    3   5  KnowledgeAppend.lean   60-62   theorem witness_left
K    3   5  KnowledgeAppend.lean   66-68   theorem witness_right
K    5   6  KnowledgeAppend.lean   71-75   def left
K    5   6  KnowledgeAppend.lean   78-82   def right
K   15  16  KnowledgeAppend.lean  182-196  def state
K    5  17  KnowledgeAppend.lean  474-488  def appendGuarded
C    2   3  SendOracle.lean        38-39   def sendSpec
C    6   7  SendOracle.lean        42-47   def sendProver
C    2   5  SendOracle.lean        50-53   def sendEmbedding
C    3   4  SendOracle.lean        56-58   def sendVerifier
C    5   6  SendOracle.lean        61-65   def sendOracle
K    3   5  SendOracle.lean        71-73   def sendOracle_relOut
K    2   4  SendOracle.lean       101-103  def sendVerifierPure
K    4   6  SendOracle.lean       121-125  def sendOracleComplete
K    1   2  SendOracle.lean       130-130  abbrev sendWitMid
K    5   7  SendOracle.lean       134-138  def sendExtractor
K    5  19  SendOracle.lean       145-161  def sendStateFunction
K    5   7  SendOracle.lean       172-177  def sendOracleSecurity
C    2   3  Phase.lean             37-38   abbrev Def
C    4   5  Phase.lean             41-44   abbrev Complete
Kx   4   5  Phase.lean             47-50   abbrev Security
C    1   2  Compose.lean           51-51   abbrev commitSpec
C    2   4  Compose.lean           55-56   abbrev commitDef
C    6  13  Compose.lean           73-84   structure Phases where
C    3   4  Compose.lean           89-91   def Phases.toDef
C    6  12  Compose.lean           94-104  structure Phases.Complete
C    3   4  Compose.lean          134-136  def leanVmPiop
C    4   6  Compose.lean          162-165  theorem piop_perfectCompleteness
Kx   6  12  Compose.lean          113-123  structure Phases.Security
Kx   3   4  Compose.lean          139-141  def leanVmVerifier
Kx   1   2  Compose.lean          149-149  def piopError
Kx   5   7  Compose.lean          181-185  theorem piop_rbrKnowledgeSoundness_exists
K    1   2  Compose.lean           59-59   abbrev commitExtractor
K    2   4  Compose.lean           63-64   def commitComplete
K    2   3  Compose.lean           67-68   def commitSecurity
K    4   5  Compose.lean          126-129  def Phases.Security.toDef
K    4   6  Compose.lean          153-156  def piopExtractor
K    6  11  Compose.lean          172-177  theorem piop_rbrKnowledgeSoundness

per file: code lines C / Kx / K ; all lines with docstrings
Field.lean               13    0    0     21
Oracles.lean              2    0    0      4
Instance.lean            75    0    0    139
Seams.lean               55    0    0    103
Component.lean           23   12   24     98
KnowledgeAppend.lean      0    0   38     58
SendOracle.lean          18    0   25     75
Phase.lean                6    4    0     13
Compose.lean             25   15   19    101

completeness theorem (C):                   code 217, with docstrings 382, declarations 70
knowledge theorem, existential form (C+Kx): code 248, with docstrings 432, declarations 76
knowledge theorem, With form (C+Kx+K):      code 354, with docstrings 612, declarations 100
```

In words. To read **what perfect completeness says**, an auditor reads 70 declarations,
217 lines of Lean (382 with their docstrings): 75 in `Instance.lean` (the instance and the
relation), 55 in `Seams.lean` (claims and seams), 25 in `Compose.lean`, 23 in
`Component.lean`, 18 in `SendOracle.lean` (the commit reduction), 13 in `Field.lean`, 6 in
`Phase.lean`, 2 in `Oracles.lean`. **Knowledge soundness in its existential form** adds 6
declarations and 31 lines (the `Security` structures, the verifier, the error). **Knowledge
soundness for the named extractor** adds 24 declarations and 106 lines, of which 38 are the
ported state-function append and 25 the commit phase's security data. The whole `With` form
is 100 declarations, 354 lines, 612 with docstrings.

The library objects the statements unfold to, by revision `dca90385` (ArkLib), `3468b38c`
(CompPoly), `f9dc47d9` (VCVio), not counted line by line:

- ArkLib: `ProtocolSpec`, `Direction`, `ChallengeIdx`, `MessageIdx`, `Transcript`,
  `FullTranscript`, `ProtocolSpec.append` (`++ₚ`) and `ChallengeIdx.sumEquiv`;
  `OracleInterface`; `Prover`, `OracleProver`, `Verifier`, `OracleVerifier`,
  `OracleOutputEmbedding`, `OracleVerifier.toVerifier`, `Reduction`, `OracleReduction`,
  `OracleReduction.append`, `Verifier.append`; `Prover.OutputIsPure`, `Verifier.PureForm`,
  `Verifier.GuardedForm`, `GuardedForm.append`, `PureForm.toGuardedForm`;
  `Reduction.completeness`, `perfectCompleteness`, `OracleReduction.perfectCompleteness`;
  `Extractor.RoundByRound`, `Extractor.RoundByRound.append`, `Verifier.KnowledgeStateFunction`,
  `rbrKnowledgeSoundnessWorstCase`, `rbrKnowledgeSoundnessWorstCaseWith`; `Verifier.run`,
  `Prover.run`, `Reduction.run` (through `perfectCompleteness`); `challengeQueryImpl`,
  `QueryImpl.addLift`.
- VCVio: `OracleComp`, `OracleSpec`, `[]ₒ` (`emptySpec`), `QueryImpl`, `simulateQ`,
  `ProbComp`, `OptionT`, `Pr[· | ·]` (`probEvent`), `$ᵗ` (`uniformSample`), `SampleableType`,
  `StateT`.
- CompPoly: `CMlPolynomialEval`, `evalMle`, `eval₂Mle`, `CMvPolynomial`, `CMvPolynomial.eval`,
  `totalDegree`, `BF64`, `BF64.Ext3`, `Extension.Ext.ofVector`, `Ext.coeffs`, `algebraMap K E`
  (through Mathlib), `Vector`.
- Mathlib: `List.Perm`, `Set`, `Finset.sum` (in `Weight.pair`), `NNReal`, `ENNReal`.

The earlier review counted "306 statement lines … about 400 lines" for the whole of the
spine's ten files (`docs/reviews/protocol-spine.md:426-448`), every declaration included. The
count here is smaller because it keeps to what the two statements unfold to and larger in the
`With` form than an auditor of the existential form needs.

### B.3 Proposals to reduce it

Each: what is removed, what it costs, whether any statement changes. Lines are code lines of
B.2.

1. **State the master knowledge theorem in the existential form and keep the named form as a
   lemma.** Removes from the reading list the 24 declarations of class K (106 lines): the
   composition of securities, the ported append, the commit phase's data. Costs: the named
   extractor leaves the theorem's statement; acceptance test 24 then rests on the lemma
   `piop_rbrKnowledgeSoundness` (kept) and on `piopExtractedStack_eq` (section F). Changes no
   statement; it changes which one is called the master theorem. Not recommended if the named
   extractor is what T4 must carry through Fiat–Shamir; recommended as the *reading order*
   (the existential theorem first, the named one as its refinement).
2. **Delete `Component.Complete.outputPure`** (2 lines, plus one line in every phase and in
   `Complete.append`): derivable for every component (D.7, ArkLib's
   `Prover.instOutputIsPureEmpty` at the pin). Costs one import (`NoAmbient`) or a four-line
   restatement. Changes no statement: `Complete` loses a field every instance discharges by
   `rfl`.
3. **Merge `TableOut` and `PubOut`** (4 lines, two structures that are both `columns : List
   (ColumnClaim I)`; `FlockOut` is `TableOut` plus `weighted`). Replace by one `Pool I` with
   `columns` and `weighted`, and let each seam say which list is empty where it must be
   (`Seam.table`: `weighted = []`). Costs: the statement types of three phases become the
   same, so a phase in the wrong slot is caught by its seam proof, not by its type; the
   docstrings' "column claims, now with the public words' claims" become a comment on the seam.
   Changes the statements of `Seam.table`, `Seam.pub` (one conjunct each) and the fields of
   `Phases`. Recommended only if the sibling dossier's `BusOut` redesign is adopted, so that the
   statement types are revisited once.
4. **Derive `Layout.read` from `extend`** (C.2; `read` and `read_eval` are 6 of `Layout`'s 6
   lines, replaced by one law on `extend`). Costs: a lemma "the extension at a cube point is
   the entry" (CompPoly has it as `eval_mle_eq_eval`, cited in `Field.lean:50`) and, for the
   toy, `slice` becomes a theorem. Changes the definition of `column` and hence of every
   clause, definitionally: no statement's meaning changes.
5. **Fold `Phase.Def/Complete/Security`** (10 lines): three abbreviations of `Component.*`
   at `TheOracle I` and `Unit`; `Phase.passThrough*` likewise. A phase author writes
   `Component.Def I.Stmt (TheOracle I) Unit …` once. Costs: longer signatures in `Phases`
   (five fields). Changes no statement. Marginal; the abbreviations are the documented
   interface and cost 13 lines with docstrings.
6. **Drop `Weight.mle` and `mle_eq`** (2 of `Weight`'s 4 lines): the seam never uses `mle`
   (`WeightedClaim.Holds` is `Weight.pair`, the cube sum). `mle` is the verifier's evaluator
   for the opening phase, a property of the *phase*, not of the claim's truth. Costs: the
   opening phase must carry the evaluator itself (as a field of its `Def`, or by requiring
   `Weight` to be `MLE-friendly` there). Changes the statement of `Seam.flock` by removing a
   field nobody reads there. Recommended: it also removes the temptation to prove the seam by
   `mle` rather than by the cube sum.
7. **`M3Instance.d` with its two proof fields** (3 lines) could be replaced by a subtype of
   polynomials on `constraints` and `flushes` (section F, the degree finding): the two
   proof fields go, `Seam.bus` loses a conjunct, the table verifier loses a guard. Changes the
   statements of `M3Instance` and `Seam.bus`, and of `VirtualTerm`.
8. **Drop `decAux`** from `M3Instance` (2 lines with the attribute): decidability of `aux` is
   used by nothing load-bearing; the `Decidable` instances for `M3Holds` serve the tests.
   Costs: the tests declare `instance : DecidablePred toy.aux` locally. Changes the statement
   of `M3Instance`. Weak: an instance that cannot decide its own `aux` is a smell, and the
   read-everything phase (D.3 (d)) needs it; keep unless the field list is revisited.
9. **The `{σ} init impl` binders** (eleven declarations): forced by ArkLib (C.6). A wrapper
   `Phase.Complete'` at `σ := Unit` would not compose (ArkLib's append needs every `s : σ`).
   Not removable at this pin.
10. **`sendOracle_relOut`** (3 lines) is `Seam.commit` under another name, needed because the
    generic send-oracle component is stated for any relation; `commitComplete`'s type
    ascription is what makes the two coincide. Keep; note in `Compose.lean` that the
    coincidence is definitional, so an auditor need not read `sendOracle_relOut`.
11. **`sendStateFunction`'s data is in the statement** (5 lines) only through the named form
    (K). If proposal 1 is taken it leaves the surface.

What is **not** proposed: removing `Phases.Complete` in favour of `Phases.Security`
(`Security extends Complete`, and completeness is landed before security per convention
*Holes*); removing `piop_rbrKnowledgeSoundness_exists` (it is the smaller statement).

Net effect of proposals 2, 4, 6 and 7, all of which keep the theorems' meaning: about 15
code lines and two proof obligations per phase (`outputPure`, the degree of its terms) off
the surface, and one guard out of the table phase's verifier.
