#!/usr/bin/env python3
"""Section A: the catalogue. Each entry's snippet is extracted from `git show b435631:<file>`
(never retyped): structures and inductives in full, definitions up to their data body without
proof fields, theorems and instances as their statement (up to the first `:=`)."""
import re, subprocess
ROOT='/home/scaraven/Documents/Verified-zkEVM/leanerVM'
PROOF_FIELDS={'complete','rbr','toFun_empty','toFun_next','toFun_full','verify_eq','read_eval',
              'mle_eq','constraints_degree','flushes_degree','hEq','outputInterface_heq','left_inv','right_inv','map_valid','eqIn'}
cache={}
def lines(f):
    if f not in cache:
        cache[f]=subprocess.run(['git','-C',ROOT,'show','b435631:'+f],capture_output=True,text=True).stdout.split('\n')
    return cache[f]
def extract(f,key,kind):
    L=lines(f)
    pat=re.compile(r'^(@\[[^\]]*\]\s*)?(private |noncomputable |public |protected )*'+re.escape(key)+r'(\b|$)')
    hits=[i for i,l in enumerate(L) if pat.match(l)]
    assert len(hits)==1,(f,key,hits)
    i=hits[0]
    if i>0 and L[i-1].strip().startswith('@['): i-=1
    j=i
    while j+1<len(L) and L[j+1].strip()!='': j+=1
    out=[]; indoc=False; inproof=False
    if kind=='stmt':
        for n in range(i,j+1):
            l=L[n]
            if ':=' in l:
                out.append(l.split(':=')[0].rstrip()+' :='); break
            out.append(l)
    else:
        for n in range(i,j+1):
            l=L[n]; t=l.strip()
            if indoc:
                if t.endswith('-/'): indoc=False
                continue
            if t.startswith('/--') or t.startswith('/-'):
                if not t.endswith('-/'): indoc=True
                continue
            if kind=='def':
                m=re.match(r'^(\w+)\s*(:=|\|)',t)
                if m and m.group(1) in PROOF_FIELDS: inproof=True; continue
                if m and m.group(1) not in PROOF_FIELDS: inproof=False
                if inproof and not re.match(r'^\w+\s*:=',t): continue
            out.append(l)
    return i+1,j+1,'\n'.join(out)
# (file, key, kind, class, plain language, depends on)
CAT=[
('LeanerVM/Protocol/Field.lean','structure Column','struct','load-bearing','A table of `2^n` values of `K`, indexed by the cube `{0,1}^n` low bit first: what is committed. Wrapped in a structure so that its oracle interface is the evaluation one, not ArkLib\'s position query on `Vector`.','CompPoly `CMlPolynomialEval`'),
('LeanerVM/Protocol/Field.lean','instance evalOracle','def','load-bearing','How the verifier queries a committed column: a query is a point `r ∈ E^n`, the answer is the multilinear extension `q̃(r)` with the entries lifted from `K` to `E`. Every seam is read through it.','`Column`, CompPoly `eval₂Mle`, ArkLib `OracleInterface`'),
('LeanerVM/Protocol/Field.lean','instance instSampleableTypeE','def','load-bearing','Uniform sampling of a challenge in `E` as three independent uniform limbs (VCVio needs a sampler for every challenge type).','`limbsEquiv`, VCVio `SampleableType`'),
('LeanerVM/Protocol/ToArkLib/Oracles.lean','abbrev NoOracle','def','load-bearing','The oracle family with no oracle (before the commit).','—'),
('LeanerVM/Protocol/ToArkLib/Oracles.lean','abbrev OneOracle','def','load-bearing','The oracle family with exactly one oracle of type `M` (the stack, from the commit on).','—'),
('LeanerVM/Protocol/ToArkLib/Oracles.lean','theorem noOracle_eq','stmt','helper','Any two empty oracle families are equal.','—'),
('LeanerVM/Protocol/Spine/Instance.lean','inductive Side','struct','load-bearing','Which side of the bus a tuple is on: provided (`push`) or consumed (`pull`).','—'),
('LeanerVM/Protocol/Spine/Instance.lean','structure Shape','struct','load-bearing','The tables: how many, each one\'s log-height (the announced sizes) and width.','—'),
('LeanerVM/Protocol/Spine/Instance.lean','abbrev Shape.ColumnId','def','load-bearing','A column: a table and a column index in it.','`Shape`'),
('LeanerVM/Protocol/Spine/Instance.lean','structure Layout','struct','load-bearing','How a column is read off the stack (`read`) and how a point of the column lifts to a point of the stack (`extend`), with the one law: the column\'s extension at `z` is the stack\'s at `extend c z`. A reading law: it does not say the columns are disjoint slices (C.2, D.4).','`Column`, CompPoly `eval₂Mle`'),
('LeanerVM/Protocol/Spine/Instance.lean','inductive Coord','struct','load-bearing','One coordinate of a boundary tuple: a constant, a column both parties know (index, bytecode), or a committed column of the block\'s height.','`Shape`, `Column`'),
('LeanerVM/Protocol/Spine/Instance.lean','structure BoundaryBlock','struct','load-bearing','`2^κ` boundary tuples on one side of the bus, given coordinate by coordinate (sixteen, separator first).','`Coord`, `Side`'),
('LeanerVM/Protocol/Spine/Instance.lean','structure PublicLine','struct','load-bearing','A column whose cells 0 and 1 the public statement fixes; `sent` says whether the proof carries its value (transcript only, not the relation); `pos` says the column has a cell 1.','`Shape`'),
('LeanerVM/Protocol/Spine/Instance.lean','structure M3Instance','struct','load-bearing','Everything the verifier reads about an arithmetization: the statement type, per table its constraints and flushes (polynomials over `K` of the row), a degree bound `d` with the two proofs, the count columns, the boundary blocks, the stack height `μ` and layout, the public lines of a statement, and the auxiliary predicate `aux` with its decision procedure. Trusted data (section F).','`Shape`, `Layout`, `BoundaryBlock`, `PublicLine`, CompPoly `CMvPolynomial`, `totalDegree`'),
('LeanerVM/Protocol/Spine/Instance.lean','abbrev κ','def','load-bearing','Log-height of a column: its table\'s.','`M3Instance`'),
('LeanerVM/Protocol/Spine/Instance.lean','def column','def','load-bearing','One column of the stack, through the layout.','`Layout.read`'),
('LeanerVM/Protocol/Spine/Instance.lean','def row','def','load-bearing','Row `x` of table `j`: the function giving each column\'s cell `x`.','`column`'),
('LeanerVM/Protocol/Spine/Instance.lean','def coordCell','def','load-bearing','The value of a boundary coordinate at row `x` of its block.','`Coord`, `column`'),
('LeanerVM/Protocol/Spine/Instance.lean','def flushTuples','def','load-bearing','The tuples of one side flushed by the tables: for every table, every flush of that side, every row, the sixteen coordinate polynomials evaluated on the row.','`row`, CompPoly `CMvPolynomial.eval`'),
('LeanerVM/Protocol/Spine/Instance.lean','def boundaryTuples','def','load-bearing','The tuples of one side on the boundary blocks: for every block of that side, every row.','`coordCell`'),
('LeanerVM/Protocol/Spine/Instance.lean','def tuples','def','load-bearing','Every tuple of one side: the tables\' then the boundary\'s.','`flushTuples`, `boundaryTuples`'),
('LeanerVM/Protocol/Spine/Instance.lean','def ConstraintsVanish','def','load-bearing','Every constraint of every table is zero on every row (the zerocheck target).','`row`'),
('LeanerVM/Protocol/Spine/Instance.lean','def Balanced','def','load-bearing','The pushed tuples are a permutation of the pulled tuples: the same multiset, counted in `ℕ`.','`tuples`, Mathlib `List.Perm`'),
('LeanerVM/Protocol/Spine/Instance.lean','def CountsNonzero','def','load-bearing','Every cell of every count column is nonzero (the count product).','`column`'),
('LeanerVM/Protocol/Spine/Instance.lean','def PublicLinesHold','def','load-bearing','Cells 0 and 1 of every line the statement names hold the line\'s values.','`column`, `PublicLine`'),
('LeanerVM/Protocol/Spine/Instance.lean','def M3Holds','def','load-bearing','The relation: the five clauses. What the verifier establishes about the committed stack.','the five clauses'),
('LeanerVM/Protocol/Spine/Instance.lean','abbrev TheOracle','def','load-bearing','The one oracle from the commit on: the stack.','`OneOracle`, `Column`'),
('LeanerVM/Protocol/Spine/Instance.lean','def M3Rel','def','load-bearing','`M3Holds` as ArkLib states relations: statement = public input with no oracle, witness = the stack.','`M3Holds`, `NoOracle`'),
('LeanerVM/Protocol/Spine/Seams.lean','structure ColumnClaim','struct','load-bearing','One column\'s extension at a point of `E^κ` equals a value.','`M3Instance`'),
('LeanerVM/Protocol/Spine/Seams.lean','def ColumnClaim.Holds','def','load-bearing','The claim is true of the stack, reading the column through the layout.','`column`, `eval₂Mle`'),
('LeanerVM/Protocol/Spine/Seams.lean','structure VirtualTerm','struct','load-bearing','One term of a linear claim: a weight in `E`, a table, a polynomial of its row over `K`, and the point the virtual table (the polynomial on every row) is extended to.','`M3Instance`'),
('LeanerVM/Protocol/Spine/Seams.lean','def VirtualTerm.table','def','load-bearing','The virtual table of a term: its polynomial evaluated on every row of its table, lifted to `E`.','`row`'),
('LeanerVM/Protocol/Spine/Seams.lean','def VirtualTerm.eval','def','load-bearing','The term\'s value: weight times the virtual table\'s extension at the point.','`table`, CompPoly `evalMle`'),
('LeanerVM/Protocol/Spine/Seams.lean','structure LinearClaim','struct','load-bearing','A weighted sum of virtual-table extensions equals a value (a zerocheck claim is one term of weight 1 and value 0; a bus form is a list of terms).','`VirtualTerm`'),
('LeanerVM/Protocol/Spine/Seams.lean','def LinearClaim.Holds','def','load-bearing','The sum of the terms\' values is the claimed value.','`VirtualTerm.eval`'),
('LeanerVM/Protocol/Spine/Seams.lean','structure Weight','struct','load-bearing','A weight on the stack (specification Definition 3.13): its values on the cube, an evaluator for its extension, and their agreement.','CompPoly `evalMle`'),
('LeanerVM/Protocol/Spine/Seams.lean','def Weight.pair','def','load-bearing','`Σ_x W(x)·q(x)` over the cube.','`Weight`, `Column`'),
('LeanerVM/Protocol/Spine/Seams.lean','structure WeightedClaim','struct','load-bearing','The pairing of a weight with the stack equals a value.','`Weight`'),
('LeanerVM/Protocol/Spine/Seams.lean','def WeightedClaim.Holds','def','load-bearing','True of the stack when the pairing is the value.','`Weight.pair`'),
('LeanerVM/Protocol/Spine/Seams.lean','structure BusOut','struct','load-bearing','What the bus phase hands on: linear claims and column claims.','`LinearClaim`, `ColumnClaim`'),
('LeanerVM/Protocol/Spine/Seams.lean','structure TableOut','struct','load-bearing','What the table sumcheck hands on: column claims.','`ColumnClaim`'),
('LeanerVM/Protocol/Spine/Seams.lean','structure PubOut','struct','load-bearing','What the public-input phase hands on: column claims (the same type as `TableOut`).','`ColumnClaim`'),
('LeanerVM/Protocol/Spine/Seams.lean','structure FlockOut','struct','load-bearing','What the Flock phase hands on: column claims and weighted claims.','`ColumnClaim`, `WeightedClaim`'),
('LeanerVM/Protocol/Spine/Seams.lean','abbrev theStack','def','load-bearing','The stack behind the one oracle.','`TheOracle`'),
('LeanerVM/Protocol/Spine/Seams.lean','def of','def','load-bearing','A seam from a predicate on the statement and the stack: the set of `((statement, oracles), ())` where it holds of the one oracle.','`theStack`'),
('LeanerVM/Protocol/Spine/Seams.lean','def commit','def','load-bearing','After the commit: `M3Holds` of the oracle itself.','`of`, `M3Holds`'),
('LeanerVM/Protocol/Spine/Seams.lean','def bus','def','load-bearing','After the bus phase: every linear claim holds, every term is within the degree bound, every column claim holds, the lines hold, `aux` holds.','`of`, the claims, `PublicLinesHold`'),
('LeanerVM/Protocol/Spine/Seams.lean','def table','def','load-bearing','After the table sumcheck: column claims, lines, `aux`.','`of`'),
('LeanerVM/Protocol/Spine/Seams.lean','def pub','def','load-bearing','After the public-input phase: column claims and `aux`.','`of`'),
('LeanerVM/Protocol/Spine/Seams.lean','def flock','def','load-bearing','After the Flock phase: column claims and weighted claims.','`of`'),
('LeanerVM/Protocol/Spine/Seams.lean','def done','def','load-bearing','After the opening: nothing (the whole set).','`of`'),
('LeanerVM/Protocol/ToArkLib/Component.lean','structure Def','struct','interface','A component: its number of rounds, its schedule (who speaks, what type), the instances that every message can be queried and every challenge sampled, the honest prover with the verifier (an ArkLib `OracleReduction` over the empty shared oracle), and the knowledge error it declares per challenge.','ArkLib `ProtocolSpec`, `OracleReduction`, `OracleInterface`, VCVio `SampleableType`'),
('LeanerVM/Protocol/ToArkLib/Component.lean','structure Complete','struct','interface','The completeness half a phase must supply: the prover\'s output is pure (redundant, D.7), the verifier is a check followed by a verdict (data), and perfect completeness from any shared state.','`Def`, ArkLib `OutputIsPure`, `GuardedForm`, `perfectCompleteness`'),
('LeanerVM/Protocol/ToArkLib/Component.lean','structure Security','struct','interface','The security half: completeness, the intermediate witness types, a round-by-round extractor, its knowledge state function from any shared state, and worst-case round-by-round knowledge soundness for them at the declared error.','`Complete`, ArkLib `Extractor.RoundByRound`, `KnowledgeStateFunction`, `rbrKnowledgeSoundnessWorstCaseWith`'),
('LeanerVM/Protocol/ToArkLib/Component.lean','def stateFunctionOfEq','def','helper (in the named statement)','Transport a knowledge state function along an equality of verifiers (needed because ArkLib\'s appended oracle verifier is only propositionally the appended ordinary verifier).','ArkLib `KnowledgeStateFunction`'),
('LeanerVM/Protocol/ToArkLib/Component.lean','theorem rbrKnowledgeSoundnessWorstCaseWith_of_eq','stmt','helper','The same transport for the bound.','`stateFunctionOfEq`'),
('LeanerVM/Protocol/ToArkLib/Component.lean','def Def.append','def','load-bearing','Two components in sequence: rounds add, schedules concatenate, reductions append (ArkLib), each challenge keeps its component\'s error.','ArkLib `OracleReduction.append`, `ChallengeIdx.sumEquiv`'),
('LeanerVM/Protocol/ToArkLib/Component.lean','def guardedAppend','def','helper (in the named statement)','The guarded form of an appended verifier from those of its parts (ArkLib\'s `GuardedForm.append`, cast along the append equation).','ArkLib `GuardedForm.append`'),
('LeanerVM/Protocol/ToArkLib/Component.lean','def Complete.append','def','helper (in the named statement)','Completeness composes: purity, guarded form, and ArkLib\'s guarded-append completeness theorem.','ArkLib `append_perfectCompleteness_of_guarded_verifiers`'),
('LeanerVM/Protocol/ToArkLib/Component.lean','def Security.append','def','helper (in the named statement)','Security composes: extractors appended through the first verdict (ArkLib), state functions by the ported `appendGuarded`, the bound by the ported theorem.','ArkLib `Extractor.RoundByRound.append`; `appendGuarded`; `append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first`'),
('LeanerVM/Protocol/ToArkLib/KnowledgeAppend.lean','def appendGuarded','def','helper (in the named statement)','The knowledge state function of two appended verifiers, the first guarded: the first\'s state up to the seam, then the first check together with the second\'s state on the first verdict (ported from ArkLib #615).','`state`'),
('LeanerVM/Protocol/ToArkLib/KnowledgeAppend.lean','theorem append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first','stmt','helper','Round-by-round knowledge soundness composes across an append whose first verifier is guarded, each challenge keeping its error (ported from ArkLib #615; admitted upstream at the pin).','`appendGuarded`, ArkLib `Extractor.RoundByRound.append`'),
('LeanerVM/Protocol/ToArkLib/PassThrough.lean','def passThrough','def','interface','The component with no round that maps the statement and keeps the oracles and the witness: the shape of bookkeeping steps.','`passThroughProver`, `passThroughVerifier`, `keepOracles`'),
('LeanerVM/Protocol/ToArkLib/PassThrough.lean','def passThroughComplete','def','interface','Its completeness, whenever the map carries the input relation into the output relation.','`passThrough`, `GuardedVerdict`'),
('LeanerVM/Protocol/ToArkLib/PassThrough.lean','def passThroughSecurity','def','interface','Its security at error zero, with the extractor that keeps the witness, whenever the map also reflects the output relation into the input relation.','`passThroughExtractor`, `passThroughStateFunction`, `passThrough_rbr`'),
('LeanerVM/Protocol/ToArkLib/SendOracle.lean','def sendOracle','def','load-bearing','The component whose one message becomes the one oracle: the prover sends the witness, the verifier keeps the statement and exposes the message; no challenge, error zero.','`sendSpec`, `sendProver`, `sendVerifier`, `sendEmbedding`'),
('LeanerVM/Protocol/ToArkLib/SendOracle.lean','def sendOracle_relOut','def','load-bearing (named form)','The input relation read on the oracle instead of the witness (definitionally `Seam.commit` at `M3Rel`).','—'),
('LeanerVM/Protocol/ToArkLib/SendOracle.lean','def sendOracleComplete','def','load-bearing (named form)','Its completeness half.','`sendVerifierPure`, `sendOracle_complete`'),
('LeanerVM/Protocol/ToArkLib/SendOracle.lean','def sendExtractor','def','load-bearing (named form)','Its extractor: read the message, at every round.','ArkLib `Extractor.RoundByRound`'),
('LeanerVM/Protocol/ToArkLib/SendOracle.lean','def sendStateFunction','def','load-bearing (named form)','Its knowledge state function: before the message, the relation of the candidate witness; after it, the relation of the message.','`sendExtractor`, `GuardedVerdict`'),
('LeanerVM/Protocol/ToArkLib/SendOracle.lean','def sendOracleSecurity','def','load-bearing (named form)','Its security half at error zero.','`sendOracleComplete`, `sendExtractor`, `sendStateFunction`, `sendOracle_rbr`'),
('LeanerVM/Protocol/ToArkLib/Refinement.lean','structure Refinement','struct','interface (the adaptor)','A map on witnesses between two relations over the same statements, sending valid witnesses to valid witnesses; the two witness types may live in different universes (D.7).','—'),
('LeanerVM/Protocol/ToArkLib/Refinement.lean','theorem map_option_valid','stmt','interface (the adaptor)','On an extractor\'s output slot: if every witness the slot may hold is valid for `R`, every witness of the mapped slot is valid for `S`. Pointwise; the probabilistic form is D.7.','`Refinement`'),
('LeanerVM/Protocol/ToArkLib/Refinement.lean','def Extractor.Straightline.map','def','helper (no consumer)','Post-compose ArkLib\'s straight-line extractor with a witness map (same universe).','ArkLib `Extractor.Straightline`'),
('LeanerVM/Protocol/ToArkLib/GuardedVerdict.lean','theorem Verifier.GuardedForm.of_probEvent_pos','stmt','helper','If a guarded verifier can output a statement satisfying `P`, its check passes and its verdict satisfies `P`: the last obligation of every knowledge state function.','ArkLib `GuardedForm`, VCVio `probEvent`'),
('LeanerVM/Protocol/ToArkLib/GuardedVerdict.lean','theorem Reduction.mem_support_run_of_guarded','stmt','helper','Every outcome of a run with a guarded verifier is a prover run with the verdict where the check passes, a rejection otherwise: how perfect completeness is proved.','ArkLib `Reduction.run`'),
('LeanerVM/Protocol/ToArkLib/KeepOracles.lean','def keepOracles','def','helper','The output-oracle description "the output oracles are the input oracles".','ArkLib `OracleOutputEmbedding`'),
('LeanerVM/Protocol/ToArkLib/KeepOracles.lean','theorem OracleVerifier.materializeOutput_of_keepOracles','stmt','helper','Such a verifier outputs the oracles it was given.','`keepOracles`'),
('LeanerVM/Protocol/Spine/Phase.lean','abbrev Def','def','interface','A phase: a component from a statement to a statement over the stack, with trivial witnesses.','`Component.Def`, `TheOracle`'),
('LeanerVM/Protocol/Spine/Phase.lean','abbrev Complete','def','interface','Its completeness half against two seams.','`Component.Complete`'),
('LeanerVM/Protocol/Spine/Phase.lean','abbrev Security','def','interface','Its security half against two seams.','`Component.Security`'),
('LeanerVM/Protocol/Spine/Phase.lean','abbrev passThrough','def','interface','The pass-through phase.','`Component.passThrough`'),
('LeanerVM/Protocol/Spine/Phase.lean','def passThroughComplete','def','interface','Its completeness when the map carries one seam into the other.','`Component.passThroughComplete`'),
('LeanerVM/Protocol/Spine/Phase.lean','def passThroughSecurity','def','interface','Its security when the map also reflects the second seam into the first (D.3 (a): impossible at the bus seam).','`Component.passThroughSecurity`'),
('LeanerVM/Protocol/Spine/Compose.lean','abbrev commitSpec','def','load-bearing','The commit phase\'s schedule: one prover message, the stack.','`sendSpec`'),
('LeanerVM/Protocol/Spine/Compose.lean','abbrev commitDef','def','load-bearing','The commit phase: the send-oracle component at the stack.','`sendOracle`'),
('LeanerVM/Protocol/Spine/Compose.lean','abbrev commitExtractor','def','load-bearing (named form)','Its extractor: read the stack off the message.','`sendExtractor`'),
('LeanerVM/Protocol/Spine/Compose.lean','def commitComplete','def','load-bearing (named form)','Its completeness from `M3Rel` to `Seam.commit`.','`sendOracleComplete`'),
('LeanerVM/Protocol/Spine/Compose.lean','def commitSecurity','def','load-bearing (named form)','Its security at error zero.','`sendOracleSecurity`'),
('LeanerVM/Protocol/Spine/Compose.lean','structure Phases where','struct','load-bearing','The five phases after the commit, by their statement types.','`Phase.Def`, the four outputs'),
('LeanerVM/Protocol/Spine/Compose.lean','def Phases.toDef','def','load-bearing','The whole protocol as one component: the commit, then five appends.','`commitDef`, `Def.append`'),
('LeanerVM/Protocol/Spine/Compose.lean','structure Phases.Complete','struct','load-bearing','The five completeness halves against the seams.','`Phase.Complete`, the seams'),
('LeanerVM/Protocol/Spine/Compose.lean','def Phases.Complete.toDef','def','helper','The composed completeness.','`commitComplete`, `Complete.append`'),
('LeanerVM/Protocol/Spine/Compose.lean','structure Phases.Security','struct','load-bearing','The five security halves against the seams.','`Phase.Security`, the seams'),
('LeanerVM/Protocol/Spine/Compose.lean','def Phases.Security.toDef','def','load-bearing (named form)','The composed security: the commit\'s, then five appends.','`commitSecurity`, `Security.append`'),
('LeanerVM/Protocol/Spine/Compose.lean','def leanVmPiop','def','load-bearing','The oracle protocol: the composed reduction.','`Phases.toDef`'),
('LeanerVM/Protocol/Spine/Compose.lean','def leanVmVerifier','def','load-bearing','Its verifier.','`Phases.toDef`'),
('LeanerVM/Protocol/Spine/Compose.lean','def leanVmProver','def','interface','Its honest prover (not in either theorem\'s statement; `leanVmPiop` carries it).','`Phases.toDef`'),
('LeanerVM/Protocol/Spine/Compose.lean','def piopError','def','load-bearing','Its error per challenge: the phases\' declarations side by side (section F).','`Def.append`'),
('LeanerVM/Protocol/Spine/Compose.lean','def piopExtractor','def','load-bearing (named form)','Its extractor: the composed one (D.5).','`Phases.Security.toDef`'),
('LeanerVM/Protocol/Spine/Compose.lean','theorem piop_perfectCompleteness','stmt','master theorem','Given every phase\'s completeness, the honest prover convinces the verifier with probability one on every `(input, q)` with `M3Holds I input q`.','`leanVmPiop`, `M3Rel`, `Seam.done`, ArkLib `perfectCompleteness`'),
('LeanerVM/Protocol/Spine/Compose.lean','theorem piop_rbrKnowledgeSoundness','stmt','master theorem','Given every phase\'s security, the verifier is round-by-round knowledge sound at the composed error, for the composed extractor and state function.','`leanVmVerifier`, `piopExtractor`, `piopError`, ArkLib `rbrKnowledgeSoundnessWorstCaseWith`'),
('LeanerVM/Protocol/Spine/Compose.lean','theorem piop_rbrKnowledgeSoundness_exists','stmt','master theorem (existential form)','The same with the extractor and state function forgotten.','`piop_rbrKnowledgeSoundness`'),
('LeanerVM/Protocol/Spine/Toy.lean','abbrev shape','def','test fixture','One table of height two and width three.','`Shape`'),
('LeanerVM/Protocol/Spine/Toy.lean','def slice','def','test fixture','Column `i` is the slice at cells `2i, 2i+1`.','`Column`'),
('LeanerVM/Protocol/Spine/Toy.lean','def extend','def','test fixture','The selector of column `i`: `(z, i mod 2, i div 2)`.','—'),
('LeanerVM/Protocol/Spine/Toy.lean','theorem read_eval','stmt','test fixture','The law for the three slices.','`slice`, `extend`'),
('LeanerVM/Protocol/Spine/Toy.lean','def layout','def','test fixture','The toy\'s layout.','`Layout`'),
('LeanerVM/Protocol/Spine/Toy.lean','def constraint','def','test fixture','Column 2 is Boolean: `X₂² − X₂`.','CompPoly `CMvPolynomial`'),
('LeanerVM/Protocol/Spine/Toy.lean','def flush','def','test fixture','The one flush: `(X₀, 0, …)`, pushed.','—'),
('LeanerVM/Protocol/Spine/Toy.lean','def boundary','def','test fixture','The one boundary block: pulls `([1, 1], 0, …)`.','`BoundaryBlock`'),
('LeanerVM/Protocol/Spine/Toy.lean','abbrev toy','def','test fixture','The toy instance: `d = 2`, column 1 a count column, the public line on column 2 with cells `(input, 0)`, `aux := True`.','everything above'),
('LeanerVM/Protocol/Spine/Toy.lean','def honest','def','test fixture','The honest stack `[1, 1, 1, 1, 1, 0, 0, 0]`.','`Column`'),
]
out=['## A. Catalogue\n',
'Every public declaration of the modules in scope, in file order, with its class: **load-bearing** (the statement of a master theorem unfolds to it; "named form" marks those reached only through `piop_rbrKnowledgeSoundness`\'s named extractor and state function, section B), **interface** (a phase author must meet or use it), **helper** (used only inside proofs; those a master statement unfolds to are marked), **test fixture**. Snippets are extracted from `git show b435631:<file>` by `probes/code-spine/catalogue.py`: structures and inductives in full, definitions with their data body and without proof fields, theorems and instances as their statement. Helpers that are pure proof lemmas (`passThrough_materializeOutput`, `passThroughVerifier_toVerifier_run`, `passThroughPure`, `passThroughProver`, `passThroughVerifier`, `passThroughExtractor`, `passThroughStateFunction`, `passThrough_rbr`, `sendSpec`, `sendProver`, `sendEmbedding`, `sendVerifier`, `sendOracle_outputPure`, `send_materializeOutput`, `sendVerifier_toVerifier_run`, `sendVerifierPure`, `sendOracle_complete`, `sendWitMid`, `sendOracle_rbr`, `Refinement.id`, `Refinement.comp`, `noOracle_eq`, and the seventeen lemmas of `KnowledgeAppend` other than its two named declarations) are named here and not listed one by one; the send-oracle ones are counted in section B where the named statement reaches them.\n',
'Library objects (all at the pins ArkLib `dca90385`, CompPoly `3468b38c`, VCVio `f9dc47d9`) are introduced where first used in sections C and D; the catalogue names them in the "depends on" column.\n']
cur=None
for f,key,kind,cls,desc,deps in CAT:
    a,b,txt=extract(f,key,kind)
    if f!=cur:
        out.append(f'### `{f}`\n'); cur=f
    name=key.split(' ',1)[1]
    out.append(f'**`{name}`** (`{f.split("/")[-1]}:{a}-{b}`) — *{cls}*. {desc} Depends on: {deps}.\n')
    out.append('```lean\n'+txt+'\n```\n')
open('dossier/70-A-catalogue.md','w').write('\n'.join(out))
print('catalogue entries', len(CAT))
