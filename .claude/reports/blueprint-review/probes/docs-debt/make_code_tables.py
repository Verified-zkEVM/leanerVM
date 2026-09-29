#!/usr/bin/env python3
"""Builds the Markdown tables of section D of the dossier from codes.json (the counts) and a
hand-written dictionary (the meanings). Counts are occurrences of the code string in each
document; for a code with several meanings the split by meaning was made by reading every
occurrence (ctx_*.txt) and is given in the dossier's collision table, not here."""
import json, re, os
P="/home/scaraven/Documents/Verified-zkEVM/leanerVM/.claude/reports/blueprint-review/probes/docs-debt"
d=json.load(open(os.path.join(P,"codes.json")))
core=[("blueprint","BP"),("status","ST"),("tracker-body","TB"),("hole-comment","HC"),("tracker-other-comments","OC"),("review-spine","RS"),("review-layer1","RL"),("review-public-input","RP")]
def uses(c):
    dv=d.get(c,{})
    parts=[f"{ab} {len(dv[n])}" for n,ab in core if dv.get(n)]
    tot=sum(len(dv.get(n,[])) for n,_ in core)
    return tot, ", ".join(parts)
def first(c,doc):
    l=d.get(c,{}).get(doc,[])
    return l[0] if l else None
def table(title, rows):
    print(f"\n**{title}**\n")
    print("| Code | What it denotes | Defined at | Uses in the eight documents |")
    print("| --- | --- | --- | --- |")
    for c,mean,where in rows:
        tot,u=uses(c)
        print(f"| `{c}` | {mean} | {where} | {tot}: {u} |")
BPH="`protocol-blueprint.md`"
holes=[
("S(hole)","the spine: instance, relation, seams, phase interfaces, composition, toy instance","blueprint:597; hole comment:5"),
("L1","tables and stacking (Layer 1): hypercube tables, stacking, the fixed columns","blueprint:603; no section in the hole comment"),
("I1","Clean expressions as polynomials (Layer 2)","blueprint:604; no section in the hole comment"),
("I2","the adaptor (Layer 3): the leanISA instance, `stackOf`, `witnessOf` and their theorems","blueprint:605; hole comment:44"),
("G1","generic sumcheck, definition and completeness (Layer 4)","blueprint:598; no section in the hole comment"),
("G2","generic sumcheck, round-by-round knowledge soundness (Layer 4)","blueprint:599"),
("G3","batching of claims by powers of one challenge (Layer 4)","blueprint:600"),
("G4","fingerprint, product-determines-multiset lemma, collision bound (Layer 5)","blueprint:601"),
("G5","grand-product GKR, definition and completeness (Layer 5)","blueprint:602; hole comment:28"),
("G6","grand-product GKR, knowledge soundness (Layer 5)","blueprint:602; hole comment:28"),
("P1","bus phase, definition and completeness (Layer 6)","blueprint:606; hole comment:61"),
("P2","bus phase, knowledge soundness (Layer 6)","blueprint:606; hole comment:61"),
("P3","table sumcheck phase, definition and completeness (Layer 7)","blueprint:607; hole comment:75"),
("P4","table sumcheck phase, knowledge soundness (Layer 7)","blueprint:607; hole comment:75"),
("P5","public-input phase, both halves (Layer 8)","blueprint:608; hole comment:89"),
("P6","Flock phase as an interface supplied by issue #3 (Layer 9)","blueprint:609; hole comment:102"),
("P7","opening phase and claim pool, definition and completeness (Layer 10)","blueprint:610; hole comment:115"),
("P8","opening phase, knowledge soundness (Layer 10)","blueprint:610; hole comment:115"),
("C1","knowledge-soundness composition, ported from ArkLib pull request 615","blueprint:611; hole comment:129"),
("K1","WHIR opening over binary Reed-Solomon codes (Layer 11)","blueprint:612; hole comment:144"),
("K2","Merkle trees, BLAKE2s byte hasher, WHIR parameters (Layer 11)","blueprint:613; hole comment:158"),
("K3","transcript, proof object, compiled verifier `verify` and its refinement theorem (Layer 12)","blueprint:614; hole comment:172"),
("K4","the two base theorems of target T4 (Layer 13)","blueprint:615; hole comment:186"),
]
ledger=[
("A1","ArkLib admits the sumcheck's single-round knowledge soundness","blueprint:259; status:173; tracker body:63"),
("A2","ArkLib admits the knowledge-soundness composition of appended reductions","blueprint:260; status:174; tracker body:64"),
("A3","ArkLib admits 'round-by-round implies plain' knowledge soundness","blueprint:261; status:175; tracker body:65"),
("A4","ArkLib admits every context-lifting security theorem (not consumed)","blueprint:262 only; absent from the status and tracker tables"),
("A5","ArkLib admits or lacks Fiat-Shamir and BCS security","blueprint:263; status:176; tracker body:66"),
("A6","ArkLib has no grand product, GKR, batching or stacking","blueprint:264; status:177; tracker body:67"),
("A7","ArkLib has no WHIR, Merkle tree or BLAKE2s","blueprint:265; status:178; tracker body:68"),
("A8","ArkLib admits mutual correlated agreement up to the Johnson bound","blueprint:266; status:179; tracker body:69"),
("A9","ArkLib admits the ring-switching packing lemmas","blueprint:267; status:180; tracker body:70"),
("C2","request to leanISA: power-of-two heights in `Caps`, bus data per channel (done)","status:182; tracker body:72; not in the blueprint's table"),
("C3","Clean lacks a balance counted in the naturals with direction tags","status:183; tracker body:73; not in the blueprint's table"),
("C4","Clean lacks fixed columns and sound prover data","status:184; tracker body:74; not in the blueprint's table"),
]
arkfind=[
("A10","ArkLib relations are sets of pairs; the documented refactor has not happened","status:332"),
("A11","ArkLib's averaged round-by-round notion is weaker than the worst-case one the layers prove","status:334"),
("A12","ArkLib's `extractability` for commitments is `False`-valued; not cited","status:336"),
("A13","two ArkLib statements contain `sorry` in their types; never cited","status:337"),
("A14","ArkLib's typed-interaction replacement has no security definitions yet","status:338"),
("A15","ArkLib's toy problem is sorry-free; its code-generation probes are the pattern for `verify`","status:340"),
("A16","ArkLib pins CompPoly at a tag; leanerVM's pin wins the resolution","status:341"),
("A17","ArkLib's position-query oracle instance on `Vector` is global, so `Column` must be a structure","status:342"),
("A18","ArkLib `main` had moved 246 commits past the pin on 2026-09-24","status:345"),
("A19","ArkLib pull request 615's composition file compiles unchanged against the pin","status:346"),
]
spec=[
("S6","specification section 8.4 (Fiat-Shamir) is `TODO` (inherited from leanISA)","status:285"),
("S9","the proof of specification Lemma 5.2 is `TODO`","status:286"),
("S10","specification section 5.3 does not state the degree of a radix-4 round polynomial","status:287"),
("S11","specification section 8.5 does not say the push and pull roots are one scalar","status:289"),
("S12","Annex B omits the 17 grinding bits per level that the Rust applies","status:291"),
("S13","retired: a bound of 5 instead of 4 read off a PDF that is not the pinned text","status:293"),
("S14","the PDF `leanVM-b-2.pdf` is not the pinned text and must not be cited","status:297"),
("S15","the specification gives no rule for stacking blocks of equal size","status:303"),
("S16","the specification's equations are numbered (1) to (4); 'equation (5.4)' does not exist","status:303"),
]
rust=[
("F1","no domain-separation labels: four numeric tags in lane 3","status:305"),
("F2","Flock's fixed coordinate is a hard-coded constant without provenance","status:307"),
("F3","one root for the push and pull products","status:309"),
("F4","the table sumcheck's target is derived by the verifier, never sent","status:310"),
("F5","the three bus forms share the last three powers of the batching challenge","status:311"),
("F6","the table round polynomial is a cubic; three scalars travel","status:312"),
("F7","one coefficient of every round polynomial is never transmitted","status:313"),
("F8","ring-switched claims take the low powers in the opening batch","status:315"),
("F9","the Python verifier omits four caps that the Rust verifier checks","status:316"),
("F10","the Rust verifier's rejection set; structure checks are `assert!`s","status:319"),
("F11","the count tree holds the tables' count columns only","status:321"),
("F12","fill blocks make announced heights exact","status:322"),
("F13","grinding binds the nonce even when the check fails","status:324"),
("F14","the seed hashes one constant naming the circuit, not the matrices","status:325"),
("F15","the stacking bound on the stack height is checked separately from the caps","status:327"),
("F16","128 security bits round by round; the bus needs no grinding","status:328"),
("F17","blocks of equal size are stacked in the order of the column index","status:330"),
("F18","the pinned verifiers check one equation on the public words, the specification one per limb","status:330"),
]
other=[
("C5","Clean has no degree bound on expressions (inherited from leanISA)","status:355 (by reference)"),
("C6","Clean has no prover-chosen heights (inherited from leanISA)","status:355 (by reference)"),
("C10","Clean's `EnsembleWitness` has no generator","status:355"),
("C11","Clean's `Ensemble.Statement` assumes the non-overflow side condition","status:356"),
("E6","a Lake race on ArkLib's lint plugin at first build","status:365"),
("E7","no `LawfulBEq E` at the CompPoly pin, so no polynomial with coefficients in `E`","status:368"),
("E8","no `OracleInterface E` at the ArkLib pin","status:375"),
("E9","`decide` cannot unfold CompPoly's `X` and `*` inside a `module`","status:380"),
("E10","a phase with a nonzero error is a `noncomputable` bundle","status:383"),
("E11","a binder over `Finset.univ : Finset E` makes a linter enumerate the field","status:388"),
("E12","`simp` does not rewrite inside instance arguments of `Component.Def.red`","status:391"),
("E13","a `Decidable` instance written by `unfold` never evaluates under `#guard`","status:396"),
("E14","Mathlib's overlapping-instances linter rejects `[Zero R]` under `[CommRing R]`","status:400"),
("E15","`#guard` finds no `Decidable` instance for vectors of computed length","status:405"),
("E16","a generic module's destination is read off its objects and imports","status:407"),
("E17","being stated over any ring does not make a declaration generic","status:415"),
("E18","a `#guard` with a numeral of `E` next to an operation finds no `Decidable` instance","status:429"),
("R21","leanISA finding: the repository holds two BLAKE2s compressions","`leanisa-status.md`; cited at blueprint:216, hole comment:162"),
]
targets=[
("T1","arithmetization and ISA equivalence (both directions)","`architecture.md`:203"),
("T2","witness-generator correctness","`architecture.md`:230"),
("T4","base proof extraction and completeness (the proof system's target)","`architecture.md`:261"),
("T5","recursive-verifier correctness","`architecture.md`:277"),
("T6","recursion and correct-trace extractability (open)","`architecture.md`:284"),
]
table("Units of work (the documents' 'holes')",holes)
table("Upstream ledger entries",ledger)
table("Findings about ArkLib beyond the ledger",arkfind)
table("Findings internal to the specification",spec)
table("Findings, Rust and Python against the specification",rust)
table("Findings about Clean and the Lean environment, and the one leanISA finding cited",other)
table("Target theorems cited by the proof-system documents",targets)
