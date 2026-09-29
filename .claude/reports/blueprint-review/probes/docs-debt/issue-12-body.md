**Roadmap:** [`docs/roadmap/protocol-blueprint.md`](https://github.com/Verified-zkEVM/leanerVM/blob/main/docs/roadmap/protocol-blueprint.md) — the specification of what is wanted; changed only by pull request; never records status. Revision 2 (2026-09-24, *The spine*) is on `main`; the spine itself landed there as #58 (`5cb7da6`, 2026-09-28), revised the same day after the adversarial review [`docs/reviews/protocol-spine.md`](https://github.com/Verified-zkEVM/leanerVM/blob/main/docs/reviews/protocol-spine.md). The specifications of the holes are the [hole comment](https://github.com/Verified-zkEVM/leanerVM/issues/12#issuecomment-5833669972) below (2026-09-25; the `[Hole]` issues #45 to #57 were folded into it and closed to keep this tracker small).
**Status:** [`docs/roadmap/protocol-status.md`](https://github.com/Verified-zkEVM/leanerVM/blob/main/docs/roadmap/protocol-status.md) — where it stands; rewritten whole when a layer or hole lands.
**Target:** [leanEthereum/leanVM](https://github.com/leanEthereum/leanVM) at [`a386121f`](https://github.com/leanEthereum/leanVM/commit/a386121f84292f6fa663aaa3e570c15bc0240ea2): specification §3–§6, §8, Annexes A–C of [`doc/leanvm/`](https://github.com/leanEthereum/leanVM/tree/a386121f84292f6fa663aaa3e570c15bc0240ea2/doc/leanvm); implementation `crates/lean_vm/src/`, `crates/fiat_shamir/src/`, `crates/pcs/src/`, `crates/flock/src/`, `python-verifier/verifier.py`.
**Framework:** [Verified-zkEVM/ArkLib](https://github.com/Verified-zkEVM/ArkLib) at [`dca90385`](https://github.com/Verified-zkEVM/ArkLib/commit/dca90385fb40dd5eb8da9145da6348ed17f5cd8b).

Both documents link back here (roadmap section *How work is tracked*). This issue holds nothing that is not in them; where they disagree, the files win.

Related: #4 (leanISA: the relation `SatisfiedBy` the adaptor targets), #3 (Flock: consumed as the phase at the flock seam, hole P6; shares the WHIR of K1), #20 and #16 (Clean's balance), #23 (fixed columns). Upstream: ArkLib [#676](https://github.com/Verified-zkEVM/ArkLib/issues/676) (composition admitted), [#627](https://github.com/Verified-zkEVM/ArkLib/issues/627) (BCS design), [#4](https://github.com/Verified-zkEVM/ArkLib/issues/4) (Merkle), [#1](https://github.com/Verified-zkEVM/ArkLib/issues/1) (sumcheck; #3 there is closed), [#893](https://github.com/Verified-zkEVM/ArkLib/issues/893) (Binius/ring switching), [#900](https://github.com/Verified-zkEVM/ArkLib/issues/900) (stacking readout), [#901](https://github.com/Verified-zkEVM/ArkLib/issues/901) (multiset fingerprints).

## What this roadmap builds (revision 2)

The relation the proof system proves knowledge of is `M3Holds I input q`: a checklist on one committed column `q` (every table's columns stacked), stated over an abstract M3 instance `I` (widths, log-heights, constraint polynomials, flush tuples, count columns, boundary blocks, stack layout) that `Ensemble.toM3` derives from any Clean ensemble. The adaptor (`witnessOf`, `satisfiedBy_witnessOf`; `stackOf`, `m3Holds_stackOf`) carries knowledge of `M3Holds` to leanISA's `SatisfiedBy prog input w` at the same error, and T1 carries that to `ValidExecution`. Nothing above the adaptor imports leanISA (*the wall*), so a leanISA change touches `leanIsaInstance`, the adaptor and T1 only.

The **spine** (hole S) is on `main` (#58): `LeanerVM/Protocol/Spine/{Instance,Seams,Phase,Compose,Toy}.lean`, the ArkLib candidates `LeanerVM/Protocol/ToArkLib/{Oracles,Component,KnowledgeAppend,PassThrough,SendOracle,Refinement}.lean`, two oracle instances for scalar messages in `LeanerVM/Protocol/Field.lean`, and the tests in `tests/LeanerVMTests/Protocol/Spine.lean`. It holds: `Shape`, `Layout` (a reading law, which #18's `Blocks` inhabits for aligned blocks), `Coord`, `BoundaryBlock`, `PublicLine`, and `M3Instance` with the degree bound `d` and its proofs `constraints_degree`, `flushes_degree`; the five clauses and the decidable relation `M3Holds` with its ArkLib form `M3Rel`; the claims (`ColumnClaim`; `VirtualTerm`, a `K`-polynomial of a table's row with an `E` weight; `LinearClaim`, `Weight`, `WeightedClaim`), the phase outputs `BusOut`, `TableOut`, `PubOut`, `FlockOut`, and the six seams `Seam.commit` to `Seam.done` through `Seam.of`, `Seam.bus` bounding every term of every linear claim by `I.d`; the hole interfaces `Component.Def` / `Component.Complete` / `Component.Security` (a `Security` carries its extractor and knowledge state function), specialised to the one oracle as `Phase.*`, with their binary `append` proved in both halves, the completeness half by ArkLib's proved guarded append and the knowledge half by the port of ArkLib #615's `Append/Knowledge.lean` (`Verifier.KnowledgeStateFunction.appendGuarded`, `Verifier.append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first`: hole C1, so the spine has no assumed statement); the pass-through and the one-message send shape, each with both halves (five pass-throughs inhabit `Phases`, `Phases.Complete` and a `Phase.Security` in the tests); the commit phase (`commitDef`, `commitComplete`, `commitSecurity`, its extractor `commitExtractor` reading the stack off the message at error zero); the bundle `Phases I` with `Phases.Complete` and `Phases.Security`, `leanVmPiop`, `leanVmVerifier`, `leanVmProver`, `piopError`, the protocol's extractor `piopExtractor` (the commit phase's followed by the phases', appended through the verdicts) and the master theorems `piop_perfectCompleteness (P) (C : P.Complete)` and `piop_rbrKnowledgeSoundness (P) (S : P.Security)`, stated for `piopExtractor` (`piop_rbrKnowledgeSoundness_exists` forgets it); `Refinement` with `map_option_valid`; and the toy instance (one table of width 3 and height 2 on a stack of height 8, `d = 2`, one constraint, one push, one boundary pull, one count column, one public line) whose `M3Holds` is decided by `#guard`, each of the four checkable clauses made to fail alone. Message schedules travel with each phase's `Def`; only `commitSpec` is fixed. Two adversarial reviews by context-free agents (2026-09-25; 2026-09-28, [`docs/reviews/protocol-spine.md`](https://github.com/Verified-zkEVM/leanerVM/blob/main/docs/reviews/protocol-spine.md)) found no theorem statement wrong or vacuous; the second's five interface findings (the bus seam's degree bound, the strong Flock predicate, the named extractor, public lines instead of cells, the caps as a hypothesis of the adaptor's soundness theorem) and six compressions are applied. Every other unit consumes spine names only, tests on the toy instance, and lands in two halves (`Def` with `Complete`, then `Security`), never with `sorry`. Then WHIR, Merkle trees, the BLAKE2s chain, `verify` with `verify_iff_compiled` (unconditional) and `verify_knowledgeSound` (conditional on three named ArkLib interfaces), and T4. Pins unchanged: leanVM `a386121f`, ArkLib `dca90385`, CompPoly `3468b38c`, Clean `93c9d1ef`, Lean `v4.33.1`.

## Hole checklist

Status per hole: **open** / **claimed** (by a comment on this issue naming the declarations taken) / **in review** (the PR carrying `awaiting-review`) / **landed** (the merged PR). Each hole's specification (produces, consumes, tests, upstream watch) is a section of the [hole comment](https://github.com/Verified-zkEVM/leanerVM/issues/12#issuecomment-5833669972). Tick a hole only when its pull request has merged with `./scripts/validate.sh` green and its tests in `tests/`. A hole with two halves ticks twice.

- [x] **0 — ArkLib dependency and field instances (Layer 0).** — *landed* (#15, 2026-09-11)
- [ ] **L1 — Layer 1: generic tables and stacking, and the leaves.** Generic half in draft #18 (rebase onto `main` pending; #25, #26 merged into it); leaves in review: #40 (`stack_eval_ambient`, #36), #38 (`unstack`, `BlockClaim`, #35), #41 (`idxColumn_eval`, `bytecodeColumn_slot`, #32), #26 (coefficient transport, #27). — *in review*; nothing lands before #18 does
- [x] **S — the spine.** — *landed* (#58, `5cb7da6`, 2026-09-28; reviewed the same day, [`docs/reviews/protocol-spine.md`](https://github.com/Verified-zkEVM/leanerVM/blob/main/docs/reviews/protocol-spine.md))
- [ ] **G1 — virtual sumcheck, `Sumcheck.Def` and completeness (Layer 4).** #37; the honest round algebra and the ArkLib bridge in #42 — *claimed*
- [ ] **G2 — sumcheck round-by-round knowledge, `Sumcheck.Security` (Layer 4, ledger A1).** #37; a one-round leaf prepared, unpublished — *claimed*
- [ ] **G3 — batching by powers, `Batch.Def` and `Security` (Layer 4).** #31; the algebra and the `(J − 1)/|F|` count in #43 — *claimed*
- [ ] **G4 — fingerprint, Lemma 5.1, the collision bound (Layer 5).** #33; the fingerprint in #39 — *claimed*
- [ ] **G5, G6 — GKR: a `Component.Def` for the grand product and its two halves (Layer 5).** — *open*
- [ ] **I1 — Clean components as polynomials (Layer 2).** #28; Clean #466 approved, unmerged — *claimed*
- [ ] **I2 — the adaptor (Layer 3): `leanIsaInstance` (an `M3Instance` with `d := 2`, three public lines on `mem_0, mem_1, mem_2`, and a layout with two readers: #18's `Blocks` for the aligned blocks, a strided reader for the eighteen BLAKE2S limb slots of `q_flock`), `stackOf`, `witnessOf`, `satisfiedBy_witnessOf (hs : s.Admissible prog)`, `m3Holds_stackOf`, `witnessOf_stackOf`.** — *open; needs I1, #18, and #3's witness generator and compression lemma*
- [ ] **P1, P2 — the bus phase (Layer 6): `Phase.Def I I.Stmt (I.Stmt × BusOut I)` against `Seam.commit`, `Seam.bus`.** — *open; P1 needs G5*
- [ ] **P3, P4 — the table sumcheck phase (Layer 7): `Phase.Def I (I.Stmt × BusOut I) (I.Stmt × TableOut I)` against `Seam.bus`, `Seam.table`.** — *open; needs G1*
- [ ] **P5 — the public-input phase (Layer 8): `Phase.Def I (I.Stmt × TableOut I) (I.Stmt × PubOut I)` against `Seam.table`, `Seam.pub`, over `I.publicLines`: one challenge, one pooled column claim per line, the prover sends nothing.** — *open; the smallest phase, a good first hole*
- [ ] **P6 — the Flock phase (Layer 9): `Phase.Def I (I.Stmt × PubOut I) (I.Stmt × FlockOut I)` against `Seam.pub`, `Seam.flock`; its input predicate is the strong `aux`, Flock's R1CS on `q_flock` (decision 12), the eighteen column claims over the strided reader `limbColumns`; the inhabitant is #3's.** — *open; needs #3*
- [ ] **P7, P8 — the opening phase (Layer 10): `Phase.Def I (I.Stmt × FlockOut I) Unit` against `Seam.flock`, `Seam.done`.** — *open; needs G1, G3*
- [x] **C1 — the knowledge-soundness append (ledger A2).** — *landed* with the spine (#58): `LeanerVM/Protocol/ToArkLib/KnowledgeAppend.lean`, the port of ArkLib #615's `Append/Knowledge.lean` at `ca7a2577`, with its attribution; `Component.Security.append` and the master knowledge theorem take no assumption. The file is deleted, and its two names replaced by ArkLib's, when the pin moves past #615
- [ ] **K1 — WHIR over binary Reed–Solomon codes (Layer 11).** Shared with #3 F6 — *open*
- [ ] **K2 — Merkle trees, BLAKE2s bytes, the WHIR parameters (Layer 11).** — *open*
- [ ] **K3 — transcript, `Proof`, `verify`, `verify_iff_compiled`, the FS and BCS interfaces (Layer 12).** — *open; needs the phase `Def`s, K1, K2*
- [ ] **K4 — T4: `baseVerifier_extractsExecution`, `baseProver_complete` (Layer 13).** — *open; needs K3, I2, leanISA Layer 10*
- [x] **VCVio controls for K3 and P7.** #29, #30 — *landed upstream* (VCVio #784)

Ordering: P1, P3, P5 (`Def`s), G1 to G6, I1, K1 and K2 can start now on `main`; I2 after #18 and I1 land; P2, P4, P8 also need the `Security` of the generic component they use. K3 needs the phase `Def`s, K1 and K2. K4 last.

## Open pull requests (2026-09-28)

None touches a spine name; each is algebra a hole consumes. The status file's table says through which spine object. On rebase, `Generic/` becomes `ToArkLib/` or `ToCompPoly/` (convention *Generic code*).

| PR | Hole | Base | CI | Against the spine | Review order |
| --- | --- | --- | --- | --- | --- |
| #18 (draft) | L1 | `4b95a60` | none until rebased | `Blocks` inhabits `Layout` in the leanISA instance (I2) | land first |
| #40 | L1 | #18 | none | the bus phase's leaf decomposition (P1) | 2 |
| #38 | L1 | #18 | none | `BlockClaim` is a `ColumnClaim` through `Layout`; its pairing is the opening phase's `ColumnClaim` to `WeightedClaim` step (P7) | 3 |
| #41 | L1 | #18 | none | the `Coord.known` columns of the leanISA instance; imports `Arithmetization.Bytecode`, so it belongs below the wall with I2 | 4 |
| #43 | G3 | #18 | none | the opening phase's batching of `FlockOut` (P7, P8) | 5 |
| #39 | G4 | #18 | none | the bus forms' `VirtualTerm.poly` and P2's collision bound | 6 |
| #42 | G1 | `main` | runs | the honest prover of a sumcheck `Component.Def` (P3, P7) | independent |
| #44 | docs | `main` | runs | none | closed 2026-09-28; its content merged with the status file in #58 |

## Upstream ledger

| Ledger | ArkLib at the pin | Hole | Upstream issue / PR |
| --- | --- | --- | --- |
| A1 sumcheck single-round rbr knowledge soundness | admitted (14 sorries on `main`) | G2 | ArkLib #1; #1128, #1129; `main`'s `Sumcheck/Interaction/Soundness.lean` |
| A2 rbr knowledge-soundness append (guarded first verifier) | admitted at the pin; ported locally, `ToArkLib/KnowledgeAppend.lean` (#58) | C1, landed | ArkLib #676; ArkLib #615 (`Append/Knowledge.lean`, the port's source); the local copy goes at the pin bump |
| A3 rbr ⇒ plain knowledge soundness | admitted | K3 (corollary) | ArkLib #676 |
| A5 Fiat–Shamir and BCS security | admitted / absent | K3 | ArkLib #627; #848, #469 |
| A6 grand product, GKR, batching, stacking | absent | L1, G3, G4, G5 | ArkLib #900 (stacking), #901 (fingerprints); batching: #615's `gammaPowers`; GKR to open |
| A7 WHIR over binary RS, Merkle | absent | K1, K2 | ArkLib #4; #383, #992 adjacent |
| A8 mutual correlated agreement up to Johnson | admitted | K1 | ArkLib coding-theory track |
| A9 ring switching packing leaves | admitted | P6 | #3, ArkLib #893, #383 |
| C1 `Expression.toMvPolynomial`, `degreeBound` | absent | I1 | Clean #466 |
| C2 power-of-two heights, bus data per channel | leanISA | I2 | done (#13, #14, #17, #24) |
| C3 ℕ-counted, direction-tagged balance | absent | I2 | Clean #464, #20, Clean #452 |
| C4 fixed columns, sound prover data | absent | I2 | Clean #446, #23 |

## Upstream watch

The full table, with adoption conditions and the date last checked, is in the status file. Rows: ArkLib #615 (C1, G3), #818 (G5, pattern only), #503 (not applicable), #383 (P6, K1, S), #992 (K1, pattern), #848/#469 (K3), #1128/#1129 (G1, G2), #926 (none), #900/#901 (L1, G4), ArkLib `main`'s typed executor (G1, G2, S); Clean #466 (I1), #464 (I2), #446 (I2); VCVio #784 (done); leanth #16 (port sources). Whoever takes a hole reads its rows first; whoever bumps a pin rewrites the table.

## Frontier

- #18 must be rebased and landed before the five pull requests stacked on it can get CI or be reviewed against `main`; it is on the adaptor's path (I2), no longer the spine's.
- The spine is on `main` (#58); the holes that consume it start there, P5 first. The status file at `main` still describes the spine as on its branch and in review; the next pull request that lands a hole rewrites it whole.
- The pins have not moved. ArkLib `main` is 246 commits past the pin (finding A18: Lean 4.34, CompPoly with #331, a typed executor, the composition knowledge theorems still admitted); the bump is one planned change.
- Findings that bind a definition: F1, F3, F5, F6, F8, F11 (status file). S13 is retired (the pinned text already charges `4·2^μ/|E|`); new are S14 (the PDF `leanVM-b-2.pdf` is not the pinned text and must not be cited), E7 (no `LawfulBEq E` at the CompPoly pin, so every polynomial is over `K` and `E` sits in the weights), E8 (no `OracleInterface E` at the ArkLib pin; two instances in `Field.lean` until upstream supplies them) and E9 (`decide` cannot unfold CompPoly's `X` and `*` inside a `module`). F9 is still to be reported to leanVM.

## Decisions pending (status file, "Decisions pending")

Decision 1 was taken with #13; decision 3 (where the zerocheck is charged) with revision 2. Building the spine settled 2, 6, 7, 8, 9 and 10 by construction (`input : I.Stmt` is the statement and the instance indexes the family; the witness is the stack; every phase is over an abstract `M3Instance`; `M3Holds` has five clauses and the caps are not one; balance is `List.Perm`; worst-case round-by-round knowledge per component), plus two more: seams carry claims only, and schedules travel with the `Def`s. The review of 2026-09-28 settled four more, applied before merge: 11 (extractor discipline: every extractor a computable definition, the protocol's being `piopExtractor`), 12 (the Flock predicate is the strong one, Flock's R1CS on `q_flock`), 13 (public lines, not cells: `PublicLine`), 14 (the degree bound belongs to the instance: `M3Instance.d`, imposed by `Seam.bus`). Each is reversible by a pull request to the spine. Still open, in the status file: 4 (generic code location; default the `To*` folders), 5 (an end-to-end `#guard` of the honest prover).

## How to work on this

- **Take a hole:** comment on this issue naming the hole and the exact declarations taken; the line above moves to *claimed*. No `[Hole]` or `[Intention]` issue is needed; open one (`[Intention]: protocol - <hole>: …`) only when a slice needs its own discussion thread, and close it with the pull request. A hole's `Def` with its `Complete`, and its `Security`, are separate pull requests.
- **Report a problem with the roadmap:** open `[Roadmap]: protocol - …` naming the hole and the acceptance test, ledger entry or convention it touches.
- **Change the roadmap:** open a pull request that edits `docs/roadmap/protocol-blueprint.md`, titled `docs(protocol): …`, and reference #12. A pull request that lands a hole rewrites `docs/roadmap/protocol-status.md` whole and ticks the hole above with the PR link. A decision taken on a pending item is written into the roadmap and removed from the status file and from this issue.
- **Per PR:** statement reviewed independently of proof; every hypothesis in the signature; assumed interfaces are structures naming their upstream witness obligation; an inhabitant and a negative control under `tests/`, on the toy instance (`LeanerVM.Protocol.Toy.toy`) for a phase; Category A written from the specification first; Category B cites section, file, lines, pin; helpers `private`; generic code under `LeanerVM/Protocol/ToArkLib/` (or `ToCompPoly/`, `ToVCVio/`), the library it is a candidate for; no `sorry`/`admit`/`axiom`/`unsafe`/`native_decide`; no dependency on an ArkLib theorem admitted at the pin (`#print axioms`); spine names only above the adaptor, never `LeanerVM.Arithmetization`; label `awaiting-review` when done, `awaiting-author` after a review.


