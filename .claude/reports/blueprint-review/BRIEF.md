# Shared brief: review of the blueprint of the leanVM proof system in leanerVM

Every sub-agent of this review reads this file first, in full. Your own task is in the message
that sent you here. This brief gives the context, the rules that bind you, where things are, and
the form your output must take.

## 1. What the review is

leanerVM (`/home/scaraven/Documents/Verified-zkEVM/leanerVM`, a Lean 4 project) formalizes leanVM,
a minimal zkVM with its own instruction set (leanISA), aimed at Ethereum L1 use. This review
covers one part: the **proof system**, and specifically its **blueprint**
(`docs/roadmap/protocol-blueprint.md`) together with the code already built from it. Three
criteria, in priority order:

1. **Faithfulness** to leanVM at the pinned revision `a386121f` (specification tex, Rust code and
   Python verifier, all at that pin).
2. **Non-vacuity**: definitions and theorem statements say what their names claim, are inhabited
   by the intended objects and refuted by the near misses.
3. **Auditability**: the amount a human auditor must read and trust (the trusted code base) is as
   small as it can be.

The final output of the whole review is a LaTeX report written by the orchestrator. Your output
is a **dossier** (a Markdown file) the orchestrator will rely on. The stakes are high (a
deployment on Ethereum L1): quality and precision come before speed or token economy.

The review is **adversarial**. Do not trust that the blueprint is faithful to leanVM, that a
definition says what its name or docstring claims, or that an earlier review (under
`docs/reviews/`) was right. One earlier review's "resolution" wrote an unfaithful shortcut into
the blueprint. A statement that typechecks and a proof that compiles are evidence of neither
faithfulness nor non-vacuity.

## 2. Rules that bind you (hard limits of this session)

- **No edit to any tracked file** of any repository: not the blueprint, not the status, not Lean
  sources, not scripts, nothing. You write only under
  `/home/scaraven/Documents/Verified-zkEVM/leanerVM/.claude/reports/blueprint-review/`
  (git-ignored).
- **Nothing is posted** to any issue tracker, in leanerVM or upstream: no new issue, no comment,
  no edit, no pull request, no push. Reading with `gh` (view, list, api GET) is fine.
- **No local checkout is moved**: no `git pull`, `git checkout`, `git reset`, `git switch`,
  `git stash`, `git rebase`, `git merge` in any existing checkout. `git fetch origin` (which
  moves no working tree) is allowed in the sibling checkouts, to read `origin/main` with
  `git show origin/main:<path>`, `git log origin/main`, `git diff <pin>..origin/main -- <path>`.
  Do not run `lake update`. Do not run `lake build` (the orchestrator has built `main`; see §5).
- **No commit** anywhere. (At the owner's request the leanerVM checkout now sits on the branch
  `docs/protocol-blueprint-review`, created from `main` at `b435631`. Its tracked source files
  are exactly those of `main`; "leanerVM `main` at `b435631`" in this brief and in your dossier
  still names the code under review. Only the orchestrator commits the review's artefacts to
  that branch, so `HEAD` may later be a commit whose parent is `b435631` and which differs from
  it only under `.claude/reports/`. Do not switch branches.)
- Lean probes and small models are welcome and must build, but they are scratch work: put them
  under `.claude/reports/blueprint-review/probes/<your-task-name>/`, and reproduce in your
  dossier every probe a conclusion rests on (full source and the command that ran it, with its
  output).
- If you spawn nothing, fine; if your tools let you spawn sub-agents, they are bound by the same
  rules and you must tell them so.

## 3. Where things are

### The object of the review (leanerVM, `main` at `b435631`)

Working directory: `/home/scaraven/Documents/Verified-zkEVM/leanerVM`.

- `docs/roadmap/protocol-blueprint.md`: **the blueprint** (titles itself "Roadmap"; 1549 lines).
- `docs/roadmap/protocol-status.md`: **the status** (622 lines). Known to be stale: it heads
  itself as a snapshot of `f4d858c` and calls the public-input phase a draft pull request.
- Issue #12 of `Verified-zkEVM/leanerVM` with its long "hole comment"
  (`issues/12#issuecomment-5833669972`): **the tracker**.
- `docs/architecture.md` (the eight target theorems T1 to T8; the proof system's is T4, base
  proof extraction and completeness), `docs/leanvm-target.md` (the pin, known discrepancies),
  `docs/reviews/*.md` (earlier review handoffs), `docs/roadmap/leanth-reuse.md`,
  `docs/roadmap/leanisa-blueprint.md` and `leanisa-status.md` (the arithmetization's roadmap,
  which owns the relation `SatisfiedBy` the proof system must deliver).
- Lean sources of the proof system: `LeanerVM/Protocol/` (4413 lines):
  `Basic`, `Field` (Layer 0), `Spine/{Instance,Seams,Phase,Compose,Toy}` (the spine),
  `ToArkLib/{Oracles,Component,KnowledgeAppend,PassThrough,SendOracle,Refinement,GuardedVerdict,KeepOracles}`,
  `ToCompPoly/{Multilinear,BitProductTable,Stacking,AmbientStacking}`,
  `ToVCVio/UniformSample`, `Stack`, `Padding`, `ClaimWeights`, `BlockClaims`, `FixedColumns`
  (Layer 1), `PublicInput` (the public-input phase). Tests: `tests/LeanerVMTests/Protocol/`.
- The arithmetization and semantics (outside the review, but the boundary is inside it):
  `LeanerVM/Arithmetization/`, `LeanerVM/Semantics/`, `LeanerVM/Parameters/`.
- **Exclude from every search** the directory `.claude/worktrees/` (a merged branch's worktree;
  it is not a reference) and `.lake/build/`.

### The ground truth (leanVM at the pin `a386121f`)

`/home/scaraven/Documents/leanEthereum/leanVM`, checked out at the pin. It must stay there.

- Specification: the tex under `doc/leanvm/body/` (`03-proving-primitives.tex`,
  `04-committing-the-witness.tex`, `05-arithmetization.tex`, `06-bus-interactions.tex`,
  `07-instruction-tables.tex`, `08-end-to-end-protocol.tex`, `a-ring-switching.tex`,
  `b-polynomial-commitment-scheme.tex`, `c-flock-protocol.tex`; macros in
  `doc/leanvm/preamble/macros.tex`). Cite it as file and line.
- Rust: `crates/lean_vm/src/` (notably `cpu/mod.rs`, `gkr.rs`, `leaf.rs`, `cpu/layout.rs`,
  `witness.rs`, `constraints.rs`, `stack_open.rs`, `pcs.rs`), `crates/fiat_shamir/src/`,
  `crates/pcs/src/`, `crates/flock/src/`, `crates/primitives/src/`.
- Python verifier: `python-verifier/verifier.py`.
- `/home/scaraven/Documents/leanEthereum/leanVM-b-2.pdf` was built from an **earlier** revision
  and differs from the pinned tex. Use it for orientation at most; **never cite it**.
- Where the specification, the Rust and the Python disagree with each other, that is a finding
  in its own right: record it and say which one the blueprint follows.

### The dependencies: two revisions each, never to be confused

| Library | Pin (what leanerVM builds against) | Pinned sources | Sibling checkout (NOT at the pin) |
| --- | --- | --- | --- |
| ArkLib | `dca90385` | `.lake/packages/Arklib/` | `../ArkLib` (on `main`, `9c2f3379`) |
| CompPoly | `3468b38c` | `.lake/packages/CompPoly/` | `../CompPoly` (on a working branch) |
| Clean | `93c9d1ef` | `.lake/packages/Clean/` | `../clean` (at `93c9d1ef`, dirty `.gitignore`) |
| VCVio | `f9dc47d9` | `.lake/packages/VCVio/` | none |
| Mathlib | `v4.33.1` (`0df444a3`) | `.lake/packages/mathlib/` | none |

(`..` is `/home/scaraven/Documents/Verified-zkEVM/`.) Every claim about what leanerVM proves,
assumes or is faithful to is made **against the pin** (read `.lake/packages/`). Upstream `main`
is read only to learn what has landed or is planned since the pin (read `origin/main` of the
sibling checkout after a `git fetch origin`, or use `gh`). Say which revision every statement
about a library is about.

The private repository `../leanth` holds an earlier formalization; it is background only.

## 4. Vocabulary (use these words, and only these)

- **blueprint**: `docs/roadmap/protocol-blueprint.md`. **status**: `protocol-status.md`.
  **tracker**: issue #12 with its hole comment.
- **spine**: the blueprint's section "The spine" and its code (`LeanerVM/Protocol/Spine/`, generic
  parts under `ToArkLib/`): the abstract instance `M3Instance`, the relation `M3Holds`, the seam
  relations `Seam.*`, the interfaces a phase must meet (`Phase.Def`, `Phase.Complete`,
  `Phase.Security`), the bundle `Phases`, and the composition with the two master theorems.
- **phase**: one step of the oracle protocol: commit, bus, table sumcheck, public input, Flock,
  opening. **hole**: a unit of work the spine leaves open. **layer**: the blueprint's numbering
  of the same work (Layers 0 to 13).
- **master theorems**: `piop_perfectCompleteness` and `piop_rbrKnowledgeSoundness`, with the
  not-yet-proved theorems built on them: `verify_knowledgeSound`,
  `baseVerifier_extractsExecution`, `baseProver_complete`.
- **pin**: the revision recorded in `upstreams.json`.
- **Letter codes.** The documents label things with a letter and a number (`P5`, `A2`, `F17`,
  `C1`). They collide and are hard to read. **In your dossier, name things in words**
  ("the public-input phase", "the knowledge-soundness composition that ArkLib admits") and give
  a code only in parentheses after the name, where it helps to find the thing in the repository.
  Never write a bare code. Your own findings get a short descriptive name, not a code.

## 5. Lean probes: how to run them

- The orchestrator has run `lake build LeanerVM LeanerVMTests` on `main`; the log is
  `.claude/reports/blueprint-review/logs/lake-build-main.log` and ends with a line `exit=0` on
  success. If that line is not there yet, the build is still running: wait for it before your
  first probe (check every minute or so).
- Run a probe from the repository root with
  `lake env lean .claude/reports/blueprint-review/probes/<your-task-name>/<File>.lean`.
  A probe file is a plain Lean file (no `module` keyword) that `import`s what it needs
  (for example `import LeanerVM.Protocol.Spine.Compose`). Plain files see only what `module`
  files expose publicly; private declarations are out of reach, which is itself information.
- The machine has 15 GB of memory and a dozen agents share it. **Every Lean process runs under
  the shared lock**, so that only one runs at a time across all agents:
  `flock .claude/reports/blueprint-review/logs/lean.lock lake env lean <file>`
  (the build on `main` has finished with `exit=0`, so no waiting is needed for it). Give the
  command a generous timeout (up to 10 minutes): it may wait for another agent's probe. Do not
  judge a run through a pipe that hides the exit status (exit 137 is an out-of-memory kill: wait
  a minute and retry). Importing ArkLib or Mathlib costs a few GB and a minute or so.
- For the same reason **do not use the `lean-lsp` tools that elaborate files** (`lean_goal`,
  `lean_diagnostic_messages`, `lean_run_code`, `lean_build`, `lean_verify`, `lean_multi_attempt`,
  `lean_hover_info`, `lean_file_outline`, …): they start Lean servers outside the lock. The
  remote search tools (`lean_leansearch`, `lean_loogle`, `lean_leanfinder`) are fine. Read
  sources with the file tools and `grep`.
- `#print axioms <name>` shows what a theorem depends on (`sorryAx` means an admitted proof).
  `#guard`, `example : … := by decide`, `#check`, `#print` are the usual probe tools. A probe
  that is *expected to fail* (to show where a proof stops when a check is removed) is reported
  with its error message.
- Lean pitfalls recorded for this repository: `E` (the field `GF(2^192)`) and `K` (`GF(2^64)`)
  arithmetic is computable but slow in the kernel (prefer `#guard`/`decide +kernel` on tiny
  instances); `deriving DecidableEq` on structures holding `K`/`E` is a hazard; a `#guard` on
  vectors of computed length should compare `.toList`; name `E`-values as `def`s before a
  `Prop`-valued `#guard`.

- **The machine is severely memory limited** (WSL on a 16 GiB host). No build of any kind. Keep
  Lean probes few and small: a probe is worth running when a conclusion rests on it, not to
  decorate one. Prefer reading the source to elaborating it.

## 6. The form of your dossier

**Write the dossier incrementally.** Create the file early and save each section as soon as it
is done. A usage limit interrupted the first wave of this review an hour in; the agents that had
written nothing to their dossier lost their conclusions.

Write one Markdown file at the path your task names, under
`.claude/reports/blueprint-review/dossiers/`. It is read by the orchestrator, who has read the
blueprint and the spine but not your sources, and who will turn it into LaTeX. So:

1. **Start with a summary** (at most one page): what you examined, the conclusions, and the
   findings by severity.
2. **Evidence for everything.** A claim about leanVM cites the pinned source as
   `path:line` (or `path:line-line`) with a short verbatim quotation. A claim about Lean quotes
   the declaration **copied from the source file at the revision reviewed, never retyped from
   memory**, with its file path and line. A claim about a library says which revision.
3. **Findings.** Each finding has: a descriptive name; a severity (`critical`: a theorem or
   definition is wrong, vacuous or unfaithful in a way that would let an unsound verifier be
   "proved"; `major`: the blueprint specifies something leanVM does not do, or omits something
   it does, or a statement cannot be proved or stated as written; `minor`: imprecision, stale
   text, avoidable audit surface; `note`: worth recording); the evidence; a classification for
   divergences from leanVM (**an error of the blueprint**, to be fixed / **a deliberate
   deviation**, to be kept with its reason and the theorem it then owes / **a deviation forced
   by an upstream library**, with its workaround and the condition under which it is retired);
   and a proposed change precise enough to apply (the passage as it stands, the passage as
   proposed, the reason).
4. **Negative results count.** Where you found no issue, say exactly what you checked and how,
   so that the absence of a finding is itself evidence. Do not pad: "checked X against Y at
   lines …, they agree" is enough.
5. **Separate fact from inference.** Mark anything you could not verify as unverified, and say
   what would verify it.
6. **Introduce every library object from scratch.** The readers are world-class cryptographers
   and zkVM engineers who may not know Lean, and formal-verification experts who may not know
   zkVMs. Before using an ArkLib, VCVio, CompPoly, Clean or Mathlib object, say in a sentence or
   two what it is and what it is for, then show its Lean snippet.
7. Be complete and concise: no filler, no restating of this brief.

Your final message back to the orchestrator is a short report: the path of the dossier, the
five or so most important conclusions, anything you could not do, and anything that contradicts
this brief. The dossier, not the message, carries the detail.

## 7. Facts already established (verify before relying on them; contradict them if wrong)

- The oracle protocol in the spine is `commit ⟫ bus ⟫ table ⟫ pub ⟫ flock ⟫ opening`, over one
  committed oracle, the stack `q : Column μ` (a table of `2^μ` values in `K`), whose oracle
  interface answers evaluation queries at points of `E^μ` (`LeanerVM/Protocol/Field.lean`).
- The master theorems are stated over an abstract `I : M3Instance` and are **conditional** on a
  bundle of phases with their proofs (`Phases.Complete`, `Phases.Security`). Only the commit
  phase and the public-input phase are built. The adaptor to leanISA (`leanIsaInstance`,
  `stackOf`, `witnessOf`, `satisfiedBy_witnessOf`, `m3Holds_stackOf`), the other four phases,
  the generic sumcheck and GKR components, WHIR, Merkle trees, Fiat–Shamir and the executable
  `verify` are specified in the blueprint and not built.
- The pinned specification's §8.5 (`08-end-to-end-protocol.tex:94-101`) says of the opening:
  "This one opening discharges every pooled claim; there is no separate reduction sumcheck",
  while the blueprint's Layer 10 gives the opening phase the schedule "`V_to_P : E` ; sumcheck
  (`W_λ · q`) rounds ; the final evaluation query". Whether this is a divergence, and of which
  kind, is one of the questions of the review.
- The blueprint's per-layer sketches (Layers 6, 7, 9, 10) give statement types and master-theorem
  signatures that differ from the spine's as built (for example two different `BusOut`, and
  `piop_rbrKnowledgeSoundness` stated with `Set.univ` and `rbrKnowledgeSoundness` in Layer 10 but
  with `Seam.done I` and `rbrKnowledgeSoundnessWorstCaseWith` in the spine).
- The public-input phase follows the specification's per-limb check; the pinned Rust and Python
  verifiers check one combined equation on the two public words and accept strictly more
  transcripts.
- Clean's bus balance argument is vacuous over `K` (characteristic 2; leanerVM issues #16, #20);
  leanISA states balance with its own definition (`BalancedPair`, counted in ℕ) until Clean
  changes.

## 8. Change of the ground under the review (2026-09-30)

The owner merged the new `main` into the review branch mid-review. Read this before anything
else.

- `main` is now `144c5aa` ("chore(deps): upgrade to Lean 4.34.1 (#61)", merged 2026-09-29
  22:31 UTC), and the checkout (`docs/protocol-blueprint-review`, now `8d3ea7d`) contains it.
  **The review's object stays `main` at `b435631`** for everything already written; the report
  states both revisions and assesses what the upgrade changes. The leanVM pin is unchanged
  (`a386121f`), so every ground-truth fact stands.
- **The pins moved**: ArkLib `dca90385` → `7653a901` (the commit several dossiers already
  examined as "upstream `main`"), CompPoly `3468b38c` → `572f9973`, Clean `93c9d1ef` →
  `42fe4b26` (Clean PR #474 over its `main`), VCVio `f9dc47d9` → `a4232d08` (VCVio PR #820),
  Mathlib `v4.34.1`, Lean `v4.34.1`. `.lake/packages/` now holds the NEW pins. To read a file
  at an OLD pin use `git -C .lake/packages/<pkg> show <old-commit>:<path>` (the old commits
  are in each package's object store; verified for all four). Say, for every library citation,
  which revision it is about.
- **The proof-system sources changed only in proofs and imports** between `b435631` and
  `144c5aa` (`git diff b435631 144c5aa -- LeanerVM/Protocol`: 77 lines in, 76 out; for
  example `if_pos` → `ite_eq_left`, `probEvent_mono` → `prEvent_mono`, the import
  `CompPoly.Multivariate.CMvPolynomial` → `CompPoly.Multivariate.Basic`). Cite Lean line
  numbers **at `b435631`** (`git show b435631:<path>`) unless you say otherwise; the two
  probability bridges (`ToArkLib/GuardedVerdict.lean`, `ToVCVio/UniformSample.lean`) were
  restated on VCVio's new probability API (`Pr{let x ← c}[P x]`) with, per the pull request,
  the same relations and bounds: a claim about their statements must name the revision.
- **CompPoly's `K` changed meaning for numerals**: `BF64` is now a structure wrapping
  `BitVec 64` and natural-number casts have their characteristic-two meaning, `(2 : K) = 0`;
  encoded words are `K.ofBits n`. Any probe or fixture written with numerals other than `0`
  and `1` in `K` means something else at the new pin.
- **Lean probes cannot run in this checkout until it is rebuilt** (`lake env lean` fails with
  "incompatible header"). Do not run Lean. Rely on the probe outputs already recorded; where a
  conclusion needed a probe that has not run, say so and mark it unverified. The owner decides
  whether the new `main` is built locally (the machine is memory limited) or whether the
  remaining probes are deferred.
- The blueprint changed in its pins table only (6 lines); the status file did not change.
  `docs/dependencies.md` was rewritten for the upgrade and describes the port
  (`git show 144c5aa:docs/dependencies.md`).
- **The leanVM checkout has moved too** (found 2026-09-30 by the boundary agent, confirmed by the
  orchestrator): `/home/scaraven/Documents/leanEthereum/leanVM` is no longer at `a386121f`; its
  HEAD is `248da071` and the crate tree changed (`crates/leanvm`, `leanvm_core`; no
  `crates/lean_vm`). The pin `a386121f` is an ancestor of HEAD, so **every leanVM citation must
  now be read with `git -C /home/scaraven/Documents/leanEthereum/leanVM show a386121f:<path>`**
  (old paths, for example `crates/lean_vm/src/cpu/mod.rs`, `python-verifier/verifier.py`,
  `doc/leanvm/body/08-end-to-end-protocol.tex`). Do not read the working tree for the pin, and
  do not move the checkout. The review's ground truth stays `a386121f`.
