# Data of the register (task `register`). Rendered by render.py into dossiers/register.md.
# Each finding row: F(sev, rank, subj, name, where, cls, claim, evid, change, status, note)
#   sev   : severity as displayed (copied from the dossiers; merged rows show each dossier's)
#   rank  : 0 critical, 1 major, 2 minor, 3 note (a position row takes the rank of the row it disputes)
#   subj  : key of SUBJECTS below
# Negative results: N(dossier, what, how, caveat). Not verified: U(dossier, claim, status, verify).

SUBJECTS = [
    ("seams", "relation and seams"),
    ("error", "master theorems and error"),
    ("setup", "phase: setup"),
    ("commit", "phase: commit"),
    ("bus", "phase: bus"),
    ("table", "phase: table sumcheck"),
    ("pub", "phase: public input"),
    ("flock", "phase: Flock and ring switching"),
    ("opening", "phase: opening and compilation"),
    ("adaptor", "adaptor and leanISA boundary"),
    ("libs", "libraries"),
    ("layer1", "Layer 1"),
    ("docs", "documentation"),
]

FINDINGS = []
NEG = []
UNV = []


def F(sev, rank, subj, name, where, cls, claim, evid, change, status, note=""):
    FINDINGS.append(dict(sev=sev, rank=rank, subj=subj, name=name, where=where, cls=cls,
                         claim=claim, evid=evid, change=change, status=status, note=note))


def N(dossier, what, how, caveat=""):
    NEG.append(dict(dossier=dossier, what=what, how=how, caveat=caveat))


def U(dossier, claim, status, verify):
    UNV.append(dict(dossier=dossier, claim=claim, status=status, verify=verify))


# ============================================================ CRITICAL

F("critical (as a warning about ArkLib's definition; not a defect of a leanerVM theorem)", 0, "error",
  "The existential forms of round-by-round knowledge soundness carry no knowledge content",
  "lib-arklib.md §G.1; §D.4, §D.6",
  "a deviation forced by an upstream library (ArkLib has no notion of running time)",
  "ArkLib's round-by-round extractor is any function, so an extractor that picks a witness by classical choice makes the verifier deciding any relation's language knowledge sound at error 0. Theorems in the existential forms (`piop_rbrKnowledgeSoundness_exists`, the sketches of Layers 9 and 10) are soundness statements only; the spine's named form is adequate only with a compiled extractor.",
  "ArkLib `Security/RoundByRound.lean:77-86, 118-123` at `dca90385`; probe `Extractors` (`chooser_sound`, exit 0, old pin)",
  "state every interface in the named (`With`) form with a compiled extractor checked by a `def` without `noncomputable`; change `:239`, `:1084`, `:1333` (lib-arklib.md §G.1)",
  "probe-run (old pin)",
  "Related: [[computable]] (literature)."),

# ============================================================ MAJOR

# --- relation and seams
F("major (gt-table-pub, code-spine)", 1, "seams",
  "The bus seam admits statements the deployed table sumcheck cannot serve",
  "gt-table-pub.md §8 (first finding), §6 E.1; code-spine.md §F \"The degree conjunct of Seam.bus\", §C.3",
  "an error of the blueprint",
  "`Seam.bus` accepts any number of linear claims, terms of one table at unrelated points, terms on any table, and a degree bound written as a clause on the statement. Round-by-round knowledge soundness quantifies over every input statement, so the deployed table-sumcheck verifier cannot be proved complete and sound against it without guards (degree, claim count, one point per table) that leanVM does not have; over the seam the error on `ξ` is unbounded.",
  "`Spine/Seams.lean:130-134, 175-181` at `b435631`; probes `SeamBusShape.lean`, `SeamBusMember.lean` (exit 0 per the dossier)",
  "give `BusOut` the shape of the Rust's `BusVerify` (`leaf.rs:849-860`): one point, forms per side and sumcheck table with the degree in the type, three totals, column claims; smallest fix: make `VirtualTerm.poly` a subtype within the degree bound (gt-table-pub.md §8; code-spine.md §F)",
  "cited-checked; probe-run",
  "DISAGREEMENT with [[buspos]]: gt-bus holds that the surplus generality costs nothing that matters. code-spine endorses gt-table-pub's redesign."),
F("— (a position of gt-bus, not a finding; placed beside the row it disputes)", 1, "seams",
  "The real bus phase can fill the spine's bus slot; the seam's surplus generality burdens only the table phase",
  "gt-bus.md Summary item 2, §E.1, §E.2, §E.4",
  "—",
  "The deployed bus phase's output is expressible as a `BusOut I` (five linear and five column claims for leanVM), it is perfectly complete (given the side conditions of [[sideconds]]), and a knowledge state function exists. `Seam.bus` admits statements the bus phase never emits, but gt-bus calls that \"a burden on the table phase's completeness\", met by \"a table phase written over the terms' own points\", and finds nothing required by the spine that matters.",
  "gt-bus.md §E.1-E.4 (paper)",
  "none proposed beyond the side conditions and the order of the linear claims",
  "cited-checked; paper",
  "DISAGREEMENT with [[busseam]]: gt-table-pub and code-spine hold that the table phase which meets the seam must run checks leanVM does not run, so it is not the deployed verifier."),
F("major", 1, "seams",
  "The spine's completeness cannot carry an error, and Flock may need one",
  "lib-arklib.md §G.2; §E.3",
  "an error of the blueprint, conditional: \"if the honest Flock prover fails at `r_eq = 1` … otherwise a note\"",
  "`Component.Complete` is perfect completeness, while ArkLib composes completeness with additive errors (proved at both pins); acceptance test 20 charges the Flock prover's failure at `r_eq = 1` to `flockError`, a soundness error.",
  "`ToArkLib/Component.lean:84-85`; blueprint `:1083`, `:1323-1325`; `crates/flock/src/zerocheck.rs:117`; ArkLib `GuardedCompleteness.lean:161-173`",
  "add `err` to `Component.Complete`, compose by `append_completeness_of_guarded_verifiers`, state `piop_completeness` with the sum and `piop_perfectCompleteness` as its corollary (lib-arklib.md §G.2)",
  "paper",
  "DISAGREEMENT with [[test20]] (gt-flock-ring): there the specification's Flock is perfectly complete, only the Rust prover fails, so a Lean honest prover sending the true coefficients needs no completeness error. lib-arklib's own condition is answered by gt-flock-ring §4 and §8.12. The check of gt-flock-ring adds that ArkLib's completeness composition has side hypotheses (`hSeam`, completeness from every shared state)."),

# --- master theorems and the error
F("major", 1, "error",
  "The declared error is unconstrained: the knowledge theorem has content only with a bound on `piopError`",
  "code-spine.md §F \"The declared error is unconstrained\"; §C.5, §D.3 (b)",
  "an error of the blueprint (an omission the spine inherited)",
  "`piopError` is whatever each phase declares; five phases that draw a challenge, check nothing and declare error 1 inhabit `Phases.Security` for the toy, and both master theorems hold of them. The blueprint's only bound, `piopError_le`, takes an argument (`s`) that the spine's `piopError` does not.",
  "`Spine/Compose.lean:149`; `ToArkLib/Component.lean:66, 148`; blueprint `:318`, `:1130`; probe `P4Junk.lean` (`piopError_junk`, old pins)",
  "the spine fixes each phase's error as a function `piopError I` of the instance's sizes and demands each phase's bound at it (recommended), or a bound field in `Phases.Security` (code-spine.md §F)",
  "probe-run",
  "lib-arklib §D.4 reaches the same conclusion (\"the error term is what carries content; `piopError_le` is the load-bearing companion\", probe `NonVacuity`)."),

# --- setup
F("major", 1, "setup",
  "The composition over the prover's announced sizes is unspecified",
  "boundary-adaptor.md §G.6; §B.3",
  "an error of the blueprint (a missing decision)",
  "The sizes are the prover's and admissibility is the verifier's check, but the per-instance theorems bound one size vector each, `verify_iff_compiled` quantifies `∃ s`, and ArkLib's fixed `ProtocolSpec` cannot express a schedule that depends on a first message. A union over the admissible sizes costs about `2^34`; the `Q · max ε` Fiat–Shamir bound needs the sizes inside the hashed statement of one protocol.",
  "blueprint `:316`, `:1218-1221`, `:1226-1227`, `:1326-1328`; `cpu/mod.rs:130-178`; `verifier.py:1372-1379`",
  "state the non-interactive theorem for the family (`niError Q` the maximum, or the sum, over admissible sizes) and `FiatShamirSecurity` in family form with the sizes in the challenge oracle's input (boundary-adaptor.md §G.6)",
  "paper; unverified (the count `2^34` is a hand estimate)",
  "gt-bus §C (its row on the announced sizes) records the deliberate deviation this rests on and the uniform bound it owes."),

# --- bus
F("major", 1, "bus",
  "The GKR layer sumcheck is the normalized variant; the blueprint gives it the wrong degree, the wrong error and no definition",
  "gt-bus.md G1",
  "an error of the blueprint",
  "Each deployed GKR round sends a degree-4 cofactor (four elements on the wire, the constant coefficient derived through the equality factor); the running claim is the cofactor's value and the layer's final check has no equality factor. The blueprint says degree 5 and error `5/|E|`, and Layer 4 defines only the plain variant, so a verifier built as written rejects every Rust proof or is a different verifier.",
  "`gkr.rs:399-404, 410-413`; `fiat_shamir/src/transcript.rs:297-302`; `verifier.py:411-413, 445, 449`; blueprint `:321`, `:898-901`, `:941-942`; Python probe H.1 (honest prover accepted by the pinned Python verifier; re-run by the check)",
  "define both sumcheck variants in Layer 4 by name; `4/|E|` per GKR round in `gkrError` and the tracker (gt-bus.md G1)",
  "cited-checked; probe-run (Python)",
  "DISAGREEMENT with [[gkrpos]] on the GKR round error (4 against 5). The check corrected G1's wording on the table sumcheck: \"three of the cubic's four coefficients are sent\", not \"the whole cubic\" (verify-gt-bus.md §4 item 1)."),
F("— (a premise of gt-table-pub, not a finding; placed beside the row it disputes)", 1, "bus",
  "The GKR last-layer rounds cost `5/|E|` each, as the blueprint says",
  "gt-table-pub.md §5 D.3 (\"On the rounds of the last layer `ε_G = 5/|E|`\"); verify-gt-table-pub.md §4 item 5",
  "—",
  "gt-table-pub's argument that the zerocheck escape adds nothing uses `ε_G = 5/|E|` per round of the last GKR layer; its check reads `next_round_poly(5, claim, Some(equality_point))` as five coefficients of a degree-4 cofactor with the equality factor applied by the verifier, \"so the full round polynomial has degree 5, consistent with the dossier's `5/|E|` and with the blueprint's row GKR\".",
  "`gkr.rs:399-401`",
  "—",
  "cited-checked; paper",
  "DISAGREEMENT with [[gkrnorm]]: gt-bus reads the check as made on the cofactor (normalized sumcheck), so the error is `4/|E|` and the blueprint's `5/|E|` is not tight. Both are upper bounds; neither dossier's conclusion on the zerocheck changes (the escape is a maximum with `ε_G ≥ 1/|E|` either way). Both agree on the combination challenges (`1/|E|` each) and on a zero error for the unused last combiner only in gt-bus."),
F("major (by the brief's definition; the fix is one sentence)", 1, "bus",
  "One combiner more than GKR layers: the last is drawn and never used",
  "gt-bus.md G2",
  "an error of the blueprint",
  "Both verifiers draw a combiner after the roots and after every layer, the last included; the blueprint says one per layer. Harmless in the oracle model, but after Fiat–Shamir the extra squeeze changes every later challenge.",
  "`gkr.rs:369, 391, 423`; `verifier.py:435, 453`; blueprint `:321`, `:940-941`; Python probe H.1 (`μ²/4 + μ + 1` challenges for even `μ`)",
  "\"a combiner after the roots and after every layer, the last included, error 0\"; add the count to acceptance test 17 (gt-bus.md G2)",
  "cited-checked; probe-run (Python)"),
F("major", 1, "bus",
  "Layer 5's generic GKR cannot be appended in the bus phase and cannot carry the zerocheck clause",
  "gt-bus.md G3",
  "an error of the blueprint; the first half also a deviation forced by an upstream library",
  "The GKR's oracles are the leaf tables, but a phase's one oracle is the stack; carrying the GKR along that map needs ArkLib's context lifting, whose completeness and knowledge soundness are admitted at the pin. And the appended state function cannot carry a clause (the zerocheck) that changes with the GKR's own challenges.",
  "blueprint `:262`, `:606`, `:930-937`; `Spine/Phase.lean:37-38`; `ToArkLib/Component.lean:143-149`; ArkLib `LiftContext/Reduction.lean:355-365, 542-560` (`sorry`, `dca90385`)",
  "restate Layer 5's GKR over a context with `leaves` and `riders`; the bus phase is `[(α, β); roots] ⟫ gkr ⟫ [boundary evaluations]` (gt-bus.md G3)",
  "cited-checked; paper",
  "The check corrected an attribution: `appendGuarded` is leanerVM's (`ToArkLib/KnowledgeAppend.lean:474`, a port of ArkLib #615), not ArkLib's at `dca90385`; the substance holds."),

# --- table sumcheck
F("major (gt-table-pub, boundary-adaptor); note (gt-bus)", 1, "table",
  "The table sumcheck's tables are not distinguished from the instance's other tables",
  "gt-table-pub.md §8 (second finding), §4 C.1 item 4; boundary-adaptor.md §G.9, §E.4; gt-bus.md G16",
  "an error of the blueprint (an omission; boundary-adaptor: a consequence of the modelling choice, unstated)",
  "Layer 3 makes the six shared columns tables of the instance, and Layer 7 takes `τ_max` and the final message's width over every table: at least 16 rounds and 110 values, where leanVM runs `τ_max` rounds over the six opcode tables (as few as 3) and sends 104 values; `verify_iff_compiled` would then fail.",
  "blueprint `:836-839`, `:987-989`; `constraints.rs:250`; `verifier.py:607`; `cpu/mod.rs:344-351`; `08-end-to-end-protocol.tex:76-77`",
  "a decidable criterion (`I.SumcheckTable` in gt-table-pub, `M3Instance.active` in boundary-adaptor: a constraint, a flush or a count column) and Layer 7 ranges over it; a test with a taller table without constraints (gt-table-pub.md §8; boundary-adaptor.md §G.9)",
  "cited-checked (gt-table-pub, gt-bus parts); unverified (a reading of Layer 3's text: `leanIsaInstance` is not built)",
  "Three dossiers."),

# --- public input
F("major (gt-table-pub, code-pubinput)", 1, "pub",
  "The public-input theorems are about a verifier none of the three executable verifiers runs; the debt is assigned to Layer 12, which cannot pay it",
  "gt-table-pub.md §8 (third finding), §7; code-pubinput.md §G.2, §B.1, §C.13",
  "gt-table-pub: a deliberate deviation (decision 15; status finding F18). code-pubinput: a disagreement between the specification and its three implementations (not an unsoundness); the blueprint follows the specification deliberately and owes the deployed verifier's theorem in the wrong place and shape",
  "The specification checks each limb; the Rust verifier, the Python verifier and the recursion guest check one combined equation `c₀ + y·c₁ = (1+r)·w₀ + r·w₁` and pool the scalars sent. That is a different oracle verifier, so Layer 12's compilation theorem cannot hold with a Rust-faithful `verify` and cannot detect the difference with a per-limb one (its fixture is an honest proof).",
  "`08-end-to-end-protocol.tex:30-31`; `cpu/mod.rs:752-755`; `verifier.py:1400`; `aggregate.py:1681-1684`; blueprint `:1053-1062`, `:1218-1221`; probe `ProbeWordsLemma.lean` (`accepts_two_challenges`, old pins)",
  "Layer 8 builds a second phase for the deployed check (pooling the values sent, `Phase.Security` at `1/|E|`), consumed by the master theorems and Layer 12; keep the specification's phase as reference; report the ambiguity of §8.2 to leanVM (gt-table-pub.md §8; code-pubinput.md §G.2)",
  "cited-checked; probe-run (key lemma); unverified (the deployed phase's full `Phase.Security`, on paper)"),
F("major", 1, "pub",
  "The check on the public-input message is not load-bearing for any theorem of the phase",
  "code-pubinput.md §G.1; §C.3, §C.4, §C.5",
  "an error of the design, introduced by an audit-surface compression (the blueprint's Layer 8 text describes a check tying the pool to the statement; the code's does not)",
  "The verifier pools the values it computes from the statement, not the values received, so a verifier that ignores the message is perfectly complete and round-by-round knowledge sound at the same seams, extractor and error; proved for every message function and every check the message passes. The earlier review's \"each of five wrong verifiers breaks a stated theorem\" is false of the merged code, and the status repeats it.",
  "`PublicInput.lean:127-128, 350-366`; `docs/reviews/public-input-phase.md:104-114, 552-573`; `protocol-status.md:440`; probes mutation 1 and `ProbeAnyCheck` (`securityG`, no `sorryAx`, old pins)",
  "pool the values sent (`pooledFrom`), which makes the check load-bearing (its removal and weakening are then refuted, §C.6, §C.7); reword blueprint `:1035-1037`; strike status `:440`; add the refutations as tests (code-pubinput.md §G.1)",
  "probe-run"),

# --- Flock
F("major (gt-flock-ring); minor (gt-table-pub)", 1, "flock",
  "Layer 9's Flock interface consumes the eighteen limb claims and emits one claim; leanVM's Flock reads no claim",
  "gt-flock-ring.md §8.1, §2.4, §5.1; gt-table-pub.md §8 \"Layer 9's sketch\", §6 E.2",
  "an error of the blueprint (the spine's Flock slot is faithful; Layer 9 and the tracker's Flock section are not)",
  "The deployed Flock verifier reads no pooled claim; the limb claims stay in the pool and are opened as strided claims on `q_flock`. A `FlockInterface` whose input is the eighteen claims and whose output is one weighted claim drops them, so with leanVM's verifier its knowledge-soundness error is 1.",
  "`cpu/mod.rs:799-805` (the dossier cites `:790-814`; quotation abbreviated, corrected by the check); blueprint `:1075-1092`",
  "a `FlockPhase I R` at the spine's seams (public-input seam to Flock seam) that hands the claims on and adds the ring-switched claim; the schedule written out (gt-flock-ring.md §8.1)",
  "cited-checked; independent check agrees"),
F("major (gt-flock-ring, boundary-adaptor; \"cannot be stated as written\")", 1, "flock",
  "The instance depends on a Flock interface that depends on the instance (the limb slot map, `aux`, the compression lemma)",
  "gt-flock-ring.md §8.2; boundary-adaptor.md §G.7",
  "an error of the blueprint",
  "The instance's `layout` takes its slot map from `FlockInterface.limbColumns`, but `FlockInterface` takes the instance as its parameter; the slot map is eighteen numbers and a generic identity. boundary-adaptor adds that the instance's `aux` must be Flock's R1CS, which only issue #3 defines, and that the lemma \"R1CS implies the limbs compress\" that `satisfiedBy_witnessOf` consumes has no carrier in any signature.",
  "blueprint `:846-848`, `:855-857`, `:1077`; `hash_flock.rs:87-115`",
  "an instance-free structure supplied by issue #3 (`blake2sLimbSlot` in `Parameters/` in gt-flock-ring; `FlockSpec` with `slot`, `Holds`, `compress_of_holds`, `gen`, `holds_gen` in boundary-adaptor); delete `limbColumns` and `FlockWitnessGen` (gt-flock-ring.md §8.2; boundary-adaptor.md §G.7)",
  "cited-checked (gt-flock-ring part); paper",
  "Two dossiers. Related, not merged: [[strided]] (the missing strided reader, code-layer1) and [[flockabs]] (the Flock phase over an abstract instance, gt-flock-ring §8.3, which boundary-adaptor's proposal also takes)."),
F("major (cannot be stated as written)", 1, "flock",
  "The Flock phase cannot be written over an abstract instance, which gives it only an opaque predicate",
  "gt-flock-ring.md §8.3; §1 item 7; probe 9.1",
  "an error of the blueprint (a design gap the spine left open)",
  "Layer 9 is to be written over an abstract instance behind the wall, but the instance's auxiliary predicate names no column, no compression count and no relation (the sketch reaches for a leanISA size). On the toy, whose predicate is `True`, a Flock phase that checks nothing is knowledge sound at error zero: today a reader of the master theorems trusts everything about Flock.",
  "`Spine/Instance.lean:143-148`; blueprint `:331`, `:1072`; probe `NoCheckFlock.lean` (exit 0 per the dossier, old pins)",
  "a `FlockRegion I` (the column, `kBatch`, its height, `aux ↔ Flock.Holds`) supplied by Layer 3 and taken by Layer 9 (gt-flock-ring.md §8.3)",
  "cited-checked; probe-run (not re-run by the check)",
  "Related: [[trusted]] (the instance as trusted data, code-spine)."),
F("major", 1, "flock",
  "Acceptance test 20 files a completeness failure under a soundness error, and attributes to the protocol an inverse only the Rust prover takes",
  "gt-flock-ring.md §8.4; §4",
  "an error of the blueprint",
  "No verifier inverts a challenge-dependent value. The pinned Rust Flock prover derives a coefficient with `(1 + r)⁻¹` and at `r = 1` emits a proof its verifier rejects: an implementation completeness defect (probability at most `(k_batch + 1)/|E|`), not part of `flockError`; the spine has no place for a completeness error.",
  "`crates/flock/src/zerocheck.rs:116-118`; `fiat_shamir/src/transcript.rs:296-302`; blueprint `:1323-1325`; Python probe 9.2 (re-run by the check)",
  "rewrite test 20 (\"no exceptional-challenge clause, in any phase\"; the Rust prover's defect recorded in `docs/leanvm-target.md`); the same sentence drafted for issue #3 (gt-flock-ring.md §8.4)",
  "cited-checked; probe-run (Python)",
  "DISAGREEMENT with [[complerr]] (lib-arklib §G.2), which would give the spine a completeness error for Flock. The check notes that \"no verifier takes an inverse\" is literally false (constants are inverted); read \"no inverse of a challenge-dependent value\"."),

# --- opening and compilation
F("major", 1, "opening",
  "ArkLib has no Fiat–Shamir or BCS statement to serve as the witness obligation, and `Verifier.fiatShamir` does not describe the compiled verifier",
  "lib-arklib.md §G.4; §F.1",
  "an error of the blueprint",
  "At both pins `fiatShamir_completeness` is admitted and stated for a constant challenge oracle, Fiat–Shamir soundness is a `TODO`, the round-by-round to state-restoration statements and `BCSTransform` are commented out, and `Commitment.extractability` has body `False`. `Verifier.fiatShamir` would hash whole oracle messages, not Merkle roots.",
  "ArkLib `FiatShamir/Basic.lean:130-136, 163-175`, `Implications.lean:230-254`, `BCS/Basic.lean`, `Commitments/Functional/Basic.lean:250-255` (`dca90385`); blueprint `:263`, `:1218-1221`",
  "ledger row A5: `FiatShamirSecurity` and `BcsSecurity` are assumed interfaces whose obligation is the literature; drop `Verifier.fiatShamir` from `verify_iff_compiled` or apply it to the compiled protocol (lib-arklib.md §G.4)",
  "paper (that the constant-oracle statement is false in general is the dossier's inference, not machine-checked)",
  "Related, not merged: [[fsother]] (literature), on what an upstream theorem would be about."),
F("major (the interface cannot be discharged by \"the upstream theorem\")", 1, "opening",
  "Upstream Fiat–Shamir and BCS theorems will be about other constructions than leanVM's one-map BLAKE2s chain",
  "literature.md §E.6 (first finding)",
  "a deviation forced by an upstream library, to be recorded with its workaround",
  "ArkLib's transforms use one random oracle on the full prefix or a duplex sponge, and the textbook BCS analysis uses independent oracles per role; leanVM uses one 64-byte BLAKE2s map for the chain, the untagged Merkle nodes and grinding. A chain lemma and a role-separation lemma are owed here.",
  "blueprint `:263`, `:1218-1221`; `fiat_shamir/src/merkle.rs:44-51`; ArkLib README at `7653a901`; [CY24] Construction 25.1.1; [CO25] §2.3",
  "rewrite ledger row A5: obligations the upstream theorems do not discharge as stated; name the chain lemma and the role-separation lemma (literature.md §E.6)",
  "paper; unverified (whether a cross-role input is exploitable; whether a later ArkLib provides a chain-based transform)"),
F("major", 1, "opening",
  "The Fiat–Shamir interface omits grinding, so it cannot state leanVM's 128-bit claim",
  "literature.md §A.4 (first finding)",
  "an error of the blueprint",
  "leanVM's query rounds reach 128 bits only with 17 bits of query grinding; the planned `FiatShamirSecurity` (error `Q · max_i ε_i`) has no proof-of-work factor, so a Lean statement would certify about 111 bits. No published theorem covers Fiat–Shamir with proof of work for multi-round IOPs.",
  "blueprint `:1224`, `:1234-1235`; `whir_config.rs:57-60`; `fiat_shamir/src/lib.rs:30-51, 126-178`; [CY24] Theorem 31.3.1",
  "restate `FiatShamirSecurity` with the grinding bits `b_i` of each challenge and error `(t + k)·max_i 2^(−b_i)·ε_i + 3.5·t²/2^256`, the proof-of-work factor marked an assumption (literature.md §A.4)",
  "paper (literature)"),
F("major", 1, "opening",
  "The proof of work is the one verifier check no planned theorem or mutation makes load-bearing",
  "literature.md §G.5 (first finding); §G.3, §G.4",
  "an error of the blueprint",
  "leanVM's 128-bit claim depends on grinding, yet the planned interfaces and Layer 12's six mutations leave it outside every theorem and test, together with truncated Merkle paths, digest canonicity and sizes above their caps.",
  "blueprint `:1224`, `:1238-1240`; `fiat_shamir/src/merkle.rs:22-37`",
  "the change of the previous row; extend Layer 12's mutations (a wrong grinding nonce at each level, a truncated path, a nonzero third limb, a size above its cap) and run transcripts the specification rejects through the Rust and Python verifiers (literature.md §G.5)",
  "paper",
  "Related, not merged: [[canon]] (canonical-encoding and consumption checks, gt-bus G9)."),
F("major (literature, \"numerically benign\"); note (gt-flock-ring)", 1, "opening",
  "The compiled error omits the list-size factor of a list-binding commitment",
  "literature.md §A.4 (second finding), §A.3 item 4; gt-flock-ring.md §8.13",
  "an error of the blueprint (and a gap in the specification, whose §8.4 is `TODO`)",
  "The commitment is list-binding only, so each challenge drawn before the claims pin a unique list member contributes `L_0 · ε_i` after compilation, and the pinning step `C(L_0, 2)·μ/|E|`; the Rust multiplies the ring-switching degree by the list size. Neither the specification, ArkLib nor the blueprint's `niError` states this.",
  "`b-polynomial-commitment-scheme.tex:4` and Lemma `lem:ood`; `whir_config.rs:540-541, 564-567`; blueprint `:1234-1235`",
  "a named composition lemma in Layer 12 and `L_0` carried into `niError` (literature.md §A.4; gt-flock-ring.md §8.13)",
  "cited-checked (gt-flock-ring part); paper; unverified (`L_0` estimated at `2^7` to `2^10`)"),

# --- adaptor
F("major (docs-debt, boundary-adaptor; a statement cannot be proved as written)", 1, "adaptor",
  "The base soundness (and completeness) theorems lack `WellFormedBytecode`; the soundness theorem is not a statement about `verify`",
  "docs-debt.md §H.1, §B.6; boundary-adaptor.md §G.3, §C, §E.6",
  "an error of the blueprint, against the leanISA roadmap (the program condition is faithful to leanVM, whose compiler guarantees it)",
  "Layer 13's two base theorems are said to compose `constraintSoundness` and `constraintCompleteness`, which require `WellFormedBytecode prog`; a bytecode with a `JUMP` in the sentinel slot has steps that balance and no valid execution, so the soundness theorem is false without it. boundary-adaptor adds that \"except with probability\" attached to the closed Boolean `verify prog input proof = true` has no meaning (the theorem must be about the random-oracle verifier, the step to BLAKE2s being a heuristic stated nowhere), and that the conclusion drops the extracted witness.",
  "blueprint `:222`, `:1247-1255`; `leanisa-blueprint.md:1156-1166`; `architecture.md:224-228`; `leanvm-target.md:57-62`; the proved test `tests/LeanerVMTests/Semantics/Execution.lean:415-461`; probe `Transport` (examples 3-4, old pins)",
  "add `(hwf : WellFormedBytecode prog)` to both (or have `verify` decide the condition and reject); restate soundness for the compiled random-oracle verifier (`baseVerifier_sound`) plus a pointwise `execution_of_extracted` (docs-debt.md §H.1; boundary-adaptor.md §G.3)",
  "paper; probe-run (`Transport`; the sentinel counterexample is a proved repository test)",
  "Two dossiers (the coordinator's known overlap). The completeness theorem's other defects are [[basecompl]]."),
F("major", 1, "adaptor",
  "The base completeness theorem is false without resource hypotheses and needs a witness generator",
  "boundary-adaptor.md §G.4; §C",
  "an error of the blueprint",
  "A valid execution may use `κ = 32`, whose four memory columns exceed the `2^28` stack the verifier accepts, and `AssignmentRepresents` fixes `κ`, so no accepted proof of that witness exists; \"witness of t\" needs the witness generator (T2), which the blueprint excludes; `constraintCompleteness` takes `WellFormedBytecode`, not `HasFillBlocks`; the rate is not chosen by the execution.",
  "blueprint `:147-148`, `:1249-1250`, `:1255-1257`; `Semantics/Execution.lean:108-110`; `Arithmetization/Statement.lean:358`; `cpu/mod.rs:174-176`; `pcs.rs:51`; `verifier.py:1379`",
  "`baseProver_complete` from a satisfying witness with admissible sizes and a valid rate, and `baseProver_complete_of_execution` with a fit hypothesis `hfit`; ask leanISA for a minimal-height `constraintCompleteness` (boundary-adaptor.md §G.4)",
  "paper",
  "Item (c) overlaps [[wfb]] (docs-debt §H.1 also names `HasFillBlocks`). Related: [[resource]] (`constraintCompleteness`'s own resource hypothesis)."),
F("major", 1, "adaptor",
  "The instance is not `Ensemble.toM3` of the eight tables",
  "boundary-adaptor.md §G.1; §A.5",
  "an error of the blueprint",
  "The memory and bytecode seed/finalize blocks and the state boundary must be boundary blocks whose index and program coordinates are `Coord.known` data of the instance (decision 8); with those blocks as tables of the instance the program would be committed, `M3Holds` would not imply the mixed witness's balance, and no adaptor theorem could be proved. No `Ensemble.toM3 : Ensemble → M3Instance` can exist (an instance needs `μ`, `layout`, public lines, `aux`, `Stmt`).",
  "blueprint `:21`, `:77`, `:803-805`, `:1369`, `:1398`; `Spine/Instance.lean:86-98, 136`; `cpu/layout.rs:352-395`; `leaf.rs:453`; probe `KnownColumn` (exit 0, old pins; `KnownColumnNew` re-run at the new pins, passes)",
  "`leanIsaInstance` as `Component.toM3` of the six opcode tables, three column groups, six boundary blocks with `Coord.known` program columns, the deployed layout, three public lines, the Flock `aux`; delete `Ensemble.toM3` (boundary-adaptor.md §G.1)",
  "probe-run",
  "gt-bus §E.3 made the same remark in passing (\"the instance is not `Ensemble.toM3` of the ensemble: those cells become `Coord.known`\")."),
F("major", 1, "adaptor",
  "No bridge lemma relates the boundary blocks to the Clean memory, bytecode and verifier rows",
  "boundary-adaptor.md §G.2; §A.2, §A.5",
  "an error of the blueprint (omission)",
  "`SatisfiedBy`'s balances range over all interactions, including the memory block's, the bytecode block's and the verifier's rows, which in the instance are boundary tuples; Layer 2's two bridges concern tables only, and nothing states that those rows' messages are the boundary tuples. Without it neither direction of the adaptor can be proved.",
  "blueprint `:775-777`, `:810-819`; Clean `FlatEnsemble.lean:225-226` (`93c9d1ef`); `Arithmetization/Statement.lean:207-209`",
  "add `boundary_tuples_eq` to Layer 3 and a Layer 2 test on the one-row witness (boundary-adaptor.md §G.2)",
  "paper"),
F("major", 1, "adaptor",
  "The polynomial bridge of Layer 2 is noncomputable at the pin",
  "boundary-adaptor.md §G.8; §E.5",
  "a deviation forced by an upstream library, with a workaround; retired if CompPoly makes `toCMvPolynomial` computable",
  "Layer 2 produces Mathlib polynomials while the instance holds CompPoly's; CompPoly's conversion is `noncomputable` at both pins, which would make `M3Holds` of the leanISA instance undecidable by evaluation and `verify` noncomputable. A direct computable translation from Clean expressions takes twelve lines.",
  "blueprint `:762-771`, `:866-867`, `:1230-1231`; `Spine/Instance.lean:123-125`; CompPoly `MvPolyEquiv/Core.lean:41` (`3468b38c` and `572f9973`); probe `PolyBridge` (exit 0; `PolyBridgeNew` re-run at the new pins, passes)",
  "`Expression.toCMvPolynomial` with `eval_toCMvPolynomial` and a Mathlib-side bridge for the degree (boundary-adaptor.md §G.8)",
  "probe-run"),
F("major (gt-bus, boundary-adaptor, code-layer1; code-layer1: \"by the scale's letter\", the fix is one line)", 1, "adaptor",
  "Layer 3's sizes and admissibility statements cannot be stated or hold as written (`Sizes`, `Sizes.ofWitness`, `Sizes.Admissible`, `admissible_iff_caps`, `leanIsaInstance_fits`)",
  "gt-bus.md G4; boundary-adaptor.md §G.5; code-layer1.md §G.2",
  "an error of the blueprint",
  "Both verifiers reject a stack outside `[15, 28]` and a rate outside `[1, 4]`, but leanISA's `Caps` has neither window, so either `verify_iff_compiled` and `piopError_le` are false or `admissible_iff_caps` is (it also has a free `w`); no witness determines the announced rate, so `Sizes.ofWitness` is ill-defined and lacks `prog`; `leanIsaInstance_fits` uses a `total` that `Layout` has not, while the fit is an argument `Blocks.layout` needs before the instance exists.",
  "`cpu/mod.rs:157-176`; `verifier.py:1377, 1379`; blueprint `:795-808`, `:1130`, `:1218-1220`; `Arithmetization/Statement.lean:79-81, 250-263`; `Spine/Instance.lean:73-81`; `Stack.lean:97`",
  "`Sizes` of the heights only; `leanIsaBlocks`, `leanIsaμ`, `leanIsaBlocks_fits`; `Sizes.Admissible` with both windows; `validRate`; `caps_of_admissible`, `sizes_of_satisfiedBy`; tests for `μ_stack = 29`, `logInvRate = 5` (gt-bus.md G4; boundary-adaptor.md §G.5; code-layer1.md §G.2)",
  "cited-checked (gt-bus part); paper",
  "Three dossiers: gt-bus has the caps side, code-layer1 the fit, boundary-adaptor both and the rate."),

# --- libraries
F("major", 1, "libs",
  "The blueprint plans on a framework ArkLib calls legacy, and on a pull request that may not merge",
  "lib-arklib.md §G.3; §F.2, §C.3",
  "an error of the blueprint's plan",
  "ArkLib calls `OracleReduction` legacy; its typed interaction framework (grown to `7653a901`) has no knowledge soundness, no round-by-round notion and no extractor; #615 is open and conflicting; no relevant admission was lifted between the pins. The blueprint expects #615 to land and upstream to prove the round-by-round to plain implication.",
  "ArkLib `AGENTS.md`, `docs/design/05-roadmap.md` (`7653a901`); issue #676, PR #615 (read with `gh`); blueprint `:257-267`, `:1143`, `:1429`; status `:201` (accurate)",
  "keep the port until any framework proves a guarded-first append; state the plain corollary locally (probe `PlainReading`, 40 lines, plus a local union bound); a ledger row for the typed framework (lib-arklib.md §G.3)",
  "paper; probe-run (`PlainReading`, old pin)"),

# --- Layer 1
F("major", 1, "layer1",
  "The strided reader of the eighteen BLAKE2s limb columns exists nowhere and is assigned to no layer",
  "code-layer1.md §G.1; §B.8",
  "an error of the blueprint (omission)",
  "leanVM reads the limb columns as strided slots of `q_flock` (the low eight coordinates frozen to the slot's bits). Layer 1 has only high-index selection, `Layout.comap` cannot place a limb column, and no layer sketches the selection lemma, the reader or the combinator; `leanIsaInstance` cannot be built without them.",
  "`pcs/src/stack_open.rs:84-97`; `verifier.py:884-894`; `hash_flock.rs:87-115`; `ToCompPoly/Multilinear.lean:50-51`; blueprint `:841-848`; probe `StridedProbe.lean` (generic lemma, twenty lines)",
  "add `sliceLow`, `evalMle_boolVec_append`, `Blocks.stridedLayout`, `Layout.piecewise` to Layer 1, with tests against the Python's `Placement.stack_point` (code-layer1.md §G.1)",
  "probe-run (the lemma; run outside `lake`, old binary); unverified (the reader and combinator are sketched)",
  "Related, not merged: [[flockcirc]] (the limb slot map, gt-flock-ring §8.2, boundary-adaptor §G.7)."),

# --- documentation
F("major (docs-debt); minor (gt-table-pub, gt-bus, code-spine)", 1, "docs",
  "The per-layer sketches (Layers 4 to 7, 9, 10) and the tracker use types the spine does not have",
  "docs-debt.md §H.3, §B.4; gt-table-pub.md §8 \"Layer 7's sketch\", §4 C.2; gt-bus.md G11; code-spine.md §E.2",
  "an error of the blueprint",
  "Layer 6's `BusOut` with challenges and totals, Layer 7's `BusOut × ColumnClaims`, Layer 9's `FlockInterface`, Layer 10's own `Weight`, `WeightedClaim`, `leanVmPiop` and master theorems over `Set.univ` and `rbrKnowledgeSoundness`, and `Sumcheck.Def`, `Gkr.Def`, `Batch.Def` plus seven undefined names; the text beside them says the spine is authoritative. gt-bus adds that Layer 6's invariant after `(α, β)` must be \"the two products differ\", not \"the multisets differ\"; gt-table-pub that `tableSumcheck_relOut_implies_constraints` has no statement.",
  "blueprint `:952`, `:954-979`, `:984`, `:988`, `:991-992`, `:1077-1085`, `:1104`, `:1109-1130` against `Spine/Seams.lean:130-135`, `Spine/Compose.lean:162-177`",
  "restate Layers 6, 7, 9 and 10 on Layer 8's pattern over the spine's seams and Layers 4, 5 as `Component.Def`s in the named form; delete the pre-spine blocks (docs-debt.md §H.3; code-spine.md §E.2)",
  "cited-checked (gt-table-pub, gt-bus parts); paper"),
F("major (docs-debt); minor (gt-table-pub)", 1, "docs",
  "The blueprint hands the holes' specification to a tracker comment that contradicts it; its public-input section says \"the prover sends nothing\"",
  "docs-debt.md §H.2, §B.3; gt-table-pub.md §8 \"The tracker's text for the public-input phase is stale\"",
  "an error of the blueprint (its delegated specification of the public-input phase differs from §8.2; the built phase is faithful)",
  "The blueprint points to the hole comment three times; eight of its thirteen sections carry pre-spine signatures that do not typecheck against `Phase.Def`, and its public-input section says the prover sends nothing and the scalars are Layer 12's encoding, where §8.2, the Rust and the code have the prover send two scalars.",
  "blueprint `:339-340`, `:590-591`, `:1485-1487`; hole comment `:3`, `:93-94` (re-read with `gh`); `08-end-to-end-protocol.tex:29`; `cpu/mod.rs:746-749`; `PublicInput.lean:99`",
  "move each section of the hole comment into the blueprint (docs-debt.md §G.4 map); the comment becomes a pointer (drafts only)",
  "cited-checked (gt-table-pub part); paper"),
F("major, of the status (gt-bus); minor (gt-table-pub, gt-flock-ring)", 1, "docs",
  "The status's finding that the Python verifier omits the caps is false at the pin (F9)",
  "gt-bus.md G5, §F; gt-table-pub.md §8 \"Two status findings are wrong\"; gt-flock-ring.md §8.10",
  "an error of the status",
  "The Python verifier's `build_layout` checks `16 ≤ log_memory ≤ 32`, every height `≤ 32`, `τ_BLAKE2S ≥ 3` and a power-of-two bytecode; the Rust itself says the other two verifiers reject there. Nothing is to be reported upstream.",
  "`verifier.py:856-864`, called at `:1378`; `log2_strict` at `:252-254`; `cpu/mod.rs:164-165`; status `:164`, `:316-318`",
  "delete F9 and `st:164`; correct the earlier reviews that cite it (gt-bus.md G5)",
  "cited-checked",
  "Three dossiers. The provenance was corrected by the check: the lines were assembled in `8a6e7750`, `348ca455`, `5751a5c7`, not introduced by `14fbca8f` (as gt-bus and gt-flock-ring say); all are ancestors of the pin."),

# ============================================================ MINOR

# --- relation and seams
F("minor", 2, "seams",
  "Knowledge soundness is bundled with perfect completeness",
  "gt-flock-ring.md §8.5",
  "a deliberate deviation of the spine from ArkLib's separate statements",
  "`Component.Security` extends `Complete`, so a protocol whose completeness is unproved or imperfect gets no soundness theorem, though the composition uses only the first verifier's guard.",
  "`ToArkLib/Component.lean:90-93, 176, 182-184`",
  "a `Component.Guarded` (output purity and guard) extended by both `Complete` and `Security`; convention Holes reworded (gt-flock-ring.md §8.5)",
  "cited-checked; paper",
  "The check adds that `Security.append` also builds `toComplete` (`:176`), so the split must give it a completeness-free path. Related: [[complerr]] and [[test20]] on completeness errors."),
F("minor (code-spine); note (lib-arklib)", 2, "seams",
  "The `outputPure` field is redundant, and `guarded` nearly so",
  "code-spine.md §F \"The outputPure field is redundant\", §D.7; lib-arklib.md §G.7",
  "a deviation forced by an upstream library (retired when the spine imports ArkLib's `NoAmbient`)",
  "Over the empty oracle every component has a pure prover output and a guarded form: ArkLib has `Prover.instOutputIsPureEmpty` and `Verifier.GuardedForm.ofEmpty` at both pins, not imported by the spine; every phase discharges `outputPure` by `rfl`.",
  "ArkLib `Composition/Sequential/NoAmbient.lean:39-55`; `ToArkLib/Component.lean:79-80`; probe `P6Surface.lean` (`outputPure_of_def`)",
  "delete `outputPure`; keep the hand-written `guarded` (readable) or make both defaults (code-spine.md §F; lib-arklib.md §G.7)",
  "probe-run"),
F("minor", 2, "seams",
  "`Layout.read` is determined by `extend`",
  "code-spine.md §F \"read is determined by extend\"; §C.2",
  "— (a design remark)",
  "The extension of a table at a cube point is its entry, so `read` can be a definition from `extend` rather than a field with a law.",
  "`Spine/Instance.lean:79-81`; argument of §C.2",
  "`Layout` with `extend` and one law; `read` a definition (code-spine.md §F)",
  "paper (the lemma `read_eq_of_extend` was not run)"),
F("minor (auditability)", 2, "seams",
  "The error bundled in `Component.Def` makes every phase, the composed verifier and the extractor noncomputable",
  "lib-arklib.md §G.5",
  "—",
  "`publicInputPhase` is `noncomputable` because of the error alone; `leanVmVerifier` and `piopExtractor` take the bundle, so on the real protocol neither compiles, though the blueprint promises the prover and extractor compute.",
  "`PublicInput.lean:374-381`; blueprint `:1145`, `:1333`; probe `ExtractorsExpectedFailure` (exit 1, expected)",
  "move `err` into `Security`, or split a computable reduction structure that `Def` extends (lib-arklib.md §G.5)",
  "probe-run",
  "Related: [[declerr]] (code-spine), whose recommended design also moves `err` out of `Def`."),
F("minor", 2, "seams",
  "Two side conditions a bus phase over an abstract instance needs",
  "gt-bus.md G10; probe H.2",
  "an error of the blueprint (the instance admits instances no deployed-shape bus phase serves; leanVM's is not one)",
  "With degree bound 0 and a count column the relation is inhabited but the count form has degree 1, outside `Seam.bus`; a table with a constraint and nothing on the bus has no zerocheck point.",
  "`Spine/Seams.lean:176`; `constraints.rs:250-253`; Lean probe `BusSeam.lean` parts 1-2 (exit 0 per the dossier)",
  "fields `one_le_d`, `constrained_on_bus` of `M3Instance`, or hypotheses of the bus phase; acceptance test 28 names the first (gt-bus.md G10)",
  "cited-checked; probe-run (not re-run by the check)"),
F("minor (code-spine, code-layer1, docs-debt)", 2, "seams",
  "`Protocol/Basic.lean` imports the arithmetization and is not a listed exception of the wall",
  "code-spine.md §E.3 row 25; code-layer1.md §G.8, §D.1; docs-debt.md §H.8, §B.5 item 12",
  "an error of the blueprint (acceptance test 25's witness text is false), and dead code",
  "`LeanerVM/Protocol/Basic.lean:3` is `public import LeanerVM.Arithmetization.Basic` in an empty placeholder imported only by `LeanerVM.lean`; the wall's `grep` witness returns it. docs-debt adds that the wall rule has no script.",
  "`git grep \"import LeanerVM.Arithmetization\" b435631 -- LeanerVM/Protocol` (two hits); blueprint `:331`, `:1341-1345`; `scripts/check-layers.sh:30-41`",
  "delete the file or its import (or list it); write the rule with an allow-list into `scripts/check-layers.sh` and a planted violation into `scripts/test-policy-checks.py` (docs-debt.md §H.8)",
  "paper (git grep)",
  "Three dossiers."),

# --- master theorems and error
F("minor", 2, "error",
  "The blueprint's headline describes master theorems that do not exist on `main`",
  "code-spine.md §F \"The headline describes theorems that do not exist\"; §C.4",
  "an error of the blueprint",
  "The headline has no phase bundle or proofs as hypotheses, a numeric `piopError I`, a plain \"except with probability\" conclusion (the theorem is round-by-round; the plain form is ArkLib's admitted implication) and \"the extractor's column `q`\" (no such definition); both theorems hold of any five phases meeting the seams, for any instance.",
  "blueprint `:8-17`; `Spine/Compose.lean:162-185`; ArkLib `Implications.lean:223-228` (`sorry`)",
  "new pseudo-signatures with `P`, `C`, `S` and a sentence that they are composition theorems (code-spine.md §F)",
  "paper (reading)"),
F("minor", 2, "error",
  "The extracted stack is not a definition; acceptance test 24's `rfl` witness covers zero-round phases only",
  "code-spine.md §F \"The extracted stack is not a definition\"; §D.5",
  "an error of the blueprint",
  "With the repository's public-input phase in the bundle the composed extractor's output has type `Unit` and the test is ill-typed; the stack is the intermediate extractor's value at round 0.",
  "ArkLib `Append/StateFunction.lean:129-139`; `ToArkLib/SendOracle.lean:137`; blueprint `:100-101`, `:1133-1135`, `:1337-1339`; probe `P3cExtractor.lean`",
  "define `piopExtractedStack` and prove it equals the first message for every bundle and transcript (code-spine.md §F)",
  "probe-run"),
F("minor (gt-table-pub, gt-bus)", 2, "error",
  "The zerocheck escape is over-charged and charged three or four different ways",
  "gt-table-pub.md §8 \"The zerocheck escape\", §5 D.1, D.3; gt-bus.md G6, §D.3",
  "an error of the blueprint",
  "Row Seams charges `1/|E|` per coordinate per constraint, Layer 6's `busError` has no term, Layer 7 charges `τ_max/|E|` per constraint to `(α, β)` (drawn before any coordinate of `ζ`), and the tracker sums them. With the bus phase's state function a conjunction, the escape costs nothing beyond the GKR's own errors (at most `τ_max/|E|` once, whatever the number of constraints).",
  "blueprint `:333`, `:974`, `:1000-1003`, `:1283`; tracker P2 (\"`1/|E|` per coordinate per constraint\")",
  "one definition of `busError` in Layer 6 with the zerocheck as a conjunct of the state function; drop \"per constraint\" and \"the (α, β) and\" (gt-bus.md G6; gt-table-pub.md §8)",
  "cited-checked; paper",
  "Two dossiers; they count three ways (gt-table-pub) or four (gt-bus, counting the tracker) and agree on the fix. See the disagreement on the GKR round error, [[gkrnorm]] and [[gkrpos]]."),
F("minor (for T4 as stated) / note", 2, "error",
  "\"Computable\" is not \"efficient\" for the compiled extractor",
  "literature.md §A.4 (fourth finding)",
  "—",
  "The literature's knowledge soundness requires a polynomial-time extractor; ArkLib's does not; after compilation a brute-force list decoder is computable but exponential. T4 as stated needs only soundness, so it is not weakened.",
  "ArkLib `RoundByRound.lean:103-117` (`dca90385`); blueprint `:1248`, `:1299`, `:1333-1340`",
  "acceptance test 24 names an efficient list decoder as intended; knowledge soundness of `verify` claimed only information-theoretically (literature.md §A.4)",
  "paper"),

# --- bus
F("minor", 2, "bus",
  "The order of the leaf stacks is nowhere stated, and the spine's `tuples` lists them in the opposite order",
  "gt-bus.md G7",
  "an error of the blueprint (omission of a transcribed convention)",
  "The deployed leaf stacks put the three unowned blocks first and break ties by that index, which fixes offsets, selectors and so the verdict; the spine lists the flush tuples first (immaterial to `Balanced`, a trap for whoever derives the leaf layout).",
  "`cpu/layout.rs:354-410`; `verifier.py:499, 507`; `Spine/Instance.lean:185-186`",
  "a conventions row \"Leaf stacks\"; a Layer 6 test with a table height equal to `κ_mem` (gt-bus.md G7)",
  "cited-checked",
  "Related: [[tieorder]] (the tie order of the witness stack, code-layer1 §G.3)."),
F("minor", 2, "bus",
  "Orders the blueprint leaves open: the two roots, the boundary evaluations, the linear claims, the point",
  "gt-bus.md G8",
  "an error of the blueprint (omissions of transcribed conventions)",
  "The roots are sent bus root first; the boundary evaluations in first-naming order with repeats skipped; the linear claims table by table, then push, pull, count; `ζ = (u₀, u₁, χ₀, …)` of the last layer.",
  "`gkr.rs:274-275`; `verifier.py:434`; `leaf.rs:428-439, 466-471`",
  "four clauses in Layer 6 (gt-bus.md G8)",
  "cited-checked"),
F("minor", 2, "bus",
  "The binary GKR layer's combination challenge has no error assigned",
  "gt-bus.md G12",
  "an error of the blueprint (omission)",
  "For odd `μ` the first layer has one combination challenge, error `1/|E|`, which `gkrError` does not name.",
  "`gkr.rs:387`; blueprint `:941-942`",
  "\"`1/|E|` to each combination challenge (two per radix-4 layer, one for the binary layer)\" (gt-bus.md G12)",
  "cited-checked"),

# --- table sumcheck
F("minor", 2, "table",
  "Sumcheck round messages: four coefficients and a check in the oracle protocol, three and none on the wire; the owed lemma is unstated",
  "gt-table-pub.md §8 \"The round message\"",
  "a deliberate deviation (it owes a lemma the blueprint does not state)",
  "Both verifiers derive the linear coefficient from the running claim and never check the round; the blueprint's oracle protocol sends all four coefficients and checks, so Fiat–Shamir absorbs different data and a transport lemma (or a challenge oracle on the encoded message) is owed.",
  "`constraints.rs:261-291`; `fiat_shamir/src/transcript.rs:303-307`; blueprint `:315`, `:1218-1221`",
  "make the wire message the oracle protocol's (three coefficients, no round check), or state the transport lemma in Layer 4 (gt-table-pub.md §8)",
  "cited-checked; paper"),

# --- public input
F("minor (code-pubinput); boundary-adaptor agrees in its §D (a conclusion, no severity)", 2, "pub",
  "The top limb is enforced only through the instance's third line and the unbuilt adaptor theorem; acceptance test 10 names the wrong witness",
  "code-pubinput.md §G.3, §D.1, §D.2; boundary-adaptor.md §D, Summary item 3",
  "— (not a divergence; an incomplete audit trail)",
  "Every theorem of the phase and the spine holds for an instance listing two lines; what a missing third line breaks is the adaptor's `satisfiedBy_witnessOf`, at `SatisfiedBy.word0_eq`, whose right side has a zero top limb by type; the ultimate anchor is the literal `0` in `PublicInput.word0`. Test 10's witness shows the pool, on a toy-shaped instance. boundary-adaptor finds the anchor correct (a `SET_CONSTANT` at cell 0 with immediate `y²` gives a stack satisfying every other clause and a program with no execution).",
  "`Arithmetization/Statement.lean:338`; `Semantics/Memory.lean:107-110`; blueprint `:815-816`, `:1293-1295`; `tests/…/PublicInput.lean:151-180`; probe `Shapes` (`E.ofLimbs a b c ≠ p.word0` for `c ≠ 0`, old pins)",
  "reword test 10 with both witnesses (`threeLimbs`, and a `#guard` on `leanIsaInstance.publicLines` when Layer 3 lands) (code-pubinput.md §G.3)",
  "paper; probe-run (the load-bearing inequality); unverified (the two-line display and the counterexample's stack were not built)",
  "Two dossiers (the coordinator's known overlap)."),
F("minor", 2, "pub",
  "`PublicLine.sent` is pinned by prose only",
  "code-pubinput.md §G.4; §E",
  "— (avoidable audit surface until Layers 3 and 12 land)",
  "The theorems hold for every assignment of `sent`; leanISA's `(true, true, false)` is only in prose and decision 15.",
  "blueprint `:335`, `:834-836`, `:1037-1039`; `cpu/mod.rs:747-749`",
  "row \"Public input\": pinned by Layer 3's `#guard` and Layer 12's fixture (code-pubinput.md §G.4)",
  "paper"),

# --- Flock
F("minor (imprecise wording on a load-bearing definition)", 2, "flock",
  "The auxiliary predicate must include the constant-one position",
  "gt-flock-ring.md §8.6",
  "an error of the blueprint (of wording)",
  "Annex C enforces position 512 of every block to be 1; without it the zero region satisfies the R1CS, and \"`aux` implies the limb slots compress\" is false.",
  "`c-flock-protocol.tex:23-28`; `crates/flock/src/hash.rs:1172-1183`; blueprint `:850-851`; status `:239-240`; `Spine/Instance.lean:24-25, 143-145`",
  "add \"and hold 1 at the constant position 512\" wherever `aux` is described; an acceptance test that `aux` fails on the zero region (gt-flock-ring.md §8.6)",
  "cited-checked; independent check agrees"),
F("minor", 2, "flock",
  "Flock is listed as written from the specification; its circuit, layout and constants exist only in the Rust and the Python",
  "gt-flock-ring.md §8.7",
  "a deviation forced by the source (the specification is incomplete); the blueprint follows the Rust, rightly, and should say so",
  "The BLAKE2s circuit and wire positions, the limb slots, the strided selector, `g₀`, `φ₈`, `k_batch = τ_BLAKE2S`, the floor `τ_BLAKE2S ≥ 3` are fixed only by the Rust and the Python.",
  "blueprint `:192`; the table of §8.7",
  "split the sources row into protocol (specification Annexes A, C) and circuit constants (Rust files, Category B) (gt-flock-ring.md §8.7)",
  "cited-checked"),
F("minor", 2, "flock",
  "The Flock error quoted in acceptance test 23 leaves out ring switching",
  "gt-flock-ring.md §8.8",
  "an error of the blueprint",
  "Test 23's `2^-183` is `(4·k_batch + 163)/|E|` alone; `flockError_le` adds `2^32/|E| = 2^-160`, which dominates by `2^23`.",
  "blueprint `:1085`, `:1331-1332`; `c-flock-protocol.tex:282`",
  "\"below `2^-183 + 2^-160`, the second term ring switching's\"; per-challenge `flockError` (gt-flock-ring.md §8.8)",
  "cited-checked"),
F("minor", 2, "flock",
  "The ledger row on ring switching suggests a missing profile; ArkLib's construction is another protocol",
  "gt-flock-ring.md §8.9; §6",
  "an error of the blueprint (of description)",
  "ArkLib's `RingSwitching/Packing` is Diamond–Posen's reduction (carrier message, batching vector, relocation sumcheck, error `κ/|L|`), with 14 `sorry` at both ArkLib pins; leanVM's is rectangular, sends nothing and draws six challenges.",
  "blueprint `:267`; ArkLib `RingSwitching/Packing/` at `dca90385` and `7653a901`",
  "rewrite ledger row A9 as new work of issue #3, at most the tensor algebra shared (gt-flock-ring.md §8.9)",
  "cited-checked; independent check agrees"),
F("minor (planning)", 2, "flock",
  "The executable verifier needs the Flock phase's definition, which no roadmap has started",
  "gt-flock-ring.md §8.11",
  "—",
  "Every proof carries a Flock transcript (at least 8 compressions), so Layer 12's Rust-proof fixture cannot pass before a Lean Flock verifier exists; issue #3's first gate has not started.",
  "`crates/flock/src/hash.rs:283-286`; blueprint `:609`, `:614`, `:1237-1238`",
  "split hole P6: the definition and completeness now, the security stays issue #3's; hole K3 waits on it (gt-flock-ring.md §8.11)",
  "cited-checked"),

# --- opening and compilation
F("minor", 2, "opening",
  "The canonical-encoding checks and the stream-consumption check are absent from the blueprint",
  "gt-bus.md G9",
  "an error of the blueprint (omission)",
  "Zero upper limbs of the announced sizes, a zero third limb in each half of a root, and a fully consumed stream: none protects soundness, but without them `verify` accepts streams the Rust rejects, and Layer 12's mutations exercise none.",
  "`cpu/mod.rs:133-135`; `fiat_shamir/src/merkle.rs:26-29`; `verifier.py:223, 1373`; blueprint `:1238-1239`",
  "list the three checks in Layer 12 with three mutations (gt-bus.md G9)",
  "cited-checked (the dossier's search wording was overstated; the substance holds)",
  "Related: [[pow]] (the proof of work, literature §G.5)."),
F("minor", 2, "opening",
  "The hash-collision term is missing from `niError`",
  "literature.md §A.4 (third finding); §A.3 item 2",
  "an error of the blueprint",
  "`BcsSecurity` needs its collision term (`3.5·t²/2^256` under [CY24] Theorem 25.2.1's condition, or [BGKTTZ23]'s `3(Q²+1)/2^256`); a 256-bit digest is at the edge of 128 bits.",
  "[CY24] §28.3.2",
  "state the term in `BcsSecurity` (literature.md §A.4)",
  "paper"),
F("minor", 2, "opening",
  "The blueprint does not state the scope of its random-oracle assumption",
  "literature.md §B.4",
  "an error of the blueprint (omission)",
  "A random-oracle theorem for the BLAKE2s map does not cover attacks that use BLAKE2s's code ([KRS25], [Fen26]); leanVM binds the statement and commits the trace before the first challenge, so the known attacks do not apply, and no theorem says more.",
  "blueprint `:28-30`, `:89-94`, `:153-157`",
  "a paragraph after `:94` (literature.md §B.4)",
  "paper"),
F("minor", 2, "opening",
  "The Lean theorem is classical; the quantum random-oracle model is not mentioned",
  "literature.md §G.5 (second finding); §G.1",
  "an omission of the blueprint",
  "Classical round-by-round security gives about 64 bits against quantum adversaries by the known bounds; neither the blueprint nor `architecture.md` mentions it.",
  "`git show b435631:… | grep -i quantum` finds nothing; ePrint 2025/2166",
  "add to the scope section after `:157` (literature.md §G.5)",
  "paper"),

# --- setup (minor)
F("minor", 2, "setup",
  "Two deployed checks are discharged by type in Lean, and the blueprint does not say who parses",
  "boundary-adaptor.md §G.15; §B.2 item 2",
  "an error of the blueprint (omission)",
  "`read_public` rejects a public word with a nonzero third limb and a bytecode that is not a power-of-two sequence of decodable instructions; in Lean these hold by type, since `verify` takes a typed `Program` and `PublicInput`, so the obligation falls on whoever builds those values from bytes (the fixture's loader, T7's encoder), which the blueprint does not say.",
  "`cpu/mod.rs:141-143`; `Arithmetization/Statement.lean:71-75`; blueprint `:326`, `:1217`, `:1236-1240`",
  "a sentence in the row \"Verifier shape\"; the differential fixture records a rejected public input as a parse failure (boundary-adaptor.md §G.15)",
  "paper",
  "Related: [[canon]] (canonical-encoding checks, gt-bus G9) and [[toplimb]] (the top limb, code-pubinput §G.3)."),

# --- adaptor
F("minor", 2, "adaptor",
  "`witnessOf_stackOf` has no Lean statement",
  "boundary-adaptor.md §G.10; §E.2",
  "an error of the blueprint",
  "`witnessOf (stackOf w) = w` is not an equality any `EnsembleWitness` satisfies (a function field, a free width, no decidable equality), and the planned `#guard` cannot run.",
  "blueprint `:819`, `:866-867`, `:1339`",
  "the three equalities of §E.2 under `SatisfiedBy` and `Sizes.ofWitness`, and a `#guard` of them on the one-row witness; say neither T4 composition uses it (boundary-adaptor.md §G.10)",
  "paper"),
F("minor (imprecision)", 2, "adaptor",
  "`witnessOf` has no public input, and the count columns have no derivation",
  "boundary-adaptor.md §G.11; §A.4 rows 1, 4",
  "an error of the blueprint (imprecision)",
  "`witnessOf` must either take the input or read the lanes off cells 0 and 1; `Component.toM3` has a `count` field and no rule saying which coordinate of which pulls it is.",
  "blueprint `:773-777`, `:813-814`; `cpu/layout.rs:412-414`",
  "add the input (or say where the lanes are read); `Component.toM3` takes the lookup channels and `count` is coordinate 2 of every pull on them; a test against `count_columns()` (boundary-adaptor.md §G.11)",
  "paper"),
F("minor", 2, "adaptor",
  "`leanIsaInstance` must be reducible",
  "boundary-adaptor.md §G.12",
  "an error of the blueprint (omission of a constraint on the code)",
  "With a `def` instance no `Decidable` instance is found for its `M3Holds`, while an `abbrev` passes; the toy is an `abbrev` for that reason and the Layer 3 tests decide `M3Holds`.",
  "`Spine/Toy.lean:94-95`; blueprint `:803`, `:866-867`; probe `DefInstance` (expected failure, exit 1, old pins)",
  "\"`abbrev leanIsaInstance …`, reducible\" (boundary-adaptor.md §G.12)",
  "probe-run"),
F("minor (harmless)", 2, "adaptor",
  "`Refinement.map_option_valid` has the wrong polarity for ArkLib's knowledge game",
  "boundary-adaptor.md §G.13; §E.6",
  "imprecision",
  "ArkLib's bad event is \"every extracted witness is invalid\"; the pointwise lemma is stated the other way; a case split converts it, and the event-form transport is the one T4 should compose.",
  "`ToArkLib/Refinement.lean:55-57`; ArkLib `Security/Basic.lean:316` (`dca90385`); probe `Transport` (`bad_of_bad`)",
  "name `Refinement.knowledge_transport` as what T4 composes; keep `map_option_valid` for the honest direction; fix the T4 line at `:407` and the tracker's `knowledgeSound_of_refinement` (boundary-adaptor.md §G.13)",
  "probe-run",
  "Related: [[transport]] (knowledge transport in three lines, code-spine)."),
F("minor", 2, "adaptor",
  "The relation ladder conflates Clean's field sum with Clean's balance relation",
  "lib-others.md §G.1; §C.5",
  "an error of the blueprint (imprecise wording; the conclusion is right)",
  "Over `K` the field sum accepts a tuple pushed twice and never pulled, but Clean's balance rejects it through the side condition `length < ringChar K = 2`, which admits at most one interaction per channel: Clean's statement holds of no real ensemble (unsatisfiable, not merely unsound); unchanged at Clean `42fe4b26`.",
  "blueprint `:359`; probe `CleanBalance` (`pushedTwice_not_balanced`, `statement_forces_at_most_one_interaction`, old pins)",
  "reword `:359`: Clean's soundness is vacuous and its completeness false over `K` (lib-others.md §G.1)",
  "probe-run"),

# --- libraries
F("minor", 2, "libs",
  "`SampleableType K` is unused audit surface, and the blueprint disagrees with itself about it (Layer 0)",
  "lib-others.md §G.2; §E.1",
  "— (avoidable audit surface)",
  "No consumer outside `Protocol/Field.lean` (leanVM samples only `E`); the Layer 0 sketch declares the `K` instance while the dependency table says Layer 0 supplies the `E` instance and the interface list names only that one.",
  "`fiat_shamir/src/lib.rs:95-99`; blueprint `:251`, `:634`, `:1400`; probe `SamplerDiamond2`",
  "keep it as the building block of the `E` sampler and say so (lib-others.md §G.2)",
  "probe-run"),
F("minor (cosmetic)", 2, "libs",
  "`evalOracle_answer` takes `n` explicitly, unlike the blueprint (Layer 0)",
  "lib-others.md §G.3",
  "— (code/blueprint mismatch)",
  "The code has `(n : ℕ) (q : Column n)`, the blueprint `(q : Column n)`.",
  "`Protocol/Field.lean:109`; blueprint `:641`",
  "make `n` implicit in the code (lib-others.md §G.3)",
  "paper (reading)"),
F("minor", 2, "libs",
  "The scalar oracle interfaces are trusted surface the blueprint does not list (Layer 0)",
  "lib-others.md §G.4",
  "an omission in the blueprint",
  "`instOracleInterfaceE` and `instOracleInterfaceListE` decide what a verifier learns of a scalar or list message; neither is in the Layer 0 sketch or the interface list.",
  "`Protocol/Field.lean:115, 118`; blueprint `:633-650`, `:1400`",
  "add both to the sketch and the list (lib-others.md §G.4)",
  "paper (reading)"),
F("minor (possibly avoidable audit surface)", 2, "libs",
  "The upstream ledger misses the Merkle trees of the pinned VCVio and cites a closed issue",
  "docs-debt.md §H.15; §B.9",
  "—",
  "The ledger says Merkle trees are absent upstream and names ArkLib issue 4 (closed 2026-09-27 for VCVio issue 571); VCVio at `f9dc47d9` has nineteen sorry-free Merkle-tree modules.",
  "blueprint `:265`, `:1179-1182`; VCVio `CryptoFoundations/MerkleTree/` at `f9dc47d9`",
  "name VCVio's library and issue 571; decide whether Layer 11 builds on it (docs-debt.md §H.15)",
  "paper; unverified (fit with leanVM's Merkle trees; state at `a4232d08`)"),

# --- Layer 1
F("minor", 2, "layer1",
  "The order of equal-size blocks in the witness stack is pinned by no statement or test before the compiled verifier",
  "code-layer1.md §G.3",
  "an error of the blueprint (a check deferred with no witness named)",
  "`Blocks` is the sorted sizes; the tie order lives only in the renaming given to `Layout.comap`. leanVM's order and \"tables first\" give the same `Blocks` and different offsets (`mem_0` at 32 against 64), and every Layer 1 theorem holds of both.",
  "`ToCompPoly/Stacking.lean:62-68`; `Stack.lean:52`; `docs/reviews/protocol-layer1.md:34`; probes `OffsetsProbe.lean`, `offsets.py` (92 offsets of the pinned Python layout)",
  "a Layer 3 test on the two configurations where a table height equals `κ_mem` (code-layer1.md §G.3)",
  "probe-run",
  "Related: [[leafstacks]] (the leaf stacks' order, gt-bus G7), \"the same gap\"."),
F("minor (code-layer1, docs-debt)", 2, "layer1",
  "Acceptance test 14 names a tautology as its witness; no test compares the bytecode column with leanVM's encoder",
  "code-layer1.md §G.4, §C.3; docs-debt.md §H.14 (one item)",
  "an error of the blueprint (stale witness), and avoidable audit surface",
  "`bytecodeColumn_slot` unfolds its definition, and the same proof proves the wrong layout's analogue; the repository's tests use all-one operands and cannot see an operand-slot swap.",
  "`FixedColumns.lean:84-87`; blueprint `:1306-1307`; status `:51`; probe `ValuesProbe.lean` (`wrongColumn_slot`; 256 cells against a transcription of the Rust encoder)",
  "witness `bytecodeColumn_answer_boolVec` and a sixteen-instruction `#guard` against `leaf.rs:585-604`; delete `bytecodeColumn_slot` (code-layer1.md §G.4)",
  "probe-run (old pins; the Rust encoder was transcribed, not executed)"),
F("minor", 2, "layer1",
  "Acceptance test 15 overclaims that `stack_eval` fails for any other placement",
  "code-layer1.md §G.5",
  "an error of the blueprint",
  "Sizes 1, 1, 2 in that order are aligned, as is any permutation of equal sizes; the test's \"4, 2, 1\" are heights, the code's sizes are 2, 1, 0.",
  "blueprint `:1308-1310`; probe `DuplicatesProbe.lean`",
  "\"largest first is sufficient, not necessary\" (code-layer1.md §G.5)",
  "probe-run (outside `lake`, old binary)"),
F("minor (audit surface)", 2, "layer1",
  "`BlockClaims.lean` has no consumer",
  "code-layer1.md §G.7; §A.8, §E.1",
  "— (avoidable audit surface)",
  "Eight public declarations, 40 lines; `isValid_iff_pairing` restates `unstack_eval₂_eq_sumCube`; the opening uses `ColumnClaim.holds_iff_weighted`.",
  "`git grep -w BlockClaim b435631 -- LeanerVM tests`; `BlockClaims.lean:31`",
  "delete the module and its test; drop it from Layer 1's list and the interface list (code-layer1.md §G.7)",
  "paper (git grep)"),
F("minor", 2, "layer1",
  "Acceptance test 7 names the wrong lemma and a witness that does not exist",
  "code-layer1.md §G.9; §F.2",
  "an error of the blueprint",
  "\"`sumCube_prodVars`\" is `sumCube_padHigh`; `tableSummand_target` is a Layer 7 name, not built.",
  "blueprint, acceptance test 7",
  "name `sumCube_padHigh` and the existing test (code-layer1.md §G.9)",
  "paper"),

# --- documentation
F("minor (docs-debt, code-pubinput)", 2, "docs",
  "The status and the tracker describe a repository two merges old",
  "docs-debt.md §H.4; §B.1, §B.2, §B.11; code-pubinput.md §G.6",
  "— (not a divergence from leanVM)",
  "The status heads itself as a snapshot of `f4d858c`, calls the merged public-input phase a draft and repeats \"five wrong verifiers\"; the tracker shows Layer 1 and the public-input phase not landed, four closed PRs as open, \"revision 2\" undefined, and renders \"ArkLib #1\", \"ArkLib #4\" as leanerVM links; both say the pins are unchanged; `README.md` says no proof-system claim has landed.",
  "`protocol-status.md:5-6, 101, 119, 146, 440`; `issue-12-body.md`; `README.md:32-33`; `docs/README.md:38-47`",
  "rewrite the status (docs-debt.md §G.3) and the tracker body (§G.4); fix the README sentences",
  "paper (reading; `gh` read)"),
F("minor (docs-debt; lib-others, at `144c5aa`)", 2, "docs",
  "After the upgrade the blueprint states superseded pins as current, and Layer 0's prose is stale",
  "docs-debt.md §H.5, §B.11; lib-others.md §G.5",
  "— (stale text; lib-others: a deviation forced by an upstream library since lifted)",
  "At `144c5aa` the blueprint says its API tables record the original baseline but still names ArkLib `dca90385`, CompPoly `3468b38c`, Clean `93c9d1ef`, VCVio `f9dc47d9`, Lean `v4.33.1` as the pins and heads the ledger \"ArkLib state at `dca90385`\"; Layer 0's prose still warns of the eager `Fintype`, says there is no `LawfulBEq E`, and misses CompPoly's `GF(2^8)`.",
  "blueprint at `144c5aa` `:52-54`, `:113`, `:167-172`, `:261`, `:285`, `:574`, `:633-635`, `:649-650`; CompPoly `Extension/Arithmetic.lean:380` (`572f9973`)",
  "pins only in `upstreams.json` and `dependencies.md`; ledger \"state at the pin\" re-read at `7653a901`; reword Layer 0's four passages (docs-debt.md §H.5; lib-others.md §G.5)",
  "paper (reading)"),
F("minor", 2, "docs",
  "Letter codes collide, and two references point at the wrong finding",
  "docs-debt.md §H.6; §D, §F",
  "— (not a divergence)",
  "At least 128 codes with 1036 occurrences; 34 with two or more meanings (`C1` has five); \"finding F3 of the status file\" means the leanISA status's; the status's legend says its `F` continues leanISA's numbering where leanISA uses `R`; codes have reached issue bodies.",
  "blueprint `:592-593`, `:1440`; `protocol-status.md:281-283`; §D counts (lower bounds)",
  "names for holes, ledger entries and findings; one index (docs-debt.md §F.3)",
  "paper (count script)"),
F("minor", 2, "docs",
  "The same fact is written in three to six places",
  "docs-debt.md §H.7; §A",
  "—",
  "The upstream ledger three times with different rows; the bus phase's specification four times with three types; a review's record four times.",
  "`protocol-blueprint.md:257-267`; `protocol-status.md:171-184`; `issue-12-body.md:61-74`",
  "one home per kind of fact (docs-debt.md §E, §G)",
  "paper"),
F("minor", 2, "docs",
  "The review tooling the blueprint prescribes is not in the repository",
  "docs-debt.md §H.9",
  "—",
  "The blueprint names a `leanerVM-review` skill that does not exist (it is `adversarial-review`); both it and `lean-spec-authoring` live under the git-ignored `.claude/`.",
  "blueprint `:178`, `:1512`; `.gitignore:9`",
  "describe the review by what it does, or track the skills (docs-debt.md §H.9)",
  "paper"),
F("minor", 2, "docs",
  "\"How work is tracked\" is contradicted by practice",
  "docs-debt.md §H.10; §B.7",
  "—",
  "Claims by comment need write access; intention issues go by layer; pull requests name no hole; labels unused; \"built, draft\" undefined; `CONTRIBUTING.md` asks for a design issue first.",
  "`protocol-status.md:553-554`; `CONTRIBUTING.md:16-19`",
  "docs-debt.md §G.1",
  "paper"),
F("minor", 2, "docs",
  "The blueprint records state and history, against its own rule",
  "docs-debt.md §H.11; §B.4 item 11",
  "—",
  "Seven places (\"done on the spine's branch\", \"(#13, taken)\", \"already in flight\", the column \"Existing work\").",
  "blueprint `:1474-1475`",
  "delete the phrases and columns (docs-debt.md §G.2)",
  "paper"),
F("minor", 2, "docs",
  "Decisions are numbered, but most of their content is gone and the numbers collide",
  "docs-debt.md §H.12; §B.8",
  "—",
  "Decisions 1 and 3 survive as \"was taken\", 6 to 10 only as outcomes; the blueprint cites decisions 6 and 8 without defining them; leanISA also numbers from 1, so \"decision 15\" means two things.",
  "`protocol-status.md:214-227, 258`; blueprint `:557`, `:560`",
  "a \"Decisions\" section in the blueprint (docs-debt.md §E.3, §F.3)",
  "paper"),
F("minor (docs-debt, code-layer1); no severity given (code-spine §E.1)", 2, "docs",
  "The list of public names is not the public boundary: most public declarations are unlisted, some load-bearing, three mislabelled",
  "docs-debt.md §H.13; code-layer1.md §G.6, §F.3; code-spine.md §E.1 (last paragraph)",
  "an error of the blueprint",
  "\"Everything not listed is a proof, a helper, or a test\" (`:1419`) is false: 198 of 333 non-private declarations are unlisted, among them load-bearing ones (the `.Holds`, `coordCell`, the tuple lists, `sendStateFunction`, `guardedAppend`; `idxColumnEval`, `bytecodeColumnEval`, `evalMle_padHigh`, `Blocks.*`; `PublicInput.check`, `pooled`); `Column`, `Weight`, `WeightedClaim` are listed as generic; `Ensemble.toM3` is listed under Spine.",
  "blueprint `:343-344`, `:1362`, `:1365-1406`, `:1419`; probe `unlisted_public.py` (198 at `b435631`, 197 at `144c5aa`)",
  "add the named declarations and modules; correct the labels (docs-debt.md §H.13; code-layer1.md §G.6; code-spine.md §E.1)",
  "probe-run (Python)",
  "Three dossiers, each with a different subset of the missing names."),
F("minor (gt-bus, docs-debt, boundary-adaptor)", 2, "docs",
  "Broken names and citations in the blueprint, status and tracker",
  "gt-bus.md G14; docs-debt.md §H.14, §B.5, §B.10; boundary-adaptor.md §G.14",
  "an error of the blueprint",
  "`leaf.rs:664-668` cited for the count blocks is `prove_balance`'s signature; \"Lemma 5.1\" is Lemma 5.2; \"specification (5.4)\" does not exist; `StateMsg` (the message is `Regs`) and `leanIsaTables` (the ensemble is `leanIsaEnsemble`) exist nowhere; `EnsembleWitness leanIsaEnsemble` needs `prog` since decision 14; the tracker's `knowledgeSound_of_refinement` does not exist; the hole table lists spine types as phase products; the status names a nonexistent `ToCompPoly/Claims.lean`; three ArkLib citations drifted.",
  "blueprint `:197`, `:220`, `:601`, `:799`, `:1280`; `05-arithmetization.tex:36, 40`; `Arithmetization/Channels.lean:138-141`; status `:177`",
  "replace each by the name that exists (gt-bus.md G14; docs-debt.md §H.14; boundary-adaptor.md §G.14)",
  "cited-checked (gt-bus part); paper",
  "Test 14's witness (also in docs-debt §H.14) is in [[test14]]; the ArkLib table's names are in [[arklibtable]] (lib-arklib §G.6)."),
F("minor", 2, "docs",
  "Source discrepancies are not recorded where both status files say they are",
  "docs-debt.md §H.16; §B.7 item 6",
  "— (about where divergences inside leanVM are recorded)",
  "`leanvm-target.md` records one discrepancy (the sentinel) and none of the proof system's twenty-seven findings against the specification, the Rust and the Python.",
  "`protocol-status.md:281`; blueprint `:1500-1501`; `leanvm-target.md:57-62`",
  "one register in `leanvm-target.md`, by name, for both roadmaps (docs-debt.md §E.2)",
  "paper"),
F("minor", 2, "docs",
  "The status's round-message finding says the cubic is sent \"at four nodes\"; the wire carries coefficients",
  "gt-table-pub.md §8 \"Two status findings are wrong\" (first bullet)",
  "an error of the status (copying a stale Rust comment)",
  "Status finding F6 says four nodes; the wire carries three of the cubic's four coefficients (`c₀, c₂, c₃`).",
  "`constraints.rs:24, 191-194`; `fiat_shamir/src/transcript.rs:56-71`",
  "\"a cubic, three of its four coefficients on the wire\" (gt-table-pub.md §8)",
  "cited-checked"),
F("minor", 2, "docs",
  "The status's finding on the one bus root misreads the specification (S11)",
  "gt-bus.md G13",
  "an error of the status",
  "The specification does say push and pull share one root; the status's F3 is an agreement of the three sources, not a divergence.",
  "`protocol-status.md:289-290`; `08-end-to-end-protocol.tex:69, 100`",
  "delete S11; reword F3 as a convention (gt-bus.md G13)",
  "cited-checked"),
F("minor", 2, "docs",
  "Names and line references in the blueprint's ArkLib table are wrong in places",
  "lib-arklib.md §G.6; §B.2",
  "an error of the blueprint",
  "`MvPolynomial.schwartz_zippel_counting` does not exist (root namespace); `prob_eval_zero_le_div` is a `PMF` statement; `Sumcheck.Domain` is `SumcheckDomain`; the completeness theorem the spine uses is missing; `CheckClaim`'s oracle variant checks nothing; the sumcheck's completeness is admitted too.",
  "blueprint `:232-251`; probe `AxiomsArkLibBuilt` (exit 1: unknown constants)",
  "corrected entries (lib-arklib.md §B.2)",
  "probe-run"),
F("minor", 2, "docs",
  "The status's dates for ArkLib #615 and #818 are last-update dates, not opening dates",
  "lib-arklib.md §F.5 (last paragraph)",
  "an error of the status",
  "\"Open since 2026-09-08\" (#615, created 2026-07-07) and \"since 2026-09-04\" (#818, created 2026-08-31).",
  "`gh api` (read-only), 2026-09-29",
  "correct the dates",
  "paper (`gh` read)"),
F("minor", 2, "docs",
  "Misattributed and mistitled references in the blueprint",
  "literature.md §A.4 (fifth finding)",
  "an error of the blueprint",
  "The Fiat–Shamir paper is Canetti, Chen, Holmgren, Lombardi, Rothblum, Rothblum, Wichs (STOC 2019); Ligerito is Novakovic and Angeris; BCHKS25's title is \"On Proximity Gaps for Reed–Solomon Codes\"; round-by-round knowledge soundness is from [CMS19] Definition 8.5.",
  "blueprint `:62`, `:1530-1537`",
  "replace by the dossier's BibTeX (literature.md, last section)",
  "paper (sources downloaded)"),
F("minor", 2, "docs",
  "The blueprint's citation for grand products points to the wrong Thaler chapter",
  "literature.md §D.3",
  "an error of the blueprint",
  "Multiset fingerprinting is [Tha22] §6.6.2 and GKR §4.6; the blueprint says chapter 4 for both.",
  "blueprint `:1538`",
  "the corrected citation (literature.md §D.3)",
  "paper"),
F("minor", 2, "docs",
  "The obligation outline behind `architecture.md`'s labels is not attributed",
  "literature.md §E.6 (second finding)",
  "an error of the documentation (outside the blueprint)",
  "`docs/architecture.md` uses CC-S, CC-C, WC as defined by Kolozyan, Sorger, Hicks, Chaliasos (arXiv:2607.23752, §VI-A) without citing it.",
  "`docs/architecture.md:101, 128, 426-433`; `git grep 2607.23752` empty",
  "add the attribution sentence (literature.md §E.6)",
  "paper"),

# ============================================================ NOTE

# --- master theorems and error (note)
F("note", 3, "error",
  "The protocol's knowledge soundness is non-adaptive in the statement",
  "boundary-adaptor.md §G.17; §B.3",
  "—",
  "ArkLib's games quantify over the input statement outside the probability, while T7's public input has a prover-chosen part; adaptive statement soundness in the random-oracle model is not given by the per-statement theorems.",
  "ArkLib `Security/Basic.lean:299-323` (`dca90385`); `architecture.md:191-195, 357-358`; `cpu/mod.rs:712`",
  "record in the blueprint's out-of-scope list that it is T7's to state",
  "paper"),

# --- seams
F("note (gt-table-pub); a conclusion (code-spine)", 3, "seams",
  "The spine's slot does not pin the protocol: a phase that reads the whole oracle fills it",
  "gt-table-pub.md §8 Notes, §6 E.4 item 6; code-spine.md §0 item 2, §D.3 (d)",
  "—",
  "Faithfulness is not in the slot's type: a zero-round phase whose verifier reads the whole stack through the evaluation oracle and decides the input seam itself inhabits `Phases.Security` at error 0. What pins the phases to leanVM is outside the oracle protocol (an error bound, the phases' definitions, Layer 12's fixture).",
  "`Spine/Compose.lean:77-78`; code-spine §D.3 (d) (paper)",
  "—",
  "cited-checked (gt-table-pub part); paper; unverified (the probe of code-spine §D.3 (d) was not run)"),
F("note", 3, "seams",
  "The instance is data the theorems trust; only the toy's relation is known inhabited",
  "code-spine.md §F \"The instance is data the theorems trust\"; §C.1, §C.2, §D.4",
  "a deliberate deviation (the wall), to keep with the theorem it owes",
  "A layout may alias columns and empty the relation (`toyAlias` is an instance with an empty relation), and the master theorems hold of such instances; non-vacuity for leanISA is `m3Holds_stackOf` (Layer 3), faithfulness Layer 12's fixture.",
  "probe `P2Relation.lean` (`toyAlias`; exhaustive `#guard` over a small range)",
  "append to \"What the spine fixes\" item 1 that the instance is trusted data (code-spine.md §F)",
  "probe-run (emptiness: guard plus paper)",
  "Related: [[comap]] (`Layout.comap` aliasing); [[flockabs]] (`aux := True`)."),

# --- setup
F("note", 3, "setup",
  "Seven disagreements between specification, Rust and Python in the setup, commitment and bus; none between the two verifiers",
  "gt-bus.md G15; §A.6",
  "an error of a source (the specification silent or in another order); the blueprint follows the Rust on each, rightly",
  "The rate is announced with the sizes; the roots' order; the seed hashes a constant naming the circuit; checks the specification omits; the last combiner; the Python takes the stacked bytecode table without checking its zero slots; the fingerprint bound `5·2^μ` against `4·2^μ`.",
  "`cpu/mod.rs:66-93, 123, 149`; `08-end-to-end-protocol.tex:55, 68`; `leaf.rs:110`; `05-arithmetization.tex:37`",
  "report to leanVM when reporting is allowed",
  "cited-checked"),
F("note", 3, "setup",
  "The Fiat–Shamir seed binds a constant that cannot be recomputed at the pin",
  "gt-flock-ring.md §8.14",
  "an error of a source (extends the status's F14)",
  "The seed binds `R1CS_DIGEST`, baked as an opaque constant whose recipe needs matrices the module no longer builds; the Python copies the bytes; it has no owner in the blueprint (no theorem depends on its value).",
  "`crates/flock/src/hash.rs:259-275`; `verifier.py:629`; `08-end-to-end-protocol.tex:55`",
  "give the constant an owner (Category B)",
  "cited-checked"),

# --- bus
F("note", 3, "bus",
  "The specification gives no round-by-round analysis of the bus phase",
  "gt-bus.md G17; §D.1",
  "an error of a source (omission)",
  "`gkrError` and the zerocheck charge are the blueprint's own analysis; the specification's only round-by-round theorem is `thm:rbr` (Annex B, the opening), and the Rust asserts only a coarse sum.",
  "`b-polynomial-commitment-scheme.tex:139-152`",
  "—",
  "cited-checked; paper",
  "gt-table-pub (§5 D.1) says the same of the table sumcheck and the public input; it named the theorem B.2, corrected to B.7 (`thm:rbr`) by the check."),

# --- table sumcheck
F("note", 3, "table",
  "The specification's batching error is loose by one, gives no error for the recycled point, and does not say which coefficient is dropped",
  "gt-table-pub.md §8 Notes; §5 D.1, D.2",
  "an error of a source (the specification)",
  "The specification charges `(ν_side + B)/|E|` while its own Corollary 3.9 gives `(ν_side + B − 1)/|E|`; the dossier wrote Corollary 3.7 (corrected by the citation check).",
  "`05-arithmetization.tex:155`; `03-proving-primitives.tex:67` (`cor:idtest`)",
  "report to leanVM",
  "cited-checked; paper"),
F("note", 3, "table",
  "Stale comments in the Rust on the round message",
  "gt-table-pub.md §8 Notes, §2 A.4; verify-gt-table-pub.md §4 item 3; verify-gt-bus.md §4 item 5",
  "an error of a source (Rust comments)",
  "`constraints.rs:24` says the round polynomial is \"sent WHOLE, at four nodes\", `:265-266` that `h(0)` is derived; the checks add `:26` and `:257-260`. The code sends three coefficients and derives `c₁`.",
  "`constraints.rs:24, 26, 257-260, 265-267`; `fiat_shamir/src/transcript.rs:63-71, 291-299`",
  "report to leanVM",
  "cited-checked"),

# --- public input
F("note", 3, "pub",
  "The public-input message type is wider than the transcript",
  "code-pubinput.md §G.5",
  "—",
  "The message is a list whose length only the check fixes; the transcript has exactly two scalars, so Layer 12 must serialize without a length prefix.",
  "`PublicInput.lean:96-99, 136-137`",
  "with the deployed phase, the words' equation's pattern match rejects a wrong length",
  "paper"),

# --- Flock
F("note", 3, "flock",
  "The pinned Rust prover of Flock is not perfectly complete",
  "gt-flock-ring.md §8.12; §4.1",
  "an error of a source (the Rust prover); the Lean honest prover deliberately deviates",
  "At `r_eq = 1` the Rust prover emits a proof its verifier rejects; the specification's protocol is perfectly complete; `baseProver_complete` is owed for the Lean prover, and the Rust-proof fixture is unaffected.",
  "`crates/flock/src/zerocheck.rs:116-118`; Python probe 9.2 (re-run by the check)",
  "record in `docs/leanvm-target.md`",
  "cited-checked; probe-run (Python)",
  "Bears on the disagreement between [[complerr]] (lib-arklib §G.2) and [[test20]]."),
F("note", 3, "flock",
  "Stale comments in the Rust on what binds the counter and the flags",
  "gt-flock-ring.md §8.15; verify-gt-flock-ring.md §4 item 8",
  "an error of a source (Rust comments)",
  "Comments say the bytecode binds the counter and flags; the table reads the metadata cell from memory, as the specification says. The check adds two more stale comments (`zerocheck.rs:389-390`, `hash_flock.rs:8-9`).",
  "`cpu/mod.rs:568-570` (reads \"bind through bytecode\", corrected by the check), `:619-621`; `tables.rs:904-907`",
  "the Lean cites the table",
  "cited-checked"),

# --- opening and compilation
F("note", 3, "opening",
  "A weighted claim carries the `2^μ` cube values of its weight",
  "gt-flock-ring.md §8.16",
  "—",
  "`Weight.onCube` is a vector of `2^μ` elements of `E` (`μ` up to 28): fine as a specification, but an executable verifier would build a table no deployed verifier builds; the ring-switching weight's identity is owed by the Flock roadmap.",
  "`Spine/Seams.lean:103-109`; `pcs/src/ring_switch.rs:63-66`",
  "—",
  "cited-checked"),
F("note", 3, "opening",
  "The one coding-theory input is a preprint theorem with a sketched proof",
  "literature.md §C.4 (first finding)",
  "— (a fact about the assumption)",
  "[BCHKS25] Theorem 4.6 is in a single ePrint version (2025-11-06) with a one-paragraph proof; peer review is pending, and ArkLib's statement is admitted.",
  "[BCHKS25] §4.3; blueprint `:153-155`, `:1176-1177`",
  "say so at the out-of-scope item and at `McaJohnson`",
  "paper"),
F("note", 3, "opening",
  "Three readings of the constant in Theorem 4.6; leanVM and ArkLib use the printed one",
  "literature.md §C.4 (second finding); §C.3 item 4",
  "none needed",
  "`McaJohnson` must be stated with the printed parameter (as ArkLib's admission is); Flock's paper quotes a stronger bound than the printed theorem.",
  "Annex B `thm:mca-johnson` (`b-polynomial-commitment-scheme.tex:176-185`); `whir_config.rs:431-444`",
  "none to the blueprint; record in the report",
  "paper"),
F("note", 3, "opening",
  "A stale comment in the pinned Rust on level-0 grinding",
  "literature.md §G.1 (bullet \"Grinding\")",
  "an error of a source (Rust comment)",
  "`whir.rs:1210` says level 0 has 0 grinding bits in production; the production derivation and its tests set every level to 17; the blueprint follows the code.",
  "`crates/pcs/src/whir.rs:1210, 2231`; `whir_config.rs:915, 1017`; blueprint `:1163`",
  "report to leanVM",
  "paper"),

# --- adaptor
F("note", 3, "adaptor",
  "Knowledge transport along the adaptor is three lines in the event form",
  "code-spine.md §F \"Knowledge transport\"; §D.7",
  "an error of the blueprint (it says the transport is not proved and has no consumer)",
  "The probabilistic transport of knowledge along a refinement is provable now without converting provers, and Layer 13 consumes it; what T4 waits on is ArkLib's round-by-round to plain implication.",
  "blueprint `:582-586`; probe `P6Surface.lean` (`knowledge_transport`)",
  "move the theorem into `ToArkLib/Refinement.lean`; reword `:582-586` (code-spine.md §F)",
  "probe-run"),
F("note (docs-debt); part of a conclusion (boundary-adaptor §F)", 3, "adaptor",
  "The completeness base theorem composes leanISA's existence theorem, where `architecture.md` says witness generation",
  "docs-debt.md §H.19; boundary-adaptor.md §F, Summary item 6",
  "a deliberate scope choice not written down as a deviation from `architecture.md`",
  "`baseProver_complete` composes the existential `constraintCompleteness`; `architecture.md` says T4's completeness composes T2 (the witness generator) with the honest prover. boundary-adaptor adds two more points where the obligation map is not met: no resource conditions are recorded, and the hash assumption (BLAKE2s as a random oracle) is nowhere an explicit hypothesis.",
  "blueprint `:147-148`, `:1255`; `architecture.md:273-275`",
  "one sentence in Layer 13 (docs-debt.md §H.19); the resource and hash points are [[basecompl]] and [[wfb]]",
  "paper",
  "Two dossiers."),
F("note", 3, "adaptor",
  "T4 drops the extracted witness that T6 needs",
  "boundary-adaptor.md §G.16; §F",
  "—",
  "The base soundness theorem concludes only `∃ t, ValidExecution`, a statement about a language; recursion (T6) needs the extracted witness and `AssignmentRepresents`.",
  "`architecture.md:332-335`",
  "the pointwise `execution_of_extracted` of [[wfb]] (boundary-adaptor.md §G.3)",
  "paper"),
F("note (leanISA's, out of scope)", 3, "adaptor",
  "`constraintCompleteness` needs a resource hypothesis of its own",
  "boundary-adaptor.md §G.18; §C",
  "—",
  "`Caps` bounds every table by `2^32` rows while `ValidExecution` bounds only `κ`; a halting run visits distinct states, so a run of more than `2^32` steps of one opcode has no satisfying witness.",
  "`Arithmetization/Statement.lean:257`; `Semantics/Execution.lean:108-115`",
  "report to the leanISA roadmap (`bp:1433-1441`)",
  "paper (the distinct-states argument is not a Lean proof)"),
F("note", 3, "adaptor",
  "The zkVM verification literature is almost entirely constraint-level",
  "literature.md §F.3",
  "—",
  "Claims about the proof system must be phrased relative to that baseline: once proved, leanerVM's master theorems would be the first mechanized round-by-round knowledge-soundness proof of a deployed zkVM's oracle protocol, with the compilation still assumed.",
  "[KSHC26] §VI-C",
  "report wording",
  "paper"),

# --- libraries
F("note", 3, "libs",
  "Locally re-implemented objects that ArkLib has (`passThrough`, `sendOracle`)",
  "lib-arklib.md §G.8",
  "—",
  "`Component.passThrough` is ArkLib's `ReduceClaim.oracleReduction` with the identity oracle map; `Component.sendOracle` is `SendSingleWitness.oracleReduction` (completeness admitted); the local versions are justified by the named form, but `PassThrough.lean`'s docstring does not name `ReduceClaim`.",
  "ArkLib `ReduceClaim.lean:282-323, 441`; `SendWitness.lean:395-443`",
  "name `ReduceClaim` in the docstring",
  "paper"),
F("note (retired)", 3, "libs",
  "The eager `Fintype BF64` blocked every executable at the old pins; retired at `144c5aa`",
  "lib-others.md §G.6; §B.3, §F.3",
  "a deviation forced by an upstream library; retirement condition met (CompPoly #331)",
  "No executable verifier or differential test was possible at the old pins; whether `lake test` can again be an executable is for the owner to check.",
  "`leanisa-status.md:753-769`; CompPoly `290c351`",
  "the owner checks `lake test`",
  "paper"),
F("note (retired)", 3, "libs",
  "`simp` misread `K` arithmetic at the old pins; the kernel rejected the result",
  "lib-others.md §G.7; §H.7",
  "a deviation forced by an upstream library (`abbrev BF64 := BitVec 64`), retired by CompPoly #329",
  "`simp` elaborated false statements about `K` (reading XOR as addition modulo `2^64`); the kernel rejected them and the axiom audit would have too.",
  "probe `NumeralHazard` (exit 1, expected)",
  "— (retired)",
  "probe-run (old pins)"),
F("note", 3, "libs",
  "Numerals in `K` changed meaning at the new pins",
  "lib-others.md §G.8; §F.3",
  "an upstream change adopted; a documentation hazard",
  "`(2 : K)` is `x` at CompPoly `3468b38c` and `0` at `572f9973`; #61 converted the fixtures but left a test comment saying \"`[1, 2, 3, 4]`\" and \"`2 = x`\"; every later probe must write words as `K.ofBits`.",
  "`tests/LeanerVMTests/Protocol/Field.lean:25-26, 37-38` at `144c5aa`",
  "fix the comment; write `K.ofBits` in probes and fixtures",
  "paper (scan)",
  "code-layer1 §H and code-spine §G record the same for their probes."),
F("note (unverified)", 3, "libs",
  "ArkLib's multilinear bridge is likely unimportable at the new pins",
  "lib-others.md §G.9; §F.2",
  "forced by upstream version skew",
  "`CompPoly.CMlPolynomialEval.eval_zero` is declared both in CompPoly `572f9973` and in ArkLib `7653a901` (whose own CompPoly pin lacks it).",
  "CompPoly `Multilinear/Basic.lean:719`; ArkLib `ToCompPoly/Multilinear/Basic.lean:45`",
  "elaborate a file importing both before a phase uses the bridge; report upstream if it fails",
  "unverified"),
F("note", 3, "libs",
  "The local counting bound is redundant with VCVio at the new pin",
  "lib-others.md §G.10; §F.1",
  "a duplicate of upstream after the pin moved",
  "VCVio `a4232d08` has `SampleableType.prEvent_uniformSample_le_div_iff`, which covers `probEvent_uniformSample_le_of_card_le`.",
  "VCVio `NativeMeasure.lean:127` at `a4232d08`",
  "use the upstream lemma; keep or upstream the subsingleton form",
  "paper (reading)"),
F("note", 3, "libs",
  "The Layer 0 module's comments cite the roadmap, layer numbers and a letter code",
  "docs-debt.md §H.17; §B.5 item 13",
  "—",
  "`Field.lean`'s docstring cites \"Protocol roadmap Layer 0\", \"(leanISA status finding P3)\", \"Layer 11\", against the convention that comments cite the specification; at `144c5aa` it says VCVio comes \"through\" ArkLib though it is now direct.",
  "`LeanerVM/Protocol/Field.lean:18, 29, 31, 37, 66`",
  "rewrite the docstring (docs-debt.md §H.17)",
  "paper"),

# --- Layer 1
F("note", 3, "layer1",
  "`Layout.comap` accepts a non-injective renaming, so a layout can alias columns",
  "code-layer1.md §G.10 (first bullet); §C.4",
  "—",
  "Three columns can be read off one block; completeness of the adaptor catches it; an injectivity hypothesis in Layer 3 is optional.",
  "probe `ValuesProbe.lean` (`aliased`)",
  "optional `Function.Injective f` for `leanIsaInstance`'s map",
  "probe-run",
  "Related: [[trusted]] (the instance as trusted data, code-spine)."),
F("note", 3, "layer1",
  "Unused or duplicated Layer 1 declarations",
  "code-layer1.md §G.10 (second bullet); §E proposals 2-5",
  "— (audit surface)",
  "`prodVars` and its two lemmas, `unstack_eval`, `stack_eval_ambient_zero`, `stackColumn_eval(_ambient)`, `bytecodeSlotColumn`, `slice_bytecodeColumn`; `evalMle_lagrangeBasis` duplicates CompPoly's `eqTilde_eq_prod`.",
  "probe `DuplicatesProbe.lean`",
  "make private or delete (code-layer1.md §E)",
  "probe-run (outside `lake`)"),
F("note", 3, "layer1",
  "Disagreements between leanVM's sources on the witness stack",
  "code-layer1.md §G.10 (fourth bullet); §B.2, §B.6",
  "an error of a source (the specification); the blueprint follows the Rust and the Python",
  "The specification's `M = ⌈log₂ N⌉` has no floor or ceiling (the verifiers bound it to `[15, 28]`) and no tie rule (both verifiers break ties by column index); the Rust evaluates the program's share per column, the Python as one stacked evaluation (equal on the Lean column).",
  "`witness.rs:97`; `verifier.py:890`",
  "—",
  "paper",
  "Related: gt-bus G15 (its sixth item)."),

# --- documentation
F("note", 3, "docs",
  "Two dispositions of the earlier spine review are met only in part",
  "code-spine.md §F \"Two statements the earlier review's disposition\"; §0 item 3, §D.3 (a)",
  "— (an error of an earlier review)",
  "The earlier review's `rfl` test \"for any `A` and `S`\" holds for zero-round phases only; the reason there is no `trivSecurity` is that none exists: the pass-through bus phase's `Phase.Security` type is empty (proved), where the test's docstring only asserts it.",
  "`docs/reviews/protocol-spine.md:36, 39`; probe `P5PassThrough.lean` (`no_security`)",
  "none (the review file is a handoff)",
  "probe-run"),
F("note", 3, "docs",
  "A review's tracker edits were never applied, while its handoff says \"met\"",
  "docs-debt.md §H.18",
  "—",
  "The Layer 1 review left two edits for GitHub (the L1 line and the open-PR table of issue 12); neither was made.",
  "`docs/reviews/protocol-layer1.md:211`",
  "tracker edits a review asks for are made in the pull request that meets it (docs-debt.md §G.1)",
  "paper"),
F("note (an observation of the citation check)", 3, "docs",
  "Blueprint line numbers shift by four at `HEAD`; the upgrade changed more than the pins table",
  "verify-gt-table-pub.md §4 item 1",
  "—",
  "At `8d3ea7d` the blueprint has a new four-line paragraph after line 51 and a rewritten row \"Module system\"; every citation at or after line 315 is +4 at `HEAD`; this contradicts the brief's §8 (\"pins table only\").",
  "`git diff b435631 HEAD -- docs/roadmap/protocol-blueprint.md`",
  "the report states that citations are at `b435631`",
  "cited-checked"),

# ============================================================ PART 2: NEGATIVE RESULTS
# N(dossier + section, what was checked and found right, how, caveat)

N("gt-table-pub §0 item 1, §2", "The table sumcheck's transcript agrees across specification, Rust and Python: one challenge `ξ`, `τ_max` rounds of three field elements, a final message of 104 values, one final check, a derived target.", "reading; cited-checked", "")
N("gt-table-pub §4 C.1", "The blueprint's table-sumcheck conventions match the ground truth: variable order, joining round, padding (`padHigh`, `evalMle_padHigh` give the Rust's factor), degree, powers of `ξ`, derived target, claim-pool order, the third public claim with value 0, the limbs as strided claims.", "reading; cited-checked", "the final message matches only for the six opcode tables ([[tables]])")
N("gt-table-pub §0 item 3, §5 D.2", "The blueprint's errors `(B+2)/|E|` on `ξ` and `3/|E|` per round are correct, tight and on the right challenges.", "paper", "")
N("gt-table-pub §2 A.4", "Checked and agreeing across the three sources: the moment of every challenge; the power assignment; the three sides and their order; the order of the 104 values (`tables.rs:436-863` against `verifier.py:823-834`); the slot of each BLAKE2s limb; the pool order.", "reading; cited-checked", "")
N("gt-table-pub §2 A.4", "The Rust-only guard `zeta.len() < n` is unreachable (`μ_bus ≥ τ_max + 1`); nothing to model.", "reading", "")
N("gt-table-pub §5 D.4", "The public input's per-limb error `1/|E|` is correct, tight and on the one challenge (attained by the test `PublicInput.lean:106-110`).", "paper; repository test", "")
N("gt-table-pub §8 Notes", "Perfect completeness needs no exceptional-challenge clause in the table sumcheck and the public input (the only inverse in the prover is of the constant `g + g²`).", "paper", "")
N("verify-gt-table-pub §1", "301 citations checked; no quotation misquoted; the load-bearing quotations (the Rust verifier loop, the public-input checks in Rust, Python and the guest, `BusVerify`, the tex, ArkLib `RoundByRound.lean`, the spine's blocks) are verbatim.", "citation check", "four numbering corrections and two wrong lines (Dossiers processed)")

N("gt-bus Summary item 1, §A.6", "Specification, Rust and Python agree on the transcript of the setup, the commitment and the bus phase, up to the specification's omissions; the Rust and Python verifiers accept the same transcripts in these phases.", "reading line by line (not a differential test)", "")
N("gt-bus §E.5", "The spine is right on the bus: `tuples` takes every row of every flush and boundary block of a side; `Balanced` is a permutation of 16-tuples, separator included; `CountsNonzero` covers every cell of every listed column; `Seam.commit` is `M3Holds` of the oracle (`Iff.rfl`); `Seam.bus` carries the public lines and `aux`; the toy's tests make each clause fail alone.", "reading; cited-checked", "")
N("gt-bus §E.3", "Every framework block of leanVM (state, memory, bytecode; seed and finalization) is expressible as a `BoundaryBlock`; the boundary depends on the program and the sizes, never on the public input.", "reading; cited-checked", "the instance is then not `Ensemble.toM3` of the ensemble ([[toM3]])")
N("gt-bus §F", "Status findings confirmed at the pin: one scalar root for push and pull (F3, but an agreement, not a divergence), the count tree holds only the tables' count columns (F11), ties put the shared columns first (F17), the caps and stacking bound (F15), padding leaves 1 and stack padding 0.", "reading; cited-checked", "")
N("gt-bus §C", "The blueprint matches: the seed; one `(α, β)` message; radix and parity; `R_c ≠ 0`; one root; the derived remainders as linear claims; the count tree; the padding; the fingerprint; the layer check; `busError` on `(α, β)`; acceptance tests 1, 2, 3, 4, 15, 17.", "reading; cited-checked", "test 18's clause is loose; test 28 is incomplete ([[sideconds]])")
N("gt-bus §C", "Deliberate deviations to keep: the sizes index the instance instead of being a message (owes absorption before the root and a uniform bound); the commitment is sent as the oracle (Layers 11, 12 owe the compilation); the verifier's assertions become layout lemmas (owes four lemmas about `leanIsaInstance`, none listed in Layer 3); the round identity is checked in the oracle protocol (owes `RoundPoly.decode`).", "reading", "the four lemmas are not listed in Layer 3")
N("gt-bus §E.2", "The multiset lemma (Lemma 5.2) holds as used; `CountsNonzero` against `R_c ≠ 0` is exact.", "paper", "")
N("gt-bus §H.1", "Python probe: an honest GKR prover written from the specification is accepted by the pinned Python verifier; `ζ` never contains the last combiner.", "probe run; re-run by the check with identical output", "")
N("verify-gt-bus §1, §4 item 7", "314 citation rows checked (about 400 references); no quotation misquoted; no finding weakened by the corrections.", "citation check", "")

N("gt-flock-ring §2.6, §10", "The Flock transcript: fifteen steps, three sources, no disagreement; one equality check (the lincheck terminal identity); Flock commits nothing of its own and the verifier queries nothing during the phase.", "reading; independent check agrees (stream count `162 + 2·k_batch`, `2·k_batch + 25` challenges)", "")
N("gt-flock-ring §10", "The blueprint's strided limb claims (`:841-846`) match `stack_open.rs:84-97, 305-323` and `verifier.py:892, 295-302`.", "reading; cited-checked", "")
N("gt-flock-ring §10", "The claim pool order (`:324`: ring-switched claim first, then bus, table, public-input claims) matches `cpu/mod.rs:656-667`, `stack_open.rs`, `verifier.py:1413`, `08:98`.", "reading; cited-checked", "")
N("gt-flock-ring §10", "The Fiat–Shamir seed convention (`:325`) matches `cpu/mod.rs:82-93`, `verifier.py:1366-1368`.", "reading; cited-checked", "")
N("gt-flock-ring §10", "The strong reading of `aux` (status decision 12) is right; a predicate on the limb slots alone has no honest prover; the spine's docstrings carry it.", "reading", "the constant position must be added ([[constone]])")
N("gt-flock-ring §10", "The phase order `pub ⟫ flock ⟫ opening` matches `cpu/mod.rs:745-768`, `verifier.py:1397-1413`.", "reading", "")
N("gt-flock-ring §1 item 4, §5.2", "`flockError_le` is right for a fixed committed polynomial: `(4·k_batch + 163)/|E|` is Annex C.7's sum and matches the Rust's parameters term by term; `2^32/|E|` bounds the ring-switching degree.", "paper", "list size after compilation ([[listsize]])")
N("gt-flock-ring §1 item 4", "The partially fixed zerocheck's hypothesis holds for the pinned constants: the 128 equality weights of the seven fixed coordinates are independent over `F_2` (rank 128).", "Python probe; re-run by the check", "")
N("gt-flock-ring §10", "`Blake2sRowsValid` is what the adaptor must reach; blocks and rows correspond one to one (no padding block).", "reading", "")
N("gt-flock-ring §1 item 6, §6", "Ring switching serves the bit witness only; `K`-valued columns need none; in leanVM it sends nothing, checks nothing and draws six challenges.", "reading; independent check agrees", "")
N("gt-flock-ring §1 item 3, §4", "Perfect completeness of the specification's Flock protocol is attainable (a prover sending the true coefficients).", "paper; Python probe 9.2", "the Rust prover is not perfectly complete ([[rustprover]])")
N("verify-gt-flock-ring §1", "About 381 citations checked; all eight independent checks agree with the dossier; both Python probes reproduce.", "citation check", "")

N("code-spine §0 item 1; probe P1", "No theorem of the spine is wrong for what it states; every stated theorem uses only the kernel's three standard axioms.", "probe-run (old pins)", "")
N("code-spine §C.1", "`M3Holds` says what the specification's accept list says, clause by clause (`05:10-16, 101, 111`; `06:74-78`; `08:29-33, 100`).", "reading", "")
N("code-spine §D.1; probe P2", "`Balanced` handles the side filter, the row ranges and multiplicity (a tuple pushed twice and pulled once; pushed twice and never pulled, which a field-summed balance accepts).", "probe-run", "")
N("code-spine §D.2; probe P3a", "Each seam is inhabited and refuted conjunct by conjunct.", "probe-run", "")
N("code-spine §D.5, §D.6; probes P3b, P1", "The commit phase's state function and extractor are as documented; the extractor chain is computable.", "probe-run", "")
N("code-spine §E.1", "The blueprint's spine sketch (`:442-554`) matches the code name for name and signature for signature; the differences listed change no statement.", "reading", "the interface list omits load-bearing names ([[publicnames]])")
N("code-spine §E.3 row 25", "The spine's five modules and `ToArkLib/` import nothing from the arithmetization.", "git grep", "`Protocol/Basic.lean` does ([[basic]])")
N("code-spine §E.2", "`Seam.done` equals `Set.univ`: same set, different spelling.", "probe-run", "")
N("code-spine §0 item 9, §C.7", "`Refinement`'s two witness universes are independent.", "reading", "")
N("code-spine §E.3", "Acceptance tests 26 (seams are the contract), 27 (the toy is honest) and 28 (degree at the seam) are met.", "reading", "26 says nothing about content; 28 is met at the cost of a guard ([[busseam]])")
N("code-spine §C.6", "The quantification over the oracle state `σ`, `init`, `impl` is without content (one `impl`, never called); it is forced by ArkLib.", "reading", "it costs three binders in eleven load-bearing declarations")
N("code-spine §B", "The audit surface was measured: 70 declarations and 217 code lines for completeness; 76 and 248 for knowledge soundness in its existential form; 100 and 354 in the named form.", "count script at `b435631`", "")

N("code-pubinput §G Negative results, §B", "The public-input phase's schedule, challenge, number of scalars, point `(r, 0, …, 0)`, honest values, three claims and their order, rejection and error agree between the specification, the three implementations and the Lean.", "reading line by line", "the check itself differs ([[pubdeployed]])")
N("code-pubinput §G Negative results", "The bit order of `linePoint` is proved (`eval₂Mle_linePoint`) and separated from the other order by a two-variable test.", "reading", "")
N("code-pubinput §G Negative results", "`1 + r` against `1 - r` is joined by `CharTwo.sub_eq_add`, correct in characteristic two.", "reading", "")
N("code-pubinput §F", "The error is charged to the right challenge and is tight.", "reading", "")
N("code-pubinput §F", "No admitted ArkLib theorem is in the closure of the phase's two bundles.", "on a verbatim copy", "`#print axioms` on the original file was not run")
N("code-pubinput §F, §C.3", "The knowledge state function's three rounds are right and none is trivial.", "probe-run", "")
N("code-pubinput §E", "`sent` is no part of the relation (`M3Holds` does not read it).", "reading", "")
N("code-pubinput §C.6-C.8", "What the theorems do catch: pooling the prover's values unchecked, checking the first value only and pooling the prover's values, not pooling an unsent line's claim; each refuted in Lean on a concrete instance.", "probe-run", "")

N("code-layer1 §B.1", "The cube's bit order and the order of points agree with leanVM.", "reading", "")
N("code-layer1 §B.2", "Stacking offsets and selectors agree: on the pinned Python verifier's real layout (92 blocks, `stack_log = 22`) `Blocks.offset` reproduces all 92 offsets.", "Python and Lean probes (`offsets.py`, `OffsetsProbe`)", "the tie order is supplied by nobody ([[tieorder]])")
N("code-layer1 §B.3, §B.4", "Padding values, the one-padded leaf identity (equation (2) of §5.4) and back-loaded padding agree.", "reading and probes", "")
N("code-layer1 §B.5", "The index column agrees (generator `g = x`; coordinate `k` carries `g^(2^k)`).", "reading", "")
N("code-layer1 §B.6", "`bytecodeColumn` of a sixteen-instruction program covering every opcode and `DEREF` mode equals, cell for cell (256 cells), the table of a transcription of the Rust encoder, and its extension at `(ζ, α)` equals `verifier.py:566`.", "probes `ValuesProbe`, `values.py`", "the Rust encoder was transcribed, not executed")
N("code-layer1 §B.7", "A column claim as a weighted claim on the stack agrees.", "reading and probe", "")
N("code-layer1 §C, §0 item 2", "No Layer 1 theorem is false or vacuous; the hypotheses `B.total ≤ 2^μ`, `Antitone size` have inhabitants; seventeen declarations depend only on the three standard axioms.", "reading; `#print axioms` probe", "")
N("code-layer1 §D.1", "No file of `LeanerVM/Protocol` imports Clean or `LeanerVM.Semantics` directly; no phase imports `FixedColumns`.", "git grep", "`Basic.lean` imports the arithmetization ([[basic]])")
N("code-layer1 §D", "The four `ToCompPoly` modules are generic; CompPoly at both pins shares only `eqTilde_eq_prod` and `eqTilde_append` with them; ArkLib at both pins has none of them.", "reading; `DuplicatesProbe`", "")
N("code-layer1 §F", "The Layer 1 sketch matches the code declaration by declaration.", "reading", "")
N("code-layer1 §E", "Today an auditor of the master theorems reads no Layer 1 declaration (17 definitions, 61 lines, become trusted with the adaptor; about 8 more with the executable verifier).", "count", "")
N("code-layer1 §G.10, §H", "`idxColumnEval` is efficient (binary exponentiation in CompPoly's `K`); the upgrade to `144c5aa` changed only proofs in Layer 1, and the tests' numerals were rewritten as `K.ofBits n`, the same words, so every test keeps its meaning.", "reading; git diff", "")

N("lib-arklib §G.9", "ArkLib's `KnowledgeStateFunction`, `rbrKnowledgeSoundnessWorstCaseWith`, `perfectCompleteness`, `GuardedForm`, `OutputIsPure` read in full at `dca90385`: no way to satisfy the named worst-case form at error 0 for a verifier accepting a false statement except through the extractor or an empty output-witness type (visible in the statement).", "reading", "")
N("lib-arklib §C.1, §G.9", "The port `KnowledgeAppend.lean` differs from ArkLib PR #615's file only in headers, the module system, docstrings and dropped wrappers.", "line-by-line diff", "")
N("lib-arklib §G.9", "The composed error is per challenge with no additive term, and the seam round is handled (`backward_right`, `extractMid_seam`).", "reading in full", "")
N("lib-arklib §B.1, §G.9", "Every `#print axioms` on leanerVM's declarations (master theorems, both phases, composition, port) reports the three standard axioms only.", "probe `AxiomsLeanerVM` (old pin)", "")
N("lib-arklib §D.2", "The named form matches the literature's round-by-round knowledge soundness (Block et al. 2023, Definition 3.13) in its worst-case-per-prefix form and per-round errors.", "reading", "the extractor may be any function ([[existential]])")
N("lib-arklib §D.4", "Non-vacuity of the notion: an accept-everything verifier has no knowledge state function and is not knowledge sound at error 0 (it is at error 1, as every verifier is).", "probe `NonVacuity`", "")
N("lib-arklib §D.1", "The transcript-level half of the plain reading of the master theorem is proved.", "probe `PlainReading`", "")
N("lib-arklib §D.6", "The spine's named extractor (\"return the first message\") compiles.", "probe `Extractors`", "")
N("lib-arklib §F.1-F.4", "At `7653a901` the spine's vocabulary exists with the same shapes; the new probability notation is notation only; the two theorems of `KnowledgeAppend.lean` differ from `b435631` only in the spelling of three probabilities; the admitted theorems (sumcheck, composition, round-by-round to plain, context lifting, Fiat–Shamir completeness) are exactly as admitted as at `dca90385`; the port is still needed.", "reading; baseline comparison by name; git diff", "")
N("lib-arklib §B.2", "Most rows of the blueprint's ArkLib table name existing, proved objects at the stated place.", "reading and probes", "the exceptions are [[arklibtable]]")

N("lib-others §B.4; probe FieldFidelity", "`K`, `E`, `y`, `ofK`, `g` agree with the specification, Rust and Python bit for bit (moduli, bit order, limb order, embedding, generator, product formula); the compiled arithmetic reproduces eleven Rust reference products.", "probe-run (old pins)", "a re-run at the new pins needs `K.ofBits` literals")
N("lib-others §B; probe Layer0", "Irreducibility, field structure and `|E| = 2^192` are proved in CompPoly without `native_decide` (a Rabin certificate checked by `rfl`), on the standard axioms.", "probe-run", "")
N("lib-others §E.1", "Both samplers are uniform by proof (uniformity is a class law of `SampleableType`); `Pr[= x | $ᵗ E] = 2^-192`; the `K` diamond is definitional at the old pins and disappears at the new.", "probes `Layer0`, `SamplerDiamond2`", "")
N("lib-others §E.2, §E.3", "The column oracle answers the specification's evaluation `q̃(r) = Σ ofK(q_i)·eq(r, i)` in little-endian cube order; `card_E`; `NoOracle`, `OneOracle`, `noOracle_eq` are correct.", "reading and probe", "")
N("lib-others §E.4", "The counting bounds are correct, tight, with load-bearing hypotheses, and the same statement before and after the probability-API port.", "probe `CountingBounds`", "")
N("lib-others §D.3", "The trusted base is the kernel and the three standard axioms, enforced lexically and transitively with a negative control; `#guard` tests are compiled-code evidence, not proof.", "reading", "")
N("lib-others §C.5-C.7", "Clean's balance is vacuous over `K` (unsatisfiable, not merely unsound); leanISA's `BalancedPair` replaces it; unchanged at Clean `42fe4b26`.", "probe `CleanBalance`", "")

N("docs-debt §B.10", "Every local Markdown link and anchor of the 24 tracked Markdown files resolves (150 links).", "probe `check_anchors.py` (re-run)", "")
N("docs-debt §B.10", "Every one of 81 citations into the pinned leanVM sources resolves to an existing range once its crate is known.", "citation probe", "22 are ambiguous as written (`transcript.rs`, `witness.rs`, `lib.rs`, `filler.rs`, drafts)")
N("docs-debt §B.10", "40 of 43 citations into the pinned libraries are exact (old pins).", "reading", "three drifted ([[broken]])")
N("docs-debt §B.10", "All 30 references to numbered acceptance tests point at the intended test.", "reading", "")
N("docs-debt §B.10, §H.3", "The spine's sketch (`:442-554`) agrees with the code; the Layer 8 sketch agrees with `PublicInput.lean`.", "reading; `check_interface_names.py`", "")
N("docs-debt (second pass)", "The body of issue 12 and the hole comment are unchanged since 2026-09-28 14:28 UTC.", "`gh` read; diff against the saved copies", "")

N("literature Summary item 1, §A.3", "\"After Fiat–Shamir the largest bound is what a random-oracle query buys\" is right at its core ([CY24] Theorems 31.2.1, 31.3.1; [BGKTTZ23] Theorem 3.15).", "literature", "the hash term, the list factor and grinding are missing ([[hashcoll]], [[listsize]], [[grinding]])")
N("literature §A.3", "The master theorems are round-by-round (as [BCS16] Theorem 1.5 requires), with per-challenge errors ([CY24] Definition 31.1.2) and a straight-line extractor that reads the oracle ([CMS19] Definition 8.5).", "literature", "")
N("literature Summary item 2, §C.4", "leanVM's PCS regime (Johnson with slack, [BCHKS25] Theorem 4.6) is the right, provable one; Annex B states Theorem 4.6 exactly as printed (term by term at `M = 1`).", "term-by-term comparison", "a preprint with a sketched proof; the Rust's arithmetic and `η` search not checked")
N("literature §B.4", "The known diagonalization attacks ([KRS25], [Fen26]) do not apply: the statement is bound and the trace committed before the first challenge at the pin.", "reading `cpu/mod.rs:78-93, 108-124`, `fiat_shamir/src/lib.rs`, `08:55-73`", "")
N("literature §D.3", "The blueprint's arithmetization references match the specification's `refs.bib`; no missed source.", "literature search", "")
N("literature §E.6", "ArkLib's round-by-round definitions, the `KnowledgeStateFunction` docstring, the basic Fiat–Shamir query and the admitted MCA theorem are textually unchanged between `dca90385` and `7653a901`.", "`git show`", "")
N("literature Summary item 4, §F.3", "The blueprint's cut (a relation on one committed column and an adaptor to the trace relation) matches the only published plan (SP1) and [KSHC26]'s obligations; characteristic 2 forces combinatorial balance, which the blueprint has.", "literature", "")
N("literature §A (search)", "No published theorem states round-by-round soundness with per-round proof of work as a Fiat–Shamir compilation result for multi-round IOPs.", "negative result of a search, not proof of absence", "")

N("boundary-adaptor §H, §A.4", "`M3Holds`'s five clauses against `SatisfiedBy`'s thirteen conjuncts: every conjunct has a source once the caps hypothesis, the boundary lemma, the count derivation and the Flock consequence lemma are in place.", "reading", "the boundary lemma and Flock lemma are missing ([[bridge]], [[flockcirc]])")
N("boundary-adaptor §H", "`w.Constraints` is asserts and lookups only; leanISA emits no lookup and only `JUMP` asserts, so `toM3_constraints_iff` is provable in principle.", "reading; probe `Shapes`", "")
N("boundary-adaptor §H", "The degree bound `d = 2` holds: every flush coordinate of the six tables has degree at most two.", "reading `Tables/*.lean`", "")
N("boundary-adaptor §H, §E.4", "The state boundary is constants only, as `layout.rs:354-358`; the memory and bytecode blocks' committed coordinates are columns of tables whose height equals the block's by construction.", "reading", "")
N("boundary-adaptor §H, §A.4, §A.6", "`Caps` is derivable from admissibility plus the construction of `witnessOf`; `Sizes.ofWitness w = some s` follows from `SatisfiedBy`.", "reading", "")
N("boundary-adaptor §H, §B.2", "The chain names one program and one input throughout; no theorem lets the prover choose either.", "reading", "")
N("boundary-adaptor §H, §D", "The top limb is anchored (agreeing with code-pubinput §D).", "reading; probe `Shapes`", "")
N("boundary-adaptor §H", "`Refinement` accepts a `Type 1` target witness; the pointwise composition of T4 typechecks; `Extractor.Straightline.map` cannot serve.", "probes `Transport`, `UniverseFail`", "")
N("boundary-adaptor §H", "The arithmetization declarations the chain will use, the two master theorems, `bytecodeColumn_eval`, `idxColumn_eval` depend on the kernel's three axioms only (`map_option_valid`: two).", "probe `Shapes`", "")

# ============================================================ PART 3: NOT VERIFIED
# U(dossier + section, claim, status, what would verify it)

U("gt-table-pub §10", "The Rust and Python verifiers behave as read.", "read, not run", "run both on a dumped proof and on the mutations of §3 B.1, B.2")
U("gt-table-pub §10", "The errors of §5 D.2, D.3 and §6 E.3.", "paper arguments", "Layer 4's sumcheck and the bus phase's `Security` with the zerocheck conjunct")
U("gt-table-pub §10", "The finding on the sumcheck's tables.", "a reading of Layer 3's text", "`leanIsaInstance`, when built")
U("gt-table-pub §10", "The combined public-input check has error `1/|E|`.", "paper; one instance tested", "the second phase proposed (code-pubinput proved the key lemma)")
U("gt-table-pub §10", "leanISA's tables have the Rust's column order.", "not checked", "compare `Arithmetization/Tables/*.lean` with `tables.rs:436-863`")
U("gt-table-pub §10", "leanth's `ZerocheckClaim` pattern, which the blueprint's row Seams cites.", "not read (private)", "—")
U("verify-gt-table-pub §1 item 7", "The probes `SeamBusShape` and `SeamBusMember` still elaborate at the new pins.", "could not check (sources identical, numerals only 0 and 1)", "re-run after the rebuild")

U("gt-bus §I", "The Rust verifier and prover (read only); the equality of the Rust and Python verdicts is by reading.", "not run", "a differential test (the repository's own tests compare them)")
U("gt-bus §I, §B", "The attack without the `τ_BLAKE2S ≥ 3` floor.", "not constructed", "a verifier without the cap at `τ_5 = 2`")
U("gt-bus §I, §B", "The public-input phase rejects a public word with a nonzero third limb (defence in depth).", "an argument", "the public-input dossiers (code-pubinput, boundary-adaptor §D)")
U("gt-bus §I", "Not examined: Fiat–Shamir beyond absorption order; the opening; the table sumcheck beyond the seam; the recursion guest.", "out of task", "gt-opening-compile, gt-table-pub")
U("verify-gt-bus §1 item 12", "The Lean probe `BusSeam.lean`'s output, the control copy's failure, `#print axioms Probe.x0_degree`.", "could not check (no Lean run)", "re-run after the rebuild")

U("gt-flock-ring §11", "The Rust prover's behaviour at `r_eq = 1`.", "read and modelled (probe 9.2), not executed", "a Rust unit test on `send_round` and `next_round_poly`")
U("gt-flock-ring §11", "`R1CS_DIGEST` is the digest of the matrices.", "not recomputable at the pin", "the commit the Rust's comment names")
U("gt-flock-ring §11", "The Rust circuit computes BLAKE2s.", "not checked (the Rust tests it, `hash.rs:1121-1170`)", "the theorem of §5.3")
U("gt-flock-ring §11", "`lincheck.rs` beyond 1400, `zerocheck/multilinear.rs` beyond 330, `univariate_skip*.rs` beyond 200.", "not read (off the verifier's path)", "—")
U("gt-flock-ring §11", "The WHIR part of the opening; the recursive verifier's hint `M_lc`.", "out of task", "gt-opening-compile")
U("gt-flock-ring §11", "The sketches `FlockPhase`, `FlockRegion`, `Component.Guarded`.", "proposals, not compiled", "write them")
U("verify-gt-flock-ring §4 item 5", "What in the lincheck prover needs `n_outer ≥ 8` (the floor's reason).", "not checked", "read the lincheck prover")
U("verify-gt-flock-ring", "The Lean probe `NoCheckFlock.lean`.", "not re-run at the new pins", "re-run after the rebuild")

U("code-spine §G", "The relation of `toyAlias` is empty for every stack and statement.", "exhaustive `#guard` over a small range at the old pin; paper", "a theorem `∀ input q, ¬ M3Holds toyAlias input q`")
U("code-spine §G", "`Layout.read` is determined by `extend`.", "paper", "a lemma `read_eq_of_extend`")
U("code-spine §G", "An always-rejecting bundle has no `Phases.Security` on an instance with an inhabited relation.", "a reading of `Security extends Complete`", "a probe with a rejecting zero-round verifier")
U("code-spine §G", "The read-everything phase inhabits `Phases.Security I` at error 0 for every `I`.", "paper (agrees with gt-table-pub §6)", "a probe on an instance with `μ = 0`")
U("code-spine §G", "The probes that use `(2 : K)` at the new CompPoly pin.", "they mean something else there", "re-run `P2Relation`, `P3aSeams`, `P5PassThrough` with `K.ofBits 2`")
U("code-spine §G", "The earlier spine review's validation paragraph.", "not re-run", "`./scripts/validate.sh` on `b435631`")

U("code-pubinput §0, §C.9", "Mutation 6 (claims pooled at a wrong point).", "paper, not written", "write and run after the rebuild")
U("code-pubinput §0, §C.13", "The deployed phase's full `Phase.Security` (mutation 4b).", "paper, not written", "write `deployedSecurity`")
U("code-pubinput §0", "The two-line-instance display for §D.1; `#print axioms` on the original `PublicInput.lean`.", "not run", "run after the rebuild")
U("code-pubinput §C.10, §C.11", "Probes 7a (a wrong check caught by completeness against a fixed prover) and 8 (an extra check caught by completeness).", "written, not run", "run `Probe7a.lean`, `Probe8.lean` after the rebuild")

U("code-layer1 §J", "The Rust bytecode encoder was not executed (compared through a transcription).", "read", "run the pinned Rust `bytecode_table` on the same program")
U("code-layer1 §J", "The proposed strided reader and layout combinator.", "sketched (only the selection lemma is proved)", "build them")
U("code-layer1 §J", "No probe was run at the new pin; `ValuesProbe`, `StridedProbe` need `K.ofBits` rewrites.", "not run", "re-run after the rebuild")
U("code-layer1 §J, §I", "`DuplicatesProbe` and `StridedProbe` ran outside `lake` (the old Lean binary on the `b435631` artefacts).", "run, by a non-standard route", "re-run with `lake env lean` after the rebuild (else §D.2 and §B.8 stand as short paper proofs)")
U("code-layer1 §J", "Not examined: the rest of Layer 3; the leaf stacks' block order in code; the pad cells past the last lane.", "—", "—")

U("lib-arklib §F.3", "The probes at the new pin (written in the old probability notation).", "not re-run", "a mechanical rewrite and a run after the rebuild")
U("lib-arklib §G.4", "`fiatShamir_completeness` is false in general for a protocol whose honest prover fails at the default challenge.", "the dossier's inference", "a counterexample probe")
U("lib-arklib §G.2", "Whether the honest Flock prover fails at `r_eq = 1` (the condition of [[complerr]]).", "left to \"the Flock reviewer\"", "answered by gt-flock-ring §4 and §8.12: the Rust prover does, the specification's does not")

U("lib-others §F.3", "`FieldFidelity` at the new pin with `K.ofBits` literals.", "not run", "re-run after the rebuild")
U("lib-others §E.1", "`instSampleableTypeK` is the only `K` sampler at the new pins.", "by reading", "a probe at the new pins")
U("lib-others §G.9", "The ArkLib/CompPoly `eval_zero` clash.", "inferred", "elaborate a file importing both")
U("lib-others §F.3", "Numerals inside vectors and other shapes at `144c5aa`.", "not scanned", "a wider scan")
U("lib-others §H", "All seven probes at the new pins.", "not re-run", "re-run after the rebuild")

U("docs-debt §H.15", "Whether VCVio's Merkle-tree library fits leanVM's Merkle trees (BLAKE2s, the leaf encoding, pruned paths), and its state at `a4232d08`.", "inference", "read VCVio's library against `fiat_shamir/src/merkle.rs:14-67` at both pins")
U("docs-debt §D", "The counts of letter codes are lower bounds (the pattern skips codes in backticks).", "stated", "a pattern that includes backticks")

U("literature (what I could not open)", "About 22 references read as abstracts only, eight not opened, four through fetch summaries; the SP1, Pico and advisory items from a stopped helper's notes not re-checked.", "—", "open and read them")
U("literature (what I could not open)", "Whether a refereed or Lean proof of [BCHKS25] Theorem 4.6 exists (ArkLib's is admitted at both pins), and whether Haböck's update of [Hab25] exists.", "—", "search again")
U("literature §A.4", "The list size `L_0` at leanVM's production parameters (estimated `2^7` to `2^10`).", "estimate", "the Rust's `validate()` output")
U("literature §E.6", "Whether a cross-role input of the shared BLAKE2s map (a Merkle node against a chain block) is exploitable.", "not analysed", "an analysis of role separation")
U("literature §E.6", "Whether an ArkLib revision after `7653a901` provides a chain-based transform.", "—", "watch upstream")

U("boundary-adaptor §H", "The injectivity of `prog ↦ (prog.logSize, bytecodeColumn prog)`.", "inferred from `entry_injective` and `bytecodeColumn_slot`", "a probe proving it")
U("boundary-adaptor §H, §D", "The counterexample program of §D (`SET_CONSTANT [g^0, y²]`): its two-line stack.", "not built (the load-bearing inequality is proved)", "build the stack")
U("boundary-adaptor §H, §B.3", "The count of admissible size vectors (about `2^34`).", "a hand estimate", "Layer 3's `μ`")
U("boundary-adaptor §H", "`Shapes`, `Transport`, `UniverseFail`, `DefInstance` at the new pins.", "not re-run (only `KnownColumnNew`, `PolyBridgeNew` were re-run at the new pins, and pass)", "re-run after the rebuild")
U("boundary-adaptor §H, §G.18", "A halting run visits distinct states.", "an argument from the determinism of `step`", "a Lean proof")

# ============================================================ CONTRADICTIONS WITH THE BRIEF, as the dossiers report them
CONTRA = [
    ("verify-gt-table-pub §4 item 1", "The blueprint changed at `144c5aa` in more than its pins table: a new paragraph after line 51 and the row \"Module system\"; citations at or after line 315 are +4 at `HEAD` (brief §8 says \"pins table only\")."),
    ("code-pubinput §C.9", "The first `lake env lean` after the merge made Lake re-resolve the manifest and re-clone PolyFun, whose old oleans are gone; from then no probe could run without a rebuild (the restart message said \"nothing else changed\")."),
    ("code-layer1 §J", "The checkout was moved during the task (reflog at 09:18) and `.lake/packages/` switched to the new pins; two Lean probes were then run with the old Lean binary directly on the `b435631` artefacts."),
    ("gt-bus §I", "The specification's round-by-round theorem is in Annex B (`thm:rbr`) and about the opening only, not in §3; the status's finding on the Python caps is false."),
    ("boundary-adaptor §H", "The leanVM checkout is no longer at the pin (`HEAD` `248da071`; brief §8 now records this). boundary-adaptor also reports that `KnownColumnNew` and `PolyBridgeNew` were re-run at the new pins after a rebuild and pass."),
]


# ============================================================ KEYS for cross-references ([[key]] in any text)
KEYS = {
    "busseam": "The bus seam admits statements the deployed table sumcheck cannot serve",
    "buspos": "The real bus phase can fill the spine's bus slot",
    "complerr": "The spine's completeness cannot carry an error",
    "declerr": "The declared error is unconstrained",
    "gkrnorm": "The GKR layer sumcheck is the normalized variant",
    "gkrpos": "The GKR last-layer rounds cost",
    "tables": "The table sumcheck's tables are not distinguished",
    "pubdeployed": "The public-input theorems are about a verifier none",
    "pubcheck": "The check on the public-input message is not load-bearing",
    "flocklimb": "Layer 9's Flock interface consumes the eighteen limb claims",
    "flockcirc": "The instance depends on a Flock interface that depends on the instance",
    "flockabs": "The Flock phase cannot be written over an abstract instance",
    "test20": "Acceptance test 20 files a completeness failure",
    "fsnone": "ArkLib has no Fiat–Shamir or BCS statement",
    "fsother": "Upstream Fiat–Shamir and BCS theorems will be about other constructions",
    "grinding": "The Fiat–Shamir interface omits grinding",
    "pow": "The proof of work is the one verifier check",
    "listsize": "The compiled error omits the list-size factor",
    "wfb": "The base soundness (and completeness) theorems lack `WellFormedBytecode`",
    "basecompl": "The base completeness theorem is false without resource hypotheses",
    "toM3": "The instance is not `Ensemble.toM3`",
    "sizes": "Layer 3's sizes and admissibility statements",
    "strided": "The strided reader of the eighteen BLAKE2s limb columns",
    "sideconds": "Two side conditions a bus phase over an abstract instance needs",
    "canon": "The canonical-encoding checks and the stream-consumption check",
    "toplimb": "The top limb is enforced only through",
    "transport": "Knowledge transport along the adaptor is three lines",
    "leafstacks": "The order of the leaf stacks is nowhere stated",
    "tieorder": "The order of equal-size blocks in the witness stack",
    "test14": "Acceptance test 14 names a tautology",
    "arklibtable": "Names and line references in the blueprint's ArkLib table",
    "trusted": "The instance is data the theorems trust",
    "comap": "`Layout.comap` accepts a non-injective renaming",
    "resource": "`constraintCompleteness` needs a resource hypothesis of its own",
    "computable": "\"Computable\" is not \"efficient\"",
    "sketches": "The per-layer sketches (Layers 4 to 7, 9, 10)",
    "caps": "The status's finding that the Python verifier omits the caps",
    "basic": "`Protocol/Basic.lean` imports the arithmetization",
    "zerocheck": "The zerocheck escape is over-charged",
    "roundmsg": "Sumcheck round messages: four coefficients",
    "rustprover": "The pinned Rust prover of Flock is not perfectly complete",
    "stale": "The status and the tracker describe a repository two merges old",
    "publicnames": "The list of public names is not the public boundary",
    "legacy": "The blueprint plans on a framework ArkLib calls legacy",
    "slotpin": "The spine's slot does not pin the protocol",
    "constone": "The auxiliary predicate must include the constant-one position",
    "existential": "The existential forms of round-by-round knowledge soundness",
    "broken": "Broken names and citations",
    "hashcoll": "The hash-collision term is missing",
    "bridge": "No bridge lemma relates the boundary blocks",
}
