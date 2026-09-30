                                                ZKP Security Tools and Verification:
                                          Coverage, Effectiveness, Adoption, and Challenges
                                                    Arman Kolozyan*                                 Tom Sorger*             Alexander Hicks             Stefanos Chaliasos
                                                Max Planck Institute for                               KTH                 Ethereum Foundation        University of Athens &
                                             Security and Privacy (MPI-SP)                Royal Institute of Technology                                     zkSecurity



                                            Abstract—Zero-knowledge proofs (ZKPs) have become a core              exploit drained roughly $2.1 million [9], and high-severity
                                         technology for privacy and verifiable computing. They are used           ZKP bugs continue to appear in bug-bounty programs [10].
                                         to secure blockchains that handle billions of dollars and identity          In response, researchers and practitioners have developed a
                                         applications dealing with sensitive personal data. However, ZKP
                                         systems are complex, and subtle implementation errors can                growing set of defenses for ZKP implementations, including
                                         completely break their guarantees, letting attackers forge money         static analyzers [11]–[15], SMT-based verifiers [16]–[19], and
                                         or false proofs of identity. Researchers and practitioners have          fuzzers [20], [21]. Given the complexity and security-critical
                                         therefore developed a growing set of bug detection and formal            role of ZKPs, formal verification is becoming increasingly
                                         verification methods to secure these systems. Yet their real-world       important, with recent efforts targeting zero-knowledge virtual
                                         effectiveness and adoption remain unclear.
                                                                                                                  machines (zkVMs), proof systems, and verifier implementa-
arXiv:2607.23752v1 [cs.CR] 26 Jul 2026




                                            In this paper, we aim to shed light on the state of ZKP
                                         security tooling. We first systematize the landscape of these tools      tions [22]–[26]. Nevertheless, the impact of these techniques
                                         and observe that most target Circom, leaving newer DSLs and              remains unclear: tools are often evaluated on curated examples,
                                         zkVMs with limited support. We then evaluate six tools across            formal-verification claims cover only selected components,
                                         70 real-world vulnerabilities and find that while the tools detect       and little is known about adoption in practice.
                                         45.7% of bugs on isolated targets, their effectiveness drops to
                                         19.6% on full codebases, with important vulnerability classes               This paper studies the state of ZKP security tooling and
                                         left unaddressed. We also present the first systematic analysis of       formal verification across five research questions. We combine
                                         formal verification efforts, revealing that current work focuses         a systematization of existing tools, an evaluation of six tools on
                                         primarily on constraint correctness and identifying key gaps and         70 real-world vulnerabilities, a systematic analysis of formal-
                                         risks. Finally, we survey 48 practitioners, showing that develop-        verification efforts, and a survey of 48 ZKP practitioners. This
                                         ment and security remain human-led, LLMs are widely used,
                                         and practitioners prioritize tools with clearer guarantees and           methodology lets us assess which languages tools cover, what
                                         lower integration effort. Overall, our results highlight the need        they detect, which parts of the stack are or could be formally
                                         for better integration of security tooling with the development          verified, and how practitioners use them. Below, we state the
                                         and auditing process, and we provide actionable insights for             research questions and summarize representative findings.
                                         researchers and practitioners.
                                            Index Terms—ZKPs, security, formal verification                       RQ1: What is the current landscape of ZKP security
                                                                                                                  tools? Which DSLs do existing tools support? What analysis
                                                                   I. I NTRODUCTION                               techniques do they use? Which vulnerability classes can they
                                                                                                                  detect, and which classes remain unsupported?
                                            Zero-knowledge proofs (ZKPs) are cryptographic protocols                 Key findings. Current tools focus almost exclusively on Cir-
                                         that let a prover convince a verifier that a statement is                com circuits and concentrate on nondeterminism and related
                                         true, optionally without revealing anything beyond its va-               underconstraint bugs, while leaving newer DSLs, zkVMs, and
                                         lidity [1]. Over the last decade, advances in proof systems              other vulnerabilities weakly supported (Section IV).
                                         and implementations have made ZKPs practical, enabling
                                                                                                                  RQ2: How effective are automated ZKP security tools on
                                         emerging applications such as private payments [2], identity
                                                                                                                  real-world vulnerabilities? What affects their effectiveness?
                                         protocols [3], blockchain scaling through zk-rollups [4], and
                                                                                                                     Key findings. Across 70 real-world bugs, at least one tool
                                         verifiable machine learning [5].
                                                                                                                  detects 45.7% on isolated circuits, but only 19.6% on whole-
                                            These applications rely on strong properties such as succinct
                                                                                                                  project codebases, with errors, timeouts, and compatibility
                                         verification, privacy, and soundness [6]. Yet ZKP implemen-
                                                                                                                  failures limiting practical effectiveness (Section V).
                                         tations are difficult to get right, as subtle bugs in circuits,
                                         proof systems, or integrations can break their guarantees,               RQ3: What parts of the ZKP stack are covered by formal
                                         allowing false statements to get accepted by the verifier [7].           verification efforts? Which systems and properties have been
                                         These risks are not hypothetical. The Orchard vulnerability              verified? How are models built, proofs discharged, and trusted
                                         in Zcash remained hidden for years and could have enabled                assumptions defined? What verification gaps remain?
                                         counterfeiting in its largest shielded pool [8], an Aztec Connect          Key findings. zkVM verification is converging on Lean and
                                                                                                                  the Sail RISC-V specification, but results remain isolated: they
                                           * These authors have equally contributed to this work.                 mostly prove constraint soundness, leave key artifacts unver-
ified, and rely on trusted extraction and modeling. Progress
requires end-to-end, CI-friendly proofs with precise claims              (a) ZK-DSL                                                           (b) zkVM
(Section VI).
                                                                                                                                                  Program
                                                                           Computations       Constraints
                                                                                                                                                  (e.g., Rust)
RQ4: How are ZKP security tools adopted in development
and audit workflows? Which tools and techniques are used                            Compiler                                                      Compiler

by practitioners? How are tools integrated into development
                                                                                                                                                  ISA binary
and audit workflows? What barriers limit tool adoption?                         Witness generator                                                (e.g., RISC-V)



   Key findings. Workflows remain human-led even though                                                     Constraint system
                                                                                                                                                   emulator
                                                                                                                                                                    VM circuit
                                                                                                                                                                  (chips + lookups)


interactive LLMs are already mainstream, used by 85% of                             Witness                                                     Execution trace


developers and 83% of auditors; advanced tools are useful but
                                                                                     Prover                                                        Prover
costly to integrate, often requiring project-specific specifica-
tions and manual validation (Section VII).                                            Proof                                                         Proof


RQ5: What gaps do practitioners perceive in security
                                                                                     Veriﬁer                                                       Veriﬁer
tooling? Which vulnerability classes are hardest to detect
during development and audits? Which classes are adequately                               Computations                          Constraints            System component
covered by existing tools, and which remain unsupported?
Which tool characteristics do practitioners prioritize? How do        Fig. 1: Two ways to develop a ZKP application. A ZK-DSL (a)
practitioners view emerging AI/LLM-based assistance?                  compiles a hand-written circuit (computations and constraints)
   Key findings. Practitioners view underconstrained bugs as          into a witness generator and a constraint system. A zkVM (b)
the most mature target for current tooling, but identify major        instead runs an ordinary program on a fixed ISA, checking the
gaps around semantic errors, Fiat–Shamir issues, and integra-         resulting execution trace against a fixed circuit.
tions. They prioritize formal verification, LLMs, and tools with
clear reports and guarantees (Section VII).
   Availability. To support reproducibility and further research,     given input. Then, the prover combines this witness with the
all of our artifacts are publicly available at https://github.com/t   constraints into a cryptographic proof that the verifier checks.
-sorger/zkp-security-tools, including the extended bug dataset,       Vulnerabilities. Developing using ZK-DSLs is error-prone,
the tool selection process, the tool-evaluation harness and its       because a mismatch between the computations and the con-
results, and the anonymized raw survey data.                          straints can break two core properties. If the constraints are
                                                                      too “weak”, they accept witnesses that the computation would
                       II. BACKGROUND                                 never produce. This breaks soundness, letting a malicious
                                                                      prover convince the verifier of an incorrect statement. If
Zero-knowledge proofs (ZKPs). A zero-knowledge proof                  instead the constraints are too strict, they reject witnesses from
(ZKP) lets a prover convince a verifier that a statement              honest runs, which breaks completeness. A soundness failure
is true without revealing anything beyond its validity [1].           is the most dangerous, as it can let an attacker forge proofs of
(In practice, proofs may only be succinct rather than zero-           false statements, leading to issues such as inflation bugs [8].
knowledge, but the term is still used.) Typically, this statement     zkVMs. Beyond being a source of bugs, writing constraints
asserts that a computation was performed correctly on public          “by hand” does not scale to large programs and is impractical
and optionally private inputs. To make this provable, the             to maintain as programs change. A zkVM removes this burden:
computation is expressed as a set of constraints, which are           the developer writes an ordinary program in a conventional
polynomial equations over a finite field. This is necessary be-       language (e.g., Rust), compiles it to a fixed instruction set
cause the proof system works on such equations, not arbitrary         architecture (ISA), and the zkVM proves the program (which
programs: any non-polynomial part of the computation, such            is committed to) was executed correctly [28]. In this model,
as a comparison, must be re-encoded as equivalent constraints.        the circuit no longer encodes the application but the fetch-
A satisfying assignment of these equations, called a witness,         decode-execute loop of a CPU, which proves the execution of
then corresponds to a correct run of the computation. The             any program for that ISA. In a zkVM, the witness generator
prover produces a proof that it knows such a witness, and the         corresponds to an ISA emulator. It first runs the program and
verifier checks the proof. Developers build such ZKP programs         records its execution trace, which is a step-by-step log of every
in two ways, depicted in Figure 1.                                    instruction executed. This trace is then checked against the
ZK-DSLs. The first approach is to write an arithmetic                 constraints, which are split by instruction type into chips (e.g.,
circuit by leveraging a domain-specific language (DSL) such           one chip for addition, one for memory). Beyond these core
as Circom [27]. When using such a DSL, the developer writes           chips, zkVMs often rely on precompiles: dedicated circuits
both the computations and the constraints themselves and must         for expensive, frequently used operations (e.g., hashing) that
keep them in sync [7], [15]. A compiler then lowers the circuit       would be prohibitively slow to prove [29]. As each chip
into a constraint system (e.g., R1CS [6]), together with a            is constrained on its own, the proof must additionally tie
witness generator that computes all intermediate values for a         them together so they describe a single, consistent execution.
Lookup and permutation arguments provide this link: a lookup          tools with optional specification-driven modes, we use only
proves that a value lies in a given set (such as the rows another     modes that do not require manual annotations.
chip exposes), while a permutation argument proves that               Dataset. We extend the dataset introduced by Chaliasos et
two sequences of values are rearrangements of one another.            al. [7], which contains real-world ZKP circuit vulnerabilities.
Together, they keep a shared state such as memory coherent            For each bug, the dataset provides the circuit containing the
across the trace, so that a value read always equals the one last     vulnerable code, metadata about the vulnerable location, and,
written to that address [30], [31]. Finally, a prover backend         when available, the original vulnerable project commit. This
turns the satisfied constraints into a proof, which a verifier        lets us evaluate each tool in two settings: in a minimal wrapper
checks. This generality comes at a cost: each stage of the            that isolates the vulnerable code (isolated mode) and in the
zkVM pipeline is a separate trust assumption, and therefore,          original project codebase (project mode).
a separate target of formal verification.                                We extend the Circom dataset from 29 to 70 bugs by
                     III. M ETHODOLOGY                                adding high-severity vulnerabilities from audit reports and
                                                                      public disclosures. All 70 bugs compile in isolated mode.
A. Qualitative Methodology
                                                                      In project mode, 56 bugs compile successfully, while the
  To dissect the current state of ZKP security tooling                remaining projects fail because of stale code or deprecated
(RQ1/Section IV) and the formal verification efforts for ZKPs         dependencies.
(RQ3/Section VI), we conducted a qualitative analysis com-
                                                                      Execution and Metrics. We developed a harness to process
bining systematic review with iterative expert analysis.
                                                                      bugs, execute tools, and handle timeouts. For each run, it stores
Corpus construction. For RQ1, we collected ZKP security               the tool’s raw output and assigns one of four labels: detected,
analysis tools, i.e., tools that analyze ZKP circuits for security-   missed, error, or timeout. Detected and missed are decided by
relevant bugs. We searched academic publications, GitHub              comparing the tool’s findings against the ground truth. When
repositories, and blog posts/project documentation. For RQ3,          a tool reports a vulnerability but does not directly identify
we collected formal verification efforts targeting ZKP systems,       the ground-truth location, two authors manually inspect the
with a focus on zkVMs as they have been the primary target of         raw output and compare it with the dataset annotation before
FV due to their significance and complexity [30]. We included         assigning the final label. Experiments were executed with a
closed-source tools or verification efforts only when public          600-second timeout on a virtual machine with 8 vCPUs, 32 GB
material provided sufficient detail to classify their targets,        RAM, and an AMD EPYC-Milan CPU running at 2.4 GHz.
techniques, and scopes. The complete process, initial corpora,
and filtering are documented in our artifact.                         C. Survey Methodology
Classification and validation. Two authors independently
classified each artifact through an iterative process. For RQ1,       Survey Design. To answer RQ4 and RQ5, we designed a
we classified tools by analysis target, technique, supported          practitioner survey following standard guidelines for survey
vulnerability classes, source availability, and automation level.     research [32], similar to prior software engineering and smart
Vulnerability coverage was mapped to existing ZKP bug                 contract security studies [33], [34]. The survey covered se-
taxonomies [7], [15], and support was marked as full, partial,        curity tool usage, perceived tooling gaps, formal verification
or unsupported based on papers, documentation, and source             workflows, and LLM-assisted security practices.
code. For RQ3, we classified formal verification efforts by ver-         We created two questionnaire variants: one for developers
ification goal, model-construction method, proving technique,         and researchers building ZKP systems, and one for security
verification scope, and trusted computing base. Disagreements         practitioners auditing them. Both variants were anonymous,
were resolved through discussion, and unresolved cases were           all questions were optional, and free-text fields were included
reviewed by a third author. The corpus and classifications were       where responses could benefit from additional context.
revisited as we went over the full corpus.                               To refine the questionnaires, two authors first drafted the
                                                                      survey independently and then converged on common ver-
B. Quantitative Methodology                                           sions. We then ran two pilot rounds with N = 3 participants
   To answer RQ2, we evaluate whether automated ZKP secu-             per questionnaire in each round. Pilot feedback was used to
rity tools can detect real-world vulnerabilities collected from       clarify wording and adjust multiple-choice options.
audits and public disclosures, rather than benchmarks tailored        Respondent Selection and Demographics. We targeted
to individual tools. We focus on true-positive detection, i.e.,       practitioners with experience in high-impact ZKP systems,
whether a tool identifies a vulnerability. We do not measure          focusing on deployed protocols with substantial usage. To
false positives, as our goal is to assess current bug-finding         reach this specialized population, we primarily contacted prac-
capability. We leave a false-positive analysis to future work.        titioners at research, development, and security organizations
DSL & Tool Selection. We focus on Circom as it is not only            through personal channels (e.g., email and instant messaging).
the DSL that most automated ZKP security tools target [7], but            In total, we contacted 200 practitioners. Since many prac-
also one of the most mature and widely deployed DSLs. We              titioners work across multiple roles, we asked participants to
selected all open-source tools that run non-interactively. For        complete the questionnaire most relevant to their work. We
            TABLE I: Survey participants’ experience.                [15]. Most tools focus on nondeterminism, where constraints
                                           Developers   Auditors     allow multiple outputs for the same input [16]. This is the
                                                                     most common form of underconstrainedness, but it is not the
     Years of ZKP experience
      Less than 1                              2 (5.6%)  2 (16.7%)   only one. A circuit is also underconstrained whenever semantic
      1–2                                    10 (27.8%) 6 (50.0%)    mismatches occur: constraints accept witnesses that do not
      3–5                                    18 (50.0%) 4 (33.3%)
      6+                                      6 (16.7%)   0 (0.0%)
                                                                     correspond to valid executions, even when deterministic.
     Types of ZKP systems used (multiple allowed)                       Some tools already extend coverage beyond nondetermin-
      Circuit DSLs                           29 (80.6%) 11 (91.7%)   ism, but mostly by requiring specifications. For instance,
      zkVM implementations                   23 (63.9%) 8 (66.7%)
      zkVM guest programs                    10 (27.8%) 2 (16.7%)    C IVER and CCC-C HECK detect missing range checks through
      Other / specialized                      3 (8.3%)   1 (8.3%)   user-defined preconditions, while C IRCOMSPECT and ZK F UZZ
    Total                                      36          12        rely on hard-coded checks that do not generalize to arbitrary
                                                                     circuits. Complex logic bugs and cryptographic issues remain
                                                                     largely unsupported and are therefore omitted from the table.
received 48 responses, corresponding to a 24% response rate.         Practical Usability. All tools except AC4 are publicly
Table I summarizes participants’ experience.                         available, but that does not imply push-button use. While
Data Analysis. We analyzed responses based on question               most tools can run automatically, some require user-provided
type. For multiple-choice and Likert-scale questions, we report      preconditions and postconditions. This specification burden
response distributions and percentages over the participants         can result in stronger guarantees and support for a wider range
who answered each question. For open-ended questions, two            of vulnerabilities, but limits automated use.
authors reviewed the responses qualitatively and grouped
                                                                      Takeaways for RQ1
recurring themes through inductive coding. We report results
separately for developers/researchers and security practitioners       • Current ZKP security analysis tools focus almost ex-

where the distinction is relevant.                                       clusively on Circom circuits, with limited support for
                                                                         language-agnostic workflows.
     IV. ZKP S ECURITY A NALYSIS T OOL L ANDSCAPE                      • Tools mainly target nondeterminism and have weaker
   This section answers RQ1 by classifying ZKP security anal-            coverage for other important bugs, including semantic
ysis tools by their target, technique, coverage, and usability.          mismatches and overconstrainedness.
Comparison Dimensions. Table II summarizes selected tools              • Stronger analyses often require specifications, limiting
along three dimensions. First, it captures the artifact being an-        their use as fully automated tools.
alyzed (e.g., source-level DSL code, or R1CS) and the analysis        Call to action: Security tools should provide broader lan-
technique. Second, it outlines the vulnerability classes the tools    guage support, either through language-agnostic analyses
can target. Third, it reports which tools are open-source and         or support for emerging DSLs, and should expand beyond
whether they run automatically without specifications.                nondeterminism, covering a wider range of vulnerabilities.
Targets and Techniques. Most tools target Circom, operating
at different abstraction levels that correspond to different                           V. T OOLS ’ E FFECTIVENESS
stages of the DSL pipeline in Figure 1a. Source-level tools,            This section answers RQ2 by evaluating existing automated
such as C IRCOMSPECT, analyze Circom code directly, while            and open-source ZKP security tools against real-world vulner-
other tools like P ICUS operate on constraint systems (R1CS).        abilities. We evaluate six Circom tools in two modes: isolated
The latter is closer to being language-agnostic, but loses           and project mode (see Section III-B for the details).
the witness-computation logic needed to detect computation-          Overall effectiveness. In isolated mode, at least one tool
constraint mismatches. To achieve language-agnostic analysis         detects 32 of the 70 bugs (45.7%). Across all executions,
while preserving access to computations, recent work instead         the tools produce 83 true positives (TPs). However, this hides
targets high-level intermediate representations [15], [38], [39].    substantial overlap, as 38 bugs are missed by every tool, while
   The tools leverage three main techniques. Static analysis         20 bugs are detected by at least two tools. In project mode,
reasons about code structure and data flow using methods             effectiveness drops sharply: at least one tool detects only 11
such as pattern matching or taint analysis. It is fast, but          of the 56 bugs (19.6%), with 14 TPs in total (see Figure 2).
often imprecise. Formal verification tools such as C IVER            Detection by root cause. Detection is concentrated in a
prove properties of the constraint system using deduction rules      narrow subset of bug patterns. Table IV groups bugs by their
and SMT solving. They provide stronger guarantees when               root cause [7], and counts a bug as detected if any tool reports
they succeed, but struggle with large circuits and non-linear        a TP. In isolated mode, all assigned-but-unconstrained bugs
finite-field arithmetic [40]–[43]. To mitigate this, several tools   are detected, and tools detect roughly half of the missing-
combine static analysis with formal verification [16], [19].         input-constraint and logic-to-constraint-translation bugs. In
Finally, ZK F UZZ applies fuzzing to detect defects [20].            contrast, no circuit-design issues are detected, and only one of
Vulnerability Coverage. Table III summarizes tool support            three specification misimplementations is detected. The project
for vulnerability classes from prior ZK bug taxonomies [7],          mode results are weaker across nearly every class. Importantly,
TABLE II: Qualitative comparison of ZKP circuit tooling. C                                                                      TABLE III: Detection capabilities of tools with respect to
= Circom, R = R1CS, CN = Circom/Noir, H = halo2, CH =                                                                           vulnerability categories. A single bug can fall under several
Circom/halo2. SA = static analysis, DA = dynamic analysis,                                                                      of them. ∼ = partial support.
FV = formal verification, SF = SA+FV, ∼ partial support.




                                                                                                                                                                                       [11]
                                                                                                                                                                                        15]
                                                                                                                                                                                        ]
                                                                                                                                                                                  r [14
                                                                                                                                                                                   ck [
                                             [11]
                                              15]




                                                                                                                                                                                 [35]
                                                                                                                                                                                  13]
                                                                                                                                                                                 pect




                                                                                                                                                                                    0]
                                                                                                                                                                                   9]




                                                                                                                                                                                  2]
                                              ]




                                                                                                                                                                                   ]
                                                                                                                                                                                   ]
                                        r [14




                                                                                                                                                                            z z [2




                                                                                                                                                                             [37]
                                         ck [




                                                                                                                                                                            a l [1
                                                                                                                                                                            -Che




                                                                                                                                                                           r [3 6




                                                                                                                                                                             [18]
                                                                                                                                                                           s [16




                                                                                                                                                                            P [1
                                                                                                                                                                           ekt [
                                        [35]




                                                                                                                                                                            ecto
                                        13]
                                       pect                                                                                      Vulnerability Class




                                                                                                                                                                           oms
                                          0]




                                                                                                                                                                          sCS
                                         9]




                                        2]
                                         ]
                                         ]
                                   zz [2




                                    [37]
                                   al [1
                                   -Che




                                  r [36




                                    [18]
                                  s [1 6




                                   P [1
                                  ekt [
                                   ecto




                                                                                                                                                                      Zequ




                                                                                                                                                                      ZKA
                                                                                                                                                                      CCC
                                                                                                                                                                      Pilsp


                                                                                                                                                                      zkFu




                                                                                                                                                                      Ecne
                                                                                                                                                                      Korr




                                                                                                                                                                      Cive




                                                                                                                                                                      AC4
Dimension
                                 oms




                                                                                                                                                                      Picu
                                                                                                                                                                      Circ
                                 sCS




                                                                                                                                                                      Con
                             Zequ




                             ZKA
                             CCC
                             Pilsp


                             zkFu




                             Ecne
                             Korr




                             Cive




                             AC4
                             Picu
                            Circ




                             Con
                                                                                                                                                     Nondeterminism ∼




                                                                                                                                  Underconstrained
                                                                                                                                                                          ✗   ✓ ✓ ✓ ✓ ✓ ✓ ✓ ✓ ✓ ✓
Target                C IR PIL H CN C R R C R C CH                                                                                                   Missing range
                                                                                                                                                                      ∼   ✓   ✗   ∼ ∼     ✗   ✗   ∼ ✓     ✗   ∼   ✗
Technique            SA SA FV SF DA SF SF SF FV FV SA FV                                                                                             checks
                                                                                                                                                     Division by zero ∼   ✓   ✗   ✗   ✓ ∼ ∼ ∼         ✗   ✗   ∼   ✗
Underconstrained ✓                  ✗     ✓        ✓        ✓         ✓         ✓        ✓        ✓         ✓         ✓     ✓                        Circuit logic
                                                                                                                                                                      ✗   ✓   ✗   ✗   ✗   ✗   ✗   ✗   ✓   ✗   ✗   ✗
                                                                                                                                                     assumptions
Overconstrained         ✗           ✗        ✗     ✓        ✓          ✗        ✗        ✗        ✗         ✗         ✗     ✓                        Other            ✗   ✓   ✗   ✗   ∼ ✓     ✗   ✗   ✓   ✗   ∼   ✗
Open source             ✓           ✓     ✓        ✓        ✓         ✓         ✓        ✓        ✓         ✓         ✓     ✗                        mismatches
Automatic               ✓           ∼     ∼        ✓        ✓         ✓         ✓        ✓        ∼         ✓         ✓     ✓    Overconstrained                     ✗    ✗   ✗   ✓ ✓     ✗   ✗   ✗   ✗   ✗   ✗   ✗



                    TP                    FN                     Error                       Timeout                            effectiveness. Among the 56 bugs that compile in both modes,
                                                  Isolated mode (n=70)                                                          31 are missed in both modes, 6 are detected in both, and 14 are
            Picus           10                                   41                                          19                 detected only in isolated mode. The common case, therefore,
            Civer            12                    18                               26                           14
                                                                                                                                is that large codebases often introduce scalability issues.
            Ecne                        25                                          38                                 7
   Circomspect                                                  57                                                13
                                                                                                                                Operational limitations. Tools lack maturity, as they often
        zkFuzz                          25                            16            4                   25
        ConsCS              11                                       43                                 5         11
                                                                                                                                produce errors. Further, as most tools rely on SMT solvers,
       All tools                             32                                               38                                timeouts occur quite often. Specifically, C IVER detects 20 TPs
                                                                                                                                in isolated mode, but also fails with 26 errors and 14 timeouts.
                    0                10           20             30          40              50             60             70
                                                                                                                                In project mode, timeouts and errors become more common
                                                  Project mode (n=56)                                                           (see Figure 2), with most timeouts stemming from the SMT
            Picus                                 30                                         20                        6        queries the tools perform. A recent line of dedicated finite-field
            Civer               8                                     36                                         11
                                                                                                                                SMT solvers aims to make exactly these queries faster [40],
            Ecne            7                              28                            4                  17
                                                                       54
                                                                                                                                [41], [43]–[45]. A complementary direction discharges finite-
   Circomspect
        zkFuzz          4               12             4                                 36
                                                                                                                                field obligations in a proof assistant instead, sidestepping the
        ConsCS                            21                          9                            25                           theory combination that stalls SMT [46].
       All tools                11                                              45
                                                                                                                                   Lightweight tools are more robust but less effective. For
                    0                   10                 20              30                40                  50             instance, C IRCOMSPECT never times out, yet it detects only
                                                                Total Bugs                                                      one TP. Although we do not systematically measure false-
  Fig. 2: Per-tool outcomes in Isolated and Project modes.                                                                      positive rates in this benchmark, our use of the tools on real
                                                                                                                                codebases revealed that, as expected, E CNE and C IRCOM -
                                                                                                                                SPECT are substantially noisier than the remaining tools, often
TABLE IV: Cumulative detection by ground-truth root cause.
                                                                                                                                producing many false positives.
   Root cause                                                               Isolated                        Project
   Missing input constraints                                              10/22 (45.5%)               3/18 (16.7%)               Takeaways for RQ2
   Logic-to-constraint translation                                        9/18 (50.0%)                3/13 (23.1%)                • ZKP security tools have practical value, as they detect
   Unsafe circuit reuse                                                    4/10 (40.0%)               2/7 (28.6%)
   Assigned but unconstrained                                             6/6 (100.0%)                 2/5 (40.0%)
                                                                                                                                    critical vulnerabilities, so developers should use them.
   Circuit design issue                                                     0/6 (0.0%)                  0/6 (0.0%)                • The tools are not yet mature. Errors and timeouts
   Arithmetic field issues                                                 2/4 (50.0%)                1/4 (25.0%)                   are common, while effectiveness drops when analyzing
   Spec. misimplementation                                                 1/3 (33.3%)                  0/2 (0.0%)
   Other programming errors                                                 0/1 (0.0%)                 0/1 (0.0%)                   large codebases, suggesting that tools are currently
                                                                                                                                    better suited to focused code-fragment analysis.
                                                                                                                                  • Results differ substantially from tool-specific bench-
                                                                                                                                    marks presented in their research papers, highlighting
assigned-but-unconstrained bugs fall from 100% to 20% and
                                                                                                                                    the bias introduced by narrow evaluation suites.
missing-input-constraint bugs from 45% to 16%.
                                                                                                                                 Call to action: ZKP security tools need better engineering,
Isolated versus project analysis. The isolated mode bench-                                                                       broader vulnerability coverage, and evaluation on real-
mark is valuable because it standardizes experiments and                                                                         world datasets. Improvements in SMT solving and comple-
isolates the vulnerable code, but it can overestimate practical
 mentary analyses could substantially reduce timeouts and            obligation, but is implemented via constraints. Any use of a
 make more sophisticated analyses practical.                         zkVM also involves a guest program, which must be compiled
                                                                     correctly or verified at the ISA level so that the compiler drops
        VI. F ORMAL V ERIFICATION OF ZKP S YSTEMS                    out of the trusted computing base and the intended statement is
   While the tools in Section IV detect bugs in circuits, a          the one proven by the zkVM. Given that a zkVM may allow
complementary line of work aims to prove their absence               for any guest program to be proven, and that verifying the
through formal verification (FV). This is particularly relevant      guest program is a traditional program verification task, we
for general-purpose ZKP systems such as zkVMs [30], which            treat this as a mostly separate concern in this section.
we focus on here as they also subsume circuit verification.          Completeness. Completeness requires that every honest exe-
A zkVM is far more complex than a single circuit, and it             cution of the guest program results in a proof accepted by
concentrates risk: a single zkVM can be a point of failure for       an honest verifier. While soundness is typically the main
many independent applications. For the same reason, however,         concern, completeness is essential in some deployments; a
verifying one zkVM can secure a whole ecosystem.                     completeness failure could, for example, cause liveness issues
   Automated tools (e.g., P ICUS) can be used to verify specific     in a blockchain that settles via validity proofs for blocks.
properties, but do not cover the full stack: reasoning about            Unlike soundness, completeness depends on the witness
ISA semantics, soundness and completeness of semantics,              generator and prover actually producing the satisfying witness
the provable security of cryptographic specifications, and the       and a valid proof, which draws in a much larger part of the
correctness of cryptographic code against those specifications.      stack, including compilers. It decomposes into the following.
This has led to broad adoption of proof assistants, often Lean,         Constraint correctness, completeness direction (CC-C). For
although Rocq [25], [47], ACL2 [24], and EasyCrypt [48]              every ISA execution, there is a witness that satisfies the
have also been used. Coordinated efforts such as the Ethereum        constraints (ISA ⇒ constraints).
Foundation’s verified-zkEVM project [49] pool resources and             Witness-constraint consistency (WC). The witness gener-
tooling, while parallel standardization of the zkVM target itself    ator produces a satisfying witness for every execution. The
(i.e., a common RISC-V profile) [50] has helped streamline           constraints alone can only show that a satisfying witness exists.
verification efforts. We therefore center this section on zkVMs,        Prover completeness (PC). The prover produces a proof the
examining which systems have been verified and for which             verifier accepts. Likewise for the recursion prover, although the
properties, how their formal models are built, which techniques      proven statement is different.
are used, and what they leave in the trusted computing base.            While constraint DSLs usually derive both constraints and
Figure 3 depicts the zkVM stack and its verification goals.          witness computation from one circuit description, zkVMs
Table V summarizes the verification efforts to date.                 often optimize the witness generator separately, so WC may
A. Verification goals                                                cover an artifact untouched by constraint-correctness proofs.
   A zkVM composes several artifacts: a guest program com-           B. Making the system verifiable
piled to the ISA, the arithmetization that encodes the ISA as
polynomial constraints, precompiles, the cryptographic proof            To verify any zkVM component, one must have the relevant
system, and a recursion layer that aggregates proofs for seg-        formal specifications, the ability to precisely state what must
ments of an execution trace into a final one. Verifying a zkVM       be verified, and the ability to model the verification target in a
means establishing end-to-end soundness and completeness             proof assistant. Specification and modeling of the target largely
guarantees, with current work typically focusing on soundness.       determine the trusted computing base beyond the verification
Soundness. Soundness means the verifier never accepts proofs         environment itself, and must therefore be validated and tested.
of false statements. It depends on the constraints, the proof        Otherwise, one risks technically correct proofs that say nothing
system, and the verifier: the witness generator and prover are       meaningful about the real system.
untrusted. This reduces the verification scope to the following:     Model creation. We distinguish four modeling approaches.
   Constraint correctness, soundness direction (CC-S). Every         The choice is primarily about the gap between the verified
witness satisfying the constraints corresponds to an execution       model and the code that actually runs, and what is trusted to
of the ISA (constraints ⇒ ISA), checked against a refer-             bridge it. Whether the model is produced by a tool or by hand
ence specification, such as the RISC-V Sail model extracted          is secondary, affecting how much code structure survives and
to a proof assistant. The same obligation applies to each            how costly the result is to maintain.
precompile against its function specification. This subsumes            Constraint extraction (E). In the case of constraints, it is
determinism, which many automated tools target.                      possible to intercept the circuit-builder API (e.g., Plonky3’s
   Proof-system soundness (PS). The cryptographic argument           Air trait) and export the constraints to a proof assistant.
prevents a malicious prover from forging a proof of a false          As extraction is automated, the model closely mirrors what
statement that an honest verifier would accept, for some             the prover actually evaluates, and the main trust assumption
security parameter (e.g., 128 bits).                                 is the correctness of the extraction tool. Nethermind’s Certi-
   Verifier correctness (VC). The verifier rejects invalid proofs.   Plonk [26], OpenVM’s constraint-correctness proofs [23], and
The verifier used for recursive aggregation carries the same         the original SP1 Hypercube proofs [22] follow this approach.
 SPECIFICATION
                      Guest program             ISA spec:                   Precompile
 (reference)                                                                                           Proof-system spec:
                          spec                RISC-V Sail                  function spec             IOP · PCS · Fiat–Shamir
                                            extracted to Lean
                                                                                                           PS, PC · SC


 IMPLEMENTATION                       Witness gen.
 (what runs)                           (emulator)
                                          WC · C
                                               consistency                                                   Prover
                                                                                                          (CPU / GPU)
                compiler                                                                                     PC · C                  Recursion
     Guest                   ISA                                                                                                                         On-chain
                                                           Constraints                                                                (verifier-
    program                program                                                                                                                        verifier
                                                                                                                                     in-circuit)
                                                            CC · SC                                                                                       VC · S
                                                                                                             Verifier                 VC · SC
                                                                                                             (CPU)
                                            ecall / libc                                                     VC · S
                                                                            Precompile
                                                                              circuits
                                                                             CC · SC


  Key
  Boxes:    implementation/artifact (runs) specification (reference)                Arrows:      data flow              verification link to spec     runtime interface
  Goals: CC constraint correctness WC witness–constraint consistency               PS proof-system soundness            VC verifier correctness PC prover completeness
  Properties: S soundness C completeness SC both

Fig. 3: The zkVM verification stack: a specification band (reference models) over an implementation band (what runs), linked
by compiler and extraction steps. Each artifact is labeled with its verification goal and its relevance to soundness/completeness.

TABLE V: Verification efforts across the zkVM stack up to date. Verification goal refers to the goals defined in Section VI-A,
with the targeted constraints in brackets for constraint correctness. Model lists the model-creation approaches (Section VI-B).
Proving technique and Tooling report the techniques and tools these efforts employ. ITP = interactive theorem proving.
   Verification goal                                 Model                                               Proving technique        Tooling
   Soundness
     Constraint correctness (ISA)            Extraction [22], [23], Translation [51], [52],              ITP; SMT                 Lean, Rocq, ACL2; Picus-AuditHub
                                             Hand-written [24], [25], [53]
        Constraint correctness (precompiles) Extraction [54], [55], Translation [47], [52]               ITP; SMT                 Lean, Rocq; Picus-AuditHub
        Proof-system soundness               Hand-written [56]                                           ITP                      Lean (ArkLib, VCVio)
        Verifier correctness                 Hand-written [48]                                           ITP                      EasyCrypt
   Completeness
     Constraint correctness (ISA)                    Correctness by construction [57]                    ITP                      Clean
     Witness-constraint consistency                  Correctness by construction [57],                   ITP; SMT                 Clean; ZIVER
                                                     Hand-written [58]



Extraction is lossy: reading constraints from the builder yields                           extractor. On the Rust side, it can be translated to a proof
flat polynomials and lookup interactions, losing the code struc-                           assistant, whether by rocq-of-rust [47] (supplemented by
ture that generated them and making proofs longer, harder, and                             manual work and validated by comparing the Rocq and Rust
less reusable across similar instructions. Extraction can also                             outputs) or via the Charon frontend [60]. A limitation of auto-
bridge approaches: SP1’s latest effort extracts constraints but                            mated Rust-to-proof-assistant tools is that they translate only a
expresses them in Clean [59], combining (E) with (CbC).                                    fragment of Rust1 and that translation is inherently trusted as
   Translation via a compiler IR (T). A compiler lowers the                                there are no complete formal Rust semantics to prove against.
artifact (typically constraints or Rust source code) through a                             Highly optimized cryptographic code not written with these
reusable intermediate representation to a verification backend.                            tools in mind can therefore be hard to extract to any proof
This preserves more high-level structure than an extractor (e.g.,                          assistant: SIMD intrinsics, unsafe, and inline assembly are
witness-generation logic), but makes the compiler pipeline a                               not supported [61], [62] and are treated as opaque. Hence,
major trust assumption that requires extensive validation. On                              only a subset of the code of a prover like Plonky3 reaches
the constraint side, frameworks such as LLZK [39] lower                                    the proof assistant. There are other Rust verification tools,
circuits through MLIR dialects to multiple backends. These                                 including Verus [63] (trialed on zkVM constraints [64]), which
include an SMT solver (e.g., P ICUS [16], integrated into RISC                             do not extract to a proof assistant and fit self-contained Rust
Zero’s CI/CD pipeline [52]) and a proof-assistant backend.                                 components well. However, they are less suited to certain
The backend is therefore an orthogonal choice while the
compiler/IR pipeline joins the trusted base in place of an                                   1 For example, see https://github.com/cryspen/hax/labels/unsupported-rust.
tasks such as verifying a verifier, which must ideally bridge           The second source is the verification tools themselves, and
a Rust implementation to a provably secure proof-system              it is the easier of the two to under-report. It includes the
specification that lives in a proof assistant.                       proof assistant’s trusted kernel, together with the axioms and
   Hand-written model (M). A human (or agent) writes the             library lemmas invoked, and any unverified solvers or decision
model directly in a proof assistant. For example, CertiK             procedures trusted to be correct. Solvers are a subtle case: even
manually re-implemented zkWasm’s circuit logic in Rocq [25].         when they produce a kernel-checkable certificate for the proof
This is laborious but flexible. Model-implementation corre-          assistant, the encoding of the proof obligation passed to them
spondence must be established separately, typically by testing       may still be trusted. It also includes the theorem statements
rather than formal equivalence. Jolt’s ACL2 model [24] did           themselves: a proof of a vacuous or misstated theorem passes
so by exhaustively comparing subtable outputs against Rust           the kernel while establishing nothing, so what is proven is as
for all inputs when feasible (at most 216 entries), and by           much part of the TCB as the machinery that checks it. Finally,
random testing otherwise. StarkWare’s Cairo effort similarly         an effort may simply assume a property rather than prove it.
built a manual Lean model of VM execution semantics [53],            OpenVM’s constraint-correctness proofs, for example, assume
complemented by a proof-producing compiler.                          the soundness of the lookup/bus argument that ties its chips
   Correctness by construction (CbC). Instead of deriving a          together [23]. A subtler cost is that large verification toolchains
model from existing code, the circuit is written and proven          exist partly just to move artifacts from one representation into
correct directly in the proof assistant. This removes the model-     a proof assistant or SMT-LIB, never discharging an obligation
implementation gap, but requires (re)writing the artifact there.     themselves while still enlarging the TCB and the maintenance
It is only practical when either fast code can be generated from     burden. This is part of why tighter integration of development
it (as in fiat-crypto [65]) or the artifact is not performance-      tooling with formal verification, and minimizing the set of
sensitive, as with constraints. Clean [59], implemented in           trusted tools and extractions, is attractive.
Lean, follows this route and proves both CC and WC.                     The TCB is therefore not a fixed baseline, but a function of
   In short, automated approaches stay closest to the deployed       both the system and the verification approach, and two verifi-
system but concentrate trust in unverified tooling, and extrac-      cation outputs can rest on very different assumptions. This is a
tion may discard code structure. Hand-written models recover         familiar lesson from software verification: even CompCert, the
structure and cover more of the system, but need separate            flagship verified C compiler, required an explicit and careful
validation and maintenance. CbC removes the model-code gap,          accounting of its trusted base, its specification, its extraction
but requires a proof-assistant implementation to be practical        to executable code, and unverified support code [66].
from a software-engineering perspective.
                                                                     C. Verification Gaps and Risks
Proving techniques. How a property is discharged also
shapes the trusted computing base. Interactive theorem proving       Isolated components. Constraint soundness is the most
is the most expressive option and yields kernel-checked proofs,      mature goal (Table V), with proofs that have covered many
but proof effort is high (though tactics and AI help) and            zkVMs [23]–[25], [53]. It is, however, only one direction
limited automation hinders CI integration when proofs break.         of one layer of the stack, and significant gaps remain else-
Automated solvers such as SMT require less effort, but have          where. No zkVM has end-to-end formal verification, and
narrower scope (e.g., only target determinism) and can struggle      verified components are isolated. Constraint-correctness proofs
with ZKPs (Section IV). Proof assistants can sidestep this           cover instruction semantics, but the witness generator, the
issue: BitModEq, for instance, proves finite-field-to-bitvector      lookup/permutation arguments, the proof-system backend, and
equivalences as a Lean tactic, outperforming general-purpose         the on-chain verifier remain largely unverified.
SMT solvers on real zkVM benchmarks [46].                            Shifted complexity. As the stack is large, verification
Trusted computing base. Every formal verification result             complexity is often shifted between components rather than
holds only relative to a trusted computing base, which has           removed. Simplifying one component can burden another:
two distinct sources. The first is the verification target: which    lookup arguments are advertised as leading to simpler zkVMs
parts of the stack were modeled, which reference specification       and simpler constraints [31], [67], but end-to-end verification
serves as the ground truth, and the gap between the proven           must then also cover the lookup argument’s specification, its
model and the code that actually runs. This gap is shaped di-        underlying cryptography, and the well-formedness of its tables.
rectly by the model-creation choice (Section VI-B). Extraction          Implementation choices can also sidestep whole tasks.
(E) and compiler translation (T) each insert an unverified tool;     Working directly with assembly, say, drops the compiler from
hand-written models (M) assume that the model, written by            the obligations, at the cost of different tools and specifica-
a human or agent, matches the implementation; correctness-           tions. In both cases the verified boundary can shrink even as
by-construction (CbC) has no separate model that can diverge         constraint-level proofs become more tractable, with complex-
but may be less performant. Any processing below the level at        ity reappearing in the trusted computing base.
which the artifact is verified (e.g., compilation) is also trusted   Witness generator. The witness generator is a core unverified
not to alter semantics. Wherever the model is not directly           component. WC could be checked automatically [19], but little
extracted, this gap must be validated rather than proven.            work applies this to zkVMs, where it remains a research
prototype [58], and extracting witness generation code to a            lookup/permutation and memory arguments, proof back-
proof assistant has not yet been done.                                 ends, and verifiers are largely unverified.
Precompiles. Precompiles also remain largely unverified.             • Every result depends on its trusted computing base,
Only individual precompiles have been verified in some form,           especially the gap between the verified model and
such as Plonky3’s Keccak circuit [47] and the determinism of           running code, so assumptions and trusted tools must be
RISC Zero’s Keccak circuit [52]. In one such attempt, Nether-          reviewed explicitly.
mind found a critical bug in Scroll’s Halo2 Keccak circuit [54].     • Adoption depends on economics and integration:
Beyond these, most precompiles remain unverified across all            zkVMs evolve quickly, proofs must be cheap to re-
zkVMs. A single zkVM may ship precompiles for several                  establish in CI, and AI lowers proof cost without solving
cryptographic primitives. Precompiles can also be generated            specification fidelity.
automatically [68] and synthesized from frequently executed         Call to action: Move from isolated constraint-correctness
guest code, thereby multiplying their number into an open-          proofs to repeatable, CI-friendly end-to-end guarantees,
ended, shifting set that cannot be chased circuit by circuit.       and state precisely which properties, components, and
This shifts what kind of verification is required to verify         versions are verified, and under what assumptions.
the generator. Assuming one can verify the ISA constraints,
the task of verifying autoprecompiles is simply translation                    VII. P RACTITIONERS ’ P ERSPECTIVE
validation, which is far more amenable to automation.                 This section answers RQ4 and RQ5 through targeted sur-
Proof system and verifier. As for the proof system, Ark-           veys of ZKP practitioners. We present the main highlights
Lib [69] and VCVio [56] aim to formalize its cryptographic         here, while complete results are in the supplementary material.
building blocks. These include the sum-check protocol [70],        Tool adoption and workflows. As shown in Figure 4a, inter-
FRI [71], WHIR [72], and Fiat–Shamir [73]. Bridging such           active LLMs are already the most popular across both groups.
a library with production-grade implementations has not yet        Auditors additionally report broader use of specialized tooling,
been done. The best verified verifier result so far targeted       such as fuzzers, formal verification, and internal AI tools.
ZKsync Era (an Ethereum zk-rollup), and proved only that the       Beyond which tools they adopt, practitioners also shared their
on-chain verifier contract matches a specification for which       workflows. Manual code review remains dominant, reported
no soundness properties have been verified [48]. Similarly,        by 79% of developers and 83% of auditors. While developers
the lookup arguments and memory consistency checks [74],           rely more on test suites (52%) and differential testing (41%),
[75] are almost entirely unverified, but could be specified in a   auditors make heavier use of AI tools (67%) and internal
library such as ArkLib.                                            tooling (58%). The picture is thus not one of push-button
Maintenance. There is an economic dimension to all this.           security, as tooling is layered around human-led review.
Verification can be lengthy and expensive – it is often done by    Usefulness and adoption barriers. When rating usefulness,
external contractors – while zkVMs evolve rapidly, sometimes       57% of developers and 67% of auditors rated tools as helpful.
with multiple releases per year. Hence, several efforts we cite    At the same time, the trait rankings in Figure 4b show that
target code that is now deprecated, making verification seem       practitioners weigh how findings are reported as much as
wasteful. The key challenge is therefore maintaining verifica-     what is found. Report quality and confidence of complete-
tion status as specifications and implementations change, as       ness stand out as the most valued traits across both groups,
in RISC Zero’s P ICUS CI/CD integration [52]. AI is making         alongside low false-positive rates and good documentation.
it more feasible to keep pace, but the usual pitfalls remain:      Auditors additionally place substantial weight on proof-of-
whether the specification and model faithfully capture the sys-    concept generation. These results indicate that practitioners
tem, and whether verification is integrated into development.      need tools that not only emit warnings but also clearly report
Guarantees not checked on every commit silently decay, while       findings. Usefulness, however, does not guarantee adoption:
AI-generated proofs remain a poor fit for CI.                      even tools that practitioners rate as helpful remain costly
Vague claims. As formal verification becomes more acces-           to integrate. High onboarding effort is reported by 57% of
sible through AI and stands to benefit from greater expertise      developers and 45% of auditors. Coverage is another barrier:
in the domains to which it is applied, it will be important to     practitioners work across languages and frameworks, which
remain clear about results. Claims have sometimes been vague,      current open-source tools do not support. In summary, our
and issues have been found upon close inspection [76], [77].       survey demonstrates that the dominant adoption barriers are
                                                                   practical, such as integration cost, limited language coverage,
 Takeaways for RQ3                                                 and the effort required to write specifications.
  • Verification is converging on Lean 4, RISC-V Sail, and
    libraries such as Clean and ArkLib, but broad adoption          Takeaways for RQ4
    remains open.                                                    • Interactive LLMs are already mainstream in ZKP devel-
  • Verified components remain isolated: constraint sound-             opment and auditing, but workflows remain human-led.
    ness is the mature core, while witness generators,               • Auditors rely more heavily on specialized security tool-
    Interactive
                                      Low false
                                       positives
                                                                                                                      TABLE VI: Practitioners’ views of vul-
                                                                              Automated
         LLMs                                                                        FV                               nerabilities and tools (including LLMs).
                                          Ease
         Static                                                                 Reusable
       analysis                           Docs                                 LLM skills                             Hard: hard to detect manually. Covered:
      Theorem
       provers
                                        Report                                AI security
                                                                                    tools
                                                                                                                      adequately covered by tools.
                                        quality

       Fuzzers                            Scale                                    Static
                                                                                 analysis                              Class                       Hard Covered
                                          PoC
        Formal                      generation                              General proof
   verification                                                                assistants                              Underconstrained circuits   72%    70%
                                           Cost
Property-based                                                                ZK-specific                              Arithmetic issues           44%    78%
        testing                          CI/CD                                   provers
                                    integration                                                                        Semantic mismatches         53%    30%
    AI security
          tools                   Completeness                                   Fuzzers                               Proof-system issues         60%    15%
                                    confidence

                  0   50    100                                                             0    25   50   75   100
                                                                                                                       Fiat-Shamir                 44%    25%
                                                   0   25   50   75   100
                      %                                     %                                         %                Crypto primitive misuse     33%    12%
  (a) Used tool categories         (b) Important tool traits                (c) Missing tool categories                System integration          26%     5%
                                      Developers            Auditors

                           Fig. 4: Practitioner survey overview.


     ing than developers.                                                                   least somewhat concerned about the trusted computing base.
   • Practitioners work across many ZKP languages, but                                      Auditors also report that communicating a tool’s security
     most security tools still target only Circom.                                          guarantees or limitations to clients often requires substantial
   • Practitioners find tools useful, but advanced tooling still
                                                                                            effort. This suggests that future tooling must also improve
     requires high-effort integration, project-specific specifi-                            transparency around assumptions and guarantees.
     cations, and manual validation.
                                                                                                Takeaways for RQ5
  Call to action: ZKP security tools should not only
                                                                                                 • Current tools are perceived as most mature for local
  broaden language support, but also reduce onboarding cost
                                                                                                    circuit-level bugs, especially underconstrained issues.
  through reusable specifications and integrations that fit
                                                                                                 • Practitioners identify major gaps for semantic mis-
  both development-time and audit-time use.
                                                                                                    matches, proof-system unsoundness, Fiat–Shamir bugs,
                                                                                                    cryptographic primitive misuse, and system integration.
Perceived vulnerability coverage. Table VI reports, for
                                                                                                 • Demand is strongest for automated formal verification,
each vulnerability class, the share of practitioners who con-
                                                                                                    domain-specific provers, reusable LLM skills, and tools
sider it hard to detect manually and those who consider
                                                                                                    with clear reports and auditable guarantees.
it adequately covered by current tools. The results suggest
that current tools are perceived as most mature for local                                       Call to action: The ZKP tooling community should prior-
circuit-level checks. Underconstrained circuits are the most                                    itize specification-centered and semantics-aware (AI) tools
frequently selected hard-to-detect class (72%), but they are                                    that make guarantees explicit and practical to validate.
also widely viewed as covered by existing tools (70%). By
contrast, proof-system issues combine high perceived difficulty                                                       VIII. D ISCUSSION
(60%) with low perceived tool coverage (15%). Fiat–Shamir                                   From local checks to system assurance. The four parts
bugs, misuse of cryptographic primitives, system integration                                of our study converge on a common boundary. Automated
issues, and semantic errors exhibit similar mismatches. The                                 analyses are strongest on local constraint properties, yet their
largest gaps thus lie beyond local constraint checks, pointing                              effectiveness drops when moving from isolated circuits to
to specification-centered and FV tools as a promising direction                             full projects. Formal verification offers stronger guarantees,
for future work.                                                                            but mostly for the soundness of selected components, while
Missing tools and unmet needs. Figure 4c shows that                                         practitioners identify semantic, proof-system, cryptographic,
automated formal verification is the most requested missing                                 and integration failures as major gaps. Those observations
category for both groups. Developers also request reusable                                  show that adding further local detectors alone will not close
LLM skills and AI security tools, while auditors report                                     the assurance gap. Future work should connect layers through
stronger demand for domain-specific interactive provers and                                 obligations such as computation–constraint consistency, inter-
fuzzers. A similar gap appears for LLMs: while respondents                                  face invariants, translation validation, and component compo-
find them useful for PoC validation and non-ZKP application                                 sition, while making uncovered layers explicit.
code, they remain weak precisely for circuit- and proof-                                    Specifications as shared security infrastructure. Moving
system-level vulnerability discovery. Even so, many report                                  beyond local properties requires making intended behavior
significant productivity gains, and over 80% of both groups                                 explicit. This connects three findings: broader circuit analyses
expect AI auditing to outperform 75% of security researchers                                require user-provided specifications, formal-verification guar-
within three years. Further, when using formal verification                                 antees depend on the fidelity of theorem statements and mod-
tools, a similar majority (over 80%) of both groups are at                                  els, and practitioners report specification work as an adoption
barrier. Specifications should therefore be reusable, versioned,     tools range from static analyses [12], [15], SMT-based sym-
machine-checkable, co-owned and independently reviewed by            bolic techniques [13], [16], [36], to fuzzing approaches [20],
those defining protocol intent and those assessing security. The     [21]. In this work, we conduct a qualitative study of these
same invariants and reference models should support testing,         tools, identify gaps in their coverage, perform the first large-
fuzzing, static analysis, and proof-assistant verification. LLMs     scale evaluation on real-world vulnerabilities, and highlight
may reduce the cost of authoring, translating, and maintaining       their limitations relative to the original papers’ evaluations.
these artifacts, but cannot establish that they faithfully capture      Due to the significance of ZKPs and the complexity of
protocol intent.                                                     their implementations, substantial work has focused on formal
From AI assistance to checkable assurance. Our survey                verification across different parts of the stack. Existing tech-
separates acceleration from assurance. Most respondents report       niques range from interactive theorem proving [17], [80], [81],
that AI has reduced development or audit effort, but they            SMT-based approaches [42], [43], [45], [82], to automated
rate LLMs most highly for bounded tasks such as validating           decision-procedure methods [18], [19], [35]. We perform the
findings, producing proofs of concept, and analyzing conven-         first systematic analysis of all these techniques and highlight
tional application code. Trust in LLMs is substantially weaker       major gaps and risks in their current applicability.
for circuit- and proof-system-level reasoning. This suggests            In addition to these techniques, there have been efforts in
that the near-term opportunity is verified acceleration: LLMs        different layers and specialized settings. These include proof
can propose specifications, invariants, tests, counterexamples,      systems [83], [84], ZKP compilers [85], [86], integrations
and proof scripts, while independent analyzers, proof kernels,       of ZKPs with smart contracts [87]–[89], and fuzzing for
and expert review determine which outputs become assurance           specific implementations [90], [91]. In contrast, we focus
evidence. AI-assisted results should record the provenance and       on generalized security tooling and on the circuit and core
review of generated artifacts, distinguish generated specifica-      implementation layers. We leave the systematic study and
tions from generated proofs, and identify which outputs were         evaluation of more specialized techniques and targets for
independently checked and continuously re-established in CI.         future work.
Threats to validity. We use a standard methodology [78] to
                                                                     Empirical studies of security tools and surveys. Empirical
identify validity threats, which we mitigate where possible.
                                                                     studies of security tools and practitioner surveys have been
   Internal. For RQ1/RQ3, we may miss tools or verifica-
                                                                     conducted in several domains. Prior work on smart contracts
tion efforts because the ZKP ecosystem evolves quickly.
                                                                     has surveyed vulnerabilities, verification methods, and analysis
For RQ2, tool outputs may be misclassified; for RQ4/RQ5,
                                                                     tools, and has empirically evaluated security tools against real-
survey responses may reflect misunderstandings. We mitigate
                                                                     world exploits [34], [92]–[94]. Other studies have examined
these threats by searching academic and practitioner sources,
                                                                     developers’ expectations of program analysis tools and the
preserving raw tool outputs, manually checking ambiguous
                                                                     usability of security tools [33].
detections, and piloting the questionnaires.
   Construct. In RQ1/RQ3, labels such as supported or partial
may hide differences in assumptions and trusted components.                                 X. C ONCLUSION
In RQ2, we measure detection of known vulnerable com-
ponents, not false positives. For RQ4/RQ5, respondents may              Our study of ZKP security tooling, six automated tools,
interpret tool categories and vulnerability classes differently;     formal-verification efforts, and 48 practitioners shows that cur-
we mitigate this with free-text fields and qualitative analysis.     rent defenses are useful but incomplete. Tools find some local
   External. The RQ1/RQ3 results are a snapshot of a fast-           underconstraint bugs, but detection drops on whole projects,
moving field. The RQ2 results may not generalize beyond              while formal verification mostly covers isolated constraint-
Circom and the six tools we evaluated, although Circom is            correctness claims rather than end-to-end systems. Practition-
currently the best-supported DSL by automated tools. The             ers likewise report human-led workflows and different needs
RQ4/RQ5 survey targets experienced practitioners from high-          across developers and auditors. By mapping tool coverage,
profile ZKP organizations, improving relevance for high-             failures, and practitioner needs, this work gives researchers a
impact systems but limiting representativeness.                      concrete agenda for broader, more reliable tooling and gives
                     IX. R ELATED W ORK                              practitioners a clearer basis for assessing defenses.
Security Tools and Verification for ZKPs. Recent studies
systematize the security of ZKP systems. Chaliasos et al. [7]                            ACKNOWLEDGMENTS
analyze real-world SNARK vulnerabilities across the circuit,
frontend, backend, and integration layers, whereas Tang et              The authors thank Shankara Pailoor for valuable feedback,
al. [79] classify ZKP vulnerabilities. Complementary to these        and the anonymous survey participants for their time and
works, we study the effectiveness, maturity, and adoption of         insights. Arman further thanks Carmela Troncoso for her
security tools and verification techniques for ZKPs.                 guidance and support throughout his internship at MPI-SP.
   Further, there has been a growing number of security tools        This work was partially funded by the Ethereum Foundation
for detecting vulnerabilities in ZKP implementations. These          (EF).
                              R EFERENCES                                        [17] J. Liu, I. Kretz, H. Liu, B. Tan, J. Wang, Y. Sun, L. Pearson, A. Miltner,
                                                                                      I. Dillig, and Y. Feng, “Certifying zero-knowledge circuits with refine-
 [1] S. Goldwasser, S. Micali, and C. Rackoff, “The knowledge complexity              ment types,” in IEEE Symposium on Security and Privacy, SP 2024, San
     of interactive proof-systems (extended abstract),” in Proceedings of the         Francisco, CA, USA, May 19-23, 2024. IEEE, 2024, pp. 1741–1759.
     17th Annual ACM Symposium on Theory of Computing, May 6-8, 1985,            [18] Q. Yang, B. Liang, H. Chen, and G. Li, “AC4: algebraic computation
     Providence, Rhode Island, USA, R. Sedgewick, Ed. ACM, 1985, pp.                  checker for circuit constraints in zero-knowledge proofs,” Formal As-
     291–304.                                                                         pects Comput., vol. 38, no. 1, pp. 11:1–11:20, 2026.
 [2] E. Ben-Sasson, A. Chiesa, C. Garman, M. Green, I. Miers, E. Tromer,         [19] J. Stephens, S. Pailoor, and I. Dillig, “Automated verification of consis-
     and M. Virza, “Zerocash: Decentralized anonymous payments from                   tency in zero-knowledge proof circuits,” in Computer Aided Verification
     bitcoin,” in 2014 IEEE Symposium on Security and Privacy, SP 2014,               - 37th International Conference, CAV 2025, Zagreb, Croatia, July 23-
     Berkeley, CA, USA, May 18-21, 2014. IEEE Computer Society, 2014,                 25, 2025, Proceedings, Part I, ser. Lecture Notes in Computer Science,
     pp. 459–474.                                                                     R. Piskac and Z. Rakamaric, Eds., vol. 15931. Springer, 2025, pp.
 [3] F. Baldimtsi, K. K. Chalkias, Y. Ji, J. Lindstrøm, D. Maram, B. Riva,            315–338.
     A. Roy, M. Sedaghat, and J. Wang, “zklogin: Privacy-preserving              [20] H. Takahashi, J. Kim, S. Jana, and J. Yang, “ zkFuzz: Foundation and
     blockchain authentication with existing credentials,” in Proceedings of          Framework for Effective Fuzzing of Zero-Knowledge Circuits ,” in 2026
     the 2024 on ACM SIGSAC Conference on Computer and Communi-                       IEEE Symposium on Security and Privacy (SP). Los Alamitos, CA,
     cations Security, CCS 2024, Salt Lake City, UT, USA, October 14-18,              USA: IEEE Computer Society, May 2026, pp. 3055–3074.
     2024, B. Luo, X. Liao, J. Xu, E. Kirda, and D. Lie, Eds. ACM, 2024,         [21] S. Chaliasos, I. Al-Fath, and A. F. Donaldson, “Towards fuzzing zero-
     pp. 3182–3196.                                                                   knowledge proof circuits (short paper),” in Proceedings of the 34th ACM
 [4] S. Chaliasos, I. Reif, A. Torralba-Agell, J. Ernstberger, A. Kattis, and         SIGSOFT International Symposium on Software Testing and Analysis,
     B. Livshits, “Analyzing and benchmarking zk-rollups,” in 6th Conference          ISSTA Companion 2025, Clarion Hotel Trondheim, Trondheim, Norway,
     on Advances in Financial Technologies, AFT 2024, Vienna, Austria,                June 25-28, 2025, M. Papadakis, M. B. Cohen, and P. Tonella, Eds.
     September 23-25, 2024, ser. LIPIcs, R. Böhme and L. Kiffer, Eds., vol.          ACM, 2025, pp. 98–104.
     316. Schloss Dagstuhl - Leibniz-Zentrum für Informatik, 2024, pp.          [22] Succinct Labs, “Formal verification of SP1 Hypercube,” 2025. [Online].
     6:1–6:24.                                                                        Available: https://blog.succinct.xyz/nethermind-lean/
 [5] Z. Peng, T. Wang, C. Zhao, G. Liao, Z. Lin, Y. Liu, B. Cao, L. Shi,         [23] OpenVM, “Announcing formal verification of OpenVM RV32IM
     Q. Yang, and S. Zhang, “A survey of zero-knowledge proof based                   constraints in Lean,” 2026, accessed: 2026-06-18. [Online]. Available:
     verifiable machine learning,” CoRR, vol. abs/2502.18535, 2025.                   https://blog.openvm.dev/fv
 [6] J. Groth, “On the size of pairing-based non-interactive arguments,” in      [24] C. Kwan, Q. Dao, and J. Thaler, “Verifying jolt zkvm lookup semantics,”
     Advances in Cryptology - EUROCRYPT 2016 - 35th Annual Interna-                   in Financial Cryptography and Data Security - 29th International
     tional Conference on the Theory and Applications of Cryptographic                Conference, FC 2025, Miyakojima, Japan, April 14-18, 2025, Revised
     Techniques, Vienna, Austria, May 8-12, 2016, Proceedings, Part II, ser.          Selected Papers, Part I, ser. Lecture Notes in Computer Science,
     Lecture Notes in Computer Science, M. Fischlin and J. Coron, Eds., vol.          C. Garman and P. Moreno-Sanchez, Eds., vol. 15751. Springer, 2025,
     9666. Springer, 2016, pp. 305–326.                                               pp. 163–179.
 [7] S. Chaliasos, J. Ernstberger, D. Theodore, D. Wong, M. Jahanara,            [25] CertiK, “Advanced formal verification of zero-knowledge proof
     and B. Livshits, “Sok: What don’t we know? understanding security                blockchains,” 2024, accessed: 2026-06-18. [Online]. Available: https:
     vulnerabilities in snarks,” in 33rd USENIX Security Symposium, USENIX            //www.certik.com/resources/blog/advanced-formal-verification-of-zer
     Security 2024, Philadelphia, PA, USA, August 14-16, 2024, D. Balzarotti          o-knowledge-proof-blockchains
     and W. Xu, Eds. USENIX Association, 2024.                                   [26] Nethermind, “Formally verifying zero-knowledge circuits: Introducing
 [8] Z. Wilcox, J. McGee, and T. Hornby, “The orchard counterfeiting                  CertiPlonk,” 2025, accessed: 2026-06-18. [Online]. Available: https:
     vulnerability—and next steps,” https://forum.zcashcommunity.com/t                //www.nethermind.io/blog/formally-verifying-zero-knowledge-circuit
     /the-orchard-counterfeiting-vulnerability-and-next-steps/56015, Jun.             s-introducing-certiplonk
     2026, accessed 2026-06-21.                                                  [27] M. Bellés-Muñoz, M. Isabel, J. L. Muñoz-Tapia, A. Rubio, and J. B.
 [9] GNcrypto, “Attacker drains $2.1M from deprecated Aztec Connect in                Melé, “Circom: A circuit description language for building zero-
     exploit,” https://www.gncrypto.news/news/attacker-drains-2-1m-depre              knowledge applications,” IEEE Trans. Dependable Secur. Comput.,
     cated-aztec-connect-exploit/, 2026, accessed: 2026-06-18.                        vol. 20, no. 6, pp. 4733–4751, 2023.
[10] Matter Labs, “ZKsync OS bug bounty program,” https://immunefi.com/          [28] E. Ben-Sasson, A. Chiesa, E. Tromer, and M. Virza, “Succinct non-
     bug-bounty/zksync-os/information/, 2026, accessed: 2026-06-18.                   interactive zero knowledge for a von neumann architecture,” in Pro-
[11] Trail of Bits, “Circomspect,” https://github.com/trailofbits/circomspect,        ceedings of the 23rd USENIX Security Symposium, San Diego, CA, USA,
     2024, accessed: 2026-06-18.                                                      August 20-22, 2014, K. Fu and J. Jung, Eds. USENIX Association,
[12] H. Wen, J. Stephens, Y. Chen, K. Ferles, S. Pailoor, K. Charbonnet,              2014, pp. 781–796.
     I. Dillig, and Y. Feng, “Practical security analysis of zero-knowledge      [29] RISC Zero, “Precompiles,” https://dev.risczero.com/api/zkvm/precompi
     proof circuits,” in 33rd USENIX Security Symposium, USENIX Security              les, 2026, accessed: 2026-06-18.
     2024, Philadelphia, PA, USA, August 14-16, 2024, D. Balzarotti and          [30] G. Yang, Y. Yang, Y. Cheng, H. Tang, B. Zhang, and K. Ren, “Sok:
     W. Xu, Eds. USENIX Association, 2024.                                            Understanding zkvm: From research to practice,” in Proceedings of the
[13] F. H. Soureshjani, M. Hall-Andersen, M. Jahanara, J. Kam, J. Gorzny,             ACM Asia Conference on Computer and Communications Security, ASIA
     and M. Ahmadvand, “Automated analysis of halo2 circuits,” in Pro-                CCS 2026, Bangalore, India, June 1-5, 2026, M. Agrawal, I. Molloy,
     ceedings of the 21st International Workshop on Satisfiability Modulo             V. Pandit, D. Mukhopadhyay, and K. Paterson, Eds. ACM, 2026, pp.
     Theories (SMT 2023) co-located with the 29th International Conference            852–868.
     on Automated Deduction (CADE 2023), Rome, Italy, July, 5-6, 2023,           [31] A. Arun, S. T. V. Setty, and J. Thaler, “Jolt: Snarks for virtual
     ser. CEUR Workshop Proceedings, S. Graham-Lengrand and M. Preiner,               machines via lookups,” in Advances in Cryptology - EUROCRYPT 2024
     Eds., vol. 3429. CEUR-WS.org, 2023, pp. 3–17.                                    - 43rd Annual International Conference on the Theory and Applications
[14] Thibaut Schaeffer, “Pilspector,” https://github.com/Schaeff/pilspector/,         of Cryptographic Techniques, Zurich, Switzerland, May 26-30, 2024,
     2023.                                                                            Proceedings, Part VI, ser. Lecture Notes in Computer Science, M. Joye
[15] A. Kolozyan, B. Vandenbogaerde, J. Swalens, L. Hoste, S. Chaliasos,              and G. Leander, Eds., vol. 14656. Springer, 2024, pp. 3–33.
     and C. De Roover, “Language-Agnostic Detection of Computation-              [32] B. A. Kitchenham and S. L. Pfleeger, “Personal opinion surveys,” in
     Constraint Inconsistencies in ZKP Programs Via Value Inference,” in              Guide to Advanced Empirical Software Engineering, F. Shull, J. Singer,
     2026 IEEE Symposium on Security and Privacy (SP). Los Alamitos,                  and D. I. K. Sjøberg, Eds. Springer, 2008, pp. 63–92.
     CA, USA: IEEE Computer Society, May 2026, pp. 3091–3110.                    [33] M. Christakis and C. Bird, “What developers want and need from
[16] S. Pailoor, Y. Chen, F. Wang, C. Rodrı́guez-Núñez, J. V. Geffen,               program analysis: an empirical study,” in Proceedings of the 31st
     J. Morton, M. Chu, B. Gu, Y. Feng, and I. Dillig, “Automated detection           IEEE/ACM International Conference on Automated Software Engineer-
     of under-constrained circuits in zero-knowledge proofs,” Proc. ACM               ing, ASE 2016, Singapore, September 3-7, 2016, D. Lo, S. Apel, and
     Program. Lang., vol. 7, no. PLDI, pp. 1510–1532, 2023.                           S. Khurshid, Eds. ACM, 2016, pp. 332–343.
[34] S. Chaliasos, M. A. Charalambous, L. Zhou, R. Galanopoulou, A. Ger-                Available: https://veridise.com/blog/audit-insights/risc-zeros-zk-vm-sec
     vais, D. Mitropoulos, and B. Livshits, “Smart contract and defi security           urity-how-veridise-enabled-risc-zero-to-achieve-provable-continuous-z
     tools: Do they meet the needs of practitioners?” in Proceedings of                 k-security/
     the 46th IEEE/ACM International Conference on Software Engineering,           [53] J. Avigad, A. Ganor, L. Goldberg, D. Levit, O. Nir, Y. Seginer,
     ICSE 2024, Lisbon, Portugal, April 14-20, 2024. ACM, 2024, pp.                     and A. Titelman, “Formal verification of the s-two AIR,” CoRR, vol.
     60:1–60:13.                                                                        abs/2606.04311, 2026.
[35] J. Jiang, X. Peng, J. Chu, and X. Luo, “Conscs: Effective and efficient       [54] Nethermind, “Formal verification of Halo2 circuits in Lean,” 2025,
     verification of circom circuits,” in 47th IEEE/ACM International Confer-           accessed: 2026-06-18. [Online]. Available: https://www.nethermind.io/
     ence on Software Engineering, ICSE 2025, Ottawa, ON, Canada, April                 blog/formal-verification-of-halo2-circuits-in-lean
     26 - May 6, 2025. IEEE, 2025, pp. 616–628.                                    [55] Y. Sun, “Releasing OpenVM 2.0 to production,” https://www.axiom.xy
[36] M. Isabel, C. Rodrı́guez-Núñez, and A. Rubio, “Scalable verification of          z/blog/openvm-2-production, 2026.
     zero-knowledge protocols,” in IEEE Symposium on Security and Privacy,         [56] D. Tuma, Q. Dao, J. Waters, A. Hicks, and N. Hopper, “VCVio: Verified
     SP 2024, San Francisco, CA, USA, May 19-23, 2024. IEEE, 2024, pp.                  cryptography in lean via oracle effects and handlers,” Cryptology ePrint
     1794–1812.                                                                         Archive, Paper 2026/899, 2026.
[37] Franklyn Wang, “Ecneproject,” https://github.com/franklynwang/Ecne            [57] G. Dell’Immagine, “Introducing Clean, a formal verification DSL for
     Project, 2022.                                                                     ZK circuits in Lean4,” https://blog.zksecurity.xyz/posts/clean/, 2025.
[38] A. Ozdemir, F. Brown, and R. S. Wahby, “Circ: Compiler infrastructure         [58] J. Ke, B. Liang, and G. Li, “Consistency verification for zero-knowledge
     for proof systems, software verification, and more,” in 43rd IEEE                  virtual machine on circuit-irrelevant representation,” IACR Cryptol.
     Symposium on Security and Privacy, SP 2022, San Francisco, CA, USA,                ePrint Arch., vol. 2025, p. 2204, 2025.
     May 22-26, 2022. IEEE, 2022, pp. 2248–2266.                                   [59] G. Mitscha-Baude, “Clean: Lean circuit dsl,” https://github.com/Verifie
[39] Veridise, “LLZK: An MLIR-based intermediate representation for zero-               d-zkEVM/clean, 2026.
     knowledge circuit languages,” https://github.com/project-llzk/llzk-lib,       [60] S. Ho, G. Boisseau, L. Franceschino, Y. Prak, A. Fromherz, and
     2026.                                                                              J. Protzenko, “Charon: An analysis framework for rust,” in Computer
[40] T. Hader, D. Kaufmann, and L. Kovács, “SMT solving over finite field              Aided Verification - 37th International Conference, CAV 2025, Zagreb,
     arithmetic,” in LPAR 2023: Proceedings of 24th International Confer-               Croatia, July 23-25, 2025, Proceedings, Part IV, ser. Lecture Notes
     ence on Logic for Programming, Artificial Intelligence and Reasoning,              in Computer Science, R. Piskac and Z. Rakamaric, Eds., vol. 15934.
     Manizales, Colombia, 4-9th June 2023, ser. EPiC Series in Computing,               Springer, 2025, pp. 377–391.
     R. Piskac and A. Voronkov, Eds., vol. 94, 2023, pp. 238–256.                  [61] S. Ho and J. Protzenko, “Aeneas: Rust verification by functional transla-
[41] A. Ozdemir, S. Pailoor, A. Bassa, K. Ferles, C. W. Barrett, and I. Dillig,         tion,” Proc. ACM Program. Lang., vol. 6, no. ICFP, pp. 711–741, 2022.
     “Split gröbner bases for satisfiability modulo finite fields,” in Computer   [62] K. Bhargavan, M. Buyse, L. Franceschino, L. L. Hansen, F. Kiefer,
     Aided Verification - 36th International Conference, CAV 2024, Montreal,            J. Schneider-Bensch, and B. Spitters, “hax: Verifying security-critical
     QC, Canada, July 24-27, 2024, Proceedings, Part I, ser. Lecture Notes              rust software using multiple provers,” in Verified Software. Theories,
     in Computer Science, A. Gurfinkel and V. Ganesh, Eds., vol. 14681.                 Tools and Experiments - 16th International Conference, VSTTE 2024,
     Springer, 2024, pp. 3–25.                                                          Prague, Czech Republic, October 14-15, 2024, Revised Selected Papers,
[42] T. Hader and A. Ozdemir, “An SMT-LIB theory of finite fields,” in                  ser. Lecture Notes in Computer Science, J. Protzenko and A. Raad, Eds.,
     Proceedings of the 22nd International Workshop on Satisfiability Modulo            vol. 15525. Springer, 2024, pp. 96–119.
     Theories co-located with the 36th International Conference on Computer        [63] A. Lattuada, T. Hance, C. Cho, M. Brun, I. Subasinghe, Y. Zhou,
     Aided Verification (CAV 2024), Montreal, Canada, July, 22-23, 2024, ser.           J. Howell, B. Parno, and C. Hawblitzel, “Verus: Verifying rust programs
     CEUR Workshop Proceedings, G. Reger and Y. Zohar, Eds., vol. 3725.                 using linear ghost types,” Proc. ACM Program. Lang., vol. 7, no.
     CEUR-WS.org, 2024, pp. 3–12.                                                       OOPSLA1, pp. 286–315, 2023.
[43] A. Ozdemir, G. Kremer, C. Tinelli, and C. W. Barrett, “Satisfiability         [64] CertiK, “zkvm-verus: Ethereum foundation verus evaluation,” https://gi
     modulo finite fields,” in Computer Aided Verification - 35th International         thub.com/CertiKProject/zkvm-verus, 2026.
     Conference, CAV 2023, Paris, France, July 17-22, 2023, Proceedings,           [65] A. Erbsen, J. Philipoom, J. Gross, R. Sloan, and A. Chlipala, “Simple
     Part II, ser. Lecture Notes in Computer Science, C. Enea and A. Lal,               high-level code for cryptographic arithmetic - with proofs, without
     Eds., vol. 13965. Springer, 2023, pp. 163–186.                                     compromises,” in 2019 IEEE Symposium on Security and Privacy, SP
[44] T. Hader, D. Kaufmann, A. Irfan, S. Graham-Lengrand, and L. Kovács,               2019, San Francisco, CA, USA, May 19-23, 2019. IEEE, 2019, pp.
     “Mcsat-based finite field reasoning in the yices2 SMT solver (short                1202–1219.
     paper),” in Automated Reasoning - 12th International Joint Conference,        [66] D. Monniaux and S. Boulmé, “The trusted computing base of the
     IJCAR 2024, Nancy, France, July 3-6, 2024, Proceedings, Part I, ser.               compcert verified compiler,” in Programming Languages and Systems
     Lecture Notes in Computer Science, C. Benzmüller, M. J. H. Heule, and             - 31st European Symposium on Programming, ESOP 2022, Held as
     R. A. Schmidt, Eds., vol. 14739. Springer, 2024, pp. 386–395.                      Part of the European Joint Conferences on Theory and Practice of
[45] M. Isabel, E. Rodrı́guez-Carbonell, C. Rodrı́guez-Núñez, and A. Rubio,           Software, ETAPS 2022, Munich, Germany, April 2-7, 2022, Proceedings,
     “An effective orchestral approach to satisfiability modulo prime fields,”          ser. Lecture Notes in Computer Science, I. Sergey, Ed., vol. 13240.
     CoRR, vol. abs/2604.26709, 2026.                                                   Springer, 2022, pp. 204–233.
[46] E. Pertseva, V. Robert, C. W. Barrett, and J. Parker, “Automating             [67] J. Thaler, “Getting the bugs out of snarks: The road ahead,” 2024,
     bitvector and finite field equivalence proofs in lean,” CoRR, vol.                 accessed: 2026-06-18. [Online]. Available: https://a16zcrypto.com/pos
     abs/2605.15163, 2026.                                                              ts/article/getting-bugs-out-of-snarks/
[47] Formal Land, “Formal verification of the Keccak precompile                    [68] powdr Labs, “Accelerating Ethereum with autoprecompiles,” https://ww
     from Plonky3,” 2026, accessed: 2026-06-18. [Online]. Available:                    w.powdr.org/blog/accelerating-ethereum-with-autoprecompiles, 2025,
     https://formal.land/blog/2026/01/14/formal-verification-keccak-plonky3             accessed: 2026-06-18.
[48] Nethermind, “We verified the verifier: a first for zero-knowledge             [69] Verified-zkEVM, “ArkLib: Formally verified arguments of knowledge,”
     proof systems,” 2025, accessed: 2026-06-18. [Online]. Available:                   2025. [Online]. Available: https://github.com/Verified-zkEVM/ArkLib
     https://www.nethermind.io/blog/we-verified-the-verifier-a-first-for-zer       [70] C. Lund, L. Fortnow, H. J. Karloff, and N. Nisan, “Algebraic methods
     o-knowledge-proof-systems                                                          for interactive proof systems,” J. ACM, vol. 39, no. 4, pp. 859–868,
[49] Ethereum Foundation, “Verified zkEVM project,” 2025, accessed:                     1992.
     2026-06-18. [Online]. Available: https://verified-zkevm.org                   [71] E. Ben-Sasson, I. Bentov, Y. Horesh, and M. Riabzev, “Fast reed-
[50] Ethereum Foundation (eth-act), “zkVM standards for Ethereum,” https:               solomon interactive oracle proofs of proximity,” in 45th International
     //github.com/eth-act/zkvm-standards, 2026.                                         Colloquium on Automata, Languages, and Programming, ICALP 2018,
[51] Veridise, “Verifying SP1 circuit determinism with Picus: A collaboration           Prague, Czech Republic, July 9-13, 2018, ser. LIPIcs, I. Chatzigiannakis,
     between Veridise and Succinct,” https://veridise.com/blog/audit-insight            C. Kaklamanis, D. Marx, and D. Sannella, Eds., vol. 107. Schloss
     s/verifying-sp1-circuit-determinism-with-picus-a-collaboration-betwe               Dagstuhl - Leibniz-Zentrum für Informatik, 2018, pp. 14:1–14:17.
     en-veridise-and-succinct/, 2025.                                              [72] G. Arnon, A. Chiesa, G. Fenzi, and E. Yogev, “WHIR: reed-solomon
[52] ——, “RISC Zero’s ZK-VM security: How Veridise enabled provable                     proximity testing with super-fast verification,” in Advances in Cryptology
     & continuous ZK security,” 2025, accessed: 2026-06-18. [Online].                   - EUROCRYPT 2025 - 44th Annual International Conference on the
     Theory and Applications of Cryptographic Techniques, Madrid, Spain,        [90] X. Peng, Z. Sun, K. Zhao, Z. Ma, Z. Li, J. Jiang, X. Luo, and Y. Zhang,
     May 4-8, 2025, Proceedings, Part IV, ser. Lecture Notes in Computer             “Automated soundness and completeness vetting of polygon zkevm,” in
     Science, S. Fehr and P. Fouque, Eds., vol. 15604. Springer, 2025, pp.           34th USENIX Security Symposium, USENIX Security 2025, Seattle, WA,
     214–243.                                                                        USA, August 13-15, 2025, L. Bauer and G. Pellegrino, Eds. USENIX
[73] A. Chiesa and M. Orrù, “A fiat-shamir transformation from duplex               Association, 2025, pp. 4093–4108.
     sponges,” in Theory of Cryptography - 23rd International Conference,       [91] C. Hochrainer, V. Wüstholz, and M. Christakis, “Arguzz: Testing zkvms
     TCC 2025, Aarhus, Denmark, December 1-5, 2025, Proceedings, Part I,             for soundness and completeness bugs,” CoRR, vol. abs/2509.10819,
     ser. Lecture Notes in Computer Science, B. Applebaum and H. R. Lin,             2025.
     Eds., vol. 16268. Springer, 2025, pp. 452–474.                             [92] H. Chen, M. Pendleton, L. Njilla, and S. Xu, “A survey on ethereum
[74] U. Haböck, “Multivariate lookups based on logarithmic derivatives,”            systems security: Vulnerabilities, attacks, and defenses,” ACM Comput.
     IACR Cryptol. ePrint Arch., vol. 2022, p. 1530, 2022.                           Surv., vol. 53, no. 3, pp. 67:1–67:43, 2021.
[75] S. T. V. Setty and J. Thaler, “Twist and shout: Faster memory checking     [93] D. Harz and W. J. Knottenbelt, “Towards safer smart contracts: A survey
     arguments via one-hot addressing and increments,” IACR Cryptol. ePrint          of languages and verification methods,” CoRR, vol. abs/1809.09805,
     Arch., vol. 2025, p. 105, 2025.                                                 2018.
[76] C. Gunton, “On formal verification and a bug in SP1 Hypercube,”            [94] S. S. Kushwaha, S. Joshi, D. Singh, M. Kaur, and H. Lee, “Ethereum
     2026, accessed: 2026-06-18. [Online]. Available: https://zkevm.ethere           smart contract analysis tools: A systematic review,” IEEE Access,
     um.foundation/blog/sp1-fv                                                       vol. 10, pp. 57 037–57 062, 2022.
[77] N. Kobeissi, “Verification theatre: False assurance in formally verified
     cryptographic libraries,” Cryptology ePrint Archive, Paper 2026/192,
     2026.
[78] R. Feldt and A. Magazinius, “Validity threats in empirical software
     engineering research - an initial survey,” in Proceedings of the 22nd
     International Conference on Software Engineering & Knowledge Engi-
     neering (SEKE’2010), Redwood City, San Francisco Bay, CA, USA, July
     1 - July 3, 2010. Knowledge Systems Institute Graduate School, 2010,
     pp. 374–379.
[79] X. Tang, L. Shi, X. Wang, K. Charbonnet, S. Tang, and S. Sun, “Zero-
     knowledge proof vulnerability analysis and security auditing,” IACR
     Cryptol. ePrint Arch., vol. 2024, p. 514, 2024.
[80] A. Coglio, E. McCarthy, and E. W. Smith, “Formal verification of zero-
     knowledge circuits,” in Proceedings of the 18th International Workshop
     on the ACL2 Theorem Prover and Its Applications, Austin, TX, USA and
     online, November 13-14, 2023, ser. EPTCS, A. Coglio and S. Swords,
     Eds., vol. 393, 2023, pp. 94–112.
[81] C. Chin, H. Wu, R. Chu, A. Coglio, E. McCarthy, and E. Smith,
     “Leo: A programming language for formally verified, zero-knowledge
     applications,” IACR Cryptol. ePrint Arch., vol. 2021, p. 651, 2021.
[82] A. Ozdemir, R. S. Wahby, F. Brown, and C. W. Barrett, “Bounded
     verification for finite-field-blasting in a compiler for zero knowledge
     proofs,” Formal Methods Syst. Des., vol. 67, no. 2, pp. 161–188, 2025.
[83] W. D. Nguyen, D. Boneh, and S. T. V. Setty, “Revisiting the nova
     proof system on a cycle of curves,” in 5th Conference on Advances
     in Financial Technologies, AFT 2023, Princeton, NJ, USA, October 23-
     25, 2023, ser. LIPIcs, J. Bonneau and S. M. Weinberg, Eds., vol. 282.
     Schloss Dagstuhl - Leibniz-Zentrum für Informatik, 2023, pp. 18:1–
     18:22.
[84] D. Khovratovich, R. D. Rothblum, and L. Soukhanov, “How to prove
     false statements: Practical attacks on fiat-shamir,” in Advances in
     Cryptology - CRYPTO 2025 - 45th Annual International Cryptology
     Conference, Santa Barbara, CA, USA, August 17-21, 2025, Proceedings,
     Part VI, ser. Lecture Notes in Computer Science, Y. T. Kalai and S. F.
     Kamara, Eds., vol. 16005. Springer, 2025, pp. 3–26.
[85] D. Xiao, Z. Liu, Y. Peng, and S. Wang, “MTZK: testing and exploring
     bugs in zero-knowledge (ZK) compilers,” in 32nd Annual Network
     and Distributed System Security Symposium, NDSS 2025, San Diego,
     California, USA, February 24-28, 2025. The Internet Society, 2025.
[86] C. Hochrainer, A. Isychev, V. Wüstholz, and M. Christakis, “Fuzzing
     processing pipelines for zero-knowledge circuits,” in Proceedings of
     the 2025 ACM SIGSAC Conference on Computer and Communications
     Security, CCS 2025, Taipei, Taiwan, October 13-17, 2025, C. Huang,
     J. Chen, S. Shieh, D. Lie, and V. Cortier, Eds. ACM, 2025, pp. 783–
     797.
[87] S. Chaliasos, D. Firsov, and B. Livshits, “Towards a formal foundation
     for blockchain ZK rollups,” in Proceedings of the 2025 ACM SIGSAC
     Conference on Computer and Communications Security, CCS 2025,
     Taipei, Taiwan, October 13-17, 2025, C. Huang, J. Chen, S. Shieh,
     D. Lie, and V. Cortier, Eds. ACM, 2025, pp. 2714–2728.
[88] F. G. Figueira, M. Derka, C. L. Chiu, and J. Gorzny, “A practical
     rollup escape hatch design,” in 2025 IEEE International Conference
     on Blockchain and Cryptocurrency, ICBC 2025, Pisa, Italy, June 2-6,
     2025. IEEE, 2025, pp. 1–5.
[89] S. Chaliasos, C. Swann, S. Pilehchiha, N. Mohnblatt, B. Livshits, and
     A. Kattis, “Unaligned incentives: Pricing attacks against blockchain
     rollups,” CoRR, vol. abs/2509.17126, 2025.
