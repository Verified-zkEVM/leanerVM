import LeanerVM.Protocol.Headline
import LeanerVMTests.Protocol.RandomOracleGame
import LeanerVMTests.Arithmetization.Steps
import LeanerVMTests.Arithmetization.Sentinel
import LeanerVMTests.Semantics.FillBlocks
import LeanerVMTests.Arithmetization.Completeness.Theorem
import LeanerVMTests.Protocol.LogScan

/-!
# The headline theorems: tests

* **Nothing is extracted from the empty log** (`extract_nil`), whatever the proof: every row
  reads zero, the transform's exact path decodes the zero word to the zero stack alone, and the
  zero stack's read counts are zero, which leanISA's relation forbids. The extractor at the
  deployed sizes is out of the interpreter's reach, so this is a theorem, not a run.
* **The replayer.** The adversary `pure proof` outputs a stored proof and asks nothing. If `verify`
  accepts the proof, its one run under BLAKE2s misbehaves (the verifier's recomputed root is a
  fresh answer equal to a root of the proof, a hit), so it fails `BlakeMisbehaves` at every
  `δ < 1` (`replayer_not_blakeMisbehaves`). The `leanervm-verify` executable checks that `verify`
  accepts the Rust proof and the test vector.
* **The honest prover's hashes.** `scan` (`LeanerVMTests.Protocol.LogScan`) finds the collisions
  and hits of a joint log in one pass with hash maps; it agrees with `QueryLog.HasCollision` and
  `HitFrom []` on the logs below, which cover a hit through a half, through the program hash a
  seed preimage carries, through a root two observe steps rebuild in either order, through a root
  of the proof, none on a repeated query, and none on an answer equal to the test statement's
  first state, which is in play only once its query is asked. The
  `leanervm-prove` executable (`log`) runs the honest prover on the test vector's witness and the
  verifier on its proof, every hash logged, and checks that the joint log has no collision and no
  hit, and that `extract` on the prover's log returns the witness's sizes and stack. A flip is
  not decidable (its bad set quantifies over a witness), so no claim is made that the honest run
  has none.
* **The deployed verifier** is `verifyWith` at BLAKE2s in `Id`, and the verifier on the oracle,
  run with BLAKE2s answering, is `pure` of it (`verifyWith_simulateQ`, `verifyWith_pure`). The
  same holds from the seed's hashes (`verifyFrom` from `FsState.seedWith`), whose state at
  BLAKE2s is the test statement's first state.
* **The adaptive forms.** At a fixed statement the adaptive hypothesis is the selective one
  (`blakeMisbehavesAdaptive_const`). The adaptive replayer, `pure (prog, input, proof)`, fails it
  at every `δ < 1` when `verify` accepts (`adaptiveReplayer_not_blakeMisbehaves`), while with the
  hash a random function its proof is accepted with probability at most
  `13700/2^128 + hashTerm 13700 0` (`adaptiveReplayer_ok_le`, through `extract_nil`): the random
  oracle draws the challenges after the statement is chosen. An adversary that asks one hash and
  picks one of two statements from its answer (`chooser`) asks one query, and the adaptive
  random-oracle theorem bounds it at `Q = 1`. An adversary that only outputs the test vector's
  program meets the well-formedness hypothesis of
  `baseVerifier_extractsExecution_adaptive_wellFormed` (an `example`).
* **A proof `verify` accepts of a statement with no execution**
  (`verify_accepts_without_execution`): for the sentinel tests' program, whose sentinel slot is a
  `JUMP`, `verify` accepts every proof `prove` returns for its witness, and the program has no
  valid execution on the input over any memory. The `leanervm-prove sentinel` executable runs
  `prove` on that witness and checks that `verify` accepts its proof.
-/

namespace LeanerVMTests.Protocol.Headline

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization LeanerVM.Protocol
open LeanerVM.Protocol.Blake2sHash LeanerVM.Protocol.LeanIsa LeanerVM.Protocol.Verify
open LeanerVM.Protocol.ProofRoots LeanerVM.Protocol.LeanVmReader OracleComp OracleSpec
open LeanerVMTests.Protocol.Proof (program input)
open LeanerVMTests.Protocol.RandomOracleGame (d nodeA nodeV)
open LeanerVMTests.Arithmetization.Statement (fillProg mulInput)
open LeanerVMTests.Arithmetization.Steps (fill_sentinelSafe)
open LeanerVMTests.Semantics.FillBlocks (ladderProg ladder_wellFormed)
open LeanerVMTests.Semantics.PaddedImageRefutation (ladderJumpProg badInput ladderJump_wellFormed)
open LeanerVMTests.Arithmetization.Completeness.Theorem (badTrace badTrace_valid badTrace_fits)
open LeanerVMTests.Arithmetization.Sentinel (sentProg sentW sent_not_safe sent_satisfiedBy
  sent_no_execution)
open LeanerVMTests.Protocol.LogScan (entries scan)
open LeanerVM.Parameters.Whir (queryGrindingBits)
open scoped ENNReal

/-! ## Nothing is extracted from the empty log -/

/-- The empty log answers no leaf: every row reads zero. -/
theorem wordRows_nil (root : Digest) (depth rowWords ℓ : ℕ) (y : Fin (2 ^ depth))
    (u : Fin (2 ^ ℓ)) : (wordRows [] root depth rowWords ℓ)[y][u] = 0 := by
  have hnone : ∀ x ∈ extractAllRows [] root depth rowWords (2 ^ ℓ), x = none := by
    intro x hx
    rw [extractAllRows_eq] at hx
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hx
    have key : ∀ (o : Option Digest) (f : Digest → Option (List K)), (∀ d, f d = none) →
        o.bind f = none := by
      rintro (_ | d) f hf
      · rfl
      · exact hf d
    exact key _ _ fun _ ↦ rfl
  have hrow : ((extractAllRows [] root depth rowWords (2 ^ ℓ))[y.val]?.bind fun a ↦ a) = none := by
    cases h : (extractAllRows [] root depth rowWords (2 ^ ℓ))[y.val]? with
    | none => rfl
    | some x => simpa using hnone x (List.mem_of_getElem? h)
  simp only [wordRows, LeanerVM.Protocol.laneRow]
  simp [hrow]

/-- The zero messages. -/
def zeroMsgs (m κ : ℕ) : Whir.Msgs m κ := fun _ ↦ Vector.replicate (2 ^ κ) 0

/-- The transform's exact path reads the zero word as the zero messages. -/
theorem exactNtt_zero {κ R ℓ : ℕ} (hb : κ + R ≤ 64) {F : Whir.LW (κ + R)}
    (hF : ∀ y (u : Fin (2 ^ ℓ)), F y u = 0) : Whir.exactNtt κ R ℓ F = some (zeroMsgs ℓ κ) :=
  Whir.exactNtt_of_codeword hb fun y u ↦ by
    rw [hF, encode_eq_sum]
    simp [zeroMsgs]

/-- The stack of the zero messages is zero. -/
theorem stackOfMsgs_zero (I : M3Instance) {sh : Whir.Shape} {κ : ℕ} (hμ : κ + sh.ℓ = I.μ)
    (i : Fin (2 ^ I.μ)) : (stackOfMsgs I hμ (zeroMsgs sh.ℓ κ)).values.get i = 0 := by
  have key : ∀ (n : ℕ) (h : κ + sh.ℓ = n) (v : CompPoly.CMlPolynomialEval K (κ + sh.ℓ)),
      (∀ j, v.get j = 0) → ∀ j, (h ▸ v : CompPoly.CMlPolynomialEval K n).get j = 0 := by
    intro n h
    subst h
    exact fun v hv ↦ hv
  refine key _ hμ _ (fun j ↦ ?_) i
  simp [relayout, Whir.ofLanes, zeroMsgs, limb_zero]

/-- A zero stack fails the relation at an instance with a count column: its count cells are
zero. -/
theorem not_m3Holds_of_zero (I : M3Instance) (input : I.Stmt) (q : Column I.μ)
    (hq : ∀ i, q.values.get i = 0) {j : Fin I.ntab} {c : Fin (I.width j)} (hc : c ∈ I.counts j) :
    ¬ M3Holds I input q := by
  rintro ⟨-, -, hcnt, -, -⟩
  apply hcnt j c hc ⟨0, Nat.two_pow_pos _⟩
  have h : (I.column q ⟨j, c⟩).values.get ⟨0, Nat.two_pow_pos _⟩ =
      I.row q j ⟨0, Nat.two_pow_pos _⟩ c := rfl
  rw [h, M3Instance.row_eq_rowFast]
  exact hq _

/-- The deployed pick on a word of zeros returns nothing at an instance with a count column. -/
theorem deployedPick_zero (I : M3Instance) {r : ℕ} (h : Whir.Admissible I.μ r) (input : I.Stmt)
    (w : Whir.KWord (Whir.deployedHeadShape I.μ r).ℓ
      (Whir.deployedHeadKap I.μ r + (Whir.deployedHeadShape I.μ r).R)
      (Whir.deployedHeadShape I.μ r).t)
    (hw : ∀ y (u : Fin (2 ^ (Whir.deployedHeadShape I.μ r).ℓ)), (w.row y)[u] = 0)
    {j : Fin I.ntab} (hj : I.counts j ≠ []) : Whir.deployedPick I h input w = none := by
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ hj
  have hb : Whir.deployedHeadKap I.μ r + (Whir.deployedHeadShape I.μ r).R ≤ 64 := by
    have hd := Whir.deployedChain_head h
    exact hd.1 ▸ hd.2.1 ▸
      ((Whir.deployedChain I.μ r h).ladder.headPar (Whir.deployedChain I.μ r h).pars).hb
  have hF : ∀ y (u : Fin (2 ^ (Whir.deployedHeadShape I.μ r).ℓ)), w.lift.lanes y u = 0 := by
    intro y u
    have h' : w.lift.lanes y u = ofK (w.row y)[u] := by
      simp [Whir.Word.lanes, Whir.KWord.lift, Vector.getD, u.2]
    rw [h', hw y u]
    exact map_zero (algebraMap K E)
  unfold Whir.deployedPick commitPick stackList Whir.deployedHeadDecoder
  simp only [Whir.ListDecoder.nttFirst, exactNtt_zero hb hF]
  simp [not_m3Holds_of_zero I input _ (stackOfMsgs_zero I _) hc]

/-- **Nothing is extracted from the empty log**, whatever the proof: every row reads zero, the
zero word decodes to the zero stack alone, and the zero stack's read counts are zero, which
leanISA's relation forbids. -/
theorem extract_nil (F : FlockSpec) (prog : Program) (input : PublicInput)
    (proof : Proof PrunedMerklePaths) : extract F prog input proof [] = none := by
  unfold extract
  split
  · rfl
  · split
    · split
      · rfl
      · rename_i _ s _ _ _ _ _ _
        have hcounts : (leanIsaInstance F prog s).counts ⟨3, by show 3 < 9; decide⟩ ≠ [] := by
          show LeanIsa.counts ⟨3, by decide⟩ ≠ []
          decide +kernel
        dsimp only
        rw [Option.map_eq_none_iff]
        apply deployedPick_zero _ _ _ _ _ hcounts
        intro y u
        exact wordRows_nil _ _ _ _ _ _
    · rfl

/-- No stack satisfying the relation is extracted from the empty log, whatever the proof. -/
theorem not_extracts_nil (F : FlockSpec) (prog : Program) (input : PublicInput)
    (proof : Proof PrunedMerklePaths) : ¬ Extracts F prog input proof [] := by
  rw [extracts_iff_isSome, extract_nil]
  exact Bool.false_ne_true

/-! ## The replayer -/

/-- **The replayer**: it outputs a stored proof and asks nothing. -/
abbrev replayer (proof : Proof PrunedMerklePaths) : Adversary := pure proof

/-- The replayer's runs carry its proof and an empty prover's log. -/
theorem replayer_run {prog : Program} {input : PublicInput} {proof : Proof PrunedMerklePaths}
    {g : Run} (hg : g ∈ support (loggedGame verifyWith prog input (replayer proof))) :
    g.proof = proof ∧ g.logA = [] := by
  simp only [loggedGame, withQueryLog_pure, pure_bind, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hg
  obtain ⟨_, _, rfl⟩ := hg
  exact ⟨rfl, rfl⟩

/-- **The replayer fails the hypothesis** at every `δ < 1`, when `verify` accepts its proof:
nothing is extracted from its empty log, so its one run misbehaves. -/
theorem replayer_not_blakeMisbehaves {prog : Program} {input : PublicInput}
    {proof : Proof PrunedMerklePaths} {δ : ℝ≥0∞} (hacc : verify prog input proof = true)
    (hδ : δ < 1) :
    ¬ BlakeMisbehaves prog input (replayer proof) δ := by
  intro hB
  have h1 : Pr{let g ← runBlake2s (loggedGame verifyWith prog input (replayer proof))}[
      HashMisbehavesFrom [] (rootsOf prog input) (leanVmReader.FlipFor (prog, input)) g] = 1 :=
    OracleComp.prEvent_eq_one_of_forall_mem_support _ _ fun g hg ↦ by
      obtain ⟨hg', hc, hok⟩ := mem_support_runBlake2s hg
      obtain ⟨hp, hl⟩ := replayer_run hg'
      exact Core.core_of_mem_support hg' hc (hok.trans (hp ▸ hacc))
        (hp ▸ hl ▸ not_extracts_nil _ _ _ _)
  unfold BlakeMisbehaves at hB
  rw [h1] at hB
  exact absurd hδ (not_lt.mpr hB)

/-! ## Collisions and hits, in one pass -/

/-- `scan` from no root in play at the start. -/
def scanAt (roots : List Digest) (nA : ℕ) (log : hashSpec.QueryLog) : Bool × Bool :=
  scan [] roots nA (entries log)

/-- `scan` agrees with the definitions on a run of the given logs. -/
def scanAgrees (roots : List Digest) (logA logV : hashSpec.QueryLog) : Bool :=
  let g : Run := ⟨⟨[], []⟩, logA, logV, true⟩
  scanAt roots logA.length g.log ==
    (decide (QueryLog.HasCollision g.log), decide (HitFrom [] (fun _ ↦ roots) g))

/-- The chain's first state at the test statement. -/
def s₀ : Digest := (FsState.seed program input).cv

#guard (Id.run (FsState.seedWith blake2sBytes program input)).cv == s₀

/-- A root the chain absorbs as two observe steps, answered by `d 1` and `d 2`. -/
def absorbed : hashSpec.QueryLog :=
  [⟨Block.input s₀ (.observe (digestScalars (d 9)).1), d 1⟩,
    ⟨Block.input (d 1) (.observe (digestScalars (d 9)).2), d 2⟩]

/- A hit through a half: the verifier's query answered by a child of the prover's node. -/
#guard scanAgrees [] nodeA nodeV && (scanAt [] 1 (nodeA ++ nodeV)).2
/- A collision. -/
#guard scanAgrees [] [⟨[1], d 1⟩] [⟨[2], d 1⟩] &&
  (scanAt [] 1 [⟨[1], d 1⟩, ⟨[2], d 1⟩]).1
/- The rebuilt root `d 9` is in play after the two observe steps, and not before. -/
#guard scanAgrees [] (absorbed ++ [⟨[5], d 9⟩]) [] &&
  (scanAt [] 3 (absorbed ++ [⟨[5], d 9⟩])).2
#guard scanAgrees [] (⟨[5], d 9⟩ :: absorbed) [] &&
  !(scanAt [] 3 (⟨[5], d 9⟩ :: absorbed)).2
/- The two observe steps in the other order: the step from `d 1` before the step answered by
`d 1`; the root is rebuilt when the second arrives. -/
#guard scanAgrees [] (absorbed.reverse ++ [⟨[5], d 9⟩]) [] &&
  (scanAt [] 3 (absorbed.reverse ++ [⟨[5], d 9⟩])).2
/- A verifier's fresh query answered by a root of the proof, and the same query asked first by
the prover. -/
#guard scanAgrees [d 9] [⟨[1], d 1⟩] [⟨[2], d 9⟩] &&
  (scanAt [d 9] 1 [⟨[1], d 1⟩, ⟨[2], d 9⟩]).2
#guard scanAgrees [d 9] [⟨[2], d 9⟩] [⟨[2], d 9⟩] &&
  !(scanAt [d 9] 1 [⟨[2], d 9⟩, ⟨[2], d 9⟩]).2
/- The program hash a seed's preimage carries: a later query answered by it. -/
#guard scanAgrees [] [⟨seedPreimageOf (d 1), d 2⟩, ⟨[5], d 1⟩] [] &&
  (scanAt [] 2 [⟨seedPreimageOf (d 1), d 2⟩, ⟨[5], d 1⟩]).2
/- An answer equal to the chain's first state is no hit: the state is in play only once its query
is asked. -/
#guard scanAgrees [] [⟨[3], s₀⟩] [] && !(scanAt [] 1 [⟨[3], s₀⟩]).2
/- A clean log. -/
#guard scanAgrees [d 9] [⟨[1], d 1⟩] [⟨[2], d 2⟩] &&
  scanAt [d 9] 1 [⟨[1], d 1⟩, ⟨[2], d 2⟩] == (false, false)

/-! ## The deployed verifier -/

/-- `verify` is `verifyWith` at BLAKE2s, in `Id`. -/
example (prog : Program) (input : PublicInput) (proof : Proof PrunedMerklePaths) :
    verify prog input proof = verifyWith (m := Id) blake2sBytes prog input proof := rfl

/-- The verifier on the oracle, run with BLAKE2s answering, is `pure` of `verify`. -/
example (prog : Program) (input : PublicInput) (proof : Proof PrunedMerklePaths) :
    runBlake2s (verifyWith hashQuery prog input proof) = pure (verify prog input proof) :=
  (verifyWith_simulateQ _ prog input proof).trans (verifyWith_pure _ _ _ _)

/-- `verify` is `verifyFrom` at BLAKE2s from the seed's hashes, in `Id`. -/
example (prog : Program) (input : PublicInput) (proof : Proof PrunedMerklePaths) :
    verify prog input proof =
      verifyFrom (m := Id) blake2sBytes (FsState.seedWith blake2sBytes prog input) prog input
        proof := rfl

/-- The verifier on the oracle from the seed's hashes as queries, run with BLAKE2s answering, is
`pure` of `verify`. -/
example (prog : Program) (input : PublicInput) (proof : Proof PrunedMerklePaths) :
    runBlake2s (verifyFrom hashQuery (FsState.seedWith hashQuery prog input) prog input proof) =
      pure (verify prog input proof) := by
  refine (verifyFrom_simulateQ _ _ prog input proof).trans ?_
  rw [show simulateQ _ (FsState.seedWith hashQuery prog input) = _ from
    FsState.seedWith_simulateQ _ prog input]
  have h := verifyFrom_hom (MonadHom.pure ProbComp) (m := Id) blake2sBytes
    (FsState.seedWith blake2sBytes prog input) prog input proof
  rw [FsState.seedWith_hom] at h
  simp only [MonadHom.pure_apply] at h
  exact h.symm

/- A proof with no announcement: `verify` rejects it, and nothing is extracted. -/
#guard !verify program input ⟨[], []⟩
example (hsafe : SentinelSafe program) :
    extractTrace (leanIsaTraceExtraction hsafe) input ⟨[], []⟩ [] = none := rfl

/-! ## The theorems, at the test statement -/

example (A : Adversary) {Q : ℕ} (hQ : IsTotalQueryBound A Q) :
    Pr{let z ← runRandom (loggedGame verifyWith program input A)}[
      z.1.ok = true ∧ ¬ ∃ e,
        extract Blake2sFlock.blake2sFlockSpec program input z.1.proof z.1.logA = some e ∧
          SatisfiedBy program input (witnessOf Blake2sFlock.blake2sFlockSpec program e.1 e.2)] ≤
      ((Q + 13700 : ℕ) / 2 ^ 128 + hashTerm 13700 Q : NNReal) :=
  baseVerifier_extractsWitness_rom hQ

/- The execution form at the test vector's program, whose sentinel slot is not a `JUMP`. -/
example (A : Adversary) {δ : ℝ≥0∞} (hB : BlakeMisbehaves fillProg mulInput A δ) :
    Pr{let g ← runBlake2s (loggedGame verifyWith fillProg mulInput A)}[
      verify fillProg mulInput g.proof = true ∧ ¬ ∃ t,
        extractExecution fillProg mulInput g.proof g.logA = some t ∧
          ValidExecution fillProg mulInput t] ≤ δ :=
  baseVerifier_extractsExecution fill_sentinelSafe hB

/- The random-oracle execution form at the test vector's program. -/
example (A : Adversary) {Q : ℕ} (hQ : IsTotalQueryBound A Q) :
    Pr{let z ← runRandom (loggedGame verifyWith fillProg mulInput A)}[
      z.1.ok = true ∧ ¬ ∃ t, extractExecution fillProg mulInput z.1.proof z.1.logA = some t ∧
        ValidExecution fillProg mulInput t] ≤
      ((Q + 13700 : ℕ) / 2 ^ 128 + hashTerm 13700 Q : NNReal) :=
  baseVerifier_extractsExecution_rom fill_sentinelSafe hQ

/- At a program whose sentinel slot is a `JUMP` the extractor returns nothing. -/
example (proof : Proof PrunedMerklePaths) (log : hashSpec.QueryLog) :
    extractExecution sentProg mulInput proof log = none := by
  simp [extractExecution, sent_not_safe]

/-! ## Completeness from an execution -/

/- **The completeness headline at an instance**: its hypotheses hold of the one-step trace of
well-formed bytecode in the completeness tests, so its conclusion is not vacuous there. -/
example : ∃ t' : Trace ladderJumpProg, t'.PaddedFrom badTrace ∧
    ValidExecution ladderJumpProg badInput t' ∧
      ∃ w : Air.Flat.EnsembleWitness (leanIsaEnsemble ladderJumpProg t'.κ),
        SatisfiedBy ladderJumpProg badInput w ∧ AssignmentRepresents w t' ∧ ∀ fuel ρ,
          (∀ proof, prove fuel ladderJumpProg badInput w ρ = some proof →
            verify ladderJumpProg badInput proof = true) ∧
          (prove fuel ladderJumpProg badInput w ρ = none → ∃ s, Sizes.ofWitness w = some s ∧
            (maxMu < leanIsaμ ladderJumpProg s ∨ ¬ validRate ρ ∨
              ∃ fs : FsState, Id.run (fs.grind blake2sBytes fuel queryGrindingBits) = none)) :=
  prove_complete_of_execution ladderJump_wellFormed badTrace_valid badTrace_fits

/-! ## The adaptive theorems -/

/-- **The adaptive replayer**: it outputs a stored statement and proof and asks nothing. -/
abbrev adaptiveReplayer (prog : Program) (input : PublicInput)
    (proof : Proof PrunedMerklePaths) : AdaptiveAdversary :=
  pure (prog, input, proof)

/-- The adaptive replayer's runs carry its statement and proof and an empty prover's log. -/
theorem adaptiveReplayer_run {prog : Program} {input : PublicInput}
    {proof : Proof PrunedMerklePaths} {g : AdaptiveRun}
    (hg : g ∈ support (adaptiveGame verifyWith (adaptiveReplayer prog input proof))) :
    g.prog = prog ∧ g.input = input ∧ g.proof = proof ∧ g.logA = [] := by
  simp only [adaptiveGame, withQueryLog_pure, pure_bind, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hg
  obtain ⟨_, _, rfl⟩ := hg
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- **The adaptive replayer fails the hypothesis** at every `δ < 1`, when `verify` accepts its
statement and proof: nothing is extracted from its empty log, so its one run misbehaves. -/
theorem adaptiveReplayer_not_blakeMisbehaves {prog : Program} {input : PublicInput}
    {proof : Proof PrunedMerklePaths} {δ : ℝ≥0∞} (hacc : verify prog input proof = true)
    (hδ : δ < 1) :
    ¬ BlakeMisbehavesAdaptive (adaptiveReplayer prog input proof) δ := by
  intro hB
  have h1 : Pr{let g ← runBlake2s (adaptiveGame verifyWith (adaptiveReplayer prog input proof))}[
      HashMisbehavesFrom [] (rootsOf g.prog g.input) (leanVmReader.FlipFor (g.prog, g.input))
        g.toRun] = 1 :=
    OracleComp.prEvent_eq_one_of_forall_mem_support _ _ fun g hg ↦ by
      obtain ⟨hg', hc, hok⟩ := mem_support_runBlake2s_adaptive hg
      obtain ⟨hp, hi, hpr, hl⟩ := adaptiveReplayer_run (QueryLog.support_simulateQ_subset _ _ hg)
      subst hp hi
      exact Core.core_of_mem_support hg' hc (hok.trans (hpr ▸ hacc))
        (hpr ▸ hl ▸ not_extracts_nil _ _ _ _)
  unfold BlakeMisbehavesAdaptive at hB
  rw [h1] at hB
  exact absurd hδ (not_lt.mpr hB)

/-- **The adaptive replayer's proof is accepted with small probability** when the hash is a random
function: nothing is extracted from its empty log, so the adaptive random-oracle theorem at
`Q = 0` bounds its acceptance. -/
theorem adaptiveReplayer_ok_le (prog : Program) (input : PublicInput)
    (proof : Proof PrunedMerklePaths) :
    Pr{let z ← runRandom (adaptiveGame verifyWith (adaptiveReplayer prog input proof))}[
      z.1.ok = true] ≤ ((0 + 13700 : ℕ) / 2 ^ 128 + hashTerm 13700 0 : NNReal) :=
  (OracleComp.prEvent_mono_of_support _ fun z hz h ↦ ⟨h, fun ⟨e, he, _⟩ ↦ by
    obtain ⟨-, -, -, hl⟩ := adaptiveReplayer_run (mem_support_runRandom_adaptive hz).1
    rw [hl, extract_nil] at he
    cases he⟩).trans (baseVerifier_extractsWitness_rom_adaptive (Q := 0) trivial)

-- At a fixed statement the adaptive hypothesis is the selective one.
example (prog : Program) (input : PublicInput) (A : Adversary) (δ : ℝ≥0∞) :
    BlakeMisbehavesAdaptive ((fun proof ↦ (prog, input, proof)) <$> A) δ ↔
      BlakeMisbehaves prog input A δ :=
  blakeMisbehavesAdaptive_const prog input A δ

/-- **An adversary that chooses the statement from a hash**: it asks the hash of one byte and,
by the answer's first word's parity, outputs one of two statements with the proof. -/
def chooser (st₀ st₁ : Program × PublicInput) (proof : Proof PrunedMerklePaths) :
    AdaptiveAdversary := do
  let h ← hashQuery [0]
  let st := if h[0] % 2 = 0 then st₀ else st₁
  return (st.1, st.2, proof)

/-- The chooser asks one query. -/
theorem chooser_queries (st₀ st₁ : Program × PublicInput) (proof : Proof PrunedMerklePaths) :
    IsTotalQueryBound (chooser st₀ st₁ proof) 1 :=
  isTotalQueryBound_query_bind_iff.mpr ⟨Nat.one_pos, fun _ ↦ trivial⟩

-- The adaptive random-oracle theorem at the chooser, between the test statement and the test
-- vector's: one prover query.
example (proof : Proof PrunedMerklePaths) :
    Pr{let z ← runRandom (adaptiveGame verifyWith
        (chooser (program, input) (fillProg, mulInput) proof))}[z.1.ok = true ∧ ¬ ∃ e,
      extract Blake2sFlock.blake2sFlockSpec z.1.prog z.1.input z.1.proof z.1.logA = some e ∧
        SatisfiedBy z.1.prog z.1.input (witnessOf Blake2sFlock.blake2sFlockSpec z.1.prog e.1 e.2)] ≤
      ((1 + 13700 : ℕ) / 2 ^ 128 + hashTerm 13700 1 : NNReal) :=
  baseVerifier_extractsWitness_rom_adaptive (chooser_queries _ _ _)

/- The execution form for an adversary that only ever outputs the fill-block ladder's program,
which is well-formed: the hypothesis on the adversary's programs is met. -/
example (A : Adversary) {δ : ℝ≥0∞}
    (hB : BlakeMisbehavesAdaptive ((fun proof ↦ (ladderProg, mulInput, proof)) <$> A) δ) :
    Pr{let g ← runBlake2s (adaptiveGame verifyWith
        ((fun proof ↦ (ladderProg, mulInput, proof)) <$> A))}[
      verify g.prog g.input g.proof = true ∧ ¬ ∃ t,
        extractExecution g.prog g.input g.proof g.logA = some t ∧
          ValidExecution g.prog g.input t] ≤ δ :=
  baseVerifier_extractsExecution_adaptive_wellFormed hB fun g hg ↦ by
    have hg' := QueryLog.support_simulateQ_subset _ _ hg
    rw [adaptiveGame_const, support_map] at hg'
    obtain ⟨_, -, rfl⟩ := hg'
    exact ladder_wellFormed

/-! ## The bytecode hypothesis cannot be dropped -/

/-- **A proof `verify` accepts of a statement with no execution**: for the sentinel tests'
program, with a `JUMP` in its sentinel slot, every proof `prove` returns for its witness. -/
theorem verify_accepts_without_execution {fuel ρ : ℕ} {proof : Proof PrunedMerklePaths}
    (hp : prove fuel sentProg mulInput sentW ρ = some proof) :
    verify sentProg mulInput proof = true ∧
      ∀ t : Trace sentProg, ¬ ValidExecution sentProg mulInput t :=
  ⟨prove_complete fuel sent_satisfiedBy hp, sent_no_execution⟩

end LeanerVMTests.Protocol.Headline
