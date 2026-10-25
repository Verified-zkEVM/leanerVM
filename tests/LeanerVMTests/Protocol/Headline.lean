import LeanerVM.Protocol.Headline
import LeanerVMTests.Protocol.RandomOracleGame
import LeanerVMTests.Arithmetization.Steps

/-!
# The headline theorems: tests

* **Nothing is extracted from the empty log** (`extract_nil`), whatever the proof: every row
  reads zero, the transform's exact path decodes the zero word to the zero stack alone, and the
  zero stack's read counts are zero, which leanISA's relation forbids. Deciding the relation on a
  stack at the deployed sizes decides the bus's permutation, quadratic in its length, so this is a
  theorem, not a run.
* **The replayer.** The adversary `pure proof` outputs a stored proof and asks nothing. If `verify`
  accepts the proof, its one run under BLAKE2s misbehaves (the verifier's recomputed root is a
  fresh answer equal to a root of the proof, a hit), so it fails `BlakeMisbehaves` at every
  `δ < 1` (`replayer_not_blakeMisbehaves`). The `leanervm-verify` executable checks that `verify`
  accepts the Rust proof and the test vector.
* **The honest prover's hashes.** `scan` finds the collisions and hits of a joint log in one pass
  with hash maps; it agrees with `QueryLog.HasCollision` and `Hit` on the logs below, which cover a
  hit through a half, through a root two observe steps rebuild, through a root of the proof, and
  none on a repeated query. The `leanervm-prove` executable (`log`) runs the honest prover on the
  test vector's witness and the verifier on its proof, every hash logged, and checks that the joint
  log has no collision and no hit. A flip is not decidable (its bad set quantifies over a
  witness), so no claim is made that the honest run has none.
* **The deployed verifier** is `verifyWith` at BLAKE2s in `Id`, and the verifier on the oracle,
  run with BLAKE2s answering, is `pure` of it (`verifyWith_simulateQ`, `verifyWith_pure`).
-/

namespace LeanerVMTests.Protocol.Headline

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization LeanerVM.Protocol
open LeanerVM.Protocol.Blake2sHash LeanerVM.Protocol.LeanIsa LeanerVM.Protocol.Verify
open LeanerVM.Protocol.ProofRoots LeanerVM.Protocol.LeanVmReader OracleComp OracleSpec
open LeanerVMTests.Protocol.Proof (program input)
open LeanerVMTests.Protocol.RandomOracleGame (d nodeA nodeV)
open LeanerVMTests.Arithmetization.Statement (fillProg mulInput)
open LeanerVMTests.Arithmetization.Steps (fill_sentinelSafe)
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
    (hδ : δ < 1) (hcore : CoreHolds prog input (replayer proof)) :
    ¬ BlakeMisbehaves prog input (replayer proof) δ := by
  intro hB
  have h1 : Pr{let g ← runBlake2s (loggedGame verifyWith prog input (replayer proof))}[
      HashMisbehaves (rootsOf prog input) (leanVmReader prog input).Flip prog input g] = 1 :=
    OracleComp.prEvent_eq_one_of_forall_mem_support _ _ fun g hg ↦ by
      obtain ⟨hg', hc, hok⟩ := mem_support_runBlake2s hg
      obtain ⟨hp, hl⟩ := replayer_run hg'
      exact hcore g hg' hc (hok.trans (hp ▸ hacc)) (hp ▸ hl ▸ not_extracts_nil _ _ _ _)
  unfold BlakeMisbehaves at hB
  rw [h1] at hB
  exact absurd hδ (not_lt.mpr hB)

/-! ## Collisions and hits, in one pass -/

/-- A logged query, compactly: its input's bytes and its answer. -/
abbrev Entry : Type := ByteArray × Digest

/-- A log, compactly. -/
def entries (log : hashSpec.QueryLog) : Array Entry :=
  log.toArray.map fun e ↦ (⟨e.1.toArray⟩, e.2)

attribute [local instance] Digest.hashable in
/-- **The collisions and hits of a joint log**, in one pass with hash maps. The first `nA` entries
are the prover's; `seed` lists the digests in play from the start, `roots` the proof's roots. An
entry is a collision when its digest answered an earlier, different input; a hit when its input is
new and its digest is in play (the seed, a half of an earlier input, a root rebuilt from two
earlier observe steps) or, past the prover's entries, a root of the proof. Then its halves and the
roots its observe step completes are put in play. -/
def scan (seed roots : List Digest) (nA : ℕ) (log : Array Entry) : Bool × Bool := Id.run do
  let rootSet : Std.HashSet Digest := Std.HashSet.ofList roots
  let mut answers : Std.HashMap Digest ByteArray := {}
  let mut seen : Std.HashSet ByteArray := {}
  let mut play : Std.HashSet Digest := Std.HashSet.ofList seed
  let mut firstObs : Std.HashMap Digest E := {}
  let mut pending : Std.HashMap Digest (Array E) := {}
  let mut collision := false
  let mut hit := false
  let mut k := 0
  for (t, a) in log do
    match answers[a]? with
    | some t' => if t' != t then collision := true
    | none => answers := answers.insert a t
    if !seen.contains t && (play.contains a || (nA ≤ k && rootSet.contains a)) then hit := true
    seen := seen.insert t
    let q := t.toList
    for h in halves q do
      play := play.insert h
    if let some (cv, x) := observed? q then
      match firstObs[cv]? with
      | some x₁ =>
        if let some r := digestOfScalars (x₁, x) then play := play.insert r
      | none => pending := pending.insert cv ((pending.getD cv #[]).push x)
      if !firstObs.contains a then
        firstObs := firstObs.insert a x
        for x' in pending.getD a #[] do
          if let some r := digestOfScalars (x, x') then play := play.insert r
        pending := pending.erase a
    k := k + 1
  return (collision, hit)

/-- `scan` at the test statement. -/
def scanAt (roots : List Digest) (nA : ℕ) (log : hashSpec.QueryLog) : Bool × Bool :=
  scan (seedDigests program input) roots nA (entries log)

/-- `scan` agrees with the definitions on a run of the given logs, at the test statement. -/
def scanAgrees (roots : List Digest) (logA logV : hashSpec.QueryLog) : Bool :=
  let g : Run := ⟨⟨[], []⟩, logA, logV, true⟩
  scanAt roots logA.length g.log ==
    (decide (QueryLog.HasCollision g.log), decide (Hit (fun _ ↦ roots) program input g))

/-- The chain's first state at the test statement. -/
def s₀ : Digest := (FsState.seed program input).cv

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
/- A verifier's fresh query answered by a root of the proof, and the same query asked first by
the prover. -/
#guard scanAgrees [d 9] [⟨[1], d 1⟩] [⟨[2], d 9⟩] &&
  (scanAt [d 9] 1 [⟨[1], d 1⟩, ⟨[2], d 9⟩]).2
#guard scanAgrees [d 9] [⟨[2], d 9⟩] [⟨[2], d 9⟩] &&
  !(scanAt [d 9] 1 [⟨[2], d 9⟩, ⟨[2], d 9⟩]).2
/- An answer equal to the chain's first state. -/
#guard scanAgrees [] [⟨[3], s₀⟩] [] && (scanAt [] 1 [⟨[3], s₀⟩]).2
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

/- A proof with no announcement: `verify` rejects it, and nothing is extracted. -/
#guard !verify program input ⟨[], []⟩
example (hsafe : SentinelSafe program) :
    extractTrace (leanIsaTraceExtraction hsafe) input ⟨[], []⟩ [] = none := rfl

/-! ## The theorems, at the test statement -/

example (A : Adversary) {Q : ℕ} (hQ : IsTotalQueryBound A Q) (hcore : CoreHolds program input A) :
    Pr{let z ← runRandom (loggedGame verifyWith program input A)}[
      z.1.ok = true ∧ ¬ ∃ e,
        extract Blake2sFlock.blake2sFlockSpec program input z.1.proof z.1.logA = some e ∧
          SatisfiedBy program input (witnessOf Blake2sFlock.blake2sFlockSpec program e.1 e.2)] ≤
      ((Q + 13697 : ℕ) / 2 ^ 128 + hashTerm 13697 Q : NNReal) :=
  baseVerifier_extractsWitness_rom hQ hcore

/- The execution form at the test vector's program, whose sentinel slot is not a `JUMP`. -/
example (A : Adversary) {δ : ℝ≥0∞} (hB : BlakeMisbehaves fillProg mulInput A δ)
    (hcore : CoreHolds fillProg mulInput A) :
    Pr{let g ← runBlake2s (loggedGame verifyWith fillProg mulInput A)}[
      verify fillProg mulInput g.proof = true ∧ ¬ ∃ t,
        extractTrace (leanIsaTraceExtraction fill_sentinelSafe) mulInput g.proof g.logA =
          some t ∧ ValidExecution fillProg mulInput t] ≤ δ :=
  baseVerifier_extractsExecution fill_sentinelSafe hB hcore

end LeanerVMTests.Protocol.Headline
