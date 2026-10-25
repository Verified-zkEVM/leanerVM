import LeanerVM.Protocol.Headline
import LeanerVMTests.Protocol.RandomOracleGame
import LeanerVMTests.Arithmetization.Steps

/-!
# The headline theorems: tests

* **The replayer.** The adversary `pure proof` outputs a stored proof and asks nothing. If `verify`
  accepts the proof and the extraction from the empty log fails, its one run under BLAKE2s
  misbehaves (the verifier's recomputed root is a fresh answer equal to a root of the proof, a
  hit), so it fails `BlakeMisbehaves` at every `δ < 1` (`replayer_not_blakeMisbehaves`). The
  extraction from the empty log reads every row as zero and fails only when the zero stack does
  not satisfy the relation, so that failure is a premise. The `leanervm-verify` executable checks
  both premises natively on the Rust proof and on the test vector, the second through
  `extractCheap`, which is `extract` (`extractCheap_eq`) with the relation's clauses decided
  cheapest first: as `extract` decides it, the bus's permutation comes second, and its decision is
  quadratic in the bus's length.
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

/-- **The replayer fails the hypothesis** at every `δ < 1`, when `verify` accepts its proof and
the extraction from the empty log fails. -/
theorem replayer_not_blakeMisbehaves {prog : Program} {input : PublicInput}
    {proof : Proof PrunedMerklePaths} {δ : ℝ≥0∞} (hacc : verify prog input proof = true)
    (hX : ¬ Extracts Blake2sFlock.blake2sFlockSpec prog input proof []) (hδ : δ < 1)
    (hcore : CoreHolds prog input (replayer proof)) :
    ¬ BlakeMisbehaves prog input (replayer proof) δ := by
  intro hB
  have h1 : Pr{let g ← runBlake2s (loggedGame verifyWith prog input (replayer proof))}[
      HashMisbehaves (rootsOf prog input) (leanVmReader prog input).Flip prog input g] = 1 :=
    OracleComp.prEvent_eq_one_of_forall_mem_support _ _ fun g hg ↦ by
      obtain ⟨hg', hc, hok⟩ := mem_support_runBlake2s hg
      obtain ⟨hp, hl⟩ := replayer_run hg'
      exact hcore g hg' hc (hok.trans (hp ▸ hacc)) (hp ▸ hl ▸ hX)
  unfold BlakeMisbehaves at hB
  rw [h1] at hB
  exact absurd hδ (not_lt.mpr hB)

/-! ## The extraction, its clauses decided cheapest first -/

/-- `M3Holds` decided with its cheap clauses first: the count cells, the public cells, the
constraints and the Flock predicate, then the bus's permutation, whose decision is quadratic in
its length. -/
def holdsCheap (I : M3Instance) (input : I.Stmt) (q : Column I.μ) : Bool :=
  decide (I.CountsNonzero q) && decide (I.PublicLinesHold input q) &&
    decide (I.ConstraintsVanish q) && decide (I.aux q) && decide (I.Balanced q)

theorem holdsCheap_eq (I : M3Instance) (input : I.Stmt) (q : Column I.μ) :
    holdsCheap I input q = decide (M3Holds I input q) := by
  rw [Bool.eq_iff_iff]
  simp only [holdsCheap, Bool.and_eq_true, decide_eq_true_eq, M3Holds]
  refine ⟨fun ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩ ↦ decide_eq_true ⟨c, e, a, b, d⟩, fun h ↦ ?_⟩
  obtain ⟨c, e, a, b, d⟩ := of_decide_eq_true h
  exact ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩

/-- `deployedPick` with `holdsCheap`. -/
def pickCheap (I : M3Instance) {r : ℕ} (h : Whir.Admissible I.μ r) (s : I.Stmt)
    (w : Whir.KWord (Whir.deployedHeadShape I.μ r).ℓ
      (Whir.deployedHeadKap I.μ r + (Whir.deployedHeadShape I.μ r).R)
      (Whir.deployedHeadShape I.μ r).t) : Option (Column I.μ) :=
  ((stackList I (Whir.deployedHeadDecoder h) (Whir.deployedHead_height h) fun _ ↦ w).find?
    fun q ↦ holdsCheap I s (q 0)).map (· 0)

/-- `extract` with `holdsCheap`: the same function, which a native run can afford on a stack that
fails a cheap clause. -/
def extractCheap (F : FlockSpec) (prog : Program) (input : PublicInput)
    (proof : Proof PrunedMerklePaths) (log : hashSpec.QueryLog) :
    Option (Σ s : Sizes, Column (leanIsaμ prog s)) :=
  match proof.announced? with
  | none => none
  | some (s, ρ) =>
    if hs : s.Admissible prog ∧ validRate ρ then
      match level0Root proof with
      | none => none
      | some root =>
        let v := wordRows log root
          (Whir.deployedHeadKap (leanIsaμ prog s) ρ + (Whir.deployedHeadShape (leanIsaμ prog s) ρ).R)
          (level0Lanes prog s (Whir.deployedHeadKap (leanIsaμ prog s) ρ))
          (Whir.deployedHeadShape (leanIsaμ prog s) ρ).ℓ
        (pickCheap (leanIsaInstance F prog s) (admissible_of_sizes hs.1 hs.2) input
          ⟨fun y ↦ v[y]⟩).map fun q ↦ ⟨s, q⟩
    else none

theorem pickCheap_eq (I : M3Instance) {r : ℕ} (h : Whir.Admissible I.μ r) (s : I.Stmt)
    (w : Whir.KWord (Whir.deployedHeadShape I.μ r).ℓ
      (Whir.deployedHeadKap I.μ r + (Whir.deployedHeadShape I.μ r).R)
      (Whir.deployedHeadShape I.μ r).t) :
    pickCheap I h s w = Whir.deployedPick I h s w := by
  simp only [pickCheap, Whir.deployedPick, commitPick, holdsCheap_eq]

theorem extractCheap_eq (F : FlockSpec) (prog : Program) (input : PublicInput)
    (proof : Proof PrunedMerklePaths) (log : hashSpec.QueryLog) :
    extractCheap F prog input proof log = extract F prog input proof log := by
  unfold extractCheap extract
  rcases proof.announced? with _ | ⟨s, ρ⟩
  · rfl
  · dsimp only
    split_ifs with hs
    · rcases level0Root proof with _ | root
      · rfl
      · dsimp only
        rw [pickCheap_eq]
    · rfl

/-! ## Collisions and hits, in one pass -/

/-- **The collisions and hits of a joint log**, in one pass with hash maps. The first `nA` entries
are the prover's; `seed` lists the digests in play from the start, `roots` the proof's roots. An
entry is a collision when its digest answered an earlier, different input; a hit when its input is
new and its digest is in play (the seed, a half of an earlier input, a root rebuilt from two
earlier observe steps) or, past the prover's entries, a root of the proof. Then its halves and the
roots its observe step completes are put in play. -/
def scan (seed roots : List Digest) (nA : ℕ) (log : hashSpec.QueryLog) : Bool × Bool := Id.run do
  let key (x : Digest) : List UInt32 := x.toList
  let rootSet : Std.HashSet (List UInt32) := Std.HashSet.ofList (roots.map key)
  let mut answers : Std.HashMap (List UInt32) (List UInt8) := {}
  let mut seen : Std.HashSet (List UInt8) := {}
  let mut play : Std.HashSet (List UInt32) := Std.HashSet.ofList (seed.map key)
  let mut firstObs : Std.HashMap (List UInt32) E := {}
  let mut pending : Std.HashMap (List UInt32) (Array E) := {}
  let mut collision := false
  let mut hit := false
  let mut k := 0
  for e in log do
    let a := key e.2
    match answers[a]? with
    | some t => if t != e.1 then collision := true
    | none => answers := answers.insert a e.1
    if !seen.contains e.1 && (play.contains a || (nA ≤ k && rootSet.contains a)) then hit := true
    seen := seen.insert e.1
    for h in halves e.1 do
      play := play.insert (key h)
    if let some (cv, x) := observed? e.1 then
      match firstObs[key cv]? with
      | some x₁ =>
        if let some r := digestOfScalars (x₁, x) then play := play.insert (key r)
      | none => pending := pending.insert (key cv) ((pending.getD (key cv) #[]).push x)
      if !firstObs.contains a then
        firstObs := firstObs.insert a x
        for x' in pending.getD a #[] do
          if let some r := digestOfScalars (x, x') then play := play.insert (key r)
        pending := pending.erase a
    k := k + 1
  return (collision, hit)

/-- `scan` agrees with the definitions on a run of the given logs, at the test statement. -/
def scanAgrees (roots : List Digest) (logA logV : hashSpec.QueryLog) : Bool :=
  let g : Run := ⟨⟨[], []⟩, logA, logV, true⟩
  scan (seedDigests program input) roots logA.length g.log ==
    (decide (QueryLog.HasCollision g.log), decide (Hit (fun _ ↦ roots) program input g))

/-- The chain's first state at the test statement. -/
def s₀ : Digest := (FsState.seed program input).cv

/-- A root the chain absorbs as two observe steps, answered by `d 1` and `d 2`. -/
def absorbed : hashSpec.QueryLog :=
  [⟨Block.input s₀ (.observe (digestScalars (d 9)).1), d 1⟩,
    ⟨Block.input (d 1) (.observe (digestScalars (d 9)).2), d 2⟩]

/- A hit through a half: the verifier's query answered by a child of the prover's node. -/
#guard scanAgrees [] nodeA nodeV && (scan (seedDigests program input) [] 1 (nodeA ++ nodeV)).2
/- A collision. -/
#guard scanAgrees [] [⟨[1], d 1⟩] [⟨[2], d 1⟩] &&
  (scan (seedDigests program input) [] 1 [⟨[1], d 1⟩, ⟨[2], d 1⟩]).1
/- The rebuilt root `d 9` is in play after the two observe steps, and not before. -/
#guard scanAgrees [] (absorbed ++ [⟨[5], d 9⟩]) [] &&
  (scan (seedDigests program input) [] 3 (absorbed ++ [⟨[5], d 9⟩])).2
#guard scanAgrees [] (⟨[5], d 9⟩ :: absorbed) [] &&
  !(scan (seedDigests program input) [] 3 (⟨[5], d 9⟩ :: absorbed)).2
/- A verifier's fresh query answered by a root of the proof, and the same query asked first by
the prover. -/
#guard scanAgrees [d 9] [⟨[1], d 1⟩] [⟨[2], d 9⟩] &&
  (scan (seedDigests program input) [d 9] 1 [⟨[1], d 1⟩, ⟨[2], d 9⟩]).2
#guard scanAgrees [d 9] [⟨[2], d 9⟩] [⟨[2], d 9⟩] &&
  !(scan (seedDigests program input) [d 9] 1 [⟨[2], d 9⟩, ⟨[2], d 9⟩]).2
/- An answer equal to the chain's first state. -/
#guard scanAgrees [] [⟨[3], s₀⟩] [] && (scan (seedDigests program input) [] 1 [⟨[3], s₀⟩]).2
/- A clean log. -/
#guard scanAgrees [d 9] [⟨[1], d 1⟩] [⟨[2], d 2⟩] &&
  scan (seedDigests program input) [d 9] 1 [⟨[1], d 1⟩, ⟨[2], d 2⟩] == (false, false)

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
