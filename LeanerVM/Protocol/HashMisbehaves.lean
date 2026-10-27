/-
  LeanerVM.Protocol.HashMisbehaves

  The probability that the hash misbehaves in the random-oracle game: a collision, a hit or a flip
  on the joint log of a cheating prover making `Q` queries and of the verifier making `V`, at most
  `(Q + V)·ε + (Q + V)(4(Q + V) + 8)/2^256`, for a statement fixed before the prover runs and any
  reader of chain histories whose bad challenges have density at most `ε`.
-/

module

public import LeanerVM.Protocol.RandomOracleBound

/-!
# The hash misbehaves with small probability

`misbehaves_rom_of` bounds, in any game in two runs (`twoRunGame`: a prover's logged run, then a
verifier's logged run on the prover's output), the probability of
`HashMisbehavesFrom seedRoots rootsOf R.Flip`, from at most one root `seedRoots` in play at the
start and a reader `R` whose starts are safe with them (`SlotReader.StartsSafe`).
`misbehaves_rom` is its instance on the random-oracle game `loggedGame V prog input A`
(`loggedGame_eq_twoRunGame`), from the chain's first state and a reader of the chains from it
alone: the probability of `HashMisbehaves rootsOf R.Flip prog input`, a collision on the joint
log, a hit on the digests in play (the chain's first state, the halves of the queries, the roots
the chain absorbs) or on the proof's roots for the verifier's queries, or a flip of the reader
`R`. The prover `A` makes at most `Q` queries, the verifier at most `V` on every proof, a proof
has at most `proofDigests` roots, and the bad challenges of `R` have density at most `ε`
(`SlotReader.Density`). The bound is `niError ε V Q`, and `niError εquery V Q` at leanVM's
`2^-128`.

The bound is selective: the statement `(prog, input)` is fixed before the prover runs. It does not
cover a prover that picks the statement after its queries. The chain's first state
`FsState.seed prog input` is computed by BLAKE2s outside the oracle, so for such a prover every
statement's first state would be in play from the start, and a hit on one of them would not be
unlikely; an oracle answer is in play only once its query is asked. A prover with coins is a
distribution over coin-free ones, each meeting the bound (`misbehaves_rom_coins`).

The proof runs the game on the lazy random oracle that records its fresh queries
(`QueryHistory.freshLog`). On every run the fresh log is the joint log with each query at its first
occurrence (so a run under the lazy random oracle is a possible run of the game whose joint log is
consistent, `mem_support_runRandom_twoRunGame`), and a misbehaving hash on the joint log leaves
the fresh log unclean (`badLog_of_hashMisbehavesFrom`): a collision, a hit and a flip survive
deduplication, and the proof's roots are answers past the prover's part. The potential of
`RandomOracleBound.lean` then bounds the two runs in sequence
(`QueryHistory.prEvent_bind_le_of_potential`, the integral form): the verifier's run starts from
the potential the prover's leaves, which `Φ_start` identifies with the prover's potential, and
each run's charges total at most its queries times the per-query bound of `charge_le`.

The reader is a parameter: the bound means what the extraction needs at the one reader of the
deployed protocol, which must also supply the density bound and the verifier's query bound.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics Blake2sHash OracleComp OracleSpec MeasureTheory
open scoped NNReal ENNReal

@[expose] public section

/-! ## The error -/

/-- The error of one challenge, `2^-128`. -/
noncomputable def εquery : ℝ≥0 := (2 ^ 128)⁻¹

/-- The chance of a collision or a hit within `Q + V` fresh queries. -/
noncomputable def hashTerm (V Q : ℕ) : ℝ≥0 := (Q + V) * (4 * (Q + V) + 8) / 2 ^ 256

/-- **The error of the random-oracle bound**: `ε` for each of the `Q + V` queries, and the chance
of a collision or a hit. -/
noncomputable def niError (ε : ℝ≥0) (V Q : ℕ) : ℝ≥0 := (Q + V) * ε + hashTerm V Q

/-- The error at `εquery` in closed form. -/
theorem niError_le (V Q : ℕ) : niError εquery V Q ≤ (Q + V) / 2 ^ 128 + hashTerm V Q := by
  simp [niError, εquery, div_eq_mul_inv]

/-- The error grows with the verifier's queries. -/
theorem niError_mono_left (ε : ℝ≥0) {V V' : ℕ} (h : V ≤ V') (Q : ℕ) :
    niError ε V Q ≤ niError ε V' Q := by
  have hV : (V : ℝ≥0) ≤ V' := by exact_mod_cast h
  unfold niError hashTerm
  gcongr

/-! ## The game in two runs -/

/-- **A game in two runs**: a prover's run with its queries logged, then a verifier's run on the
prover's output with its own queries logged; the output, and the run with the proof `proofOf`
reads off the output. -/
def twoRunGame {β : Type} (proofOf : β → Proof PrunedMerklePaths) (A : OracleComp hashSpec β)
    (V : β → OracleComp hashSpec Bool) : OracleComp hashSpec (β × Run) := do
  let p ← A.withQueryLog
  let q ← (V p.1).withQueryLog
  return (p.1, ⟨proofOf p.1, p.2, q.2, q.1⟩)

/-- The game on a statement is the game in two runs of the prover and the verifier on it. -/
theorem loggedGame_eq_twoRunGame (V : VerifierWith) (prog : Program) (input : PublicInput)
    (A : Adversary) :
    loggedGame V prog input A = Prod.snd <$> twoRunGame id A (V hashQuery prog input) := by
  simp only [twoRunGame, map_bind, map_pure]
  rfl

/-- A computation's output map is the map of its run under the lazy random oracle. -/
theorem runRandom_map {α γ : Type} (f : α → γ) (oa : OracleComp hashSpec α) :
    runRandom (f <$> oa) = Prod.map f id <$> runRandom oa := by
  simp only [runRandom, simulateQ_map, StateT.run_map]
  rfl

/-- The verifier's part of the game in two runs: its run on the prover's output, logged, with the
prover's log passed on. -/
private def verifierPart {β : Type} (proofOf : β → Proof PrunedMerklePaths)
    (V : β → OracleComp hashSpec Bool) (p : β × hashSpec.QueryLog) :
    OracleComp hashSpec (β × Run) :=
  (V p.1).withQueryLog >>= fun q ↦ pure (p.1, ⟨proofOf p.1, p.2, q.2, q.1⟩)

/-- The game is the prover's logged run, then the verifier's part. -/
private theorem twoRunGame_eq {β : Type} (proofOf : β → Proof PrunedMerklePaths)
    (A : OracleComp hashSpec β) (V : β → OracleComp hashSpec Bool) :
    twoRunGame proofOf A V = A.withQueryLog >>= verifierPart proofOf V := rfl

/-- **The fresh log of the game.** On every run of the game on the lazy random oracle that records
its fresh queries, the run keeps the prover's output, its proof and log, the joint log is
consistent, and the fresh log after each part is its log with each query at its first
occurrence. -/
private theorem twoRunGame_support {β : Type} {proofOf : β → Proof PrunedMerklePaths}
    {V : β → OracleComp hashSpec Bool} {A : OracleComp hashSpec β}
    {z₁ : (β × hashSpec.QueryLog) × OracleState}
    (hz₁ : z₁ ∈ support ((simulateQ QueryHistory.freshLog.randomOracle A.withQueryLog).run
      ((∅ : hashSpec.QueryCache), [])))
    {z₂ : (β × Run) × OracleState}
    (hz₂ : z₂ ∈ support ((simulateQ QueryHistory.freshLog.randomOracle
      (verifierPart proofOf V z₁.1)).run z₁.2)) :
    z₂.1.1 = z₁.1.1 ∧ z₂.1.2.proof = proofOf z₁.1.1 ∧ z₂.1.2.logA = z₁.1.2 ∧
      QueryLog.Consistent z₂.1.2.log ∧ z₁.2.2 = List.dedupKeys z₂.1.2.logA ∧
      z₂.2.2 = List.dedupKeys z₂.1.2.log := by
  obtain ⟨h₁, hf₁, -, hc₁⟩ :=
    QueryHistory.withQueryLog_freshLog_support _ QueryHistory.isFreshLog_empty hz₁
  simp only [QueryCache.empty_apply, Option.isNone_none, List.filter_true, List.nil_append]
    at h₁
  simp only [verifierPart, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz₂
  obtain ⟨⟨q, s₂⟩, hq, rfl⟩ := hz₂
  obtain ⟨h₂, -, hle, hc₂⟩ := QueryHistory.withQueryLog_freshLog_support _ hf₁ hq
  have hcached : ∀ e ∈ z₁.1.2 ++ q.2, s₂.1 e.1 = some e.2 := fun e he ↦ by
    rcases List.mem_append.mp he with he | he
    · exact hle (hc₁ e he)
    · exact hc₂ e he
  refine ⟨rfl, rfl, rfl, fun e₁ he₁ e₂ he₂ h ↦ ?_, h₁, ?_⟩
  · have h₁' := hcached e₁ he₁
    have h₂' := hcached e₂ he₂
    rw [h] at h₁'
    exact Option.some.inj (h₁'.symm.trans h₂')
  · simp only [Run.log]
    rw [h₂, h₁, QueryLog.dedupKeys_append]
    congr 1
    refine List.filter_congr fun e _ ↦ ?_
    have hkey : (z₁.2.1 e.1).isNone = true ↔ e.1 ∉ z₁.1.2.map (·.1) := by
      rw [Option.isNone_iff_eq_none, ← QueryLog.mem_keys_dedupKeys, ← h₁]
      constructor
      · rintro hn hm
        obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hm
        have := hf₁.1 x hx
        obtain ⟨t', u'⟩ := x
        simp only at hxe this
        subst hxe
        rw [hn] at this
        cases this
      · intro hm
        by_contra hs
        obtain ⟨u', hu'⟩ := Option.ne_none_iff_exists'.mp hs
        exact hm (List.mem_map.mpr ⟨⟨e.1, u'⟩, hf₁.2.1 _ _ hu', rfl⟩)
    exact Bool.eq_iff_iff.mpr (hkey.trans (by simp))

/-- **A run of the game in two runs under the lazy random oracle** is a possible run of the game,
and its joint log is consistent: every logged answer is the final cache's. -/
theorem mem_support_runRandom_twoRunGame {β : Type} {proofOf : β → Proof PrunedMerklePaths}
    {A : OracleComp hashSpec β} {V : β → OracleComp hashSpec Bool}
    {z : (β × Run) × hashSpec.QueryCache} (hz : z ∈ support (runRandom (twoRunGame proofOf A V))) :
    z.1 ∈ support (twoRunGame proofOf A V) ∧ QueryLog.Consistent z.1.2.log := by
  have hrun : runRandom (twoRunGame proofOf A V) = Prod.map id QueryHistory.freshLog.view <$>
      (simulateQ QueryHistory.freshLog.randomOracle (twoRunGame proofOf A V)).run
        ((∅ : hashSpec.QueryCache), []) :=
    ((QueryHistory.freshLog (spec := hashSpec)).randomOracle_run_view
      (twoRunGame proofOf A V) ((∅ : hashSpec.QueryCache), [])).symm
  rw [hrun, support_map] at hz
  obtain ⟨z', hz', rfl⟩ := hz
  refine ⟨support_simulateQ_run'_subset QueryHistory.freshLog.randomOracle _
    ((∅ : hashSpec.QueryCache), []) ?_, ?_⟩
  · rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem _ hz'
  rw [twoRunGame_eq] at hz'
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz'
  obtain ⟨z₁, hz₁, hz₂⟩ := hz'
  exact (twoRunGame_support hz₁ hz₂).2.2.2.1

/-- **A run under the lazy random oracle** is a possible run of the game, and its joint log is
consistent: every logged answer is the final cache's. -/
theorem mem_support_runRandom {V : VerifierWith} {prog : Program} {input : PublicInput}
    {A : Adversary} {z : Run × hashSpec.QueryCache}
    (hz : z ∈ support (runRandom (loggedGame V prog input A))) :
    z.1 ∈ support (loggedGame V prog input A) ∧ QueryLog.Consistent z.1.log := by
  rw [loggedGame_eq_twoRunGame, runRandom_map, support_map] at hz
  obtain ⟨z', hz', rfl⟩ := hz
  obtain ⟨h₁, h₂⟩ := mem_support_runRandom_twoRunGame hz'
  refine ⟨?_, h₂⟩
  rw [loggedGame_eq_twoRunGame, support_map]
  exact ⟨z'.1, h₁, rfl⟩

/-! ## A misbehaving hash leaves the fresh log unclean -/

/-- **A misbehaving hash leaves the fresh log unclean.** On a run whose joint log is consistent, a
collision, a hit from `seedRoots` or a flip of `R` on the joint log is one on the log with each
query at its first occurrence, and a verifier's query answered by a proof root is past the
prover's part. -/
theorem badLog_of_hashMisbehavesFrom (R : SlotReader) {seedRoots : List Digest}
    {rootsOf : Proof PrunedMerklePaths → List Digest} {g : Run}
    (hcons : QueryLog.Consistent g.log) (h : HashMisbehavesFrom seedRoots rootsOf R.Flip g) :
    ¬ R.Clean seedRoots (rootsOf g.proof) (List.dedupKeys g.logA).length
      (List.dedupKeys g.log) := by
  rintro ⟨hcl, -, hf, hr⟩
  rcases h with hc | (hhit | ⟨k, hk, hfr, hroot⟩) | hflip
  · exact hcl.noCollision (QueryLog.hasCollision_dedupKeys hcons hc)
  · exact hcl.noHit (QueryLog.hasHit_dedupKeys (fun i d hd ↦
      (inPlay_dedupKeys _ (hcons.of_prefix (List.take_prefix _ _)) d).mpr hd) hhit)
  · have hmem := QueryLog.mem_drop_dedupKeys (k₀ := g.logA.length) hk k.2 (by simpa using hfr)
    have htake : g.log.take g.logA.length = g.logA := List.take_left' rfl
    rw [htake] at hmem
    exact hr _ hmem (by simpa using hroot)
  · exact hf (R.flipAt_dedupKeys hcons hflip)

/-- **A misbehaving hash leaves the fresh log unclean**, on a run of the statement
`(prog, input)`. -/
theorem badLog_of_hashMisbehaves (R : SlotReader) {rootsOf : Proof PrunedMerklePaths → List Digest}
    {prog : Program} {input : PublicInput} {g : Run} (hcons : QueryLog.Consistent g.log)
    (h : HashMisbehaves rootsOf R.Flip prog input g) :
    ¬ R.Clean (seedDigests prog input) (rootsOf g.proof) (List.dedupKeys g.logA).length
      (List.dedupKeys g.log) :=
  badLog_of_hashMisbehavesFrom R hcons h

/-! ## The bound -/

/-- The two runs' budgets add up to the error. -/
private theorem budget_le (ε : ℝ≥0) (V Q : ℕ) :
    (Q : ℝ≥0∞) * (((4 * Q + 1 + 0 : ℕ) : ℝ≥0∞) / 2 ^ 256 + ε) +
      (V : ℝ≥0∞) * (((4 * (Q + V) + 1 + proofDigests : ℕ) : ℝ≥0∞) / 2 ^ 256 + ε) ≤
      niError ε V Q := by
  have key : Q * (4 * Q + 1 + 0) + V * (4 * (Q + V) + 1 + proofDigests) ≤
      (Q + V) * (4 * (Q + V) + 8) := by
    rw [Nat.add_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ (by omega))
      (Nat.mul_le_mul_left _ (by simp only [proofDigests]; omega))
  have hcoe : ((niError ε V Q : ℝ≥0) : ℝ≥0∞) = (Q + V : ℝ≥0∞) * ε +
      (((Q + V) * (4 * (Q + V) + 8) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    simp only [niError, hashTerm, ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_natCast]
    rw [ENNReal.coe_div (by positivity)]
    push_cast
    ring
  rw [hcoe]
  calc (Q : ℝ≥0∞) * (((4 * Q + 1 + 0 : ℕ) : ℝ≥0∞) / 2 ^ 256 + ε) +
        (V : ℝ≥0∞) * (((4 * (Q + V) + 1 + proofDigests : ℕ) : ℝ≥0∞) / 2 ^ 256 + ε)
      = (Q + V : ℝ≥0∞) * ε + ((Q * (4 * Q + 1 + 0) +
          V * (4 * (Q + V) + 1 + proofDigests) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
        push_cast
        simp only [div_eq_mul_inv, add_zero]
        ring
    _ ≤ _ := add_le_add le_rfl (ENNReal.div_le_div_right (Nat.cast_le.mpr key) _)

/-- **The hash misbehaves with probability at most `niError ε Vq Q`** in a game in two runs:
from roots `seedRoots` in play at the start, at most one; a reader `R` whose starts are safe with
them and whose bad challenges have density at most `ε`; a prover making at most `Q` queries; a
verifier making at most `Vq` on every output of the prover; and at most `proofDigests` roots of
the proof per output. -/
theorem misbehaves_rom_of (R : SlotReader) {seedRoots : List Digest}
    (hlen : seedRoots.length ≤ 1) (hsafe : R.StartsSafe seedRoots) {ε : ℝ≥0} (hbad : R.Density ε)
    {β : Type} (proofOf : β → Proof PrunedMerklePaths) (A : OracleComp hashSpec β) {Q : ℕ}
    (hQ : IsTotalQueryBound A Q) (V : β → OracleComp hashSpec Bool) {Vq : ℕ}
    (hV : ∀ b, IsTotalQueryBound (V b) Vq)
    (rootsOf : β → Proof PrunedMerklePaths → List Digest)
    (hroots : ∀ b proof, (rootsOf b proof).length ≤ proofDigests) :
    Pr{let z ← runRandom (twoRunGame proofOf A V)}[
      HashMisbehavesFrom seedRoots (rootsOf z.1.1) R.Flip z.1.2] ≤ niError ε Vq Q := by
  classical
  have hrun : runRandom (twoRunGame proofOf A V) = Prod.map id QueryHistory.freshLog.view <$>
      (simulateQ QueryHistory.freshLog.randomOracle (twoRunGame proofOf A V)).run
        ((∅ : hashSpec.QueryCache), []) := by
    unfold runRandom
    exact ((QueryHistory.freshLog (spec := hashSpec)).randomOracle_run_view
      (twoRunGame proofOf A V) ((∅ : hashSpec.QueryCache), [])).symm
  rw [hrun, prEvent_map, twoRunGame_eq]
  have hA : IsTotalQueryBound A.withQueryLog Q := (isTotalQueryBound_withQueryLog_iff A Q).mpr hQ
  have hB : ∀ p, IsTotalQueryBound (verifierPart proofOf V p) Vq := fun p ↦ by
    have := isTotalQueryBound_bind (n₂ := 0)
      (ob := fun q : Bool × hashSpec.QueryLog ↦
        (pure (p.1, ⟨proofOf p.1, p.2, q.2, q.1⟩) : OracleComp hashSpec (β × Run)))
      ((isTotalQueryBound_withQueryLog_iff _ Vq).mpr (hV p.1)) (fun _ ↦ trivial)
    simpa [verifierPart] using this
  refine ((QueryHistory.freshLog (spec := hashSpec)).prEvent_bind_le_of_potential A.withQueryLog
    (verifierPart proofOf V) ((∅ : hashSpec.QueryCache), [])
    (fun z ↦ HashMisbehavesFrom seedRoots (rootsOf (Prod.map id QueryHistory.freshLog.view z).1.1)
      R.Flip (Prod.map id QueryHistory.freshLog.view z).1.2)
    (fun _ ↦ False)
    (fun z₁ z₂ ↦ ¬ (QueryHistory.IsFreshLog z₂.2 ∧
      R.Clean seedRoots (rootsOf z₁.1.1 (proofOf z₁.1.1)) z₁.2.2.length z₂.2.2))
    (fun z₁ hz₁ z₂ hz₂ hE ↦ .inr fun hgood ↦ ?_) (R.Φ seedRoots [] 0) (R.charge seedRoots [] 0)
    (fun s t ht ↦ R.potential_step s t ht) (fun _ h ↦ h.elim)
    (ε := Vq * (((4 * (Q + Vq) + 1 + proofDigests : ℕ) : ℝ≥0∞) / 2 ^ 256 + ε))
    (fun z₁ hz₁ _ ↦ ?_)).trans ?_
  · -- a misbehaving hash leaves the verifier's fresh log unclean
    obtain ⟨hb, hp, -, hcons, h₁, h₂⟩ := twoRunGame_support hz₁ hz₂
    refine badLog_of_hashMisbehavesFrom R hcons hE ?_
    simp only [Prod.map_fst, id_eq]
    rw [← h₂, hp, hb, ← h₁]
    exact hgood.2
  · -- the verifier's run, from the potential the prover's leaves
    have henn : z₁.2.1.enncard ≤ Q := by
      simpa using (QueryHistory.freshLog (spec := hashSpec)).enncard_le_of_mem_support hA _ hz₁
    refine ((QueryHistory.freshLog (spec := hashSpec)).prEvent_le_of_potential
      (fun z₂ ↦ ¬ (QueryHistory.IsFreshLog z₂.2 ∧
        R.Clean seedRoots (rootsOf z₁.1.1 (proofOf z₁.1.1)) z₁.2.2.length z₂.2.2))
      (R.Φ seedRoots (rootsOf z₁.1.1 (proofOf z₁.1.1)) z₁.2.2.length) (fun z h ↦ R.one_le_Φ h)
      (R.charge seedRoots (rootsOf z₁.1.1 (proofOf z₁.1.1)) z₁.2.2.length)
      (fun s t ht ↦ R.potential_step s t ht) (verifierPart proofOf V z₁.1) z₁.2).trans ?_
    rw [R.Φ_start]
    refine add_le_add le_rfl ((QueryHistory.freshLog (spec := hashSpec)).expected_charge_le_mul
      (hB z₁.1) z₁.2 fun s' t _ hs' ↦ ?_)
    refine (R.charge_le hsafe hbad (L := Q + Vq) ?_ t).trans (add_le_add
      (ENNReal.div_le_div_right (Nat.cast_le.mpr (by
        have := hroots z₁.1.1 (proofOf z₁.1.1)
        omega)) _) le_rfl)
    calc s'.1.enncard + 1 ≤ z₁.2.1.enncard + Vq := hs'
      _ ≤ Q + Vq := add_le_add henn le_rfl
      _ = ((Q + Vq : ℕ) : ℝ≥0∞) := by push_cast; rfl
  · -- the prover's run, from the empty state
    rw [R.Φ_empty, zero_add]
    refine le_trans (add_le_add ((QueryHistory.freshLog (spec := hashSpec)).expected_charge_le_mul
      hA _ fun s' t _ hs' ↦ (R.charge_le hsafe hbad (L := Q) ?_ t).trans (by
        refine add_le_add (ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _) le_rfl
        simp only [List.length_nil]
        omega)) le_rfl) (budget_le ε Vq Q)
    simpa using hs'

/-- **The hash misbehaves with probability at most `niError ε V Q`** in the random-oracle game,
for a statement `(prog, input)` fixed before the prover runs (selective: the chain's first state is
computed outside the oracle, so a prover picking the statement after its queries is not covered); a
reader `R` of the chains from that first state alone whose bad challenges have density at most
`ε`; a prover making at most `Q` queries; a verifier making at most `V` on every proof; and at most
`proofDigests` roots per proof. -/
theorem misbehaves_rom (R : SlotReader) (prog : Program) (input : PublicInput)
    (hseed : R.toChainStarts = ChainStarts.startAt (FsState.seed prog input).cv) {ε : ℝ≥0}
    (hbad : R.Density ε)
    (V : VerifierWith) {Vq : ℕ} (hV : ∀ proof, IsTotalQueryBound (V hashQuery prog input proof) Vq)
    (rootsOf : Proof PrunedMerklePaths → List Digest)
    (hroots : ∀ proof, (rootsOf proof).length ≤ proofDigests)
    (A : Adversary) {Q : ℕ} (hQ : IsTotalQueryBound A Q) :
    Pr{let z ← runRandom (loggedGame V prog input A)}[
      HashMisbehaves rootsOf R.Flip prog input z.1] ≤ niError ε Vq Q := by
  rw [loggedGame_eq_twoRunGame, runRandom_map, prEvent_map]
  exact misbehaves_rom_of R (seedRoots := seedDigests prog input) le_rfl
    (R.startsSafe_of_seed _ hseed (List.mem_singleton_self _)) hbad id A hQ
    (V hashQuery prog input) hV (fun _ ↦ rootsOf) fun _ ↦ hroots

/-- **The bound for a prover with coins**: a distribution over provers each making at most `Q`
queries is a mixture of coin-free ones, each meeting the bound. -/
theorem misbehaves_rom_coins (R : SlotReader) (prog : Program) (input : PublicInput)
    (hseed : R.toChainStarts = ChainStarts.startAt (FsState.seed prog input).cv) {ε : ℝ≥0}
    (hbad : R.Density ε)
    (V : VerifierWith) {Vq : ℕ} (hV : ∀ proof, IsTotalQueryBound (V hashQuery prog input proof) Vq)
    (rootsOf : Proof PrunedMerklePaths → List Digest)
    (hroots : ∀ proof, (rootsOf proof).length ≤ proofDigests)
    (coins : ProbComp Adversary) {Q : ℕ} (hQ : ∀ A ∈ support coins, IsTotalQueryBound A Q) :
    Pr{let A ← coins; let z ← runRandom (loggedGame V prog input A)}[
      HashMisbehaves rootsOf R.Flip prog input z.1] ≤ niError ε Vq Q := by
  rw [← bind_assoc]
  exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun A hA ↦
    misbehaves_rom R prog input hseed hbad V hV rootsOf hroots A (hQ A hA)

end
end LeanerVM.Protocol
