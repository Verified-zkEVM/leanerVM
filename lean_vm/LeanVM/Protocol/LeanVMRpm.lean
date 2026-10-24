/-
  LeanVM.Protocol.LeanVMRpm

  The proofs of the two statements of `LeanVM/Spec/Rpm.lean`, `LeanVM.KnowledgeSoundness` and
  `LeanVM.Completeness`: knowledge soundness and completeness of the leanVM verifier in the
  random-permutation model, from the two-oracle random-oracle model.
-/

import LeanVM.Protocol.LeanVM
import LeanVM.Protocol.Rpm.Cost
import LeanVM.Protocol.Rpm.Duplex
import LeanVM.Protocol.Rpm.Extract
import LeanVM.Protocol.Rpm.RomRelabel
import LeanVM.Protocol.Rpm.RpmRelabel

/-!
# leanVM in the random-permutation model

The statements are in `LeanVM/Spec/Rpm.lean`: Keccak-256 the sponge over one uniformly random
permutation `π` of the Keccak state, Keccak-f[1600] `π` itself, the adversary querying `π` and
`π⁻¹`.

**Knowledge soundness** (`knowledgeSoundnessRpm`): for an adversary of at most `Q` queries, the
probability that the verifier accepts while the program's last instruction is not a `JUMP` and
the extractor `extractorRpm` (the extractor of `Extractor.lean` on the Keccak-256 evaluations of
the adversary's transcript) does not return a valid execution is at most
`soundnessError Q + (Q + 12008 · 2^32)² / 2^508`, which is at most `(Q + 2^14) · 2^-127` for
`Q ≤ 2^120` (`soundnessRpm_le_bits`, `knowledgeSoundness_bits`) and at most `2^-63` for
`Q ≤ 2^64` (`soundnessRpm_le`). The proof:

1. the experiment is `common`'s real world of a transfer game (`rpmExperiment_evalDistEq`,
   `RpmRelabel.lean`): the adversary, recording its transcript, then the verifier;
2. the verifier's permutation calls follow the duplex discipline (`duplex_postR`, from
   `Duplex.lean`), and the game makes at most `Q + verifierPermCalls` permutation calls
   (`isWeightBound_game`, from `Cost.lean`);
3. `Common.keccak256_transfer2` moves the event to the two-oracle random-oracle model, against
   the adversary with the indifferentiability simulator, at a cost of `q² / 2^508`, which is where
   the random-permutation model meets the random-oracle model;
4. there, the adversary's cached Keccak-256 answers are exactly the evaluations of its transcript
   (`transcriptHashes_eq_of_mem_support`, `Extract.lean`), so the event is the event of
   `KnowledgeSoundnessRom` (`LeanVM/Protocol/Rom/Statement.lean`) against the random-oracle
   adversary `romAdv` (`romGame_le`), which makes at
   most `Q` oracle queries (`isWeightBound_romAdv`) and flips coins;
5. coins do not help (`knowledgeSoundness_coins`, `Coins.lean`), and
   `knowledgeSoundnessRom_holds` bounds the rest by `soundnessError Q`.

**Completeness** (`completenessRpm`): the same game with no adversary and, after it, the honest
prover of `CompletenessRom` followed by the verifier, both following the duplex discipline
(`duplexVm_honest`), of at most `completenessPermCalls fuel` permutation calls
(`isWeightBound_honest`): the rejection probability is at most
`completenessError fuel + completenessPermCalls fuel² / 2^508`, below `2^-127` at a fuel of `2^25`
(`completenessRpm_le`).

Every theorem depends only on `propext`, `Classical.choice` and `Quot.sound` (`LeanVM.lean`).
-/

namespace LeanVM.Rpm

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open scoped ENNReal

/-! ## The duplex discipline on bytes -/

/-- An admissible permutation call on lanes is admissible on bytes. -/
theorem admissible_toRpm {hist : List KState} {x : KState} (h : AdmissibleVm hist x) :
    Common.Admissible Common.KState.zero Common.keccakNF (hist.map KState.toRpm)
      (KState.toRpm x) := by
  rcases h with h | ⟨y, hy, h⟩
  · left
    have hk := keccakNF_of_keep x (Vector.replicate 25 0) fun i hi ↦ by simp [h i hi]
    rw [toRpm_zero] at hk
    exact hk
  · right
    exact ⟨KState.toRpm y, List.mem_map_of_mem hy, keccakNF_of_keep x y h⟩

/-- **The discipline on lanes is the discipline on bytes**: a computation over the calls of
`Statement.lean` (`HashSpec`) whose permutation calls follow the duplex discipline on lanes, read
on bytes, follows `common`'s duplex discipline (`Common.Duplex`, at the zero state, for the
non-final blocks `Common.keccakNF`). -/
theorem duplex_toRHF {β : Type} (V : OracleComp HashSpec β) (hist : List KState)
    (hV : DuplexVm V hist) :
    Common.Duplex Common.KState.zero Common.keccakNF (simulateQ toRHF V)
      (hist.map KState.toRpm) := by
  induction V using OracleComp.inductionOn generalizing hist with
  | pure a => trivial
  | query_bind t k ih =>
    rw [duplexVm_query_bind] at hV
    rcases t with m | x
    · simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self, toRHF,
        bind_map_left]
      intro d
      exact ih _ hist (hV _)
    · simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self, toRHF,
        bind_map_left]
      refine ⟨admissible_toRpm hV.1, fun y ↦ ?_⟩
      have := ih (KState.ofRpm y) (KState.ofRpm y :: hist) (hV.2 _)
      rw [List.map_cons, toRpm_ofRpm] at this
      exact this

/-- A map keeps the duplex discipline. -/
theorem duplex_map {α β : Type} (f : α → β) (X : OracleComp HFSpec α)
    (hist : List Common.KState)
    (hX : Common.Duplex Common.KState.zero Common.keccakNF X hist) :
    Common.Duplex Common.KState.zero Common.keccakNF (f <$> X) hist := by
  induction X using OracleComp.inductionOn generalizing hist with
  | pure a => trivial
  | query_bind t k ih =>
    rw [map_bind]
    rcases t with n | m | x
    · exact fun u ↦ ih u hist (hX u)
    · exact fun u ↦ ih u hist (hX u)
    · exact ⟨hX.1, fun y ↦ ih y (y :: hist) (hX.2 y)⟩

/-- The verifier on bytes follows the duplex discipline. -/
theorem duplex_postR (z : (Statement × Proof) × Transcript) :
    Common.Duplex Common.KState.zero Common.keccakNF (postR z) [] :=
  duplex_map _ _ [] (duplex_toRHF _ [] (duplexVm_verifier _ _ _))

/-! ## The permutation calls of the games -/

/-- Weight bounds through a stateless simulation. -/
theorem isWeightBound_simulateQ' {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {α : Type} (impl : QueryImpl spec (OracleComp spec')) (w : ι → ℕ) (w' : ι' → ℕ)
    (h : ∀ t, Common.IsWeightBound (impl t) w' (w t)) {X : OracleComp spec α} {n : ℕ}
    (hX : Common.IsWeightBound X w n) : Common.IsWeightBound (simulateQ impl X) w' n := by
  induction X using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind t k ih =>
    rw [Common.isWeightBound_query_bind_iff] at hX
    simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self]
    exact ((h t).bind fun u ↦ ih u (hX.2 u)).mono (by omega)

/-- The cost of the game's queries (`Common.queryCost2`): a hash of `n` bytes `⌊n / 136⌋ + 1`,
a permutation query or call one. -/
abbrev gameCost : D2Spec.Domain → ℕ := Common.queryCost2 (Dg := Common.KDigest) Common.keccakPadding

/-- The cost of the adversary's queries (`Common.queryCost`). -/
abbrev advCost : RSpec.Domain → ℕ :=
  Common.queryCost (Dg := Common.KDigest) (St := Common.KState) Common.keccakPadding

/-- The adversary's permutation queries, one each. -/
theorem isWeightBound_advR_cost {A : RpmAdversary} {Q : ℕ} (hA : A.IsTotalQueryBound Q) :
    Common.IsWeightBound (advR A) advCost Q := by
  refine Common.isWeightBound_run_simulateQ logRel (fun _ ↦ 1) _ (fun q T ↦ ?_)
    (isWeightBound_one_of_total hA) []
  simp only [logRel, StateT.run_mk, relP]
  exact Common.isWeightBound_map _ (Common.isWeightBound_map _
    (Common.isWeightBound_query advCost (.inr (.inr (permQueryToRpm q)))))

theorem isWeightBound_advEmbed {α : Type} {X : OracleComp RSpec α} {n : ℕ}
    (hX : Common.IsWeightBound X advCost n) :
    Common.IsWeightBound (simulateQ Common.advEmbed X) gameCost n := by
  refine isWeightBound_simulateQ' _ _ _ (fun t ↦ ?_) hX
  rcases t with k | m | q
  · exact Common.isWeightBound_query (spec := D2Spec) gameCost (.inl k)
  · exact Common.isWeightBound_query (spec := D2Spec) gameCost (.inr (.inl m))
  · exact Common.isWeightBound_query (spec := D2Spec) gameCost (.inr (.inr (.inl q)))

theorem isWeightBound_hfEmbed_toRHF {β : Type} {V : OracleComp HashSpec β} {n : ℕ}
    (hV : Common.IsWeightBound V hashBlocks n) :
    Common.IsWeightBound (simulateQ Common.hfEmbed (simulateQ toRHF V)) gameCost n := by
  rw [← QueryImpl.simulateQ_compose]
  refine isWeightBound_simulateQ' _ _ _ (fun t ↦ ?_) hV
  rcases t with m | x
  · simp only [QueryImpl.apply_compose, toRHF, simulateQ_map]
    refine Common.isWeightBound_map _ ?_
    simp only [Common.hQuery, hq_eq, simulateQ_spec_query]
    have := Common.isWeightBound_query (spec := D2Spec) gameCost (.inr (.inl m))
    rwa [show gameCost (.inr (.inl m)) = hashBlocks (.inl m) from Common.keccakPad_length m]
      at this
  · simp only [QueryImpl.apply_compose, toRHF, simulateQ_map]
    refine Common.isWeightBound_map _ ?_
    simp only [Common.fQuery, hq_eq, simulateQ_spec_query]
    exact Common.isWeightBound_query (spec := D2Spec) gameCost (.inr (.inr (.inr _)))

/-- **The permutation calls of the transfer game**: the adversary's `Q`, then at most
`verifierPermCalls` of the verifier. -/
theorem isWeightBound_game {A : RpmAdversary} {Q : ℕ} (hA : A.IsTotalQueryBound Q) :
    Common.IsWeightBound (game A) gameCost (Q + verifierPermCalls) := by
  rw [game, Common.rpmGame2, simulateQ_pure, pure_bind]
  refine (isWeightBound_advEmbed (isWeightBound_advR_cost hA)).bind fun z ↦ ?_
  rw [postR, simulateQ_map]
  exact Common.isWeightBound_map _ (isWeightBound_hfEmbed_toRHF (isWeightBound_verifier _ _ _))

/-! ## Knowledge soundness -/

/-- The verifier's phase of the random-oracle experiment, from the adversary's statement and proof
and the oracles' cache. -/
noncomputable def verifierPhase (z : Statement × Proof) (cA : HashSpec.QueryCache) :
    ProbComp Outcome :=
  (fun r ↦ ((z, r.1), r.2, cA)) <$>
    (simulateQ HashSpec.randomOracle (verifier queryH queryF z.1.1 z.1.2 z.2)).run cA

theorem experimentCoins_eq (B : OracleComp CSpec (Statement × Proof)) :
    experimentCoins B = (simulateQ HashSpec.romImpl B).run ∅ >>= fun p ↦ verifierPhase p.1 p.2 := by
  simp only [experimentCoins, verifierPhase, bind_pure_comp]

/-- **The random-oracle game of the transfer is bounded by the random-oracle experiment of the
transfer's adversary**: the transcript's Keccak-256 evaluations are the adversary's cached hash
answers (`transcriptHashes_eq_of_mem_support`), so the extractor in the random-permutation model
sees what the extractor of the random-oracle model (`LeanVM.extractor`) sees. -/
theorem romGame_le (A : RpmAdversary) :
    Pr{let a ← Common.romRun2 (simulateQ Common.hInF (pure ()) >>= fun x ↦
        Common.advS2 Common.keccakPadding Common.KState.zero ((fun _ ↦ advR A) x) >>= fun a ↦
          (fun _ z ↦ postR z) x a)}[BreaksRpm extractorRpm a] ≤
      Pr{let z ← experimentCoins (romAdv A)}[Breaks extractor z] := by
  set X := Common.advS2 Common.keccakPadding Common.KState.zero (advR A)
  set J := (simulateQ HFS.romImpl X).run ∅ with hJ
  have e1 : Common.romRun2 (simulateQ Common.hInF (pure ()) >>= fun x ↦
      Common.advS2 Common.keccakPadding Common.KState.zero ((fun _ ↦ advR A) x) >>= fun a ↦
        (fun _ z ↦ postR z) x a) =
      J >>= fun p ↦ (simulateQ HFS.romImpl (postR p.1)).run' p.2 := by
    simp only [Common.romRun2, simulateQ_pure, pure_bind, simulateQ_bind, StateT.run'_eq,
      StateT.run_bind, map_bind, hJ, X]
  rw [e1]
  have e2 : experimentCoins (romAdv A) =ᵈ J >>= fun p ↦ verifierPhase p.1.1 (cmap p.2) := by
    rw [experimentCoins_eq, romAdv, simulateQ_map, StateT.run_map]
    have h := run_ofRHF X ∅
    rw [cmap_empty] at h
    rw [bind_map_left]
    refine (EvalDistEq.bind_left h _).trans ?_
    rw [bind_map_left]
    exact EvalDistEq.rfl
  rw [e2.prEvent_eq]
  refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun p hp ↦ le_of_eq ?_
  have ht := transcriptHashes_eq_of_mem_support A hp
  rw [postR, simulateQ_map, StateT.run'_eq, StateT.run_map, prEvent_map, prEvent_map,
    verifierPhase, prEvent_map]
  have h := (run'_toRHF (verifier queryH queryF p.1.1.1.1 p.1.1.1.2 p.1.1.2) p.2).prEvent_eq
    (fun v ↦ BreaksRpm extractorRpm ((p.1.1, v), p.1.2))
  rw [StateT.run'_eq, StateT.run'_eq, prEvent_map, prEvent_map] at h
  refine h.trans ?_
  congr 2
  funext r
  simp only [BreaksRpm, Breaks, extractorRpm, extractor, ht]
  rfl

/-- **Knowledge soundness in the random-permutation model.** An adversary of at most `Q` queries
to `π` and `π⁻¹` breaks soundness, for the extractor `extractorRpm`, with probability at most the
random-oracle error at `Q` queries plus `(Q + verifierPermCalls)² / 2^508`. -/
theorem knowledgeSoundnessRpm {A : RpmAdversary} {Q : ℕ} (hA : A.IsTotalQueryBound Q) :
    Pr{let z ← rpmExperiment A}[BreaksRpm extractorRpm z] ≤
      soundnessError Q + rpmError (Q + verifierPermCalls) := by
  rw [(rpmExperiment_evalDistEq A).prEvent_eq, game]
  obtain ⟨h1, -⟩ := Common.keccak256_transfer2 (pure ()) (fun _ ↦ advR A) (fun _ z ↦ postR z)
    (fun _ z ↦ duplex_postR z) (Q + verifierPermCalls) (isWeightBound_game hA)
    (BreaksRpm extractorRpm)
  refine h1.trans (add_le_add ((romGame_le A).trans ?_) le_rfl)
  exact knowledgeSoundness_coins (isWeightBound_romAdv hA)

/-! ## Completeness -/

/-- The honest prover and the verifier, one oracle computation. -/
noncomputable def honestRun (prog : Program) (input : PublicInput) (t : Trace prog) (ρ fuel : ℕ) :
    OracleComp HashSpec Bool :=
  EndToEnd.Complete.honestComp prog input t ρ fuel >>= fun proof ↦
    verifier queryH queryF prog input proof

/-- The verdict of the random-oracle experiment against the honest prover is the run of the honest
prover and the verifier against the random oracles. -/
theorem experiment_honest (prog : Program) (input : PublicInput) (t : Trace prog) (ρ fuel : ℕ) :
    (fun z ↦ z.1.2) <$> experiment (honestProver prog input t ρ fuel) =
      (simulateQ HashSpec.randomOracle (honestRun prog input t ρ fuel)).run' ∅ := by
  simp only [experiment, honestProver, EndToEnd.Complete.honestProverRom, honestRun,
    simulateQ_map, StateT.run_map, bind_map_left, map_bind, simulateQ_bind, StateT.run'_eq,
    StateT.run_bind]
  refine bind_congr fun p ↦ ?_
  simp

theorem isWeightBound_honestGame (prog : Program) (input : PublicInput) (t : Trace prog)
    (ρ fuel : ℕ) :
    Common.IsWeightBound (honestGame (honestRun prog input t ρ fuel)) gameCost
      (completenessPermCalls fuel) := by
  rw [honestGame, Common.rpmGame2, simulateQ_pure, pure_bind, simulateQ_pure, pure_bind]
  exact isWeightBound_hfEmbed_toRHF (isWeightBound_honest prog input t ρ fuel)

/-- **Completeness in the random-permutation model**, for the honest prover
`LeanVM.Protocol.EndToEnd.Complete.honestComp`. -/
theorem completenessRpm {prog : Program} {input : PublicInput} {t : Trace prog}
    (hv : ValidExecution prog input t) (hbudget : t.committedSize ≤ 2 ^ 28) {ρ : ℕ}
    (hρ : 1 ≤ ρ ∧ ρ ≤ 4) {fuel : ℕ} (hfuel : fuel ≤ 2 ^ 64) :
    Pr{let v ← rpmCompletenessExperiment
        (fun prog input t ρ fuel ↦ EndToEnd.Complete.honestComp prog input t ρ fuel)
        prog input t ρ fuel}[v = false] ≤
      completenessError fuel + rpmError (completenessPermCalls fuel) := by
  have e0 : rpmCompletenessExperiment
      (fun prog input t ρ fuel ↦ EndToEnd.Complete.honestComp prog input t ρ fuel)
      prog input t ρ fuel = (simulateQ rpmImpl (honestRun prog input t ρ fuel)).run' [] := rfl
  rw [e0, (rpmHonest_evalDistEq _).prEvent_eq, honestGame]
  obtain ⟨h1, -⟩ := Common.keccak256_transfer2 (pure ()) (fun _ ↦ (pure () : OracleComp RSpec Unit))
    (fun _ _ ↦ simulateQ toRHF (honestRun prog input t ρ fuel))
    (fun _ _ ↦ duplex_toRHF _ [] (duplexVm_honest prog input t ρ fuel))
    (completenessPermCalls fuel) (isWeightBound_honestGame prog input t ρ fuel) (· = false)
  refine h1.trans (add_le_add (le_of_eq_of_le ?_ (completenessRom hv hbudget hρ hfuel)) le_rfl)
  have e1 : Common.romRun2 (simulateQ Common.hInF (pure ()) >>= fun x ↦
      Common.advS2 Common.keccakPadding Common.KState.zero
        ((fun _ ↦ (pure () : OracleComp RSpec Unit)) x) >>= fun a ↦
          (fun _ _ ↦ simulateQ toRHF (honestRun prog input t ρ fuel)) x a) =
      (simulateQ HFS.romImpl (simulateQ toRHF (honestRun prog input t ρ fuel))).run' ∅ := by
    simp [Common.romRun2, Common.advS2]
  rw [e1, (run'_toRHF _ _).prEvent_eq, cmap_empty, ← experiment_honest, prEvent_map]

/-! ## The numbers -/

theorem soundnessError_eq (Q : ℕ) :
    soundnessError Q = (((Q + 12008) * (2 ^ 128 + 7 * (Q + 12008)) + 12008 : ℕ) : ℝ≥0∞) /
      ((2 ^ 256 : ℕ) : ℝ≥0∞) := by
  have h2 : ((2 ^ 256 : ℕ) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ 256 := by rw [Nat.cast_pow, Nat.cast_ofNat]
  have hV : (verifierQueries : ℝ≥0∞) = ((12008 : ℕ) : ℝ≥0∞) := rfl
  rw [soundnessError, hV, show verifierQueries = 12008 from rfl,
    EndToEnd.Sound.inv_pow_eq_div 128 256 (by norm_num), ← h2,
    ENNReal.div_add_div_same, ← mul_div_assoc, ← Nat.cast_add, ← Nat.cast_mul,
    ENNReal.div_add_div_same, ← Nat.cast_add]

theorem rpmError_eq (q : ℕ) :
    rpmError q = ((q ^ 2 : ℕ) : ℝ≥0∞) / ((2 ^ 508 : ℕ) : ℝ≥0∞) := by
  rw [rpmError, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat]

/-- **The knowledge-soundness bound in the random-permutation model**: against `2^64` queries to
`π` and `π⁻¹`, at most `2^-63`. -/
theorem soundnessRpm_le {Q : ℕ} (hQ : Q ≤ 2 ^ 64) :
    soundnessError Q + rpmError (Q + verifierPermCalls) ≤ (2 : ℝ≥0∞)⁻¹ ^ 63 := by
  have hc : ((2 ^ 252 : ℕ) : ℝ≥0∞) ≠ 0 := by positivity
  have hc' : ((2 ^ 252 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [soundnessError_eq, rpmError_eq, EndToEnd.Sound.inv_pow_eq_div 63 508 (by norm_num),
    ← ENNReal.mul_div_mul_right _ _ hc hc', ← Nat.cast_mul, ← Nat.cast_mul,
    ← pow_add, ENNReal.div_add_div_same, ← Nat.cast_add, show 256 + 252 = 508 from rfl]
  refine ENNReal.div_le_div_right (Nat.cast_le.2 ?_) _
  rw [show verifierPermCalls = 12008 * 2 ^ 32 from rfl]
  calc ((Q + 12008) * (2 ^ 128 + 7 * (Q + 12008)) + 12008) * 2 ^ 252 +
        (Q + 12008 * 2 ^ 32) ^ 2
      ≤ ((2 ^ 64 + 12008) * (2 ^ 128 + 7 * (2 ^ 64 + 12008)) + 12008) * 2 ^ 252 +
        (2 ^ 64 + 12008 * 2 ^ 32) ^ 2 := by gcongr
    _ ≤ 2 ^ 200 * 2 ^ 245 := by norm_num
    _ = 2 ^ (508 - 63) := by rw [← pow_add]

/-- **The knowledge-soundness bound in bits in the random-permutation model**: for `Q ≤ 2^120`
queries to `π` and `π⁻¹`, at most `(Q + 2^14) · 2^-127`. The random-oracle error is bounded as in
`soundnessError_le_bits`, and `(Q + verifierPermCalls)² / 2^508 ≤ 2^242 / 2^508` fits in the
slack. -/
theorem soundnessRpm_le_bits {Q : ℕ} (hQ : Q ≤ 2 ^ 120) :
    soundnessError Q + rpmError (Q + verifierPermCalls) ≤
      (Q + 2 ^ 14 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 127 := by
  have hc : ((2 ^ 252 : ℕ) : ℝ≥0∞) ≠ 0 := by positivity
  have hc' : ((2 ^ 252 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hQ' : (Q + 2 ^ 14 : ℝ≥0∞) = ((Q + 2 ^ 14 : ℕ) : ℝ≥0∞) := by norm_cast
  rw [soundnessError_eq, rpmError_eq,
    ← ENNReal.mul_div_mul_right _ _ hc hc', ← Nat.cast_mul, ← Nat.cast_mul,
    ← pow_add, ENNReal.div_add_div_same, ← Nat.cast_add, show 256 + 252 = 508 from rfl,
    EndToEnd.Sound.inv_pow_eq_div 127 508 (by norm_num), hQ', ← mul_div_assoc, ← Nat.cast_mul]
  refine ENNReal.div_le_div_right (Nat.cast_le.2 ?_) _
  rw [show verifierPermCalls = 12008 * 2 ^ 32 from rfl, show 508 - 127 = 381 from rfl]
  have h7 : 7 * (Q + 12008) ≤ 2 ^ 128 :=
    calc 7 * (Q + 12008) ≤ 7 * (2 ^ 120 + 12008) := by gcongr
      _ ≤ 2 ^ 128 := by norm_num
  have hP : Q + 12008 * 2 ^ 32 ≤ 2 ^ 121 :=
    calc Q + 12008 * 2 ^ 32 ≤ 2 ^ 120 + 12008 * 2 ^ 32 := by gcongr
      _ ≤ 2 ^ 121 := by norm_num
  calc ((Q + 12008) * (2 ^ 128 + 7 * (Q + 12008)) + 12008) * 2 ^ 252 + (Q + 12008 * 2 ^ 32) ^ 2
      ≤ ((Q + 12008) * (2 ^ 128 + 2 ^ 128) + 12008) * 2 ^ 252 + (2 ^ 121) ^ 2 := by gcongr
    _ ≤ ((Q + 12008) * (2 ^ 128 + 2 ^ 128) + 12008) * 2 ^ 252 + 2 ^ 252 :=
        Nat.add_le_add_left (by norm_num) _
    _ = ((Q + 12008) * (2 ^ 128 + 2 ^ 128) + 12008 + 1) * 2 ^ 252 := by ring
    _ ≤ (Q + 2 ^ 14) * 2 ^ 129 * 2 ^ 252 := by
        gcongr
        calc (Q + 12008) * (2 ^ 128 + 2 ^ 128) + 12008 + 1
            = Q * 2 ^ 129 + (12008 * 2 ^ 129 + 12009) := by ring
          _ ≤ Q * 2 ^ 129 + 2 ^ 14 * 2 ^ 129 := Nat.add_le_add_left (by norm_num) _
          _ = (Q + 2 ^ 14) * 2 ^ 129 := by ring
    _ = (Q + 2 ^ 14) * 2 ^ 381 := by rw [mul_assoc, ← pow_add]

theorem rpmError_completenessPermCalls_le :
    rpmError (completenessPermCalls (2 ^ 25)) ≤ (2 : ℝ≥0∞)⁻¹ ^ 128 := by
  rw [rpmError_eq, EndToEnd.Sound.inv_pow_eq_div 128 508 (by norm_num)]
  refine ENNReal.div_le_div_right (Nat.cast_le.2 ?_) _
  rw [completenessPermCalls, show 508 - 128 = 190 + 190 from rfl, pow_add]
  norm_num

/-- **The completeness bound in the random-permutation model**: at a fuel of `2^25` nonces per
proof of work, at most `2^-127`. -/
theorem completenessRpm_le :
    completenessError (2 ^ 25) + rpmError (completenessPermCalls (2 ^ 25)) ≤
      (2 : ℝ≥0∞)⁻¹ ^ 127 := by
  calc completenessError (2 ^ 25) + rpmError (completenessPermCalls (2 ^ 25))
      ≤ (2 : ℝ≥0∞)⁻¹ ^ 128 + (2 : ℝ≥0∞)⁻¹ ^ 128 :=
        add_le_add completenessError_le rpmError_completenessPermCalls_le
    _ = (2 : ℝ≥0∞)⁻¹ ^ 127 := by
        rw [← two_mul, pow_succ, ← mul_assoc, mul_comm 2, mul_assoc,
          ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]

end LeanVM.Rpm

namespace LeanVM

/-! ## The statements of `LeanVM/Spec/Rpm.lean` -/

/-- **Knowledge soundness holds** (in the random-permutation model), for the extractor
`extractorRpm`. -/
theorem knowledgeSoundness_holds : KnowledgeSoundness :=
  fun _ _ hA ↦ Rpm.knowledgeSoundnessRpm hA

open OracleComp OracleSpec in
open scoped ENNReal in
/-- **Knowledge soundness in bits** (in the random-permutation model): an adversary of at most
`Q ≤ 2^120` queries to `π` and `π⁻¹` breaks soundness, for the extractor `extractorRpm`, with
probability at most `(Q + 2^14) · 2^-127`. -/
theorem knowledgeSoundness_bits : ∀ (A : RpmAdversary) (Q : ℕ), A.IsTotalQueryBound Q →
    Q ≤ 2 ^ 120 →
      Pr{let z ← rpmExperiment A}[BreaksRpm extractorRpm z] ≤
        (Q + 2 ^ 14 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 127 :=
  fun _ _ hA hQ ↦ (Rpm.knowledgeSoundnessRpm hA).trans (Rpm.soundnessRpm_le_bits hQ)

/-- **Completeness holds** (in the random-permutation model), with the honest prover
`LeanVM.Protocol.EndToEnd.Complete.honestComp`. -/
theorem completeness_holds : Completeness :=
  ⟨fun prog input t ρ fuel ↦ Protocol.EndToEnd.Complete.honestComp prog input t ρ fuel,
    fun _ _ _ _ _ hv hbudget hρ hfuel ↦ Rpm.completenessRpm hv hbudget hρ hfuel⟩

/-- Keccak-256 over the deployed Keccak-f[1600] is the deployed Keccak-256, and `common`'s
Keccak-256 sponge over it, read on bytes. -/
theorem keccak256_eq_rpm (data : Protocol.Compile.Bytes) :
    keccak256With (m := Id) Semantics.keccakF data = Protocol.KeccakHash.keccak256 data ∧
      Protocol.KeccakHash.keccak256 data = Digest.ofRpm (Common.keccak256With (m := Id)
        (fun x ↦ KState.toRpm (Semantics.keccakF (Rpm.KState.ofRpm x))) data) :=
  ⟨Rpm.keccak256With_keccakF data, Rpm.keccak256_eq_rpm data⟩

end LeanVM
