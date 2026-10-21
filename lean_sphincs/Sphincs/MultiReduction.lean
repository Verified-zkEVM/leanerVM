import Sphincs.MultiEager
import Sphincs.BridgeAssembly
import Sphincs.BridgeDetInternalize
import Sphincs.StatementMulti

/-! **From `n` keys to one.** The reduction `toSingle adversary j` plays the multi-user experiment
against the single-key experiment of `StatementDet`, its challenge key at position `j`: it draws the
seeds of the other keys, generates them through the oracle, answers the signing requests of key `j`
with its own signing oracle and the others by running `Seeded.sign` through the oracle, and outputs
the message and signature of the forgery. Every hash call of the multi-user experiment is a hash
call of the single-key one: a win for key `j` within `q` hash calls is a win of the reduction within
`q` hash calls. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.Multi

open MultiEager Completeness Internalize Short Eager SeedCoupling

set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

variable [Params] {n : ℕ}

/-! ### The reduction -/

/-- A placeholder secret key, never used: the reduction does not know the challenge key. -/
def placeholderKey : Seeded.SecretKey := ⟨0, 0, 0⟩

/-- The key of a position: the given public key with a placeholder secret key, or the key
generated from its seed. -/
def keyFor (given : Option PublicKey) (seed : MasterSeed) : OracleComp HashSpec (PublicKey × Seeded.SecretKey) :=
  match given with
  | some pk => pure (pk, placeholderKey)
  | none => Seeded.keygenFromSeed seed

/-- Key generation of the keys without a given public key, the given ones in place. -/
def keygenSel : (k : ℕ) → (Fin k → MasterSeed) → (Fin k → Option PublicKey) →
    OracleComp HashSpec (Fin k → PublicKey × Seeded.SecretKey)
  | 0, _, _ => pure Fin.elim0
  | k + 1, seeds, given =>
      keygenSel k (fun i => seeds i.castSucc) (fun i => given i.castSucc) >>= fun keys =>
        keyFor (given (Fin.last k)) (seeds (Fin.last k)) >>= fun key => pure (Fin.lastCases key keys)

/-- The challenge key at position `j`. -/
def givenAt (j : Fin n) (pk : PublicKey) : Fin n → Option PublicKey := fun i => if i = j then some pk else none

/-- The multi-user oracles inside the reduction: the signing requests of key `j` go to the
single-key signing oracle, the others are signed through the oracle. -/
noncomputable def reductionImpl (j : Fin n) (keys : Fin n → PublicKey × Seeded.SecretKey) :
    QueryImpl (OracleWorld + SigningSpec n) (OracleComp AdvSpec)
  | .inl query => liftM (AdvSpec.query (.inl query))
  | .inr request => if request.1 = j then liftM (AdvSpec.query (.inr request.2))
      else liftWorld (liftM (Seeded.sign (keys request.1).2 request.2 : OracleComp HashSpec (Option Signature)))

/-- **The reduction** against the single-key experiment, its challenge key at position `j`. -/
noncomputable def toSingle (adversary : Adversary n) (j : Fin n) : Security.Adversary where
  main pk := do
    let others ← liftWorld (liftM (sampleSeeds n) : OracleComp OracleWorld (Fin n → MasterSeed))
    let keys ← liftWorld (liftM (keygenSel n others (givenAt j pk)) :
      OracleComp OracleWorld (Fin n → PublicKey × Seeded.SecretKey))
    let forgery ← simulateQ (reductionImpl j keys) (adversary.main fun i => if i = j then pk else (keys i).1)
    return ⟨forgery.message, forgery.signature⟩

/-! ### The logs -/

/-- The requests of key `j`, as a single-key log. -/
def logOf (j : Fin n) (log : QueryLog (SigningSpec n)) : QueryLog Sphincs.SigningSpec :=
  log.filterMap fun entry => if entry.1.1 = j then some ⟨entry.1.2, entry.2⟩ else none

omit [Params] in
theorem logOf_append (j : Fin n) (log log' : QueryLog (SigningSpec n)) :
    logOf j (log ++ log') = logOf j log ++ logOf j log' := List.filterMap_append

omit [Params] in
theorem requests_eq_length (log : QueryLog (SigningSpec n)) (j : Fin n) :
    requests log j = (logOf j log).length := by
  induction log with
  | nil => rfl
  | cons entry log ih =>
      unfold requests logOf at *
      by_cases h : entry.1.1 = j <;> simp [h, ih]

omit [Params] in
theorem contains_iff (log : QueryLog (SigningSpec n)) (j : Fin n) (message : Message) (signature : Signature) :
    Contains log ⟨j, message, signature⟩ ↔
      SigningTranscript.Contains (logOf j log) ⟨message, signature⟩ := by
  unfold Contains SigningTranscript.Contains logOf
  constructor
  · rintro ⟨entry, hmem, h1, h2⟩
    refine ⟨⟨entry.1.2, entry.2⟩, List.mem_filterMap.2 ⟨entry, hmem, ?_⟩, ?_, h2⟩
    · simp [show entry.1.1 = j from congrArg Prod.fst h1]
    · exact congrArg Prod.snd h1
  · rintro ⟨entry, hmem, h1, h2⟩
    obtain ⟨e, he, hfe⟩ := List.mem_filterMap.1 hmem
    by_cases hj : e.1.1 = j
    · simp only [hj, ↓reduceIte, Option.some.injEq] at hfe
      subst hfe
      exact ⟨e, he, Prod.ext hj h1, h2⟩
    · simp [hj] at hfe

/-! ### The run of the adversary inside the reduction -/

/-- The multi-user run of an adversary computation with the signing oracles of `keys`. -/
noncomputable def runMU (keys : Fin n → PublicKey × Seeded.SecretKey) {α : Type}
    (M : OracleComp (OracleWorld + SigningSpec n) α) : OracleComp OracleWorld (α × QueryLog (SigningSpec n)) :=
  (simulateQ (QueryImpl.ofLift OracleWorld (WriterT (QueryLog (SigningSpec n)) (OracleComp OracleWorld)) +
    signingOracle keys) M).run

theorem run_signingOracle (keys : Fin n → PublicKey × Seeded.SecretKey) (request : Fin n × Message) :
    (signingOracle keys request).run = (do
      let signature ← (liftM (Seeded.sign (keys request.1).2 request.2 : OracleComp HashSpec (Option Signature)) :
        OracleComp OracleWorld (Option Signature))
      pure (signature, [⟨request, signature⟩])) := by
  simp only [signingOracle, QueryImpl.run_withLogging_apply]

theorem run_gameImplDet_sign (sk : Seeded.SecretKey) (message : Message) :
    (simulateQ (Det.gameImplDet sk) (liftM (AdvSpec.query (.inr message)) : OracleComp AdvSpec _)).run = (do
      let signature ← (liftM (Seeded.sign sk message : OracleComp HashSpec (Option Signature)) :
        OracleComp OracleWorld (Option Signature))
      pure (signature, [⟨message, signature⟩])) := by
  rw [simulateQ_spec_query]
  simp only [Det.gameImplDet, QueryImpl.add_apply_inr, Det.signingOracleDet, QueryImpl.run_withLogging_apply]

omit [Params] in
theorem run_liftM_world_writer {ω : Type} [EmptyCollection ω] [Append ω] (query : OracleWorld.Domain) :
    (liftM (OracleWorld.query query) : WriterT ω (OracleComp OracleWorld) _).run =
      (fun answer => (answer, ∅)) <$> (liftM (OracleWorld.query query) : OracleComp OracleWorld _) := rfl

/-- **The reduction runs the adversary as the multi-user experiment does**, with the signing log of
key `j` as its own. -/
theorem run_reduction (j : Fin n) (keys : Fin n → PublicKey × Seeded.SecretKey) {α : Type}
    (M : OracleComp (OracleWorld + SigningSpec n) α) :
    (simulateQ (Det.gameImplDet (keys j).2) (simulateQ (reductionImpl j keys) M)).run =
      (fun result => (result.1, logOf j result.2)) <$> runMU keys M := by
  induction M using OracleComp.inductionOn with
  | pure value => simp [runMU, logOf]
  | query_bind input next ih =>
      unfold runMU at ih ⊢
      rcases input with world | request
      · simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind, reductionImpl, Det.gameImplDet,
          QueryImpl.add_apply_inl, QueryImpl.ofLift_apply, map_bind, Functor.map_map, logOf_append]
        rw [run_liftM_world_writer, run_liftM_world_writer, bind_map_left, bind_map_left]
        refine bind_congr fun answer => ?_
        have h := ih answer
        simp only [Det.gameImplDet] at h
        simp only [h, Functor.map_map]
        simp [logOf]
      · rcases request with ⟨i, message⟩
        simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind, QueryImpl.add_apply_inr]
        rw [run_signingOracle]
        by_cases hij : i = j
        · subst hij
          have hred : reductionImpl i keys (.inr (i, message)) = liftM (AdvSpec.query (.inr message)) := by
            simp [reductionImpl]
          rw [hred, run_gameImplDet_sign]
          simp only [bind_assoc, pure_bind, map_bind]
          refine bind_congr fun signature => ?_
          simp only [ih, Functor.map_map]
          simp [logOf]
        · have hred : reductionImpl j keys (.inr (i, message)) =
              liftWorld (liftM (Seeded.sign (keys i).2 message : OracleComp HashSpec (Option Signature))) := by
            simp [reductionImpl, hij]
          rw [hred, Det.gameImplDet_liftWorld, bind_map_left]
          simp only [bind_assoc, pure_bind, map_bind]
          refine bind_congr fun signature => ?_
          simp only [ih, Functor.map_map]
          simp [logOf, hij]

/-! ### Key generation under fixed answers -/

section Fixed

variable (answers : HashInput → HashOutput)

/-- One key from its seed. -/
abbrev keygenOne (seed : MasterSeed) : OracleComp HashSpec (PublicKey × Seeded.SecretKey) :=
  Seeded.keygenFromSeed seed

/-- The key of a position: the given public key, or the key generated from its seed. -/
def keyAt {k : ℕ} (seeds : Fin k → MasterSeed) (given : Fin k → Option PublicKey) (i : Fin k) :
    PublicKey × Seeded.SecretKey :=
  (given i).elim (valF answers (keygenOne (seeds i))) fun pk => (pk, placeholderKey)

theorem keygenSel_succ (k : ℕ) (seeds : Fin (k + 1) → MasterSeed) (given : Fin (k + 1) → Option PublicKey) :
    keygenSel (k + 1) seeds given =
      keygenSel k (fun i => seeds i.castSucc) (fun i => given i.castSucc) >>= fun keys =>
        keyFor (given (Fin.last k)) (seeds (Fin.last k)) >>= fun key => pure (Fin.lastCases key keys) := rfl

theorem valF_keyFor (given : Option PublicKey) (seed : MasterSeed) :
    valF answers (keyFor given seed) = given.elim (valF answers (keygenOne seed)) fun pk => (pk, placeholderKey) := by
  cases given <;> rfl

theorem callsF_keyFor (given : Option PublicKey) (seed : MasterSeed) :
    callsF answers (keyFor given seed) = given.elim (callsF answers (keygenOne seed)) fun _ => 0 := by
  cases given <;> rfl

theorem recF_keyFor (given : Option PublicKey) (seed : MasterSeed) (cache : QueryCache HashSpec) :
    recF answers (keyFor given seed) cache = given.elim (recF answers (keygenOne seed) cache) fun _ => cache := by
  cases given <;> rfl

theorem valF_keygenSel : ∀ (k : ℕ) (seeds : Fin k → MasterSeed) (given : Fin k → Option PublicKey),
    valF answers (keygenSel k seeds given) = keyAt answers seeds given
  | 0, _, _ => funext fun i => i.elim0
  | k + 1, seeds, given => by
      rw [keygenSel_succ, valF_bind, valF_bind, valF_keygenSel k, valF_keyFor]
      funext i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simp [keyAt, valF]
      · simp [keyAt, valF]

/-- The calls of a position: those of its key generation, none for a given key. -/
def callsAt {k : ℕ} (seeds : Fin k → MasterSeed) (given : Fin k → Option PublicKey) (i : Fin k) : ℕ :=
  (given i).elim (callsF answers (keygenOne (seeds i))) fun _ => 0

theorem callsF_keygenSel : ∀ (k : ℕ) (seeds : Fin k → MasterSeed) (given : Fin k → Option PublicKey),
    callsF answers (keygenSel k seeds given) = ∑ i, callsAt answers seeds given i
  | 0, _, _ => rfl
  | k + 1, seeds, given => by
      rw [keygenSel_succ, callsF_bind, callsF_bind, callsF_keygenSel k, Fin.sum_univ_castSucc, callsF_keyFor]
      simp [callsAt, callsF]

/-- A position records an input: its key generation does, the given keys record nothing. -/
def RecordsAt {k : ℕ} (seeds : Fin k → MasterSeed) (given : Fin k → Option PublicKey) (i : Fin k)
    (input : HashInput) : Prop :=
  given i = none ∧ recF answers (keygenOne (seeds i)) ∅ input ≠ none

theorem recF_keygenSel_none : ∀ (k : ℕ) (seeds : Fin k → MasterSeed) (given : Fin k → Option PublicKey)
    (input : HashInput),
    recF answers (keygenSel k seeds given) ∅ input = none ↔ ∀ i, ¬RecordsAt answers seeds given i input
  | 0, _, _, _ => by simp [recF, RecordsAt, keygenSel]
  | k + 1, seeds, given, input => by
      rw [keygenSel_succ, recF_bind, recF_bind, recF_keyFor, Fin.forall_fin_succ']
      have ih := recF_keygenSel_none k (fun i => seeds i.castSucc) (fun i => given i.castSucc) input
      change ((given (Fin.last k)).elim _ _ : QueryCache HashSpec) input = none ↔ _
      cases hg : given (Fin.last k) with
      | some pk => simpa [RecordsAt, hg] using ih
      | none =>
          rw [Option.elim_none, recF_apply]
          by_cases hr : recF answers (keygenOne (seeds (Fin.last k))) ∅ input = none
          · simp only [hr, ↓reduceIte, ih]
            simp [RecordsAt, hr]
          · simp [hr, RecordsAt, hg]

theorem keygenAll_eq : ∀ (k : ℕ) (seeds : Fin k → MasterSeed),
    keygenAll k seeds = keygenSel k seeds fun _ => none
  | 0, _ => rfl
  | k + 1, seeds => by
      rw [keygenSel_succ, ← keygenAll_eq k]
      rfl

/-- The hash calls of the reduction's world before the adversary runs: the challenge key, then the
other keys around it. -/
def hashB (j : Fin n) (seed : MasterSeed) (others : Fin n → MasterSeed) :
    OracleComp HashSpec ((PublicKey × Seeded.SecretKey) × (Fin n → PublicKey × Seeded.SecretKey)) :=
  keygenOne seed >>= fun key => keygenSel n others (givenAt j key.1) >>= fun keys => pure (key, keys)

/-- The keys of the multi-user experiment from those of the reduction's world. -/
def combine (j : Fin n) (keys : (PublicKey × Seeded.SecretKey) × (Fin n → PublicKey × Seeded.SecretKey)) :
    Fin n → PublicKey × Seeded.SecretKey := fun i => if i = j then keys.1 else keys.2 i

theorem valF_hashB (j : Fin n) (seed : MasterSeed) (others : Fin n → MasterSeed) :
    combine j (valF answers (hashB j seed others)) =
      valF answers (keygenAll n (Function.update others j seed)) := by
  rw [keygenAll_eq, valF_keygenSel, hashB, valF_bind, valF_bind, valF_keygenSel]
  funext i
  by_cases hi : i = j
  · subst hi
    simp [combine, keyAt, valF]
  · simp [combine, keyAt, valF, givenAt, hi]

theorem callsF_hashB (j : Fin n) (seed : MasterSeed) (others : Fin n → MasterSeed) :
    callsF answers (hashB j seed others) = callsF answers (keygenAll n (Function.update others j seed)) := by
  rw [keygenAll_eq, callsF_keygenSel, hashB, callsF_bind, callsF_bind, callsF_keygenSel,
    Fintype.sum_eq_add_sum_compl j, Fintype.sum_eq_add_sum_compl j (callsAt answers _ _)]
  have hrest : ∑ i ∈ ({j} : Finset (Fin n))ᶜ, callsAt answers others (givenAt j (valF answers (keygenOne seed)).1) i =
      ∑ i ∈ ({j} : Finset (Fin n))ᶜ, callsAt answers (Function.update others j seed) (fun _ => none) i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hij : i ≠ j := by simpa using hi
    simp [callsAt, givenAt, hij]
  rw [hrest]
  simp [callsAt, givenAt, callsF]

theorem recF_hashB (j : Fin n) (seed : MasterSeed) (others : Fin n → MasterSeed) :
    recF answers (hashB j seed others) ∅ = recF answers (keygenAll n (Function.update others j seed)) ∅ := by
  refine QueryCache.ext fun input => ?_
  have hB : recF answers (hashB j seed others) ∅ =
      recF answers (keygenSel n others (givenAt j (valF answers (keygenOne seed)).1))
        (recF answers (keygenOne seed) ∅) := by
    rw [hashB, recF_bind, recF_bind]
    rfl
  rw [hB, recF_apply answers (keygenSel n _ _), recF_apply answers (keygenAll n _),
    recF_apply answers (keygenOne seed)]
  have hnone : (recF answers (keygenSel n others (givenAt j (valF answers (keygenOne seed)).1)) ∅ input = none ∧
      recF answers (keygenOne seed) ∅ input = none) ↔
      recF answers (keygenAll n (Function.update others j seed)) ∅ input = none := by
    rw [keygenAll_eq, recF_keygenSel_none, recF_keygenSel_none]
    constructor
    · rintro ⟨h1, h2⟩ i ⟨-, hi⟩
      by_cases hij : i = j
      · subst hij
        simp only [Function.update_self] at hi
        exact hi h2
      · rw [Function.update_of_ne hij] at hi
        exact h1 i ⟨by simp [givenAt, hij], hi⟩
    · intro h
      refine ⟨fun i ⟨hg, hi⟩ => ?_, ?_⟩
      · have hij : i ≠ j := by
          intro hij
          simp [givenAt, hij] at hg
        exact h i ⟨rfl, by rwa [Function.update_of_ne hij]⟩
      · by_contra hc
        exact h j ⟨rfl, by simpa using hc⟩
  by_cases h1 : recF answers (keygenSel n others (givenAt j (valF answers (keygenOne seed)).1)) ∅ input = none <;>
    by_cases h2 : recF answers (keygenOne seed) ∅ input = none
  · have h3 := hnone.1 ⟨h1, h2⟩
    simp only [h1, h2, h3, ↓reduceIte]
  · have h3 : ¬recF answers (keygenAll n (Function.update others j seed)) ∅ input = none :=
      fun h => h2 (hnone.2 h).2
    simp only [h1, h2, h3, ↓reduceIte]
  · have h3 : ¬recF answers (keygenAll n (Function.update others j seed)) ∅ input = none :=
      fun h => h1 (hnone.2 h).1
    simp only [h1, h3, ↓reduceIte]
  · have h3 : ¬recF answers (keygenAll n (Function.update others j seed)) ∅ input = none :=
      fun h => h1 (hnone.2 h).1
    simp only [h1, h3, ↓reduceIte]

end Fixed

/-! ### The hash calls before the adversary runs -/

theorem only_keyFor (given : Option PublicKey) (seed : MasterSeed) : Short.Only (keyFor given seed) := by
  cases given
  · exact Short.Seeded.Only.keygenFromSeed seed
  · exact Short.Only.pure' _

theorem only_keygenSel : ∀ (k : ℕ) (seeds : Fin k → MasterSeed) (given : Fin k → Option PublicKey),
    Short.Only (keygenSel k seeds given)
  | 0, _, _ => Short.Only.pure' _
  | k + 1, _, _ => Short.Only.bind (only_keygenSel k _ _) fun _ =>
      Short.Only.bind (only_keyFor _ _) fun _ => Short.Only.pure' _

theorem only_hashB (j : Fin n) (seed : MasterSeed) (others : Fin n → MasterSeed) :
    Short.Only (hashB j seed others) :=
  Short.Only.bind (Short.Seeded.Only.keygenFromSeed seed) fun _ =>
    Short.Only.bind (only_keygenSel n _ _) fun _ => Short.Only.pure' _

omit [Params] in
/-- The counted lazy run of a hash computation with only short inputs from the empty cache: the
value, the calls and the record under a uniform table. -/
theorem evalDist_counted_liftM {α : Type} (oa : OracleComp HashSpec α) (h : Short.Only oa) :
    (simulateQ romImpl (countHashQueries (liftM oa : OracleComp OracleWorld α))).run ∅ =ᵈ
      (do let table ← $ᵗ Table
          pure ((valF (extend ∅ table) oa, callsF (extend ∅ table) oa), recF (extend ∅ table) oa ∅)) := by
  refine (evalDist_romImpl_run_eq_table (countHashQueries (liftM oa : OracleComp OracleWorld α))
    (Assembly.OnlyW.counted _ _ (OnlyW.liftHash h)) ∅).trans ?_
  simp only [fixedRec_run_liftM]
  exact EvalDistEq.refl _

/-- **The reduction's hash calls before the adversary runs are those of the multi-user
experiment**: the same keys, calls and cache, the challenge key in place. -/
theorem evalDist_hashB (j : Fin n) (seed : MasterSeed) (others : Fin n → MasterSeed) :
    (fun result => ((combine j result.1.1, result.1.2), result.2)) <$>
        (simulateQ romImpl (countHashQueries (liftM (hashB j seed others) : OracleComp OracleWorld _))).run ∅ =ᵈ
      (simulateQ romImpl (countHashQueries (liftM (keygenAll n (Function.update others j seed)) :
        OracleComp OracleWorld _))).run ∅ := by
  refine ((evalDist_counted_liftM _ (only_hashB j seed others)).map _).trans ?_
  refine EvalDistEq.trans ?_ (evalDist_counted_liftM _ (by
    rw [keygenAll_eq]
    exact only_keygenSel n _ _)).symm
  simp only [map_bind, map_pure, valF_hashB, callsF_hashB, recF_hashB]
  exact EvalDistEq.refl _

/-! ### The multi-user experiment, split at the forgery's key -/

/-- The end of the multi-user game, after key generation: the forgery is checked at key `j`. -/
noncomputable def restAt (adversary : Adversary n) (j : Fin n) (keys : Fin n → PublicKey × Seeded.SecretKey) :
    OracleComp OracleWorld Bool := do
  let ((forgery, log) : Forgery n × QueryLog (SigningSpec n)) ← runMU keys (adversary.main fun i => (keys i).1)
  let verified ← liftM (Concrete.verify (keys j).1 forgery.message forgery.signature : OracleComp HashSpec Bool)
  return decide (Valid log j ∧ ¬Contains log ⟨j, forgery.message, forgery.signature⟩) && verified

/-- The multi-user game checking the forgery at key `j`. -/
noncomputable def gameAt (adversary : Adversary n) (j : Fin n) : OracleComp OracleWorld Bool := do
  let seeds ← liftM (sampleSeeds n)
  let keys ← liftM (keygenAll n seeds)
  restAt adversary j keys

/-- The multi-user game, also returning the forgery's key. -/
noncomputable def gameKey (adversary : Adversary n) : OracleComp OracleWorld (Bool × Fin n) := do
  let seeds ← liftM (sampleSeeds n)
  let keys ← liftM (keygenAll n seeds)
  let ((forgery, log) : Forgery n × QueryLog (SigningSpec n)) ← runMU keys (adversary.main fun i => (keys i).1)
  let verified ← liftM (Concrete.verify (keys forgery.key).1 forgery.message forgery.signature :
    OracleComp HashSpec Bool)
  return (decide (Valid log forgery.key ∧ ¬Contains log forgery) && verified, forgery.key)

/-- The counted run of a game from the empty cache. -/
noncomputable def counted {α : Type} (game : OracleComp OracleWorld α) : ProbComp (α × ℕ) :=
  (simulateQ romImpl (countHashQueries game)).run' ∅

theorem experiment_eq (adversary : Adversary n) :
    experiment adversary = (fun result => (result.1.1, result.2)) <$> counted (gameKey adversary) := by
  rw [experiment, counted, ← simulateQ_countHashQueries]
  have hgame : gameCore adversary = Prod.fst <$> gameKey adversary := by
    simp only [gameCore, gameKey, runMU, map_bind, map_pure]
  rw [hgame, countHashQueries, SphincsBase.QueryCap.counted_map, simulateQ_map, StateT.run'_eq,
    StateT.run'_eq, StateT.run_map, Functor.map_map, Functor.map_map]
  rfl

omit [Params] in
/-- The counted run of a game split after a first part. -/
theorem counted_bind {α β : Type} (first : OracleComp OracleWorld α) (next : α → OracleComp OracleWorld β) :
    counted (first >>= next) =
      (simulateQ romImpl (countHashQueries first)).run ∅ >>= fun result =>
        (fun rest => (rest.1, result.1.2 + rest.2)) <$>
          (simulateQ romImpl (countHashQueries (next result.1.1))).run' result.2 := by
  rw [counted, countHashQueries, SphincsBase.QueryCap.counted_bind, simulateQ_bind, StateT.run'_eq,
    StateT.run_bind, map_bind]
  refine bind_congr fun result => ?_
  rw [simulateQ_bind, StateT.run_bind, StateT.run'_eq, map_bind, Functor.map_map]
  simp only [simulateQ_pure, StateT.run_pure, map_eq_bind_pure_comp]
  rfl

/-- The game up to the forgery: the keys and the adversary's run. -/
noncomputable def prefixMU (adversary : Adversary n) :
    OracleComp OracleWorld ((Fin n → PublicKey × Seeded.SecretKey) × (Forgery n × QueryLog (SigningSpec n))) := do
  let seeds ← liftM (sampleSeeds n)
  let keys ← liftM (keygenAll n seeds)
  let result ← runMU keys (adversary.main fun i => (keys i).1)
  return (keys, result)

/-- The check of the forgery at key `j`. -/
noncomputable def checkAt (j : Fin n)
    (state : (Fin n → PublicKey × Seeded.SecretKey) × (Forgery n × QueryLog (SigningSpec n))) :
    OracleComp OracleWorld Bool := do
  let verified ← liftM (Concrete.verify (state.1 j).1 state.2.1.message state.2.1.signature :
    OracleComp HashSpec Bool)
  return decide (Valid state.2.2 j ∧ ¬Contains state.2.2 ⟨j, state.2.1.message, state.2.1.signature⟩) && verified

theorem gameKey_eq (adversary : Adversary n) :
    gameKey adversary = prefixMU adversary >>= fun state =>
      (fun won => (won, state.2.1.key)) <$> checkAt state.2.1.key state := by
  simp only [gameKey, prefixMU, checkAt, bind_assoc, pure_bind, map_bind, map_pure]

theorem gameAt_eq (adversary : Adversary n) (j : Fin n) :
    gameAt adversary j = prefixMU adversary >>= checkAt j := by
  simp only [gameAt, restAt, prefixMU, checkAt, bind_assoc, pure_bind]

/-- **A win at key `j` within the budget is a win of the game checking key `j`.** -/
theorem win_key_le (adversary : Adversary n) (j : Fin n) (q : ℕ) :
    Pr{let result ← counted (gameKey adversary)}[result.1.1 = true ∧ result.1.2 = j ∧ result.2 ≤ q] ≤
      Pr{let result ← counted (gameAt adversary j)}[result.1 = true ∧ result.2 ≤ q] := by
  rw [gameKey_eq, gameAt_eq, counted_bind, counted_bind]
  refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun first _ => ?_
  rw [countHashQueries, SphincsBase.QueryCap.counted_map, simulateQ_map, StateT.run'_eq, StateT.run_map,
    Functor.map_map, Functor.map_map, prEvent_map, StateT.run'_eq, Functor.map_map, prEvent_map,
    ← countHashQueries]
  by_cases hkey : first.1.1.2.1.key = j
  · rw [hkey]
    refine prEvent_mono_of_support (m := ProbComp) _ _ _ fun result _ h => ?_
    simp only at h ⊢
    exact ⟨h.1, h.2.2⟩
  · refine le_trans (le_of_eq (prEvent_eq_zero_of_forall_mem_support (m := ProbComp) _ _
      fun result _ h => ?_)) bot_le
    simp only at h
    exact hkey h.2.1

/-! ### The reduction's game -/

/-- The end of the reduction's game, after its key generations. -/
noncomputable def restB (adversary : Adversary n) (j : Fin n) (key : PublicKey × Seeded.SecretKey)
    (keys : Fin n → PublicKey × Seeded.SecretKey) : OracleComp OracleWorld Bool := do
  let ((forgery, log) : Forgery n × QueryLog Sphincs.SigningSpec) ←
    (simulateQ (Det.gameImplDet key.2) (simulateQ (reductionImpl j keys)
      (adversary.main fun i => if i = j then key.1 else (keys i).1))).run
  let verified ← liftM (Concrete.verify key.1 forgery.message forgery.signature : OracleComp HashSpec Bool)
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log ⟨forgery.message, forgery.signature⟩) &&
    verified

theorem reductionImpl_congr (j : Fin n) {keys keys' : Fin n → PublicKey × Seeded.SecretKey}
    (h : ∀ i, i ≠ j → keys i = keys' i) : reductionImpl j keys = reductionImpl j keys' := by
  funext query
  rcases query with world | ⟨i, message⟩
  · rfl
  · by_cases hij : i = j
    · simp [reductionImpl, hij]
    · simp [reductionImpl, hij, h i hij]

/-- **The reduction's game ends as the multi-user game checking key `j`.** -/
theorem restB_eq (adversary : Adversary n) (j : Fin n) (key : PublicKey × Seeded.SecretKey)
    (keys : Fin n → PublicKey × Seeded.SecretKey) :
    restB adversary j key keys = restAt adversary j (combine j (key, keys)) := by
  have hkeys : reductionImpl j keys = reductionImpl j (combine j (key, keys)) :=
    reductionImpl_congr j fun i hij => by simp [combine, hij]
  have hpk : (fun i => if i = j then key.1 else (keys i).1) = fun i => (combine j (key, keys) i).1 := by
    funext i
    by_cases hij : i = j <;> simp [combine, hij]
  have hsk : key.2 = (combine j (key, keys) j).2 := by simp [combine]
  have hrun := run_reduction j (combine j (key, keys)) (adversary.main fun i => (combine j (key, keys) i).1)
  rw [restB, restAt, hkeys, hpk, hsk, hrun, bind_map_left]
  refine bind_congr fun result => ?_
  have hverify : (combine j (key, keys) j).1 = key.1 := by simp [combine]
  simp only [hverify, SigningTranscript.Valid, Valid, requests_eq_length, contains_iff]

/-- **The reduction's game**: the challenge key, the other keys, then the end of the game. -/
theorem gameCoreDet_toSingle (adversary : Adversary n) (j : Fin n) :
    Det.gameCoreDet (toSingle adversary j) =
      (liftM sampleMasterSeed : OracleComp OracleWorld MasterSeed) >>= fun seed =>
        (liftM (keygenOne seed) : OracleComp OracleWorld _) >>= fun key =>
          (liftM (sampleSeeds n) : OracleComp OracleWorld _) >>= fun others =>
            (liftM (keygenSel n others (givenAt j key.1)) : OracleComp OracleWorld _) >>= fun keys =>
              restB adversary j key keys := by
  unfold Det.gameCoreDet
  refine bind_congr fun seed => bind_congr fun key => ?_
  rcases key with ⟨pk, sk⟩
  change (simulateQ (Det.gameImplDet sk) ((toSingle adversary j).main pk)).run >>= _ = _
  simp only [toSingle, simulateQ_bind, WriterT.run_bind, Det.gameImplDet_liftWorld, bind_map_left, bind_assoc]
  refine bind_congr fun others => bind_congr fun keys => ?_
  simp only [restB]
  refine bind_congr fun result => ?_
  simp [List.empty_eq]

omit [Params] in
theorem run'_sampling_bind {α β : Type} (sampling : ProbComp α) (next : α → OracleComp OracleWorld β)
    (cache : QueryCache HashSpec) :
    (simulateQ romImpl (countHashQueries ((liftM sampling : OracleComp OracleWorld α) >>= next))).run' cache =
      sampling >>= fun value => (simulateQ romImpl (countHashQueries (next value))).run' cache := by
  rw [countHashQueries_sampling_bind, simulateQ_bind, StateT.run'_eq, StateT.run_bind, run_lift_prob,
    bind_map_left, map_bind]
  rfl

omit [Params] in
theorem counted_sampling_bind {α β : Type} (sampling : ProbComp α) (next : α → OracleComp OracleWorld β) :
    counted ((liftM sampling : OracleComp OracleWorld α) >>= next) =
      sampling >>= fun value => counted (next value) :=
  run'_sampling_bind sampling next ∅

omit [Params] in
/-- A private draw commutes with the hash calls before it. -/
theorem counted_swap {α β γ : Type} (first : OracleComp HashSpec α) (sampling : ProbComp β)
    (next : α → β → OracleComp OracleWorld γ) :
    counted ((liftM first : OracleComp OracleWorld α) >>= fun a =>
        (liftM sampling : OracleComp OracleWorld β) >>= fun b => next a b) =ᵈ
      (sampling >>= fun b => counted ((liftM first : OracleComp OracleWorld α) >>= fun a => next a b)) := by
  rw [counted_bind]
  simp only [run'_sampling_bind, map_bind]
  refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
  refine EvalDistEq.bind_right _ fun b => ?_
  rw [counted_bind]

/-- **The reduction's experiment is the multi-user game checking key `j`.** -/
theorem experimentDet_toSingle (adversary : Adversary n) (j : Fin n) :
    Det.experimentDet (toSingle adversary j) =ᵈ counted (gameAt adversary j) := by
  have hexp : Det.experimentDet (toSingle adversary j) = counted (Det.gameCoreDet (toSingle adversary j)) := by
    rw [Det.experimentDet, counted, simulateQ_countHashQueries]
  rw [hexp, gameCoreDet_toSingle, counted_sampling_bind]
  refine (EvalDistEq.bind_right _ fun seed => counted_swap _ _ _).trans ?_
  have hhash : ∀ (seed : MasterSeed) (others : Fin n → MasterSeed),
      counted ((liftM (keygenOne seed) : OracleComp OracleWorld _) >>= fun key =>
          (liftM (keygenSel n others (givenAt j key.1)) : OracleComp OracleWorld _) >>= fun keys =>
            restB adversary j key keys) =ᵈ
        counted ((liftM (keygenAll n (Function.update others j seed)) : OracleComp OracleWorld _) >>=
          restAt adversary j) := by
    intro seed others
    have hb : ((liftM (keygenOne seed) : OracleComp OracleWorld _) >>= fun key =>
          (liftM (keygenSel n others (givenAt j key.1)) : OracleComp OracleWorld _) >>= fun keys =>
            restB adversary j key keys) =
        (liftM (hashB j seed others) : OracleComp OracleWorld _) >>= fun keys =>
          restAt adversary j (combine j keys) := by
      simp only [hashB, liftM_bind, bind_assoc, liftM_pure, pure_bind, restB_eq]
    rw [hb, counted_bind, counted_bind]
    have hmap := (evalDist_hashB j seed others).bind_left fun result =>
      (fun rest => (rest.1, result.1.2 + rest.2)) <$>
        (simulateQ romImpl (countHashQueries (restAt adversary j result.1.1))).run' result.2
    rw [bind_map_left] at hmap
    exact hmap
  refine (EvalDistEq.bind_right _ fun seed => EvalDistEq.bind_right _ fun others => hhash seed others).trans ?_
  rw [gameAt, counted_sampling_bind]
  let : SampleableType MasterSeed := SampleableType.ofFintype MasterSeed
  let : SampleableType (Fin n → MasterSeed) := SampleableType.ofFintype (Fin n → MasterSeed)
  have hupdate := (uniformSample_bind_update_evalDistEq (D := Fin n) (R := MasterSeed) j).bind_left
    fun seeds => counted ((liftM (keygenAll n seeds) : OracleComp OracleWorld _) >>= restAt adversary j)
  simp only [bind_assoc, pure_bind] at hupdate
  exact hupdate

/-! ### `n` keys -/

/-- **A multi-user win within the budget is a win of one of the `n` reductions within the
budget.** -/
theorem forgeAdvantage_le_sum (adversary : Adversary n) (q : ℕ) (hbound : HasHashQueryBound adversary q) :
    forgeAdvantage adversary ≤ ∑ j, Det.winWithin (toSingle adversary j) q := by
  have hwin : forgeAdvantage adversary =
      Pr{let result ← counted (gameKey adversary)}[result.1.1 = true ∧ result.2 ≤ q] := by
    rw [forgeAdvantage, prEvent_congr_of_support _ _ (fun result => result.1 = true ∧ result.2 ≤ q)
      fun result hresult => ⟨fun h => ⟨h, hbound result hresult⟩, And.left⟩, experiment_eq, prEvent_map]
  rw [hwin]
  calc _ ≤ Pr{let result ← counted (gameKey adversary)}[∃ j, result.1.1 = true ∧ result.1.2 = j ∧ result.2 ≤ q] :=
        prEvent_mono_of_support (m := ProbComp) _ _ _ fun result _ h => ⟨result.1.2, h.1, rfl, h.2⟩
    _ ≤ ∑ j, Pr{let result ← counted (gameKey adversary)}[result.1.1 = true ∧ result.1.2 = j ∧ result.2 ≤ q] :=
        prEvent_exists_le _ _
    _ ≤ ∑ j, Pr{let result ← counted (gameAt adversary j)}[result.1 = true ∧ result.2 ≤ q] :=
        Finset.sum_le_sum fun j _ => win_key_le adversary j q
    _ = ∑ j, Det.winWithin (toSingle adversary j) q := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Det.winWithin, (experimentDet_toSingle adversary j).prEvent_eq]

/-- **`n` keys from one**: the budgeted single-key bound `q / 2^bits` gives the multi-user bound
`n q / 2^bits`. -/
theorem hasMultiUserBound_of_budgeted {bits : ℕ} (h : Det.HasClassicalSecurityBitsDetBudgeted bits) (n : ℕ) :
    HasMultiUserBound n fun q => n * (q / ((2 ^ bits : ℕ) : ℝ≥0∞)) := by
  intro q hq adversary hbound
  refine (forgeAdvantage_le_sum adversary q hbound).trans ?_
  calc ∑ j, Det.winWithin (toSingle adversary j) q ≤ ∑ _j : Fin n, (q / ((2 ^ bits : ℕ) : ℝ≥0∞)) :=
        Finset.sum_le_sum fun j _ => h q hq (toSingle adversary j)
    _ = n * (q / ((2 ^ bits : ℕ) : ℝ≥0∞)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Sphincs.Security.Multi
