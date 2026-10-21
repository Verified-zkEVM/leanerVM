import Sphincs.MultiOnly
import Sphincs.MultiTransport
import Sphincs.MultiReduction

/-! **Weighted counts of hash calls.** The experiments count every hash call once. The multi-user
bound charges each reduction for the calls of its own key, so the reduction's experiment is
compared with the multi-user experiment under a weighted count, `cntW w`, which adds `w x` for each
hash call on `x`; with values in the functions from public parameters to `ℕ`, it counts the calls
of every key at once. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.Multi

open MultiEager Completeness Internalize Short Eager SeedCoupling

set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-! ### Weighted counts -/

section Weighted

variable {ω : Type} [AddCommMonoid ω] (w : HashInput → ω)

/-- The weight of a query of the world: `w x` for a hash call on `x`, nothing for a private draw. -/
def weightOf : OracleWorld.Domain → ω
  | .inl _ => 0
  | .inr x => w x

/-- The run of a world computation with the weighted count of its hash calls. -/
noncomputable def cntW {α : Type} (computation : OracleComp OracleWorld α) : OracleComp OracleWorld (α × ω) :=
  OracleComp.construct (fun result => pure (result, 0))
    (fun input _ next => do
      let answer ← liftM (OracleWorld.query input)
      let result ← next answer
      pure (result.1, weightOf w input + result.2)) computation

theorem cntW_pure {α : Type} (value : α) : cntW w (pure value : OracleComp OracleWorld α) = pure (value, 0) := rfl

theorem cntW_query_bind {α : Type} (input : OracleWorld.Domain) (next : OracleWorld.Range input → OracleComp OracleWorld α) :
    cntW w (liftM (OracleWorld.query input) >>= next) = (do
      let answer ← liftM (OracleWorld.query input)
      let result ← cntW w (next answer)
      pure (result.1, weightOf w input + result.2)) := rfl

theorem cntW_bind {α β : Type} (computation : OracleComp OracleWorld α) (next : α → OracleComp OracleWorld β) :
    cntW w (computation >>= next) = (do
      let first ← cntW w computation
      let second ← cntW w (next first.1)
      pure (second.1, first.2 + second.2)) := by
  induction computation using OracleComp.inductionOn with
  | pure result => simp only [pure_bind, cntW_pure, zero_add, Prod.mk.eta, bind_pure]
  | query_bind input continuation ih =>
      simp only [bind_assoc, cntW_query_bind, ih, pure_bind, add_assoc]

theorem cntW_map {α β : Type} (computation : OracleComp OracleWorld α) (f : α → β) :
    cntW w (f <$> computation) = (fun result => (f result.1, result.2)) <$> cntW w computation := by
  rw [show f <$> computation = computation >>= fun result => pure (f result) from (bind_pure_comp f computation).symm,
    cntW_bind]
  simp only [cntW_pure, map_pure, add_zero, bind_pure_comp]

theorem cntW_forget {α : Type} (computation : OracleComp OracleWorld α) :
    Prod.fst <$> cntW w computation = computation := by
  induction computation using OracleComp.inductionOn with
  | pure result => simp only [cntW_pure, map_pure]
  | query_bind input next ih =>
      simp only [cntW_query_bind, map_bind, bind_pure_comp, Functor.map_map, ih]

theorem cntW_lift_prob {α : Type} (computation : ProbComp α) :
    cntW w (liftM computation : OracleComp OracleWorld α) =
      (fun value => (value, 0)) <$> (liftM computation : OracleComp OracleWorld α) := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rw [liftM_bind]
      change cntW w (liftM (OracleWorld.query (.inl input)) >>= _) = _
      simp only [cntW_query_bind, ih, map_bind, bind_pure_comp, Functor.map_map, weightOf, zero_add]
      rfl

theorem cntW_sampling_bind {α β : Type} (sampling : ProbComp α) (next : α → OracleComp OracleWorld β) :
    cntW w ((liftM sampling : OracleComp OracleWorld α) >>= next) =
      (liftM sampling : OracleComp OracleWorld α) >>= fun value => cntW w (next value) := by
  rw [cntW_bind, cntW_lift_prob, bind_map_left]
  simp only [zero_add, Prod.mk.eta, bind_pure]

theorem OnlyW.cntW {α : Type} (oa : OracleComp OracleWorld α) (h : OnlyW oa) : OnlyW (cntW w oa) := by
  induction oa using OracleComp.inductionOn with
  | pure value => exact OnlyW.pure' _
  | query_bind input next ih =>
      rw [OnlyW, isQueryBoundP_query_bind_iff] at h
      rw [cntW_query_bind, OnlyW, isQueryBoundP_query_bind_iff]
      refine ⟨h.1, fun answer => ?_⟩
      have hnext : OnlyW (next answer) := by
        have := h.2 answer
        split at this <;> simpa [OnlyW] using this
      have := OnlyW.bind (ih answer hnext) (fun result => OnlyW.pure' (result.1, weightOf w input + result.2))
      simpa [OnlyW] using this

/-- The weighted counted run of a game from the empty cache. -/
noncomputable def runW {α : Type} (game : OracleComp OracleWorld α) : ProbComp (α × ω) :=
  (simulateQ romImpl (cntW w game)).run' ∅

theorem runW_bind {α β : Type} (first : OracleComp OracleWorld α) (next : α → OracleComp OracleWorld β) :
    runW w (first >>= next) =
      (simulateQ romImpl (cntW w first)).run ∅ >>= fun result =>
        (fun rest => (rest.1, result.1.2 + rest.2)) <$>
          (simulateQ romImpl (cntW w (next result.1.1))).run' result.2 := by
  rw [runW, cntW_bind, simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  refine bind_congr fun result => ?_
  rw [simulateQ_bind, StateT.run_bind, StateT.run'_eq, map_bind, Functor.map_map]
  simp only [simulateQ_pure, StateT.run_pure, map_eq_bind_pure_comp]
  rfl

theorem run'_cntW_sampling_bind {α β : Type} (sampling : ProbComp α) (next : α → OracleComp OracleWorld β)
    (cache : QueryCache HashSpec) :
    (simulateQ romImpl (cntW w ((liftM sampling : OracleComp OracleWorld α) >>= next))).run' cache =
      sampling >>= fun value => (simulateQ romImpl (cntW w (next value))).run' cache := by
  rw [cntW_sampling_bind, simulateQ_bind, StateT.run'_eq, StateT.run_bind, run_lift_prob,
    bind_map_left, map_bind]
  rfl

theorem runW_sampling_bind {α β : Type} (sampling : ProbComp α) (next : α → OracleComp OracleWorld β) :
    runW w ((liftM sampling : OracleComp OracleWorld α) >>= next) =
      sampling >>= fun value => runW w (next value) :=
  run'_cntW_sampling_bind w sampling next ∅

/-- A private draw commutes with the hash calls before it. -/
theorem runW_swap {α β γ : Type} (first : OracleComp HashSpec α) (sampling : ProbComp β)
    (next : α → β → OracleComp OracleWorld γ) :
    runW w ((liftM first : OracleComp OracleWorld α) >>= fun a =>
        (liftM sampling : OracleComp OracleWorld β) >>= fun b => next a b) =ᵈ
      (sampling >>= fun b => runW w ((liftM first : OracleComp OracleWorld α) >>= fun a => next a b)) := by
  rw [runW_bind]
  simp only [run'_cntW_sampling_bind, map_bind]
  refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
  refine EvalDistEq.bind_right _ fun b => ?_
  rw [runW_bind]

/-- The weighted calls of a hash computation under fixed answers. -/
def callsW (answers : HashInput → HashOutput) {α : Type} (oa : OracleComp HashSpec α) : ω :=
  OracleComp.construct (C := fun _ => ω) (fun _ => 0) (fun input _ next => w input + next (answers input)) oa

theorem callsW_query_bind (answers : HashInput → HashOutput) {α : Type} (input : HashInput)
    (next : HashOutput → OracleComp HashSpec α) :
    callsW w answers (liftM (HashSpec.query input) >>= next) = w input + callsW w answers (next (answers input)) := rfl

theorem callsW_bind (answers : HashInput → HashOutput) {α β : Type} (oa : OracleComp HashSpec α)
    (f : α → OracleComp HashSpec β) :
    callsW w answers (oa >>= f) = callsW w answers oa + callsW w answers (f (valF answers oa)) := by
  induction oa using OracleComp.inductionOn with
  | pure value => simp [callsW, valF]
  | query_bind input next ih =>
      rw [bind_assoc, callsW_query_bind, callsW_query_bind, ih, valF_query_bind, add_assoc]

/-- Under fixed answers the weighted counted run of a hash computation is deterministic. -/
theorem fixedRec_run_cntW (answers : HashInput → HashOutput) {α : Type} (oa : OracleComp HashSpec α)
    (cache : QueryCache HashSpec) :
    (simulateQ (fixedRec answers) (cntW w (liftM oa : OracleComp OracleWorld α))).run cache =
      pure ((valF answers oa, callsW w answers oa), recF answers oa cache) := by
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure value => rfl
  | query_bind input next ih =>
      rw [liftM_bind]
      change (simulateQ (fixedRec answers) (cntW w
        (liftM (OracleWorld.query (.inr input)) >>= fun answer => liftM (next answer)))).run cache = _
      rw [cntW_query_bind]
      simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, fixedRec_inr_run,
        pure_bind, ih, StateT.run_pure]
      rfl

/-- The weighted counted lazy run of a short hash computation from the empty cache. -/
theorem evalDist_cntW_liftM {α : Type} (oa : OracleComp HashSpec α) (h : Short.Only oa) :
    (simulateQ romImpl (cntW w (liftM oa : OracleComp OracleWorld α))).run ∅ =ᵈ
      (do let table ← $ᵗ Table
          pure ((valF (extend ∅ table) oa, callsW w (extend ∅ table) oa), recF (extend ∅ table) oa ∅)) := by
  refine (evalDist_romImpl_run_eq_table (cntW w (liftM oa : OracleComp OracleWorld α))
    (OnlyW.cntW w _ (OnlyW.liftHash h)) ∅).trans ?_
  simp only [fixedRec_run_cntW]
  exact EvalDistEq.refl _

end Weighted

variable [Params] {n : ℕ}

/-! ### Key generation under fixed answers, weighted -/

section FixedW

variable {ω : Type} [AddCommMonoid ω] (w : HashInput → ω) (answers : HashInput → HashOutput)

/-- The weighted calls of a position: those of its key generation, none for a given key. -/
def callsAtW {k : ℕ} (seeds : Fin k → MasterSeed) (given : Fin k → Option PublicKey) (i : Fin k) : ω :=
  (given i).elim (callsW w answers (keygenOne (seeds i))) fun _ => 0

theorem callsW_keyFor (given : Option PublicKey) (seed : MasterSeed) :
    callsW w answers (keyFor given seed) = given.elim (callsW w answers (keygenOne seed)) fun _ => 0 := by
  cases given <;> rfl

theorem callsW_keygenSel : ∀ (k : ℕ) (seeds : Fin k → MasterSeed) (given : Fin k → Option PublicKey),
    callsW w answers (keygenSel k seeds given) = ∑ i, callsAtW w answers seeds given i
  | 0, _, _ => rfl
  | k + 1, seeds, given => by
      rw [keygenSel_succ, callsW_bind, callsW_bind, callsW_keygenSel k, Fin.sum_univ_castSucc, callsW_keyFor]
      simp [callsAtW, callsW]

theorem callsW_hashB (j : Fin n) (seed : MasterSeed) (others : Fin n → MasterSeed) :
    callsW w answers (hashB j seed others) = callsW w answers (keygenAll n (Function.update others j seed)) := by
  rw [keygenAll_eq, callsW_keygenSel, hashB, callsW_bind, callsW_bind, callsW_keygenSel,
    Fintype.sum_eq_add_sum_compl j, Fintype.sum_eq_add_sum_compl j (callsAtW w answers _ _)]
  have hrest : ∑ i ∈ ({j} : Finset (Fin n))ᶜ,
      callsAtW w answers others (givenAt j (valF answers (keygenOne seed)).1) i =
      ∑ i ∈ ({j} : Finset (Fin n))ᶜ, callsAtW w answers (Function.update others j seed) (fun _ => none) i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hij : i ≠ j := by simpa using hi
    simp [callsAtW, givenAt, hij]
  rw [hrest]
  simp [callsAtW, givenAt, callsW]

/-- **The reduction's hash calls before the adversary runs weigh as those of the multi-user
experiment.** -/
theorem evalDist_hashBW (j : Fin n) (seed : MasterSeed) (others : Fin n → MasterSeed) :
    (fun result => ((combine j result.1.1, result.1.2), result.2)) <$>
        (simulateQ romImpl (cntW w (liftM (hashB j seed others) : OracleComp OracleWorld _))).run ∅ =ᵈ
      (simulateQ romImpl (cntW w (liftM (keygenAll n (Function.update others j seed)) :
        OracleComp OracleWorld _))).run ∅ := by
  refine ((evalDist_cntW_liftM w _ (only_hashB j seed others)).map _).trans ?_
  refine EvalDistEq.trans ?_ (evalDist_cntW_liftM w _ (by
    rw [keygenAll_eq]
    exact only_keygenSel n _ _)).symm
  simp only [map_bind, map_pure, valF_hashB, callsW_hashB, recF_hashB]
  exact EvalDistEq.refl _

end FixedW

/-! ### The games returning the key's parameter -/

/-- The deterministic single-key game, also returning the public parameter of its key. -/
noncomputable def gameCoreDetP (adversary : Security.Adversary) : OracleComp OracleWorld (Bool × PublicParameter) := do
  let seed ← liftM sampleMasterSeed
  let (pk, sk) ← liftM (Seeded.keygenFromSeed seed)
  let ((forgery, log) : _root_.Sphincs.Forgery × QueryLog Sphincs.SigningSpec) ←
    (simulateQ (QueryImpl.ofLift OracleWorld
      (WriterT (QueryLog Sphincs.SigningSpec) (OracleComp OracleWorld)) + Det.signingOracleDet sk)
      (adversary.main pk)).run
  let verified ← liftM (Concrete.verify pk forgery.message forgery.signature : OracleComp HashSpec Bool)
  return (decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified, pk.parameter)

/-- The end of the multi-user game checking key `j`, also returning the parameter of key `j`. -/
noncomputable def restAtP (adversary : Adversary n) (j : Fin n) (keys : Fin n → PublicKey × Seeded.SecretKey) :
    OracleComp OracleWorld (Bool × PublicParameter) :=
  (fun won => (won, (keys j).1.parameter)) <$> restAt adversary j keys

/-- The multi-user game checking key `j`, also returning the parameter of key `j`. -/
noncomputable def gameAtP (adversary : Adversary n) (j : Fin n) : OracleComp OracleWorld (Bool × PublicParameter) := do
  let seeds ← liftM (sampleSeeds n)
  let keys ← liftM (keygenAll n seeds)
  restAtP adversary j keys

/-- The end of the reduction's game, also returning the parameter of the challenge key. -/
noncomputable def restBP (adversary : Adversary n) (j : Fin n) (key : PublicKey × Seeded.SecretKey)
    (keys : Fin n → PublicKey × Seeded.SecretKey) : OracleComp OracleWorld (Bool × PublicParameter) :=
  (fun won => (won, key.1.parameter)) <$> restB adversary j key keys

theorem restBP_eq (adversary : Adversary n) (j : Fin n) (key : PublicKey × Seeded.SecretKey)
    (keys : Fin n → PublicKey × Seeded.SecretKey) :
    restBP adversary j key keys = restAtP adversary j (combine j (key, keys)) := by
  rw [restBP, restAtP, restB_eq]
  simp [combine]

theorem gameCoreDetP_toSingle (adversary : Adversary n) (j : Fin n) :
    gameCoreDetP (toSingle adversary j) =
      (liftM sampleMasterSeed : OracleComp OracleWorld MasterSeed) >>= fun seed =>
        (liftM (keygenOne seed) : OracleComp OracleWorld _) >>= fun key =>
          (liftM (sampleSeeds n) : OracleComp OracleWorld _) >>= fun others =>
            (liftM (keygenSel n others (givenAt j key.1)) : OracleComp OracleWorld _) >>= fun keys =>
              restBP adversary j key keys := by
  unfold gameCoreDetP
  refine bind_congr fun seed => bind_congr fun key => ?_
  rcases key with ⟨pk, sk⟩
  change (simulateQ (Det.gameImplDet sk) ((toSingle adversary j).main pk)).run >>= _ = _
  simp only [toSingle, simulateQ_bind, WriterT.run_bind, Det.gameImplDet_liftWorld, bind_map_left, bind_assoc]
  refine bind_congr fun others => bind_congr fun keys => ?_
  simp only [restBP, restB, map_bind, map_pure]
  refine bind_congr fun result => ?_
  simp [List.empty_eq]

/-- **The reduction's game weighs as the multi-user game checking key `j`**, for any weight of the
hash calls, with the parameter of the challenge key. -/
theorem runW_toSingle {ω : Type} [AddCommMonoid ω] (w : HashInput → ω) (adversary : Adversary n) (j : Fin n) :
    runW w (gameCoreDetP (toSingle adversary j)) =ᵈ runW w (gameAtP adversary j) := by
  rw [gameCoreDetP_toSingle, runW_sampling_bind]
  refine (EvalDistEq.bind_right _ fun seed => runW_swap w _ _ _).trans ?_
  have hhash : ∀ (seed : MasterSeed) (others : Fin n → MasterSeed),
      runW w ((liftM (keygenOne seed) : OracleComp OracleWorld _) >>= fun key =>
          (liftM (keygenSel n others (givenAt j key.1)) : OracleComp OracleWorld _) >>= fun keys =>
            restBP adversary j key keys) =ᵈ
        runW w ((liftM (keygenAll n (Function.update others j seed)) : OracleComp OracleWorld _) >>=
          restAtP adversary j) := by
    intro seed others
    have hb : ((liftM (keygenOne seed) : OracleComp OracleWorld _) >>= fun key =>
          (liftM (keygenSel n others (givenAt j key.1)) : OracleComp OracleWorld _) >>= fun keys =>
            restBP adversary j key keys) =
        (liftM (hashB j seed others) : OracleComp OracleWorld _) >>= fun keys =>
          restAtP adversary j (combine j keys) := by
      simp only [hashB, liftM_bind, bind_assoc, liftM_pure, pure_bind, restBP_eq]
    rw [hb, runW_bind, runW_bind]
    have hmap := (evalDist_hashBW w j seed others).bind_left fun result =>
      (fun rest => (rest.1, result.1.2 + rest.2)) <$>
        (simulateQ romImpl (cntW w (restAtP adversary j result.1.1))).run' result.2
    rw [bind_map_left] at hmap
    exact hmap
  refine (EvalDistEq.bind_right _ fun seed => EvalDistEq.bind_right _ fun others => hhash seed others).trans ?_
  rw [gameAtP, runW_sampling_bind]
  let : SampleableType MasterSeed := SampleableType.ofFintype MasterSeed
  let : SampleableType (Fin n → MasterSeed) := SampleableType.ofFintype (Fin n → MasterSeed)
  have hupdate := (uniformSample_bind_update_evalDistEq (D := Fin n) (R := MasterSeed) j).bind_left
    fun seeds => runW w ((liftM (keygenAll n seeds) : OracleComp OracleWorld _) >>= restAtP adversary j)
  simp only [bind_assoc, pure_bind] at hupdate
  exact hupdate

end Sphincs.Security.Multi
