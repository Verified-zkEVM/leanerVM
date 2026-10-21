import LeanXmss.MultiUserStatement
import XmssSecurity.Proof.MultiUser.Trace
import XmssSecurity.Proof.Bridge.Reduction

/-!
# One reduction per key

Against key `j`, the single-key adversary `reduction adversary j` receives the key's public key,
generates the other keys itself through the oracle, answers their signing requests with their secret
keys, forwards the requests to key `j` to its own signing oracle, and outputs the forgery
(`reduction`). Its signing log is the multi-user log's requests to key `j` (`run_reduction`), so its
game is the multi-user game with key `j` generated first and the forgery verified under key `j`;
key generations commute (`romRun_sequenceFin_front`), so its game is the multi-user game verified
under key `j` (`forgeAdvantage_reduction`). A multi-user win names some key: its probability is at
most the sum of the per-key games' (`forgeAdvantage_le_sum`).
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.MultiUser

set_option backward.isDefEq.respectTransparency false

local notation "World" => LeanXmss.OracleWorld

/-- A key pair. -/
abbrev KeyPair := LeanXmss.PublicKey × LeanXmss.Seeded.SecretKey

/-- The secret key the reduction places in the position of the key under attack; never used. -/
def dummySecretKey : LeanXmss.Seeded.SecretKey := ⟨0, 0, 0⟩

/-! ## A writer simulation through a filter of its log -/

theorem simulateQ_writer_filterMap {ι : Type} {source : OracleSpec ι} {target : OracleSpec κ}
    {α L L' : Type}
    (left : QueryImpl source (WriterT (List L) (OracleComp target)))
    (right : QueryImpl source (WriterT (List L') (OracleComp target))) (g : L' → Option L)
    (h : ∀ input, (left input).run = (fun p => (p.1, p.2.filterMap g)) <$> (right input).run)
    (computation : OracleComp source α) :
    (simulateQ left computation).run =
      (fun p => (p.1, p.2.filterMap g)) <$> (simulateQ right computation).run := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      simp only [simulateQ_pure, WriterT.run_pure', map_pure]
      rfl
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, WriterT.run_bind', map_bind]
      show ((left input).run >>= fun x => Prod.map id (x.2 ++ ·) <$> (simulateQ left (next x.1)).run) =
        (right input).run >>= fun a => (fun p => (p.1, p.2.filterMap g)) <$>
          (Prod.map id (a.2 ++ ·) <$> (simulateQ right (next a.1)).run)
      rw [h input, bind_map_left]
      refine bind_congr fun a => ?_
      rw [ih, Functor.map_map, Functor.map_map]
      congr 1
      funext p
      simp [List.filterMap_append]

theorem run_simulateQ_ofLift_writer {α L : Type} (computation : OracleComp World α) :
    (simulateQ (QueryImpl.ofLift World (WriterT (List L) (OracleComp World)))
      computation).run = (fun a => (a, ([] : List L))) <$> computation := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      simp only [simulateQ_pure, WriterT.run_pure', map_pure]
      rfl
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, WriterT.run_bind', QueryImpl.ofLift_apply, ih, map_bind]
      change ((fun a => (a, ([] : List L))) <$> (liftM (LeanXmss.OracleWorld.query input) :
        OracleComp World _)) >>= _ = _
      simp only [Functor.map_map]
      rfl

/-! ## The multi-user game's parts -/

variable {n : Nat}

/-- The adversary with every key's signing oracle. -/
noncomputable def body (adversary : LeanXmss.MultiUser.Adversary n) (keys : Fin n → KeyPair) :
    OracleComp World (LeanXmss.MultiUser.Forgery n × QueryLog (LeanXmss.MultiUser.SigningSpec n)) :=
  (simulateQ (QueryImpl.ofLift World
      (WriterT (QueryLog (LeanXmss.MultiUser.SigningSpec n)) (OracleComp World)) +
    LeanXmss.MultiUser.signingOracle (fun key => (keys key).2))
    (adversary.main fun key => (keys key).1)).run

/-- Verify the forgery under `publicKey`, judging it against the requests to key `j`. -/
noncomputable def finish (publicKey : LeanXmss.PublicKey) (j : Fin n)
    (result : LeanXmss.MultiUser.Forgery n × QueryLog (LeanXmss.MultiUser.SigningSpec n)) :
    OracleComp World Bool := do
  let verified ← liftM (LeanXmss.Concrete.verify publicKey result.1.forgery.message
    result.1.forgery.signature : OracleComp LeanXmss.HashSpec Bool)
  return decide (LeanXmss.SigningTranscript.Valid (LeanXmss.MultiUser.keyLog result.2 j) ∧
    ¬LeanXmss.SigningTranscript.Contains (LeanXmss.MultiUser.keyLog result.2 j) result.1.forgery) &&
      verified

/-- The keys, then the adversary. -/
noncomputable def prefixRun (adversary : LeanXmss.MultiUser.Adversary n) :
    OracleComp World ((Fin n → KeyPair) ×
      (LeanXmss.MultiUser.Forgery n × QueryLog (LeanXmss.MultiUser.SigningSpec n))) :=
  LeanXmss.Concrete.sequenceFin (fun _ : Fin n => LeanXmss.MultiUser.keygen) >>= fun keys =>
    (fun result => (keys, result)) <$> body adversary keys

/-- The multi-user game with the forgery verified under key `j`. -/
noncomputable def gameAt (adversary : LeanXmss.MultiUser.Adversary n) (j : Fin n) :
    OracleComp World Bool :=
  LeanXmss.Concrete.sequenceFin (fun _ : Fin n => LeanXmss.MultiUser.keygen) >>= fun keys =>
    body adversary keys >>= finish (keys j).1 j

theorem gameCore_eq_prefixRun (adversary : LeanXmss.MultiUser.Adversary n) :
    LeanXmss.MultiUser.gameCore adversary = prefixRun adversary >>= fun p =>
      finish (p.1 p.2.1.key).1 p.2.1.key p.2 := by
  simp only [prefixRun, bind_assoc, bind_map_left]
  rfl

theorem gameAt_eq_prefixRun (adversary : LeanXmss.MultiUser.Adversary n) (j : Fin n) :
    gameAt adversary j = prefixRun adversary >>= fun p => finish (p.1 j).1 j p.2 := by
  simp only [prefixRun, gameAt, bind_assoc, bind_map_left]

/-- **A multi-user win names some key.** -/
theorem gameCore_le_sum (adversary : LeanXmss.MultiUser.Adversary n) :
    Pr{let x ← (simulateQ romImpl (LeanXmss.MultiUser.gameCore adversary : OracleComp OracleWorld Bool)).run' ∅}[x = true] ≤
      ∑ j, Pr{let x ← (simulateQ romImpl (gameAt adversary j : OracleComp OracleWorld Bool)).run' ∅}[x = true] := by
  have hrun : ∀ (game : OracleComp OracleWorld Bool),
      Pr{let x ← (simulateQ romImpl game).run' ∅}[x = true] =
        Pr{let x ← romRun game ∅}[x.1 = true] := fun game => by
    rw [StateT.run'_eq, prEvent_map]
  simp only [hrun, gameCore_eq_prefixRun, gameAt_eq_prefixRun, romRun_bind,
    OracleComp.prEvent_bind_eq_tsum]
  rw [← Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
  refine ENNReal.tsum_le_tsum fun r => ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul' le_rfl ?_
  exact Finset.single_le_sum (f := fun j => Pr{let x ← romRun (finish (r.1.1 j).1 j r.1.2) r.2}[x.1 = true])
    (fun _ _ => zero_le) (Finset.mem_univ r.1.2.1.key)

/-! ## The reduction -/

/-- A world query, as a query of the single-key adversary's world. -/
noncomputable def worldToSum : QueryImpl World (OracleComp (World + LeanXmss.SigningSpec)) :=
  fun input => liftM ((World + LeanXmss.SigningSpec).query (.inl input))

/-- Forward hash calls; answer requests to key `j` with the own signing oracle and the others with
their secret keys. -/
noncomputable def reductionImpl (j : Fin n) (others : Fin n → LeanXmss.Seeded.SecretKey) :
    QueryImpl (World + LeanXmss.MultiUser.SigningSpec n)
      (OracleComp (World + LeanXmss.SigningSpec)) :=
  worldToSum + fun (request : LeanXmss.MultiUser.SignRequest n) =>
    if request.key = j then
      (liftM ((World + LeanXmss.SigningSpec).query (.inr request.request)) :
        OracleComp (World + LeanXmss.SigningSpec) _)
    else
      simulateQ worldToSum (liftM (LeanXmss.Seeded.sign (others request.key) request.request.leafIndex
        request.request.message : OracleComp LeanXmss.HashSpec _) : OracleComp World _)

/-- **The reduction against key `j`.** -/
noncomputable def reduction (adversary : LeanXmss.MultiUser.Adversary n) (j : Fin n) :
    LeanXmss.Security.Adversary where
  main publicKey := do
    let keys ← simulateQ worldToSum (LeanXmss.Concrete.sequenceFin fun i : Fin n =>
        if i = j then pure (publicKey, dummySecretKey) else LeanXmss.MultiUser.keygen)
    let forgery ← simulateQ (reductionImpl j fun i => (keys i).2)
      (adversary.main fun i => if i = j then publicKey else (keys i).1)
    return forgery.forgery

theorem compose_worldToSum (secretKey : LeanXmss.Seeded.SecretKey) :
    (QueryImpl.ofLift World (WriterT (QueryLog LeanXmss.SigningSpec) (OracleComp World)) +
        LeanXmss.Security.signingOracle secretKey) ∘ₛ worldToSum =
      QueryImpl.ofLift World (WriterT (QueryLog LeanXmss.SigningSpec) (OracleComp World)) := by
  funext input
  rw [QueryImpl.apply_compose, worldToSum, simulateQ_spec_query, QueryImpl.add_apply_inl]

theorem run_simulate_worldToSum (secretKey : LeanXmss.Seeded.SecretKey) {α : Type}
    (computation : OracleComp World α) :
    (simulateQ (QueryImpl.ofLift World (WriterT (QueryLog LeanXmss.SigningSpec) (OracleComp World)) +
        LeanXmss.Security.signingOracle secretKey) (simulateQ worldToSum computation)).run =
      (fun a => (a, [])) <$> computation := by
  rw [← QueryImpl.simulateQ_compose, compose_worldToSum, run_simulateQ_ofLift_writer]

/-- The reduction's signing oracle in the single-key game: every request to key `j` is answered
by the own oracle and logged; the multi-user log, filtered to key `j`, is the same. -/
theorem simulate_reductionImpl (j : Fin n) (others : Fin n → LeanXmss.Seeded.SecretKey)
    (secretKey : LeanXmss.Seeded.SecretKey) {α : Type}
    (computation : OracleComp (World + LeanXmss.MultiUser.SigningSpec n) α) :
    (simulateQ (QueryImpl.ofLift World (WriterT (QueryLog LeanXmss.SigningSpec) (OracleComp World)) +
        LeanXmss.Security.signingOracle secretKey)
      (simulateQ (reductionImpl j others) computation)).run =
      (fun r => (r.1, LeanXmss.MultiUser.keyLog r.2 j)) <$>
        (simulateQ (QueryImpl.ofLift World
            (WriterT (QueryLog (LeanXmss.MultiUser.SigningSpec n)) (OracleComp World)) +
          LeanXmss.MultiUser.signingOracle (fun i => if i = j then secretKey else others i))
          computation).run := by
  rw [← QueryImpl.simulateQ_compose]
  refine simulateQ_writer_filterMap _ _ _ (fun input => ?_) computation
  rcases input with input | request
  · change (simulateQ (QueryImpl.ofLift World (WriterT (QueryLog LeanXmss.SigningSpec) (OracleComp World)) +
        LeanXmss.Security.signingOracle secretKey)
        (liftM ((World + LeanXmss.SigningSpec).query (.inl input)))).run = _
    rw [simulateQ_spec_query, QueryImpl.add_apply_inl]
    simp only [QueryImpl.add_apply_inl, QueryImpl.ofLift_apply]
    change (fun a => (a, ([] : QueryLog LeanXmss.SigningSpec))) <$>
        (liftM (LeanXmss.OracleWorld.query input) : OracleComp World _) =
      _ <$> ((fun a => (a, ([] : QueryLog (LeanXmss.MultiUser.SigningSpec n)))) <$>
        (liftM (LeanXmss.OracleWorld.query input) : OracleComp World _))
    rw [Functor.map_map]
    rfl
  · change (simulateQ (QueryImpl.ofLift World (WriterT (QueryLog LeanXmss.SigningSpec) (OracleComp World)) +
        LeanXmss.Security.signingOracle secretKey) (if request.key = j then
          (liftM ((World + LeanXmss.SigningSpec).query (.inr request.request)) :
            OracleComp (World + LeanXmss.SigningSpec) _)
        else
          simulateQ worldToSum (liftM (LeanXmss.Seeded.sign (others request.key) request.request.leafIndex
            request.request.message : OracleComp LeanXmss.HashSpec _) : OracleComp World _))).run = _
    by_cases hkey : request.key = j
    · simp only [hkey, ↓reduceIte, simulateQ_spec_query, QueryImpl.add_apply_inr,
        LeanXmss.Security.signingOracle, LeanXmss.MultiUser.signingOracle,
        QueryImpl.run_withLogging_apply, map_bind, map_pure, List.filterMap_cons, List.filterMap_nil]
    · simp only [hkey, ↓reduceIte, run_simulate_worldToSum,
        QueryImpl.add_apply_inr, LeanXmss.MultiUser.signingOracle,
        QueryImpl.run_withLogging_apply, map_bind, map_pure, List.filterMap_cons, List.filterMap_nil]
      rw [map_eq_bind_pure_comp]
      rfl

/-- **The reduction's run**: the other keys, then the multi-user adversary with every key's signing
oracle, key `j`'s requests forming the log. -/
theorem run_reduction (adversary : LeanXmss.MultiUser.Adversary n) (j : Fin n)
    (publicKey : LeanXmss.PublicKey) (secretKey : LeanXmss.Seeded.SecretKey) :
    (simulateQ (QueryImpl.ofLift World (WriterT (QueryLog LeanXmss.SigningSpec) (OracleComp World)) +
        LeanXmss.Security.signingOracle secretKey) ((reduction adversary j).main publicKey)).run =
      LeanXmss.Concrete.sequenceFin (fun i : Fin n =>
          if i = j then pure (publicKey, dummySecretKey) else LeanXmss.MultiUser.keygen) >>= fun keys =>
        (fun r => (r.1.forgery, LeanXmss.MultiUser.keyLog r.2 j)) <$>
          body adversary (fun i => if i = j then (publicKey, secretKey) else keys i) := by
  simp only [reduction, simulateQ_bind, simulateQ_pure, WriterT.run_bind', run_simulate_worldToSum,
    bind_map_left, simulate_reductionImpl]
  refine bind_congr fun keys => ?_
  have hpk : (fun i => if i = j then publicKey else (keys i).1) =
      fun i => (if i = j then (publicKey, secretKey) else keys i).1 := by
    funext i; split <;> rfl
  have hsk : (fun i => if i = j then secretKey else (keys i).2) =
      fun i => (if i = j then (publicKey, secretKey) else keys i).2 := by
    funext i; split <;> rfl
  rw [hpk, hsk, body]
  simp only [WriterT.run_pure', map_pure, map_bind, List.nil_append]
  rw [map_eq_bind_pure_comp]
  refine bind_congr fun r => ?_
  simp [Prod.map]

/-- The single-key game after key generation, for the reduction against key `j` with key `j`'s
pair `keys`. -/
noncomputable def restAt (adversary : LeanXmss.MultiUser.Adversary n) (j : Fin n) (key : KeyPair) :
    OracleComp World Bool :=
  LeanXmss.Concrete.sequenceFin (fun i : Fin n => if i = j then pure key else LeanXmss.MultiUser.keygen) >>=
    fun keys => body adversary keys >>= finish key.1 j

theorem gameRest_reduction (adversary : LeanXmss.MultiUser.Adversary n) (j : Fin n) (key : KeyPair) :
    LeanXmss.Security.gameRest (reduction adversary j) key.1 key.2 = restAt adversary j key := by
  unfold LeanXmss.Security.gameRest restAt
  rw [run_reduction, ← sequenceFin_slot j (key.1, dummySecretKey) key (fun _ => LeanXmss.MultiUser.keygen)]
  simp only [bind_assoc, bind_map_left]
  rfl

theorem gameCore_reduction (adversary : LeanXmss.MultiUser.Adversary n) (j : Fin n) :
    LeanXmss.Security.gameCore (reduction adversary j) =
      LeanXmss.MultiUser.keygen >>= restAt adversary j := by
  rw [Bridge.gameCore_eq]
  simp only [LeanXmss.MultiUser.keygen, bind_assoc]
  refine bind_congr fun seed => bind_congr fun key => ?_
  exact gameRest_reduction adversary j key

/-- **The reduction against key `j` wins the single-key game as often as the multi-user game
verified under key `j` is won.** -/
theorem forgeAdvantage_reduction (adversary : LeanXmss.MultiUser.Adversary n) (j : Fin n) :
    LeanXmss.Security.forgeAdvantage (reduction adversary j) =
      Pr{let x ← (simulateQ romImpl (gameAt adversary j : OracleComp OracleWorld Bool)).run' ∅}[x = true] := by
  have hadv : LeanXmss.Security.forgeAdvantage (reduction adversary j) =
      Pr{let x ← (simulateQ romImpl (LeanXmss.Security.gameCore (reduction adversary j) :
        OracleComp OracleWorld Bool)).run' ∅}[x = true] := by
    unfold LeanXmss.Security.forgeAdvantage LeanXmss.Security.experiment
    rw [← Bridge.probOutput_countHashQueries, simulateQ_countHashQueries]
    rfl
  have hfront := romRun_sequenceFin_front n (fun _ => (LeanXmss.MultiUser.keygen : OracleComp OracleWorld _)) j
    (fun key keys => (body adversary keys >>= finish key.1 j : OracleComp OracleWorld Bool)) ∅
  rw [hadv, gameCore_reduction, StateT.run'_eq, StateT.run'_eq, prEvent_map, prEvent_map]
  exact hfront.prEvent_eq _

end XmssSecurity.MultiUser
