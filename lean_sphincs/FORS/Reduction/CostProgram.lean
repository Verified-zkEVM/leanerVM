import FORS.Reduction.InternalizeGame

/-! The graph-view cost program of the deterministic-randomizer game. The randomizer base
`R0` of a message is read from a table `rnd` of full hash outputs indexed by message; its one
derivation hash call is charged as a one-unit tick, so the cost program preserves the joint law of output and original
hash cost whenever `rnd` holds the answers at the seed's randomizer-derivation inputs. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.Det

variable [Params]

open Concrete Completeness Prefix HiddenGraph SeedCoupling GraphView

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Randomizer-base derivation outputs (`R0`), by message. -/
abbrev RTable := Message → HashOutput

/-- One half of every randomizer derivation output, by message: the base randomizers, or the step
halves. -/
abbrev LTable := Message → Randomness

/-- The hash output whose low half is `low` and whose high half is `high`. -/
def joinHalves (low high : Digest) : HashOutput :=
  BitVec.ofNat hashOutputBits (high.toNat * 2 ^ digestBits + low.toNat)

theorem joinHalves_toNat (low high : Digest) :
    (joinHalves low high).toNat = high.toNat * 2 ^ 128 + low.toNat := by
  have hl : low.toNat < 2 ^ 128 := low.isLt
  have hh : high.toNat < 2 ^ 128 := high.isLt
  rw [joinHalves, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by simp only [hashOutputBits, digestBits]; omega)

theorem truncateHash_joinHalves (low high : Digest) : truncateHash (joinHalves low high) = low := by
  apply BitVec.eq_of_toNat_eq
  rw [truncateHash, BitVec.extractLsb'_toNat, joinHalves_toNat, Nat.shiftRight_zero]
  show (high.toNat * 2 ^ 128 + low.toNat) % 2 ^ 128 = low.toNat
  have hl : low.toNat < 2 ^ 128 := low.isLt
  omega

theorem upperHash_joinHalves (low high : Digest) : upperHash (joinHalves low high) = high := by
  apply BitVec.eq_of_toNat_eq
  rw [upperHash, BitVec.extractLsb'_toNat, joinHalves_toNat, Nat.shiftRight_eq_div_pow]
  show (high.toNat * 2 ^ 128 + low.toNat) / 2 ^ 128 % 2 ^ 128 = high.toNat
  have hl : low.toNat < 2 ^ 128 := low.isLt
  have hh : high.toNat < 2 ^ 128 := high.isLt
  omega

theorem joinHalves_truncate (x : HashOutput) : joinHalves (truncateHash x) (upperHash x) = x := by
  apply BitVec.eq_of_toNat_eq
  rw [joinHalves_toNat, truncateHash, upperHash, BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat,
    Nat.shiftRight_zero, Nat.shiftRight_eq_div_pow]
  have hx : x.toNat < 2 ^ 256 := x.isLt
  show x.toNat / 2 ^ 128 % 2 ^ 128 * 2 ^ 128 + x.toNat % 2 ^ 128 = x.toNat
  omega

/-- The randomizer table with base randomizers `lows` and step halves `highs`. -/
def joinTable (lows highs : LTable) : RTable := fun message => joinHalves (lows message) (highs message)

theorem joinTable_bijective : Function.Bijective (fun pair : LTable × LTable => joinTable pair.1 pair.2) := by
  refine ⟨fun a b h => ?_, fun rnd => ⟨(fun m => truncateHash (rnd m), fun m => upperHash (rnd m)), ?_⟩⟩
  · have hl : ∀ m, a.1 m = b.1 m := fun m => by
      have := congrArg (fun t : RTable => truncateHash (t m)) h
      simpa only [joinTable, truncateHash_joinHalves] using this
    have hh : ∀ m, a.2 m = b.2 m := fun m => by
      have := congrArg (fun t : RTable => upperHash (t m)) h
      simpa only [joinTable, upperHash_joinHalves] using this
    exact Prod.ext (funext hl) (funext hh)
  · funext m
    exact joinHalves_truncate (rnd m)

theorem joinTable_update (lows highs : LTable) (message : Message) (low : Randomness) :
    joinTable (Function.update lows message low) highs =
      Function.update (joinTable lows highs) message (joinHalves low (highs message)) := by
  funext m
  by_cases h : m = message
  · subst h
    simp [joinTable]
  · simp [joinTable, Function.update_of_ne h]


/-- The deterministic signer in the graph view: charge the one derivation call of the randomizer
base and step, read them from the table, then scan. -/
noncomputable def signCostDet (parameter : PublicParameter) (data : PublicData) (rnd : RTable)
    (message : Message) : OracleComp CostSpec (Option Signature) := do
  HiddenCost.tick 1
  signCostSourceLoop parameter data message (walkStep (upperHash (rnd message))) digestAttemptLimit
    (truncateHash (rnd message))

noncomputable def costInteractionDet (parameter : PublicParameter) (data : PublicData) (rnd : RTable) :
    QueryImpl (OracleWorld + SigningSpec) (WriterT (QueryLog SigningSpec) (OracleComp CostSpec)) :=
  ordinaryCostSource.liftTarget (WriterT (QueryLog SigningSpec) (OracleComp CostSpec)) +
    QueryImpl.withLogging (spec := SigningSpec) (m := OracleComp CostSpec)
      (fun message => signCostDet parameter data rnd message)

noncomputable def costRestDet (parameter : PublicParameter) (data : PublicData) (rnd : RTable)
    (adversary : Adversary) : OracleComp CostSpec Bool := do
  let pk : PublicKey := ⟨data.root, parameter⟩
  let (forgery, log) ← (simulateQ (costInteractionDet parameter data rnd) (adversary.main pk)).run
  let verified ← liftM (Concrete.verify pk forgery.message forgery.signature : OracleComp HashSpec Bool)
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

noncomputable def costGameDet (parameter : PublicParameter) (data : PublicData) (rnd : RTable)
    (adversary : Adversary) : OracleComp CostSpec Bool := do
  HiddenCost.tick Prefix.keygenHashCost
  costRestDet parameter data rnd adversary

theorem eval_deriveRandomizer (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (message : Message) :
    evalWithAnswerFn f (deriveRandomizer parameter seed message : OracleComp HashSpec (Randomness × Randomness)) =
      (truncateHash (f (randomizerHashInput parameter seed message)),
        walkStep (upperHash (f (randomizerHashInput parameter seed message)))) := by
  simp only [deriveRandomizer, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rfl

/-- The crate's signer and its graph view have the same joint output and cost law, for a full or
layered key: the view's landing call and its FORS charge less one make the crate's digest calls and
its FORS instance built once. -/
theorem signCostDet_correct (hfull : subtreeHeight = totalHeight) (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter)
    (seed : MasterSeed) (data : PublicData) (table : HiddenGraph.Table)
    (hdata : DataCorrect f parameter seed data) (htable : CoordinatesCorrect f parameter seed table)
    (rnd : RTable) (hrnd : ∀ message, f (randomizerHashInput parameter seed message) = rnd message)
    (message : Message) :
    simulateQ (fixedCostSource f table) (signCostDet parameter data rnd message) =
      simulateQ (fixedWorldCost f) (liftM (Seeded.sign ⟨seed, parameter, data.root⟩ message :
        OracleComp HashSpec (Option Signature)) : OracleComp OracleWorld (Option Signature)) := by
  set sk : Seeded.SecretKey := ⟨seed, parameter, data.root⟩ with hsk
  set randomness := truncateHash (rnd message) with hrandomness
  have hwalk : (evalWithAnswerFn f (deriveRandomizer parameter seed message :
      OracleComp HashSpec (Randomness × Randomness))).1 = randomness := by
    rw [eval_deriveRandomizer, hrnd]
  have hland : ∀ first : HashOutput, Landed parameter (blockIndex first) :=
    fun _ => landed_of_full hfull _ _
  have hlimit : digestAttemptLimit = (digestAttemptLimit - 1) + 1 := by
    unfold digestAttemptLimit; decide
  rw [fixedWorldCost_lift_hash, signCostDet, simulateQ_bind, fixedCostSource_tick, hlimit,
    signCostSourceLoop, simulateQ_bind, fixedCostSource_lift_hash, fixedWorldCost_lift_hash]
  simp only [hland, ↓reduceIte, fixed_finishCostSource]
  rw [eval_sign_eq_finishSign f sk hfull, hwalk,
    eval_finishSign_assembled f parameter seed data table hdata htable message randomness
      (landed_of_full hfull _ _), hashCalls_sign f sk hfull, hwalk]
  apply WriterT.ext
  simp only [WriterT.run_bind, WriterT.run_mk, AddWriterT.run_addTell, ← PMF.monad_pure_eq_pure,
    pure_bind, map_pure, ← ofAdd_add, hashCalls_messageDigestCall]
  congr 3
  -- the costs: the view's `1 + 1 + digest + (FORS - 1) + layers` is the crate's
  have hfors : 1 ≤ forsKeyCost := by
    have hk := Params.forsTrees_pos
    have ha := Params.forsHeight_ge
    unfold forsKeyCost
    have : 1 ≤ 5 * 2 ^ (forsHeight - 2) - 1 := by
      have := Nat.one_le_two_pow (n := forsHeight - 2); omega
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hlayers : seqCost (fun i : Fin numLayers => layerFound f parameter data
        (digestIndex (evalWithAnswerFn f (messageDigest parameter data.root message randomness :
          OracleComp HashSpec MessageDigest))) i.rev)
      (fun i => layerHashCostUp f parameter data (digestIndex (evalWithAnswerFn f
        (messageDigest parameter data.root message randomness : OracleComp HashSpec MessageDigest))) i.rev) =
      seqCost (fun i : Fin numLayers => layerFoundUp f sk (digestIndex (evalWithAnswerFn f
        (messageDigest sk.parameter sk.root message randomness : OracleComp HashSpec MessageDigest)))
          (Seeded.layerFromBottom i.val))
        (fun i => layerCostUp f sk (digestIndex (evalWithAnswerFn f
          (messageDigest sk.parameter sk.root message randomness : OracleComp HashSpec MessageDigest)))
            (Seeded.layerFromBottom i.val)) := by
    have hrev : ∀ i : Fin numLayers, i.rev = Seeded.layerFromBottom i.val := fun i => by
      apply Fin.ext; simp only [Fin.val_rev, Seeded.layerFromBottom]; omega
    have hmsg : ∀ (index : Index) (lay : Layer),
        data.keyMessage lay (treeIndexAt index lay) (leafIndexAt index lay) =
          layerMessageValue f sk index lay := fun index lay =>
      hdata.keyMessage lay _ _ ⟨index, landed_of_full hfull _ _, rfl, rfl⟩
    simp only [hrev, layerFound, layerFoundUp, layerHashCostUp, layerCostUp, layerSearch, hmsg, hsk]
  rw [← hrandomness]
  unfold finishHashCostUp
  dsimp only
  rw [hlayers]
  omega

theorem fixedCostSource_interactionDet (hfull : subtreeHeight = totalHeight) (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (data : PublicData) (table : HiddenGraph.Table)
    (hdata : DataCorrect f parameter seed data) (htable : CoordinatesCorrect f parameter seed table)
    (rnd : RTable) (hrnd : ∀ message, f (randomizerHashInput parameter seed message) = rnd message) :
    (fixedCostSource f table).writerTMapBase (costInteractionDet parameter data rnd) =
      (fixedWorldCost f).writerTMapBase
        (QueryImpl.ofLift OracleWorld
          (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) +
          signingOracle ⟨seed, parameter, data.root⟩) := by
  funext request
  cases request with
  | inl request =>
      change ((fixedCostSource f table).writerTMapBase
        (ordinaryCostSource.liftTarget (WriterT (QueryLog SigningSpec) (OracleComp CostSpec)))) request = _
      rw [map_lift_query, fixedCostSource_ordinary]
      apply WriterT.ext
      change (fun value => (value, (∅ : QueryLog SigningSpec))) <$> fixedWorldCost f request =
        simulateQ (fixedWorldCost f) ((fun value => (value, (∅ : QueryLog SigningSpec))) <$>
          (liftM (OracleWorld.query request) : OracleComp OracleWorld _))
      rw [simulateQ_map, simulateQ_spec_query]
  | inr message =>
      change ((fixedCostSource f table).writerTMapBase
        (QueryImpl.withLogging (spec := SigningSpec) (m := OracleComp CostSpec)
          (fun message => signCostDet parameter data rnd message))) message =
        ((fixedWorldCost f).writerTMapBase (signingOracle ⟨seed, parameter, data.root⟩)) message
      rw [signingOracle, map_logging_query, map_logging_query]
      have hsign : (fun message => simulateQ (fixedCostSource f table)
          (signCostDet parameter data rnd message)) =
          (fun message => simulateQ (fixedWorldCost f)
            (liftM (Seeded.sign ⟨seed, parameter, data.root⟩ message :
              OracleComp HashSpec (Option Signature)) : OracleComp OracleWorld (Option Signature))) := by
        funext message
        exact signCostDet_correct hfull f parameter seed data table hdata htable rnd hrnd message
      exact congrArg (fun impl : QueryImpl SigningSpec (AddWriterT Nat PMF) =>
        impl.withLogging message) hsign

theorem fixedCostSource_restDet (hfull : subtreeHeight = totalHeight) (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (data : PublicData) (table : HiddenGraph.Table)
    (hdata : DataCorrect f parameter seed data) (htable : CoordinatesCorrect f parameter seed table)
    (rnd : RTable) (hrnd : ∀ message, f (randomizerHashInput parameter seed message) = rnd message)
    (adversary : Adversary) :
    simulateQ (fixedCostSource f table) (costRestDet parameter data rnd adversary) =
      simulateQ (fixedWorldCost f) (do
        let pk : PublicKey := ⟨data.root, parameter⟩
        let (forgery, log) ← (simulateQ (QueryImpl.ofLift OracleWorld
          (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) +
          signingOracle ⟨seed, parameter, data.root⟩) (adversary.main pk)).run
        let verified ← liftM (Concrete.verify pk forgery.message forgery.signature : OracleComp HashSpec Bool)
        return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified) := by
  simp only [costRestDet, simulateQ_bind, simulateQ_pure, QueryImpl.simulateQ_writerTMapBase_run,
    fixedCostSource_interactionDet hfull f parameter seed data table hdata htable rnd hrnd, fixedCostSource_lift_hash]

/-- Fixed-oracle equality for the complete deterministic game, with its original hash budget. -/
theorem costGameDet_correct (hfull : subtreeHeight = totalHeight) (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (data : PublicData) (table : HiddenGraph.Table)
    (hdata : DataCorrect f parameter seed data) (htable : CoordinatesCorrect f parameter seed table)
    (hparameter : evalWithAnswerFn f (deriveKey 0 .parameter seed : OracleComp HashSpec Digest) = parameter)
    (rnd : RTable) (hrnd : ∀ message, f (randomizerHashInput parameter seed message) = rnd message)
    (adversary : Adversary) :
    simulateQ (fixedCostSource f table) (costGameDet parameter data rnd adversary) =
      simulateQ (fixedWorldCost f) (gameAfterSeedDet adversary seed) := by
  simp only [costGameDet, gameAfterSeedDet, simulateQ_bind, fixedCostSource_tick]
  rw [fixedWorldCost_keygen_graph f parameter seed data hdata hparameter]
  apply WriterT.ext
  simp only [WriterT.run_bind, WriterT.run_mk, AddWriterT.run_addTell,
    ← PMF.monad_pure_eq_pure, pure_bind]
  rw [fixedCostSource_restDet hfull f parameter seed data table hdata htable rnd hrnd]
  simp only [simulateQ_bind, WriterT.run_bind]

end FORS.Security.Det
