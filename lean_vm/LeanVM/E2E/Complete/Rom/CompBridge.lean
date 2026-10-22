/-
  LeanVM.E2E.Complete.Rom.CompBridge

  T6-prob: the honest prover of the random-oracle model, its queries answered by a hash function,
  is the H-oblivious prover `honestOutN` at that hash.
-/

module

public import LeanVM.E2E.Complete.Rom.Comp

/-!
# The bridge: the oracle prover at a fixed hash

`docs/roadmap/t6-prob.md` §3, §4.4. Interpreting the queries of `honestProverComp` by any
implementation `impl` is running `honestProverM` with `impl` as the hash
(`simulateQ_honestProverM`), piece by piece as `simulateQ_proveM` (`Compile/Rom/Prover.lean`):
the seed, the digests, the children's claims, the batching, the node's log, the Fiat–Shamir run.
At `Id` with a hash function `H` the monadic prover is `honestOutN H` (`honestProverM_id`, from
the pieces' `…_id` lemmas, `MonadicM.lean`), so the oracle prover answered by `H` is
`honestOutN H` (`honestProverComp_at`); and a run answered by a log's answers returns what
`honestOutN` returns at every hash agreeing with the log (`honestProverComp_look`).
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Node LeanVM.Guest
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd LeanVM.Protocol.Whir.Complete
open LeanVM.Protocol.Compile.Rom LeanVM.E2E OracleComp

@[expose] public section

/-! ## Simulation commutes with the prover's pieces -/

section Commute

variable {r : Type → Type} [Monad r] [LawfulMonad r] (impl : QueryImpl HashSpec r) (ρ pfuel : ℕ)

/-- Simulation is closed under `bind`, as a relation. -/
theorem simulateQ_rel_bind {α β : Type} (x : OracleComp HashSpec α) (y : r α)
    (f : α → OracleComp HashSpec β) (g : α → r β) (hx : simulateQ impl x = y)
    (hf : ∀ a, simulateQ impl (f a) = g a) : simulateQ impl (x >>= f) = y >>= g := by
  rw [simulateQ_bind, hx]
  exact congrArg _ (funext hf)

theorem simulateQ_seedWith (bytecode : List K) (pd : Digest) :
    simulateQ impl (seedWith queryH bytecode pd) = seedWith (fun x ↦ impl x) bytecode pd := by
  simp only [seedWith, simulateQ_bind, simulateQ_queryH]

theorem simulateQ_seedOfM : simulateQ impl (seedOfM queryH) = seedOfM (fun x ↦ impl x) :=
  rel_fiatShamirIvWith (fun {α : Type} (x : OracleComp HashSpec α) (y : r α) ↦ simulateQ impl x = y)
    (simulateQ_rel_bind impl) queryH _ (simulateQ_queryH impl) End.bytecode

theorem simulateQ_digestOfM (s : NodeStatement) :
    simulateQ impl (digestOfM queryH s) = digestOfM (fun x ↦ impl x) s :=
  simulateQ_rel_bind impl _ _ _ _ (simulateQ_seedOfM impl) fun seed ↦
    rel_statementDigestWith
      (fun {α : Type} (x : OracleComp HashSpec α) (y : r α) ↦ simulateQ impl x = y)
      (simulateQ_rel_bind impl) queryH _ (simulateQ_queryH impl) seed s

theorem simulateQ_claimsOfM (cs : List Child) :
    simulateQ impl (claimsOfM queryH cs) = claimsOfM (fun x ↦ impl x) cs :=
  rel_mapM (fun {α : Type} (x : OracleComp HashSpec α) (y : r α) ↦ simulateQ impl x = y)
    (fun a ↦ simulateQ_pure impl a) (simulateQ_rel_bind impl) _ _
    (fun _ ↦ simulateQ_rel_bind impl _ _ _ _ (simulateQ_digestOfM impl _) fun _ ↦
      simulateQ_pure impl _) cs

theorem simulateQ_batchWith (s0 : Digest) (cs : List ChildClaims) (h : BatchHints) :
    simulateQ impl (batchWith queryH s0 cs h) = batchWith (fun x ↦ impl x) s0 cs h :=
  rel_batchWith (fun {α : Type} (x : OracleComp HashSpec α) (y : r α) ↦ simulateQ impl x = y)
    (fun a ↦ simulateQ_pure impl a) (simulateQ_rel_bind impl) queryH _ (simulateQ_queryH impl)
    s0 cs h

/-! ### The batching -/

theorem simulateQ_obsAllHM : ∀ (cv : Digest) (xs : List E),
    simulateQ impl (obsAllHM queryH cv xs) = obsAllHM (fun x ↦ impl x) cv xs
  | cv, [] => by simp [obsAllHM]
  | cv, x :: xs => by
    simp only [obsAllHM, List.foldlM_cons, simulateQ_bind, simulateQ_queryH]
    exact congrArg _ (funext fun cv' ↦ simulateQ_obsAllHM cv' xs)

theorem simulateQ_sq2HM : ∀ (n : ℕ) (cv : Digest),
    simulateQ impl (sq2HM queryH n cv) = sq2HM (fun x ↦ impl x) n cv
  | 0, _ => by simp [sq2HM]
  | n + 1, cv => by
    simp only [sq2HM, simulateQ_bind, simulateQ_queryH, simulateQ_pure, simulateQ_sq2HM n]

theorem simulateQ_sq3HM : ∀ (n : ℕ) (cv : Digest),
    simulateQ impl (sq3HM queryH n cv) = sq3HM (fun x ↦ impl x) n cv
  | 0, _ => by simp [sq3HM]
  | n + 1, cv => by
    simp only [sq3HM, simulateQ_bind, simulateQ_queryH, simulateQ_pure, simulateQ_sq3HM n]

theorem simulateQ_roundCvM (cv : Digest) (msg : E × E) :
    simulateQ impl (roundCvM queryH cv msg) = roundCvM (fun x ↦ impl x) cv msg := by
  simp only [roundCvM, simulateQ_bind, simulateQ_queryH]

theorem simulateQ_honestRoundsM (n : ℕ) (f : List E → E) : ∀ (k : ℕ) (pre : List E) (cv : Digest),
    simulateQ impl (honestRoundsM queryH n f k pre cv) = honestRoundsM (fun x ↦ impl x) n f k pre cv
  | 0, _, _ => by simp [honestRoundsM]
  | k + 1, pre, cv => by
    simp only [honestRoundsM, simulateQ_bind, simulateQ_roundCvM, simulateQ_pure,
      simulateQ_honestRoundsM n f k]

theorem simulateQ_batchRoundsWith_run (claim : E) (rounds : List (E × E)) (cv : Digest) :
    simulateQ impl ((batchRoundsWith queryH claim rounds).run cv) =
      (batchRoundsWith (fun x ↦ impl x) claim rounds).run cv :=
  relS_batchRoundsWith
    (fun {α : Type} (x : OracleComp HashSpec α) (y : r α) ↦ simulateQ impl x = y)
    (fun a ↦ simulateQ_pure impl a) (simulateQ_rel_bind impl) queryH _ (simulateQ_queryH impl)
    claim rounds cv

theorem simulateQ_honestBatchM (s0 : Digest) (bytecode : List K) (cs : List ChildClaims) :
    simulateQ impl (honestBatchM queryH s0 bytecode cs) =
      honestBatchM (fun x ↦ impl x) s0 bytecode cs := by
  simp only [honestBatchM, simulateQ_bind, simulateQ_pure, simulateQ_obsAllHM, simulateQ_sq2HM,
    simulateQ_honestRoundsM, simulateQ_batchRoundsWith_run, simulateQ_sq3HM]

/-! ### The node's log -/

theorem simulateQ_logHashM (x : Bytes) (ℓ : Log) :
    simulateQ impl ((logHashM queryH x).run ℓ) = (logHashM (fun x ↦ impl x) x).run ℓ := by
  simp [logHashM, simulateQ_queryH]

theorem simulateQ_nodeLogPairsWithM (s0 : Digest) (pc pr : LeanDa.Digest) (bytecode : List K)
    (seed : Digest) (s : NodeStatement) (w : NodeWitness) :
    simulateQ impl (nodeLogPairsWithM queryH s0 pc pr bytecode seed s w) =
      nodeLogPairsWithM (fun x ↦ impl x) s0 pc pr bytecode seed s w := by
  unfold nodeLogPairsWithM
  rw [simulateQ_map]
  congr 1
  exact rel_nodeChecksWith (m := StateT Log (OracleComp HashSpec)) (n := StateT Log r)
    (fun {α : Type} x y ↦ RelS
      (fun {α : Type} (x : OracleComp HashSpec α) (y : r α) ↦ simulateQ impl x = y) (α := α) x y)
    (relS_pure _ fun a ↦ simulateQ_pure impl a) (relS_bind _ (simulateQ_rel_bind impl))
    (logHashM queryH) (logHashM fun x ↦ impl x) (simulateQ_logHashM impl) s0 pc pr bytecode
    seed s w []

theorem simulateQ_nodeLogPairsM (s : NodeStatement) (w : NodeWitness) :
    simulateQ impl (nodeLogPairsM queryH s w) = nodeLogPairsM (fun x ↦ impl x) s w := by
  simp only [nodeLogPairsM, simulateQ_bind, simulateQ_seedOfM, simulateQ_nodeLogPairsWithM]

/-! ### The Fiat–Shamir run -/

theorem simulateQ_fsRunM (S : Strategy) (fuel : ℕ) {α : Type} :
    ∀ (p : Prog α) (cv : Digest) (h : List Ev),
      simulateQ impl (fsRunM queryH S fuel p cv h) = fsRunM (fun x ↦ impl x) S fuel p cv h
  | .ret _, _, _ => by simp [fsRunM]
  | .fail, _, _ => by simp [fsRunM]
  | .read k, cv, h => by
    simp only [fsRunM, simulateQ_bind, simulateQ_queryH]
    exact congrArg _ (funext fun _ ↦ simulateQ_fsRunM S fuel _ _ _)
  | .sample k, cv, h => by
    simp only [fsRunM, simulateQ_bind, simulateQ_queryH]
    exact congrArg _ (funext fun _ ↦ simulateQ_fsRunM S fuel _ _ _)
  | .grind bits k, cv, h => by
    simp only [fsRunM, simulateQ_bind, simulateQ_findNonceM]
    refine congrArg _ (funext fun o ↦ ?_)
    split
    · simp
    · simp only [simulateQ_bind, simulateQ_queryH]
      exact congrArg _ (funext fun _ ↦ simulateQ_fsRunM S fuel _ _ _)
  | .commit ht w k, cv, h => by
    simp only [fsRunM]
    split
    · simp only [simulateQ_bind, simulateQ_treeRootM, simulateQ_queryH]
      refine congrArg _ (funext fun _ ↦ congrArg _ (funext fun _ ↦ congrArg _ (funext fun _ ↦ ?_)))
      exact simulateQ_fsRunM S fuel _ _ _
    · simp
  | .query i ps k, cv, h => by
    simp only [fsRunM]
    split
    · simp
    · exact simulateQ_fsRunM S fuel _ _ _

theorem simulateQ_freshRunM (S : Strategy) (fuel : ℕ) (bc : List K) (pd seed : Digest) :
    simulateQ impl (freshRunM queryH S fuel bc pd seed) =
      freshRunM (fun x ↦ impl x) S fuel bc pd seed := by
  simp only [freshRunM, simulateQ_map, simulateQ_fsRunM]

/-! ### The prover, through the failures -/

/-- The simulation of a failing computation's run. -/
def SimE {α : Type} (x : ExceptT ProverFail (OracleComp HashSpec) α) (y : ExceptT ProverFail r α) :
    Prop :=
  simulateQ impl x.run = y.run

omit [LawfulMonad r] in
theorem simE_pure {α : Type} (a : α) : SimE impl (pure a) (pure a) := by
  simp [SimE]

theorem simE_bind {α β : Type} (x : ExceptT ProverFail (OracleComp HashSpec) α)
    (y : ExceptT ProverFail r α) (f : α → ExceptT ProverFail (OracleComp HashSpec) β)
    (g : α → ExceptT ProverFail r β) (hx : SimE impl x y) (hf : ∀ a, SimE impl (f a) (g a)) :
    SimE impl (x >>= f) (y >>= g) := by
  unfold SimE at hx ⊢
  rw [ExceptT.run_bind, ExceptT.run_bind, simulateQ_bind, hx]
  refine congrArg _ (funext fun e ↦ ?_)
  cases e with
  | error e => simp
  | ok a => exact hf a

theorem simE_lift {α : Type} (x : OracleComp HashSpec α) (y : r α) (hx : simulateQ impl x = y) :
    SimE impl (liftM x) (liftM y) := by
  unfold SimE
  simp [hx]

omit [LawfulMonad r] in
theorem simE_throw {α : Type} (e : ProverFail) :
    SimE impl (throw e : ExceptT ProverFail (OracleComp HashSpec) α) (throw e) := by
  simp [SimE]

theorem simulateQ_honestDeferM (cs : List Child) :
    SimE impl (honestDeferM queryH cs) (honestDeferM (fun x ↦ impl x) cs) := by
  unfold honestDeferM
  by_cases h0 : cs = []
  · simp only [h0, ↓reduceIte]
    exact simE_pure impl _
  · simp only [h0, ↓reduceIte]
    refine simE_bind impl _ _ _ _ (simE_lift impl _ _ (simulateQ_claimsOfM impl cs)) fun ccs ↦ ?_
    refine simE_bind impl _ _ _ _ (simE_lift impl _ _ (simulateQ_honestBatchM impl _ _ _))
      fun wh ↦ ?_
    by_cases hw : wh.1 = (0, 0)
    · simp only [hw, ↓reduceIte]
      exact simE_throw impl _
    · simp only [hw, ↓reduceIte]
      refine simE_bind impl _ _ _ _ (simE_lift impl _ _ (simulateQ_batchWith impl _ _ _))
        fun o ↦ ?_
      rcases o with _ | d
      · exact simE_throw impl _
      · by_cases hh : d.BytecodeHolds End.bytecode
        · simp only [hh, ↓reduceIte]
          exact simE_pure impl _
        · simp only [hh, ↓reduceIte]
          exact simE_throw impl _

theorem simulateQ_proveNodeM (s : NodeStatement) (w : NodeWitness) (kos : List HonestOutN) :
    SimE impl (proveNodeM queryH ρ pfuel s w kos) (proveNodeM (fun x ↦ impl x) ρ pfuel s w kos) := by
  unfold proveNodeM
  refine simE_bind impl _ _ _ _ (simE_lift impl _ _ (simulateQ_digestOfM impl s)) fun pi ↦ ?_
  refine simE_bind impl _ _ _ _ (simE_lift impl _ _ (simulateQ_nodeLogPairsM impl s w))
    fun L ↦ ?_
  cases execOf L pi w with
  | none => exact simE_throw impl _
  | some e =>
    refine simE_bind impl _ _ _ _ (simE_lift impl _ _ (simulateQ_seedWith impl _ _)) fun seed ↦ ?_
    refine simE_bind impl _ _ _ _ (simE_lift impl _ _ (simulateQ_proveM impl _ _ _ _)) fun o ↦ ?_
    rcases o with _ | π
    · exact simE_throw impl _
    · refine simE_bind impl _ _ _ _ (simE_lift impl _ _ (simulateQ_freshRunM impl _ _ _ _ _))
        fun c? ↦ ?_
      rcases c? with _ | c
      · exact simE_throw impl _
      · refine simE_bind impl _ _ _ _ (simE_lift impl _ _ ?_) fun _ ↦ simE_pure impl _
        exact rel_mapM
          (fun {α : Type} (x : OracleComp HashSpec α) (y : r α) ↦ simulateQ impl x = y)
          (fun a ↦ simulateQ_pure impl a) (simulateQ_rel_bind impl) _ _
          (fun _ ↦ simulateQ_rel_bind impl _ _ _ _ (simulateQ_digestOfM impl _) fun _ ↦
            simulateQ_pure impl _) kos

theorem simulateQ_honestStepM (claims : Claims) (xs : List (Holder LeanXmss.Signature))
    (ss : List (Holder Sphincs.Signature)) (ds : List (Holder Da.Witness))
    (kos : List HonestOutN) :
    SimE impl (honestStepM queryH ρ pfuel claims xs ss ds kos)
      (honestStepM (fun x ↦ impl x) ρ pfuel claims xs ss ds kos) :=
  simE_bind impl _ _ _ _ (simulateQ_honestDeferM impl _) fun _ ↦
    simulateQ_proveNodeM impl ρ pfuel _ _ _

theorem simE_honestProverM : ∀ T : HonestTree,
    SimE impl (honestProverM queryH ρ pfuel T) (honestProverM (fun x ↦ impl x) ρ pfuel T)
  | .node claims xs ss ds kids => by
    rw [honestProverM, honestProverM]
    refine simE_bind impl _ _ _ _ ?_ fun kos ↦ simulateQ_honestStepM impl ρ pfuel _ _ _ _ kos
    exact rel_mapM (fun {α : Type} x y ↦ SimE impl (α := α) x y) (fun a ↦ simE_pure impl a)
      (simE_bind impl) _ _ (fun k ↦ simE_honestProverM k.1) kids.attach
termination_by T => sizeOf T
decreasing_by
  have := List.sizeOf_lt_of_mem k.2
  simp_wf
  omega

/-- **The oracle prover commutes with simulation**: its queries answered by `impl` is the
monadic prover with `impl` as the hash. -/
theorem simulateQ_honestProverM (T : HonestTree) :
    simulateQ impl (honestProverComp ρ pfuel T) = (honestProverM (fun x ↦ impl x) ρ pfuel T).run :=
  simE_honestProverM impl ρ pfuel T

end Commute

variable (ρ pfuel : ℕ)

/-- **The prover at a log's answers is the prover with the hash the log.** -/
theorem honestProverComp_lookImpl (ℓ : Log) (T : HonestTree) :
    simulateQ (lookImpl ℓ) (honestProverComp ρ pfuel T) =
      (honestProverM (look ℓ) ρ pfuel T).run :=
  simulateQ_honestProverM (lookImpl ℓ) ρ pfuel T

/-! ## The `Id` instance is the H-oblivious prover -/

section Id

variable (H : Bytes → Digest) (ρ pfuel : ℕ)

local notation "HI" => fun x ↦ (pure (H x) : Id Digest)

/-- `ExceptT ε Id`'s bind is `Except`'s. -/
theorem exceptTId_run_bind {ε α β : Type} (x : ExceptT ε Id α) (f : α → ExceptT ε Id β) :
    (x >>= f).run = (x.run : Except ε α).bind fun a ↦ (f a).run := by
  rw [ExceptT.run_bind]
  rcases h : (x.run : Except ε α) with e | a <;> rfl

/-- `ExceptT ε Id`'s `mapM` is `Except`'s. -/
theorem exceptTId_run_mapM {ε α β : Type} (f : α → ExceptT ε Id β) :
    ∀ l : List α, (l.mapM f).run = (l.mapM fun a ↦ (f a).run : Except ε (List β))
  | [] => rfl
  | a :: l => by
    rw [List.mapM_cons, List.mapM_cons, exceptTId_run_bind]
    rcases h : (f a).run with e | b
    · rfl
    · show ((l.mapM f >>= fun bs ↦ pure (b :: bs)) : ExceptT ε Id _).run = _
      rw [exceptTId_run_bind, exceptTId_run_mapM f l]
      rfl

theorem claimsOfM_id (cs : List Child) :
    claimsOfM (m := Id) HI cs = childClaimsOf H cs := by
  show Id.run (List.mapM _ cs) = _
  rw [List.idRun_mapM]
  rfl

/-- The batching with the hash in `Option`, every answer `some`, is the `Id` batching. -/
theorem batchWith_someH_id (s0 : Digest) (cs : List ChildClaims) (h : BatchHints) :
    batchWith (fun x ↦ some (H x)) s0 cs h = some (batchWith (m := Id) HI s0 cs h) :=
  (rel_batchWith (m := Id) (n := Option) (fun x y ↦ y = some x) (fun _ ↦ rfl)
    (fun x y f g hxy hfg ↦ by rw [hxy]; exact hfg _) HI (fun x ↦ some (H x)) (fun _ ↦ rfl)
    s0 cs h)

/-- A lifted `Id` computation's bind runs its continuation on the value. The lift is the one the
monad-generic definitions instantiate at `Id` (`MonadLiftT Id Id` by reflexivity): with the
`MonadLiftT Id m` of `pure ∘ Id.run` the kernel's check of the rewrite unfolds the lifted value. -/
theorem exceptTId_liftM_bind_run {ε α β : Type} (x : Id α) (f : α → ExceptT ε Id β) :
    (@liftM Id (ExceptT ε Id) (@instMonadLiftTOfMonadLift Id Id (ExceptT ε Id) _ (instMonadLiftT Id))
      α x >>= f).run = (f x).run := rfl

/-- **The `Id` instance of the deferred claim is `honestDeferN`.** -/
theorem honestDeferM_id (cs : List Child) :
    (honestDeferM (m := Id) HI cs).run = honestDeferN H cs := by
  unfold honestDeferM honestDeferN
  by_cases h0 : cs = []
  · rw [ite_eq_left h0, ite_eq_left h0]
    exact ExceptT.run_pure _
  · simp only [h0, ↓reduceIte, claimsOfM_id, honestBatchM_id, batchWith_someH_id,
      exceptTId_liftM_bind_run]
    by_cases hw : honestWeights H B1.Main.aggSeedD End.bytecode (childClaimsOf H cs) = (0, 0)
    · rw [ite_eq_left hw, ite_eq_left hw]
      exact ExceptT.run_throw
    · rw [ite_eq_right hw, ite_eq_right hw]
      generalize honestHints H B1.Main.aggSeedD End.bytecode (childClaimsOf H cs) = hs
      generalize batchWith (m := Id) HI B1.Main.aggSeedD (childClaimsOf H cs) hs = ob
      rw [exceptTId_liftM_bind_run]
      rcases ob with _ | d
      · exact ExceptT.run_throw
      · dsimp only
        by_cases hh : d.BytecodeHolds End.bytecode
        · rw [ite_eq_left hh, ite_eq_left hh]
          exact ExceptT.run_pure _
        · rw [ite_eq_right hh, ite_eq_right hh]
          exact ExceptT.run_throw

theorem nodeLogPairsM_id' (s : NodeStatement) (w : NodeWitness) :
    nodeLogPairsM (m := Id) HI s w = logOf H (nodeLog H s w) :=
  nodeLogPairsM_id H s w

theorem seedWith_id (pi : Digest) :
    seedWith (m := Id) HI End.bytecode (publicDigest (End.publicInputOf pi)) = seedAt H pi := rfl

theorem prove_pureH (P : Prog Bool) (S : Strategy) (seed : Digest) (fuel : ℕ) :
    prove (fun x ↦ (pure (H x) : Id Digest)) P S seed fuel = prove H P S seed fuel := rfl

theorem kidsM_id (kos : List HonestOutN) :
    kos.mapM (m := Id) (fun ko ↦ (do
      let d ← (digestOf H ko.stmt : Id Digest)
      pure (d, ko.proof) : Id (Digest × Proof))) = kos.map (nodeOfOutN H) := by
  show Id.run (List.mapM _ kos) = _
  rw [List.idRun_mapM]
  rfl

/-- **The `Id` instance of a node's proof is `proveNode`.** -/
theorem proveNodeM_id (s : NodeStatement) (w : NodeWitness) (kos : List HonestOutN) :
    (proveNodeM (m := Id) HI ρ pfuel s w kos).run = proveNode H ρ pfuel s w kos := by
  unfold proveNodeM proveNode
  simp only [nodeLogPairsM_id', digestOfM_id, seedWith_id, proveM_id, prove_pureH, freshRunM_id,
    exceptTId_liftM_bind_run]
  simp only [kidsM_id]
  generalize execOf (logOf H (nodeLog H s w)) (digestOf H s) w = eo
  rcases eo with _ | e
  · dsimp only
    exact ExceptT.run_throw (m := Id)
  · dsimp only
    simp only [exceptTId_liftM_bind_run]
    generalize LeanVM.Protocol.Compile.prove H (progOf (digestOf H s)) (stratOf ρ e) (seedAt H (digestOf H s)) pfuel = po
    rcases po with _ | π
    · dsimp only
      exact ExceptT.run_throw (m := Id)
    · dsimp only
      simp only [exceptTId_liftM_bind_run]
      generalize freshRun H (stratOf ρ e) pfuel End.bytecode
        (publicDigest (End.publicInputOf (digestOf H s))) (seedAt H (digestOf H s)) = co
      rcases co with _ | c
      · dsimp only
        exact ExceptT.run_throw (m := Id)
      · dsimp only
        simp only [exceptTId_liftM_bind_run]
        exact ExceptT.run_pure (m := Id) _

theorem honestStepM_id (claims : Claims) (xs : List (Holder LeanXmss.Signature))
    (ss : List (Holder Sphincs.Signature)) (ds : List (Holder Da.Witness))
    (kos : List HonestOutN) :
    (honestStepM (m := Id) HI ρ pfuel claims xs ss ds kos).run =
      honestStepN H ρ pfuel claims xs ss ds kos := by
  unfold honestStepM honestStepN
  rw [exceptTId_run_bind, honestDeferM_id]
  rcases honestDeferN H (kos.map HonestOutN.child) with e | hd
  · rfl
  · exact proveNodeM_id H ρ pfuel _ _ _

/-- **The `Id` instance is the H-oblivious prover.** -/
theorem honestProverM_id : ∀ T : HonestTree,
    (honestProverM (m := Id) HI ρ pfuel T).run = honestOutN H ρ pfuel T
  | .node claims xs ss ds kids => by
    rw [honestProverM, honestOutN_node, exceptTId_run_bind, exceptTId_run_mapM]
    have hk : (kids.attach.mapM fun k ↦ (honestProverM (m := Id) HI ρ pfuel k.1).run :
        Except ProverFail (List HonestOutN)) = kidOutsN H ρ pfuel kids := by
      unfold kidOutsN
      congr 1
      funext k
      exact honestProverM_id k.1
    rw [hk]
    rcases kidOutsN H ρ pfuel kids with e | kos
    · rfl
    · exact honestStepM_id H ρ pfuel _ _ _ _ kos
termination_by T => sizeOf T
decreasing_by
  have := List.sizeOf_lt_of_mem k.2
  simp_wf
  omega

/-- **The oracle prover answered by a hash function is the H-oblivious prover.** -/
theorem honestProverComp_at (T : HonestTree) :
    simulateQ (fun x ↦ (pure (H x) : Id Digest)) (honestProverComp ρ pfuel T) =
      honestOutN H ρ pfuel T :=
  (simulateQ_honestProverM (fun x ↦ (pure (H x) : Id Digest)) ρ pfuel T).trans
    (honestProverM_id H ρ pfuel T)

end Id

/-- **From the log to every agreeing hash**: the oracle prover's run answered by a log's answers
is the H-oblivious prover's output at every hash agreeing with the log. -/
theorem honestProverComp_look {ℓ : Log} {T : HonestTree} {r : Except ProverFail HonestOutN}
    (h : simulateQ (lookImpl ℓ) (honestProverComp ρ pfuel T) = some r) (Ht : Bytes → Digest)
    (hH : ∀ x u, look ℓ x = some u → Ht x = u) : honestOutN Ht ρ pfuel T = r :=
  (honestProverComp_at Ht ρ pfuel T).symm.trans (simulateQ_id_of_look ℓ Ht hH _ r h)

end
end LeanVM.E2E.Complete
