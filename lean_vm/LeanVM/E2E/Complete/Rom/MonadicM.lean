/-
  LeanVM.E2E.Complete.Rom.MonadicM

  T6-prob: the honest prover's pieces with the hash in any monad — the Fiat–Shamir run, the seed
  and the statement digest, the batching's honest hints and weights, the node's log with its
  answers, and the fresh claims' run — each with its `Id` instance the pure function of T6-det.
-/

module

public import LeanVM.E2E.Complete.Prover
public import LeanVM.E2E.Complete.Count.Basic
public import LeanVM.E2E.Complete.Rom.Fresh
public import LeanVM.Protocol.Compile.Rom.Prover

/-!
# The honest prover's pieces, monadic

`docs/roadmap/t6-prob.md` §3. The honest prover as an oracle computation makes every hash a
query; its pieces are written here with the hash `H : Bytes → m Digest` in any monad, as the
verifier's `…With` functions are, and each `Id` instance at `fun x ↦ pure (H x)` is the pure
function of T6-det (`…_id`):

* `fsRunM`: the run along the Fiat–Shamir challenges (`fsRun`), its proofs of work searched by
  `findNonceM`, its commitments' roots by `treeRootM`; `freshRunM`, the fresh claims' run
  (`freshRun`);
* `seedOfM`, `digestOfM`: the guest's IV and a statement's digest (`seedOf`, `digestOf`);
* `honestBatchM`: the batching's honest weights and hints (`honestWeights`, `honestHints`): the
  lambdas, the bytecode's honest rounds (`honestRoundsM`, each round's chain state by queries,
  `lead` a function of the round polynomial), the two sumchecks and the matrices' values;
* `nodeChecksWith`: the node's checks in `nodeLogWith`'s order; run with the logging hash
  `logHashM` (the answer, recorded with its string) it gives the node's log with its answers,
  `nodeLogPairsWithM` (`nodeLog`'s strings, each with `H`'s answer: `nodeLogPairsM_id`).

The query counts are in `CountM.lean`.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Node LeanVM.Guest
open LeanVM.Guest.Batch LeanVM.Guest.B1.Main LeanVM.E2E LeanVM.Protocol.Compile.Rom

@[expose] public section

/-! ## The Fiat–Shamir run -/

section FsRun

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest)

open Classical in
/-- **The run along the Fiat–Shamir challenges** (`fsRun`) with the hash in any monad. -/
noncomputable def fsRunM (S : Strategy) (fuel : ℕ) {α : Type} :
    Prog α → Digest → List Ev → m (Option (α × Digest × List Ev))
  | .ret a, cv, h => pure (some (a, cv, h))
  | .fail, _, _ => pure none
  | .read k, cv, h => do
    let cv' ← H (digestBytes cv ++ blockOf (S.msg h) 1)
    fsRunM S fuel (k (S.msg h)) cv' (h ++ [Ev.read (S.msg h)])
  | .sample k, cv, h => do
    let cv' ← H (digestBytes cv ++ blockOf 0 2)
    fsRunM S fuel (k (challengeOf cv')) cv' (h ++ [Ev.sample (challengeOf cv')])
  | .grind bits k, cv, h => do
    match ← findNonceM H bits cv fuel with
    | none => pure none
    | some n => do
      let cv' ← H (digestBytes cv ++ blockOf n 4)
      fsRunM S fuel k cv' (h ++ [Ev.grind bits])
  | .commit ht w k, cv, h =>
    if WellShaped w (S.word h) then do
      let root ← treeRootM H ht (S.word h)
      let cv0 ← H (digestBytes cv ++ blockOf (digestScalars root).1 1)
      let cv1 ← H (digestBytes cv0 ++ blockOf (digestScalars root).2 1)
      fsRunM S fuel k cv1 (h ++ [Ev.commit ht w (S.word h)])
    else pure none
  | .query i ps k, cv, h => match (commits h)[i]? with
    | none => pure none
    | some (ht, _, word) =>
      fsRunM S fuel (k (ps.map fun q ↦ word (q % 2 ^ ht))) cv
        (h ++ [Ev.query (ps.map fun q ↦ word (q % 2 ^ ht))])

/-- **The fresh claims' run** (`freshRun`) with the hash in any monad. -/
noncomputable def freshRunM (S : Strategy) (fuel : ℕ) (bc : List K) (pd seed : Digest) :
    m (Option FixedClaims) :=
  (Option.map (·.1)) <$> fsRunM H S fuel (claimsProg bc pd) seed []

end FsRun

section FsRunId

variable (H : Bytes → Digest)

/-- **The `Id` instance is `fsRun`.** -/
theorem fsRunM_id (S : Strategy) (fuel : ℕ) {α : Type} :
    ∀ (p : Prog α) (cv : Digest) (h : List Ev),
      fsRunM (m := Id) (fun x ↦ pure (H x)) S fuel p cv h = fsRun H S fuel p cv h
  | .ret _, _, _ => rfl
  | .fail, _, _ => rfl
  | .read k, cv, h => by
    simp only [fsRunM, fsRun]
    exact fsRunM_id S fuel _ _ _
  | .sample k, cv, h => by
    simp only [fsRunM, fsRun]
    exact fsRunM_id S fuel _ _ _
  | .grind bits k, cv, h => by
    simp only [fsRunM, fsRun]
    show (match findNonceM (m := Id) (fun x ↦ pure (H x)) bits cv fuel with
      | none => _ | some n => _) = _
    rw [findNonceM_id]
    cases findNonce H bits cv fuel
    · rfl
    · exact fsRunM_id S fuel _ _ _
  | .commit ht w k, cv, h => by
    simp only [fsRunM, fsRun]
    split
    · show fsRunM (m := Id) _ S fuel k _ _ = _
      rw [fsRunM_id S fuel, show treeRootM (m := Id) (fun x ↦ pure (H x)) ht (S.word h) =
        treeRoot H ht (S.word h) from treeRootM_id H ht (S.word h)]
      rfl
    · rfl
  | .query i ps k, cv, h => by
    simp only [fsRunM, fsRun]
    rcases (commits h)[i]? with _ | ⟨ht, w, word⟩
    · rfl
    · exact fsRunM_id S fuel _ _ _

/-- **The `Id` instance is `freshRun`.** -/
theorem freshRunM_id (S : Strategy) (fuel : ℕ) (bc : List K) (pd seed : Digest) :
    freshRunM (m := Id) (fun x ↦ pure (H x)) S fuel bc pd seed = freshRun H S fuel bc pd seed := by
  show Option.map (·.1) (fsRunM (m := Id) _ S fuel _ seed []) = _
  rw [fsRunM_id]
  rfl

end FsRunId

/-! ## The seed and the statement's digest -/

section Seed

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest)

/-- **The guest's IV** (`seedOf`), the seed of every node. -/
def seedOfM : m Digest := fiatShamirIvWith H End.bytecode

/-- **A node's statement digest** (`digestOf`), from the IV. -/
def digestOfM (s : NodeStatement) : m Digest := do
  statementDigestWith H (← seedOfM H) s

theorem seedOfM_id (H : Bytes → Digest) :
    seedOfM (m := Id) (fun x ↦ pure (H x)) = seedOf H := rfl

theorem digestOfM_id (H : Bytes → Digest) (s : NodeStatement) :
    digestOfM (m := Id) (fun x ↦ pure (H x)) s = digestOf H s := rfl

end Seed

/-! ## The batching's honest hints and weights -/

section Batch

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest)

/-- Absorb the scalars `xs` from `cv` (`obsAllW`). -/
def obsAllHM (cv : Digest) (xs : List E) : m Digest :=
  xs.foldlM (fun cv x ↦ H (digestBytes cv ++ blockOf x 1)) cv

/-- Two squeezes per child (`sq2W`). -/
def sq2HM : ℕ → Digest → m (List (E × E) × Digest)
  | 0, cv => pure ([], cv)
  | n + 1, cv => do
    let c1 ← H (digestBytes cv ++ blockOf 0 2)
    let c2 ← H (digestBytes c1 ++ blockOf 0 2)
    let r ← sq2HM n c2
    pure ((challengeOf c1, challengeOf c2) :: r.1, r.2)

/-- Three squeezes per child (`sq3W`). -/
def sq3HM : ℕ → Digest → m (List (E × E × E) × Digest)
  | 0, cv => pure ([], cv)
  | n + 1, cv => do
    let c1 ← H (digestBytes cv ++ blockOf 0 2)
    let c2 ← H (digestBytes c1 ++ blockOf 0 2)
    let c3 ← H (digestBytes c2 ++ blockOf 0 2)
    let r ← sq3HM n c3
    pure ((challengeOf c1, challengeOf c2, challengeOf c3) :: r.1, r.2)

/-- A round's chain state (`roundCv`): its two scalars absorbed, then the challenge squeezed. -/
def roundCvM (cv : Digest) (msg : E × E) : m Digest := do
  let a ← H (digestBytes cv ++ blockOf msg.1 1)
  let b ← H (digestBytes a ++ blockOf msg.2 1)
  H (digestBytes b ++ blockOf 0 2)

/-- **The honest rounds** (`honestRounds`): each round's message a function of the round
polynomial, its chain state by queries. -/
noncomputable def honestRoundsM (n : ℕ) (f : List E → E) :
    ℕ → List E → Digest → m (List (E × E))
  | 0, _, _ => pure []
  | k + 1, pre, cv => do
    let cv' ← roundCvM H cv (cubeSum n f (pre ++ [1]), lead fun x ↦ cubeSum n f (pre ++ [x]))
    let rest ← honestRoundsM n f k (pre ++ [challengeOf cv']) cv'
    pure ((cubeSum n f (pre ++ [1]), lead fun x ↦ cubeSum n f (pre ++ [x])) :: rest)

/-- The honest hints from the matrices' weights, the bytecode's rounds and challenges and the
matrices' final claim (`honestHints`'s fields). -/
noncomputable def hintsOf (bytecode : List K) (w : E × E) (rounds : List (E × E)) (rB : List E)
    (finM : E) : BatchHints where
  bytecodeRounds := rounds
  matrixRounds := zeroRounds
  bytecodeValue := multilinearEval (bytecode.map ofK) rB
  matrixA := if w.1 ≠ 0 then finM / w.1 else 0
  matrixB := if w.1 ≠ 0 then 0 else if w.2 ≠ 0 then finM / w.2 else 0

/-- **The batching's honest weights and hints** (`honestWeights`, `honestHints`): the bytecode's
lambdas, its honest rounds and sumcheck, the matrices' lambdas and zero-round sumcheck, the
matrices' weights at its challenges, and the hints. -/
noncomputable def honestBatchM (s0 : Digest) (bytecode : List K) (cs : List ChildClaims) :
    m ((E × E) × BatchHints) := do
  let cvA ← obsAllHM H s0 (ofK (gpow cs.length) :: cs.flatMap childCells)
  let b ← sq2HM H cs.length cvA
  let rounds ← honestRoundsM H (Nat.log2 bytecode.length) (bytecodePoly bytecode cs b.1)
    (Nat.log2 bytecode.length) [] b.2
  let be ← (batchRoundsWith H (claimBOf cs b.1) rounds).run b.2
  let ms ← sq3HM H cs.length be.2
  let me ← (batchRoundsWith H (claimMOf cs ms.1) zeroRounds).run ms.2
  pure ((matrixWeightA cs ms.1 me.1.1, matrixWeightB cs ms.1 me.1.1),
    hintsOf bytecode (matrixWeightA cs ms.1 me.1.1, matrixWeightB cs ms.1 me.1.1) rounds be.1.1
      me.1.2)

/-- The batching's honest hints. -/
noncomputable def honestHintsM (s0 : Digest) (bytecode : List K) (cs : List ChildClaims) :
    m BatchHints :=
  Prod.snd <$> honestBatchM H s0 bytecode cs

/-- The matrices' weights at the end of the honest batching. -/
noncomputable def honestWeightsM (s0 : Digest) (bytecode : List K) (cs : List ChildClaims) :
    m (E × E) :=
  Prod.fst <$> honestBatchM H s0 bytecode cs

end Batch

section BatchId

variable (H : Bytes → Digest)

local notation "HI" => fun x ↦ (pure (H x) : Id Digest)

theorem obsAllW_someH_eq : ∀ (cv : Digest) (xs : List E),
    obsAllW (someH H) cv xs = some (obsAllHM (m := Id) HI cv xs)
  | cv, [] => rfl
  | cv, x :: xs => by
    rw [obsAllW_cons]
    exact obsAllW_someH_eq _ xs

theorem sq2W_someH_eq : ∀ (n : ℕ) (cv : Digest),
    sq2W (someH H) n cv = some (sq2HM (m := Id) HI n cv)
  | 0, _ => rfl
  | n + 1, cv => by
    simp only [sq2W, someH, Option.bind_eq_bind, Option.bind_some, sq2W_someH_eq n]
    rfl

theorem sq3W_someH_eq : ∀ (n : ℕ) (cv : Digest),
    sq3W (someH H) n cv = some (sq3HM (m := Id) HI n cv)
  | 0, _ => rfl
  | n + 1, cv => by
    simp only [sq3W, someH, Option.bind_eq_bind, Option.bind_some, sq3W_someH_eq n]
    rfl

theorem batchRoundsWith_someH_eq (claim : E) (rounds : List (E × E)) (cv : Digest) :
    (batchRoundsWith (someH H) claim rounds).run cv =
      some ((batchRoundsWith (m := Id) HI claim rounds).run cv) :=
  (relS_batchRoundsWith (m := Id) (n := Option) (fun x y ↦ y = some x) (fun _ ↦ rfl)
    (fun x y f g hxy hfg ↦ by rw [hxy]; exact hfg _) HI (someH H) (fun _ ↦ rfl) claim rounds
    cv).symm ▸ rfl

theorem honestRoundsM_id (n : ℕ) (f : List E → E) : ∀ (k : ℕ) (pre : List E) (cv : Digest),
    honestRoundsM (m := Id) HI n f k pre cv = honestRounds H n f k pre cv
  | 0, _, _ => rfl
  | k + 1, pre, cv => by
    simp only [honestRoundsM, honestRounds]
    exact congrArg _ (honestRoundsM_id n f k _ _)

/-- **The `Id` instance is the honest weights and hints.** -/
theorem honestBatchM_id (s0 : Digest) (bytecode : List K) (cs : List ChildClaims) :
    honestBatchM (m := Id) HI s0 bytecode cs =
      (honestWeights H s0 bytecode cs, honestHints H s0 bytecode cs) := by
  simp only [honestWeights, honestHints, mEnd, mStart, bEnd, bRounds, bStart,
    obsAllW_someH_eq, sq2W_someH_eq, sq3W_someH_eq, batchRoundsWith_someH_eq, Option.getD_some,
    ← honestRoundsM_id]
  rfl

theorem honestHintsM_id (s0 : Digest) (bytecode : List K) (cs : List ChildClaims) :
    honestHintsM (m := Id) HI s0 bytecode cs = honestHints H s0 bytecode cs := by
  simp only [honestHintsM, honestBatchM_id]
  rfl

theorem honestWeightsM_id (s0 : Digest) (bytecode : List K) (cs : List ChildClaims) :
    honestWeightsM (m := Id) HI s0 bytecode cs = honestWeights H s0 bytecode cs := by
  simp only [honestWeightsM, honestBatchM_id]
  rfl

end BatchId

/-! ## The node's checks and their log -/

section Checks

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest)

/-- A child's checks: its statement's digest and its deferring verifier. -/
def childChecksWith (bytecode : List K) (seed : Digest) (c : Child) : m Unit := do
  let pi ← statementDigestWith H seed c.statement
  let _ ← verifyDeferredWith H bytecode seed pi c.fresh c.proof
  pure ()

/-- The children's checks. -/
def childrenChecksWith (bytecode : List K) (seed : Digest) : List Child → m Unit
  | [] => pure ()
  | c :: cs => do
    childChecksWith H bytecode seed c
    childrenChecksWith bytecode seed cs

/-- A holder's check: `f` of the claim and the witness, if held directly. -/
def holderChecksWith {α W : Type} (f : α → W → m Unit) (a : α) : Holder W → m Unit
  | .direct w => f a w
  | .child _ => pure ()

/-- The holders' checks: `f` of every claim held directly. -/
def holdersChecksWith {α W : Type} (f : α → W → m Unit) : List α → List (Holder W) → m Unit
  | a :: as, h :: hs => do
    holderChecksWith f a h
    holdersChecksWith f as hs
  | _, _ => pure ()

/-- A leanXMSS signature's check. -/
def xmssCheckWith (c : XmssClaim) (σ : LeanXmss.Signature) : m Unit := do
  let _ ← xmssVerifyWith H c.1 c.2 σ
  pure ()

/-- A leanSPHINCS signature's check. -/
def sphincsCheckWith (c : SphincsClaim) (σ : Sphincs.Signature) : m Unit := do
  let _ ← sphincsVerifyWith H c.1 c.2 σ
  pure ()

/-- A DA opening's check: the commitment and the vector digest. -/
def daCheckWith (pc pr : LeanDa.Digest) (_ : DaClaim) (w : Da.Witness) : m Unit := do
  let _ ← Da.commitCodewordsWith (Da.daHash H) pc pr w.rows
  let _ ← Da.vectorDigestWith (Da.daHash H) w.vector
  pure ()

/-- **The node's checks**, in `nodeLogWith`'s order: the statement's digest, the children's
digests and deferring verifiers, the signatures' verifications, the DA openings, the children's
claims and the batching. -/
def nodeChecksWith (s0 : Digest) (pc pr : LeanDa.Digest) (bytecode : List K) (seed : Digest)
    (s : NodeStatement) (w : NodeWitness) : m Unit := do
  let _ ← statementDigestWith H seed s
  childrenChecksWith H bytecode seed w.children
  holdersChecksWith (xmssCheckWith H) s.claims.xmss w.xmss
  holdersChecksWith (sphincsCheckWith H) s.claims.sphincs w.sphincs
  holdersChecksWith (daCheckWith H pc pr) s.claims.da w.da
  let ccs ← childClaimsM H seed w.children
  let _ ← batchWith H s0 ccs w.hints
  pure ()

/-- **The logging hash**: the answer, recorded with its string. -/
def logHashM (x : Bytes) : StateT Log m Digest := do
  let u ← (H x : m Digest)
  modify (· ++ [(x, u)])
  pure u

/-- **The node's log with its answers**, at the batching's chain state `s0`, the DA padding
digests `pc`, `pr`, the bytecode and the seed. -/
def nodeLogPairsWithM (s0 : Digest) (pc pr : LeanDa.Digest) (bytecode : List K) (seed : Digest)
    (s : NodeStatement) (w : NodeWitness) : m Log :=
  Prod.snd <$> (nodeChecksWith (logHashM H) s0 pc pr bytecode seed s w).run []

/-- **The node's log with its answers**, at the deployed parameters, from the IV (whose two
queries are not logged, as `nodeLog` does not). -/
noncomputable def nodeLogPairsM (s : NodeStatement) (w : NodeWitness) : m Log := do
  nodeLogPairsWithM H B1.Main.aggSeedD B1.Main.daPadCell B1.Main.daPadRow End.bytecode
    (← seedOfM H) s w

end Checks

/-! ### The relational closure of the node's checks -/

section RelChecks

variable {m n : Type → Type} [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
  (R : ∀ {α : Type}, m α → n α → Prop)
  (hpure : ∀ {α : Type} (a : α), R (pure a) (pure a))
  (hbind : ∀ {α β : Type} (x : m α) (y : n α) (f : α → m β) (g : α → n β), R x y →
    (∀ a, R (f a) (g a)) → R (x >>= f) (y >>= g))
  (H : Bytes → m Digest) (H' : Bytes → n Digest) (hH : ∀ x, R (H x) (H' x))
include hpure hbind hH

omit [LawfulMonad m] [LawfulMonad n] in
theorem rel_childrenChecksWith (bytecode : List K) (seed : Digest) :
    ∀ cs : List Child,
      R (childrenChecksWith H bytecode seed cs) (childrenChecksWith H' bytecode seed cs)
  | [] => hpure _
  | c :: cs => by
    simp only [childrenChecksWith, childChecksWith]
    refine hbind _ _ _ _ ?_ fun _ ↦ rel_childrenChecksWith bytecode seed cs
    exact hbind _ _ _ _ (rel_statementDigestWith R hbind H H' hH _ _) fun _ ↦
      hbind _ _ _ _ (rel_verifyDeferredWith R hpure hbind H H' hH _ _ _ _ _) fun _ ↦ hpure _

omit [LawfulMonad m] [LawfulMonad n] hH in
theorem rel_holdersChecksWith {α W : Type} (f : α → W → m Unit) (g : α → W → n Unit)
    (hfg : ∀ a w, R (f a w) (g a w)) :
    ∀ (as : List α) (hs : List (Holder W)),
      R (holdersChecksWith f as hs) (holdersChecksWith g as hs)
  | a :: as, h :: hs => by
    simp only [holdersChecksWith]
    refine hbind _ _ _ _ ?_ fun _ ↦ rel_holdersChecksWith f g hfg as hs
    cases h with
    | direct w => exact hfg a w
    | child _ => exact hpure _
  | [], _ => hpure _
  | _ :: _, [] => hpure _

/-- **A closed relation relates the node's checks with related hashes.** -/
theorem rel_nodeChecksWith (s0 : Digest) (pc pr : LeanDa.Digest) (bytecode : List K)
    (seed : Digest) (s : NodeStatement) (w : NodeWitness) :
    R (nodeChecksWith H s0 pc pr bytecode seed s w)
      (nodeChecksWith H' s0 pc pr bytecode seed s w) := by
  have hHD : ∀ x, R (Da.daHash H x) (Da.daHash H' x) := fun x ↦
    rel_map R hpure hbind _ _ _ (hH x)
  unfold nodeChecksWith
  refine hbind _ _ _ _ (rel_statementDigestWith R hbind H H' hH _ _) fun _ ↦ ?_
  refine hbind _ _ _ _ (rel_childrenChecksWith R hpure hbind H H' hH _ _ _) fun _ ↦ ?_
  refine hbind _ _ _ _ (rel_holdersChecksWith R hpure hbind _ _ (fun a σ ↦
    hbind _ _ _ _ (rel_xmssVerifyWith R hpure hbind H H' hH _ _ _) fun _ ↦ hpure _) _ _)
    fun _ ↦ ?_
  refine hbind _ _ _ _ (rel_holdersChecksWith R hpure hbind _ _ (fun a σ ↦
    hbind _ _ _ _ (rel_sphincsVerifyWith R hpure hbind H H' hH _ _ _) fun _ ↦ hpure _) _ _)
    fun _ ↦ ?_
  refine hbind _ _ _ _ (rel_holdersChecksWith R hpure hbind _ _ (fun a dw ↦
    hbind _ _ _ _ (rel_commitCodewordsWith R hpure hbind _ _ hHD _ _ _) fun _ ↦
      hbind _ _ _ _ (hHD _) fun _ ↦ hpure _) _ _) fun _ ↦ ?_
  refine hbind _ _ _ _ (rel_mapM R hpure hbind _ _ (fun _ ↦ rel_map R hpure hbind _ _ _
    (rel_statementDigestWith R hbind H H' hH _ _)) _) fun _ ↦ ?_
  exact hbind _ _ _ _ (rel_batchWith R hpure hbind H H' hH _ _ _) fun _ ↦ hpure _

end RelChecks

/-! ### The logged checks are `nodeLogWith` -/

section LogEq

variable (H : Bytes → Digest)

theorem childrenChecksWith_log (bytecode : List K) (seed : Digest) :
    ∀ cs : List Child,
      (childrenChecksWith (LogM.hash H) bytecode seed cs).log =
        cs.flatMap (childLog H bytecode seed)
  | [] => rfl
  | c :: cs => by
    simp only [childrenChecksWith, childChecksWith, LogM.bind_log, LogM.pure_log,
      List.append_nil, List.flatMap_cons, childLog, childrenChecksWith_log bytecode seed cs]

theorem holdersChecksWith_log {α W : Type} (f : α → W → LogM Unit) (g : α → W → List Bytes)
    (hfg : ∀ a w, (f a w).log = g a w) :
    ∀ (as : List α) (hs : List (Holder W)), (holdersChecksWith f as hs).log = holdersLog g as hs
  | a :: as, h :: hs => by
    simp only [holdersChecksWith, LogM.bind_log, holdersChecksWith_log f g hfg as hs]
    cases h with
    | direct w => simp [holderChecksWith, holdersLog, holderLog, hfg]
    | child _ => simp [holderChecksWith, holdersLog, holderLog, LogM.pure_log]
  | [], _ => by simp [holdersChecksWith, holdersLog, LogM.pure_log]
  | _ :: _, [] => by simp [holdersChecksWith, holdersLog, LogM.pure_log]

/-- **The logged checks' log is `nodeLogWith`.** -/
theorem nodeChecksWith_log (s0 : Digest) (pc pr : LeanDa.Digest) (bytecode : List K)
    (seed : Digest) (s : NodeStatement) (w : NodeWitness) :
    (nodeChecksWith (LogM.hash H) s0 pc pr bytecode seed s w).log =
      nodeLogWith H s0 pc pr bytecode seed s w := by
  have hx : (holdersChecksWith (xmssCheckWith (LogM.hash H)) s.claims.xmss w.xmss).log =
      holdersLog (fun c σ ↦ (xmssVerifyWith (LogM.hash H) c.1 c.2 σ).log) s.claims.xmss w.xmss :=
    holdersChecksWith_log _ _ (fun _ _ ↦ List.append_nil _) _ _
  have hs : (holdersChecksWith (sphincsCheckWith (LogM.hash H)) s.claims.sphincs w.sphincs).log =
      holdersLog (fun c σ ↦ (sphincsVerifyWith (LogM.hash H) c.1 c.2 σ).log) s.claims.sphincs
        w.sphincs :=
    holdersChecksWith_log _ _ (fun _ _ ↦ List.append_nil _) _ _
  have hd : (holdersChecksWith (daCheckWith (LogM.hash H) pc pr) s.claims.da w.da).log =
      holdersLog (fun (_ : DaClaim) ↦ daLog H pc pr) s.claims.da w.da :=
    holdersChecksWith_log _ _ (fun _ _ ↦ by
      simp only [daCheckWith, daLog, LogM.bind_log, LogM.pure_log, List.append_nil]) _ _
  simp only [nodeChecksWith, nodeLogWith, LogM.bind_log, LogM.pure_log, List.append_nil,
    List.append_assoc, childrenChecksWith_log, hx, hs, hd]

end LogEq

/-! ### The logged run in `Id` -/

section LogId

variable (H : Bytes → Digest)

local notation "HI" => fun x ↦ (pure (H x) : Id Digest)

/-- A logging run and a logged computation agree: from every log, the run returns the
computation's value and appends its strings with `H`'s answers. -/
def LogAgree {α : Type} (x : StateT Log Id α) (a : LogM α) : Prop :=
  ∀ ℓ, x.run ℓ = (a.val, ℓ ++ a.log.map fun y ↦ (y, H y))

theorem logAgree_pure {α : Type} (a : α) : LogAgree H (pure a) (pure a) := fun ℓ ↦ by
  simp [LogM.pure_log, LogM.pure_val]
  rfl

theorem logAgree_bind {α β : Type} (x : StateT Log Id α) (a : LogM α) (f : α → StateT Log Id β)
    (g : α → LogM β) (hx : LogAgree H x a) (hf : ∀ b, LogAgree H (f b) (g b)) :
    LogAgree H (x >>= f) (a >>= g) := fun ℓ ↦ by
  rw [StateT.run_bind]
  show (f (x.run ℓ).1).run (x.run ℓ).2 = _
  rw [hx ℓ, hf]
  simp [LogM.bind_log, LogM.bind_val, List.map_append, List.append_assoc]

theorem logAgree_hash (x : Bytes) : LogAgree H (logHashM (m := Id) HI x) (LogM.hash H x) :=
  fun _ ↦ rfl

/-- **The `Id` instance is the node's log with `H`'s answers.** -/
theorem nodeLogPairsWithM_id (s0 : Digest) (pc pr : LeanDa.Digest) (bytecode : List K)
    (seed : Digest) (s : NodeStatement) (w : NodeWitness) :
    Id.run (nodeLogPairsWithM (m := Id) HI s0 pc pr bytecode seed s w) =
      (nodeLogWith H s0 pc pr bytecode seed s w).map fun x ↦ (x, H x) := by
  have h := rel_nodeChecksWith (m := StateT Log Id) (n := LogM) (fun x a ↦ LogAgree H x a)
    (logAgree_pure H) (logAgree_bind H) (logHashM (m := Id) HI) (LogM.hash H)
    (logAgree_hash H) s0 pc pr bytecode seed s w []
  show ((nodeChecksWith (logHashM (m := Id) HI) s0 pc pr bytecode seed s w).run []).2 = _
  rw [h, ← nodeChecksWith_log]
  rfl

/-- **The `Id` instance is `nodeLog` with `H`'s answers.** -/
theorem nodeLogPairsM_id (s : NodeStatement) (w : NodeWitness) :
    Id.run (nodeLogPairsM (m := Id) HI s w) = (nodeLog H s w).map fun x ↦ (x, H x) :=
  nodeLogPairsWithM_id H _ _ _ _ _ s w

end LogId

end
end LeanVM.E2E.Complete
