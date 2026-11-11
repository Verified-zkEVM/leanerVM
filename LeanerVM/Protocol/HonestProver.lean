/-
  LeanerVM.Protocol.HonestProver

  leanVM's honest prover with prover-only state: the bus phase's product trees built once from
  the stack, the table sumcheck's tables read once and bound one challenge at a time, the Flock
  phase's tables built once, proved to run as the honest prover of `leanVmPhases`, with the
  oracle protocol's completeness for it.
-/

module

public import LeanerVM.Protocol.Piop
public import LeanerVM.Protocol.ToArkLib.CachedProver
public import LeanerVM.Protocol.ToArkLib.GrandProductCached
public import LeanerVM.Protocol.ToArkLib.SumcheckCached
public import LeanerVM.Protocol.ToArkLib.Flock.Cached

/-!
# The honest prover, with state

The honest prover of `leanVmPhases` computes every message from the statement, the stack and
the challenges so far, so it rebuilds what it reads at every round: the bus leaves from the stack
and the trees' levels from the leaves, and in the table sumcheck the columns, read through the
layout and lifted to `E`, and their binding to the challenges. `leanVmCached` is a cached prover
of the whole protocol (`Component.Cached`): the bus phase builds the three trees once, after the
fingerprint challenges, reads the roots off them and carries them through the grand-product
argument (`busCached`, by `cachedGkr`); the table sumcheck reads its tables off the stack once
and binds each challenge once (`tableCached`, by `Sumcheck.cachedRounds`); the Flock phase walks
each block of its region once and builds its skip and lincheck tables once (`flockCached`, by
`Flock.flockCached`); the other phases run their honest provers.

`leanVmFastProver` is its prover. **`leanVmFastProver_run`**: its run is the run of
`leanVmProver (leanVmPhases I h)`, on every statement, stack and challenge sequence. The oracle
reduction with it and leanVM's verifier, `leanVmFastPiop`, has leanVM's verifier
(`leanVmFastPiop_verifier`, by `rfl`), so `leanVm_rbrKnowledgeSoundness` is a statement about
it, and it is perfectly complete (`leanVmFast_perfectCompleteness`). No definition or statement of
the protocol changes.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly CMlPolynomialEval OracleComp OracleSpec ProtocolSpec

@[expose] public section

variable (I : M3Instance)

namespace Bus

/-- The roots read off the trees: the push tree's and the count tree's. -/
def rootsFromTrees (T : Vector (Levels E I.μBus) 3) : E × E :=
  ((T[(0 : Fin 3)].get 0)[0]'(Nat.two_pow_pos 0), (T[(2 : Fin 3)].get 0)[0]'(Nat.two_pow_pos 0))

/-- The roots read off the trees of the leaves are the honest roots. -/
theorem rootsFromTrees_treesOf (p : (Data I × ∀ i, TheOracle I i) × Unit) :
    rootsFromTrees I (Gkr.treesOf 3 I.μBus (leaves I) p.1.1 p.1.2) = rootsHonest I p := by
  simp only [rootsFromTrees, rootsHonest, Gkr.get_treesOf]
  rw [← layerTable_zero_getElem, ← layerTable_zero_getElem]

/-- The cached roots' message: the trees built from the stack at the fingerprint challenges, the
roots read off them, the trees handed on. -/
def rootsCached : Component.Cached (rootsStep I) (fun _ ↦ ())
    (Gkr.treesAtRoots 3 I.μBus (leaves I)) :=
  (Component.Cached.sendChecked (msg := fun _ T ↦ rootsFromTrees I T) (upd := fun _ T _ ↦ T)
    (cin := fun p ↦ Gkr.treesOf 3 I.μBus (leaves I) p.1.1 p.1.2)
    (rootsFromTrees_treesOf I) fun _ ↦ rfl).adaptIn
    (fun p _ ↦ Gkr.treesOf 3 I.μBus (leaves I) p.1.1 p.1.2) fun _ ↦ rfl

/-- A bus output with its forms and totals tabulated: computed once, read back at every use. The
table sumcheck reads them at every point of every round. -/
def memoOut (b : BusOut I) : BusOut I :=
  let ft : Vector (Vector (Σ j : Fin I.ntab, I.Form j) I.ntab) 3 :=
    Vector.ofFn fun k ↦ Vector.ofFn fun j ↦
      ⟨j, if hj : I.SumcheckTable j then b.forms k ⟨j, hj⟩ else []⟩
  let tv := Vector.ofFn b.totals
  { point := b.point
    forms := fun k j ↦ cast (congrArg I.Form (by simp [ft])) ft[k][j.1].2
    totals := fun k ↦ tv[k]
    columns := b.columns }

/-- A value read back through a cast, from a pair with the index it was stored at. -/
private theorem cast_snd_of_eq {α : Type} {β : α → Type} {i : α} {x : β i} :
    ∀ (p : Σ i, β i) (_ : p = ⟨i, x⟩) (h : β p.1 = β i), cast h p.2 = x
  | _, rfl, _ => rfl

/-- The tabulated output is the output. -/
theorem memoOut_eq (b : BusOut I) : memoOut I b = b := by
  obtain ⟨pt, fs, ts, cs⟩ := b
  simp only [memoOut, BusOut.mk.injEq, true_and, and_true]
  refine ⟨funext fun k ↦ funext fun j ↦ cast_snd_of_eq (β := I.Form) (i := j.1) _ ?_ _,
    funext fun k ↦ ?_⟩
  · simp [j.2]
  · simp

/-- The cached boundary values: sent once, the output tabulated. -/
def valuesCached (h : Conditions I) :
    Component.Cached (valuesStep I h) (fun _ ↦ ()) (fun _ ↦ ()) :=
  Component.Cached.sendCheckedOut (msg := fun p _ ↦ honestValues h (theStack p.1.2) p.1.1.2.1)
    (upd := fun _ _ _ ↦ ()) (honest := fun p ↦ honestValues h (theStack p.1.2) p.1.1.2.1)
    (check := fun _ _ ↦ true)
    (out := fun (ℓ : Gkr.LayerStmt (Data I) E 3 I.μBus) (vals : Vector E I.busClaims) ↦
      (ℓ.1.1, busOut h ℓ vals))
    (cin := fun _ ↦ ()) (cout := fun _ ↦ ())
    (fun ℓ vals ↦ (ℓ.1.1, memoOut I (busOut h ℓ vals))) (fun ℓ vals ↦ by rw [memoOut_eq])
    (fun _ ↦ rfl) fun _ ↦ rfl

/-- The cached bus phase: the fingerprint challenges, the roots off the trees, the grand-product
argument carrying the trees, the boundary values with the output built once. -/
def busCached (h : Conditions I) :
    Component.Cached (busPhase I h).toDef (fun _ ↦ ()) (fun _ ↦ ()) :=
  (((Component.Cached.ofDef (challengeStep I)).append (rootsCached I)).append
    (cachedGkr 3 I.μBus (leaves I))).append (valuesCached I h)

end Bus

namespace TableSumcheck

/-- The cached table sumcheck: the batching challenge, the rounds on the tables read off the stack
once and bound one challenge at a time, the values read off the bound tables. -/
def tableCached : Component.Cached (tableSumcheck I).toDef (fun _ ↦ ()) (fun _ ↦ ()) :=
  ((Component.Cached.ofDef (batchStep I)).append
    ((Sumcheck.cachedRounds (tableSummand I) Sumcheck.unitWeights nodes).adaptIn
      (fun p _ ↦ Sumcheck.boundCache (tableSummand I) (SumcheckRound.ctxOf p) 0 p.1.1.2.1)
      fun _ ↦ rfl)).append
    (Sumcheck.cachedFinal (tableSummand I) (tableOut I))

end TableSumcheck

/-- The cached Flock phase on a slot: on a region, the Flock argument's cached prover. -/
def flockCachedOpt : (o : Option (FlockRegion I.toShape)) → (h : I.flock = o) →
    Component.Cached (flockPhaseOpt I o h).toDef (fun _ ↦ ()) (fun _ ↦ ())
  | none, _ => Component.Cached.ofDef _
  | some r, h => Flock.flockCached (flockParams r.kBatch) r.r1cs (FlockPhase.bits r)
      FlockPhase.side 5 (algebraMap K E) g (FlockPhase.lift r) (FlockPhase.finish r h)

/-- The cached Flock phase: the witness tables and products walked once, the skip tables and the
lincheck's tables each built once. -/
def flockCached : Component.Cached (flockPhase I).toDef (fun _ ↦ ()) (fun _ ↦ ()) :=
  flockCachedOpt I I.flock rfl

variable (h : Bus.Conditions I)

/-- **leanVM's cached honest prover**: the commitment, the bus phase, the table sumcheck and the
Flock phase cached, the public-input check and the opening as they are. -/
def leanVmCached : Component.Cached (leanVmPhases I h).toDef (fun _ ↦ ()) (fun _ ↦ ()) :=
  (((((Component.Cached.ofDef (commitDef I)).append (Bus.busCached I h)).append
    (TableSumcheck.tableCached I)).append
    (Component.Cached.ofDef (deployedPublicInputPhase I).toDef)).append
    (flockCached I)).append
    (Component.Cached.ofDef (openingPhase I))

/-- leanVM's honest prover with its state. -/
def leanVmFastProver :
    OracleProver []ₒ I.Stmt NoOracle (Column I.μ) Unit (TheOracle I) Unit (piopSpec I) :=
  (leanVmCached I h).toProver

/-- **The prover with state is the honest prover**: on every statement and stack, its run (its
transcript and its output, at every challenge sequence) is the run of `leanVmProver`. -/
theorem leanVmFastProver_run (s : I.Stmt × ∀ i, NoOracle i) (w : Column I.μ) :
    (leanVmFastProver I h).run s w = (leanVmProver (leanVmPhases I h)).run s w :=
  (leanVmCached I h).toProver_run s w

/-- The oracle protocol with the prover with state. -/
def leanVmFastPiop :
    OracleReduction []ₒ I.Stmt NoOracle (Column I.μ) Unit (TheOracle I) Unit (piopSpec I) :=
  (leanVmCached I h).toDef.red

/-- Its verifier is leanVM's. -/
theorem leanVmFastPiop_verifier :
    (leanVmFastPiop I h).verifier = leanVmVerifier (leanVmPhases I h) :=
  rfl

/-- **Perfect completeness with the prover with state**: on every statement and stack with
`M3Holds`, it convinces leanVM's verifier with probability one. -/
theorem leanVmFast_perfectCompleteness (hd : I.d ≤ 2) {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (leanVmFastPiop I h).perfectCompleteness init impl (M3Rel I) (Seam.done I) :=
  ((leanVmCached I h).complete (leanVmComplete I h hd).toDef).complete init impl

end
end LeanerVM.Protocol
