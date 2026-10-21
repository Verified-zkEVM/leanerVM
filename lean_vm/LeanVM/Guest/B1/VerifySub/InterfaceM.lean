/-
  LeanVM.Guest.B1.VerifySub.InterfaceM

  What `verify_sub`'s soundness over a hash model assumes of the callees that hash: their
  outcomes with every hash answered by the model, and at the deployed model the deployed ones.
-/

module

public import LeanVM.Guest.B1.VerifySub.InterfaceW

/-!
# `verify_sub`'s callees over a hash model

`Interface.lean`'s and `InterfaceW.lean`'s soundness of the callees that hash, over a hash model
`M` (`Value.HashModel`): the relation under `M.sem` (`coreProgram.RelB M.sem`), the runs over the
model's answered hash (`RunsToM M`, and `RunsWithM M` for the stacked opening, which reads
openings and roots), the fixed polynomials' values over the model's run (`BytecodeAtM`,
`MatricesAtM`). Each `…M` statement is its deployed one with these replaced, and nothing else:

| deployed | over `M` |
|---|---|
| `GkrOut`, `SoundGkr` (`verify_bus_gkr`) | `GkrOutM`, `SoundGkrM` |
| `TablesOut`, `SoundTables` (`verify_tables`) | `TablesOutM`, `SoundTablesM` |
| `FlockOut`, `SoundFlock` (`verify_flock`) | `FlockOutM`, `SoundFlockM` |
| `OpenOut`, `SoundOpen`, `OpenOutW`, `SoundOpenWC` (`open_stacked`) | `OpenOutM`, `SoundOpenM`, `OpenOutWM`, `SoundOpenWCM` |

At `HashModel.deployed` each is its deployed statement (`gkrOutM_deployed`, `soundGkr_of_model`,
…). The callees that do not hash (`certify_placement`, `check_opening_terminal`, the logs and
powers) need no new statement: their relations are the deployed ones under every semantics
(`ExtractB.relB_vsFree`), so `SoundPlace`, `HypKappa` and `SoundTerm` are used as they are.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable (M : HashModel)

/-! ## Runs with openings and roots -/

/-- **`RunsWith` over the model**: `p` runs from the chain state `cv` and the roots `roots`,
reading exactly the stream words `xs` and the openings `os`, to `a`, the state `cv'` and the roots
`roots'`, every hash answered by the model, on any stream and openings continuing them. -/
def RunsWithM {α : Type} (p : Prog α) (cv : Digest) (xs : List E) (os : List Opening)
    (roots : List (Digest × ℕ × ℕ)) (a : α) (cv' : Digest) (roots' : List (Digest × ℕ × ℕ)) :
    Prop :=
  ∀ (rest : List E) (orest : List Opening),
    runM M p ⟨cv, xs ++ rest, os ++ orest, roots⟩ = some (some (a, ⟨cv', rest, orest, roots'⟩))

/-- `ev` takes `value` for the bytecode at `point`, consuming nothing, over the model. -/
def BytecodeAtM (ev : Evaluations) (words : List K) (point : List E) (value : E) : Prop :=
  ∀ s, runM M (ev.bytecode words point) s = some (some (value, s))

/-- `ev` takes `value` for the matrices at the lincheck's weights, consuming nothing, over the
model. -/
def MatricesAtM (ev : Evaluations) (alpha zSkip : E) (chiIn chiInPrime slices : List E)
    (value : E) : Prop :=
  ∀ s, runM M (ev.matrices alpha zSkip chiIn chiInPrime slices) s = some (some (value, s))

/-! ## The callees -/

section Callees

variable (bytecode : List K)
  (TCtx : Reader → Layout → BusResult → List ColumnClaim → List E → Prop) (rd : Reader)

/-- **`GkrOut` over the model**: GKR's run with every hash answered. -/
def GkrOutM (fs0 fs1 cur gmu zeta : E) (rets : List E) : Prop :=
  ∃ (cv : Digest) (depth : ℕ) (xs : List E) (r : E × List E × List E) (cv' : Digest),
    (fs0, fs1) = digestScalars cv ∧ gmu = gen ^ depth ∧ depth < 33 ∧
    ReadsAt rd cur xs ∧ RunsToM M (gkrPhase depth) cv xs r cv' ∧ r.2.1.length = depth ∧
    r.2.2.length = 3 ∧ ReadsAt rd zeta r.2.1 ∧
    rets = [(digestScalars cv').1, (digestScalars cv').2, cur * gen ^ xs.length] ++ r.2.2

/-- **`verify_bus_gkr` is sound over the model.** -/
def SoundGkrM : Prop :=
  ∀ fs0 fs1 cur gmu zeta rets,
    coreProgram.RelB M.sem rd "verify_bus_gkr" [fs0, fs1, cur, gmu, zeta] rets →
      GkrOutM M rd fs0 fs1 cur gmu zeta rets

/-- **`TablesOut` over the model**: the tables' run with every hash answered, for every `ev`
taking `bv` for the bytecode over the model. -/
def TablesOutM (pi : Digest) (logMem : ℕ) (alphas point values : List E) :
    List E → List E → Prop
  | [fs0, fs1, cur, _, _, zeta, gmu, dims, rows, _, _, _, beta, pool, cplen, chi, _, _, _],
    [fs0', fs1', cur', gzcn, bv, rm] =>
      ∃ (cv : Digest) (xs : List E) (cv' : Digest) (rowsN : List ℕ) (bus : BusResult)
          (claims : List ColumnClaim), (fs0, fs1) = digestScalars cv ∧ rowsN.length = 6 ∧
        ReadsAt rd rows (rowsN.map eOfNat) ∧
        ReadsAt rd dims (gen ^ logMem :: rowsN.map fun n ↦ gen ^ log2Ceil n) ∧
        (∀ n ∈ rowsN, log2Ceil n < 29) ∧ ReadsAt rd cur xs ∧
        (∀ ev, BytecodeAtM M ev bytecode
            (point.take (layoutOf bytecode logMem rowsN).logBytecode ++ alphas) bv →
          RunsToM M (tablesSeg ev (layoutOf bytecode logMem rowsN) pi alphas beta point values) cv
            xs (bus, claims) cv') ∧
        claims.length = nClaims ∧ ReadsAt rd pool (claims.map (·.value)) ∧
        TCtx rd (layoutOf bytecode logMem rowsN) bus claims [zeta, chi, rm, gmu, gzcn, cplen] ∧
        (fs0', fs1') = digestScalars cv' ∧ cur' = cur * gen ^ xs.length
  | _, _ => False

/-- **`verify_tables` is sound over the model.** -/
def SoundTablesM : Prop :=
  ∀ lp pi logMem alphas point values args rets,
    TablesPre rd lp pi logMem alphas point values args →
    coreProgram.RelB M.sem rd "verify_tables" args rets →
      TablesOutM M bytecode TCtx rd pi logMem alphas point values args rets

/-- **`FlockOut` over the model**: Flock's run with every hash answered, for every `ev` taking
`mv` for the matrices over the model. -/
def FlockOutM (τ : ℕ) (fs0 fs1 cur zchis lrs zpart : E) (rets : List E) : Prop :=
  ∃ (cv : Digest) (xs : List E) (cv' : Digest) (zSkip alpha mv : E) (chi rcs s : List E),
    (fs0, fs1) = digestScalars cv ∧
    ReadsAt rd cur xs ∧ chi.length = 8 + τ ∧ rcs.length = 8 ∧ s.length = 64 ∧
    ReadsAt rd zchis chi ∧ ReadsAt rd lrs rcs ∧ ReadsAt rd zpart s ∧
    (∀ ev, MatricesAtM M ev alpha zSkip (chi.take 8) rcs.reverse s mv →
      RunsToM M (verifyFlock ev (blake2sR1csLogSize + τ)) cv xs (rcs.reverse ++ chi.drop 8, s)
        cv') ∧
    rets = [(digestScalars cv').1, (digestScalars cv').2, cur * gen ^ xs.length, zSkip, alpha, mv]

/-- **`verify_flock` is sound over the model**, for a BLAKE2s table of log-height `τ < 29`. -/
def SoundFlockM : Prop :=
  ∀ τ fs0 fs1 cur zchis lrs zpart rets, τ < 29 →
    coreProgram.RelB M.sem rd "verify_flock" [fs0, fs1, cur, gen ^ τ, zchis, lrs, zpart] rets →
      FlockOutM M rd τ fs0 fs1 cur zchis lrs zpart rets

/-- **`OpenOutW` over the model**: the stacked opening's run at the openings `os`, every hash
(the transcript's and the openings' paths) answered. -/
def OpenOutWM (μ r : ℕ) (root : Digest) (fs0 fs1 target cur : E) (rets : List E)
    (os : List Opening) : Prop :=
  ∃ (cv : Digest) (xs : List E) (w : WhirEnd) (cv' : Digest)
    (roots' : List (Digest × ℕ × ℕ)), (fs0, fs1) = digestScalars cv ∧ ReadsAt rd cur xs ∧
    RunsWithM M (whirOpen μ r target) cv xs os [(root, stackShape μ r)] w cv' roots' ∧
    ∃ pt, rets = [w.target, pt, w.inner, w.residual] ∧
      ReadsAt rd pt (w.point ++ List.replicate (pointCap - w.point.length) 0) ∧ w.point.length = μ

/-- **`OpenOut` over the model**: some openings over which `OpenOutWM` holds. -/
def OpenOutM (μ r : ℕ) (root : Digest) (fs0 fs1 target cur : E) (rets : List E) : Prop :=
  ∃ os, OpenOutWM M rd μ r root fs0 fs1 target cur rets os

/-- **`open_stacked` is sound over the model** at every candidate. -/
def SoundOpenM : Prop :=
  ∀ μ r, 22 ≤ μ → μ ≤ 28 → 1 ≤ r → r ≤ 4 →
    ∀ (root : Digest) fs0 fs1 target root0 root1 cur rets, (root0, root1) = digestScalars root →
      coreProgram.RelB M.sem rd (openName μ r) [fs0, fs1, target, root0, root1, cur] rets →
        OpenOutM M rd μ r root fs0 fs1 target cur rets

/-- **`open_stacked` is sound over the model with the openings `wO`**, over the call relation
`C`. -/
def SoundOpenWCM (C : CallRel) (wO : String → List E → List E → List Opening) : Prop :=
  ∀ μ r, 22 ≤ μ → μ ≤ 28 → 1 ≤ r → r ≤ 4 →
    ∀ (root : Digest) fs0 fs1 target root0 root1 cur rets, (root0, root1) = digestScalars root →
      C (openName μ r) [fs0, fs1, target, root0, root1, cur] rets →
        OpenOutWM M rd μ r root fs0 fs1 target cur rets
          (wO (openName μ r) [fs0, fs1, target, root0, root1, cur] rets)

end Callees

/-! ## At the deployed model -/

section Deployed

variable {bytecode : List K} {TCtx : Reader → Layout → BusResult → List ColumnClaim → List E → Prop}
  {rd : Reader}

theorem runsWithM_deployed {α : Type} {p : Prog α} {cv : Digest} {xs : List E}
    {os : List Opening} {roots : List (Digest × ℕ × ℕ)} {a : α} {cv' : Digest}
    {roots' : List (Digest × ℕ × ℕ)} :
    RunsWithM HashModel.deployed p cv xs os roots a cv' roots' ↔
      RunsWith p cv xs os roots a cv' roots' := by
  simp only [RunsWithM, RunsWith, runM_deployed, Option.some.injEq]

theorem bytecodeAtM_deployed {ev : Evaluations} {words : List K} {point : List E} {value : E} :
    BytecodeAtM HashModel.deployed ev words point value ↔ BytecodeAt ev words point value := by
  simp only [BytecodeAtM, BytecodeAt, runM_deployed, Option.some.injEq]

theorem matricesAtM_deployed {ev : Evaluations} {alpha zSkip : E}
    {chiIn chiInPrime slices : List E} {value : E} :
    MatricesAtM HashModel.deployed ev alpha zSkip chiIn chiInPrime slices value ↔
      MatricesAt ev alpha zSkip chiIn chiInPrime slices value := by
  simp only [MatricesAtM, MatricesAt, runM_deployed, Option.some.injEq]

theorem gkrOutM_deployed {fs0 fs1 cur gmu zeta : E} {rets : List E} :
    GkrOutM HashModel.deployed rd fs0 fs1 cur gmu zeta rets ↔ GkrOut rd fs0 fs1 cur gmu zeta rets := by
  simp only [GkrOutM, GkrOut, runsToM_deployed]

/-- `SoundGkrM` at the deployed model is `SoundGkr`. -/
theorem soundGkrM_deployed : SoundGkrM HashModel.deployed rd ↔ SoundGkr rd := by
  simp only [SoundGkrM, SoundGkr, gkrOutM_deployed]
  rw [show HashModel.deployed.sem = blakeDeployed from rfl, relB_deployed]

theorem tablesOutM_deployed {pi : Digest} {logMem : ℕ} {alphas point values : List E}
    {args rets : List E} :
    TablesOutM HashModel.deployed bytecode TCtx rd pi logMem alphas point values args rets ↔
      TablesOut bytecode TCtx rd pi logMem alphas point values args rets := by
  unfold TablesOutM TablesOut
  split <;> simp only [bytecodeAtM_deployed, runsToM_deployed]

/-- `SoundTablesM` at the deployed model is `SoundTables`. -/
theorem soundTablesM_deployed :
    SoundTablesM HashModel.deployed bytecode TCtx rd ↔ SoundTables bytecode TCtx rd := by
  simp only [SoundTablesM, SoundTables, tablesOutM_deployed]
  rw [show HashModel.deployed.sem = blakeDeployed from rfl, relB_deployed]

theorem flockOutM_deployed {τ : ℕ} {fs0 fs1 cur zchis lrs zpart : E} {rets : List E} :
    FlockOutM HashModel.deployed rd τ fs0 fs1 cur zchis lrs zpart rets ↔
      FlockOut rd τ fs0 fs1 cur zchis lrs zpart rets := by
  simp only [FlockOutM, FlockOut, matricesAtM_deployed, runsToM_deployed]

/-- `SoundFlockM` at the deployed model is `SoundFlock`. -/
theorem soundFlockM_deployed : SoundFlockM HashModel.deployed rd ↔ SoundFlock rd := by
  simp only [SoundFlockM, SoundFlock, flockOutM_deployed]
  rw [show HashModel.deployed.sem = blakeDeployed from rfl, relB_deployed]

theorem openOutWM_deployed {μ r : ℕ} {root : Digest} {fs0 fs1 target cur : E} {rets : List E}
    {os : List Opening} :
    OpenOutWM HashModel.deployed rd μ r root fs0 fs1 target cur rets os ↔
      OpenOutW rd μ r root fs0 fs1 target cur rets os := by
  simp only [OpenOutWM, OpenOutW, runsWithM_deployed]

theorem openOutM_deployed {μ r : ℕ} {root : Digest} {fs0 fs1 target cur : E} {rets : List E} :
    OpenOutM HashModel.deployed rd μ r root fs0 fs1 target cur rets ↔
      OpenOut rd μ r root fs0 fs1 target cur rets := by
  simp only [OpenOutM, openOutWM_deployed]
  exact ⟨fun ⟨_, h⟩ => h.openOut, fun h => h.exists_w⟩

/-- `SoundOpenM` at the deployed model is `SoundOpen`. -/
theorem soundOpenM_deployed : SoundOpenM HashModel.deployed rd ↔ SoundOpen rd := by
  simp only [SoundOpenM, SoundOpen, openOutM_deployed]
  rw [show HashModel.deployed.sem = blakeDeployed from rfl, relB_deployed]

/-- `SoundOpenWCM` at the deployed model is `SoundOpenWC`. -/
theorem soundOpenWCM_deployed {C : CallRel} {wO : String → List E → List E → List Opening} :
    SoundOpenWCM HashModel.deployed rd C wO ↔ SoundOpenWC rd C wO := by
  simp only [SoundOpenWCM, SoundOpenWC, openOutWM_deployed]

end Deployed

end
end LeanVM.Guest.B1.VerifySub
