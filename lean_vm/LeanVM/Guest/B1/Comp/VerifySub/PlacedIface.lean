/-
  LeanVM.Guest.B1.Comp.VerifySub.PlacedIface

  What `verify_sub`'s placed completeness over a completeness model assumes of its hashing
  callees: `CompleteIface.lean`'s placed shapes with the phases run over the model's answers.
-/

module

public import LeanVM.Guest.B1.VerifySub.CPlaced8
public import LeanVM.Guest.B1.VerifySub.StaticWS
public import LeanVM.Guest.B1.Comp.FreeTree
public import LeanVM.Guest.B1.Comp.VerifySub.Assemble

/-!
# `verify_sub`'s hashing callees, placed, over a completeness model

`CompleteIface.lean`'s `CompleteGkrAtW`, `CompleteTablesAtW`, `CompleteFlockAtW` and
`CompleteOpenAtB` over a `CompModel`: the phase runs over the model's answers (`RunsToM CM.hm`,
`BytecodeAtM`, `MatricesAtM`, `RunsWithM`), the trees valid under `CM.sem` (`CompleteAtWS`,
`CompleteAtBS`). Their callees' other groups prove them (Tables, Whir). `certify_placement` and
`check_opening_terminal` are free of `BLAKE2S` (`vsFree`): their deployed shapes serve
(`completeAtBS_of_freeOn`, `completeAtWS_of_freeOn`).

`VsWeightHypsS`: `VsWeightHyps` under `S` (`WeightLeB`), from `VsStatOkS` (`ofStat`).

At `CompModel.deployed` each deployed shape gives the model's (`….toC`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.E2E.Complete
open LeanVM.Guest.B1.Main (MemL)

@[expose] public section

section Placed

variable (CM : CompModel) (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (bytecode : List K)
  (TCtx : Reader → Layout → BusResult → List ColumnClaim → List E → Prop)
  {Θ : Type} (wt : Θ → String → ℕ)

/-- **`verify_bus_gkr`, placed, within weights, over the model** (`CompleteGkrAtW`). -/
def CompleteGkrAtWC (B : ℕ) (Bw : Θ → ℕ) : Prop :=
  ∀ (cv : Digest) (depth : ℕ) (xs : List E) (r : E × List E × List E) (cv' : Digest) (c z : ℕ)
    (Lin : Main.Layout), depth < 33 → RunsToM CM.hm (gkrPhase depth) cv xs r cv' →
    r.2.1.length = depth → r.2.2.length = 3 →
    (∀ rd, LowDef k rd → MemL rd Lin →
      ReadsAt rd (ofK (Parameters.gpow c)) xs ∧ ReadsAt rd (ofK (Parameters.gpow z)) r.2.1) →
    Main.CompleteAtWS CM.sem fs cert wt k "verify_bus_gkr" Lin [(digestScalars cv).1,
      (digestScalars cv).2, ofK (Parameters.gpow c), gen ^ depth, ofK (Parameters.gpow z)]
      (Returns ([(digestScalars cv').1, (digestScalars cv').2,
        ofK (Parameters.gpow c) * gen ^ xs.length] ++ r.2.2)) B Bw

/-- **`verify_tables`, placed, within weights, over the model** (`CompleteTablesAtW`). -/
def CompleteTablesAtWC (B : ℕ) (Bw : Θ → ℕ) : Prop :=
  ∀ (pi : Digest) (logMem : ℕ) (alphas point values : List E) (cv : Digest) (xs : List E)
    (cv' : Digest) (rowsN : List ℕ) (bus : BusResult) (claims : List ColumnClaim)
    (beta bv rm gzcn : E) (c z lp sq dims rows bk fpw pool cplen chi : ℕ) (Lin : Main.Layout),
    bytecode.length = 2 ^ 22 →
    point.length = (busLayout [0, logMem, 18] (layoutOf bytecode logMem rowsN).push).depth →
    point.length < 33 → gzcn = gen ^ (layoutOf bytecode logMem rowsN).tableLogHeights.foldl max 0 →
    16 ≤ logMem → logMem ≤ 32 → alphas.length = 4 → values.length = 3 →
    rowsN.length = 6 → (∀ n ∈ rowsN, log2Ceil n < 29) → claims.length = nClaims →
    (∀ ev, BytecodeAtM CM.hm ev bytecode
        (point.take (layoutOf bytecode logMem rowsN).logBytecode ++ alphas) bv →
      RunsToM CM.hm (tablesSeg ev (layoutOf bytecode logMem rowsN) pi alphas beta point values) cv xs
        (bus, claims) cv') →
    (∀ rd, LowDef k rd → MemL rd Lin →
      ReadsAt rd (ofK (Parameters.gpow c)) xs ∧ ReadsAt rd (ofK (Parameters.gpow z)) point ∧
      ExpTables rd (ofK (Parameters.gpow lp)) (ofK (Parameters.gpow sq)) ∧
      ReadsAt rd (ofK (Parameters.gpow rows)) (rowsN.map eOfNat) ∧
      ReadsAt rd (ofK (Parameters.gpow dims)) (gen ^ logMem :: rowsN.map fun n ↦ gen ^ log2Ceil n) ∧
      ReadsAt rd (ofK (Parameters.gpow bk))
        (blockKappas (gen ^ logMem) (rowsN.map fun n ↦ gen ^ log2Ceil n)) ∧
      ReadsAt rd (ofK (Parameters.gpow fpw)) (eqKernel alphas) ∧
      ReadsAt rd (ofK (Parameters.gpow pool)) (claims.map (·.value)) ∧
      TCtx rd (layoutOf bytecode logMem rowsN) bus claims [ofK (Parameters.gpow z),
        ofK (Parameters.gpow chi), rm, gen ^ point.length, gzcn, ofK (Parameters.gpow cplen)]) →
    Main.CompleteAtWS CM.sem fs cert wt k "verify_tables" Lin
      [(digestScalars cv).1, (digestScalars cv).2, ofK (Parameters.gpow c), (digestScalars pi).1,
        (digestScalars pi).2, ofK (Parameters.gpow z), gen ^ point.length,
        ofK (Parameters.gpow dims), ofK (Parameters.gpow rows), ofK (Parameters.gpow bk),
        ofK (Parameters.gpow sq), ofK (Parameters.gpow fpw), beta, ofK (Parameters.gpow pool),
        ofK (Parameters.gpow cplen), ofK (Parameters.gpow chi), values.getD 0 0, values.getD 1 0,
        values.getD 2 0]
      (Returns [(digestScalars cv').1, (digestScalars cv').2,
        ofK (Parameters.gpow c) * gen ^ xs.length, gzcn, bv, rm]) B Bw

/-- **`verify_flock`, placed, within weights, over the model** (`CompleteFlockAtW`). -/
def CompleteFlockAtWC (B : ℕ) (Bw : Θ → ℕ) : Prop :=
  ∀ (τ : ℕ) (cv : Digest) (xs : List E) (cv' : Digest) (zSkip alpha mv : E) (chi rcs s : List E)
    (c zc lr zp : ℕ) (Lin : Main.Layout), τ < 29 → chi.length = 8 + τ → rcs.length = 8 →
    s.length = 64 →
    (∀ ev, MatricesAtM CM.hm ev alpha zSkip (chi.take 8) rcs.reverse s mv →
      RunsToM CM.hm (verifyFlock ev (blake2sR1csLogSize + τ)) cv xs (rcs.reverse ++ chi.drop 8, s) cv') →
    (∀ rd, LowDef k rd → MemL rd Lin →
      ReadsAt rd (ofK (Parameters.gpow c)) xs ∧ ReadsAt rd (ofK (Parameters.gpow zc)) chi ∧
      ReadsAt rd (ofK (Parameters.gpow lr)) rcs ∧ ReadsAt rd (ofK (Parameters.gpow zp)) s) →
    Main.CompleteAtWS CM.sem fs cert wt k "verify_flock" Lin [(digestScalars cv).1,
      (digestScalars cv).2, ofK (Parameters.gpow c), gen ^ τ, ofK (Parameters.gpow zc),
      ofK (Parameters.gpow lr), ofK (Parameters.gpow zp)]
      (Returns [(digestScalars cv').1, (digestScalars cv').2,
        ofK (Parameters.gpow c) * gen ^ xs.length, zSkip, alpha, mv]) B Bw

/-- **`open_stacked`, placed, bounded, over the model** (`CompleteOpenAtB`): on a run of
`whirOpen μ r target` over the model's answers and the agreement `CapOk` at the cap. -/
def CompleteOpenAtBC (CapOk : ℕ → ℕ → Digest → Digest → List E → List Opening → E → Prop)
    (B : ℕ) : Prop :=
  ∀ μ r, 22 ≤ μ → μ ≤ 28 → 1 ≤ r → r ≤ 4 →
    ∀ (root cv : Digest) (xs : List E) (os : List Opening) (w : WhirEnd) (cv' : Digest)
      (roots' : List (Digest × ℕ × ℕ)) (target : E) (c : ℕ) (Lin : Main.Layout),
      RunsWithM CM.hm (whirOpen μ r target) cv xs os [(root, stackShape μ r)] w cv' roots' →
      CapOk μ r root cv xs os target →
      (∀ rd, LowDef k rd → MemL rd Lin → ReadsAt rd (ofK (Parameters.gpow c)) xs) →
      CompleteAtBS CM.sem fs cert k (openName μ r) Lin [(digestScalars cv).1, (digestScalars cv).2,
        target, (digestScalars root).1, (digestScalars root).2, ofK (Parameters.gpow c)]
        (fun rets Lout =>
          ∃ b, rets = [w.target, ofK (Parameters.gpow b), w.inner, w.residual] ∧
            Lout = [(b, w.point ++ List.replicate (pointCap - w.point.length) 0)]) B

end Placed

/-! ## At the deployed model -/

section Deployed

variable {fs : String → ℕ} {cert : String → V → ℕ} {k : ℕ} {bytecode : List K}
  {TCtx : Reader → Layout → BusResult → List ColumnClaim → List E → Prop}
  {Θ : Type} {wt : Θ → String → ℕ}

theorem CompleteGkrAtW.toC {B : ℕ} {Bw : Θ → ℕ} (h : CompleteGkrAtW fs cert k wt B Bw) :
    CompleteGkrAtWC CompModel.deployed fs cert k wt B Bw := by
  intro cv depth xs r cv' c z Lin hd hr h1 h2 hm
  exact completeAtWS_deployed.mpr (h cv depth xs r cv' c z Lin hd (runsToM_hm_deployed.mp hr) h1 h2 hm)

theorem CompleteTablesAtW.toC {B : ℕ} {Bw : Θ → ℕ} (h : CompleteTablesAtW fs cert k bytecode TCtx wt B Bw) :
    CompleteTablesAtWC CompModel.deployed fs cert k bytecode TCtx wt B Bw := by
  intro pi logMem alphas point values cv xs cv' rowsN bus claims beta bv rm gzcn c z lp sq dims rows
    bk fpw pool cplen chi Lin h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hrun hm
  exact completeAtWS_deployed.mpr (h pi logMem alphas point values cv xs cv' rowsN bus claims beta bv
    rm gzcn c z lp sq dims rows bk fpw pool cplen chi Lin h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    (fun ev hev => runsToM_hm_deployed.mp (hrun ev (bytecodeAtM_deployed.mpr hev))) hm)

theorem CompleteFlockAtW.toC {B : ℕ} {Bw : Θ → ℕ} (h : CompleteFlockAtW fs cert k wt B Bw) :
    CompleteFlockAtWC CompModel.deployed fs cert k wt B Bw := by
  intro τ cv xs cv' zSkip alpha mv chi rcs s c zc lr zp Lin h1 h2 h3 h4 hrun hm
  exact completeAtWS_deployed.mpr (h τ cv xs cv' zSkip alpha mv chi rcs s c zc lr zp Lin h1 h2 h3 h4
    (fun ev hev => runsToM_hm_deployed.mp (hrun ev (matricesAtM_deployed.mpr hev))) hm)

theorem CompleteOpenAtB.toC {CapOk : ℕ → ℕ → Digest → Digest → List E → List Opening → E → Prop}
    {B : ℕ} (h : CompleteOpenAtB fs cert k CapOk B) :
    CompleteOpenAtBC CompModel.deployed fs cert k CapOk B := by
  intro μ r h1 h2 h3 h4 root cv xs os w cv' roots' target c Lin hrun hcap hm
  exact completeAtBS_deployed.mpr (h μ r h1 h2 h3 h4 root cv xs os w cv' roots' target c Lin
    (runsWithM_deployed.mp hrun) hcap hm)

end Deployed

/-! ## The statically bounded callees' weights under `S` -/

section Weights

variable {S : BlakeSem} {Θ : Type}

variable (S) in
/-- **`VsWeightHyps` under `S`**: the weights of `verify_sub`'s statically bounded callees at the
frame weights `w θ`, every tree valid under `S` within them. -/
structure VsWeightHypsS (w : Θ → String → ℕ) : Type where
  gpw : Θ → ℕ
  gpw_le : ∀ θ, WeightLeB S coreProgram (w θ) "g_power_of_word__L6" fun _ => gpw θ
  l2a : Θ → ℕ
  l2a_le : ∀ θ, WeightLeB S coreProgram (w θ) "log2_ceil_in_the_exponent__L0_L34" fun _ => l2a θ
  l2b : Θ → ℕ
  l2b_le : ∀ θ, WeightLeB S coreProgram (w θ) "log2_ceil_in_the_exponent__L15_L34" fun _ => l2b θ
  ac : Θ → ℕ
  ac_le : ∀ θ, WeightLeB S coreProgram (w θ) "assert_canonical" fun _ => ac θ
  pl : Θ → ℕ
  pl_le : ∀ θ, WeightLeB S coreProgram (w θ) "certify_placement" fun _ => pl θ
  os : Θ → ℕ
  os_le : ∀ θ μ r, 22 ≤ μ → μ ≤ 28 → 1 ≤ r → r ≤ 4 →
    WeightLeB S coreProgram (w θ) (openName μ r) fun _ => os θ

/-- The hypotheses from a weight of each callee at every `w θ` under `S`. -/
def VsWeightHypsS.ofStat {w : Θ → String → ℕ} (c : Θ → VsStat) (h : ∀ θ, VsStatOkS S (w θ) (c θ)) :
    VsWeightHypsS S w :=
  ⟨fun θ => (c θ).gpw, fun θ => (h θ).gpw, fun θ => (c θ).l2a, fun θ => (h θ).l2a, fun θ => (c θ).l2b,
    fun θ => (h θ).l2b, fun θ => (c θ).ac, fun θ => (h θ).ac, fun θ => (c θ).pl, fun θ => (h θ).pl,
    fun θ => (c θ).os, fun θ => (h θ).os⟩

/-- At the deployed semantics, the deployed hypotheses. -/
def VsWeightHyps.toS {w : Θ → String → ℕ} (H : VsWeightHyps w) : VsWeightHypsS blakeDeployed w :=
  ⟨H.gpw, fun θ => by rw [weightLeB_deployed]; exact H.gpw_le θ, H.l2a,
    fun θ => by rw [weightLeB_deployed]; exact H.l2a_le θ, H.l2b,
    fun θ => by rw [weightLeB_deployed]; exact H.l2b_le θ, H.ac,
    fun θ => by rw [weightLeB_deployed]; exact H.ac_le θ, H.pl,
    fun θ => by rw [weightLeB_deployed]; exact H.pl_le θ, H.os,
    fun θ μ r h1 h2 h3 h4 => by rw [weightLeB_deployed]; exact H.os_le θ μ r h1 h2 h3 h4⟩

/-- A call before the dispatch: its callee's weight (`vsBdW`). -/
def vsBdWS (w : Θ → String → ℕ) (H : VsWeightHypsS S w) (Bsw : VsBoundsW Θ) (k : Kid) (θ : Θ) : ℕ :=
  if k.f = "g_power_of_word__L6" then H.gpw θ
  else if k.f = "log2_ceil_in_the_exponent__L0_L34" then H.l2a θ
  else if k.f = "assert_canonical" then H.ac θ
  else if k.f = "verify_bus_gkr" then Bsw.gkr θ
  else if k.f = "verify_tables" then Bsw.tab θ
  else if k.f = "verify_flock" then Bsw.fl θ
  else if k.f = "__loop84" then 64 * (2 * w θ "__loop84")
  else if k.f = "__loop85" then 28 * (2 * w θ "__loop85")
  else if k.f = "certify_placement" then H.pl θ
  else H.l2b θ

/-- The calls before the dispatch: their callees' weights (`vsKidsBoundW`). -/
def vsKidsBoundWS (w : Θ → String → ℕ) (H : VsWeightHypsS S w) (Bsw : VsBoundsW Θ) (θ : Θ) : ℕ :=
  2 * H.gpw θ + H.l2a θ + 2 * H.ac θ + Bsw.gkr θ + Bsw.tab θ + Bsw.fl θ + 64 * (2 * w θ "__loop84") +
    28 * (2 * w θ "__loop85") + H.pl θ + H.l2b θ

/-- **`verify_sub`'s weight under `S`** (`vsBoundW`): its frame's, its callees'. -/
def vsBoundWS (w : Θ → String → ℕ) (H : VsWeightHypsS S w) (Bsw : VsBoundsW Θ) (θ : Θ) : ℕ :=
  w θ "verify_sub" + vsKidsBoundWS w H Bsw θ + H.os θ + Bsw.term θ

theorem vsBoundWS_toS {w : Θ → String → ℕ} (H : VsWeightHyps w) (Bsw : VsBoundsW Θ) (θ : Θ) :
    vsBoundWS w H.toS Bsw θ = vsBoundW w H Bsw θ := rfl

theorem vsBoundWS_ofStat {w : Θ → String → ℕ} (c : Θ → VsStat) (h : ∀ θ, VsStatOkS S (w θ) (c θ))
    (Bsw : VsBoundsW Θ) (θ : Θ) :
    vsBoundWS w (VsWeightHypsS.ofStat c h) Bsw θ = w θ "verify_sub" + (2 * (c θ).gpw + (c θ).l2a +
      2 * (c θ).ac + Bsw.gkr θ + Bsw.tab θ + Bsw.fl θ + 64 * (2 * w θ "__loop84") +
      28 * (2 * w θ "__loop85") + (c θ).pl + (c θ).l2b) + (c θ).os + Bsw.term θ := rfl

end Weights

end
end LeanVM.Guest.B1.VerifySub
