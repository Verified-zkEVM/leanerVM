/-
  LeanVM.Guest.B1.Terminal.Interface

  B1 of `check_opening_terminal`: the stacked opening's transparent weight (V:1453-1459,
  1514-1517), what `verify_sub` hands the terminal, and the statement of its soundness.
-/

module

public import LeanVM.Guest.B1.Tables.Interface
public import LeanVM.Guest.B1.Placement.Interface
public import LeanVM.Guest.B1.KeccakGkr.Interface

/-!
# `check_opening_terminal` (TRIAGE G #70): the interface

`check_opening_terminal(zeta, chi, rm, g_bus_mu, g_zc_n, g_log_mem, tau_keccak_g, claim_cplen_g,
lam_out, lam_pool, col_offsets, col_kappas, z_vals, c_table, point, point1, inner_total,
yr_at_tail, sumcheck_target)` (G:3078-3144) evaluates the stacked opening's transparent weight at
the WHIR terminal point and checks the terminal (`whirLevels`' last `require`, V:1195-1198):
`(inner + basis(point)) · residual = target`, `basis` the weight `verifyStackedOpening` hands WHIR
(V:1453-1459) for the claims `verifyExecution` opens (V:1514-1517): the ring switch's, then every
column claim but the `KECCAK` output lanes' (which the Keccak reduction consumed, `keccakPhase`,
V:1505-1509), then the reduction's claim on its committed outputs, batched by the powers of one
challenge `λ`.

* `openedClaims claims outs`: the column claims the opening batches;
* `stackWeight layout claims ringPoint coeffs lam x`: `basis(x)`;
* `TermPre`: what `verify_sub` establishes before the call: `verify_tables`' context (`TCtx`) and
  `certify_placement`'s (`PCtx`, `KappasBelow`), the layout's placement being `placementsOf`'s, the
  powers of `λ` in `lam_pool` and `lam_out`, the outputs' claim's point at `z_vals` and the ring
  switch's point at `z_vals·g^39`, the ring map's coefficients at `c_table`, the terminal point at
  `point` (zero-padded to `SIZE_BITS + QKECCAK_SLOT_LOG = 40` words) and `1 + point` at `point1`;
  the memory nonempty (`1 ≤ log_mem`, `buildLayout` gives `16 ≤ log_mem`) and the bus point at most
  `40` long (`eq_prefix_chain`'s range);
* `check_opening_terminal_Spec`: under `TermPre`, the relation gives the terminal check.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The opening's weight -/

/-- The column claims the stacked opening batches after the Keccak phase (V:1505-1509): every
claim but the output lanes', then the Keccak reduction's. -/
def openedClaims (claims outs : List ColumnClaim) : List ColumnClaim :=
  claims.filter (fun c ↦ c.column ∉ keccakOutputColumns) ++ outs

/-- The stacked opening's transparent weight at `x` (V:1453-1459, 1514-1517): the ring switch's
claim (`ringSwitchClaim`, its weight `ringWeight ringPoint · coeffs`), then every column claim on
the stack, batched by the powers of `lam`. -/
def stackWeight (layout : Layout) (claims : List ColumnClaim) (ringPoint coeffs : List E)
    (lam : E) (x : List E) : E :=
  let all := ringSwitchClaim layout 0 (fun rPrime ↦ ringWeight ringPoint rPrime coeffs) ::
    claims.map (·.onStack layout)
  dot (powers lam all.length) (all.map fun c ↦ c.1 x)

/-! ## The terminal's precondition -/

/-- `SIZE_BITS + QKECCAK_SLOT_LOG`: the terminal point's buffers' length. -/
abbrev termPointCap : ℕ := 40

/-- The number of pooled claims before claim `j` that the opening batches (not an output
lane's): claim `j`'s power of `λ` is `λ^(1 + poolRank j)`. -/
def poolRank (j : ℕ) : ℕ :=
  ((List.range j).filter fun i ↦ Tables.claimColumns.getD i 0 ∉ keccakOutputColumns).length

/-- The terminal point, zero-padded to `40` words. -/
def padPoint (x : List E) : List E := x ++ List.replicate (termPointCap - x.length) 0

/-- **What `verify_sub` establishes before `check_opening_terminal`**, for the layout, the bus
result and the pooled claims of `verify_tables`, the Keccak reduction's claim on its outputs
`out`, the batching challenge `lam`, the ring switch's point and coefficients and the WHIR
terminal point `x`. -/
def TermPre (rd : Reader) (layout : Layout) (bus : BusResult) (claims : List ColumnClaim)
    (out : ColumnClaim) (lam : E) (ringPoint coeffs x : List E) : List E → Prop
  | [zeta, chi, rm, gmu, gzcn, glm, gtau, cplen, lamOut, lamPool, off, kap, zv, ct, pt, pt1, _,
      _, _] =>
      let kappas := columnKappas layout.logMemory layout.logBytecode layout.tableLogHeights
      let τ := layout.tableLogHeights.getD opKeccak 0
      Tables.TCtx rd layout bus claims [zeta, chi, rm, gmu, gzcn, cplen] ∧
      Tables.PCtx rd kappas off kap ∧ Tables.KappasBelow rd kap ∧
      layout.placements = (placementsOf kappas).1 ∧ layout.stackLog = (placementsOf kappas).2 ∧
      layout.stackLog ≤ 28 ∧ 1 ≤ layout.logMemory ∧ layout.logMemory ≤ 32 ∧
      bus.point.length ≤ 40 ∧ layout.tableLogHeights.length = 6 ∧
      (∀ h ∈ layout.tableLogHeights, h < 29) ∧
      glm = gen ^ layout.logMemory ∧ gtau = gen ^ τ ∧
      (∀ j < Tables.nClaims, Tables.claimColumns.getD j 0 ∉ keccakOutputColumns →
        LoadHolds rd lamPool j (lam ^ (1 + poolRank j))) ∧
      lamOut = lam ^ (1 + poolRank Tables.nClaims) ∧
      out.column = qkeccak ∧ out.point.length = τ + qkeccakSlotBits ∧ ReadsAt rd zv out.point ∧
      ringPoint.length = τ + qkeccakSlotBits ∧ ReadsAt rd (zv * gen ^ qkeccakVarsCap) ringPoint ∧
      coeffs.length = kBits ∧ ReadsAt rd ct coeffs ∧
      x.length = layout.stackLog ∧ ReadsAt rd pt (padPoint x) ∧
      ReadsAt rd pt1 ((padPoint x).map (1 + ·))
  | _ => False

/-- **`check_opening_terminal`'s outcome**: it returns nothing, and for every reading of its
arguments that `TermPre` allows, the WHIR terminal holds: `(inner + basis(x))·residual = target`,
the last three arguments being `inner`, `residual` and `target`. -/
def MeaningTerminal (rd : Reader) (args rets : List E) : Prop :=
  rets = [] ∧ ∀ (layout : Layout) (bus : BusResult) (claims : List ColumnClaim) (out : ColumnClaim)
    (lam : E) (ringPoint coeffs x : List E),
    TermPre rd layout bus claims out lam ringPoint coeffs x args →
      (args.getD 16 0 + stackWeight layout (openedClaims claims [out]) ringPoint coeffs lam x) *
        args.getD 17 0 = args.getD 18 0

/-- **`check_opening_terminal` is sound** (G:3078-3144; TRIAGE #70). -/
def check_opening_terminal_Spec (rd : Reader) : Prop :=
  ∀ args rets, coreProgram.Rel rd "check_opening_terminal" args rets → MeaningTerminal rd args rets

end
end LeanVM.Guest.B1.VerifySub
