/-
  LeanVM.Guest.B1.Tables.VtC.ADefs

  `verify_tables`' honest memory and oracle: the caller's buffers, its own buffers in allocation
  order at the bump allocator's positions, and the oracle's words.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.AHon
public import LeanVM.Guest.B1.Tables.VtC.ABuf
public import LeanVM.Guest.B1.Tables.VtC.BMain
public import LeanVM.Guest.B1.Selectors.LayoutBasic
public import LeanVM.Guest.Memory.Straight
public import LeanVM.Guest.B1.Tables.VtC.FData

/-!
# The honest memory

`VtBases`: the caller's buffers' addresses (the cursor, `zeta`, `dims_g`, `table_rows`,
`block_kappa`, `g_squares`, `fp_w`, `claim_pool`, `claim_cplen_g`, `chi`) and the first word of
`verify_tables`' own buffers. `VtHonest.args`: the 22 arguments. `VtHonest.linL`: the caller's
buffers' honest words. `vtAllocVars`: the 110 allocations' values, in order (`vt_allocs`, by the
kernel); `VtHonest.sizes`, `VtHonest.ownW`: their sizes and honest words; `VtHonest.ownL`: them
at the bump allocator's positions. `VtWOk`: what the oracle answers (the allocations' pointers,
the witnesses, the callees' returns).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (termsPure blockSel)

@[expose] public section

/-- The caller's buffers' addresses and the first word of the function's own. -/
structure VtBases where
  cur : ℕ
  zeta : ℕ
  dims : ℕ
  rows : ℕ
  bk : ℕ
  sq : ℕ
  fpw : ℕ
  pool : ℕ
  cplen : ℕ
  chi : ℕ
  own : ℕ

/-- The allocations' values, in order. -/
def vtAllocVars : List ℕ :=
  [30, 31, 185, 2732, 2767, 2769, 2770, 2851] ++ vtFwV.map (· + 6) ++
    (List.range 51).map (fun i ↦ (vtPushSel.getD i default).2.2.1 + 6) ++
    (List.range 45).map (fun i ↦ (vtCountSel.getD i default).2.2.1 + 6) ++ [5912, 5915, 5936]

theorem vtAllocVars_length : vtAllocVars.length = 110 := by decide

/-- **The allocations, by the kernel.** -/
theorem vt_allocs : (vtPre.filterMap LeanVM.Guest.Memory.Stmt.allocSz).map (fun x ↦ x.1) =
    vtAllocVars.map V.n := by decide +kernel

namespace VtHonest

variable (H : VtHonest) (B : VtBases)

/-- `|point|`. -/
def μ : ℕ := H.point.length

/-- Table `t`'s height. -/
def τ (t : ℕ) : ℕ := vtHt H.rows t

/-- Block `b`'s log-size. -/
def κ (b : ℕ) : ℕ := vtKap H.lm H.τ b

/-- The push side's offsets. -/
def offP : List ℕ := (stackOffsets (vtSizesP H.lm H.τ)).1

/-- The count side's offsets. -/
def offC : List ℕ := (stackOffsets (vtSizesC H.τ)).1

/-- The arguments. -/
noncomputable def args : List E :=
  [H.f.getD 0 0, H.f.getD 1 0, H.f.getD 2 0, H.f.getD 3 0, H.f.getD 4 0, ofK (gpow B.cur),
    (digestScalars H.pi).1, (digestScalars H.pi).2, ofK (gpow B.zeta), gen ^ H.μ,
    ofK (gpow B.dims), ofK (gpow B.rows), ofK (gpow B.bk), ofK (gpow B.sq), ofK (gpow B.fpw),
    H.beta, ofK (gpow B.pool), ofK (gpow B.cplen), ofK (gpow B.chi), H.values.getD 0 0,
    H.values.getD 1 0, H.values.getD 2 0]

/-- `dims_g`'s words. -/
noncomputable def dimsW : List E := gen ^ H.lm :: (vtTauList H.τ).map (gen ^ ·)

/-- `block_kappa`'s words. -/
noncomputable def bkW : List E := blockKappaWords (gen ^ H.lm) ((vtTauList H.τ).map (gen ^ ·))

/-- The stream words. -/
def curW : List E := H.xs5 ++ H.xsR ++ H.evsT.flatten

/-- The public input's claims' values. -/
noncomputable def pcW : List E :=
  ([0, 1, 2] : List (Fin 3)).map fun limb ↦
    multilinearEval [ofK ((digestScalars H.pi).1.limb limb),
      ofK ((digestScalars H.pi).2.limb limb)] [H.rm]

/-- `claim_pool`'s words. -/
noncomputable def poolW : List E := H.xs5 ++ H.evsT.flatten ++ H.pcW

/-- `claim_cplen_g`'s words. -/
noncomputable def cplenW : List E :=
  [gen ^ H.lm, gen ^ H.lm, gen ^ H.lm, gen ^ H.lm, gen ^ 19] ++
    (List.range 157).map fun k ↦ gen ^ vtHt H.rows (vtEvTab k)

/-- `chi`'s words: the challenges, last first. -/
noncomputable def chiW : List E := zcChis H.cap0 H.target H.xsR H.n

/-- **The caller's buffers.** -/
noncomputable def linL : TLay :=
  [(B.cur, H.curW), (B.zeta, H.point), (B.dims, H.dimsW), (B.rows, H.rows.map eOfNat),
    (B.bk, H.bkW), (B.sq, gSquaresList), (B.fpw, eqKernel H.alphas), (B.pool, H.poolW),
    (B.cplen, H.cplenW), (B.chi, H.chiW)]

/-- The own buffers' sizes, in allocation order. -/
def sizes : List ℕ :=
  [153, 153, 153, 34, H.μ, 1728, 864, 153] ++ List.replicate 99 34 ++
    [7 * (H.n + 1), H.n + 1, H.n + 1]

/-- **The own buffers' honest words**, in allocation order. -/
noncomputable def ownW : List (List E) :=
  [vtSortW H.κ, vtSideW, vtOffW H.κ, vtIdxcW, H.point.map (1 + ·), vtShEqW H.point H.τ,
    vtShGW H.point H.τ, vtIdxBufW H.point H.lm] ++
    (List.range 54).map (fun i ↦ offBits (H.offP.getD i 0)) ++
    (List.range 45).map (fun i ↦ offBits (H.offC.getD i 0)) ++
    [zcRoundsW H.cap0 H.target (ofK (gpow B.cur) * gen ^ 5) H.xsR H.n,
      zcCprodW H.cap0 H.target H.xsR H.n,
      (List.range (H.n + 1)).map (prefixProd 1 H.chiW ((H.point.map (1 + ·)).take H.n))]

/-- The own buffers' bases. -/
def ownB : List ℕ := LeanVM.Guest.Memory.bases B.own H.sizes

/-- **The own buffers at the bump allocator's positions.** -/
noncomputable def ownL : TLay := (H.ownB B).zip (H.ownW B)

end VtHonest

/-- **What the oracle answers**: the allocations' pointers, the witnesses, the callees'
returns. -/
structure VtWOk (H : VtHonest) (B : VtBases) (w : ℕ → E) : Prop where
  alloc : ∀ j < 110, w (vtAllocVars.getD j 0) = ofK (gpow ((H.ownB B).getD j 0))
  pads : ∀ t < 6, w (vtPadV t) = paddingWeight (H.point.take (H.τ t)) (vtRw H.rows t) ∧
    w (vtPadV t + 1) = PadLead (H.τ t) (vtRw H.rows t) ∧
    w (vtPadV t + 2) = PadRest (H.τ t) (vtRw H.rows t)
  w2768 : w 2768 = 0
  w2639 : w 2639 = H.bv
  w5817 : w 5817 = gen ^ H.n
  hwI : w 2908 = indexMle (H.point.take H.lm) ∧ w 2983 = indexMle (H.point.take 19)
  hwF : ∀ b < 3, w (vtFwV.getD b 0 + 16) = blockSel (vtSizesP H.lm H.τ) H.μ b H.point ∧
    w (vtFwV.getD b 0 + 17) = gen ^ H.offP.getD b 0
  hwP : ∀ i < 51, w (vtSelE (vtPushSel.getD i default).2.2.1 (vtPushSel.getD i default).2.2.2.1) =
      blockSel (vtSizesP H.lm H.τ) H.μ (3 + i) H.point ∧
    w (vtSelE (vtPushSel.getD i default).2.2.1 (vtPushSel.getD i default).2.2.2.1 + 1) =
      gen ^ H.offP.getD (3 + i) 0
  hwC : ∀ i < 45, w (vtSelE (vtCountSel.getD i default).2.2.1
      (vtCountSel.getD i default).2.2.2.1) = blockSel (vtSizesC H.τ) H.μ i H.point ∧
    w (vtSelE (vtCountSel.getD i default).2.2.1 (vtCountSel.getD i default).2.2.2.1 + 1) =
      gen ^ H.offC.getD i 0

end
end LeanVM.Guest.B1.Tables
