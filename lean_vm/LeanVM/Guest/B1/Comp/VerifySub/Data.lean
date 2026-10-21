/-
  LeanVM.Guest.B1.Comp.VerifySub.Data

  `verify_sub`'s completeness data over a completeness model: the transcript's digests the model
  answers (a run record in place of `VsData`'s computed fields), and the model versions of
  `VsData.Ok`, `VsMem0` and `VsCallsOk`.
-/

module

public import LeanVM.Guest.B1.Comp.VerifySub.Tail
public import LeanVM.Guest.B1.Comp.VerifySub.Ring
public import LeanVM.Guest.B1.VerifySub.CRel
public import LeanVM.Guest.B1.VerifySub.InterfaceM
public import LeanVM.Guest.B1.VerifySub.ExtractB

/-!
# `verify_sub`'s run over a completeness model

`VsData` (`VerifySub/CData.lean`) records one run of the deferring verifier; its Fiat-Shamir
states and challenges (`cv0`, `cv10`, `alphas`, `cvB`, `beta`, `mcs`, `cvM`, `cvL`, `lam`,
`target`, `fresh`) are computed with BLAKE2s. Over a completeness model they are the model's
answers, which exist only where the model answers:

* `VsRunC`: the states of the transcript (`cv0`, after the announced words `cvA`, after the root
  `cv10`, the bus squeezes `stB` and `cvB`, the ring map's squeezes `stR`, the batching's `cvL`),
  with the values derived from them (`alphas`, `beta`, `mcs`, `cvM`, `lam`, `target`, `fresh`);
  `VsRunC.Ans CM D R`: the model answers each step. At the deployed model the run of `D` itself
  (`VsRunC.ofD`, `ans_ofD`, `alphas_ofD`, …).
* `VsData.OkC CM bytecode D R`: `VsData.Ok` with the phases run over the model (`RunsToM`,
  `RunsWithM`, `BytecodeAtM`, `MatricesAtM`) at the model's challenges; `VsData.Ok.toOkC` at the
  deployed model.
* `VsMem0C rd D R P out`: `VsMem0` at the model's challenges; `VsMem0.toC`.
* `VsCallsFree`: the calls of the body to functions free of `BLAKE2S` (`ExtractB.vsFree`), the same
  under every semantics (`VsCallsFree.relB`); `VsCallsOkC`: `VsCallsOk` at the model's states,
  the hashing callees (`verify_bus_gkr`, `verify_tables`, `verify_flock`, `open_stacked`) at the
  model's states and challenges; `VsCallsOk.toC`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig LeanVM.E2E.Complete

@[expose] public section

/-! ## The run record -/

/-- **The states of `verify_sub`'s Fiat-Shamir transcript over a model.** -/
structure VsRunC where
  /-- The seed's state. -/
  cv0 : Digest
  /-- After the announced words. -/
  cvA : Digest
  /-- After the root. -/
  cv10 : Digest
  /-- The bus squeezes, `stB 0 = cv10`. -/
  stB : ℕ → Digest
  /-- The state GKR starts from. -/
  cvB : Digest
  /-- The ring map's squeezes, `stR 0` Flock's final state. -/
  stR : ℕ → Digest
  /-- The batching challenge's state. -/
  cvL : Digest

namespace VsRunC

variable (R : VsRunC) (D : VsData)

/-- The bus challenges. -/
def alphas : List E := (List.range 4).map fun c ↦ challengeOf (R.stB (c + 1))

/-- GKR's challenge. -/
def beta : E := challengeOf R.cvB

/-- The ring map's challenges and the state after them. -/
def mcs : List E := mcsOf R.stR

def cvM : Digest := R.stR 6

/-- The batching challenge. -/
def lam : E := challengeOf R.cvL

/-- The opening's target. -/
def target : E := dot (powers R.lam (D.claims.length + 1)) (ringTarget D.s R.mcs :: D.claims.map (·.value))

/-- The claims on the fixed polynomials. -/
def fresh : FixedClaims :=
  ⟨D.gr.2.1.take 18 ++ R.alphas, D.bv, D.alpha, D.zSkip, D.chi.take 8, D.rcs.reverse, D.s, D.mv⟩

/-- **The model answers the transcript** of `D` along `R`. -/
structure Ans (CM : CompModel) (D : VsData) (R : VsRunC) : Prop where
  cv0 : CM.H (digestBytes D.seed ++ digestBytes D.pi) = some R.cv0
  cvA : obsAllM CM.hm R.cv0 D.ann = some R.cvA
  cv10 : obsAllM CM.hm R.cvA [D.x0, D.x1] = some R.cv10
  stB0 : R.stB 0 = R.cv10
  stB : ∀ k < 4, sqCvM CM.hm (R.stB k) = some (R.stB (k + 1))
  cvB : sqCvM CM.hm (R.stB 4) = some R.cvB
  stR0 : R.stR 0 = D.cvF
  stR : ∀ k < 6, sqCvM CM.hm (R.stR k) = some (R.stR (k + 1))
  cvL : sqCvM CM.hm (R.stR 6) = some R.cvL

/-- **The deployed run of `D`.** -/
def ofD : VsRunC :=
  ⟨D.cv0, obsAll D.cv0 D.ann, D.cv10, fun k ↦ sqCv^[k] D.cv10, D.cvB, fun k ↦ sqCv^[k] D.cvF, D.cvL⟩

theorem sqCv_iter_succ (cv : Digest) (k : ℕ) : sqCv^[k + 1] cv = sqCv (sqCv^[k] cv) :=
  Function.iterate_succ_apply' sqCv k cv

theorem ans_ofD : Ans CompModel.deployed D (ofD D) where
  cv0 := rfl
  cvA := obsAllM_hm_deployed _ _
  cv10 := by
    show obsAllM CompModel.deployed.hm (obsAll D.cv0 D.ann) [D.x0, D.x1] = some D.cv10
    rw [obsAllM_hm_deployed]; rfl
  stB0 := rfl
  stB k _ := sqCvM_iterate_deployed _ k
  cvB := by
    show sqCvM CompModel.deployed.hm (sqCv^[4] D.cv10) = some (sqCv (sqAll 4 D.cv10).2)
    rw [sqCvM_hm_deployed, sqAll_eq]
  stR0 := rfl
  stR k _ := sqCvM_iterate_deployed _ k
  cvL := by
    show sqCvM CompModel.deployed.hm (sqCv^[6] D.cvF) = some (sqCv (sqAll 6 D.cvF).2)
    rw [sqCvM_hm_deployed, sqAll_eq]

theorem alphas_ofD : (ofD D).alphas = D.alphas := by
  simp only [alphas, ofD, VsData.alphas, sqAll_eq]

theorem beta_ofD : (ofD D).beta = D.beta := rfl

theorem mcs_ofD : (ofD D).mcs = D.mcs := by
  simp only [mcs, mcsOf, ofD, VsData.mcs, sqAll_eq]

theorem cvM_ofD : (ofD D).cvM = D.cvM := by
  simp only [cvM, ofD, VsData.cvM, sqAll_eq]

theorem cvB_ofD : (ofD D).cvB = D.cvB := rfl

theorem cvL_ofD : (ofD D).cvL = D.cvL := rfl

theorem lam_ofD : (ofD D).lam = D.lam := rfl

theorem target_ofD : (ofD D).target D = D.target := by
  simp only [target, VsData.target, lam_ofD, mcs_ofD]

theorem fresh_ofD : (ofD D).fresh D = D.fresh := by
  simp only [fresh, VsData.fresh, alphas_ofD]

theorem alphas_length : R.alphas.length = 4 := by simp [alphas]

theorem mcs_length : R.mcs.length = 6 := by simp [mcs, mcsOf]

end VsRunC

/-! ## The run within the limits, over the model -/

/-- **The run is an accepting run within the deployed limits, over the model** (`VsData.Ok`): the
phases run with every hash answered by the model, at the model's challenges. -/
structure VsData.OkC (CM : CompModel) (bytecode : List K) (D : VsData) (R : VsRunC) : Prop where
  logMem_ge : 16 ≤ D.logMem
  logMem_le : D.logMem ≤ 32
  rate_ge : 1 ≤ D.rate
  rate_le : D.rate ≤ 4
  rows_length : D.rows.length = 6
  rows_log : ∀ n ∈ D.rows, log2Ceil n < 29
  stack_ge : 22 ≤ (layoutOf bytecode D.logMem D.rows).stackLog
  stack_le : (layoutOf bytecode D.logMem D.rows).stackLog ≤ 28
  depth_lt : pushDepth (layoutOf bytecode D.logMem D.rows) < 33
  gkr : RunsToM CM.hm (gkrPhase (pushDepth (layoutOf bytecode D.logMem D.rows))) R.cvB D.xsG D.gr D.cvG
  point_length : D.gr.2.1.length = pushDepth (layoutOf bytecode D.logMem D.rows)
  values_length : D.gr.2.2.length = 3
  tables : ∀ ev, BytecodeAtM CM.hm ev bytecode
      (D.gr.2.1.take (layoutOf bytecode D.logMem D.rows).logBytecode ++ R.alphas) D.bv →
    RunsToM CM.hm (tablesSeg ev (layoutOf bytecode D.logMem D.rows) D.pi R.alphas R.beta D.gr.2.1
      D.gr.2.2) D.cvG D.xsT (D.bus, D.claims) D.cvT
  claims_length : D.claims.length = nClaims
  flock : ∀ ev, MatricesAtM CM.hm ev D.alpha D.zSkip (D.chi.take 8) D.rcs.reverse D.s D.mv →
    RunsToM CM.hm (verifyFlock ev (blake2sR1csLogSize + D.tau)) D.cvT D.xsF (D.fpoint, D.s) D.cvF
  chi_length : D.chi.length = 8 + D.tau
  rcs_length : D.rcs.length = 8
  s_length : D.s.length = 64
  opening : RunsWithM CM.hm (whirOpen (layoutOf bytecode D.logMem D.rows).stackLog D.rate (R.target D))
    R.cvL D.xsW D.os [(D.root, stackShape (layoutOf bytecode D.logMem D.rows).stackLog D.rate)]
    D.w D.cvW D.roots'
  open_point : D.w.point.length = (layoutOf bytecode D.logMem D.rows).stackLog
  accepts : D.w.Accepts (stackWeight (layoutOf bytecode D.logMem D.rows) D.claims D.fpoint
    (ringCoefficients R.mcs) R.lam)

/-- **The deployed run is an accepting run over the deployed model.** -/
theorem VsData.Ok.toOkC {bytecode : List K} {D : VsData} (hok : D.Ok bytecode) :
    D.OkC CompModel.deployed bytecode (VsRunC.ofD D) where
  logMem_ge := hok.logMem_ge
  logMem_le := hok.logMem_le
  rate_ge := hok.rate_ge
  rate_le := hok.rate_le
  rows_length := hok.rows_length
  rows_log := hok.rows_log
  stack_ge := hok.stack_ge
  stack_le := hok.stack_le
  depth_lt := hok.depth_lt
  gkr := runsToM_hm_deployed.mpr hok.gkr
  point_length := hok.point_length
  values_length := hok.values_length
  tables ev h := by
    rw [VsRunC.alphas_ofD] at h ⊢
    exact runsToM_hm_deployed.mpr (hok.tables ev (bytecodeAtM_deployed.mp h))
  claims_length := hok.claims_length
  flock ev h := runsToM_hm_deployed.mpr (hok.flock ev (matricesAtM_deployed.mp h))
  chi_length := hok.chi_length
  rcs_length := hok.rcs_length
  s_length := hok.s_length
  opening := by
    rw [VsRunC.target_ofD]
    exact runsWithM_deployed.mpr hok.opening
  open_point := hok.open_point
  accepts := by rw [VsRunC.mcs_ofD, VsRunC.lam_ofD]; exact hok.accepts

/-! ## The memory, over the model -/

/-- **The honest memory at `verify_sub`'s buffers, over the model** (`VsMem0`). -/
structure VsMem0C (rd : Reader) (D : VsData) (R : VsRunC) (P : VsPtrs) (out : E) : Prop where
  stream : ReadsAt rd P.stream D.stream
  pool : ReadsAt rd P.pool (D.claims.map (·.value))
  rows : ReadsAt rd P.rows (D.rows.map eOfNat)
  dims : ReadsAt rd P.dims (gen ^ D.logMem :: D.hs.map (gen ^ ·))
  kbase : ReadsAt rd P.kbase (kappaBase (gen ^ D.logMem) (D.hs.map (gen ^ ·)))
  bk : ReadsAt rd P.bk (blockKappas (gen ^ D.logMem) (D.hs.map (gen ^ ·)))
  zeta : ReadsAt rd P.zeta D.gr.2.1
  alpha : ReadsAt rd P.alpha R.alphas
  fpw : ReadsAt rd P.fpw (eqKernel R.alphas)
  zchis : ReadsAt rd P.zchis D.chi
  lrs : ReadsAt rd P.lrs D.rcs
  zpart : ReadsAt rd P.zpart D.s
  mcs : ReadsAt rd P.mcs R.mcs
  ctab : ReadsAt rd P.ctab (ringCoefficients R.mcs)
  zvals : ReadsAt rd P.zvals D.fpoint
  rs : ReadsAt rd P.rs (rsChainC D.s R.mcs)
  lam : ReadsAt rd P.lam (powersFrom R.lam R.lam nClaims)
  out : ReadsAt rd out (Node.fixedCells (R.fresh D))

theorem VsMem0.toC {rd : Reader} {D : VsData} {P : VsPtrs} {out : E} (hm : VsMem0 rd D P out) :
    VsMem0C rd D (VsRunC.ofD D) P out where
  stream := hm.stream
  pool := hm.pool
  rows := hm.rows
  dims := hm.dims
  kbase := hm.kbase
  bk := hm.bk
  zeta := hm.zeta
  alpha := by rw [VsRunC.alphas_ofD]; exact hm.alpha
  fpw := by rw [VsRunC.alphas_ofD]; exact hm.fpw
  zchis := hm.zchis
  lrs := hm.lrs
  zpart := hm.zpart
  mcs := by rw [VsRunC.mcs_ofD]; exact hm.mcs
  ctab := by rw [VsRunC.mcs_ofD]; exact hm.ctab
  zvals := hm.zvals
  rs := by rw [VsRunC.mcs_ofD, rsChainC_deployed]; exact hm.rs
  lam := by rw [VsRunC.lam_ofD]; exact hm.lam
  out := by rw [VsRunC.fresh_ofD]; exact hm.out

/-! ## The calls, over the model -/

/-- **The calls of the body to functions free of `BLAKE2S`** (`VsCallsOk`'s fields at
`ExtractB.vsFree`): the same under every semantics. -/
structure VsCallsFree (C : CallRel) (bytecode : List K) (D : VsData) (P : VsPtrs) (lp sq : E) :
    Prop where
  gpwRate : C "g_power_of_word__L6" [eOfNat D.rate, sq] [gen ^ D.rate]
  gpwMem : C "g_power_of_word__L6" [eOfNat D.logMem, sq] [gen ^ D.logMem]
  log2Push : C "log2_ceil_in_the_exponent__L0_L34" [gen ^ D.pushTotal, lp, sq]
    [gen ^ log2Ceil D.pushTotal]
  canon0 : C "assert_canonical" [D.x0] [0]
  canon1 : C "assert_canonical" [D.x1] [0]
  loop84 : C "__loop84" [word 1 0 0, P.zpart, P.mcs, P.rs] []
  loop85 : D.tau ≠ 0 →
    C "__loop85" [word 1 0 0, gen ^ D.tau, P.zvals * word 256 0 0, P.zchis * word 256 0 0] []
  certify : C "certify_placement" [P.kbase, sq] [gen ^ D.stackTot, P.off, P.kap]
  log2Stack : C "log2_ceil_in_the_exponent__L15_L34" [gen ^ D.stackTot, lp, sq]
    [gen ^ max 15 (log2Ceil D.stackTot)]
  terminal : C "check_opening_terminal" [P.zeta, P.chi, D.rm, gen ^ log2Ceil D.pushTotal, D.gzcn,
    gen ^ D.logMem, gen ^ D.tau, P.cplen, P.lam, P.off, P.kap, P.zvals, P.ctab, P.pt, D.w.inner,
    D.w.residual, D.w.target] []

/-- **The free calls under any semantics** are their deployed relations (`relB_vsFree`). -/
theorem VsCallsFree.relB {S : BlakeSem} {rd : Reader} {bytecode : List K} {D : VsData} {P : VsPtrs}
    {lp sq : E} (h : VsCallsFree (coreProgram.Rel rd) bytecode D P lp sq) :
    VsCallsFree (coreProgram.RelB S rd) bytecode D P lp sq where
  gpwRate := (relB_vsFree (by simp [vsFree]) _ _).mpr h.gpwRate
  gpwMem := (relB_vsFree (by simp [vsFree]) _ _).mpr h.gpwMem
  log2Push := (relB_vsFree (by simp [vsFree]) _ _).mpr h.log2Push
  canon0 := (relB_vsFree (by simp [vsFree]) _ _).mpr h.canon0
  canon1 := (relB_vsFree (by simp [vsFree]) _ _).mpr h.canon1
  loop84 := (relB_vsFree (by simp [vsFree]) _ _).mpr h.loop84
  loop85 hτ := (relB_vsFree (by simp [vsFree]) _ _).mpr (h.loop85 hτ)
  certify := (relB_vsFree (by simp [vsFree]) _ _).mpr h.certify
  log2Stack := (relB_vsFree (by simp [vsFree]) _ _).mpr h.log2Stack
  terminal := (relB_vsFree (by simp [vsFree]) _ _).mpr h.terminal

/-- **The calls of `verify_sub`'s body hold of `C`, over the model** (`VsCallsOk`): the free calls,
and the hashing callees at the model's states and challenges. -/
structure VsCallsOkC (C : CallRel) (bytecode : List K) (D : VsData) (R : VsRunC) (P : VsPtrs)
    (lp sq : E) : Prop extends VsCallsFree C bytecode D P lp sq where
  gkr : C "verify_bus_gkr" [(digestScalars R.cvB).1, (digestScalars R.cvB).2, curG P,
    gen ^ log2Ceil D.pushTotal, P.zeta]
    [(digestScalars D.cvG).1, (digestScalars D.cvG).2, curT D P, D.gr.2.2.getD 0 0,
      D.gr.2.2.getD 1 0, D.gr.2.2.getD 2 0]
  tables : C "verify_tables" [(digestScalars D.cvG).1, (digestScalars D.cvG).2, curT D P,
    (digestScalars D.pi).1, (digestScalars D.pi).2, P.zeta, gen ^ log2Ceil D.pushTotal, P.dims,
    P.rows, P.bk, sq, P.fpw, R.beta, P.pool, P.cplen, P.chi, D.gr.2.2.getD 0 0, D.gr.2.2.getD 1 0,
    D.gr.2.2.getD 2 0] [(digestScalars D.cvT).1, (digestScalars D.cvT).2, curF D P, D.gzcn, D.bv, D.rm]
  flock : C "verify_flock" [(digestScalars D.cvT).1, (digestScalars D.cvT).2, curF D P,
    gen ^ D.tau, P.zchis, P.lrs, P.zpart]
    [(digestScalars D.cvF).1, (digestScalars D.cvF).2, curW D P, D.zSkip, D.alpha, D.mv]
  opening : C (openName (layoutOf bytecode D.logMem D.rows).stackLog D.rate)
    [(digestScalars R.cvL).1, (digestScalars R.cvL).2, R.target D, D.x0, D.x1, curW D P]
    [D.w.target, P.pt, D.w.inner, D.w.residual]

theorem VsCallsOk.toFree {C : CallRel} {bytecode : List K} {D : VsData} {P : VsPtrs} {lp sq : E}
    (h : VsCallsOk C bytecode D P lp sq) : VsCallsFree C bytecode D P lp sq :=
  ⟨h.gpwRate, h.gpwMem, h.log2Push, h.canon0, h.canon1, h.loop84, h.loop85, h.certify, h.log2Stack,
    h.terminal⟩

theorem VsCallsOk.toC {C : CallRel} {bytecode : List K} {D : VsData} {P : VsPtrs} {lp sq : E}
    (h : VsCallsOk C bytecode D P lp sq) : VsCallsOkC C bytecode D (VsRunC.ofD D) P lp sq where
  toVsCallsFree := h.toFree
  gkr := h.gkr
  tables := h.tables
  flock := h.flock
  opening := by rw [VsRunC.target_ofD]; exact h.opening

/-- **The calls over `CM.sem`** from the free calls' deployed relations and the hashing callees'
relations under the model. -/
theorem VsCallsOkC.ofRelB {CM : CompModel} {rd : Reader} {bytecode : List K} {D : VsData}
    {R : VsRunC} {P : VsPtrs} {lp sq : E} (hfree : VsCallsFree (coreProgram.Rel rd) bytecode D P lp sq)
    (hgkr : coreProgram.RelB CM.sem rd "verify_bus_gkr" [(digestScalars R.cvB).1, (digestScalars R.cvB).2,
      curG P, gen ^ log2Ceil D.pushTotal, P.zeta]
      [(digestScalars D.cvG).1, (digestScalars D.cvG).2, curT D P, D.gr.2.2.getD 0 0,
        D.gr.2.2.getD 1 0, D.gr.2.2.getD 2 0])
    (htab : coreProgram.RelB CM.sem rd "verify_tables" [(digestScalars D.cvG).1, (digestScalars D.cvG).2,
      curT D P, (digestScalars D.pi).1, (digestScalars D.pi).2, P.zeta, gen ^ log2Ceil D.pushTotal, P.dims,
      P.rows, P.bk, sq, P.fpw, R.beta, P.pool, P.cplen, P.chi, D.gr.2.2.getD 0 0, D.gr.2.2.getD 1 0,
      D.gr.2.2.getD 2 0] [(digestScalars D.cvT).1, (digestScalars D.cvT).2, curF D P, D.gzcn, D.bv, D.rm])
    (hfl : coreProgram.RelB CM.sem rd "verify_flock" [(digestScalars D.cvT).1, (digestScalars D.cvT).2,
      curF D P, gen ^ D.tau, P.zchis, P.lrs, P.zpart]
      [(digestScalars D.cvF).1, (digestScalars D.cvF).2, curW D P, D.zSkip, D.alpha, D.mv])
    (hop : coreProgram.RelB CM.sem rd (openName (layoutOf bytecode D.logMem D.rows).stackLog D.rate)
      [(digestScalars R.cvL).1, (digestScalars R.cvL).2, R.target D, D.x0, D.x1, curW D P]
      [D.w.target, P.pt, D.w.inner, D.w.residual]) :
    VsCallsOkC (coreProgram.RelB CM.sem rd) bytecode D R P lp sq :=
  ⟨hfree.relB, hgkr, htab, hfl, hop⟩

end
end LeanVM.Guest.B1.VerifySub
