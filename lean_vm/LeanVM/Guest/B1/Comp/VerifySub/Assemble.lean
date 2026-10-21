/-
  LeanVM.Guest.B1.Comp.VerifySub.Assemble

  `verify_sub`'s body complete over a completeness model, block by block (`vs_body`), and its
  relation under the model's semantics (`verify_sub_complete_rel`).
-/

module

public import LeanVM.Guest.B1.Comp.VerifySub.Data

/-!
# `verify_sub` over a completeness model

The `CAssemble` chain over a `CompModel`: each block's completeness over the model
(`Comp/VerifySub/{Front,Bus,Tail,Ring}.lean`), at the run record `R` the model answers
(`VsRunC.Ans`), within the limits (`VsData.OkC`), on the honest memory (`VsMem0C`), the calls
holding of `C` (`VsCallsOkC`), each block keeping the values before it
(`completesB_step`, `completesB_last`):

* `vs_bodyC`: the body completes under `CM.sem`, from the arguments to the values every block
  leaves (`vsG11C`);
* `verify_sub_complete_relC`: `verify_sub`'s relation under `CM.sem` at the run's public input and
  seed, its calls the model callees' relations (`VsCallsOkC.ofRelB` builds them from the hashing
  callees' and the free functions' relations);
* at the deployed model: `vs_body_of_comp` (the deployed `vs_body`) and
  `verify_sub_rel_of_comp` (the body's relation from the calls', `verify_sub_complete_rel`'s last
  step).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig LeanVM.E2E.Complete

@[expose] public section

variable {CM : CompModel} {C : CallRel} {rd : Reader} {D : VsData} {R : VsRunC} {P : VsPtrs}
  {out lp sq : E} {bytecode : List K}

/-! ## The run and the memory, word by word -/

theorem hs_lengthC (hok : D.OkC CM bytecode R) : D.hs.length = 6 := by
  simp [VsData.hs, hok.rows_length]

theorem hs_ltC (hok : D.OkC CM bytecode R) : ∀ h ∈ D.hs, h < 29 := by
  intro x hx; obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx; exact hok.rows_log n hn

theorem depth_eqC (hb : bytecode.length = 2 ^ 22) (hok : D.OkC CM bytecode R) :
    D.gr.2.1.length = log2Ceil D.pushTotal := by
  rw [hok.point_length, pushDepth_eq hb _ _ hok.rows_length]; rfl

theorem depth_geC (hb : bytecode.length = 2 ^ 22) (hok : D.OkC CM bytecode R) : 18 ≤ D.gr.2.1.length := by
  rw [depth_eqC hb hok]
  have : 2 ^ 17 < D.pushTotal := by
    simp only [VsData.pushTotal, pushKappas, List.map_append, List.sum_append, List.map_cons,
      List.sum_cons]
    have := Nat.one_le_two_pow (n := D.logMem)
    omega
  exact log2Ceil_ge this

theorem mem_streamC (hl : D.rows.length = 6) (hm : VsMem0C rd D R P out) :
    (∀ k < 8, LoadHolds rd P.stream k (D.ann.getD k 0)) ∧ LoadHolds rd P.stream 8 D.x0 ∧
      LoadHolds rd P.stream 9 D.x1 := by
  have h := hm.stream
  rw [VsData.stream] at h
  have ha := readsAt_left h
  have hr := readsAt_right h
  rw [ann_length hl] at hr
  refine ⟨fun k hk => readsAt_getD ha (by rw [ann_length hl]; exact hk), ?_, ?_⟩
  · have := hr 0 (by simp); rw [loadHolds_mul_gen_pow] at this; simpa using this
  · have := hr 1 (by simp); rw [loadHolds_mul_gen_pow] at this; simpa using this

theorem mem_rowsC (hl : D.rows.length = 6) (hm : VsMem0C rd D R P out) :
    ∀ t < 6, LoadHolds rd P.rows t (eOfNat (D.rows.getD t 0)) := fun t ht => by
  have := readsAt_getD hm.rows (k := t) (by simp [hl]; omega)
  rwa [List.getD_eq_getElem _ _ (by simp [hl]; omega), List.getElem_map,
    ← List.getD_eq_getElem _ 0 (by omega)] at this

theorem mem_dimsC (hok : D.OkC CM bytecode R) (hm : VsMem0C rd D R P out) :
    LoadHolds rd P.dims 0 (gen ^ D.logMem) ∧
      ∀ t < 6, LoadHolds rd P.dims (1 + t) (gen ^ D.hs.getD t 0) := by
  have hl := hs_lengthC hok
  refine ⟨by simpa using readsAt_getD hm.dims (k := 0) (by simp), fun t ht => ?_⟩
  have := readsAt_getD hm.dims (k := 1 + t) (by simp [hl]; omega)
  rw [show 1 + t = t + 1 by omega, List.getD_cons_succ, List.getD_eq_getElem _ _ (by simp [hl]; omega),
    List.getElem_map, ← List.getD_eq_getElem _ 0 (by omega)] at this
  rwa [show 1 + t = t + 1 by omega]

theorem dims_sixC (hok : D.OkC CM bytecode R) (hm : VsMem0C rd D R P out) :
    LoadHolds rd P.dims 6 (gen ^ D.tau) := by
  have := hm.dims 6 (by simp [hs_lengthC hok])
  simp only [List.getElem_cons_succ, List.getElem_map] at this
  convert this using 2
  unfold VsData.tau
  rw [List.getD_eq_getElem _ _ (by simp [hs_lengthC hok])]

theorem mem_kbaseC (hok : D.OkC CM bytecode R) (hm : VsMem0C rd D R P out) :
    LoadHolds rd P.kbase 0 1 ∧ LoadHolds rd P.kbase 1 (gen ^ D.logMem) ∧
      (∀ t < 6, LoadHolds rd P.kbase (2 + t) (gen ^ D.hs.getD t 0)) ∧
      ∀ b < 102, LoadHolds rd P.kbase (blockKappaSrc.getD b 0) (bkSrc D b) := by
  have hl := hs_lengthC hok
  have hlen : (kappaBase (gen ^ D.logMem) (D.hs.map (gen ^ ·))).length = 8 := by
    simp [kappaBase, hl]
  refine ⟨by simpa [kappaBase] using readsAt_getD hm.kbase (k := 0) (by omega),
    by simpa [kappaBase] using readsAt_getD hm.kbase (k := 1) (by omega), fun t ht => ?_,
    fun b hb => readsAt_getD hm.kbase (by rw [hlen]; exact blockKappaSrc_lt b hb)⟩
  have := readsAt_getD hm.kbase (k := 2 + t) (by omega)
  rw [show 2 + t = t + 2 by omega, kappaBase, List.getD_cons_succ, List.getD_cons_succ,
    List.getD_eq_getElem _ _ (by simp [hl]; omega), List.getElem_map,
    ← List.getD_eq_getElem _ 0 (by omega)] at this
  rwa [show 2 + t = t + 2 by omega]

theorem mem_bkC (hm : VsMem0C rd D R P out) :
    ∀ b < 102, LoadHolds rd P.bk b ((blockKappas (gen ^ D.logMem) (D.hs.map (gen ^ ·))).getD b 0) :=
  fun b hb => readsAt_getD hm.bk (by simp [blockKappas]; omega)

theorem mem_bk_powC (hok : D.OkC CM bytecode R) (hm : VsMem0C rd D R P out) :
    ∀ b < 37, LoadHolds rd P.bk b (gen ^ pkap D b) := fun b hb => by
  have := mem_bkC hm b (by omega)
  rwa [blockKappas_pow _ _ (hs_lengthC hok) b hb] at this

theorem alphas_eqC : R.alphas = [challengeOf (R.stB 1), challengeOf (R.stB 2), challengeOf (R.stB 3),
    challengeOf (R.stB 4)] := by
  simp [VsRunC.alphas, List.range_succ]

theorem mem_alphaC (hm : VsMem0C rd D R P out) :
    ∀ c < 4, LoadHolds rd P.alpha c (challengeOf (R.stB (c + 1))) := by
  intro c hc
  have := readsAt_getD hm.alpha (k := c) (by rw [alphas_eqC]; simp; omega)
  rw [alphas_eqC] at this
  interval_cases c <;> simpa using this

theorem mem_fpwC (hm : VsMem0C rd D R P out) : ∀ x < 16, LoadHolds rd P.fpw x
    (eqFactor (fun c ↦ challengeOf (R.stB (c + 1))) x 0 * eqFactor (fun c ↦ challengeOf (R.stB (c + 1))) x 1 *
      eqFactor (fun c ↦ challengeOf (R.stB (c + 1))) x 2 *
      eqFactor (fun c ↦ challengeOf (R.stB (c + 1))) x 3) := by
  intro x hx
  have := readsAt_getD hm.fpw (k := x) (by rw [alphas_eqC]; simp [eqKernel]; omega)
  rw [alphas_eqC, eqKernel4 (fun c ↦ challengeOf (R.stB (c + 1))) x hx] at this
  exact this

theorem target_eqC (hl : D.claims.length = 112) :
    R.target D = lamTC (ringTarget D.s R.mcs) R.lam (vals D) 111 := by
  have hvl : (vals D).length = 112 := by simp [vals, hl]
  rw [VsRunC.target, show D.claims.length = (vals D).length by simp [vals], show
    ringTarget D.s R.mcs :: D.claims.map (·.value) = ringTarget D.s R.mcs :: vals D from rfl,
    dot_powers_cons, hvl, lamTC]

/-- The cells of `defer_out`, segment by segment, over the model (`out_cells`). -/
theorem out_cellsC (hb : bytecode.length = 2 ^ 22) (hok : D.OkC CM bytecode R) (hm : VsMem0C rd D R P out) :
    (∀ k < 18, LoadHolds rd out k (D.gr.2.1.getD k 0)) ∧ (∀ k < 4, LoadHolds rd out (18 + k) (R.alphas.getD k 0)) ∧
      LoadHolds rd out 22 D.bv ∧ LoadHolds rd out 23 D.alpha ∧ LoadHolds rd out 24 D.zSkip ∧
      (∀ k < 8, LoadHolds rd out (25 + k) (D.chi.getD k 0)) ∧
      (∀ k < 8, LoadHolds rd out (33 + k) (D.rcs.getD k 0)) ∧
      (∀ k < 64, LoadHolds rd out (41 + k) (D.s.getD k 0)) ∧ LoadHolds rd out 105 D.mv := by
  have hd := depth_geC hb hok
  have hal : R.alphas.length = 4 := R.alphas_length
  have hcl := hok.chi_length
  have hrl := hok.rcs_length
  have hsl := hok.s_length
  have h := hm.out
  simp only [Node.fixedCells, VsRunC.fresh, List.reverse_reverse] at h
  have hbp : (D.gr.2.1.take 18 ++ R.alphas).length = 22 := by simp [hal]; omega
  have h1 := readsAt_left (readsAt_left (readsAt_left (readsAt_left (readsAt_left h))))
  have h2 := readsAt_right (readsAt_left (readsAt_left (readsAt_left (readsAt_left h))))
  have h3 := readsAt_right (readsAt_left (readsAt_left (readsAt_left h)))
  have h4 := readsAt_right (readsAt_left (readsAt_left h))
  have h5 := readsAt_right (readsAt_left h)
  have h6 := readsAt_right h
  simp only [List.length_append, hbp, List.length_cons, List.length_nil, List.length_take, hrl, hsl,
    show min 8 D.chi.length = 8 by omega] at h2 h3 h4 h5 h6
  have at_ : ∀ {p : E} {xs : List E} {o k : ℕ}, ReadsAt rd (p * gen ^ o) xs → k < xs.length →
      LoadHolds rd p (o + k) (xs.getD k 0) := fun hr hk => by
    rw [← loadHolds_mul_gen_pow]; exact readsAt_getD hr hk
  refine ⟨fun k hk => ?_, fun k hk => ?_, ?_, ?_, ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, ?_⟩
  · have := readsAt_getD (readsAt_left h1) (k := k) (by simp; omega)
    rwa [getD_take' (by omega) (by omega)] at this
  · have := readsAt_getD (readsAt_right h1) (k := k) (by omega)
    rwa [List.length_take, show min 18 D.gr.2.1.length = 18 by omega,
      loadHolds_mul_gen_pow] at this
  · have := at_ (o := 22) (k := 0) h2 (by simp); simpa using this
  · have := at_ (o := 22) (k := 1) h2 (by simp); simpa using this
  · have := at_ (o := 22) (k := 2) h2 (by simp); simpa using this
  · have := at_ (o := 25) h3 (k := k) (by simp; omega)
    rwa [getD_take' (by omega) (by omega)] at this
  · exact at_ (o := 33) h4 (by omega)
  · exact at_ (o := 41) h5 (by omega)
  · have := at_ (o := 105) (k := 0) h6 (by simp); simpa using this

/-- The model's memory gives `defer_out`'s copied cells (`deferCells_of`). -/
theorem deferCells_ofC (hb : bytecode.length = 2 ^ 22) (hok : D.OkC CM bytecode R)
    (hm : VsMem0C rd D R P out) : DeferCells rd D P out := by
  obtain ⟨o1, o2, o22, o23, o24, o3, o4, o5, o105⟩ := out_cellsC hb hok hm
  have hd := depth_geC hb hok
  have hal : R.alphas.length = 4 := R.alphas_length
  exact ⟨fun k hk => ⟨_, readsAt_getD hm.zeta (by omega), o1 k hk⟩,
    fun k hk => ⟨_, readsAt_getD hm.alpha (by omega), o2 k hk⟩, o22, o23, o24,
    fun k hk => ⟨_, readsAt_getD hm.zchis (by rw [hok.chi_length]; omega), o3 k hk⟩,
    fun k hk => ⟨_, readsAt_getD hm.lrs (by rw [hok.rcs_length]; omega), o4 k hk⟩,
    fun k hk => ⟨_, readsAt_getD hm.zpart (by rw [hok.s_length]; omega), o5 k hk⟩, o105⟩

/-! ## The accumulated values -/

def vsG1C (D : VsData) (R : VsRunC) (P : VsPtrs) (lp sq out : E) : List (ℕ × E) :=
  seedOutC P R.cv0 ++ vsG0 D lp sq out
def vsG2C (D : VsData) (R : VsRunC) (P : VsPtrs) (lp sq out : E) : List (ℕ × E) :=
  readsOutC D P R.cvA ++ vsG1C D R P lp sq out
def vsG3C (D : VsData) (R : VsRunC) (P : VsPtrs) (lp sq out : E) : List (ℕ × E) :=
  sizesOut D P ++ vsG2C D R P lp sq out
def vsG4C (D : VsData) (R : VsRunC) (P : VsPtrs) (lp sq out : E) : List (ℕ × E) :=
  [(155, P.kbase)] ++ vsG3C D R P lp sq out
def vsG5C (D : VsData) (R : VsRunC) (P : VsPtrs) (lp sq out : E) : List (ℕ × E) :=
  [(155, P.kbase), (163, P.bk)] ++ vsG4C D R P lp sq out
def vsG6C (D : VsData) (R : VsRunC) (P : VsPtrs) (lp sq out : E) : List (ℕ × E) :=
  pushOut D P sq ++ vsG5C D R P lp sq out
def vsG7C (D : VsData) (R : VsRunC) (P : VsPtrs) (lp sq out : E) : List (ℕ × E) :=
  rootOutC D R.cv10 ++ vsG6C D R P lp sq out
def vsG8C (D : VsData) (R : VsRunC) (P : VsPtrs) (lp sq out : E) : List (ℕ × E) :=
  busOutC P R.cvB ++ vsG7C D R P lp sq out
def vsG9C (D : VsData) (R : VsRunC) (P : VsPtrs) (lp sq out : E) : List (ℕ × E) :=
  callsOut D P ++ vsG8C D R P lp sq out
def vsG10C (D : VsData) (R : VsRunC) (P : VsPtrs) (lp sq out : E) : List (ℕ × E) :=
  ringOutC D P R.cvM R.mcs ++ vsG9C D R P lp sq out
/-- **The values `verify_sub`'s body leaves, over the model** (`vsG11`). -/
def vsG11C (D : VsData) (R : VsRunC) (P : VsPtrs) (lp sq out : E) : List (ℕ × E) :=
  lamOutC P R.cvL (R.target D) ++ vsG10C D R P lp sq out

theorem vsG11C_deployed : vsG11C D (VsRunC.ofD D) P lp sq out = vsG11 D P lp sq out := by
  simp only [vsG11C, vsG10C, vsG9C, vsG8C, vsG7C, vsG6C, vsG5C, vsG4C, vsG3C, vsG2C, vsG1C,
    vsG11, vsG10, vsG9, vsG8, vsG7, vsG6, vsG5, vsG4, vsG3, vsG2, vsG1, VsRunC.target_ofD,
    VsRunC.cvM_ofD, VsRunC.mcs_ofD]
  rfl

/-- Membership in the accumulated lists over the model. -/
macro "vs_memC" : tactic => `(tactic| simp [vsG0, vsG1C, vsG2C, vsG3C, vsG4C, vsG5C, vsG6C, vsG7C,
  vsG8C, vsG9C, vsG10C, vsG11C, seedOutC, readsOutC, sizesOut, pushOut, rootOutC, busOutC, callsOut,
  ringOutC, lamOutC, curG, deferIn, openInC, lamInC, ringIn, callsInC, pushPtrs, pushK,
  VsRunC.beta, VsRunC.cvM, VsRunC.mcs, List.range_succ])

/-! ## The steps -/

section Steps

variable (hlow : LowDef 6 rd) (hb : bytecode.length = 2 ^ 22) (hR : R.Ans CM D)
  (hok : D.OkC CM bytecode R) (ht : ExpTables rd lp sq) (hm : VsMem0C rd D R P out)
  (hC : VsCallsOkC C bytecode D R P lp sq)

include hR in
theorem s_seedC (σ : Val) (h : Fixes σ (vsG0 D lp sq out)) :
    CompletesB CM.sem C rd 7 15 bSeed σ (fun σ' => Fixes σ' (vsG1C D R P lp sq out)) :=
  completesB_step (c_seed_comp σ (h.get (by vs_memC)) (h.get (by vs_memC)) (h.get (by vs_memC))
    (h.get (by vs_memC)) hR.cv0) h (by vs_memC)

include hR hok hm in
theorem s_readsC (σ : Val) (h : Fixes σ (vsG1C D R P lp sq out)) :
    CompletesB CM.sem C rd 15 136 bReads σ (fun σ' => Fixes σ' (vsG2C D R P lp sq out)) :=
  completesB_step (c_reads_comp hok.rows_length σ (h.sub fun _ hp => List.mem_append_left _ hp) hR.cvA
    (mem_streamC hok.rows_length hm).1 (mem_rowsC hok.rows_length hm)) h (by vs_memC)

include hlow hok hm hC in
theorem s_sizesC (σ : Val) (h : Fixes σ (vsG2C D R P lp sq out)) :
    CompletesB CM.sem C rd 136 155 bSizes σ (fun σ' => Fixes σ' (vsG3C D R P lp sq out)) :=
  completesB_step (c_sizesB hlow hok.logMem_ge hok.logMem_le hok.rate_ge hok.rate_le hC.gpwRate hC.gpwMem
    (mem_dimsC hok hm).1 σ (h.sub (by vs_memC))) h (by vs_memC)

include hok hm in
theorem s_kbaseC (σ : Val) (h : Fixes σ (vsG3C D R P lp sq out)) :
    CompletesB CM.sem C rd 155 163 bKBase σ (fun σ' => Fixes σ' (vsG4C D R P lp sq out)) :=
  completesB_step (c_kbaseB σ (h.sub (by vs_memC)) (mem_dimsC hok hm).2 (mem_kbaseC hok hm).1
    (mem_kbaseC hok hm).2.1 (mem_kbaseC hok hm).2.2.1) h (by vs_memC)

include hok hm in
theorem s_bkC (σ : Val) (h : Fixes σ (vsG4C D R P lp sq out)) :
    CompletesB CM.sem C rd 163 270 bBlockKappa σ (fun σ' => Fixes σ' (vsG5C D R P lp sq out)) :=
  completesB_step (c_blockKappaB σ (h.get (by vs_memC)) (mem_kbaseC hok hm).2.2.2 (mem_bkC hm)) h
    (by vs_memC)

include hok ht hm hC in
theorem s_pushC (σ : Val) (h : Fixes σ (vsG5C D R P lp sq out)) :
    CompletesB CM.sem C rd 270 419 bPush σ (fun σ' => Fixes σ' (vsG6C D R P lp sq out)) :=
  completesB_step (c_pushB ht hok.rows_length hok.logMem_le (hs_ltC hok) (mem_bk_powC hok hm) hC.log2Push σ
    (h.sub (by vs_memC))) h (by vs_memC)

include hR hok hm hC in
theorem s_rootC (σ : Val) (h : Fixes σ (vsG6C D R P lp sq out)) :
    CompletesB CM.sem C rd 419 451 bRoot σ (fun σ' => Fixes σ' (vsG7C D R P lp sq out)) :=
  completesB_step (c_root_comp σ (h.get (by vs_memC))
    (by rw [h.get (k := 134) (e := (digestScalars R.cvA).1) (by vs_memC),
      h.get (k := 135) (e := (digestScalars R.cvA).2) (by vs_memC)])
    hR.cv10 (mem_streamC hok.rows_length hm).2.1 (mem_streamC hok.rows_length hm).2.2 hC.canon0 hC.canon1)
    h (by vs_memC)

include hR hm in
theorem s_busC (σ : Val) (h : Fixes σ (vsG7C D R P lp sq out)) :
    CompletesB CM.sem C rd 451 701 bBus σ (fun σ' => Fixes σ' (vsG8C D R P lp sq out)) := by
  refine completesB_step (c_bus_comp (D := D) (st := R.stB) hR.stB hR.cvB σ ?_ (mem_alphaC hm) (mem_fpwC hm)) h
    (by vs_memC)
  rw [hR.stB0]
  exact h.sub (by vs_memC)

include hok hm hC in
theorem s_callsC (σ : Val) (h : Fixes σ (vsG8C D R P lp sq out)) :
    CompletesB CM.sem C rd 701 735 bCalls σ (fun σ' => Fixes σ' (vsG9C D R P lp sq out)) :=
  completesB_step (c_callsB (dims_sixC hok hm) hC.gkr hC.tables hC.flock σ (h.sub (by vs_memC))) h
    (by vs_memC)

include hR hok hm hC in
theorem s_ringC (σ : Val) (h : Fixes σ (vsG9C D R P lp sq out)) :
    CompletesB CM.sem C rd 735 1166 bRing σ (fun σ' => Fixes σ' (vsG10C D R P lp sq out)) :=
  completesB_step (c_ring_comp (st := R.stR) hR.stR0 hR.stR hok.s_length hok.rcs_length hm.mcs hm.ctab
    hm.rs hm.lrs hm.zvals hC.loop84 hC.loop85 σ (h.sub (by vs_memC))) h (by vs_memC)

include hR hok hm in
theorem s_lamC (σ : Val) (h : Fixes σ (vsG10C D R P lp sq out)) :
    CompletesB CM.sem C rd 1166 1629 bLam σ (fun σ' => Fixes σ' (vsG11C D R P lp sq out)) := by
  have hcl : D.claims.length = 112 := hok.claims_length
  have hlam := hm.lam
  rw [show nClaims = 112 from rfl] at hlam
  have := c_lam_comp (C := C) (cvM := R.cvM) (cvL := R.cvL) (t0 := ringTarget D.s R.mcs) hcl hR.cvL
    hm.pool hlam σ (h.sub (by vs_memC))
  have e : lamTC (ringTarget D.s R.mcs) (challengeOf R.cvL) (vals D) 111 = R.target D :=
    (target_eqC hcl).symm
  rw [e] at this
  exact completesB_step this h (by vs_memC)

include hlow hb hok hC in
theorem s_openC (σ : Val) (h : Fixes σ (vsG11C D R P lp sq out)) :
    CompletesB CM.sem C rd 1629 1652 bOpen σ (fun σ' => Fixes σ' (vsG11C D R P lp sq out)) :=
  completesB_last (c_openB hlow hb hok.stack_ge hok.stack_le hok.rate_ge hok.rate_le hC.certify hC.log2Stack
    hC.opening hC.terminal σ (h.sub (by vs_memC))) h (by vs_memC)

include hb hok hm in
theorem s_deferC (σ : Val) (h : Fixes σ (vsG11C D R P lp sq out)) :
    CompletesB CM.sem C rd 1652 1754 bDefer σ (fun σ' => Fixes σ' (vsG11C D R P lp sq out)) :=
  completesB_last (c_deferB (deferCells_ofC hb hok hm) σ (h.sub (by vs_memC))) h (by vs_memC)

end Steps

/-- **`verify_sub`'s body completes over the model** (`vs_body`), for any relation `C` its calls
hold of, over the model's honest memory, at a run record the model answers. -/
theorem vs_bodyC (hlow : LowDef 6 rd) (hb : bytecode.length = 2 ^ 22) (hR : R.Ans CM D)
    (hok : D.OkC CM bytecode R) (ht : ExpTables rd lp sq) (hm : VsMem0C rd D R P out)
    (hC : VsCallsOkC C bytecode D R P lp sq) (σ0 : Val) (h0 : Fixes σ0 (vsG0 D lp sq out)) :
    CompletesB CM.sem C rd 7 1754 vsBody σ0 (fun σ' => Fixes σ' (vsG11C D R P lp sq out)) := by
  rw [vsBody_eq]
  refine CompletesB.append (by omega) (by omega) numBelow_pre12 ?_ fun σ _ h =>
    s_deferC hb hok hm σ h
  refine CompletesB.append (by omega) (by omega) numBelow_pre11 ?_ fun σ _ h =>
    s_openC hlow hb hok hC σ h
  refine CompletesB.append (by omega) (by omega) numBelow_pre10 ?_ fun σ _ h =>
    s_lamC hR hok hm σ h
  refine CompletesB.append (by omega) (by omega) numBelow_pre9 ?_ fun σ _ h =>
    s_ringC hR hok hm hC σ h
  refine CompletesB.append (by omega) (by omega) numBelow_pre8 ?_ fun σ _ h =>
    s_callsC hok hm hC σ h
  refine CompletesB.append (by omega) (by omega) numBelow_pre7 ?_ fun σ _ h =>
    s_busC hR hm σ h
  refine CompletesB.append (by omega) (by omega) numBelow_pre6 ?_ fun σ _ h =>
    s_rootC hR hok hm hC σ h
  refine CompletesB.append (by omega) (by omega) numBelow_pre5 ?_ fun σ _ h =>
    s_pushC hok ht hm hC σ h
  refine CompletesB.append (by omega) (by omega) numBelow_pre4 ?_ fun σ _ h =>
    s_bkC hok hm σ h
  refine CompletesB.append (by omega) (by omega) numBelow_pre3 ?_ fun σ _ h =>
    s_kbaseC hok hm σ h
  refine CompletesB.append (by omega) (by omega) numBelow_pre2 ?_ fun σ _ h =>
    s_sizesC hlow hok hm hC σ h
  refine CompletesB.append (by omega) (by omega) numBelow_pre1 ?_ fun σ _ h =>
    s_readsC hR hok hm σ h
  exact s_seedC hR σ0 h0

/-- **`verify_sub` is complete over the model** (`verify_sub_complete_rel`): on a memory defined
below `2^6` holding the model's honest words, at a run the model answers within the limits, its
calls the relations under `CM.sem`, `verify_sub` holds under `CM.sem` of the run's public input and
seed, at any `defer_out` holding the run's claims. -/
theorem verify_sub_complete_relC (hlow : LowDef 6 rd) (hb : bytecode.length = 2 ^ 22)
    (hR : R.Ans CM D) (hok : D.OkC CM bytecode R) (ht : ExpTables rd lp sq) (hm : VsMem0C rd D R P out)
    (hC : VsCallsOkC (coreProgram.RelB CM.sem rd) bytecode D R P lp sq) :
    coreProgram.RelB CM.sem rd "verify_sub" [(digestScalars D.pi).1, (digestScalars D.pi).2,
      (digestScalars D.seed).1, (digestScalars D.seed).2, lp, sq, out] [] := by
  set σ0 := upds (fun _ => 0) (vsG0 D lp sq out)
  have h0 : Fixes σ0 (vsG0 D lp sq out) := by
    intro p hp; simp only [vsG0, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [σ0, vsG0, upds_n]
  obtain ⟨σ, he, -, hh⟩ := vs_bodyC hlow hb hR hok ht hm hC σ0 h0
  rw [relB_iff_sem find_verify_sub, core15_body', core15_params]
  refine ⟨σ, ?_, ?_⟩
  · have hp : ∀ k < 7, σ (.n k) = σ0 (.n k) := fun k hk => he.apply (Or.inl hk)
    simp only [List.map_cons, List.map_nil, hp 0 (by omega), hp 1 (by omega), hp 2 (by omega),
      hp 3 (by omega), hp 4 (by omega), hp 5 (by omega), hp 6 (by omega)]
    simp [σ0, vsG0, upds_n]
  · rw [holdsListB_append]
    exact hh _ _ rfl

/-! ## At the deployed model -/

/-- The deployed `vs_body`, from the model's at `CompModel.deployed`. -/
theorem vs_body_of_comp (hlow : LowDef 6 rd) (hb : bytecode.length = 2 ^ 22)
    (hok : D.Ok bytecode) (ht : ExpTables rd lp sq) (hm : VsMem0 rd D P out)
    (hC : VsCallsOk C bytecode D P lp sq) (σ0 : Val) (h0 : Fixes σ0 (vsG0 D lp sq out)) :
    Completes C rd 7 1754 vsBody σ0 (fun σ' => Fixes σ' (vsG11 D P lp sq out)) := by
  have := vs_bodyC hlow hb (VsRunC.ans_ofD D) hok.toOkC ht hm.toC hC.toC σ0 h0
  rw [vsG11C_deployed] at this
  exact this.of_deployed

/-- The deployed `verify_sub`'s relation from its calls' (`verify_sub_complete_rel`'s last step),
from the model's at `CompModel.deployed`. -/
theorem verify_sub_rel_of_comp (hlow : LowDef 6 rd) (hb : bytecode.length = 2 ^ 22)
    (hok : D.Ok bytecode) (ht : ExpTables rd lp sq) (hm : VsMem0 rd D P out)
    (hC : VsCallsOk (coreProgram.Rel rd) bytecode D P lp sq) :
    coreProgram.Rel rd "verify_sub" [(digestScalars D.pi).1, (digestScalars D.pi).2,
      (digestScalars D.seed).1, (digestScalars D.seed).2, lp, sq, out] [] := by
  have hC' : VsCallsOkC (coreProgram.RelB CompModel.deployed.sem rd) bytecode D (VsRunC.ofD D) P lp sq := by
    rw [show CompModel.deployed.sem = blakeDeployed from rfl, relB_deployed]; exact hC.toC
  have := verify_sub_complete_relC hlow hb (VsRunC.ans_ofD D) hok.toOkC ht hm.toC hC'
  rwa [show CompModel.deployed.sem = blakeDeployed from rfl, relB_deployed] at this

end
end LeanVM.Guest.B1.VerifySub
