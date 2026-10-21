/-
  LeanVM.Guest.B1.Comp.Da.ColumnAtC

  The vector cells, `da_vector_dispatch`, a column and the column loops placed by the bump
  allocator (`B1/Da/VectorAt`, `DispatchAt`, `ColumnAt`, `ColLoopAt`), the vector hash's rows
  under any semantics, the cells and the trees over a completeness model.
-/

module

public import LeanVM.Guest.B1.Comp.Da.RowsInS
public import LeanVM.Guest.B1.Comp.Da.Column
public import LeanVM.Guest.B1.Da.ColLoopAt

/-!
# The columns, placed, over a completeness model

The deployed placed lemmas with the vector hash's 96 rows checked under `S` (`ChainSteps S`,
`vx_relAtInS`, `vd_relAtInS`), the row cells' digests and the column tree over a model's answers
(`RowCellM CM.hm`, `Meaning_da_levelsWith CM.hm`; `col_relAtInC`, `colLoop_relAtInC`). The proofs
are the deployed ones: the body holds under the honest values (`col_holdsC`), the hashing callees
are placed by `…S` lemmas, the gap loop, free of `BLAKE2S`, by the deployed one
(`relAtInWS_of_freeOn`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.Value LeanVM.E2E.Complete
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Main (RelAtInWS relAtInWS_of_walk relAtInWS_of_walk_loop)

@[expose] public section

variable {S : BlakeSem}

/-! ## The vector cell and its dispatch -/

/-- **`da_vector_cell__L{final}`, placed at `fp`, under `S`** (`vx_relAtIn`): its rows chained
under `S`. -/
theorem vx_relAtInS (fs : String → ℕ) (cert : String → V → ℕ) (final : Bool) {xb h0 h1 ctr o0 o1 : E}
    {ws cv : List E} {b c : ℕ} {R D : ℕ → Prop} (hxb : xb = gen ^ b) (hctr : ctr = gen ^ c)
    (hch : ChainSteps S (h0, h1) (vxBlocks (ws.getD · 0)) (vxMd final (cv.getD · 0)) 96 (o0, o1))
    (hR : ∀ k < 4, R (c + 3 * b + k)) (fp : ℕ)
    (hD : ∀ i, D i → fp + cert (vxName final) (.n 4) ≤ i ∧ i < fp + cert (vxName final) (.n 4) + 256)
    (rd : Reader) (hcv : CellsAt rd (ctr * (xb * xb * xb)) cv) (hcl : cv.length = 4)
    (hws : ∀ k < 256, ∀ v, rd (gpow (fp + cert (vxName final) (.n 4) + k)) = some v → v = ws.getD k 0) :
    RelAtInWS S fs cert wId rd R D fp (fs (vxName final)) (vxName final) [xb, h0, h1, ctr]
      [o0, o1, gen ^ (fp + cert (vxName final) (.n 4))] fun θ => θ (vxName final) := by
  obtain ⟨sts, hst0, hout, hsteps⟩ := hch
  set a0 := fp + cert (vxName final) (.n 4)
  have hcv' : ∀ k < 4, LoadHolds rd (ctr * (xb * xb * xb)) k (cv.getD k 0) := fun k hk => by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact hcv k (by omega)
  have hfr : IsInK (gen ^ a0) ∧ ∀ k < 256, ∀ v, rd ((gen ^ a0).limb 0 * Parameters.gpow k) = some v →
      v = ws.getD k 0 := ⟨by rw [gen_pow_eq_ofK]; exact ofK_isInK _, fun k hk v hv => hws k hk v (by
        rwa [limb0_gen_pow, gpow_add'] at hv)⟩
  obtain ⟨ha, hr, hp⟩ := vx_core_holdsB (S := S) (final := final) (wsf := (ws.getD · 0))
    (cvf := (cv.getD · 0)) (st := sts) hcv' hfr hst0 hout hsteps
  set σ : Val := fun v => vxVals final xb h0 h1 ctr (gen ^ a0) (ws.getD · 0) (cv.getD · 0) sts
    (vxMd final (cv.getD · 0)) v.idx with hσ
  have h3464 : σ (.n 3464) = gen ^ (c + 3 * b) := by
    show ctr * (xb * xb * xb) = _; rw [hxb, hctr]; ring
  have h3468 : σ (.n 3468) = gen ^ (c + 3 * b) := h3464
  have h3600 : σ (.n 3600) = gen ^ (c + 3 * b + 1) := by
    show ctr * (xb * xb * xb * word 2 0 0) = _
    rw [hxb, hctr, word_gen]; ring
  have h3732 : σ (.n 3732) = gen ^ (c + 3 * b + 2) := by
    show ctr * (xb * xb * xb * word 4 0 0) = _
    rw [hxb, hctr, word4]; ring
  have hload : ∀ A ∈ loadAddrs σ ((vxAtoms final).map Ev.atom), ∃ i, A = gpow i ∧
      (ownData cert fp (fp + fs (vxName final)) (vxName final) (allocs σ ((vxAtoms final).map Ev.atom))
        ((vxAtoms final).map Ev.atom) i ∨ R i ∨ (fun _ => False) i) := by
    rw [loadAddrs_atoms, vx_loads]
    intro A hA
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
    rcases hA with rfl | rfl | rfl | rfl
    · exact ⟨c + 3 * b + 0, by rw [h3464, limb0_gen_pow, gpow_add'], Or.inr (Or.inl (hR 0 (by omega)))⟩
    · exact ⟨c + 3 * b + 1, by rw [h3468, limb0_gen_pow, gpow_add'], Or.inr (Or.inl (hR 1 (by omega)))⟩
    · exact ⟨c + 3 * b + 2, by rw [h3600, limb0_gen_pow, gpow_add'], Or.inr (Or.inl (hR 2 (by omega)))⟩
    · exact ⟨c + 3 * b + 3, by rw [h3732, limb0_gen_pow, gpow_add'], Or.inr (Or.inl (hR 3 (by omega)))⟩
  have h := relAtInWS_of_walk (S := S) (fs := fs) (cert := cert) (w := wId) (σ := σ) (rd := rd)
    (R := R) (D := D) (Dk := fun _ => False) (fp := fp) (N := 0) (bws := []) (find_vx final)
    (Or.inr (calls_atoms _)) hp (walk_atoms σ (vxAtoms final) _) hr (holdsB_atoms ha)
    (by rw [allocDsts_atoms (vx_noAlloc final), allocs_atoms σ (vx_noAlloc final)]; rfl)
    (fun q hq => by
      rw [addrs_atoms, vx_addrs] at hq
      obtain rfl := List.mem_singleton.mp hq
      show σ (.n (vxF final)) = _
      rw [show σ (.n (vxF final)) = gen ^ a0 by cases final <;> rfl, gen_pow_eq_ofK])
    (by rw [calls_atoms]; exact ⟨rfl, fun i h => h⟩) hload
    (fun i hi => Or.inl (Or.inr ⟨(.n 4, 256), by rw [runs_atoms, vx_runs]; simp, (hD i hi).1, (hD i hi).2⟩))
  simp only [allocs_atoms σ (vx_noAlloc final), List.sum_nil, Nat.add_zero, List.map_nil] at h
  exact h

/-- `da_vector_dispatch` at `fp` under `S`, its selector's branch given (`vd_relAtIn'`). -/
theorem vd_relAtInS' (fs : String → ℕ) (cert : String → V → ℕ) {xb h0 h1 ctr o0 o1 : E}
    {ws cv : List E} (final : Bool) {b c : ℕ} {R D : ℕ → Prop}
    (hf5 : xb + word 9223372036854775983 0 0 = 0 ↔ final = true) (hxb : xb = gen ^ b) (hctr : ctr = gen ^ c)
    (hch : ChainSteps S (h0, h1) (vxBlocks (ws.getD · 0)) (vxMd (final) (cv.getD · 0)) 96 (o0, o1))
    (hR : ∀ k < 4, R (c + 3 * b + k)) (fp : ℕ)
    (hD : ∀ i, D i → fp + fs "da_vector_dispatch" + cert (vxName (final)) (.n 4) ≤ i ∧
      i < fp + fs "da_vector_dispatch" + cert (vxName (final)) (.n 4) + 256)
    (rd : Reader) (hcv : CellsAt rd (ctr * (xb * xb * xb)) cv) (hcl : cv.length = 4)
    (hws : ∀ k < 256, ∀ v, rd (gpow (fp + fs "da_vector_dispatch" + cert (vxName (final)) (.n 4) + k)) =
      some v → v = ws.getD k 0) :
    RelAtInWS S fs cert wId rd R D fp (fs "da_vector_dispatch" + fs (vxName (final)))
      "da_vector_dispatch" [xb, h0, h1, ctr]
      [o0, o1, gen ^ (fp + fs "da_vector_dispatch" + cert (vxName (final)) (.n 4))]
      fun θ => θ "da_vector_dispatch" + θ (vxName final) := by
  set wp := gen ^ (fp + fs "da_vector_dispatch" + cert (vxName final) (.n 4))
  let σ : Val := listVal [xb, h0, h1, ctr, word 9223372036854775983 0 0, xb + word 9223372036854775983 0 0,
    o0, o1, wp, o0, o1, wp, o0, o1, wp, o0, o1, wp]
  have h5 : σ (.n 5) = 0 ↔ final = true := hf5
  have hkid := vx_relAtInS fs cert final hxb hctr hch hR (fp + fs "da_vector_dispatch" + 0)
    (D := fun i => fp + fs "da_vector_dispatch" + cert (vxName final) (.n 4) ≤ i ∧
      i < fp + fs "da_vector_dispatch" + cert (vxName final) (.n 4) + 256)
    (fun i h => by rw [Nat.add_zero]; exact h) rd hcv hcl (by rw [Nat.add_zero]; exact hws)
  have h := relAtInWS_of_walk (S := S) (fs := fs) (cert := cert) (w := wId) (σ := σ) (rd := rd)
    (R := R) (D := D) (Dk := fun i => fp + fs "da_vector_dispatch" + cert (vxName final) (.n 4) ≤ i ∧
      i < fp + fs "da_vector_dispatch" + cert (vxName final) (.n 4) + 256)
    (fp := fp) (N := fs (vxName final)) (bws := [fun θ => θ (vxName final)]) find_vd
    (Or.inl (by decide +kernel)) rfl (vd_walk σ final h5) rfl
    (fun e he => by
      have hk : IsInK (σ (.n 5)) := (isInK_add_left (by rw [hxb]; exact isInK_gen_pow b)).mpr
        (by rw [word_g127]; exact isInK_gen_pow 127)
      cases final <;> simp [vdEs] at he <;>
        rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | rfl | exact trivial | exact hk)
    (by cases final <;> rfl) (fun q hq => by cases final <;> simp [vdEs, addrs, Ev.addr?] at hq)
    (by
      have hc : calls (vdEs final) = [⟨vxName final, [.n 0, .n 1, .n 2, .n 3],
          if final then [.n 6, .n 7, .n 8] else [.n 12, .n 13, .n 14], true⟩] := by
        cases final <;> rfl
      have e : allocs σ (vdEs final) = [] := by cases final <;> rfl
      rw [hc, e]
      refine ⟨fs (vxName final), 0, R, _, rfl, fun i hi => Or.inl (Or.inl hi), ?_, rfl,
        fun i hi => Or.inr ⟨rfl, hi⟩⟩
      simp only [↓reduceIte]
      have hr : (if final then [Core.V.n 6, .n 7, .n 8] else [.n 12, .n 13, .n 14]).map σ =
          [o0, o1, wp] := by
        cases final <;> rfl
      rw [List.sum_nil, Nat.add_zero, hr]
      exact hkid)
    (fun A hA => by cases final <;> simp [vdEs, loadAddrs, Ev.loadAddr?] at hA)
    (fun i hi => Or.inr (hD i hi))
  have e : allocs σ (vdEs final) = [] := by cases final <;> rfl
  simp only [e, List.sum_nil, Nat.add_zero, List.map_cons, List.map_nil, List.sum_cons] at h
  exact h

/-- **`da_vector_dispatch` at `fp` under `S`** (`vd_relAtIn`). -/
theorem vd_relAtInS (fs : String → ℕ) (cert : String → V → ℕ) {xb h0 h1 ctr o0 o1 : E}
    {ws cv : List E} {b c : ℕ} {R D : ℕ → Prop} (hb : b < 128) (hxb : xb = gen ^ b) (hctr : ctr = gen ^ c)
    (hch : ChainSteps S (h0, h1) (vxBlocks (ws.getD · 0)) (vxMd (decide (b = 127)) (cv.getD · 0)) 96
      (o0, o1))
    (hR : ∀ k < 4, R (c + 3 * b + k)) (fp : ℕ)
    (hD : ∀ i, D i → fp + fs "da_vector_dispatch" + cert (vxName (decide (b = 127))) (.n 4) ≤ i ∧
      i < fp + fs "da_vector_dispatch" + cert (vxName (decide (b = 127))) (.n 4) + 256)
    (rd : Reader) (hcv : CellsAt rd (ctr * (xb * xb * xb)) cv) (hcl : cv.length = 4)
    (hws : ∀ k < 256, ∀ v, rd (gpow (fp + fs "da_vector_dispatch" +
      cert (vxName (decide (b = 127))) (.n 4) + k)) = some v → v = ws.getD k 0) :
    RelAtInWS S fs cert wId rd R D fp (fs "da_vector_dispatch" + fs (vxName (decide (b = 127))))
      "da_vector_dispatch" [xb, h0, h1, ctr]
      [o0, o1, gen ^ (fp + fs "da_vector_dispatch" + cert (vxName (decide (b = 127))) (.n 4))]
      fun θ => θ "da_vector_dispatch" + θ (vxName (decide (b = 127))) :=
  vd_relAtInS' fs cert (decide (b = 127)) (by
    rw [e_add_eq_zero_iff, word_g127, hxb, decide_eq_true_iff]
    exact ⟨fun h => gen_pow_inj' (by omega) (by omega) h, fun h => by rw [h]⟩) hxb hctr hch hR fp hD rd
    hcv hcl hws

/-! ## A column -/

/-- **The column's body holds over a completeness model** under its honest values
(`col_holds`). -/
theorem col_holdsC {CM : CompModel} (store : Bool) {rd : Reader}
    {xb nb np gap glp pb ct rb hs ctr h0 h1 o0 o1 lv node c0 c1 : E}
    (h12 : CellsAt rd (hs * (xb * xb)) [h0, h1])
    (hdisp : coreProgram.RelB CM.sem rd "da_vector_dispatch" [xb, h0, h1, ctr] [o0, o1, lv])
    (h14 : CellsAt rd (hs * (xb * gen * (xb * gen))) [o0, o1]) (hk1 : IsInK nb)
    (hrow : nb ≠ 1 → LoopTo nb fun j => RowCellM CM.hm store rd lv rb xb node pb (gen ^ j))
    (hk3 : IsInK gap) (hgap : gap ≠ 1 → LoopTo gap fun j => GapStep rd node nb (gen ^ j))
    (hdl : ∃ k < 11, glp = gen ^ k ∧ Meaning_da_levelsWith CM.hm k rd [node] [c0, c1])
    (h30 : CellsAt rd (ct * (xb * xb)) [c0, c1]) :
    Stmt.HoldsListB CM.sem (coreProgram.RelB CM.sem rd) rd
      (colVals xb nb np gap glp pb ct rb hs ctr h0 h1 o0 o1 lv node c0 c1)
      (colBody store) False (fun rs => rs = []) := by
  obtain ⟨l12, l13⟩ := cellsAt_two.mp h12
  obtain ⟨l14, l15⟩ := cellsAt_two.mp h14
  obtain ⟨l30, l31⟩ := cellsAt_two.mp h30
  simp only [colBody, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, true_and,
    word_one, word_gen, colVals, listVal, List.getD_cons_succ, List.getD_cons_zero, and_true]
  exact ⟨l12, l13, hdisp, l14, l15, isInK_one_add.mpr hk1,
    fun h => row_loop_comp store rd _ _ _ _ _ _ (hrow (one_add_ne_zero.mp h)),
    isInK_one_add.mpr hk3, fun h => gap_loop_compB store rd _ _ _ (hgap (one_add_ne_zero.mp h)),
    dl_dispatch_comp hdl, l30, l31⟩

/-- **A column at `fp` over a completeness model** (`col_relAtIn`): the vector hash's rows under
the model's semantics, the row cells and the column tree over its answers. -/
theorem col_relAtInC (fs : String → ℕ) (cert : String → V → ℕ) {CM : CompModel} (store : Bool)
    {b r N lp p t q h c a pd : ℕ}
    (hb : b < 128) (hr1 : 1 ≤ r) (hrN : r ≤ N) (hN : N = 2 ^ lp) (hlp : lp ≤ 10)
    {h0 h1 o0 o1 c0 c1 : E} {ws cv : List E} (hcl : cv.length = 4)
    (hch : ChainSteps CM.sem (h0, h1) (vxBlocks (ws.getD · 0)) (vxMd (decide (b = 127)) (cv.getD · 0))
      96 (o0, o1))
    {R : ℕ → Prop} (hRc : ∀ k < 4, R (c + 3 * b + k)) (hRh : ∀ k < 4, R (h + 2 * b + k))
    (hRt : ∀ k < 2, R (t + 2 * b + k))
    (hRrow : ∀ j < r, R (q + j) ∧ R (a + 129 * j + b) ∧ R (a + 129 * j + b + 1) ∧
      (store = true → R (p + j) ∧ R (pd + 128 * j + 2 * b) ∧ R (pd + 128 * j + 2 * b + 1)))
    (fp : ℕ) (rd : Reader)
    (hhs : CellsAt rd (gen ^ h * (gen ^ b * gen ^ b)) [h0, h1])
    (hho : CellsAt rd (gen ^ h * (gen ^ b * gen * (gen ^ b * gen))) [o0, o1])
    (hcv : CellsAt rd (gen ^ c * (gen ^ b * gen ^ b * gen ^ b)) cv)
    (hws : ∀ k < 256, ∀ v, rd (gpow (fp + fs (colName store) + 4 * N + fs "da_vector_dispatch" +
      cert (vxName (decide (b = 127))) (.n 4) + k)) = some v → v = ws.getD k 0)
    (hrows : ∀ j < r, RowCellM CM.hm store rd (gen ^ (fp + fs (colName store) + 4 * N +
      fs "da_vector_dispatch" + cert (vxName (decide (b = 127))) (.n 4))) (gen ^ q) (gen ^ b)
      (gen ^ (fp + fs (colName store))) (gen ^ p) (gen ^ j))
    (hrb : ∀ j < r, rd (gpow (q + j)) = some (gen ^ (a + 129 * j)))
    (hpb : store = true → ∀ j < r, rd (gpow (p + j)) = some (gen ^ (pd + 128 * j)))
    (hgap : ∀ d < N - r, GapStep rd (gen ^ (fp + fs (colName store))) (gen ^ r) (gen ^ d))
    (hlv : Meaning_da_levelsWith CM.hm lp rd [gen ^ (fp + fs (colName store))] [c0, c1])
    (hct : CellsAt rd (gen ^ t * (gen ^ b * gen ^ b)) [c0, c1]) :
    RelAtInWS CM.sem fs cert wId rd R (fun _ => False) fp (colTot fs store b r N lp) (colName store)
      [gen ^ b, gen ^ r, gen ^ N, gen ^ (N - r), gen ^ lp, gen ^ p, gen ^ t, gen ^ q, gen ^ h, gen ^ c] []
      fun θ => colTot θ store b r N lp := by
  set nodeP := fp + fs (colName store)
  set b0 := nodeP + 4 * N
  set lvP := b0 + fs "da_vector_dispatch" + cert (vxName (decide (b = 127))) (.n 4)
  have hN10 : N ≤ 1024 := by
    rw [hN]; exact le_trans (Nat.pow_le_pow_right (by norm_num) hlp) (by norm_num)
  have hr33 : r < 2 ^ 33 := by omega
  set σ := colVals (gen ^ b) (gen ^ r) (gen ^ N) (gen ^ (N - r)) (gen ^ lp) (gen ^ p) (gen ^ t) (gen ^ q)
    (gen ^ h) (gen ^ c) h0 h1 o0 o1 (gen ^ lvP) (gen ^ nodeP) c0 c1 with hσ
  -- the body holds
  have hdisp : coreProgram.RelB CM.sem rd "da_vector_dispatch" [gen ^ b, h0, h1, gen ^ c]
      [o0, o1, gen ^ lvP] :=
    (vd_relAtInS fs cert (D := fun _ => False) hb rfl rfl hch hRc b0 (fun _ h => h.elim) rd hcv hcl
      hws).toRelAtIn.relAt.rel
  have hrowL : LoopTo (gen ^ r) fun j => RowCellM CM.hm store rd (gen ^ lvP) (gen ^ q) (gen ^ b)
      (gen ^ nodeP) (gen ^ p) (gen ^ j) := loopTo_all' hr1 hr33 hrows
  have hgapL : gen ^ (N - r) ≠ 1 → LoopTo (gen ^ (N - r)) fun j =>
      GapStep rd (gen ^ nodeP) (gen ^ r) (gen ^ j) :=
    fun hne => loopTo_all' (by by_contra h0; exact hne (by rw [show N - r = 0 by omega, pow_zero]))
      (by omega) hgap
  have hholds := col_holdsC store hhs hdisp hho (isInK_gen_pow r) (fun _ => hrowL) (isInK_gen_pow _)
    hgapL ⟨lp, by omega, rfl, hlv⟩ hct (np := gen ^ N) (glp := gen ^ lp)
  -- the path
  have hx : σ (.n 4) = ofK (gpow lp) := by rw [← gen_pow_eq_ofK]; rfl
  have hw := walk_dispatch σ (colPre store) colPost (colPre_straight store) colPost_straight (.n 4) dlNames
    [.n 23] [.n 30, .n 31] [] (i := lp) (by simp [dlNames]; omega) (by simp [dlNames]) hx
  rw [← colBody_split] at hw
  set es := (colPre store).flatMap (Main.slEvs σ) ++
    .call dlNames[lp]! [.n 23] [.n 30, .n 31] :: colPost.flatMap (Main.slEvs σ) with hes
  have hev := holdsB_of_holdsList (find_col store) hholds hw
  obtain ⟨hpd, hpa, hpad, hpc⟩ := Main.straight_parts σ _ (colPre_straight store)
  obtain ⟨hqd, hqa, hqad, hqc⟩ := Main.straight_parts σ _ colPost_straight
  have h22 : σ (.n 22) = gen ^ (4 * N) := by
    show gen ^ N * gen ^ N * (gen ^ N * gen ^ N) = _; ring
  have hal : allocs σ es = [4 * N] := by
    rw [hes, allocs_append, show allocs σ (.call dlNames[lp]! [.n 23] [.n 30, .n 31] ::
      colPost.flatMap (Main.slEvs σ)) = allocs σ (colPost.flatMap (Main.slEvs σ)) from rfl, hpa, hqa,
      show (colPre store).filterMap Main.Stmt.allocSz = [(.n 23, .inr (.n 22))] by cases store <;> rfl]
    simp only [List.map_cons, List.map_nil, Sum.elim_inr, h22,
      logG_gen_pow (show 4 * N < 2 ^ 64 - 1 by omega)]
    rfl
  have hown : ∀ i, nodeP ≤ i → i < nodeP + 4 * N → ownData cert fp (fp + fs (colName store))
      (colName store) [4 * N] es i := fun i h1 h2 => Or.inl ⟨(4 * N, nodeP), List.Mem.head _, h1, h2⟩
  have hcalls : calls es = [⟨"da_vector_dispatch", [.n 0, .n 12, .n 13, .n 9], [.n 14, .n 15, .n 16], true⟩,
      ⟨rowName store, [.n 26, .n 1, .n 16, .n 7, .n 0, .n 23, .n 5], [], true⟩,
      ⟨gapName store, [.n 29, .n 3, .n 23, .n 1], [], decide (N - r ≠ 0)⟩,
      ⟨dlNames[lp]!, [.n 23], [.n 30, .n 31], true⟩] := by
    rw [hes, calls_append, show calls (.call dlNames[lp]! [.n 23] [.n 30, .n 31] ::
      colPost.flatMap (Main.slEvs σ)) = ⟨dlNames[lp]!, [.n 23], [.n 30, .n 31], true⟩ ::
        calls (colPost.flatMap (Main.slEvs σ)) from rfl, hpc, hqc,
      show (colPre store).filterMap Main.Stmt.callS = [(none, "da_vector_dispatch",
        [.n 0, .n 12, .n 13, .n 9], [.n 14, .n 15, .n 16]),
        (some (.n 25), rowName store, [.n 26, .n 1, .n 16, .n 7, .n 0, .n 23, .n 5], []),
        (some (.n 28), gapName store, [.n 29, .n 3, .n 23, .n 1], [])] by cases store <;> rfl,
      show colPost.filterMap Main.Stmt.callS = [] from rfl]
    have h25 : decide (σ (.n 25) ≠ 0) = true := by
      rw [decide_eq_true_iff]
      exact one_add_ne_zero.mpr fun he => by have := (gen_pow_eq_one_iff (by omega)).mp he; omega
    have h28 : decide (σ (.n 28) ≠ 0) = decide (N - r ≠ 0) := by
      show decide (1 + gen ^ (N - r) ≠ 0) = _
      refine decide_eq_decide.mpr ⟨fun h he => h (by rw [he, pow_zero]; exact e_add_eq_zero_iff.mpr rfl),
        fun h he => h ?_⟩
      have := (gen_pow_eq_one_iff (show N - r < 2 ^ 64 - 1 by omega)).mp (e_add_eq_zero_iff.mp he).symm
      exact this
    simp only [List.map_cons, List.map_nil, Main.mkCall, h25, h28, List.nil_append, List.cons_append]
  -- the callees
  have hrowRel : coreProgram.RelB CM.sem rd (rowName store)
      [gen ^ 0, gen ^ r, gen ^ lvP, gen ^ q, gen ^ b, gen ^ nodeP, gen ^ p] [] := by
    rw [pow_zero]; exact row_loop_comp store rd _ _ _ _ _ _ hrowL
  have kid2 := relAtInWS_of_relInTWS_pure fs cert (row_pure store) (by simp)
    (rowLoop_relInTS fs store (R := RowR store r lvP q b nodeP p a pd) hr33 hrb hpb (fun _ h => h) hr1
      hrowRel)
    (b0 + (fs "da_vector_dispatch" + fs (vxName (decide (b = 127)))))
  rw [pow_zero] at kid2
  have hlvRel : coreProgram.RelB CM.sem rd (dlNames.getD lp "") [gen ^ nodeP] [c0, c1] :=
    da_levels_comp lp hlp _ _ hlv
  have kid4 := relAtInWS_of_relInTWS_pure fs cert (lv_pure hlp) (by simp [lvSet])
    (levels_relInTS fs hlp (R := TreeR nodeP lp) (fun _ h => h) hlvRel)
  rw [← dlNames_getElem! (by omega)] at kid4
  have h := relAtInWS_of_walk (S := CM.sem) (fs := fs) (cert := cert) (w := wId) (σ := σ) (rd := rd)
    (R := R) (D := fun _ => False) (Dk := fun _ => False) (fp := fp)
    (N := fs "da_vector_dispatch" + fs (vxName (decide (b = 127))) + (rowTot fs store r 0 +
      ((if N - r = 0 then fs (gapName store) else gapTot fs store (N - r) 0) + (dlTot fs lp + 0))))
    (bws := [fun θ => θ "da_vector_dispatch" + θ (vxName (decide (b = 127))), fun θ => rowTot θ store r 0,
      fun θ => gapTot θ store (N - r) 0, fun θ => dlTot θ lp])
    (find_col store) (Or.inl (by cases store <;> decide +kernel)) rfl hw rfl hev
    (by
      rw [hal, hes, allocDsts_append, show allocDsts (.call dlNames[lp]! [.n 23] [.n 30, .n 31] ::
        colPost.flatMap (Main.slEvs σ)) = allocDsts (colPost.flatMap (Main.slEvs σ)) from rfl, hpd, hqd,
        show (colPre store).filterMap Main.Stmt.allocSz = [(.n 23, .inr (.n 22))] by cases store <;> rfl,
        show colPost.filterMap Main.Stmt.allocSz = [] from rfl]
      simp only [List.map_cons, List.map_nil, List.append_nil, bases]
      rw [← gen_pow_eq_ofK]; rfl)
    (fun q hq => by
      rw [hes, addrs_append, show addrs (.call dlNames[lp]! [.n 23] [.n 30, .n 31] ::
        colPost.flatMap (Main.slEvs σ)) = addrs (colPost.flatMap (Main.slEvs σ)) from rfl, hpad, hqad,
        show (colPre store).filterMap Main.Stmt.addrS = [] by cases store <;> rfl,
        show colPost.filterMap Main.Stmt.addrS = [] from rfl] at hq
      simp at hq)
    ?_ ?_ (fun _ h => h.elim)
  · rw [hal, List.sum_cons, List.sum_nil, Nat.add_zero] at h
    refine h.wmono fun θ => ?_
    have hg : (if N - r = 0 then θ (gapName store) else gapTot θ store (N - r) 0) =
        gapTot θ store (N - r) 0 := by
      split_ifs with h0
      · simp [gapTot, h0]
      · rfl
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, colTot, hg, wId]
    omega
  · rw [hcalls, hal, List.sum_cons, List.sum_nil, Nat.add_zero]
    refine ⟨_, _, R, fun i => lvP ≤ i ∧ i < lvP + 256, rfl, fun i hi => Or.inl (Or.inl hi),
      vd_relAtInS fs cert hb rfl rfl hch hRc b0 (fun _ h => h) rd hcv hcl hws, ?_⟩
    refine ⟨_, _, RowR store r lvP q b nodeP p a pd, fun _ => False, rfl, fun i hi => ?_, kid2, ?_⟩
    · rcases hi with ⟨j, hj, hc⟩ | hl
      · obtain ⟨r1, r2, r3, r4⟩ := hRrow j hj
        rcases hc with rfl | rfl | rfl | rfl | rfl | ⟨hs, rfl | rfl | rfl⟩
        · exact Or.inl (Or.inl r1)
        · exact Or.inl (Or.inl r2)
        · exact Or.inl (Or.inl r3)
        · exact Or.inl (Or.inr (hown (nodeP + 2 * j) (by omega) (by omega)))
        · exact Or.inl (Or.inr (hown (nodeP + 2 * j + 1) (by omega) (by omega)))
        · exact Or.inl (Or.inl (r4 hs).1)
        · exact Or.inl (Or.inl (r4 hs).2.1)
        · exact Or.inl (Or.inl (r4 hs).2.2)
      · exact Or.inr (Or.inr ⟨rfl, hl⟩)
    by_cases hG : N - r = 0
    · refine ⟨_, _, fun _ => False, fun _ => False, rfl, fun i hi => hi.elim, ?_, ?_⟩
      · simp only [hG, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      · simp only [hG, ↓reduceIte]
        refine ⟨_, _, TreeR nodeP lp, fun _ => False, rfl, fun i hi => Or.inl (Or.inr (hown _ hi.1
          (by unfold TreeR at hi; rw [hN]; omega))), kid4 _, ⟨rfl, fun i hi => hi.elim⟩⟩
    · have hGp : 0 < N - r := by omega
      have hgRel : coreProgram.Rel rd (gapName store) [gen ^ 0, gen ^ (N - r), gen ^ nodeP, gen ^ r] [] := by
        rw [pow_zero]
        exact (gap_loop_meaning store rd _ _ _).mpr
          (hgapL fun he => hG ((gen_pow_eq_one_iff (by omega)).mp he))
      have kid3 := fun fp' => relAtInWS_of_freeOn (S := CM.sem) fs freeOn_gap
        (by cases store <;> simp [gapName]) cert
        (relAtInW_of_relInTW_pure fs cert (gap_pure store) (by simp)
          (gapLoop_relInT fs store (R := GapR r (N - r) nodeP) (by omega) (fun _ h => h) hGp hgRel) fp')
      rw [pow_zero] at kid3
      refine ⟨_, _, GapR r (N - r) nodeP, fun _ => False, rfl, fun i hi => ?_, ?_, ?_⟩
      · obtain ⟨d, hd, hi⟩ := hi
        rcases hi with rfl | rfl
        · exact Or.inl (Or.inr (hown (nodeP + 2 * (r + d)) (by omega) (by omega)))
        · exact Or.inl (Or.inr (hown (nodeP + 2 * (r + d) + 1) (by omega) (by omega)))
      · simp only [ne_eq, hG, not_false_eq_true, decide_true, ↓reduceIte]
        exact kid3 _
      · simp only [hG, ↓reduceIte]
        refine ⟨_, _, TreeR nodeP lp, fun _ => False, rfl, fun i hi => Or.inl (Or.inr (hown _ hi.1
          (by unfold TreeR at hi; rw [hN]; omega))), kid4 _, ⟨rfl, fun i hi => hi.elim⟩⟩
  · intro A hA
    rw [hes, loadAddrs_append, show loadAddrs σ (.call dlNames[lp]! [.n 23] [.n 30, .n 31] ::
      colPost.flatMap (Main.slEvs σ)) = loadAddrs σ (colPost.flatMap (Main.slEvs σ)) from rfl,
      loadAddrs_straight σ _ (colPre_straight store), loadAddrs_straight σ _ colPost_straight,
      show (colPre store).filterMap stmtLoad? = [(.n 11, 0), (.n 11, 1), (.n 20, 0), (.n 20, 1)] by
        cases store <;> rfl,
      show colPost.filterMap stmtLoad? = [(.n 33, 0), (.n 33, 1)] from rfl] at hA
    have g11 : σ (.n 11) = gen ^ (h + 2 * b) := by show gen ^ h * (gen ^ b * gen ^ b) = _; ring
    have g20 : σ (.n 20) = gen ^ (h + 2 * b + 2) := by
      show gen ^ h * (gen ^ b * gen * (gen ^ b * gen)) = _; ring
    have g33 : σ (.n 33) = gen ^ (t + 2 * b) := by show gen ^ t * (gen ^ b * gen ^ b) = _; ring
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hA
    rcases hA with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by rw [g11, addr_gen], Or.inr (Or.inl (hRh 0 (by omega)))⟩
    · exact ⟨_, by rw [g11, addr_gen], Or.inr (Or.inl (hRh 1 (by omega)))⟩
    · exact ⟨_, by rw [g20, addr_gen], Or.inr (Or.inl (by have := hRh 2 (by omega); rwa [Nat.add_zero] at *))⟩
    · exact ⟨_, by rw [g20, addr_gen], Or.inr (Or.inl (by
        have := hRh 3 (by omega); rwa [show h + 2 * b + 2 + 1 = h + 2 * b + 3 by ring]))⟩
    · exact ⟨_, by rw [g33, addr_gen], Or.inr (Or.inl (hRt 0 (by omega)))⟩
    · exact ⟨_, by rw [g33, addr_gen], Or.inr (Or.inl (hRt 1 (by omega)))⟩

/-! ## The column loops -/

/-- A column's memory over a completeness model (`ColMem`): the row cells and the column tree
over the model's answers. -/
def ColMemC (CM : CompModel) (store : Bool) (rd : Reader) (b r N lp : ℕ)
    (pb ct rb hs ctr node lv h0 h1 o0 o1 c0 c1 : E) (ws cv : List E) : Prop :=
  CellsAt rd (hs * (gen ^ b * gen ^ b)) [h0, h1] ∧
  CellsAt rd (hs * (gen ^ b * gen * (gen ^ b * gen))) [o0, o1] ∧
  CellsAt rd (ctr * (gen ^ b * gen ^ b * gen ^ b)) cv ∧
  (∀ k < 256, ∀ v, rd (lv.limb 0 * Parameters.gpow k) = some v → v = ws.getD k 0) ∧
  (∀ j < r, RowCellM CM.hm store rd lv rb (gen ^ b) node pb (gen ^ j)) ∧
  (∀ d < N - r, GapStep rd node (gen ^ r) (gen ^ d)) ∧
  Meaning_da_levelsWith CM.hm lp rd [node] [c0, c1] ∧
  CellsAt rd (ct * (gen ^ b * gen ^ b)) [c0, c1]

/-- A column's memory at `fp` over a completeness model (`ColAt`). -/
def ColAtC (CM : CompModel) (fs : String → ℕ) (cert : String → V → ℕ) (store : Bool) (rd : Reader)
    (b r N lp p t q h c : ℕ) (h0 h1 o0 o1 c0 c1 : E) (ws cv : List E) (fp : ℕ) : Prop :=
  ColMemC CM store rd b r N lp (gen ^ p) (gen ^ t) (gen ^ q) (gen ^ h) (gen ^ c)
    (gen ^ (fp + fs (colName store)))
    (gen ^ (fp + fs (colName store) + 4 * N + fs "da_vector_dispatch" +
      cert (vxName (decide (b = 127))) (.n 4)))
    h0 h1 o0 o1 c0 c1 ws cv

/-- **One iteration of the column loop under `S`** (`colLoop_iter`). -/
theorem colLoop_iterS (fs : String → ℕ) (cert : String → V → ℕ) (store : Bool) {rd : Reader}
    {R : ℕ → Prop} {ps : List E} (hps : ps.length = 9) {j m n : ℕ} (hj : j < clHi store) (fp : ℕ)
    {Bc Bt : (String → ℕ) → ℕ}
    (hcol : RelAtInWS S fs cert wId rd R (fun _ => False) (fp + fs (colLoopName store) + m) n
      (colName store) (gen ^ j :: ps) [] Bc)
    (htail : if j + 1 < clHi store then RelAtInWS S fs cert wId rd R (fun _ => False)
      (fp + fs (colLoopName store)) m (colLoopName store) (gen ^ (j + 1) :: ps) [] Bt
      else m = fs (colLoopName store)) :
    RelAtInWS S fs cert wId rd R (fun _ => False) fp (fs (colLoopName store) + m + n)
      (colLoopName store) (gen ^ j :: ps) [] fun θ => θ (colLoopName store) + Bc θ + Bt θ := by
  match ps, hps with
  | [nb, np, gap, glp, pb, ct, rb, hs, ctr], _ =>
  have hend : colLoopEnd store = gen ^ clHi store := by rw [colLoopEnd_eq]; cases store <;> rfl
  have hhi : clHi store ≤ 128 := by cases store <;> decide
  let σ : Val := listVal [gen ^ j, nb, np, gap, glp, pb, ct, rb, hs, ctr, gen, gen ^ (j + 1),
    colLoopEnd store, gen ^ (j + 1) + colLoopEnd store, gen, gen ^ (j + 1)]
  have h13 : σ (.n 13) ≠ 0 ↔ j + 1 < clHi store := by
    show gen ^ (j + 1) + colLoopEnd store ≠ 0 ↔ _
    rw [hend, ne_eq, e_add_eq_zero_iff]
    exact ⟨fun h => by by_contra h'; exact h (by rw [show j + 1 = clHi store by omega]),
      fun h he => by have := gen_pow_inj' (by omega) (by omega) he; omega⟩
  have hholds : Stmt.HoldsListB S (coreProgram.RelB S rd) rd σ (colLoopBody store) False
      (fun rs => rs = []) := by
    simp only [colLoopBody, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil,
      word_gen]
    refine ⟨hcol.toRelAtIn.relAt.rel, rfl, (pow_succ gen j).symm ▸ rfl, rfl, rfl, rfl,
      (pow_succ gen j).symm ▸ rfl,
      (isInK_add_left (isInK_gen_pow _)).mpr (colLoopEnd_isInK store), fun hne => ?_, trivial⟩
    have ht := (h13.mp hne)
    rw [ite_pos' ht] at htail
    exact htail.toRelAtIn.relAt.rel
  have hw : walk σ (colLoopBody store) =
      .ret ((colLoopBody store).dropLast.flatMap (Main.slEvs σ)) [] :=
    (congrArg (walk σ) (colLoopBody_split store)).trans
      (Main.walk_straight σ [] _ (colLoopPre_straight store))
  have hev := holdsB_of_holdsList (find_colLoop store) hholds hw
  obtain ⟨had, hal, hadr, hcl⟩ := Main.straight_parts σ _ (colLoopPre_straight store)
  have hal0 : allocs σ ((colLoopBody store).dropLast.flatMap (Main.slEvs σ)) = [] := by
    rw [hal]; cases store <;> rfl
  have hcalls : calls ((colLoopBody store).dropLast.flatMap (Main.slEvs σ)) =
      [⟨colName store, [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9], [], true⟩] ++
      [⟨colLoopName store, [.n 15, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9], [],
        decide (σ (.n 13) ≠ 0)⟩] := by
    rw [hcl]; cases store <;> rfl
  have h := relAtInWS_of_walk_loop (S := S) (fs := fs) (cert := cert) (w := wId) (σ := σ) (rd := rd)
    (R := R) (D := fun _ => False) (Dk := fun _ => False) (Rt := R) (Dt := fun _ => False) (fp := fp)
    (m := m) (N := n) (bws := [Bc]) (bt := Bt) (find_colLoop store) (by cases store <;> decide +kernel)
    rfl hw rfl hev hcalls ?_
    (by rw [had, hal0]; cases store <;> rfl)
    (fun q hq => by
      rw [hadr, show (colLoopBody store).dropLast.filterMap Main.Stmt.addrS = [] by
        cases store <;> rfl] at hq
      simp at hq)
    (by rw [hal0]; exact ⟨n, 0, R, fun _ => False, rfl, fun i hi => Or.inl (Or.inl hi), hcol,
      ⟨rfl, fun i h => h.elim⟩⟩)
    (fun i hi => Or.inl hi)
    (fun A hA => by
      rw [loadAddrs_straight σ _ (colLoopPre_straight store),
        show (colLoopBody store).dropLast.filterMap stmtLoad? = [] by cases store <;> rfl] at hA
      simp at hA)
    (fun _ h => h.elim)
  · simp only [hal0, List.sum_nil, Nat.add_zero, List.map_cons, List.map_nil, List.sum_cons] at h
    exact h
  · by_cases ht : j + 1 < clHi store
    · rw [ite_pos' ht] at htail
      simp only [decide_eq_true (h13.mpr ht), ↓reduceIte]
      exact htail
    · rw [ite_neg' ht] at htail
      have : ¬ σ (.n 13) ≠ 0 := fun h => ht (h13.mp h)
      simp only [this, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact htail

/-- **The column loop at iteration `j` over a completeness model** (`colLoop_relAtIn`). -/
theorem colLoop_relAtInC (fs : String → ℕ) (cert : String → V → ℕ) {CM : CompModel} (store : Bool)
    {r N lp p t q h c a pd : ℕ}
    (hr1 : 1 ≤ r) (hrN : r ≤ N) (hN : N = 2 ^ lp) (hlp : lp ≤ 10)
    {H0 H1 O0 O1 C0 C1 : ℕ → E} {WS CV : ℕ → List E} (hcl : ∀ b, (CV b).length = 4)
    (hch : ∀ b < 128, ChainSteps CM.sem (H0 b, H1 b) (vxBlocks ((WS b).getD · 0))
      (vxMd (decide (b = 127)) ((CV b).getD · 0)) 96 (O0 b, O1 b))
    {R : ℕ → Prop} (hRc : ∀ b < 128, ∀ k < 4, R (c + 3 * b + k))
    (hRh : ∀ b < 128, ∀ k < 4, R (h + 2 * b + k)) (hRt : ∀ b < 128, ∀ k < 2, R (t + 2 * b + k))
    (hRrow : ∀ b < clHi store, ∀ j < r, R (q + j) ∧ R (a + 129 * j + b) ∧ R (a + 129 * j + b + 1) ∧
      (store = true → R (p + j) ∧ R (pd + 128 * j + 2 * b) ∧ R (pd + 128 * j + 2 * b + 1)))
    (fp0 : ℕ) (rd : Reader)
    (hmem : ∀ b, clLo store ≤ b → b < clHi store → ColAtC CM fs cert store rd b r N lp p t q h c
      (H0 b) (H1 b) (O0 b) (O1 b) (C0 b) (C1 b) (WS b) (CV b) (colPos fs store r N lp fp0 b))
    (hrb : ∀ j < r, rd (gpow (q + j)) = some (gen ^ (a + 129 * j)))
    (hpb : store = true → ∀ j < r, rd (gpow (p + j)) = some (gen ^ (pd + 128 * j))) :
    ∀ j, clLo store ≤ j → j < clHi store →
      RelAtInWS CM.sem fs cert wId rd R (fun _ => False) (fp0 + (j - clLo store) * fs (colLoopName store))
        (clTot fs store r N lp j) (colLoopName store)
        [gen ^ j, gen ^ r, gen ^ N, gen ^ (N - r), gen ^ lp, gen ^ p, gen ^ t, gen ^ q, gen ^ h, gen ^ c] []
        fun θ => clTot θ store r N lp j := by
  have hhi : clHi store ≤ 128 := by cases store <;> decide
  suffices H : ∀ k j, j + k + 1 = clHi store → clLo store ≤ j →
      RelAtInWS CM.sem fs cert wId rd R (fun _ => False) (fp0 + (j - clLo store) * fs (colLoopName store))
        (clTot fs store r N lp j) (colLoopName store)
        [gen ^ j, gen ^ r, gen ^ N, gen ^ (N - r), gen ^ lp, gen ^ p, gen ^ t, gen ^ q, gen ^ h, gen ^ c] []
        (fun θ => clTot θ store r N lp j) from
    fun j hj1 hj2 => H (clHi store - j - 1) j (by omega) hj1
  have hcol : ∀ j, clLo store ≤ j → j < clHi store →
      RelAtInWS CM.sem fs cert wId rd R (fun _ => False) (colPos fs store r N lp fp0 j)
        (colTot fs store j r N lp) (colName store)
        [gen ^ j, gen ^ r, gen ^ N, gen ^ (N - r), gen ^ lp, gen ^ p, gen ^ t, gen ^ q, gen ^ h, gen ^ c] []
        (fun θ => colTot θ store j r N lp) :=
    fun j hj1 hj2 => by
      obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8⟩ := hmem j hj1 hj2
      exact col_relAtInC fs cert store (by omega) hr1 hrN hN hlp (hcl j) (hch j (by omega))
        (hRc j (by omega)) (hRh j (by omega)) (hRt j (by omega)) (hRrow j (by omega)) _ rd m1 m2 m3
        (fun k hk v hv => m4 k hk v (by rwa [limb0_gen_pow, gpow_add'])) m5 hrb hpb m6 m7 m8
  intro k
  induction k with
  | zero =>
    intro j hj hlo
    have hlast : ¬ j + 1 < clHi store := by omega
    have := colLoop_iterS fs cert store (ps := [gen ^ r, gen ^ N, gen ^ (N - r), gen ^ lp, gen ^ p,
      gen ^ t, gen ^ q, gen ^ h, gen ^ c]) rfl (j := j) (m := fs (colLoopName store)) (by omega)
      (fp0 + (j - clLo store) * fs (colLoopName store)) (Bt := fun θ => θ (colLoopName store))
      (by have := hcol j hlo (by omega); rwa [colPos, ite_neg' hlast] at this) (by rw [ite_neg' hlast])
    rw [clTot_succ fs store r N lp j (by omega), ite_neg' hlast]
    refine this.wmono fun θ => ?_
    rw [clTot_succ θ store r N lp j (by omega), ite_neg' hlast]
    omega
  | succ k ih =>
    intro j hj hlo
    have hnext : j + 1 < clHi store := by omega
    have ht := ih (j + 1) (by omega) (by omega)
    rw [show j + 1 - clLo store = (j - clLo store) + 1 by omega, Nat.add_mul, Nat.one_mul,
      ← Nat.add_assoc] at ht
    have := colLoop_iterS fs cert store (ps := [gen ^ r, gen ^ N, gen ^ (N - r), gen ^ lp, gen ^ p,
      gen ^ t, gen ^ q, gen ^ h, gen ^ c]) rfl (j := j) (m := clTot fs store r N lp (j + 1)) (by omega)
      (fp0 + (j - clLo store) * fs (colLoopName store))
      (by have := hcol j hlo (by omega); rwa [colPos, ite_pos' hnext] at this)
      (by rw [ite_pos' hnext]; exact ht)
    rw [clTot_succ fs store r N lp j (by omega), ite_pos' hnext]
    refine this.wmono fun θ => ?_
    rw [clTot_succ θ store r N lp j (by omega), ite_pos' hnext]
    omega

end
end LeanVM.Guest.B1.Digest
