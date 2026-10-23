/-
  LeanVM.Guest.B1.Opening.QueriesPlaced9

  `opening_queries` placed (`RelAtIn`): the function's own frame, its chain buffer, its loop.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlaced8

/-!
# The function, placed

`oqMain_relAtIn`: `opening_queries` on `(cap, flags, λ, λ_n, qptrs, wp, g^N)` at its honest values
(`oqMainF`), placed at `fp`: its chain buffer of `N + 1` words at `fp + fs name` (its `HeapBuf`),
its odd first query's frame run at `fp + cert name ch`, its loop right after the buffer
(`relAtIn_of_walk`), the loop given placed and loading from `R` and the buffer; it returns the
chain's end times `λ_n`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem fn_loop_main {s : Oq} {odd : ℕ} {name loop : String} {fm : Fn}
    (hfm : coreProgram.find? name = some fm) (hbm : fm.body = oqMainT s odd loop) :
    coreProgram.loop name = false := by
  rw [Program.loop_of_find? hfm, Fn.loop, hbm]
  simp [oqMainT]

/-- **`opening_queries`, placed.** -/
theorem oqMain_relAtIn (hP : coreProgram.Wf) (fs : String → ℕ) (cert : String → V → ℕ)
    {s : Oq} (hs : s.RowShape) (hpd : 4 * s.pd ≤ 80) (hpd1 : 1 ≤ s.pd) (hcd : 2 ≤ s.cd)
    (hcd8 : s.cd ≤ 8) {odd : ℕ} (hodd : odd ≤ 1) {name loop : String} {fm : Fn}
    (hfm : coreProgram.find? name = some fm)
    (hpm : fm.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6])
    (hbm : fm.body = oqMainT s odd loop)
    {rd : Reader} {R : ℕ → Prop} {fp N m : ℕ} (hN : N + 1 < ordG)
    {cap flags lam lamN qptrs wp : E} (hlam : lam ≠ 0)
    {r : List K} {w : ℕ → E} {q : ℕ} {sb : List Digest} {bp hNv : E}
    (h1 : odd = 1 → LoadHolds rd qptrs 0 bp ∧
      (∀ l < s.pd + s.cd, LoadHolds rd bp l (bitE (q.testBit l))) ∧
      (⟨s, 13, true, 0, r, w, q, sb,
        ofK (Parameters.gpow (fp + cert name (.n (oqCh s 13 true)))), cap, flags, rd⟩ : QD).Ok rd wp ∧
      LoadHolds rd (ofK (Parameters.gpow (fp + fs name))) 0 (rowDot s.base s.I r w * lam⁻¹) ∧
      OqIn R (qptrs.limb 0 * Parameters.gpow 0) ∧ OqQReg R s cap flags wp bp q)
    (h0 : odd ≠ 1 → LoadHolds rd (ofK (Parameters.gpow (fp + fs name))) 0 0)
    (hNl : LoadHolds rd (ofK (Parameters.gpow (fp + fs name))) N hNv)
    (hloop : if 1 + gen ^ N ≠ 0 then
      RelAtIn coreProgram fs cert rd (fun i ↦ R i ∨ (fp + fs name ≤ i ∧ i < fp + fs name + (N + 1)))
        (fun _ ↦ False) (fp + fs name + (N + 1)) m loop
        [1, gen ^ N, qptrs, cap, flags, wp, ofK (Parameters.gpow (fp + fs name)), lam⁻¹] []
      else m = fs loop) :
    RelAtIn coreProgram fs cert rd R (fun _ ↦ False) fp (fs name + (N + 1) + m) name
      [cap, flags, lam, lamN, qptrs, wp, gen ^ N] [hNv * lamN] := by
  set ch0 : E := ofK (Parameters.gpow (fp + fs name)) with hch0
  set c0 := fp + cert name (.n (oqCh s 13 true)) with hc0
  set D : QD := ⟨s, 13, true, 0, r, w, q, sb, ofK (Parameters.gpow c0), cap, flags, rd⟩ with hD
  obtain ⟨σ, hσ⟩ : ∃ σ : Val, ∀ v : V, σ v = oqMainF s odd [cap, flags, lam, lamN, qptrs, wp, gen ^ N]
      ch0 bp D [ch0 * gen ^ N, hNv, hNv * lamN] v.idx := ⟨_, fun _ ↦ rfl⟩
  obtain ⟨hpar, e8, e10, e11, eT, eodd, hA⟩ := oqMain_at (σ := σ) hs hpd hcd hcd8 hodd hlam
    (fun h ↦ ⟨(h1 h).1, (h1 h).2.1, (h1 h).2.2.1, (h1 h).2.2.2.1⟩) h0
    [ch0 * gen ^ N, hNv, hNv * lamN] (fun _ ↦ hσ _)
  set k := oqMK s odd with hk
  have t : ∀ o, σ (.n (k + o)) = (oqMainTl (gen ^ N) [ch0 * gen ^ N, hNv, hNv * lamN]).getD o 0 := eT
  have t1 : σ (.n (k + 1)) = 1 + gen ^ N := by rw [t 1]; simp [oqMainTl, word_one]
  have t2 : σ (.n (k + 2)) = 1 := by rw [t 2]; simp [oqMainTl, word_one]
  have t3 : σ (.n (k + 3)) = ch0 * gen ^ N := by rw [t 3]; rfl
  have t4 : σ (.n (k + 4)) = hNv := by rw [t 4]; rfl
  have t5 : σ (.n (k + 5)) = hNv * lamN := by rw [t 5]; rfl
  have eP : ∀ i < 7, σ (.n i) = [cap, flags, lam, lamN, qptrs, wp, gen ^ N].getD i 0 := by
    intro i hi
    have := congrArg (·.getD i 0) hpar
    interval_cases i <;> simpa using this
  -- the body
  set ca : Stmt := .callIf (.n (k + 1)) loop [.n (k + 2), .n 6, .n 4, .n 0, .n 1, .n 5, .n 11, .n 8]
    with hca
  set post : List Stmt := [.atom (.mul (.n (k + 3)) (.n 11) (.n 6)),
    .atom (.load (.n (k + 4)) (.n (k + 3)) 0), .atom (.mul (.n (k + 5)) (.n (k + 4)) (.n 3))]
    with hpost
  set pre := oqMainA s odd ++ (ca :: post) with hpre
  have hok := oqMainA_ok hcd odd
  have hst : pre.all Stmt.straight = true := by
    rw [hpre, List.all_append, hok.straight]; rfl
  have hbody : fm.body = pre ++ [.ret [.n (k + 5)]] := by
    rw [hbm, hpre, oqMainT]; simp [hca, hpost, hk]
  set es := pre.flatMap (slEvs σ) with hes
  have hw : walk σ fm.body = .ret es [.n (k + 5)] := by
    rw [hbody]; exact walk_straight σ _ pre hst
  obtain ⟨i1, i2, i3, i4⟩ := straight_parts σ pre hst
  have hal : pre.filterMap Stmt.allocSz = [(.n 11, .inr (.n 10))] := by
    rw [hpre, List.filterMap_append, oqMainA_allocSz hcd]; rfl
  have hlogN : logG (σ (.n 10)) = N + 1 := by
    rw [e10, ← pow_succ, gen_pow_eq_ofK, logG_spec hN]
  have hallocs : allocs σ es = [N + 1] := by
    rw [i2, hal]; simp [hlogN]
  have hcalls : calls es = [⟨loop, [.n (k + 2), .n 6, .n 4, .n 0, .n 1, .n 5, .n 11, .n 8], [],
      decide (σ (.n (k + 1)) ≠ 0)⟩] := by
    rw [i4, hpre, List.filterMap_append, hok.callS]; rfl
  -- the events hold
  have hev : ∀ e ∈ es, e.Holds rd σ := by
    intro e he
    obtain ⟨x, hx, he⟩ := List.mem_flatMap.mp he
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨a, rfl, -⟩ := hok x hx
      simp only [slEvs, List.mem_singleton] at he
      subst he
      exact hA a hx
    · simp only [hpost, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · simp only [hca, slEvs, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | he
        · show IsInK (σ (.n (k + 1)))
          rw [t1, gen_pow_eq_ofK, ← ofK_one, ← ofK_add]; exact ofK_isInK _
        · rw [he]; split <;> trivial
      · simp only [slEvs, List.mem_singleton] at he
        subst he
        show σ (.n (k + 3)) = σ (.n 11) * σ (.n 6)
        rw [t3, e11, eP 6 (by omega)]; rfl
      · simp only [slEvs, List.mem_singleton] at he
        subst he
        show LoadHolds rd (σ (.n (k + 3))) 0 (σ (.n (k + 4)))
        rw [t3, t4, loadHolds_mul_gen_pow, Nat.add_zero]; exact hNl
      · simp only [slEvs, List.mem_singleton] at he
        subst he
        show σ (.n (k + 5)) = σ (.n (k + 4)) * σ (.n 3)
        rw [t5, t4, eP 3 (by omega)]; rfl
  -- the own data
  have hbufd : ∀ i, fp + fs name ≤ i → i < fp + fs name + (N + 1) →
      ownData cert fp (fp + fs name) name (allocs σ es) es i := by
    intro i h1' h2'
    refine Or.inl ⟨(N + 1, fp + fs name), ?_, h1', by omega⟩
    rw [hallocs]; simp [bases]
  have hrun : odd = 1 → (.n (oqCh s 13 true), 80) ∈ runs es := by
    intro ho
    rw [runs_straight σ pre hst, hpre, List.filterMap_append]
    refine List.mem_append_left _ (List.mem_filterMap.mpr ⟨_, ?_,
      stmtRun_oqRun s _ hpd1 hpd (.n (oqCh s 13 true + 4 * s.pd))⟩)
    simp only [oqMainA, ho, ↓reduceIte, List.mem_append]
    exact Or.inl (Or.inr (Or.inl (Or.inr (oqQuery_frameAddr _ _ _ _ _ _ _ _))))
  have hR : ∀ i, R i → ∃ j, Parameters.gpow i = Parameters.gpow j ∧
      (ownData cert fp (fp + fs name) name (allocs σ es) es j ∨ R j ∨ False) :=
    fun i hi ↦ ⟨i, rfl, Or.inr (Or.inl hi)⟩
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd) hP
    (R := R) (D := fun _ ↦ False) (Dk := fun _ ↦ False) (fp := fp) (N := m)
    (args := [cap, flags, lam, lamN, qptrs, wp, gen ^ N]) (rets := [hNv * lamN])
    hfm (Or.inl (fn_loop_main hfm hbm)) (by rw [hpm]; exact hpar) hw (by simp [t5]) hev
    (by rw [i1, hal, hallocs]; simp [bases, e11, hch0])
    (fun q hq ↦ ?_) ?_ (fun A hA ↦ ?_) (fun _ h ↦ h.elim)
  · rw [hallocs] at h; simpa using h
  · -- the frame address
    rw [i3, hpre, List.filterMap_append] at hq
    rcases List.mem_append.mp hq with hq | hq
    · have hb : ∀ p run, oqAlloc ≠ .frameAddr p run := fun p run h ↦ by cases h
      obtain ⟨run, ⟨h1', h2'⟩, hh⟩ := hok.addr' hb hq
      have hh' : q.2 = .n (oqCh s 13 true) := by
        rw [h2', oqRun_head s _ hpd1] at hh; exact (Option.some.inj hh).symm
      rw [h1', hh']
      -- the odd first query is the only `frameAddr`: its frame address
      by_cases ho : odd = 1
      · subst ho
        have hv : ∀ i, D.b ≤ i → i < D.z + 11 → σ (.n i) = D.val i := fun i hi1 hi2 ↦
          (eodd rfl).2 i hi1 (by
            have h1' := QD.end_eq D
            have h2' : oqMK s 1 = oqEnd s 13 true + 1 := rfl
            have h3' : oqEnd D.s D.b D.emit = oqEnd s 13 true := rfl
            omega)
        exact D.ptr_pp hv hpd
      · exfalso
        have : q ∈ (oqMainA s odd).filterMap Stmt.addrS := hq
        rw [List.mem_filterMap] at this
        obtain ⟨x, hx, hxq⟩ := this
        simp only [oqMainA, ho, ↓reduceIte, List.mem_append, List.mem_cons, List.not_mem_nil,
          or_false] at hx
        rcases hx with ((rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)) | (rfl | rfl | rfl) <;>
          simp [Stmt.addrS] at hxq
    · simp [hca, hpost, Stmt.addrS] at hq
  · -- the loop
    rw [hcalls]
    have hsum : (allocs σ es).sum = N + 1 := by rw [hallocs]; simp
    rw [hsum]
    refine ⟨m, 0, (fun i ↦ R i ∨ (fp + fs name ≤ i ∧ i < fp + fs name + (N + 1))), fun _ ↦ False,
      by omega, fun i hi ↦ ?_, ?_, ⟨rfl, fun _ h ↦ h.elim⟩⟩
    · rcases hi with hi | hi
      · exact Or.inl (Or.inl hi)
      · exact Or.inl (Or.inr (hbufd i hi.1 hi.2))
    · have hargs : ([.n (k + 2), .n 6, .n 4, .n 0, .n 1, .n 5, .n 11, .n 8] : List V).map σ =
          [1, gen ^ N, qptrs, cap, flags, wp, ch0, lam⁻¹] := by
        simp only [List.map_cons, List.map_nil, t2, eP 6 (by omega), eP 4 (by omega),
          eP 0 (by omega), eP 1 (by omega), eP 5 (by omega), e11, e8]
        rfl
      by_cases ht : 1 + gen ^ N ≠ 0
      · have htk : decide (σ (.n (k + 1)) ≠ 0) = true := by rw [t1]; exact decide_eq_true ht
        simp only [htk, ↓reduceIte, List.map_nil]
        rw [hargs]
        split at hloop
        · exact hloop
        · next h' => exact absurd ht h'
      · have htk : decide (σ (.n (k + 1)) ≠ 0) = false := by rw [t1]; exact decide_eq_false ht
        simp only [htk, Bool.false_eq_true, ↓reduceIte]
        split at hloop
        · next h' => exact absurd h' ht
        · exact hloop
  · -- the loads
    rw [loadAddrs_straight σ pre hst] at hA
    obtain ⟨⟨p, off⟩, hq, rfl⟩ := List.mem_map.mp hA
    rw [hpre, List.filterMap_append] at hq
    have hb : ∀ d p off, oqAlloc ≠ .load d p off := fun d p off h ↦ by cases h
    rcases List.mem_append.mp hq with hq | hq
    · rcases hok.load' hb hq with ⟨ho, hl⟩ | ⟨ho, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · subst ho
        obtain ⟨-, -, hokD, -, -, hreg⟩ := h1 rfl
        have hv : ∀ i, D.b ≤ i → i < D.z + 11 → σ (.n i) = D.val i := fun i hi1 hi2 ↦
          (eodd rfl).2 i hi1 (by
            have h1' := QD.end_eq D
            have h2' : oqMK s 1 = oqEnd s 13 true + 1 := rfl
            have h3' : oqEnd D.s D.b D.emit = oqEnd s 13 true := rfl
            omega)
        obtain ⟨i, hi, hr⟩ := oqQLoad_in (R := R) cert (f := name) (D := D) hv hpd hcd hcd8
          hokD.hq (bp := .n 12) (wp := .n 5)
          ⟨fun o ho ↦ by rw [eP 5 (by omega)]; exact hreg.w o ho,
            fun o ho ↦ by rw [(eodd rfl).1]; exact hreg.b o ho, hreg.f, hreg.c⟩ rfl hl
        refine ⟨i, hi, ?_⟩
        rcases hr with hr | ⟨h1', h2'⟩
        · exact Or.inr (Or.inl hr)
        · exact Or.inl (Or.inr ⟨_, hrun rfl, h1', h2'⟩)
      · obtain ⟨i, hi, hr⟩ := (h1 ho).2.2.2.2.1
        rw [eP 4 (by omega)]
        exact ⟨i, hi, Or.inr (Or.inl hr)⟩
      · rw [e11, hch0, limb_ofK]
        exact ⟨fp + fs name, by simp, Or.inl (hbufd _ le_rfl (by omega))⟩
      · rw [t3, hch0, addr_gpow]
        exact ⟨_, rfl, Or.inl (hbufd _ (by omega) (by omega))⟩
    · simp only [hca, hpost, stmtLoad?, List.filterMap_cons, List.filterMap_nil,
        List.mem_singleton, Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl⟩ := hq
      rw [t3, hch0, addr_gpow]
      exact ⟨_, rfl, Or.inl (hbufd _ (by omega) (by omega))⟩

end
end LeanVM.Guest.B1
