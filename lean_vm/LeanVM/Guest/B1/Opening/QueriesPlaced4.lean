/-
  LeanVM.Guest.B1.Opening.QueriesPlaced4

  A level-0 iteration of `opening_queries`' loop, placed (`RelAtIn`).
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlaced3

/-!
# A level-0 iteration, placed

`oqIter1_relAtIn`: the iteration at `x = g^j`, placed at `fp`, at its honest values (`oqIter1F`,
its two queries' frame addresses `g^(fp + cert loop ch_i)`), its tail at `fp + fs loop`, is
`RelAtIn` the caller's region `R`: its loads read its two frame runs (its own data) or `R`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- What a query of an iteration reads from the caller's region: its weights, its bit run, its
flag and its cap leaf. -/
structure OqQReg (R : ℕ → Prop) (s : Oq) (cap flags wp bp : E) (q : ℕ) : Prop where
  w : ∀ off < s.lo + s.I / s.lo, OqIn R (wp.limb 0 * Parameters.gpow off)
  b : ∀ off < s.pd + s.cd, OqIn R (bp.limb 0 * Parameters.gpow off)
  f : OqIn R ((flags * gen ^ (q / 2 ^ (s.pd + 1))).limb 0 * Parameters.gpow (2 ^ (s.cd - 1)))
  c : ∀ e < 2, OqIn R ((cap * gen ^ (4 * (q / 2 ^ (s.pd + 1)) +
    (if q.testBit s.pd then 2 else 0))).limb 0 * Parameters.gpow (2 ^ (s.cd + 1) + e))

/-- A query's load reads the caller's region or its frame run. -/
theorem oqQLoad_in {R : ℕ → Prop} (cert : String → V → ℕ) {fp : ℕ} {f : String} {D : QD}
    {σ : Val} (hv : ∀ i, D.b ≤ i → i < D.z + 11 → σ (.n i) = D.val i)
    (hpd : 4 * D.s.pd ≤ 80) (hcd : 2 ≤ D.s.cd) (hcd8 : D.s.cd ≤ 8) (hq : D.q < 2 ^ (D.s.pd + D.s.cd))
    {bp wp : V} (hreg : OqQReg R D.s D.capv D.flagsv (σ wp) (σ bp) D.q)
    (hpp : D.pp = ofK (Parameters.gpow (fp + cert f (.n D.ch)))) {p : V} {off : ℕ}
    (hl : OqQLoad D.s bp wp D.ch p off) :
    ∃ i, (σ p).limb 0 * Parameters.gpow off = Parameters.gpow i ∧
      (R i ∨ (fp + cert f (.n D.ch) ≤ i ∧ i < fp + cert f (.n D.ch) + 80)) := by
  rcases hl with ⟨rfl, ho⟩ | ⟨rfl, ho⟩ | ⟨l, hl, rfl, ho⟩ | ⟨rfl, rfl⟩ | ⟨rfl, ho⟩
  · obtain ⟨i, hi, hr⟩ := hreg.w off ho
    exact ⟨i, hi, Or.inl hr⟩
  · obtain ⟨i, hi, hr⟩ := hreg.b off ho
    exact ⟨i, hi, Or.inl hr⟩
  · rw [D.ptr_level hv hl, hpp, addr_gpow]
    refine ⟨_, rfl, Or.inr ⟨by omega, ?_⟩⟩
    rcases ho with rfl | rfl <;> split <;> omega
  · have e : oqCq D.s D.ch + 5 + 6 * (D.s.cd - 2) = D.z := rfl
    rw [e, D.ptr_flag hv hcd hcd8 hq]
    obtain ⟨i, hi, hr⟩ := hreg.f
    exact ⟨i, hi, Or.inl hr⟩
  · have e : oqCq D.s D.ch + 5 + 6 * (D.s.cd - 2) + 10 = D.z + 10 := rfl
    rw [e, D.ptr_cap hv hcd hcd8 hq]
    rcases ho with rfl | rfl
    · obtain ⟨i, hi, hr⟩ := hreg.c 0 (by omega)
      exact ⟨i, hi, Or.inl hr⟩
    · obtain ⟨i, hi, hr⟩ := hreg.c 1 (by omega)
      exact ⟨i, hi, Or.inl hr⟩

/-- **A level-0 iteration, placed.** -/
theorem oqIter1_relAtIn (hP : coreProgram.Wf) (fs : String → ℕ) (cert : String → V → ℕ)
    {s : Oq} (hs : s.RowShape) (hpd : 4 * s.pd ≤ 80) (hpd1 : 1 ≤ s.pd) (hcd : 2 ≤ s.cd)
    (hcd8 : s.cd ≤ 8) {odd : ℕ} {loop : String} {fl : Fn}
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop1T s odd loop) (hlp : coreProgram.loop loop = true)
    {rd : Reader} {R : ℕ → Prop} {fp m j : ℕ} {N qptrs cap flags wp ch mu : E}
    {r1 r2 : List K} {w1 w2 : ℕ → E} {q1 q2 : ℕ} {sb1 sb2 : List Digest} {bp1 bp2 v : E}
    (hok1 : (⟨s, 11, true, 0, r1, w1, q1, sb1,
      ofK (Parameters.gpow (fp + cert loop (.n (oqCh s 11 true)))), cap, flags, rd⟩ : QD).Ok rd wp)
    (hok2 : (⟨s, oqE1 s + 1, false, oqK1 11 s.R + s.D, r2, w2, q2, sb2,
      ofK (Parameters.gpow (fp + cert loop (.n (oqCh s (oqE1 s + 1) false)))), cap, flags, rd⟩ :
        QD).Ok rd wp)
    (hb1 : LoadHolds rd qptrs (2 * j + odd) bp1)
    (hbits1 : ∀ l < s.pd + s.cd, LoadHolds rd bp1 l (bitE (q1.testBit l)))
    (hb2 : LoadHolds rd qptrs (2 * j + odd + 1) bp2)
    (hbits2 : ∀ l < s.pd + s.cd, LoadHolds rd bp2 l (bitE (q2.testBit l)))
    (hv : LoadHolds rd ch j v)
    (hv1 : LoadHolds rd ch (j + 1) (((v + rowDot s.base s.I r1 w1) * mu +
      rowDot s.base s.I r2 w2) * mu))
    (hK : IsInK (gen ^ j * gen + N))
    (htail : if gen ^ j * gen + N ≠ 0 then
      RelAtIn coreProgram fs cert rd R (fun _ => False) (fp + fs loop) m loop
        [gen ^ j * gen, N, qptrs, cap, flags, wp, ch, mu] []
      else m = fs loop)
    (hRq : ∀ e < 2, OqIn R ((qptrs * gen ^ j * gen ^ j).limb 0 * Parameters.gpow (odd + e)))
    (hR1 : OqQReg R s cap flags wp bp1 q1) (hR2 : OqQReg R s cap flags wp bp2 q2)
    (hRc : ∀ e < 2, OqIn R ((ch * gen ^ j).limb 0 * Parameters.gpow e)) :
    RelAtIn coreProgram fs cert rd R (fun _ => False) fp (fs loop + m) loop
      [gen ^ j, N, qptrs, cap, flags, wp, ch, mu] [] := by
  set c01 := fp + cert loop (.n (oqCh s 11 true)) with hc01
  set c02 := fp + cert loop (.n (oqCh s (oqE1 s + 1) false)) with hc02
  set D1 : QD := ⟨s, 11, true, 0, r1, w1, q1, sb1, ofK (Parameters.gpow c01), cap, flags, rd⟩
    with hD1
  set D2 : QD := ⟨s, oqE1 s + 1, false, oqK1 11 s.R + s.D, r2, w2, q2, sb2,
    ofK (Parameters.gpow c02), cap, flags, rd⟩ with hD2
  obtain ⟨σ, hσ⟩ : ∃ σ : Val, ∀ w : V, σ w = oqIter1F s [gen ^ j, N, qptrs, cap, flags, wp, ch, mu]
      D1 D2 bp1 bp2 v w.idx := ⟨_, fun _ ↦ rfl⟩
  obtain ⟨hpar, hA, eQ1, eQ2, e9, e10, eE1, eC0, eC6, eC9, eC11⟩ :=
    oqIter1_at (σ := σ) hs hpd hcd hcd8 hok1 hok2 hb1 hbits1 hb2 hbits2 hv hv1 (fun _ ↦ hσ _)
  have he1 : oqE1 s = D1.z + 11 := QD.end_eq D1
  have hc : oqC1 s = D2.z + 11 := QD.end_eq D2
  have hv1' : ∀ i, D1.b ≤ i → i < D1.z + 11 → σ (.n i) = D1.val i := fun i h1 h2 ↦
    eQ1 i h1 (by omega)
  have hv2' : ∀ i, D2.b ≤ i → i < D2.z + 11 → σ (.n i) = D2.val i := fun i h1 h2 ↦
    eQ2 i h1 (by omega)
  have eP : ∀ i < 8, σ (.n i) = [gen ^ j, N, qptrs, cap, flags, wp, ch, mu].getD i 0 := by
    intro i hi
    have := congrArg (·.getD i 0) hpar
    simp only [oqLoopParams] at this
    interval_cases i <;> simpa using this
  -- the body
  set ca : Stmt := .callIf (.n (oqC1 s + 9)) loop
    [.n (oqC1 s + 11), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7] with hca
  set pre := oqLoop1A s odd ++ [ca] with hpre
  have hok := oqLoop1A_ok hcd odd
  have hst : pre.all Stmt.straight = true := by
    rw [hpre, List.all_append, hok.straight]; rfl
  have hbody : fl.body = pre ++ [.ret []] := by rw [hbl, hpre, oqLoop1T, List.append_assoc]; rfl
  set es := pre.flatMap (slEvs σ) with hes
  have hw : walk σ fl.body = .ret es [] := by rw [hbody]; exact walk_straight σ [] pre hst
  obtain ⟨i1, i2, i3, i4⟩ := straight_parts σ pre hst
  have hal : pre.filterMap Stmt.allocSz = [] := by
    rw [hpre, List.filterMap_append, hok.allocSz]; rfl
  have hallocs : allocs σ es = [] := by rw [i2, hal]; rfl
  have hcalls : calls es = [] ++ [⟨loop, [.n (oqC1 s + 11), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7],
      [], decide (σ (.n (oqC1 s + 9)) ≠ 0)⟩] := by
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
    · simp only [List.mem_singleton] at hx
      subst hx
      simp only [hca, slEvs, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | he
      · show IsInK (σ (.n (oqC1 s + 9)))
        rw [eC9]; exact hK
      · rw [he]; split <;> trivial
  -- the runs
  have hrun1 : (.n (oqCh s 11 true), 80) ∈ runs es := by
    rw [runs_straight σ pre hst, hpre, List.filterMap_append]
    refine List.mem_append_left _ (List.mem_filterMap.mpr ⟨_, ?_,
      stmtRun_oqRun s _ hpd1 hpd (.n (oqCh s 11 true + 4 * s.pd))⟩)
    simp only [oqLoop1A, List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inr (oqQuery_frameAddr _ _ _ _ _ _ _ _))))
  have hrun2 : (.n (oqCh s (oqE1 s + 1) false), 80) ∈ runs es := by
    rw [runs_straight σ pre hst, hpre, List.filterMap_append]
    refine List.mem_append_left _ (List.mem_filterMap.mpr ⟨_, ?_,
      stmtRun_oqRun s _ hpd1 hpd (.n (oqCh s (oqE1 s + 1) false + 4 * s.pd))⟩)
    simp only [oqLoop1A, List.mem_append]
    exact Or.inl (Or.inr (oqQuery_frameAddr _ _ _ _ _ _ _ _))
  have hown1 : ∀ i, c01 ≤ i → i < c01 + 80 →
      ownData cert fp (fp + fs loop + m) loop (allocs σ es) es i :=
    fun i h1 h2 ↦ Or.inr ⟨_, hrun1, h1, h2⟩
  have hown2 : ∀ i, c02 ≤ i → i < c02 + 80 →
      ownData cert fp (fp + fs loop + m) loop (allocs σ es) es i :=
    fun i h1 h2 ↦ Or.inr ⟨_, hrun2, h1, h2⟩
  have inR : ∀ A, OqIn R A → ∃ i, A = Parameters.gpow i ∧
      (ownData cert fp (fp + fs loop + m) loop (allocs σ es) es i ∨ R i ∨ False ∨
        ((⟨loop, [.n (oqC1 s + 11), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7], [],
          decide (σ (.n (oqC1 s + 9)) ≠ 0)⟩ : Call).taken = true ∧ False)) :=
    fun A ⟨i, hi, hr⟩ ↦ ⟨i, hi, Or.inr (Or.inl hr)⟩
  have h := relAtIn_of_walk_loop (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
    hP (R := R) (D := fun _ => False) (Dk := fun _ => False) (Rt := R) (Dt := fun _ => False)
    (fp := fp) (m := m) (N := 0) (args := [gen ^ j, N, qptrs, cap, flags, wp, ch, mu]) (rets := [])
    hfl hlp (hpl ▸ hpar) hw rfl hev hcalls ?_
    (by rw [i1, hal, hallocs]; rfl)
    (fun q hq ↦ ?_) (by rw [hallocs]; exact ⟨rfl, fun _ h ↦ h.elim⟩) (fun i hi ↦ Or.inl hi)
    (fun A hA ↦ ?_) (fun _ h ↦ h.elim)
  · rw [hallocs, List.sum_nil, Nat.add_zero, Nat.add_zero] at h; exact h
  · -- the tail
    have hargs' : ([.n (oqC1 s + 11), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7] : List V).map σ =
        [gen ^ j * gen, N, qptrs, cap, flags, wp, ch, mu] := by
      simp only [List.map_cons, List.map_nil, eC11, eP 1 (by omega), eP 2 (by omega),
        eP 3 (by omega), eP 4 (by omega), eP 5 (by omega), eP 6 (by omega), eP 7 (by omega)]
      rfl
    by_cases ht : gen ^ j * gen + N ≠ 0
    · simp only [ht, ne_eq, not_false_eq_true, ↓reduceIte] at htail
      have htk : decide (σ (.n (oqC1 s + 9)) ≠ 0) = true := by rw [eC9]; exact decide_eq_true ht
      simp only [htk, ↓reduceIte, List.map_nil]
      rw [hargs']; exact htail
    · simp only [ht, ↓reduceIte] at htail
      have htk : decide (σ (.n (oqC1 s + 9)) ≠ 0) = false := by rw [eC9]; exact decide_eq_false ht
      simp only [htk, Bool.false_eq_true, ↓reduceIte]
      exact htail
  · -- the frame addresses
    rw [i3, hpre, List.filterMap_append] at hq
    rcases List.mem_append.mp hq with hq | hq
    · obtain ⟨run, hF, hh⟩ := hok.addr hq
      rcases hF with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hh' : q.2 = .n (oqCh s 11 true) := by
          rw [h2, oqRun_head s _ hpd1] at hh; exact (Option.some.inj hh).symm
        rw [h1, hh']; exact D1.ptr_pp hv1' hpd
      · have hh' : q.2 = .n (oqCh s (oqE1 s + 1) false) := by
          rw [h2, oqRun_head s _ hpd1] at hh; exact (Option.some.inj hh).symm
        rw [h1, hh']; exact D2.ptr_pp hv2' hpd
    · simp [hca, Stmt.addrS] at hq
  · -- the loads
    rw [loadAddrs_straight σ pre hst] at hA
    obtain ⟨⟨p, off⟩, hq, rfl⟩ := List.mem_map.mp hA
    rw [hpre, List.filterMap_append] at hq
    rcases List.mem_append.mp hq with hq | hq
    · rcases hok.load hq with hl | hl | ⟨rfl, ho⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · obtain ⟨i, hi, hr⟩ := oqQLoad_in (R := R) cert (f := loop) (D := D1) hv1' hpd hcd hcd8
          hok1.hq (bp := .n 10) (wp := .n 5)
          ⟨fun o ho ↦ by rw [eP 5 (by omega)]; exact hR1.w o ho,
            fun o ho ↦ by rw [e10]; exact hR1.b o ho, hR1.f, hR1.c⟩ rfl hl
        refine ⟨i, hi, ?_⟩
        rcases hr with hr | ⟨h1, h2⟩
        · exact Or.inr (Or.inl hr)
        · exact Or.inl (hown1 i h1 h2)
      · obtain ⟨i, hi, hr⟩ := oqQLoad_in (R := R) cert (f := loop) (D := D2) hv2' hpd hcd hcd8
          hok2.hq (bp := .n (oqE1 s)) (wp := .n 5)
          ⟨fun o ho ↦ by rw [eP 5 (by omega)]; exact hR2.w o ho,
            fun o ho ↦ by rw [eE1]; exact hR2.b o ho, hR2.f, hR2.c⟩ rfl hl
        refine ⟨i, hi, ?_⟩
        rcases hr with hr | ⟨h1, h2⟩
        · exact Or.inr (Or.inl hr)
        · exact Or.inl (hown2 i h1 h2)
      · rw [e9]
        rcases ho with rfl | rfl
        · exact inR _ (by simpa using hRq 0 (by omega))
        · exact inR _ (hRq 1 (by omega))
      · rw [eC0]; exact inR _ (hRc 0 (by omega))
      · rw [eC6]; exact inR _ (hRc 1 (by omega))
    · simp [hca, stmtLoad?] at hq

end
end LeanVM.Guest.B1
