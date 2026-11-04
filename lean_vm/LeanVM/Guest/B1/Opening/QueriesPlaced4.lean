/-
  LeanVM.Guest.B1.Opening.QueriesPlaced4

  A level-0 iteration of `opening_queries`' loop, placed (`RelAtIn`).
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlaced3

/-!
# A level-0 iteration, placed

`oqIter1_relAtIn`: the iteration at `x = g^j`, placed at `fp`, at its honest values (`oqIter1F`),
its tail at `fp + fs loop`, is `RelAtIn` the caller's region `R`: its body is flat
(`walk_flatM`: its path's `match`es take the arms their windows name), no `HeapBuf`, no
`frameAddr`, every load reading `R` (`OqQReg`: the weights, the windows, the flag, the cap leaf;
the window pointers and the chain).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- What a query of an iteration reads from the caller's region: its weights, its windows (the
path's and the cap's two), its flag and its cap leaf. -/
structure OqQReg (R : ℕ → Prop) (s : Oq) (cap flags wp bp : E) (q : ℕ) : Prop where
  w : ∀ off < s.lo + s.I / s.lo, OqIn R (wp.limb 0 * Parameters.addressOfIndex off)
  b : ∀ off < oqNpw s + 2, OqIn R (bp.limb 0 * Parameters.addressOfIndex off)
  f : OqIn R ((flags * gen ^ (q / 2 ^ (s.pd + 1))).limb 0 * Parameters.addressOfIndex (2 ^
      (s.cd - 1)))
  c : ∀ e < 2, OqIn R ((cap * gen ^ (4 * (q / 2 ^ (s.pd + 1)) +
    (if q.testBit s.pd then 2 else 0))).limb 0 * Parameters.addressOfIndex (2 ^ (s.cd + 1) + e))

/-- **A query's load reads the caller's region.** -/
theorem oqQLoad_in {R : ℕ → Prop} {D : QD} {σ : Val} (hv : D.Hv σ) {bp wp : V}
    (hreg : OqQReg R D.s D.capv D.flagsv (σ wp) (σ bp) D.q) {p : V} {off : ℕ}
    (hl : OqQLoad D.s bp wp D.ch p off) : OqIn R ((σ p).limb 0 * Parameters.addressOfIndex off) := by
  rcases hl with ⟨rfl, ho⟩ | ⟨rfl, ho⟩ | ⟨rfl, rfl⟩ | ⟨rfl, ho⟩
  · exact hreg.w off ho
  · exact hreg.b off ho
  · rw [show (V.n (oqCq D.s D.ch + 2)) = .n (D.Cq + 2) from rfl, D.ptr_flag hv]
    exact hreg.f
  · rw [show (V.n (oqCq D.s D.ch + 8)) = .n (D.Cq + 8) from rfl, D.ptr_cap hv]
    rcases ho with rfl | rfl
    · exact hreg.c 0 (by omega)
    · exact hreg.c 1 (by omega)

/-- **A level-0 iteration, placed.** -/
theorem oqIter1_relAtIn (hP : coreProgram.Wf) (fs : String → ℕ) (cert : String → V → ℕ)
    {s : Oq} (hs : s.RowShape) (hpd1 : 1 ≤ s.pd) (hcd : 2 ≤ s.cd) {odd : ℕ} {loop : String} {fl : Fn}
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop1T s odd loop) (hlp : coreProgram.loop loop = true)
    {rd : Reader} {R : ℕ → Prop} {fp m j : ℕ} {N qptrs cap flags wp ch mu : E}
    {r1 r2 : List K} {w1 w2 : ℕ → E} {q1 q2 : ℕ} {sb1 sb2 : List Digest} {bp1 bp2 v : E}
    (hok1 : (⟨s, 11, true, 0, r1, w1, q1, sb1, cap, flags⟩ : QD).Ok rd wp bp1)
    (hok2 : (⟨s, oqE1 s + 1, false, oqK1 11 s.R + s.D, r2, w2, q2, sb2, cap, flags⟩ : QD).Ok rd wp bp2)
    (hb1 : LoadHolds rd qptrs (2 * j + odd) bp1) (hb2 : LoadHolds rd qptrs (2 * j + odd + 1) bp2)
    (hv : LoadHolds rd ch j v)
    (hv1 : LoadHolds rd ch (j + 1) (((v + rowDot s.base s.I r1 w1) * mu +
      rowDot s.base s.I r2 w2) * mu))
    (hK : IsInK (gen ^ j * gen + N))
    (htail : if gen ^ j * gen + N ≠ 0 then
      RelAtIn coreProgram fs cert rd R (fun _ => False) (fp + fs loop) m loop
        [gen ^ j * gen, N, qptrs, cap, flags, wp, ch, mu] []
      else m = fs loop)
    (hRq : ∀ e < 2, OqIn R ((qptrs * gen ^ j * gen ^ j).limb 0 * Parameters.addressOfIndex
        (odd + e)))
    (hR1 : OqQReg R s cap flags wp bp1 q1) (hR2 : OqQReg R s cap flags wp bp2 q2)
    (hRc : ∀ e < 2, OqIn R ((ch * gen ^ j).limb 0 * Parameters.addressOfIndex e)) :
    RelAtIn coreProgram fs cert rd R (fun _ => False) fp (fs loop + m) loop
      [gen ^ j, N, qptrs, cap, flags, wp, ch, mu] [] := by
  set D1 : QD := ⟨s, 11, true, 0, r1, w1, q1, sb1, cap, flags⟩ with hD1
  set D2 : QD := ⟨s, oqE1 s + 1, false, oqK1 11 s.R + s.D, r2, w2, q2, sb2, cap, flags⟩ with hD2
  obtain ⟨σ, hσ⟩ : ∃ σ : Val, ∀ w : V, σ w = oqIter1F s [gen ^ j, N, qptrs, cap, flags, wp, ch, mu]
      D1 D2 bp1 bp2 v w.idx := ⟨_, fun _ ↦ rfl⟩
  obtain ⟨hpar, hA, hv1', hv2', e9, e10, eE1, eC0, eC6, eC9, eC11⟩ :=
    oqIter1_at (σ := σ) hs hpd1 hcd hok1 hok2 hb1 hb2 hv hv1 (fun _ ↦ hσ _)
  have eP : ∀ i < 8, σ (.n i) = [gen ^ j, N, qptrs, cap, flags, wp, ch, mu].getD i 0 := by
    intro i hi
    have := congrArg (·.getD i 0) hpar
    simp only [oqLoopParams] at this
    interval_cases i <;> simpa using this
  -- the body
  set ca : Stmt := .callIf (.n (oqC1 s + 9)) loop
    [.n (oqC1 s + 11), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7] with hca
  set pre := oqLoop1A s odd ++ [ca] with hpre
  have hok := oqLoop1A_ok s odd
  have hfm : pre.all Stmt.flatM = true := by
    rw [hpre, List.all_append, hok.flatM]; rfl
  have hmo : ∀ x ∈ pre, MatchOk σ x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hok.matchOk hA x hx
    · simp only [List.mem_singleton] at hx
      subst hx; trivial
  have hbody : fl.body = pre ++ [.ret []] := by rw [hbl, hpre, oqLoop1T, List.append_assoc]; rfl
  set es := pre.flatMap (fmEvs σ) with hes
  have hw : walk σ fl.body = .ret es [] := by rw [hbody]; exact walk_flatM σ [] pre hfm hmo
  obtain ⟨i1, i2, i3, i4⟩ := flatM_parts σ pre hfm
  have hal : pre.filterMap Stmt.allocSz = [] := by
    rw [hpre, List.filterMap_append, hok.allocSz]; rfl
  have hallocs : allocs σ es = [] := by rw [i2, hal]; rfl
  have hcalls : calls es = [] ++ [⟨loop, [.n (oqC1 s + 11), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7],
      [], decide (σ (.n (oqC1 s + 9)) ≠ 0)⟩] := by
    rw [i4, hpre, List.filterMap_append, hok.callS]; rfl
  -- the events hold
  have hev : ∀ e ∈ es, e.Holds rd σ := by
    intro e he
    rw [hes, hpre, List.flatMap_append] at he
    rcases List.mem_append.mp he with he | he
    · exact hok.evs_holds hA e he
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at he
      change e ∈ slEvs σ ca at he
      simp only [hca, slEvs, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | he
      · show IsInK (σ (.n (oqC1 s + 9)))
        rw [eC9]; exact hK
      · rw [he]; split <;> trivial
  have inR : ∀ A, OqIn R A → ∃ i, A = Parameters.addressOfIndex i ∧
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
    (fun A hAl ↦ ?_) (fun _ h ↦ h.elim)
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
  · -- no frame address
    rw [i3, hpre, List.filterMap_append, hok.addrS] at hq
    simp [hca, Stmt.addrS] at hq
  · -- the loads
    rw [loadAddrs_flatM σ pre hfm] at hAl
    obtain ⟨⟨p, off⟩, hq, rfl⟩ := List.mem_map.mp hAl
    rw [hpre, List.filterMap_append] at hq
    rcases List.mem_append.mp hq with hq | hq
    · rcases hok.load hq with hl | hl | ⟨rfl, ho⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact inR _ (oqQLoad_in (D := D1) hv1' (bp := .n 10) (wp := .n 5)
          ⟨fun o ho ↦ by rw [eP 5 (by omega)]; exact hR1.w o ho,
            fun o ho ↦ by rw [e10]; exact hR1.b o ho, hR1.f, hR1.c⟩ hl)
      · exact inR _ (oqQLoad_in (D := D2) hv2' (bp := .n (oqE1 s)) (wp := .n 5)
          ⟨fun o ho ↦ by rw [eP 5 (by omega)]; exact hR2.w o ho,
            fun o ho ↦ by rw [eE1]; exact hR2.b o ho, hR2.f, hR2.c⟩ hl)
      · rw [e9]
        rcases ho with rfl | rfl
        · exact inR _ (by simpa using hRq 0 (by omega))
        · exact inR _ (hRq 1 (by omega))
      · rw [eC0]; exact inR _ (hRc 0 (by omega))
      · rw [eC6]; exact inR _ (hRc 1 (by omega))
    · simp [hca, stmtLoad?] at hq

end
end LeanVM.Guest.B1
