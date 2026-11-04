/-
  LeanVM.Guest.B1.Opening.QueriesPlaced5

  A deeper iteration of `opening_queries`' loop, placed (`RelAtIn`).
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlaced4

/-!
# A deeper iteration, placed

`oqIter0_relAtIn`: as `oqIter1_relAtIn`, the iteration at `x = g^j` of a deeper level (one query,
its window pointer `qptrs[x]`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **A deeper iteration, placed.** -/
theorem oqIter0_relAtIn (hP : coreProgram.Wf) (fs : String → ℕ) (cert : String → V → ℕ)
    {s : Oq} (hs : s.RowShape) (hpd1 : 1 ≤ s.pd) (hcd : 2 ≤ s.cd) {loop : String} {fl : Fn}
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop0T s loop) (hlp : coreProgram.loop loop = true)
    {rd : Reader} {R : ℕ → Prop} {fp m j : ℕ} {N qptrs cap flags wp ch mu : E}
    {r : List K} {w : ℕ → E} {q : ℕ} {sb : List Digest} {bp v : E}
    (hok : (⟨s, 10, true, 0, r, w, q, sb, cap, flags⟩ : QD).Ok rd wp bp)
    (hb : LoadHolds rd qptrs j bp)
    (hv : LoadHolds rd ch j v)
    (hv1 : LoadHolds rd ch (j + 1) ((v + rowDot s.base s.I r w) * mu))
    (hK : IsInK (gen ^ j * gen + N))
    (htail : if gen ^ j * gen + N ≠ 0 then
      RelAtIn coreProgram fs cert rd R (fun _ => False) (fp + fs loop) m loop
        [gen ^ j * gen, N, qptrs, cap, flags, wp, ch, mu] []
      else m = fs loop)
    (hRq : OqIn R ((qptrs * gen ^ j).limb 0 * Parameters.addressOfIndex 0))
    (hR1 : OqQReg R s cap flags wp bp q)
    (hRc : ∀ e < 2, OqIn R ((ch * gen ^ j).limb 0 * Parameters.addressOfIndex e)) :
    RelAtIn coreProgram fs cert rd R (fun _ => False) fp (fs loop + m) loop
      [gen ^ j, N, qptrs, cap, flags, wp, ch, mu] [] := by
  set D1 : QD := ⟨s, 10, true, 0, r, w, q, sb, cap, flags⟩ with hD1
  obtain ⟨σ, hσ⟩ : ∃ σ : Val, ∀ w : V, σ w = oqIter0F s [gen ^ j, N, qptrs, cap, flags, wp, ch, mu]
      D1 bp v w.idx := ⟨_, fun _ ↦ rfl⟩
  obtain ⟨hpar, hA, hv1', e8, e9, eC0, eC4, eC7, eC9⟩ :=
    oqIter0_at (σ := σ) hs hpd1 hcd hok hb hv hv1 (fun _ ↦ hσ _)
  have eP : ∀ i < 8, σ (.n i) = [gen ^ j, N, qptrs, cap, flags, wp, ch, mu].getD i 0 := by
    intro i hi
    have := congrArg (·.getD i 0) hpar
    simp only [oqLoopParams] at this
    interval_cases i <;> simpa using this
  set ca : Stmt := .callIf (.n (oqC0 s + 7)) loop
    [.n (oqC0 s + 9), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7] with hca
  set pre := oqLoop0A s ++ [ca] with hpre
  have hok' := oqLoop0A_ok s
  have hfm : pre.all Stmt.flatM = true := by
    rw [hpre, List.all_append, hok'.flatM]; rfl
  have hmo : ∀ x ∈ pre, MatchOk σ x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hok'.matchOk hA x hx
    · simp only [List.mem_singleton] at hx
      subst hx; trivial
  have hbody : fl.body = pre ++ [.ret []] := by rw [hbl, hpre, oqLoop0T, List.append_assoc]; rfl
  set es := pre.flatMap (fmEvs σ) with hes
  have hw : walk σ fl.body = .ret es [] := by rw [hbody]; exact walk_flatM σ [] pre hfm hmo
  obtain ⟨i1, i2, i3, i4⟩ := flatM_parts σ pre hfm
  have hal : pre.filterMap Stmt.allocSz = [] := by
    rw [hpre, List.filterMap_append, hok'.allocSz]; rfl
  have hallocs : allocs σ es = [] := by rw [i2, hal]; rfl
  have hcalls : calls es = [] ++ [⟨loop, [.n (oqC0 s + 9), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7],
      [], decide (σ (.n (oqC0 s + 7)) ≠ 0)⟩] := by
    rw [i4, hpre, List.filterMap_append, hok'.callS]; rfl
  have hev : ∀ e ∈ es, e.Holds rd σ := by
    intro e he
    rw [hes, hpre, List.flatMap_append] at he
    rcases List.mem_append.mp he with he | he
    · exact hok'.evs_holds hA e he
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at he
      change e ∈ slEvs σ ca at he
      simp only [hca, slEvs, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | he
      · show IsInK (σ (.n (oqC0 s + 7)))
        rw [eC7]; exact hK
      · rw [he]; split <;> trivial
  have inR : ∀ A, OqIn R A → ∃ i, A = Parameters.addressOfIndex i ∧
      (ownData cert fp (fp + fs loop + m) loop (allocs σ es) es i ∨ R i ∨ False ∨
        ((⟨loop, [.n (oqC0 s + 9), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7], [],
          decide (σ (.n (oqC0 s + 7)) ≠ 0)⟩ : Call).taken = true ∧ False)) :=
    fun A ⟨i, hi, hr⟩ ↦ ⟨i, hi, Or.inr (Or.inl hr)⟩
  have h := relAtIn_of_walk_loop (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
    hP (R := R) (D := fun _ => False) (Dk := fun _ => False) (Rt := R) (Dt := fun _ => False)
    (fp := fp) (m := m) (N := 0) (args := [gen ^ j, N, qptrs, cap, flags, wp, ch, mu]) (rets := [])
    hfl hlp (hpl ▸ hpar) hw rfl hev hcalls ?_
    (by rw [i1, hal, hallocs]; rfl)
    (fun q hq ↦ ?_) (by rw [hallocs]; exact ⟨rfl, fun _ h ↦ h.elim⟩) (fun i hi ↦ Or.inl hi)
    (fun A hAl ↦ ?_) (fun _ h ↦ h.elim)
  · rw [hallocs, List.sum_nil, Nat.add_zero, Nat.add_zero] at h; exact h
  · have hargs' : ([.n (oqC0 s + 9), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7] : List V).map σ =
        [gen ^ j * gen, N, qptrs, cap, flags, wp, ch, mu] := by
      simp only [List.map_cons, List.map_nil, eC9, eP 1 (by omega), eP 2 (by omega),
        eP 3 (by omega), eP 4 (by omega), eP 5 (by omega), eP 6 (by omega), eP 7 (by omega)]
      rfl
    by_cases ht : gen ^ j * gen + N ≠ 0
    · simp only [ht, ne_eq, not_false_eq_true, ↓reduceIte] at htail
      have htk : decide (σ (.n (oqC0 s + 7)) ≠ 0) = true := by rw [eC7]; exact decide_eq_true ht
      simp only [htk, ↓reduceIte, List.map_nil]
      rw [hargs']; exact htail
    · simp only [ht, ↓reduceIte] at htail
      have htk : decide (σ (.n (oqC0 s + 7)) ≠ 0) = false := by rw [eC7]; exact decide_eq_false ht
      simp only [htk, Bool.false_eq_true, ↓reduceIte]
      exact htail
  · rw [i3, hpre, List.filterMap_append, hok'.addrS] at hq
    simp [hca, Stmt.addrS] at hq
  · rw [loadAddrs_flatM σ pre hfm] at hAl
    obtain ⟨⟨p, off⟩, hq, rfl⟩ := List.mem_map.mp hAl
    rw [hpre, List.filterMap_append] at hq
    rcases List.mem_append.mp hq with hq | hq
    · rcases hok'.load hq with hl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact inR _ (oqQLoad_in (D := D1) hv1' (bp := .n 9) (wp := .n 5)
          ⟨fun o ho ↦ by rw [eP 5 (by omega)]; exact hR1.w o ho,
            fun o ho ↦ by rw [e9]; exact hR1.b o ho, hR1.f, hR1.c⟩ hl)
      · rw [e8]; exact inR _ hRq
      · rw [eC0]; exact inR _ (hRc 0 (by omega))
      · rw [eC4]; exact inR _ (hRc 1 (by omega))
    · simp [hca, stmtLoad?] at hq

end
end LeanVM.Guest.B1
