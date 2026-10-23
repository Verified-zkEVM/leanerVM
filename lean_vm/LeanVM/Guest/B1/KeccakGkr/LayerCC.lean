/-
  LeanVM.Guest.B1.KeccakGkr.LayerCC

  `keccak_layer`'s pack rounds' setup and last record, completely.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerCB

/-!
# The pack rounds' setup and the last record, completely

* `packSetup_complete`: with the claim's point pointer in its record, the first round record in
  memory, and the pack loop's (and with `odd` the last round's) relations, the setup holds.
* `last_complete`: with the last record in memory, `lastT` reads it and holds.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

variable {C : CallRel} {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val}

theorem capAt_get {rec : E} {k : ℕ} {cap : List E} (h : CapAt rd rec k krCap cap) {j : ℕ}
    (hj : j < 5) : LoadHolds rd rec (k + 16 * j) (cap.getD j 0) := by
  obtain ⟨hl, h⟩ := h
  have := h j (by omega)
  rw [List.getD_eq_getElem _ _ (by omega), show k + 16 * j = k + j * krCap by simp [krCap]; ring]
  exact this

/-- **The pack rounds' setup, completely.** -/
theorem packSetup_complete {first odd : ℕ} (hg : ∀ s ∈ packSetupT first odd, GoodS rd S w σ s)
    (hS : Atom.load (.n 1308) (.n 11) 2 ∉ S) {pp : E} (hpp : LoadHolds rd (σ (.n 11)) 2 pp)
    (hrec : RoundRec rd (σ (.n 1310)) 0 ((cap5 1078).map σ) (σ (.n 7) * gen ^ 47) (σ (.n 1307)) 1)
    (hik : IsInK (1 + σ (.n 9)))
    (hcall : 1 + σ (.n 9) ≠ 0 →
      C (packLoopName first odd) [1, σ (.n 9), σ (.n 1310), pp, σ (.n 1309)] [])
    (hodd : odd = 1 → C "keccak_round" [σ (.n 1310) * σ (.n 9), pp * σ (.n 9) ^ 2,
        σ (.n 1309) * σ (.n 9) ^ 2] []) :
    σ (.n 1308) = pp ∧ ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList C rd σ (packSetupT first odd) next kret := by
  have hg0 := fun s hs ↦ hg s (by rw [packSetupT]; exact List.mem_append_left _ hs)
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true,
    GoodS, Good] at hg0
  obtain ⟨g1308, -, -, -, -, -, -, -, e1311, e1312, -, -, e1313, -, e1314, e1315, e1316⟩ := hg0
  have epp := load_val (w := w) g1308 hS hpp
  simp only [V.n] at e1312
  rw [ite_pos' (by simp)] at e1312
  obtain ⟨hcap, lcur, lcl, lsc⟩ := hrec
  have c : ∀ j < 5, LoadHolds rd (σ (.n 1310)) (16 * j) (σ (.n (1078 + j))) := by
    intro j hj
    have := capAt_get hcap hj
    rw [zero_add] at this
    interval_cases j <;> simpa [cap5] using this
  have e1315' : σ (.n 1315) = 1 + σ (.n 9) := by rw [e1315, e1314, word_one]
  refine ⟨epp, fun {next kret} hn ↦ ?_⟩
  rw [packSetupT, holdsList_append]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]
  refine ⟨by rw [epp]; exact hpp, trivial, trivial, c 0 (by norm_num), c 1 (by norm_num),
    c 2 (by norm_num), c 3 (by norm_num), c 4 (by norm_num), e1311, e1312, ?_, ?_, e1313, ?_,
    e1314, e1315, e1316, by rw [e1315']; exact hik, fun hne ↦ ?_, ?_⟩
  · simpa [krCap, e1312, e1311, gen47] using lcur
  · simpa [krCap] using lcl
  · simpa [krCap, e1313, word_one] using lsc
  · rw [e1316, word_one, epp]
    exact hcall (by rw [← e1315']; exact hne)
  · by_cases ho : odd = 1
    · have hg1 := fun s hs ↦ hg s (by rw [packSetupT]; exact List.mem_append_right _ hs)
      simp only [ho, ↓reduceIte, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
        implies_true, and_true, GoodS, Good, V.n] at hg1
      obtain ⟨e17, e18, e19, e20⟩ := hg1
      rw [ite_pos' (by simp)] at e17 e18 e19 e20
      simp only [ho, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons,
        List.map_nil]
      refine ⟨e17, e18, e19, e20, ?_, hn⟩
      rw [e18, e19, e20, e17, epp]
      simpa [sq] using hodd ho
    · simp only [ho, ↓reduceIte, Stmt.HoldsList]
      exact hn

theorem last_kernel {odd : ℕ} (ho : odd < 2) :
    (lastT (4 * odd)).all isAtom = true ∧ canonChk [] (atomsL ([] ++ lastT (4 * odd))) = true ∧
      resid (atomsL (lastT (4 * odd))) =
        (List.range 5).map (fun j ↦ .load (.n (4 * odd + 1318 + j)) (.n (4 * odd + 1317)) (16 * j)) ++
          [.load (.n (4 * odd + 1323)) (.n (4 * odd + 1317)) 80,
            .load (.n (4 * odd + 1324)) (.n (4 * odd + 1317)) 96] := by
  interval_cases odd
  · exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩
  · exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 20000 in
/-- **The last record, completely**: with the record `rounds·y_last` in memory, its capacity,
cursor and claim are read, and `lastT` holds. -/
theorem last_complete {odd : ℕ} (ho : odd < 2) (hσ : ∀ v, σ v = σ (.n v.idx))
    (hg : ∀ s ∈ lastT (4 * odd), GoodS rd S w σ s)
    (hS : ∀ d off, Atom.load d (.n (4 * odd + 1317)) off ∉ S) {capL : List E} {curL vL scL : E}
    (hrec : RoundRec rd (σ (.n 1310) * σ (.n 10)) 0 capL curL vL scL) :
    σ (.n (4 * odd + 1317)) = σ (.n 1310) * σ (.n 10) ∧
      (cap5 (4 * odd + 1318)).map σ = capL ∧ σ (.n (4 * odd + 1323)) = curL ∧
      σ (.n (4 * odd + 1324)) = vL ∧ ∀ {next : Prop} {kret : List E → Prop}, next →
        Stmt.HoldsList C rd σ (lastT (4 * odd)) next kret := by
  obtain ⟨hall, hk, hr⟩ := last_kernel ho
  have g17 := hg (.atom (.mul (.n (4 * odd + 1317)) (.n 1310) (.n 10)))
      (by unfold lastT; exact List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self))
  simp only [GoodS, Good, V.n] at g17
  rw [ite_pos' (by simp)] at g17
  obtain ⟨⟨hcl, hcap⟩, lcur, lv, -⟩ := hrec
  rw [← g17] at hcap lcur lv
  have gl : ∀ j < 5, Good rd S w σ (.load (.n (4 * odd + 1318 + j)) (.n (4 * odd + 1317)) (16 * j)) :=
    fun j hj ↦ hg (.atom (.load _ _ _))
      (by
        unfold lastT
        exact List.mem_append_left _ (List.mem_append_right _
          (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))
  have hcapj : ∀ j (hj : j < 5), LoadHolds rd (σ (.n (4 * odd + 1317))) (16 * j)
      (capL[j]'(by omega)) := fun j hj ↦ by
    have := hcap j (by omega)
    rwa [zero_add, show j * krCap = 16 * j by simp [krCap]; ring] at this
  have ecap : ∀ j (hj : j < 5), σ (.n (4 * odd + 1318 + j)) = capL[j]'(by omega) :=
    fun j hj ↦ load_val (gl j hj) (hS _ _) (hcapj j hj)
  have g23 : Good rd S w σ (.load (.n (4 * odd + 1323)) (.n (4 * odd + 1317)) 80) :=
    hg (.atom (.load _ _ _)) (by unfold lastT; exact List.mem_append_right _ List.mem_cons_self)
  have g24 : Good rd S w σ (.load (.n (4 * odd + 1324)) (.n (4 * odd + 1317)) 96) :=
    hg (.atom (.load _ _ _))
      (by unfold lastT; exact List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have lcur' : LoadHolds rd (σ (.n (4 * odd + 1317))) 80 curL := by simpa [krCap] using lcur
  have lv' : LoadHolds rd (σ (.n (4 * odd + 1317))) 96 vL := by simpa [krCap] using lv
  refine ⟨g17, ?_, load_val g23 (hS _ _) lcur', load_val g24 (hS _ _) lv', ?_⟩
  · obtain ⟨c0, c1, c2, c3, c4, rfl⟩ : ∃ c0 c1 c2 c3 c4, capL = [c0, c1, c2, c3, c4] := by
      match capL, hcl with
      | [c0, c1, c2, c3, c4], _ => exact ⟨c0, c1, c2, c3, c4, rfl⟩
    have e0 := ecap 0 (by norm_num)
    have e1 := ecap 1 (by norm_num)
    have e2 := ecap 2 (by norm_num)
    have e3 := ecap 3 (by norm_num)
    have e4 := ecap 4 (by norm_num)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] at e0 e1 e2 e3 e4
    simp only [cap5, List.map_cons, List.map_nil, e0, e1, e2, e3, e4]
  · refine block_holdsP (P := []) hall hσ hk (by simpa using hg) (A := []) (by simp) ?_
    rw [hr]
    intro a ha
    right
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
      exact side_load (hS _ _) (hcapj j (List.mem_range.mp hj))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact side_load (hS _ _) lcur'
      · exact side_load (hS _ _) lv'

end
end LeanVM.Guest.B1.VerifySub
