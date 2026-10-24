/-
  LeanVM.Guest.Budget.VsCount

  `verify_sub`'s instructions on a child, per opcode, by its callees at the child's candidate:
  the static callees' and its opening arm's counts (`Count/VsCountData`), and its four callees with
  no static bound within ratios of their words.
-/

module

public import LeanVM.Guest.Count.VsCountChkX
public import LeanVM.Guest.Count.VsCountChkM
public import LeanVM.Guest.Count.VsCountChkS
public import LeanVM.Guest.Count.VsCountChkD
public import LeanVM.Guest.Count.VsCountChkJ
public import LeanVM.Guest.Count.VsCountChkK
public import LeanVM.Guest.Count.RatioV
public import LeanVM.Guest.Budget.FlatShape
public import LeanVM.Guest.B1.Whir.Interface
public import LeanVM.Guest.B1.VerifySub.CompleteBT

/-!
# `verify_sub`'s instructions per candidate

`B1.VerifySub.vsNames μ r`: `verify_sub`'s thirteen callees in call order, its opening arm `openName μ r`
twelfth. `vsWs op c Bs`: a bound on each callee's instructions of `op`, the static ones' and the
arm's (candidate `c`) from the `V` certificates, `verify_bus_gkr`'s, `verify_tables`',
`verify_keccak`'s and `check_opening_terminal`'s within their ratios of their words `Bs[5]`,
`Bs[6]`, `Bs[7]`, `Bs[12]`. `vs_weight_le`: a `verify_sub` node whose callees are those names
within the words `Bs` (`FlatShape`, `NamedWithin`) weighs at most its frame's weight and
`vsWs`. `vs_weight_le_num`: with the four words within `49403`, `59762`, `87672`, `38888`, at most
`vsCountT op c`; `vs_weight_le_vsTs`: the same of B1-d's `vsTs` (its bounds `vsBsAt`).
-/

namespace LeanVM.Guest.Budget

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest
open LeanVM.Guest.Count

@[expose] public section

/-- **The callees' instructions of `op`** at the candidate `c`, the four ratio-bounded ones
within the words `Bs`. -/
def vsWs (op : Opcode) (c : ℕ) (Bs : List ℕ) : List ℕ :=
  [(kcVsStT op).getD 0 0, (kcVsStT op).getD 0 0, (kcVsStT op).getD 1 0, (kcVsStT op).getD 2 0,
    (kcVsStT op).getD 2 0, krVbgA op * Bs.getD 5 0 / 1000, krVtA op * Bs.getD 6 0 / 1000,
    krVkA op * Bs.getD 7 0 / 1000, (kcVsStT op).getD 3 0, (kcVsStT op).getD 4 0,
    (kcVsStT op).getD 5 0, (kcOsT op).getD c 0, krVtermA op * Bs.getD 12 0 / 1000]

theorem vsTab_ok (op : Opcode) : vsTabOk op = true := by
  cases op
  · exact vsTab_ok_x
  · exact vsTab_ok_m
  · exact vsTab_ok_s
  · exact vsTab_ok_d
  · exact vsTab_ok_j
  · exact vsTab_ok_k

/-- A table's entry is a `WeightLe` bound. -/
theorem weightLe_tab {op : Opcode} {j n : ℕ} {f : String}
    (h : (kvOkB op j f && kvSBJ op j == n) = true) :
    WeightLe coreProgram (B2C.ωArm B2C.xmssArmC op) f fun _ => n := by
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hok, hv⟩ := h
  have hw := kvSB_weightLe hok
  have hn : (coreProgram[j]?).map Fn.name = some f := by
    simp only [kvOkB, Bool.and_eq_true, decide_eq_true_eq] at hok; exact hok.1
  rw [kvSB_idx hn, hv] at hw
  exact hw

/-- A table's entry is a `LoopWeightLe` bound. -/
theorem loopWeightLe_tab {op : Opcode} {j n : ℕ} {f : String}
    (h : (kvOkK op j f && kvSKJ op j == n) = true) :
    LoopWeightLe (B2C.ωArm B2C.xmssArmC op) f n := by
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hok, hv⟩ := h
  have hw := kvSK_loop hok
  have hn : (coreProgram[j]?).map Fn.name = some f := by
    simp only [kvOkK, Bool.and_eq_true, decide_eq_true_eq] at hok; exact hok.1
  rw [kvSK_idx hn, hv] at hw
  exact hw

theorem vsTab_parts (op : Opcode) :
    (∀ c < 28, (kvOkB op (osJ.getD c 0) ("open_stacked__L" ++ B1.Whir.natStr c) &&
      kvSBJ op (osJ.getD c 0) == (kcOsT op).getD c 0) = true) ∧
    (∀ i < 6, (kvOkB op (vsStJ.getD i 0) (vsStNames.getD i "") &&
      kvSBJ op (vsStJ.getD i 0) == (kcVsStT op).getD i 0) = true) ∧
    (∀ k < 17, (kvOkB op (cclJ.getD k 0) ("child_claim_list_last__L" ++ B1.Whir.natStr k) &&
      kvSBJ op (cclJ.getD k 0) == (kcCclT op).getD k 0) = true) ∧
    (kvOkB op lsJ "list_split" && kvSBJ op lsJ == kcLs op) = true ∧
    (kvOkK op l17J "__loop17" && kvSKJ op l17J == kcL17 op) = true ∧
    (∀ i < 3, decide ((coreProgram[omJ.getD i 0]?).map Fn.name = some (omNames.getD i "")) = true ∧
      (B2C.plumbOf (omJ.getD i 0 + 1)).pmax.getD (B2C.opIdx op) 0 = (omT op).getD i 0) := by
  have h := vsTab_ok op
  simp only [vsTabOk, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4a⟩, h4b⟩, h5a⟩, h5b⟩, h6⟩ := h
  refine ⟨fun c hc => ?_, fun i hi => ?_, fun k hk => ?_, ?_, ?_, fun i hi => h6 i hi⟩
  · have := h1 c hc; simp only [Bool.and_eq_true, beq_iff_eq]; exact this
  · have := h2 i hi; simp only [Bool.and_eq_true, beq_iff_eq]; exact this
  · have := h3 k hk; simp only [Bool.and_eq_true, beq_iff_eq]; exact this
  · simp only [Bool.and_eq_true, beq_iff_eq]; exact ⟨h4a, h4b⟩
  · simp only [Bool.and_eq_true, beq_iff_eq]; exact ⟨h5a, h5b⟩

/-- **The opening arm of candidate `c`.** -/
theorem kcOs_weightLe (op : Opcode) {c : ℕ} (hc : c < 28) :
    WeightLe coreProgram (B2C.ωArm B2C.xmssArmC op) ("open_stacked__L" ++ B1.Whir.natStr c)
      fun _ => (kcOsT op).getD c 0 :=
  weightLe_tab ((vsTab_parts op).1 c hc)

/-- **`verify_sub`'s static callees.** -/
theorem vsSt_weightLe (op : Opcode) {i : ℕ} (hi : i < 6) :
    WeightLe coreProgram (B2C.ωArm B2C.xmssArmC op) (vsStNames.getD i "")
      fun _ => (kcVsStT op).getD i 0 :=
  weightLe_tab ((vsTab_parts op).2.1 i hi)

/-- **`child_claim_list_last__L{k}`.** -/
theorem ccl_weightLe (op : Opcode) {k : ℕ} (hk : k < 17) :
    WeightLe coreProgram (B2C.ωArm B2C.xmssArmC op) ("child_claim_list_last__L" ++ B1.Whir.natStr k)
      fun _ => (kcCclT op).getD k 0 :=
  weightLe_tab ((vsTab_parts op).2.2.1 k hk)

/-- **`list_split`.** -/
theorem ls_weightLe (op : Opcode) :
    WeightLe coreProgram (B2C.ωArm B2C.xmssArmC op) "list_split" fun _ => kcLs op :=
  weightLe_tab (vsTab_parts op).2.2.2.1

/-- **`__loop17`, per iteration.** -/
theorem l17_loop (op : Opcode) : LoopWeightLe (B2C.ωArm B2C.xmssArmC op) "__loop17" (kcL17 op) :=
  loopWeightLe_tab (vsTab_parts op).2.2.2.2.1

/-- **The frame weights** of `verify_sub`, `child_claim_list_digest`, `__loop5`. -/
theorem om_eq (op : Opcode) {i : ℕ} (hi : i < 3) :
    B2C.ωArm B2C.xmssArmC op (omNames.getD i "") = (omT op).getD i 0 := by
  obtain ⟨hn, hv⟩ := (vsTab_parts op).2.2.2.2.2 i hi
  rw [ωArm_idx (decide_eq_true_eq.mp hn) (by interval_cases i <;> decide), hv]

theorem openName_eq {μ r : ℕ} (h : B1.Whir.candidate μ r < 28) :
    B1.Whir.openName μ r = "open_stacked__L" ++ B1.Whir.natStr (B1.Whir.candidate μ r) := by
  unfold B1.Whir.openName B1.Whir.openNames
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h, Option.map_some,
    Option.getD_some, B1.Whir.natStr_eq]

theorem div_of_ratio {w A t B : ℕ} (h : 1000 * w ≤ A * t) (ht : t ≤ B) : w ≤ A * B / 1000 :=
  (Nat.le_div_iff_mul_le (by norm_num)).mpr (by
    have := Nat.mul_le_mul_left A ht; rw [Nat.mul_comm w]; omega)

set_option maxHeartbeats 1000000 in
/-- **`verify_sub`'s instructions of `op`**: a node whose callees are `B1.VerifySub.vsNames μ r` within the
words `Bs` weighs at most its frame's weight and `vsWs op (candidate μ r) Bs`. -/
theorem vs_weight_le (op : Opcode) {μ r : ℕ} (hc : B1.Whir.candidate μ r < 28) (Bs : List ℕ)
    {rd : Reader} {t : Tree} {args rets : List E}
    (h : FlatShape coreProgram "verify_sub" (List.zipWith (NamedWithin B2C.fs) (B1.VerifySub.vsNames μ r) Bs) t)
    (hv : t.Valid coreProgram rd args rets) (hb : t.BufsOk coreProgram) :
    t.weight (B2C.ωArm B2C.xmssArmC op) ≤
      B2C.ωArm B2C.xmssArmC op "verify_sub" + (vsWs op (B1.Whir.candidate μ r) Bs).sum := by
  refine FlatShape.weight_le _ _ h hv hb (by simp [B1.VerifySub.vsNames, vsWs]) ?_
  intro i hT hW rd' t' args' rets' hv' hb' hTi
  have hi : i < 13 := by simpa [vsWs] using hW
  have hBs : i < Bs.length := by simp at hT; omega
  rw [List.getElem_zipWith] at hTi
  obtain ⟨hn, htot⟩ := hTi
  have hg : Bs[i] = Bs.getD i 0 := by rw [List.getD_eq_getElem]
  rw [hg] at htot
  have st := fun (k : ℕ) (hk : k < 6) (hnk : t'.name = vsStNames.getD k "") =>
    vsSt_weightLe op hk rd' t' args' rets' hnk hv' hb'
  interval_cases i <;> simp only [B1.VerifySub.vsNames, vsWs, List.getElem_cons_zero, List.getElem_cons_succ] at hn ⊢
  · exact st 0 (by norm_num) hn
  · exact st 0 (by norm_num) hn
  · exact st 1 (by norm_num) hn
  · exact st 2 (by norm_num) hn
  · exact st 2 (by norm_num) hn
  · exact div_of_ratio (krVbg_weight op rd' t' args' rets' hn hv' hb') htot
  · exact div_of_ratio (krVt_weight op rd' t' args' rets' hn hv' hb') htot
  · exact div_of_ratio (krVk_weight op rd' t' args' rets' hn hv' hb') htot
  · exact st 3 (by norm_num) hn
  · exact st 4 (by norm_num) hn
  · exact st 5 (by norm_num) hn
  · rw [openName_eq hc] at hn
    exact kcOs_weightLe op hc rd' t' args' rets' hn hv' hb'
  · exact div_of_ratio (krVterm_weight op rd' t' args' rets' hn hv' hb') htot

/-- `vsCountT` is the frame's weight and `vsWs` at the four ratio-bounded callees' words. -/
theorem vsCountT_eq (op : Opcode) : ∀ c < 28, (omT op).getD 0 0 +
    (vsWs op c [0, 0, 0, 0, 0, 49403, 59762, 87672, 0, 0, 0, 0, 38888]).sum = (vsCountT op).getD c 0 := by
  cases op <;> decide +kernel

theorem vsWs_mono (op : Opcode) (c : ℕ) {Bs Bs' : List ℕ} (h5 : Bs.getD 5 0 ≤ Bs'.getD 5 0)
    (h6 : Bs.getD 6 0 ≤ Bs'.getD 6 0) (h7 : Bs.getD 7 0 ≤ Bs'.getD 7 0)
    (h12 : Bs.getD 12 0 ≤ Bs'.getD 12 0) : (vsWs op c Bs).sum ≤ (vsWs op c Bs').sum := by
  have m := fun (A x y : ℕ) (h : x ≤ y) => Nat.div_le_div_right (c := 1000) (Nat.mul_le_mul_left A h)
  have := m (krVbgA op) _ _ h5; have := m (krVtA op) _ _ h6; have := m (krVkA op) _ _ h7
  have := m (krVtermA op) _ _ h12
  simp only [vsWs, List.sum_cons, List.sum_nil]
  omega

/-- **`verify_sub`'s instructions of `op` at candidate `c`, numerically**: its four ratio-bounded
callees within `49403`, `59762`, `87672`, `38888` words. -/
theorem vs_weight_le_num (op : Opcode) {μ r : ℕ} (hc : B1.Whir.candidate μ r < 28) (Bs : List ℕ)
    (h5 : Bs.getD 5 0 ≤ 49403) (h6 : Bs.getD 6 0 ≤ 59762) (h7 : Bs.getD 7 0 ≤ 87672)
    (h12 : Bs.getD 12 0 ≤ 38888) {rd : Reader} {t : Tree} {args rets : List E}
    (h : FlatShape coreProgram "verify_sub" (List.zipWith (NamedWithin B2C.fs) (B1.VerifySub.vsNames μ r) Bs) t)
    (hv : t.Valid coreProgram rd args rets) (hb : t.BufsOk coreProgram) :
    t.weight (B2C.ωArm B2C.xmssArmC op) ≤ (vsCountT op).getD (B1.Whir.candidate μ r) 0 := by
  have h1 := vs_weight_le op hc Bs h hv hb
  have h2 := vsWs_mono op (B1.Whir.candidate μ r)
    (Bs' := [0, 0, 0, 0, 0, 49403, 59762, 87672, 0, 0, 0, 0, 38888]) h5 h6 h7 h12
  have h3 := vsCountT_eq op _ hc
  have h4 := om_eq op (i := 0) (by norm_num)
  simp only [omNames, List.getD_cons_zero] at h4
  omega

/-- **`verify_sub`'s instructions of `op` on a tree of B1-d's shape** (`vsTs`, the callees within
`vsBsAt`), its four ratio-bounded callees' bounds within `49403`, `59762`, `87672`, `38888`
words. -/
theorem vs_weight_le_vsTs (op : Opcode) {W : B1.VerifySub.VsWords B2C.fs} {Bvk μ r : ℕ}
    (hc : B1.Whir.candidate μ r < 28)
    (h5 : B1.VerifySub.vbgMax B2C.fs W.K29 W.R W.K8 ≤ 49403)
    (h6 : B1.VerifySub.vtMax B2C.fs W.Kf W.Ksh W.K10 ≤ 59762) (h7 : Bvk ≤ 87672)
    (h12 : B1.VerifySub.termBound B2C.fs W.Beqc W.K15 W.Bcs W.Brs ≤ 38888)
    {rd : Reader} {t : Tree} {args rets : List E}
    (h : FlatShape coreProgram "verify_sub" (B1.VerifySub.vsTs B2C.fs W Bvk μ r) t)
    (hv : t.Valid coreProgram rd args rets) (hb : t.BufsOk coreProgram) :
    t.weight (B2C.ωArm B2C.xmssArmC op) ≤ (vsCountT op).getD (B1.Whir.candidate μ r) 0 :=
  vs_weight_le_num op hc (B1.VerifySub.vsBsAt W Bvk μ r) h5 h6 h7 h12 h hv hb

end
end LeanVM.Guest.Budget
