/-
  LeanVM.Guest.B1.Placement.CertifyAt

  `certify_placement` is complete in the uniform placed form (`CompleteAtD`): its three buffers
  at the bump allocator's positions, returned.
-/

module

public import LeanVM.Guest.B1.Placement.CertifyComplete
public import LeanVM.Guest.B1.Tables.FlatAt

/-!
# `certify_placement`, placed (TRIAGE G #67)

At frame pointer `fp` the buffers lie at `e2 = fp + fs "certify_placement"` (the columns'
`g^κ`), `e120 = e2 + 113` (the order) and `e121 = e2 + 226` (the offsets), `113` words each;
the function returns the stack's total and the offsets' and sizes' pointers, and its returned
layout is `cpOwn` there (`cpOut`). `certify_placement_completeAt`: `CompleteAtD` on the base and
squares runs `cpLin`, for `κ ≥ 7`, by `completeAt_flatOutD` on the honest valuation `cpσ`
(`cp_body_holds`), every load in the base, the squares or the buffers. `cp_out_ctx`: the
returned buffers satisfy `PCtx`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier hiding Layout gpow
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- What `certify_placement` returns: the stack's total, the offsets' and sizes' pointers, and its
three buffers holding `cpOwn`. -/
def cpOut (lm : ℕ) (hs : List ℕ) : List E → Layout → Prop := fun rets L =>
  ∃ e2 e120 e121 : ℕ, rets = [gen ^ stackTotal (columnKappas lm guestLogBytecode hs),
    ofK (gpow e121), ofK (gpow e2)] ∧ L = cpOwn lm hs e2 e120 e121

/-- The body before its `ret`. -/
def cpPreL : List Stmt :=
  [.atom (.hint (.alloc (.n 2) 113))] ++ ((List.range 113).map cpInit).flatten ++
    [.atom (.hint (.alloc (.n 120) 113)),
      .atom (.hint (.witness "col_sort_order" (.heap (.n 120) 0 113))),
      .atom (.hint (.alloc (.n 121) 113))] ++
    cpRank0 ++ ((List.range 112).map fun r => cpRank (r + 1)).flatten ++
    [.atom (.copy (.n 3049) (.n 3048)), .atom (.copy (.n 3050) (.n 121)),
      .atom (.copy (.n 3051) (.n 2))]

theorem cpBody_eq : cpBody = cpPreL ++ [.ret [.n 3049, .n 3050, .n 3051]] := by
  simp [cpBody, cpPreL]

theorem cp_flat : cpPreL.all Stmt.flat = true := by decide +kernel

theorem cp_addrs : cpPreL.filterMap Main.Stmt.addrS = [] := by decide +kernel

theorem cp_allocs : cpPreL.filterMap Main.Stmt.allocSz =
    [(.n 2, .inl 113), (.n 120, .inl 113), (.n 121, .inl 113)] := by decide +kernel

theorem cp_not_loop : coreProgram.loop "certify_placement" = false := by decide +kernel

/-- Neither a dispatch nor a call. -/
def noCallB : Stmt → Bool
  | .atom _ | .ite .. => true
  | _ => false

theorem cp_noCall : cpPreL.all noCallB = true := by decide +kernel

theorem cpInit_loads : ∀ c < 113,
    (cpInit c).filterMap Stmt.loadS = [(.n 0, colKappaSrc c), (.n 2, c)] := by decide +kernel

theorem cpRank_loads : ∀ r < 112, (cpRank (r + 1)).filterMap Stmt.loadS =
    [(.n 120, r + 1), (.n (111 + 26 * (r + 1) + 5), 0), (.n (111 + 26 * (r + 1) + 18), 0),
      (.n (111 + 26 * (r + 1) + 23), 0)] := by decide +kernel

theorem cp_loads {q : V × ℕ} (hq : q ∈ cpPreL.filterMap Stmt.loadS) :
    (∃ c < 113, q = (.n 0, colKappaSrc c) ∨ q = (.n 2, c)) ∨
      q = (.n 120, 0) ∨ q = (.n 127, 0) ∨ q = (.n 130, 0) ∨ q = (.n 135, 0) ∨
      ∃ r < 112, q = (.n 120, r + 1) ∨ q = (.n (111 + 26 * (r + 1) + 5), 0) ∨
        q = (.n (111 + 26 * (r + 1) + 18), 0) ∨ q = (.n (111 + 26 * (r + 1) + 23), 0) := by
  simp only [cpPreL, List.filterMap_append, List.filterMap_flatten, List.map_map,
    List.mem_append, List.mem_flatten, List.mem_map, List.mem_range] at hq
  rcases hq with ((((hq | ⟨_, ⟨c, hc, rfl⟩, hq⟩) | hq) | hq) | ⟨_, ⟨r, hr, rfl⟩, hq⟩) | hq
  · simp [Stmt.loadS] at hq
  · simp only [Function.comp_apply, cpInit_loads c hc, List.mem_cons,
      List.not_mem_nil, or_false] at hq
    exact Or.inl ⟨c, hc, hq⟩
  · simp [Stmt.loadS] at hq
  · simp only [cpRank0, List.filterMap_cons, Stmt.loadS, List.filterMap_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hq
    rcases hq with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · simp only [Function.comp_apply, cpRank_loads r hr, List.mem_cons, List.not_mem_nil,
      or_false] at hq
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨r, hr, hq⟩))))
  · simp [Stmt.loadS] at hq

theorem cp_limb_mul (b c : ℕ) : (ofK (gpow b) * gen ^ c).limb 0 * gpow 0 = gpow (b + c) := by
  have e : ofK (gpow b) * gen ^ c = ofK (gpow (b + c)) := by
    rw [gen_pow_eq_ofK, ← ofK_mul, gpow, gpow, gpow, pow_add]
  rw [e, tb_addr_ofK, Nat.add_zero]

/-- **`certify_placement` is complete, placed**: on its base and squares runs, at every frame
pointer, on memories defined below `2^κ`, `κ ≥ 7`, its buffers at the bump allocator's positions,
returned. -/
theorem certify_placement_completeAt (fs : String → ℕ) (cert : String → V → ℕ) {k : ℕ}
    (hk : 7 ≤ k) {lm : ℕ} {hs : List ℕ} (hl : hs.length = 6) (hlm : lm ≤ 32)
    (hhs : ∀ h ∈ hs, h < 29) (h5 : hs.getD 5 0 ≤ 27) (ekb esq : ℕ) :
    CompleteAtD fs cert k "certify_placement" (cpLin lm hs ekb esq)
      [ofK (gpow ekb), ofK (gpow esq)] (cpOut lm hs) := by
  have hf : coreProgram.find? "certify_placement" = some Data.core15 :=
    Program.find?_of_indexOf? (j := 15) (by decide +kernel) rfl
  set f := "certify_placement"
  have hb : Data.core15.body = cpPreL ++ [.ret [.n 3049, .n 3050, .n 3051]] :=
    core15_body.trans cpBody_eq
  have hown : List.Forall₂ (fun c s => c.length ≤ s)
      [(cpKs lm hs).map (gen ^ ·), (cpOrd lm hs).map (gen ^ ·),
        (stackOffsets (cpKs lm hs)).1.map (gen ^ ·)] [113, 113, 113] := by
    simp [cpKs_length, cpOrd_length, tb_stackOffsets_length]
  have hbuf : ∀ fp, bufL (fp + fs f) [113, 113, 113]
      [(cpKs lm hs).map (gen ^ ·), (cpOrd lm hs).map (gen ^ ·),
        (stackOffsets (cpKs lm hs)).1.map (gen ^ ·)] =
        cpOwn lm hs (fp + fs f) (fp + fs f + 113) (fp + fs f + 113 + 113) := by
    intro fp; simp [bufL, bases, cpOwn]
  refine completeAt_flatOutD (fs := fs) (cert := cert) hf cp_not_loop k (cpLin lm hs ekb esq) _
    (fun fp ↦ [gen ^ stackTotal (columnKappas lm guestLogBytecode hs),
      ofK (gpow (fp + fs f + 113 + 113)), ofK (gpow (fp + fs f))]) _ hb cp_flat cp_addrs
    [113, 113, 113] (fun _ ↦ [(cpKs lm hs).map (gen ^ ·), (cpOrd lm hs).map (gen ^ ·),
      (stackOffsets (cpKs lm hs)).1.map (gen ^ ·)])
    (fun _ ↦ hown) (fun fp ↦ ⟨_, _, _, rfl, hbuf fp⟩) (fun _ ↦ []) (fun _ _ h ↦ absurd h (by simp))
    (fun _ _ h ↦ absurd h (by simp)) (fun _ _ _ _ _ h ↦ absurd h (by simp)) ?_
  intro fp outs ho rd hlow hB hLin
  rw [hbuf fp] at hB
  have hm : MemLay rd (cpOwn lm hs (fp + fs f) (fp + fs f + 113) (fp + fs f + 113 + 113) ++
      cpLin lm hs ekb esq) := memLay_append.mpr ⟨hB, hLin⟩
  have hbody := cp_body_holds hl hlm hhs h5 ekb esq (fp + fs f) (fp + fs f + 113)
    (fp + fs f + 113 + 113) rd hm (hlow.mono hk)
  set σ := cpσ lm hs ekb esq (fp + fs f) (fp + fs f + 113) (fp + fs f + 113 + 113) rd with hσ
  have hnc : ∀ s ∈ cpPreL, noCallB s = true := fun s hs ↦ List.all_eq_true.mp cp_noCall s hs
  have hK : ∀ r < 113, cpKF lm hs r < 34 := fun r hr ↦ cpKs_lt hl hlm hhs h5 (cpColF_lt hr)
  have hsq : gSquaresList.length = 34 := by simp [gSquaresList]
  have hkb : (1 :: gen ^ lm :: hs.map (gen ^ ·)).length = 8 := by simp [hl]
  set_option maxRecDepth 4000 in
  refine ⟨σ, rfl, fun s hs ↦ ?_, by rw [core15_body]; exact hbody, ?_, ?_, ?_, ?_⟩
  · have := hnc s hs
    cases s <;> first | exact True.intro | simp [noCallB] at this
  · rw [cp_allocs]; rfl
  · rw [cp_allocs]; rfl
  · have : cpPreL.filterMap (Stmt.callSF σ) = [] := by
      rw [List.filterMap_eq_nil_iff]
      intro s hs
      have := hnc s hs
      cases s <;> first | rfl | simp [noCallB] at this
    rw [this]
    match outs, ho with
    | [], _ => exact True.intro
  · intro q hq
    have hOwn : ∀ j < 3, ∀ i, fp + fs f + 113 * j ≤ i → i < fp + fs f + 113 * j + 113 →
        RegionL (bufL (fp + fs f) [113, 113, 113]
        [(cpKs lm hs).map (gen ^ ·), (cpOrd lm hs).map (gen ^ ·),
          (stackOffsets (cpKs lm hs)).1.map (gen ^ ·)]) i := by
      intro j hj i hi1 hi2
      rw [hbuf fp]
      interval_cases j
      · exact ⟨_, List.mem_cons_self, by omega, by simp [cpKs_length]; omega⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by omega,
          by simp [cpOrd_length]; omega⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), by omega,
          by simp [tb_stackOffsets_length, cpKs_length]; omega⟩
    have hKb : ∀ s < 8, RegionL (cpLin lm hs ekb esq) (ekb + s) := fun s hs ↦
      ⟨_, List.mem_cons_self, by omega, by simp only [hkb]; omega⟩
    have hSq : ∀ s < 34, RegionL (cpLin lm hs ekb esq) (esq + s) := fun s hs ↦
      ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by omega, by simp only [hsq]; omega⟩
    have hc0 := cpColF_lt (lm := lm) (hs := hs) (r := 0) (by norm_num)
    rcases cp_loads hq with ⟨c, hc, rfl | rfl⟩ | rfl | rfl | rfl | rfl | ⟨r, hr, rfl | rfl | rfl | rfl⟩
    · exact ⟨ekb + colKappaSrc c, tb_addr_ofK _ _, Or.inl (hKb _ colKappaSrc_lt)⟩
    · exact ⟨fp + fs f + c, by rw [show σ (.n 2) = ofK (gpow (fp + fs f)) from rfl,
        tb_addr_ofK], Or.inr (hOwn 0 (by norm_num) _ (by omega) (by omega))⟩
    · exact ⟨fp + fs f + 113 + 0, by rw [show σ (.n 120) = ofK (gpow (fp + fs f + 113)) from rfl,
        tb_addr_ofK], Or.inr (hOwn 1 (by norm_num) _ (by omega) (by omega))⟩
    · refine ⟨fp + fs f + cpColF lm hs 0, ?_, Or.inr (hOwn 0 (by norm_num) _
        (by omega) (by omega))⟩
      rw [show σ (.n 127) = ofK (gpow (fp + fs f)) * gen ^ cpColF lm hs 0 from
        cpσ_rank0 lm hs ekb esq _ _ _ rd (j := 5) (by norm_num)]
      rw [cp_limb_mul]
    · refine ⟨fp + fs f + 113 + 113 + cpColF lm hs 0, ?_, Or.inr (hOwn 2 (by norm_num) _
        (by omega) (by omega))⟩
      rw [show σ (.n 130) = ofK (gpow (fp + fs f + 113 + 113)) * gen ^ cpColF lm hs 0 from
        cpσ_rank0 lm hs ekb esq _ _ _ rd (j := 8) (by norm_num)]
      rw [cp_limb_mul]
    · refine ⟨esq + cpKF lm hs 0, ?_, Or.inl (hSq _ (hK 0 (by norm_num)))⟩
      rw [show σ (.n 135) = ofK (gpow esq) * gen ^ cpKF lm hs 0 from
        cpσ_rank0 lm hs ekb esq _ _ _ rd (j := 13) (by norm_num)]
      rw [cp_limb_mul]
    · exact ⟨fp + fs f + 113 + (r + 1), by rw [show σ (.n 120) = ofK (gpow (fp + fs f + 113))
        from rfl, tb_addr_ofK], Or.inr (hOwn 1 (by norm_num) _ (by omega) (by omega))⟩
    · have hcr := cpColF_lt (lm := lm) (hs := hs) (r := r + 1) (by omega)
      refine ⟨fp + fs f + cpColF lm hs (r + 1), ?_, Or.inr (hOwn 0 (by norm_num) _
        (by omega) (by omega))⟩
      rw [show σ (.n (111 + 26 * (r + 1) + 5)) = ofK (gpow (fp + fs f)) * gen ^ cpColF lm hs (r + 1) from
        cpσ_rank lm hs ekb esq _ _ _ rd (r := r + 1) (j := 5) (by omega) (by omega) (by norm_num)]
      rw [cp_limb_mul]
    · have hcr := cpColF_lt (lm := lm) (hs := hs) (r := r + 1) (by omega)
      refine ⟨fp + fs f + 113 + 113 + cpColF lm hs (r + 1), ?_, Or.inr (hOwn 2 (by norm_num) _
        (by omega) (by omega))⟩
      rw [show σ (.n (111 + 26 * (r + 1) + 18)) = ofK (gpow (fp + fs f + 113 + 113)) * gen ^ cpColF lm hs (r + 1) from
        cpσ_rank lm hs ekb esq _ _ _ rd (r := r + 1) (j := 18) (by omega) (by omega) (by norm_num)]
      rw [cp_limb_mul]
    · refine ⟨esq + cpKF lm hs (r + 1), ?_, Or.inl (hSq _ (hK (r + 1) (by omega)))⟩
      rw [show σ (.n (111 + 26 * (r + 1) + 23)) = ofK (gpow esq) * gen ^ cpKF lm hs (r + 1) from
        cpσ_rank lm hs ekb esq _ _ _ rd (r := r + 1) (j := 23) (by omega) (by omega) (by norm_num)]
      rw [cp_limb_mul]

/-- **The returned buffers satisfy `PCtx`** on any memory holding them. -/
theorem cp_out_ctx {lm : ℕ} {hs : List ℕ} {rets : List E} {L : Layout} (h : cpOut lm hs rets L)
    {rd : Reader} (hm : MemL rd L) :
    PCtx rd (columnKappas lm guestLogBytecode hs) (rets.getD 1 0) (rets.getD 2 0) := by
  obtain ⟨e2, e120, e121, rfl, rfl⟩ := h
  exact cp_ctx hm

end
end LeanVM.Guest.B1.Tables
