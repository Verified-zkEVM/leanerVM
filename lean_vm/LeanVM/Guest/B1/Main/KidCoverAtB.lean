/-
  LeanVM.Guest.B1.Main.KidCoverAtB

  A child's DA roots within bounds before the memory (`CompleteAtDTB`): `cover_da_root` within its
  frame, `__loop28` within its frames and its `cover_da_root` calls', and the pure digests
  `statement_digest`, `da_list_digest` within their static bounds. Same proofs as `KidCoverAt`.
-/

module

public import LeanVM.Guest.B1.Main.KidCoverAt
public import LeanVM.Guest.Budget.Bounded
public import LeanVM.Guest.Memory.Size

/-!
# A child's DA roots, bounded

`l28B fs t`: `__loop28`'s words over its last `t` iterations, each its frame and its
`cover_da_root` call's frame, plus the last iteration's phantom tail call's frame.
`cover_completeAtB`, `l28_stepAtB`, `l28_completeAtB`; `statement_completeAtB`, `daList_completeAtB`
from `TotalLe` bounds.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1.Da (relAtIn_atoms RunIn SlOk slEvs_holds regionL_of_mem limb0_gen_pow_mul
  fn_name_of_find)
open LeanVM.Guest.B1 (CompleteAtD CompleteAtDTB Returns DisjL Within disj_append within_append LowDef
  completeAt_of_rel_pureBat)

@[expose] public section

/-- **`__loop28`'s words over its last `t` iterations**: each its frame and its `cover_da_root`
call's, and the last one's phantom tail call's frame. -/
def l28B (fs : String → ℕ) (t : ℕ) : ℕ := t * (fs "__loop28" + fs "cover_da_root") + fs "__loop28"

variable (fs : String → ℕ) (cert : String → V → ℕ)

set_option maxRecDepth 10000 in
set_option maxRecDepth 10000 in
/-- **`cover_da_root` is complete, placed**: its slot's cover word and its root's words among the
caller's words. -/
theorem cover_completeAtB {R C n i : ℕ} {mark : E} {r : List E} (hn : n ≤ 2 ^ 16) (hi : i < n)
    (hr : r.length = 4) {Lin : Layout}
    (hmem : ∀ rd, MemL rd Lin → LoadHolds rd (gen ^ C) i mark ∧ ReadsAt rd (gen ^ (R + 4 * i)) r)
    (hRc : RegionL Lin (C + i)) (hRr : ∀ c < 4, RegionL Lin (R + 4 * i + c)) :
    CompleteAtDTB fs cert 16 "cover_da_root" Lin [gen ^ R, gen ^ C, gen ^ n, mark] (Returns r)
      (fun _ => True) (fs "cover_da_root") := by
  intro fp
  refine ⟨fs "cover_da_root", [], r, [], le_rfl, ⟨rfl, rfl⟩, fun q hq => by simp at hq,
    List.Pairwise.nil, fun rd hlow hm => RelAtIn.relAtInT ?_⟩
  simp only [List.append_nil, List.nil_append] at hm
  obtain ⟨hmark, hrets⟩ := hmem rd hm
  match r, hr, hrets with
  | [r0, r1, r2, r3], _, hrets =>
  have h1 := B1.loadHolds_low hlow (i := i) (by omega)
  have h2 := B1.loadHolds_low hlow (i := n - 1 - i) (by omega)
  rw [gen_pow_ofK] at h1 h2
  set t1 := (rd (gpow i)).getD 0
  set t2 := (rd (gpow (n - 1 - i))).getD 0
  have h4 : gen ^ R * ((gen ^ i * gen ^ i) * (gen ^ i * gen ^ i)) = gen ^ (R + 4 * i) := by
    simp only [← pow_add]; congr 1; ring
  have hload : ∀ c < 4, LoadHolds rd (gen ^ R * ((gen ^ i * gen ^ i) * (gen ^ i * gen ^ i))) c
      ([r0, r1, r2, r3].getD c 0) := by
    intro c hc
    rw [h4, List.getD_eq_getElem _ _ (by simpa using hc)]
    exact hrets c (by simpa using hc)
  let σ : Val := Val.ofArgs [gen ^ R, gen ^ C, gen ^ n, mark, gen ^ i, ginvW, gen ^ n * ginvW,
    gen ^ (n - 1 - i), t1, t2, gen ^ C * gen ^ i, gen ^ i * gen ^ i,
    (gen ^ i * gen ^ i) * (gen ^ i * gen ^ i), gen ^ R * ((gen ^ i * gen ^ i) * (gen ^ i * gen ^ i)),
    r0, r1, r2, r3]
  have hh : Stmt.HoldsList (coreProgram.Rel rd) rd σ (Fn.body Data.core30) False
      (fun rs => rs = [r0, r1, r2, r3]) := by
    rw [core30_body]
    simp only [σ, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, ofArgs_n,
      List.getD_cons_succ, List.getD_cons_zero]
    refine ⟨trivial, trivial, trivial, ⟨h1, ?_, h2⟩, trivial, ?_, trivial, trivial, trivial,
      hload 0 (by omega), hload 1 (by omega), hload 2 (by omega), hload 3 (by omega), trivial⟩
    · rw [gen_pow_mul_ginv (by omega), ← pow_add]; congr 1; omega
    · rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact hmark
  rw [cv_split, holdsList_atoms_ret] at hh
  obtain ⟨hat, hrr⟩ := hh
  refine relAtIn_atoms find_cover_da_root cv_split cv_loop (by decide) rfl hat hrr
    (fun q hq => by
      rw [show cvAs.filterMap atomAddr? = [] by decide] at hq; exact absurd hq List.not_mem_nil)
    (fun q hq => ?_) (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq)
  rw [cv_loads] at hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · refine ⟨C + i + 0, ?_, Or.inl hRc⟩
    show (gen ^ C * gen ^ i).limb 0 * gpow 0 = gpow (C + i + 0)
    rw [← pow_add, limb0_gen_pow_mul]
  · refine ⟨R + 4 * i + 0, ?_, Or.inl (hRr 0 (by omega))⟩
    show (gen ^ R * ((gen ^ i * gen ^ i) * (gen ^ i * gen ^ i))).limb 0 * gpow 0 = _
    rw [h4, limb0_gen_pow_mul]
  · refine ⟨R + 4 * i + 1, ?_, Or.inl (hRr 1 (by omega))⟩
    show (gen ^ R * ((gen ^ i * gen ^ i) * (gen ^ i * gen ^ i))).limb 0 * gpow 1 = _
    rw [h4, limb0_gen_pow_mul]
  · refine ⟨R + 4 * i + 2, ?_, Or.inl (hRr 2 (by omega))⟩
    show (gen ^ R * ((gen ^ i * gen ^ i) * (gen ^ i * gen ^ i))).limb 0 * gpow 2 = _
    rw [h4, limb0_gen_pow_mul]
  · refine ⟨R + 4 * i + 3, ?_, Or.inl (hRr 3 (by omega))⟩
    show (gen ^ R * ((gen ^ i * gen ^ i) * (gen ^ i * gen ^ i))).limb 0 * gpow 3 = _
    rw [h4, limb0_gen_pow_mul]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **One step of `__loop28`, placed**: root `d`'s cover check and copy, and the rest. -/
theorem l28_stepAtB {A R C n ed d : ℕ} {base nsub : E} {Lin : Layout} {r : List E}
    (hn : n ≤ 2 ^ 16) (hed : ed < 2 ^ 34) (hd : d + 1 ≤ ed) (hr : r.length = 4) {i : ℕ}
    (hi : i < n)
    (hmem : ∀ rd, MemL rd Lin → LoadHolds rd (gen ^ C) i (base * nsub * gen ^ d) ∧
      ReadsAt rd (gen ^ (R + 4 * i)) r ∧ ReadsAt rd (gen ^ (A + 4 * d)) r)
    (hRc : RegionL Lin (C + i)) (hRr : ∀ c < 4, RegionL Lin (R + 4 * i + c))
    (hRa : ∀ c < 4, RegionL Lin (A + 4 * d + c))
    (htail : d + 1 < ed → CompleteAtDTB fs cert 16 "__loop28" Lin
      [gen ^ (d + 1), gen ^ ed, gen ^ A, gen ^ R, gen ^ C, gen ^ n, base, nsub] (Returns [])
      (fun _ => True) (l28B fs (ed - (d + 1)))) :
    CompleteAtDTB fs cert 16 "__loop28" Lin
      [gen ^ d, gen ^ ed, gen ^ A, gen ^ R, gen ^ C, gen ^ n, base, nsub] (Returns [])
      (fun _ => True) (l28B fs (ed - d)) := by
  have hloop : coreProgram.loop "__loop28" = true := by
    rw [Program.loop_of_find? find_l28, Fn.loop, l28_body, fn_name_of_find find_l28]
    simp [l28Pre]
  intro fp
  obtain ⟨nt, Lt, hnt, hWt, hDt, hRt⟩ : ∃ nt Lt, nt ≤ (if d + 1 < ed then l28B fs (ed - (d + 1))
        else fs "__loop28") ∧ Within Lt (fp + fs "__loop28") nt ∧ DisjL Lt ∧
      ∀ rd, LowDef 16 rd → MemL rd (Lt ++ Lin) →
        if decide (d + 1 ≠ ed) = true then
          RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL []) (fp + fs "__loop28") nt "__loop28"
            [gen ^ (d + 1), gen ^ ed, gen ^ A, gen ^ R, gen ^ C, gen ^ n, base, nsub] []
        else nt = fs "__loop28" := by
    by_cases hlast : d + 1 = ed
    · exact ⟨fs "__loop28", [], by simp [hlast], fun q hq => by simp at hq, List.Pairwise.nil,
        fun _ _ _ => by simp [hlast]⟩
    · obtain ⟨nt, Lt, rt, Lot, hnB, ⟨rfl, rfl⟩, hW, hD, hR⟩ := htail (by omega) (fp + fs "__loop28")
      refine ⟨nt, Lt, by simpa [show d + 1 < ed by omega] using hnB, by simpa using hW,
        by simpa using hD, fun rd hl hm => ?_⟩
      simp only [ne_eq, hlast, not_false_eq_true, decide_true, ↓reduceIte]
      exact (hR rd hl (by simpa using hm)).relAtIn
  obtain ⟨nc, Lc, rc, Loc, hncB, ⟨hrc, rfl⟩, hWc, hDc, hRc'⟩ :=
    cover_completeAtB fs cert (mark := base * nsub * gen ^ d) hn hi hr
      (fun rd hm => ⟨(hmem rd hm).1, (hmem rd hm).2.1⟩) hRc hRr (fp + fs "__loop28" + nt)
  rw [hrc] at hRc'
  simp only [List.nil_append] at hWc hDc hRc'
  refine ⟨fs "__loop28" + nt + nc, Lt ++ Lc, [], [], ?_, ⟨rfl, rfl⟩, ?_,
    by simpa using disj_append hDt hDc hWt hWc le_rfl, fun rd hlow hm => RelAtIn.relAtInT ?_⟩
  · have e : ed - d = ed - (d + 1) + 1 := by omega
    rw [e]
    split at hnt
    · simp only [l28B] at hnt ⊢
      nlinarith
    · have : ed - (d + 1) = 0 := by omega
      simp only [l28B, this] at hnt ⊢
      omega
  · rw [List.nil_append, within_append]
    exact ⟨hWt.mono (by omega) (by omega), hWc.mono (by omega) (by omega)⟩
  simp only [List.nil_append] at hm
  obtain ⟨hm1, hLin⟩ := memL_append.mp hm
  obtain ⟨hmt, hmc⟩ := memL_append.mp hm1
  have ht := hRt rd hlow (memL_append.mpr ⟨hmt, hLin⟩)
  have hc := (hRc' rd hlow (memL_append.mpr ⟨hmc, hLin⟩)).relAtIn
  obtain ⟨-, -, hcopy⟩ := hmem rd hLin
  set σ := l28σ d ed A R C n base nsub r with hσ
  have hw' := Main.walk_straight σ [] l28Pre l28Pre_straight
  rw [← l28_body] at hw'
  obtain ⟨hpd, hpa, hpad, hpc⟩ := Main.straight_parts σ _ l28Pre_straight
  have h19 : σ (.n 19) = gen ^ (d + 1) + gen ^ ed := by
    show gen ^ d * word 2 0 0 + gen ^ ed = _
    rw [word_gen, gen_pow_mul_gen]
  have htk : decide (σ (.n 19) ≠ 0) = decide (d + 1 ≠ ed) := by
    rw [h19]
    refine decide_eq_decide.mpr ⟨fun h he => h (by rw [he]; exact e_add_eq_zero_iff.mpr rfl),
      fun h he => h ?_⟩
    exact gen_pow_inj' (by omega) (by omega) (e_add_eq_zero_iff.mp he)
  have hcalls : calls (l28Pre.flatMap (Main.slEvs σ)) =
      [⟨"cover_da_root", [.n 3, .n 4, .n 5, .n 12], [.n 13, .n 14, .n 15, .n 16], true⟩] ++
        [⟨"__loop28", [.n 21, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7], [], decide (d + 1 ≠ ed)⟩] := by
    rw [hpc, show l28Pre.filterMap Main.Stmt.callS =
      [(none, "cover_da_root", [.n 3, .n 4, .n 5, .n 12], [.n 13, .n 14, .n 15, .n 16]),
        (some (.n 19), "__loop28", [.n 21, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7], [])] from rfl]
    simp only [List.map_cons, List.map_nil, Main.mkCall, htk, List.cons_append, List.nil_append]
  have hal : allocs σ (l28Pre.flatMap (Main.slEvs σ)) = [] := by
    rw [hpa, show l28Pre.filterMap Main.Stmt.allocSz = [] from rfl]; rfl
  have hcp : ∀ k < 4, LoadHolds rd (gen ^ A * ((gen ^ d * gen ^ d) * (gen ^ d * gen ^ d))) k
      (r.getD k 0) := fun k hk => by
    rw [l28_cda, List.getD_eq_getElem _ _ (by omega)]; exact hcopy k (by omega)
  have hev : ∀ e ∈ l28Pre.flatMap (Main.slEvs σ), e.Holds rd σ := by
    refine slEvs_holds fun s hs => ?_
    simp only [l28Pre, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    all_goals simp only [SlOk, Atom.Holds, hσ, l28σ, ofArgs_n, List.getD_cons_succ,
      List.getD_cons_zero]
    · exact hcp 0 (by omega)
    · exact hcp 1 (by omega)
    · exact hcp 2 (by omega)
    · exact hcp 3 (by omega)
    · rw [word_gen, gen_pow_mul_gen]
      exact gen_pow_add_isInK _ _
  have hargs : [V.n 21, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7].map σ =
      [gen ^ (d + 1), gen ^ ed, gen ^ A, gen ^ R, gen ^ C, gen ^ n, base, nsub] := by
    show [gen ^ d * word 2 0 0, gen ^ ed, gen ^ A, gen ^ R, gen ^ C, gen ^ n, base, nsub] = _
    rw [word_gen, gen_pow_mul_gen]
  have hrets : [V.n 13, .n 14, .n 15, .n 16].map σ = r := by
    show [r.getD 0 0, r.getD 1 0, r.getD 2 0, r.getD 3 0] = r
    exact list4_eq hr
  have h := relAtIn_of_walk_loop (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
    (R := RegionL Lin) (D := RegionL []) (Dk := fun _ => False) (Rt := RegionL Lin)
    (Dt := RegionL []) (fp := fp) (m := nt) (N := nc)
    (args := [gen ^ d, gen ^ ed, gen ^ A, gen ^ R, gen ^ C, gen ^ n, base, nsub])
    coreProgram_wf find_l28 hloop (by rw [l28_params]; rfl) hw' rfl hev hcalls
    (by
      by_cases hlast : d + 1 = ed
      · simpa [hlast] using ht
      · simp only [ne_eq, hlast, not_false_eq_true, decide_true, ↓reduceIte] at ht ⊢
        rw [hargs]; exact ht)
    (by rw [hal, hpd, show l28Pre.filterMap Main.Stmt.allocSz = [] from rfl]; rfl)
    (fun q hq => by
      rw [hpad, show l28Pre.filterMap Main.Stmt.addrS = [] from rfl] at hq
      simp at hq)
    (by
      rw [hal]
      refine ⟨nc, 0, RegionL Lin, fun _ => False, rfl, fun i hi => Or.inl (Or.inl hi), ?_,
        ⟨rfl, fun i hi => hi.elim⟩⟩
      simp only [ite_true, List.sum_nil, Nat.add_zero]
      rw [hrets]
      exact B1.relAtIn_dmono hc fun _ h => h.elim)
    (fun i hi => Or.inl hi)
    (fun A' hA => by
      rw [B1.loadAddrs_straight σ _ l28Pre_straight,
        show l28Pre.filterMap B1.Stmt.loadS = [(.n 10, 0), (.n 10, 1), (.n 10, 2), (.n 10, 3)]
          from rfl] at hA
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
      have g10 : σ (.n 10) = gen ^ (A + 4 * d) := l28_cda A d
      rcases hA with rfl | rfl | rfl | rfl
      · exact ⟨A + 4 * d + 0, by rw [g10, limb0_gen_pow_mul], Or.inr (Or.inl (hRa 0 (by omega)))⟩
      · exact ⟨A + 4 * d + 1, by rw [g10, limb0_gen_pow_mul], Or.inr (Or.inl (hRa 1 (by omega)))⟩
      · exact ⟨A + 4 * d + 2, by rw [g10, limb0_gen_pow_mul], Or.inr (Or.inl (hRa 2 (by omega)))⟩
      · exact ⟨A + 4 * d + 3, by rw [g10, limb0_gen_pow_mul], Or.inr (Or.inl (hRa 3 (by omega)))⟩)
    (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq)
  rw [hal] at h
  simp only [List.sum_nil, Nat.add_zero] at h
  exact h

/-- **`__loop28` is complete, placed**, from every counter `d < ed`, when every root `d < ed` has
its slot `slot d < n`, its cover word, its words `r d` at the table and their copy at
`g^(A + 4d)`. -/
theorem l28_completeAtB {A R C n ed : ℕ} {base nsub : E} {Lin : Layout} {slot : ℕ → ℕ}
    {r : ℕ → List E} (hn : n ≤ 2 ^ 16) (hed : ed < 2 ^ 34) (hr : ∀ d < ed, (r d).length = 4)
    (hslot : ∀ d < ed, slot d < n)
    (hmem : ∀ rd, MemL rd Lin → ∀ d < ed, LoadHolds rd (gen ^ C) (slot d) (base * nsub * gen ^ d) ∧
      ReadsAt rd (gen ^ (R + 4 * slot d)) (r d) ∧ ReadsAt rd (gen ^ (A + 4 * d)) (r d))
    (hreg : ∀ d < ed, RegionL Lin (C + slot d) ∧ (∀ c < 4, RegionL Lin (R + 4 * slot d + c)) ∧
      ∀ c < 4, RegionL Lin (A + 4 * d + c)) :
    ∀ d < ed, CompleteAtDTB fs cert 16 "__loop28" Lin
      [gen ^ d, gen ^ ed, gen ^ A, gen ^ R, gen ^ C, gen ^ n, base, nsub] (Returns [])
      (fun _ => True) (l28B fs (ed - d)) := by
  have key : ∀ t d, d + 1 + t = ed → CompleteAtDTB fs cert 16 "__loop28" Lin
      [gen ^ d, gen ^ ed, gen ^ A, gen ^ R, gen ^ C, gen ^ n, base, nsub] (Returns [])
      (fun _ => True) (l28B fs (ed - d)) := by
    intro t
    induction t with
    | zero =>
      intro d hd
      exact l28_stepAtB fs cert hn hed (by omega) (hr d (by omega)) (hslot d (by omega))
        (fun rd hm => hmem rd hm d (by omega)) (hreg d (by omega)).1 (hreg d (by omega)).2.1
        (hreg d (by omega)).2.2 fun h => absurd h (by omega)
    | succ t ih =>
      intro d hd
      exact l28_stepAtB fs cert hn hed (by omega) (hr d (by omega)) (hslot d (by omega))
        (fun rd hm => hmem rd hm d (by omega)) (hreg d (by omega)).1 (hreg d (by omega)).2.1
        (hreg d (by omega)).2.2 fun _ => ih (d + 1) (by omega)
  intro d hd
  exact key (ed - d - 1) d (by omega)

/-- **`statement_digest` within its static bound.** -/
theorem statement_completeAtB {Lin : Layout} {args rets : List E} (SB : String → ℕ)
    (hT : TotalLe coreProgram fs "statement_digest" (fun _ => SB "statement_digest"))
    (h : ∀ rd, MemL rd Lin → MeaningStatementDigest rd args rets) :
    CompleteAtDTB fs cert 16 "statement_digest" Lin args (Returns rets) (fun _ => True)
      (SB "statement_digest") :=
  (completeAt_of_rel_pureBat sd_pure (List.mem_singleton_self _)
    (fun rd hm => statement_digest_complete rd args rets (h rd hm)) 16
    (fun rd t hn hv hb => hT rd t _ _ hn hv hb)).toDTB

/-- **`da_list_digest` within its static bound.** -/
theorem daList_completeAtB {Lin : Layout} {args rets : List E} (SB : String → ℕ)
    (hT : TotalLe coreProgram fs "da_list_digest" (fun _ => SB "da_list_digest"))
    (h : ∀ rd, MemL rd Lin → MeaningDaListDigest rd args rets) :
    CompleteAtDTB fs cert 16 "da_list_digest" Lin args (Returns rets) (fun _ => True)
      (SB "da_list_digest") :=
  (completeAt_of_rel_pureBat dl_pure (by simp [dlSet])
    (fun rd hm => da_list_digest_complete rd args rets (h rd hm)) 16
    (fun rd t hn hv hb => hT rd t _ _ hn hv hb)).toDTB

end
end LeanVM.Guest.B1.Main
