/-
  LeanVM.Guest.B1.Main.MainStaticB

  `main`'s statically bounded callees within their words: `cover_da_root` within its frame, the
  pure ones (`__loop0`…`__loop4`, `da_list_digest`, `statement_digest`) within the bounds the static
  certificates give every valid tree (`TotalLe`, `TotalLeOn`).
-/

module

public import LeanVM.Guest.B1.Main.KidCoverAt
public import LeanVM.Guest.B1.Main.RawAt
public import LeanVM.Guest.Budget.Bounded
public import LeanVM.Guest.Memory.LoopPre

/-!
# `main`'s static callees, bounded

The static bounds' convention: `SB g` bounds every valid tree of a statically bounded callee `g`
(`TotalLe coreProgram fs g (fun _ => SB g)`), `SK g` an iteration of a statically bounded loop
helper `g` (`TotalLeOn coreProgram fs g LoopPre (fun a => logG (a.getD 1 0) * SK g)`).
`cover_completeAtB`, `daList_completeAtB`, `statement_completeAtB`, `rawX_completeAtB`,
`rawS_completeAtB`: the `CompleteAtD` lifts within those bounds.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1.Da (relAtIn_atoms RunIn SlOk slEvs_holds regionL_of_mem limb0_gen_pow_mul
  fn_name_of_find)
open LeanVM.Guest.B1 (CompleteAtD CompleteAtDTB Returns DisjL Within disj_append within_append LowDef
  completeAt_of_rel_pureD completeAt_of_rel_pureBat completeAtDTB_of_relIn)

@[expose] public section

/-- A loop helper's call from `g^i` to `g^e`, `i < e < 2^64 - 1`, satisfies `LoopPre`. -/
theorem loopPre_pow {i e : ℕ} (hie : i < e) (he : e < 2 ^ 64 - 1) (rest : List E) :
    LoopPre (gen ^ i :: gen ^ e :: rest) :=
  ⟨i, e, by simp [gen_pow_eq_ofK], by simp [gen_pow_eq_ofK], hie, he⟩

theorem logG_gen {e : ℕ} (he : e < 2 ^ 64 - 1) : logG (gen ^ e) = e := by
  rw [gen_pow_eq_ofK]; exact logG_spec he

variable (fs : String → ℕ) (cert : String → V → ℕ)

set_option maxRecDepth 10000 in
/-- **`cover_da_root` is complete within its frame.** -/
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

/-- **`statement_digest` within its static bound.** -/
theorem statement_completeAtB {Lin : Layout} {args rets : List E} {SB : String → ℕ}
    (hT : TotalLe coreProgram fs "statement_digest" (fun _ => SB "statement_digest"))
    (h : ∀ rd, MemL rd Lin → MeaningStatementDigest rd args rets) :
    CompleteAtDTB fs cert 16 "statement_digest" Lin args (Returns rets) (fun _ => True)
      (SB "statement_digest") :=
  (completeAt_of_rel_pureBat sd_pure (List.mem_singleton_self _)
    (fun rd hm => statement_digest_complete rd args rets (h rd hm)) 16
    fun rd t hn hv hb => hT rd t _ _ hn hv hb).toDTB

/-- **`da_list_digest` within its static bound.** -/
theorem daList_completeAtB {Lin : Layout} {args rets : List E} {SB : String → ℕ}
    (hT : TotalLe coreProgram fs "da_list_digest" (fun _ => SB "da_list_digest"))
    (h : ∀ rd, MemL rd Lin → MeaningDaListDigest rd args rets) :
    CompleteAtDTB fs cert 16 "da_list_digest" Lin args (Returns rets) (fun _ => True)
      (SB "da_list_digest") :=
  (completeAt_of_rel_pureBat dl_pure (by simp [dlSet])
    (fun rd hm => da_list_digest_complete rd args rets (h rd hm)) 16
    fun rd t hn hv hb => hT rd t _ _ hn hv hb).toDTB

/-- **`__loop3` within its static bound**, from every counter below the count. -/
theorem rawX_completeAtB (hc : Sig.verify_lean_xmss_complete_Spec) {nrx X cv tb : ℕ} {Lin : Layout}
    (D : RawXData nrx X cv tb Lin) (hX : X ≤ 2 ^ 16) (hnrx : nrx < 2 ^ 34) {SK : String → ℕ}
    (hT : TotalLeOn coreProgram fs "__loop3" LoopPre (fun a => logG (a.getD 1 0) * SK "__loop3")) :
    ∀ i < nrx, CompleteAtDTB fs cert 16 "__loop3" Lin
      [gen ^ i, gen ^ nrx, gen ^ X, gen ^ cv, gen ^ tb] (Returns []) (fun _ => True)
      (nrx * SK "__loop3") := fun i hi =>
  completeAtDTB_of_relIn raw3_pure (by simp)
    (fun rd t rets' hn hv hb => by
      have := hT rd t _ rets' hn (loopPre_pow hi (by omega) _) hv hb
      simpa [logG_gen (show nrx < 2 ^ 64 - 1 by omega)] using this)
    fun rd hl hL => rawX_relIn hc D hX hnrx hl hL i hi

/-- **`__loop4` within its static bound**, from every counter below the count. -/
theorem rawS_completeAtB (hc : Sig.verify_sig_lean_sphincs_complete_loads_Spec)
    {nrs Y X nrx cv tb bb : ℕ} {Lin : Layout} (D : RawSData nrs Y X nrx cv tb bb Lin)
    (hY : Y ≤ 2 ^ 16) (hnrs : nrs < 2 ^ 34) {SK : String → ℕ}
    (hT : TotalLeOn coreProgram fs "__loop4" LoopPre (fun a => logG (a.getD 1 0) * SK "__loop4")) :
    ∀ j < nrs, CompleteAtDTB fs cert 16 "__loop4" Lin
      [gen ^ j, gen ^ nrs, gen ^ Y, gen ^ cv, gen ^ X, gen ^ nrx, gen ^ tb, gen ^ bb] (Returns [])
      (fun _ => True) (nrs * SK "__loop4") := fun j hj =>
  completeAtDTB_of_relIn raw4_pure (by simp)
    (fun rd t rets' hn hv hb => by
      have := hT rd t _ rets' hn (loopPre_pow hj (by omega) _) hv hb
      simpa [logG_gen (show nrs < 2 ^ 64 - 1 by omega)] using this)
    fun rd hl hL => rawS_relIn hc D hY hnrs hl hL j hj

end
end LeanVM.Guest.B1.Main
