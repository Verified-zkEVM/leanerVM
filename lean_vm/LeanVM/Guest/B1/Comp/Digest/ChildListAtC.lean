/-
  LeanVM.Guest.B1.Comp.Digest.ChildListAtC

  `child_claim_list_digest` complete over a completeness model in the uniform placed form
  (`CompleteRelBS`): the model version of `B1/Digest/ChildListAt.lean`'s `ccld_completeRelAtB`.
-/

module

public import LeanVM.Guest.B1.Digest.ChildListAt
public import LeanVM.Guest.B1.Comp.Digest.ChildList
public import LeanVM.Guest.B1.Comp.Digest.ClaimListAtC

/-!
# `child_claim_list_digest`, uniformly placed, over a completeness model

`ChildAt.lean`'s and `ChildListAt.lean`'s proofs under any semantics, the chains the model's:

* `cct_runB`, `ccw_runB`: the tail's and the window's honest runs on a memory defined below `2^16`
  from chained rows under `Sem` (`ChainSteps Sem`), their loads the child's reads;
  `cct_relB_low`, `ccw_relB_low` their relations;
* `cct_completeAtBS`, `ccw_completeAtBS`: placed under `Sem`;
* `l87_steps_lowC`, `l87_completeAtBS`: `__loop87`'s iterations over the model's states;
* `ccld_holds_zeroC`, `ccld_holds_posC`: the body at its honest values over the model;
* `ccld_completeRelBS` at `CclPreAtC CM.H` (the claims' digest the model's answer), and the
  deployed `ccld_completeRelAtB` at `CompModel.deployed` (`ccld_completeRelB_of_comp`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.Value LeanVM.E2E.Complete
open LeanVM.Protocol.Verifier (gen eOfNat)
open LeanVM.Guest.B1 (LowDef CompleteAtBS CompleteRelBS CompleteRelB kidsBound DisjL disj_nil disj_append
  Within Returns completeRelBS_deployed)
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-! ## `child_claims_tail__L{k}` -/

/-- **`child_claims_tail__L{k}`'s honest run under `Sem`** (`cct_run`), `k ≥ 1`, on a memory defined
below `2^16`, from chained rows. -/
theorem cct_runB {Sem : BlakeSem} {rd : Reader} (hl : Low16 rd) (k : ℕ) (hk1 : 1 ≤ k) (hk : k < 32)
    {s0 s1 base entries cover marks origin limit o0 o1 : E} {L : ℕ} (hL16 : L ≤ 2 ^ 16)
    (hlim : limit = gen ^ L) {off : ℕ → ℕ} {cs : List E}
    (hR : ChildReads rd entries cover marks origin limit off cs k)
    (hch : ChainSteps Sem (s0, s1) (blocksOf cs) (baseMd base) k (o0, o1)) :
    ∃ σ : Val, [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7].map σ =
        [s0, s1, base, entries, cover, marks, origin, limit] ∧
      (∀ a ∈ cctAtoms k, a.HoldsB Sem rd σ) ∧ [σ (.n (8 + 21 * k)), σ (.n (9 + 21 * k))] = [o0, o1] ∧
      ∀ A ∈ loadAddrs σ ((cctAtoms k).map Ev.atom), ChildLoad entries cover origin off k A := by
  obtain ⟨sts, hst, hout, hsteps⟩ := hch
  have hoff : ∀ j < k, off j < L := fun j hj => by
    obtain ⟨⟨L', hL', hlim', ho⟩, -⟩ := hR j hj
    have := gen_pow_inj (a := L) (b := L') (by omega) (by omega) (hlim.symm.trans hlim')
    omega
  have hw : ∀ j, ∃ t1 t2, j < k → LoadHolds rd (gen ^ off j) 0 t1 ∧
      LoadHolds rd (gen ^ (L - 1 - off j)) 0 t2 := fun j => by
    by_cases hj : j < k
    · obtain ⟨t1, t2, l1, -, l2⟩ := rangeCheck_complete_low hl (e := off j) (e' := L - 1 - off j)
        (by have := hoff j hj; omega) (by omega)
      exact ⟨t1, t2, fun _ => ⟨l1, l2⟩⟩
    · exact ⟨0, 0, fun h => absurd h hj⟩
  choose T1 T2 hT using hw
  set P := listVal [s0, s1, base, entries, cover, marks, origin, limit] with hP
  set S := sts with hS
  have hS0 : S 0 = (s0, s1) := hst
  obtain ⟨e8, e8k, e6⟩ := cctVals_end k P off L T1 T2 cs S
  obtain ⟨t8, t9⟩ := cctVals_st0 k P off L T1 T2 cs S
  have hH : Stmt.HoldsListB Sem (coreProgram.RelB Sem rd) rd (fun v => cctVals k P off L T1 T2 cs S v.idx)
      (cctBody k) False (fun rs => rs = [o0, o1]) := by
    simp only [cctBody, holdsListB_atoms, holdsListB_ret, List.forall_mem_append,
      forall_mem_flatMap_range, List.forall_mem_cons, Atom.HoldsB, forall_mem_nil_iff, and_true,
      List.map_cons, List.map_nil]
    refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, fun i hi => ?_⟩, ?_, ?_⟩, ?_⟩
    · show cctVals k P off L T1 T2 cs S 8 = cctVals k P off L T1 T2 cs S 0
      rw [t8, hS0]; rfl
    · show cctVals k P off L T1 T2 cs S 9 = cctVals k P off L T1 T2 cs S 1
      rw [t9, hS0]; rfl
    · obtain ⟨-, hs, hc⟩ := hR 0 hk1
      rw [pow_zero, mul_one] at hs
      have hcc := hsteps 0 hk1
      rw [blocksOf_getD] at hcc
      refine cBlk0B_bwd (o := 8) (out := S 1) (hoff 0 hk1) hlim (hT 0 hk1).1 (hT 0 hk1).2 hs hc ?_
        (fun r hr => cctVals_blk0 k P off L T1 T2 cs S r hr)
      show Sem.check _ (cctVals k P off L T1 T2 cs S 8) (cctVals k P off L T1 T2 cs S 9) _ _ _
      rw [t8, t9]
      exact hcc
    · obtain ⟨-, hs, hc⟩ := hR (i + 1) (by omega)
      have hcc := hsteps (i + 1) (by omega)
      rw [blocksOf_getD] at hcc
      have eb := cctVals_blk k P off L T1 T2 cs S (i + 1)
      refine cBlkB_bwd (o := 8) (out := S (i + 1 + 1)) (by omega) (hoff _ (by omega)) hlim
        (hT _ (by omega)).1 (hT _ (by omega)).2 hs hc ?_ (fun r hr => ?_) ?_ ?_ ?_ ?_
      · obtain ⟨o1', o2'⟩ := cctVals_out k P off L T1 T2 cs S (i + 1) (by omega) (by omega)
        show Sem.check _ (cctVals k P off L T1 T2 cs S (8 + 21 * (i + 1) - 2))
          (cctVals k P off L T1 T2 cs S (8 + 21 * (i + 1) - 1)) _ _ _
        rw [show 8 + 21 * (i + 1) - 2 = 6 + 21 * (i + 1) by omega,
          show 8 + 21 * (i + 1) - 1 = 7 + 21 * (i + 1) by omega, o1', o2']
        exact hcc
      · show cctVals k P off L T1 T2 cs S (8 + 21 * (i + 1) + r) = _
        rw [eb r (by omega) (by omega) (by omega), cBlkVals,
          List.getD_append _ _ _ _ (by simp [cHeadVals]; omega)]
        rfl
      · show cctVals k P off L T1 T2 cs S (8 + 21 * (i + 1) + 17) = _
        rw [eb 17 (by omega) (by omega) (by omega)]
        simp [cBlkVals, cHeadVals]
      · show cctVals k P off L T1 T2 cs S (8 + 21 * (i + 1) + 18) = _
        rw [eb 18 (by omega) (by omega) (by omega)]
        simp [cBlkVals, cHeadVals]
        rfl
      · show cctVals k P off L T1 T2 cs S (8 + 21 * (i + 1) + 19) = _
        rw [eb 19 (by omega) (by omega) (by omega)]
        simp [cBlkVals, cHeadVals]
      · show cctVals k P off L T1 T2 cs S (8 + 21 * (i + 1) + 20) = _
        rw [eb 20 (by omega) (by omega) (by omega)]
        simp [cBlkVals, cHeadVals]
    · show cctVals k P off L T1 T2 cs S (8 + 21 * k) = cctVals k P off L T1 T2 cs S (6 + 21 * k)
      rw [e8, (e6 hk1).1]
    · show cctVals k P off L T1 T2 cs S (9 + 21 * k) = cctVals k P off L T1 T2 cs S (7 + 21 * k)
      rw [e8k, (e6 hk1).2]
    · show [cctVals k P off L T1 T2 cs S (8 + 21 * k), cctVals k P off L T1 T2 cs S (9 + 21 * k)] = _
      rw [e8, e8k]
      show [(S k).1, (S k).2] = [o0, o1]
      rw [show S k = (o0, o1) from hout]
  rw [cctBody_eq, holdsListB_atoms, holdsListB_ret] at hH
  refine ⟨fun v => cctVals k P off L T1 T2 cs S v.idx, rfl, hH.1, hH.2, fun A hA => ?_⟩
  rw [loadAddrs_atoms] at hA
  simp only [cctAtoms, List.filterMap_append, List.filterMap_flatMap, cBlk0_loads, cBlk_loads, List.map_append,
    List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false,
    List.filterMap_cons, List.filterMap_nil, atomLoad?] at hA
  have h17 : cctVals k P off L T1 T2 cs S (8 + 9) = cover * (origin * gen ^ off 0) := by
    rw [show 8 + 9 = 8 + 2 + 7 from rfl, cctVals_blk0 k P off L T1 T2 cs S 7 (by omega)]; rfl
  have h20 : cctVals k P off L T1 T2 cs S (8 + 12) = entries * gen ^ (4 * off 0) := by
    rw [show 8 + 12 = 8 + 2 + 10 from rfl, cctVals_blk0 k P off L T1 T2 cs S 10 (by omega)]
    show P (.n 3) * (gen ^ off 0 * gen ^ off 0 * (gen ^ off 0 * gen ^ off 0)) = _
    rw [pow4_eq _ _ rfl]; rfl
  have hb9 : ∀ j, 1 ≤ j → j < k →
      cctVals k P off L T1 T2 cs S (8 + 21 * j + 9) = cover * (origin * gen ^ off j) := fun j h1 h2 => by
    rw [cctVals_blk k P off L T1 T2 cs S j 9 h1 h2 (by omega)]; rfl
  have hb12 : ∀ j, 1 ≤ j → j < k →
      cctVals k P off L T1 T2 cs S (8 + 21 * j + 12) = entries * gen ^ (4 * off j) := fun j h1 h2 => by
    rw [cctVals_blk k P off L T1 T2 cs S j 12 h1 h2 (by omega)]
    show P (.n 3) * (gen ^ off j * gen ^ off j * (gen ^ off j * gen ^ off j)) = _
    rw [pow4_eq _ _ rfl]; rfl
  rcases hA with ((⟨_, h, _⟩ | ⟨q, hq, rfl⟩) | ⟨q, ⟨i, hi, hq⟩, rfl⟩) | ⟨_, h, _⟩
  · exact h.elim
  · rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, hk1, by show (cctVals k P off L T1 T2 cs S (8 + 9)).limb 0 * _ = _; rw [h17]⟩
    all_goals refine Or.inr ⟨0, hk1, ?_⟩
    · exact ⟨0, by omega, by show (cctVals k P off L T1 T2 cs S (8 + 12)).limb 0 * _ = _; rw [h20]⟩
    · exact ⟨1, by omega, by show (cctVals k P off L T1 T2 cs S (8 + 12)).limb 0 * _ = _; rw [h20]⟩
    · exact ⟨2, by omega, by show (cctVals k P off L T1 T2 cs S (8 + 12)).limb 0 * _ = _; rw [h20]⟩
    · exact ⟨3, by omega, by show (cctVals k P off L T1 T2 cs S (8 + 12)).limb 0 * _ = _; rw [h20]⟩
  · rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨i + 1, by omega, by
        show (cctVals k P off L T1 T2 cs S (8 + 21 * (i + 1) + 9)).limb 0 * _ = _
        rw [hb9 _ (by omega) (by omega)]⟩
    all_goals refine Or.inr ⟨i + 1, by omega, ?_⟩
    all_goals have e12 := hb12 (i + 1) (by omega) (by omega)
    · exact ⟨0, by omega, by
        show (cctVals k P off L T1 T2 cs S (8 + 21 * (i + 1) + 12)).limb 0 * _ = _; rw [e12]⟩
    · exact ⟨1, by omega, by
        show (cctVals k P off L T1 T2 cs S (8 + 21 * (i + 1) + 12)).limb 0 * _ = _; rw [e12]⟩
    · exact ⟨2, by omega, by
        show (cctVals k P off L T1 T2 cs S (8 + 21 * (i + 1) + 12)).limb 0 * _ = _; rw [e12]⟩
    · exact ⟨3, by omega, by
        show (cctVals k P off L T1 T2 cs S (8 + 21 * (i + 1) + 12)).limb 0 * _ = _; rw [e12]⟩
  · exact h.elim

/-- **`child_claims_tail__L{k}` holds under `Sem`** (`cct_rel_low`), `k < 32`, on a memory defined
below `2^16`, from chained rows. -/
theorem cct_relB_low {Sem : BlakeSem} {rd : Reader} (hl : Low16 rd) (k : ℕ) (hk : k < 32)
    {s0 s1 base entries cover marks origin limit o0 o1 : E} {L : ℕ} (hL16 : L ≤ 2 ^ 16)
    (hlim : limit = gen ^ L) {off : ℕ → ℕ} {cs : List E}
    (hR : ChildReads rd entries cover marks origin limit off cs k)
    (hch : ChainSteps Sem (s0, s1) (blocksOf cs) (baseMd base) k (o0, o1)) :
    coreProgram.RelB Sem rd (cctNames.getD k "") [s0, s1, base, entries, cover, marks, origin, limit]
      [o0, o1] := by
  rw [relB_of_find (find_child_claims_tail k hk)]
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · obtain ⟨sts, h0, hn, -⟩ := hch
    exact child_tail_zero_compB rd _ _ _ ⟨_, _, _, _, _, _, _, _, _, _, rfl, rfl, off, [], rfl,
      fun j hj => absurd hj (by omega), sts, h0, hn, fun j hj => absurd hj (by omega)⟩
  · obtain ⟨σ, hp, hh, hr, -⟩ := cct_runB hl k hk1 hk hL16 hlim hR hch
    refine ⟨σ, hp, ?_⟩
    simp only [show ¬k = 0 by omega, ↓reduceIte]
    rw [cctBody_eq, holdsListB_atoms, holdsListB_ret]
    exact ⟨hh, hr⟩

/-- **`child_claims_tail__L{k}` is complete under `Sem`, uniformly placed** (`cct_completeAtB`). -/
theorem cct_completeAtBS {Sem : BlakeSem} (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ}
    (hκ : 16 ≤ κ) (k : ℕ) (hk : k < 32)
    (Lin : Layout) {s0 s1 base entries cover marks origin limit o0 o1 : E} {L : ℕ} (hL16 : L ≤ 2 ^ 16)
    (hlim : limit = gen ^ L) {off : ℕ → ℕ} {cs : List E}
    (hR : ∀ rd, LowDef κ rd → MemL rd Lin → ChildReads rd entries cover marks origin limit off cs k)
    (hreg : ∀ A, ChildLoad entries cover origin off k A → ∃ i, A = gpow i ∧ RegionL Lin i)
    (hch : ChainSteps Sem (s0, s1) (blocksOf cs) (baseMd base) k (o0, o1)) :
    CompleteAtBS Sem fs cert κ (cctNames.getD k "") Lin [s0, s1, base, entries, cover, marks, origin, limit]
      (Returns [o0, o1]) (fs (cctNames.getD k "")) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · have hout := chainSteps_zero hch
    simp only [Prod.mk.injEq] at hout
    refine LeanVM.Guest.B1.completeAtS_leafB (find_child_claims_tail 0 hk) (by decide +kernel) κ Lin _ _ []
      (fun _ => []) (fun _ => List.Forall₂.nil) fun fp rd _ _ _ => ?_
    refine ⟨listVal [s0, s1, base, entries, cover, marks, origin, limit, s0, s1, s0, s1], _, _, rfl,
      by show walk _ cctBody0 = _; exact walk_atoms _ _ _, by rw [hout.1, hout.2]; rfl, ?_, calls_atoms _,
      by rw [addrs_atoms]; rfl,
      allocs_atoms _ (by decide), by rw [allocDsts_atoms (by decide)]; rfl, ?_⟩
    · intro e he
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl <;> rfl
    · intro A hA
      rw [loadAddrs_atoms] at hA
      simp [atomLoad?] at hA
  · refine LeanVM.Guest.B1.completeAtS_leafB (find_child_claims_tail k hk) (by
      rw [Program.loop_of_find? (find_child_claims_tail k hk)]
      simp only [Fn.loop, show ¬k = 0 by omega, ↓reduceIte, cctBody_eq, List.reverse_append]
      rfl) κ Lin _ _ [] (fun _ => []) (fun _ => List.Forall₂.nil) fun fp rd hl _ hL => ?_
    obtain ⟨σ, hp, hh, hr, hld⟩ := cct_runB (fun i hi => hl i (lt_of_lt_of_le hi
      (Nat.pow_le_pow_right (by norm_num) hκ))) k hk1 hk hL16 hlim (hR rd hl hL) hch
    refine ⟨σ, _, [.n (8 + 21 * k), .n (9 + 21 * k)], hp,
      by simp only [show ¬k = 0 by omega, ↓reduceIte, cctBody_eq]; exact walk_atoms _ _ _, hr,
      fun e he => ?_, calls_atoms _, by rw [addrs_atoms, cctAtoms_noAddr], allocs_atoms _ (cctAtoms_noAlloc k),
      by rw [allocDsts_atoms (cctAtoms_noAlloc k)]; rfl, fun A hA => ?_⟩
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
      exact hh a ha
    · obtain ⟨i, hi, hRi⟩ := hreg A (hld A hA)
      exact ⟨i, hi, Or.inr hRi⟩

/-! ## `child_claims_window` -/

/-- **`child_claims_window`'s honest run under `Sem`** (`ccw_run`) on a memory defined below `2^16`,
from chained rows. -/
theorem ccw_runB {Sem : BlakeSem} {rd : Reader} (hl : Low16 rd) {gsq : E} (hT : SquaresAt rd gsq)
    {s0 s1 base entries cover marks origin limit xq o0 o1 nxt : E} {L : ℕ} (hL16 : L ≤ 2 ^ 16)
    (hlim : limit = gen ^ L) {N : ℕ} (hN : N < 2 ^ 16) (hxq : xq * gen = gen ^ N)
    (hnxt : nxt = eOfNat (2 ^ 11 * N))
    {off : ℕ → ℕ} {cs : List E} (hR : ChildReads rd entries cover marks origin limit off cs 32)
    (hch : ChainSteps Sem (s0, s1) (blocksOf cs) (windowMd base nxt) 32 (o0, o1)) :
    ∃ σ : Val, [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9].map σ =
        [s0, s1, base, entries, cover, marks, origin, limit, xq, gsq] ∧
      Stmt.HoldsListB Sem (coreProgram.RelB Sem rd) rd σ ccwBody False (fun rs => rs = [o0, o1, nxt]) ∧
      σ (.n 11) = xq * word 2 0 0 ∧ σ (.n 12) = nxt ∧
      [σ (.n 683), σ (.n 684), σ (.n 685)] = [o0, o1, nxt] ∧
      ∀ A ∈ loadAddrs σ (ccwPre.flatMap (Main.slEvs σ)), ChildLoad entries cover origin off 32 A := by
  obtain ⟨sts, hst, hout, hsteps⟩ := hch
  have hoff : ∀ j < 32, off j < L := fun j hj => by
    obtain ⟨⟨L', hL', hlim', ho⟩, -⟩ := hR j hj
    have := gen_pow_inj (a := L) (b := L') (by omega) (by omega) (hlim.symm.trans hlim')
    omega
  have hw : ∀ j, ∃ t1 t2, j < 32 → LoadHolds rd (gen ^ off j) 0 t1 ∧
      LoadHolds rd (gen ^ (L - 1 - off j)) 0 t2 := fun j => by
    by_cases hj : j < 32
    · obtain ⟨t1, t2, l1, -, l2⟩ := rangeCheck_complete_low hl (e := off j) (e' := L - 1 - off j)
        (lt_of_lt_of_le (hoff j hj) hL16) (by omega)
      exact ⟨t1, t2, fun _ => ⟨l1, l2⟩⟩
    · exact ⟨0, 0, fun h => absurd h hj⟩
  choose T1 T2 hT' using hw
  set P := listVal [s0, s1, base, entries, cover, marks, origin, limit, xq, gsq] with hP
  set S := sts with hS
  have hS0 : S 0 = (s0, s1) := hst
  obtain ⟨e681, e682, e683, e684, e685⟩ := ccwVals_end P off L T1 T2 cs S xq nxt
  have hH : Stmt.HoldsListB Sem (coreProgram.RelB Sem rd) rd (fun v => ccwVals P off L T1 T2 cs S xq nxt v.idx)
      ccwBody False (fun rs => rs = [o0, o1, nxt]) := by
    simp only [ccwBody, ccwLast, holdsListB_atoms, List.cons_append, List.nil_append,
      Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.forall_mem_append, forall_mem_flatMap_range,
      List.forall_mem_cons, forall_mem_nil_iff, and_true, List.map_cons, List.map_nil]
    refine ⟨rfl, rfl, ?_, ?_, ?_, ⟨⟨⟨?_, fun i hi => ?_⟩, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
    · exact (scaled_log_11_iffB hT _ _).mpr ⟨nxt, rfl, N, hN,
        by show xq * word 2 0 0 = gen ^ N; rw [word_gen]; exact hxq, hnxt⟩
    · show ccwVals P off L T1 T2 cs S xq nxt 13 = ccwVals P off L T1 T2 cs S xq nxt 0
      simp only [ccwVals]; simp [hS0, hP, listVal]
    · show ccwVals P off L T1 T2 cs S xq nxt 14 = ccwVals P off L T1 T2 cs S xq nxt 1
      simp only [ccwVals]; simp [hS0, hP, listVal]
    · obtain ⟨-, hs, hc⟩ := hR 0 (by omega)
      rw [pow_zero, mul_one] at hs
      have hcc := hsteps 0 (by omega)
      rw [blocksOf_getD] at hcc
      refine cBlk0B_bwd (o := 13) (out := S 1) (hoff 0 (by omega)) hlim (hT' 0 (by omega)).1
        (hT' 0 (by omega)).2 hs hc ?_ (fun r hr => ccwVals_blk0 P off L T1 T2 cs S xq nxt r hr)
      show Sem.check _ (ccwVals P off L T1 T2 cs S xq nxt 13) (ccwVals P off L T1 T2 cs S xq nxt 14) _ _ _
      have e13 : ccwVals P off L T1 T2 cs S xq nxt 13 = (S 0).1 := by simp [ccwVals]
      have e14 : ccwVals P off L T1 T2 cs S xq nxt 14 = (S 0).2 := by simp [ccwVals]
      rw [e13, e14]
      have : windowMd base nxt 0 = baseMd base 0 := by simp [windowMd]
      rw [this] at hcc
      exact hcc
    · obtain ⟨-, hs, hc⟩ := hR (i + 1) (by omega)
      have hcc := hsteps (i + 1) (by omega)
      rw [blocksOf_getD, show windowMd base nxt (i + 1) = baseMd base (i + 1) by
        simp [windowMd]; omega] at hcc
      have eb := ccwVals_blk P off L T1 T2 cs S xq nxt (i + 1)
      refine cBlkB_bwd (o := 13) (out := S (i + 1 + 1)) (by omega) (hoff _ (by omega)) hlim
        (hT' _ (by omega)).1 (hT' _ (by omega)).2 hs hc ?_ (fun r hr => ?_) ?_ ?_ ?_ ?_
      · obtain ⟨o1', o2'⟩ := ccwVals_out P off L T1 T2 cs S xq nxt (i + 1) (by omega) (by omega)
        show Sem.check _ (ccwVals P off L T1 T2 cs S xq nxt (13 + 21 * (i + 1) - 2))
          (ccwVals P off L T1 T2 cs S xq nxt (13 + 21 * (i + 1) - 1)) _ _ _
        rw [show 13 + 21 * (i + 1) - 2 = 11 + 21 * (i + 1) by omega,
          show 13 + 21 * (i + 1) - 1 = 12 + 21 * (i + 1) by omega, o1', o2']
        exact hcc
      · show ccwVals P off L T1 T2 cs S xq nxt (13 + 21 * (i + 1) + r) = _
        rw [eb r (by omega) (by omega) (by omega), cBlkVals,
          List.getD_append _ _ _ _ (by simp [cHeadVals]; omega)]
        rfl
      · show ccwVals P off L T1 T2 cs S xq nxt (13 + 21 * (i + 1) + 17) = _
        rw [eb 17 (by omega) (by omega) (by omega)]
        simp [cBlkVals, cHeadVals]
      · show ccwVals P off L T1 T2 cs S xq nxt (13 + 21 * (i + 1) + 18) = _
        rw [eb 18 (by omega) (by omega) (by omega)]
        simp [cBlkVals, cHeadVals]
        rfl
      · show ccwVals P off L T1 T2 cs S xq nxt (13 + 21 * (i + 1) + 19) = _
        rw [eb 19 (by omega) (by omega) (by omega)]
        simp [cBlkVals, cHeadVals]
      · show ccwVals P off L T1 T2 cs S xq nxt (13 + 21 * (i + 1) + 20) = _
        rw [eb 20 (by omega) (by omega) (by omega)]
        simp [cBlkVals, cHeadVals]
    · obtain ⟨-, hs, hc⟩ := hR 31 (by omega)
      exact cBlkHeadB_bwd (b := 664) (by omega) (hoff 31 (by omega)) hlim (hT' 31 (by omega)).1
        (hT' 31 (by omega)).2 hs hc (fun r hr => ccwVals_last P off L T1 T2 cs S xq nxt r hr)
    · have hcc := hsteps 31 (by omega)
      rw [blocksOf_getD, show windowMd base nxt 31 = nxt by simp [windowMd]] at hcc
      obtain ⟨o1', o2'⟩ := ccwVals_out P off L T1 T2 cs S xq nxt 31 (by omega) (by omega)
      have l0 := ccwVals_last P off L T1 T2 cs S xq nxt 13 (by omega)
      have l1 := ccwVals_last P off L T1 T2 cs S xq nxt 14 (by omega)
      have l2 := ccwVals_last P off L T1 T2 cs S xq nxt 15 (by omega)
      have l3 := ccwVals_last P off L T1 T2 cs S xq nxt 16 (by omega)
      simp only [cHeadVals, List.getD_cons_succ, List.getD_cons_zero] at l0 l1 l2 l3
      show Sem.check ![ccwVals P off L T1 T2 cs S xq nxt (664 + 13),
        ccwVals P off L T1 T2 cs S xq nxt (664 + 14), ccwVals P off L T1 T2 cs S xq nxt (664 + 15),
        ccwVals P off L T1 T2 cs S xq nxt (664 + 16)] (ccwVals P off L T1 T2 cs S xq nxt (11 + 21 * 31))
        (ccwVals P off L T1 T2 cs S xq nxt (12 + 21 * 31)) (ccwVals P off L T1 T2 cs S xq nxt 681)
        (ccwVals P off L T1 T2 cs S xq nxt 682) (ccwVals P off L T1 T2 cs S xq nxt 12)
      rw [l0, l1, l2, l3, o1', o2', e681, e682, show ccwVals P off L T1 T2 cs S xq nxt 12 = nxt by
        simp [ccwVals]]
      exact hcc
    · show ccwVals P off L T1 T2 cs S xq nxt 683 = ccwVals P off L T1 T2 cs S xq nxt 681
      rw [e683, e681]
    · show ccwVals P off L T1 T2 cs S xq nxt 684 = ccwVals P off L T1 T2 cs S xq nxt 682
      rw [e684, e682]
    · show ccwVals P off L T1 T2 cs S xq nxt 685 = ccwVals P off L T1 T2 cs S xq nxt 12
      rw [e685]; simp [ccwVals]
    · show [ccwVals P off L T1 T2 cs S xq nxt 683, ccwVals P off L T1 T2 cs S xq nxt 684,
        ccwVals P off L T1 T2 cs S xq nxt 685] = _
      rw [e683, e684, e685]
      show [(S 32).1, (S 32).2, nxt] = [o0, o1, nxt]
      rw [show S 32 = (o0, o1) from hout]
  refine ⟨fun v => ccwVals P off L T1 T2 cs S xq nxt v.idx, rfl, hH, rfl, rfl, ?_, fun A hA => ?_⟩
  · show [ccwVals P off L T1 T2 cs S xq nxt 683, ccwVals P off L T1 T2 cs S xq nxt 684,
      ccwVals P off L T1 T2 cs S xq nxt 685] = _
    rw [e683, e684, e685, show S 32 = (o0, o1) from hout]
  rw [loadAddrs_straight _ _ ccwPre_straight] at hA
  simp only [ccwPre, ccwRest, ccwLast, List.filterMap_append, stmtLoad_atoms, List.filterMap_flatMap, cBlk0_loads,
    cBlk_loads, cBlkHead_loads, List.map_append, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false, List.filterMap_cons, List.filterMap_nil, atomLoad?, stmtLoad?] at hA
  set V := ccwVals P off L T1 T2 cs S xq nxt with hV
  have h22 : V (13 + 9) = cover * (origin * gen ^ off 0) := by
    rw [hV, show 13 + 9 = 13 + 2 + 7 from rfl, ccwVals_blk0 P off L T1 T2 cs S xq nxt 7 (by omega)]; rfl
  have h25 : V (13 + 12) = entries * gen ^ (4 * off 0) := by
    rw [hV, show 13 + 12 = 13 + 2 + 10 from rfl, ccwVals_blk0 P off L T1 T2 cs S xq nxt 10 (by omega)]
    show P (.n 3) * (gen ^ off 0 * gen ^ off 0 * (gen ^ off 0 * gen ^ off 0)) = _
    rw [pow4_eq _ _ rfl]; rfl
  have hb9 : ∀ j, 1 ≤ j → j < 31 → V (13 + 21 * j + 9) = cover * (origin * gen ^ off j) := fun j h1 h2 => by
    rw [hV, ccwVals_blk P off L T1 T2 cs S xq nxt j 9 h1 h2 (by omega)]; rfl
  have hb12 : ∀ j, 1 ≤ j → j < 31 → V (13 + 21 * j + 12) = entries * gen ^ (4 * off j) := fun j h1 h2 => by
    rw [hV, ccwVals_blk P off L T1 T2 cs S xq nxt j 12 h1 h2 (by omega)]
    show P (.n 3) * (gen ^ off j * gen ^ off j * (gen ^ off j * gen ^ off j)) = _
    rw [pow4_eq _ _ rfl]; rfl
  have hl9 : V (664 + 9) = cover * (origin * gen ^ off 31) := by
    rw [hV, ccwVals_last P off L T1 T2 cs S xq nxt 9 (by omega)]; rfl
  have hl12 : V (664 + 12) = entries * gen ^ (4 * off 31) := by
    rw [hV, ccwVals_last P off L T1 T2 cs S xq nxt 12 (by omega)]
    show P (.n 3) * (gen ^ off 31 * gen ^ off 31 * (gen ^ off 31 * gen ^ off 31)) = _
    rw [pow4_eq _ _ rfl]; rfl
  rcases hA with (⟨_, h, _⟩ | ⟨_, h, _⟩) | ((((⟨_, h, _⟩ | ⟨q, hq, rfl⟩) | ⟨q, ⟨i, hi, hq⟩, rfl⟩) |
    (⟨q, hq, rfl⟩ | ⟨_, h, _⟩)) | ⟨_, h, _⟩)
  all_goals try exact h.elim
  · rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by show (V (13 + 9)).limb 0 * _ = _; rw [h22]⟩
    · exact Or.inr ⟨0, by omega, 0, by omega, by show (V (13 + 12)).limb 0 * _ = _; rw [h25]⟩
    · exact Or.inr ⟨0, by omega, 1, by omega, by show (V (13 + 12)).limb 0 * _ = _; rw [h25]⟩
    · exact Or.inr ⟨0, by omega, 2, by omega, by show (V (13 + 12)).limb 0 * _ = _; rw [h25]⟩
    · exact Or.inr ⟨0, by omega, 3, by omega, by show (V (13 + 12)).limb 0 * _ = _; rw [h25]⟩
  · have e9 := hb9 (i + 1) (by omega) (by omega)
    have e12 := hb12 (i + 1) (by omega) (by omega)
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨i + 1, by omega, by show (V (13 + 21 * (i + 1) + 9)).limb 0 * _ = _; rw [e9]⟩
    · exact Or.inr ⟨i + 1, by omega, 0, by omega, by
        show (V (13 + 21 * (i + 1) + 12)).limb 0 * _ = _; rw [e12]⟩
    · exact Or.inr ⟨i + 1, by omega, 1, by omega, by
        show (V (13 + 21 * (i + 1) + 12)).limb 0 * _ = _; rw [e12]⟩
    · exact Or.inr ⟨i + 1, by omega, 2, by omega, by
        show (V (13 + 21 * (i + 1) + 12)).limb 0 * _ = _; rw [e12]⟩
    · exact Or.inr ⟨i + 1, by omega, 3, by omega, by
        show (V (13 + 21 * (i + 1) + 12)).limb 0 * _ = _; rw [e12]⟩
  · rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨31, by omega, by show (V (664 + 9)).limb 0 * _ = _; rw [hl9]⟩
    · exact Or.inr ⟨31, by omega, 0, by omega, by show (V (664 + 12)).limb 0 * _ = _; rw [hl12]⟩
    · exact Or.inr ⟨31, by omega, 1, by omega, by show (V (664 + 12)).limb 0 * _ = _; rw [hl12]⟩
    · exact Or.inr ⟨31, by omega, 2, by omega, by show (V (664 + 12)).limb 0 * _ = _; rw [hl12]⟩
    · exact Or.inr ⟨31, by omega, 3, by omega, by show (V (664 + 12)).limb 0 * _ = _; rw [hl12]⟩

/-- **`child_claims_window` holds under `Sem`** on a memory defined below `2^16`, from chained rows. -/
theorem ccw_relB_low {Sem : BlakeSem} {rd : Reader} (hl : Low16 rd) {gsq : E} (hT : SquaresAt rd gsq)
    {s0 s1 base entries cover marks origin limit xq o0 o1 nxt : E} {L : ℕ} (hL16 : L ≤ 2 ^ 16)
    (hlim : limit = gen ^ L) {N : ℕ} (hN : N < 2 ^ 16) (hxq : xq * gen = gen ^ N)
    (hnxt : nxt = eOfNat (2 ^ 11 * N))
    {off : ℕ → ℕ} {cs : List E} (hR : ChildReads rd entries cover marks origin limit off cs 32)
    (hch : ChainSteps Sem (s0, s1) (blocksOf cs) (windowMd base nxt) 32 (o0, o1)) :
    coreProgram.RelB Sem rd "child_claims_window" [s0, s1, base, entries, cover, marks, origin, limit, xq, gsq]
      [o0, o1, nxt] := by
  obtain ⟨σ, hp, hH, -, -, -, -⟩ := ccw_runB hl hT hL16 hlim hN hxq hnxt hR hch
  exact (relB_of_find find_child_claims_window _ _).mpr ⟨σ, hp, hH⟩

/-- **`child_claims_window` is complete under `Sem`, uniformly placed** (`ccw_completeAtB`). -/
theorem ccw_completeAtBS {Sem : BlakeSem} (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ}
    (hκ : 16 ≤ κ) (Lin : Layout)
    {gsq s0 s1 base entries cover marks origin limit xq o0 o1 nxt : E} {L : ℕ} (hL16 : L ≤ 2 ^ 16)
    (hlim : limit = gen ^ L) {N : ℕ} (hN : N < 2 ^ 16) (hxq : xq * gen = gen ^ N)
    (hnxt : nxt = eOfNat (2 ^ 11 * N))
    {off : ℕ → ℕ} {cs : List E}
    (hR : ∀ rd, LowDef κ rd → MemL rd Lin → ChildReads rd entries cover marks origin limit off cs 32)
    (hsq : ∀ rd, MemL rd Lin → SquaresAt rd gsq)
    (hreg : ∀ A, ChildLoad entries cover origin off 32 A → ∃ i, A = gpow i ∧ RegionL Lin i)
    (hch : ChainSteps Sem (s0, s1) (blocksOf cs) (windowMd base nxt) 32 (o0, o1)) (Bsl : ℕ)
    (hsl : TotalLeB Sem coreProgram fs "scaled_log__L11" fun _ => Bsl) :
    CompleteAtBS Sem fs cert κ "child_claims_window" Lin
      [s0, s1, base, entries, cover, marks, origin, limit, xq, gsq]
      (Returns [o0, o1, nxt]) (fs "child_claims_window" + Bsl) := by
  refine completeAtS_nodeB find_child_claims_window (by
      rw [Program.loop_of_find? find_child_claims_window]
      simp only [Fn.loop, ccwBody_eq, List.reverse_append]
      rfl) κ Lin _ _ [] (fun _ => []) (fun _ _ h => by obtain ⟨q, hq, _⟩ := h; simp at hq)
    (fun _ q hq => by simp at hq) (fun _ => disj_nil)
    (fun _ => [⟨"scaled_log__L11", true, [xq * word 2 0 0, gsq], Lin, [nxt]⟩]) (fun _ => Bsl)
    (fun _ k hk _ => by
      simp only [List.mem_singleton] at hk
      subst hk
      exact LeanVM.Guest.B1.completeAtS_of_rel_pureB cldKid_pure (by simp [cldKidSet])
        (fun rd hL => (scaled_log_11_iffB (hsq rd hL) _ _).mpr
          ⟨nxt, rfl, N, hN, by rw [word_gen]; exact hxq, hnxt⟩) κ hsl)
    (fun _ k hk _ i hi => by
      simp only [List.mem_singleton] at hk
      subst hk
      exact Or.inr hi) _ (fun _ => by simp [kidsBound, KidR.kid]) fun fp rd hl _ hL => ?_
  refine ⟨fun k hk => by simp only [List.mem_singleton] at hk; subst hk; exact hL, ?_⟩
  obtain ⟨σ, hp, hH, h11, h12, hr, hld⟩ := ccw_runB (fun i hi => hl i (lt_of_lt_of_le hi
    (Nat.pow_le_pow_right (by norm_num) hκ))) (hsq rd hL) hL16 hlim hN hxq hnxt (hR rd hl hL) hch
  have hw : walk σ ccwBody = .ret (ccwPre.flatMap (Main.slEvs σ)) [.n 683, .n 684, .n 685] := by
    rw [ccwBody_eq]; exact Main.walk_straight σ _ _ ccwPre_straight
  obtain ⟨e1, e2, e3, e4⟩ := Main.straight_parts σ _ ccwPre_straight
  have h9 : σ (.n 9) = gsq := by
    simp only [List.map_cons, List.map_nil, List.cons.injEq] at hp; exact hp.2.2.2.2.2.2.2.2.2.1
  refine ⟨σ, _, _, hp, hw, hr, holdsB_of_holdsList find_child_claims_window hH hw, ?_, ?_, ?_, ?_,
    fun A hA => ?_⟩
  · rw [e4, show ccwPre.filterMap Main.Stmt.callS = [(none, "scaled_log__L11", [.n 11, .n 9], [.n 12])] by
      decide +kernel]
    exact ⟨rfl, rfl, fun _ => ⟨show [σ (.n 11), σ (.n 9)] = _ by rw [h11, h9],
      show [σ (.n 12)] = _ by rw [h12]⟩, trivial⟩
  · rw [e3]; decide +kernel
  · rw [e2, show ccwPre.filterMap Main.Stmt.allocSz = [] by decide +kernel]; rfl
  · rw [e1, show ccwPre.filterMap Main.Stmt.allocSz = [] by decide +kernel]; rfl
  · obtain ⟨i, hi, hRi⟩ := hreg A (hld A hA)
    exact ⟨i, hi, Or.inr hRi⟩

/-! ## `__loop87` over the model -/

/-- The windows' scratch slot `q` of a child's list over the model (`cclSlot`). -/
def cclSlotC (CM : CompModel) (cs : List E) (q : ℕ) : List E :=
  [(CM.st (prefixAt (cs.flatMap cellBytes) (32 * q))).1,
    (CM.st (prefixAt (cs.flatMap cellBytes) (32 * q))).2, eOfNat (2 ^ 11 * q)]

/-- `__loop87`'s body holds under any semantics (`l87_holds`). -/
theorem l87_holdsB {Sem : BlakeSem} {rd : Reader} {C : CallRel}
    {x W c base entries cover origin limit gsq s0 s1 bs o0 o1 nxt : E}
    (hs : CellsAt rd (c * (x * x * (x * x))) [s0, s1, bs])
    (hcall : C "child_claims_window" [s0, s1, bs, entries, cover, base * pow32 x, origin, limit, x, gsq]
      [o0, o1, nxt])
    (ho : CellsAt rd (c * (x * gen * (x * gen) * (x * gen * (x * gen)))) [o0, o1, nxt])
    (hk : IsInK (x * gen + W))
    (hnext : x * gen + W ≠ 0 → C "__loop87" (x * gen :: [W, c, base, entries, cover, origin, limit, gsq]) []) :
    Stmt.HoldsListB Sem C rd
      (listVal (l87List x W c base entries cover origin limit gsq s0 s1 bs o0 o1 nxt)) l87Body
      False (fun rs => rs = []) := by
  rw [cellsAt_three] at hs ho
  obtain ⟨l18, l19, l20⟩ := hs
  obtain ⟨l21, l22, l23⟩ := ho
  simp only [l87Body, List.cons_append, List.nil_append, Stmt.HoldsListB,
    Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil]
  simp only [l87List, listVal, List.getD_cons_succ, List.getD_cons_zero, true_and]
  rw [← word_gen] at l21 l22 l23 hk hnext
  exact ⟨rfl, l18, l19, l20, hcall, l21, l22, l23, hk, hnext, trivial⟩

/-- **The windows hold over the model** (`l87_steps_low`), on a memory defined below `2^16` holding
the squares table, the reads and the scratch table of the model's states. -/
theorem l87_steps_lowC {CM : CompModel} {rd : Reader} (hl : Low16 rd) {gsq : E} (hT : SquaresAt rd gsq)
    {c base entries cover origin : E} {L n w : ℕ} (hL16 : L ≤ 2 ^ 16) (hn : n < 2 ^ 16) (hw : 32 * w < n)
    {off : ℕ → ℕ} {cs : List E} (hlen : cs.length = 4 * n)
    (hR : ChildReads rd entries cover base origin (gen ^ L) off cs n)
    (hcan : ∀ x ∈ cs, IsCanonical128 x) {d : Digest} (hH : CM.H (cs.flatMap cellBytes) = some d)
    (hscr : ChildScratchC CM rd c cs w) :
    ∀ j < w, L87Step rd c base entries cover origin (gen ^ L) gsq (coreProgram.RelB CM.sem rd) (gen ^ j) := by
  intro j hj
  have h0 := cellsAt_three.mp (hscr j (by omega))
  have h1 := hscr (j + 1) (by omega)
  rw [show 32 * (j + 1) = 32 * j + 32 by ring] at h1
  refine ⟨_, _, _, (CM.st (prefixAt (cs.flatMap cellBytes) (32 * j + 32))).1,
    (CM.st (prefixAt (cs.flatMap cellBytes) (32 * j + 32))).2, eOfNat (2 ^ 11 * (j + 1)),
    by rw [pow4_eq _ j rfl]; exact cellsAt_three.mpr h0, ?_,
    by rw [← pow_succ, pow4_eq _ (j + 1) rfl]; exact h1⟩
  rw [pow32_eq]
  exact ccw_relB_low hl hT hL16 rfl (N := j + 1) (by omega) (pow_succ gen j).symm rfl
    (childReads_slice hR (32 * j) 32 (by omega))
    (chainSteps_cells CM hlen hH hcan (k := 32 * j) (m := 32) (by omega)
      (blocksOf_sliceOf cs (32 * j) 32) (fun i hi => windowMd_eq j i hi))

/-- **One iteration of `__loop87` over the model, complete, placed** (`l87_iterB`), from the next
one's. -/
theorem l87_iterBS {CM : CompModel} (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 16 ≤ κ)
    (KL : Layout)
    {gsq base entries cover origin : E} {cx L n w : ℕ} (hL16 : L ≤ 2 ^ 16) (hn : n < 2 ^ 16)
    (hw : 32 * w < n)
    {off : ℕ → ℕ} {cs : List E} (hlen : cs.length = 4 * n) (hcan : ∀ x ∈ cs, IsCanonical128 x)
    {d : Digest} (hH : CM.H (cs.flatMap cellBytes) = some d)
    (hR : ∀ rd, LowDef κ rd → MemL rd KL → ChildReads rd entries cover base origin (gen ^ L) off cs n)
    (hsq : ∀ rd, MemL rd KL → SquaresAt rd gsq)
    (hscr : ∀ rd, MemL rd KL → ChildScratchC CM rd (gen ^ cx) cs w)
    (hreg : ∀ A, ChildLoad entries cover origin off n A → ∃ i, A = gpow i ∧ RegionL KL i)
    (hsR : ∀ q ≤ w, ∀ r < 3, RegionL KL (cx + 4 * q + r)) (Bsl : ℕ)
    (hsl : TotalLeB CM.sem coreProgram fs "scaled_log__L11" fun _ => Bsl) {j : ℕ} (hj : j < w)
    (hnext : j + 1 < w → CompleteAtBS CM.sem fs cert κ "__loop87" KL
      [gen ^ (j + 1), gen ^ w, gen ^ cx, base, entries, cover, origin, gen ^ L, gsq] (Returns [])
      (l87Bound fs (fs "child_claims_window" + Bsl) w (j + 1))) :
    CompleteAtBS CM.sem fs cert κ "__loop87" KL
      [gen ^ j, gen ^ w, gen ^ cx, base, entries, cover, origin, gen ^ L, gsq] (Returns [])
      (l87Bound fs (fs "child_claims_window" + Bsl) w j) := by
  have hlow : ∀ rd, LowDef κ rd → Low16 rd := fun rd hl i hi =>
    hl i (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hκ))
  have hch : ChainSteps CM.sem (CM.st (prefixAt (cs.flatMap cellBytes) (32 * j)))
      (blocksOf (sliceOf cs (32 * j) 32)) (windowMd (eOfNat (2 ^ 11 * j)) (eOfNat (2 ^ 11 * (j + 1)))) 32
      (CM.st (prefixAt (cs.flatMap cellBytes) (32 * j + 32))) :=
    chainSteps_cells CM hlen hH hcan (k := 32 * j) (m := 32) (by omega)
      (blocksOf_sliceOf cs (32 * j) 32) (fun i hi => windowMd_eq j i hi)
  have hRj : ∀ rd, LowDef κ rd → MemL rd KL → ChildReads rd entries cover (base * pow32 (gen ^ j)) origin
      (gen ^ L) (fun k => off (32 * j + k)) (sliceOf cs (32 * j) 32) 32 := fun rd hl hL => by
    rw [pow32_eq]; exact childReads_slice (hR rd hl hL) (32 * j) 32 (by omega)
  refine completeAtS_loopB find_loop87 (by rw [Program.loop_of_find? find_loop87]; decide +kernel) κ KL _ []
    [⟨"child_claims_window", true,
      cclSlotC CM cs j ++ [entries, cover, base * pow32 (gen ^ j), origin, gen ^ L, gen ^ j, gsq],
      KL, [(CM.st (prefixAt (cs.flatMap cellBytes) (32 * j + 32))).1,
        (CM.st (prefixAt (cs.flatMap cellBytes) (32 * j + 32))).2, eOfNat (2 ^ 11 * (j + 1))]⟩]
    ⟨"__loop87", decide (gen ^ j * word 2 0 0 + gen ^ w ≠ 0),
      [gen ^ (j + 1), gen ^ w, gen ^ cx, base, entries, cover, origin, gen ^ L, gsq], KL, []⟩
    (fun _ => fs "child_claims_window" + Bsl) (l87Bound fs (fs "child_claims_window" + Bsl) w (j + 1)) ?_ ?_
    (l87Bound fs (fs "child_claims_window" + Bsl) w j)
    (by simpa [kidsBound, KidR.kid] using l87Bound_step fs (fs "child_claims_window" + Bsl) w j hj) ?_ ?_
  · intro k hk _
    simp only [List.mem_singleton] at hk
    subst hk
    exact ccw_completeAtBS fs cert hκ KL hL16 rfl (N := j + 1) (by omega) (pow_succ gen j).symm rfl hRj hsq
      (fun A hA => hreg A (childLoad_shift (by omega) hA)) hch Bsl hsl
  · intro ht
    refine hnext ?_
    have : gen ^ j * word 2 0 0 + gen ^ w ≠ 0 := by simpa using ht
    rw [word_gen, ← pow_succ] at this
    by_contra h
    exact this (by rw [show w = j + 1 by omega]; exact e_add_self _)
  · intro k _ _ i hi
    simp only [List.mem_append, List.mem_singleton] at *
    rcases ‹_ ∨ _› with rfl | rfl <;> exact hi
  intro rd hl hL
  refine ⟨fun k hk => by
    simp only [List.mem_append, List.mem_singleton] at hk; rcases hk with rfl | rfl <;> exact hL, ?_⟩
  have hT := hsq rd hL
  have hs := hscr rd hL j (by omega)
  have ho := hscr rd hL (j + 1) (by omega)
  have hcall := ccw_relB_low (hlow rd hl) hT hL16 rfl (N := j + 1) (by omega) (pow_succ gen j).symm rfl
    (hRj rd hl hL) hch
  have hsteps := l87_steps_lowC (hlow rd hl) hT hL16 hn hw hlen (hR rd hl hL) hcan hH (hscr rd hL)
  have hk : IsInK (gen ^ j * gen + gen ^ w) := by
    rw [← pow_succ, gen_pow_eq_ofK, gen_pow_eq_ofK, ← ofK_add]; exact ofK_isInK _
  have hnx : gen ^ j * gen + gen ^ w ≠ 0 → coreProgram.RelB CM.sem rd "__loop87"
      (gen ^ j * gen :: [gen ^ w, gen ^ cx, base, entries, cover, origin, gen ^ L, gsq]) [] := fun h => by
    rw [← pow_succ] at h ⊢
    have hjw : j + 1 < w := by
      by_contra h'
      exact h (by rw [show w = j + 1 by omega]; exact e_add_self _)
    exact loopB_bwd (B := L87Step rd (gen ^ cx) base entries cover origin (gen ^ L) gsq
        (coreProgram.RelB CM.sem rd))
      (fun x hB hK hnext => l87_step_bwdB rd (gen ^ w) (gen ^ cx) base entries cover origin (gen ^ L) gsq x
        hB hK hnext) hjw rfl (fun i _ h2 => hsteps i h2)
  have hh := l87_holdsB (Sem := CM.sem) (C := coreProgram.RelB CM.sem rd) (W := gen ^ w)
    (by rw [pow4_eq _ j rfl]; exact hs) hcall (by rw [← pow_succ, pow4_eq _ (j + 1) rfl]; exact ho) hk hnx
  set σ := listVal (l87List (gen ^ j) (gen ^ w) (gen ^ cx) base entries cover origin (gen ^ L) gsq
    (CM.st (prefixAt (cs.flatMap cellBytes) (32 * j))).1 (CM.st (prefixAt (cs.flatMap cellBytes) (32 * j))).2
    (eOfNat (2 ^ 11 * j))
    (CM.st (prefixAt (cs.flatMap cellBytes) (32 * j + 32))).1
    (CM.st (prefixAt (cs.flatMap cellBytes) (32 * j + 32))).2
    (eOfNat (2 ^ 11 * (j + 1)))) with hσ
  have hwk : walk σ l87Body = .ret (l87S.flatMap (Main.slEvs σ)) [] := by
    rw [l87Body_eq]; exact Main.walk_straight σ _ _ l87S_straight
  obtain ⟨e1, e2, e3, e4, e5⟩ := l87_events σ
  refine ⟨σ, _, [], rfl, hwk, rfl, holdsB_of_holdsList find_loop87 hh hwk, ?_, e2, e3, e4, fun A hA => ?_⟩
  · rw [e1]
    refine ⟨rfl, rfl, fun _ => ⟨rfl, rfl⟩, rfl, rfl, fun _ => ⟨?_, rfl⟩, trivial⟩
    show [gen ^ j * word 2 0 0, _, _, _, _, _, _, _, _] = _
    rw [word_gen, ← pow_succ]
    rfl
  · rw [e5] at hA
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
    have g11 : σ (.n 11) = gen ^ (cx + 4 * j) := by
      show gen ^ cx * (gen ^ j * gen ^ j * (gen ^ j * gen ^ j)) = _
      rw [pow4_eq _ j rfl, ← pow_add]
    have g28 : σ (.n 28) = gen ^ (cx + 4 * (j + 1)) := by
      show gen ^ cx * (gen ^ j * word 2 0 0 * (gen ^ j * word 2 0 0) *
        (gen ^ j * word 2 0 0 * (gen ^ j * word 2 0 0))) = _
      rw [word_gen, ← pow_succ, pow4_eq _ (j + 1) rfl, ← pow_add]
    rcases hA with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by rw [g11, limb0_gen_pow, gpow_add'], hsR j (by omega) 0 (by omega)⟩
    · exact ⟨_, by rw [g11, limb0_gen_pow, gpow_add'], hsR j (by omega) 1 (by omega)⟩
    · exact ⟨_, by rw [g11, limb0_gen_pow, gpow_add'], hsR j (by omega) 2 (by omega)⟩
    · exact ⟨_, by rw [g28, limb0_gen_pow, gpow_add'], hsR (j + 1) (by omega) 0 (by omega)⟩
    · exact ⟨_, by rw [g28, limb0_gen_pow, gpow_add'], hsR (j + 1) (by omega) 1 (by omega)⟩
    · exact ⟨_, by rw [g28, limb0_gen_pow, gpow_add'], hsR (j + 1) (by omega) 2 (by omega)⟩

/-- **`__loop87`'s iterations over the model are complete, uniformly placed** (`l87_completeAtB`). -/
theorem l87_completeAtBS {CM : CompModel} (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ}
    (hκ : 16 ≤ κ) (KL : Layout)
    {gsq base entries cover origin : E} {cx L n w : ℕ} (hL16 : L ≤ 2 ^ 16) (hn : n < 2 ^ 16)
    (hw : 32 * w < n)
    {off : ℕ → ℕ} {cs : List E} (hlen : cs.length = 4 * n) (hcan : ∀ x ∈ cs, IsCanonical128 x)
    {d : Digest} (hH : CM.H (cs.flatMap cellBytes) = some d)
    (hR : ∀ rd, LowDef κ rd → MemL rd KL → ChildReads rd entries cover base origin (gen ^ L) off cs n)
    (hsq : ∀ rd, MemL rd KL → SquaresAt rd gsq)
    (hscr : ∀ rd, MemL rd KL → ChildScratchC CM rd (gen ^ cx) cs w)
    (hreg : ∀ A, ChildLoad entries cover origin off n A → ∃ i, A = gpow i ∧ RegionL KL i)
    (hsR : ∀ q ≤ w, ∀ r < 3, RegionL KL (cx + 4 * q + r)) (Bsl : ℕ)
    (hsl : TotalLeB CM.sem coreProgram fs "scaled_log__L11" fun _ => Bsl) :
    ∀ j < w, CompleteAtBS CM.sem fs cert κ "__loop87" KL
      [gen ^ j, gen ^ w, gen ^ cx, base, entries, cover, origin, gen ^ L, gsq] (Returns [])
      (l87Bound fs (fs "child_claims_window" + Bsl) w j) := by
  suffices H : ∀ d j, j + d + 1 = w → CompleteAtBS CM.sem fs cert κ "__loop87" KL
      [gen ^ j, gen ^ w, gen ^ cx, base, entries, cover, origin, gen ^ L, gsq] (Returns [])
      (l87Bound fs (fs "child_claims_window" + Bsl) w j) from
    fun j hj => H (w - j - 1) j (by omega)
  intro e
  induction e with
  | zero =>
    exact fun j hj => l87_iterBS fs cert hκ KL hL16 hn hw hlen hcan hH hR hsq hscr hreg hsR Bsl hsl
      (j := j) (by omega) (fun h => absurd h (by omega))
  | succ e ih =>
    exact fun j hj => l87_iterBS fs cert hκ KL hL16 hn hw hlen hcan hH hR hsq hscr hreg hsR Bsl hsl
      (j := j) (by omega) (fun _ => ih (j + 1) (by omega))

/-! ## `child_claim_list_digest`'s body over the model -/

/-- **`child_claim_list_digest`'s body holds over a completeness model**, `n = 0`: the empty
string's row (`ccld_holds_zero`). -/
theorem ccld_holds_zeroC {CM : CompModel} (rd : Reader) (entries cover base origin limit gsq : E)
    {d0 d1 : E} {d : Digest} (hH : CM.H (([] : List E).flatMap cellBytes) = some d)
    (hd : (d0, d1) = digestScalars d) :
    Stmt.HoldsListB CM.sem (coreProgram.RelB CM.sem rd) rd
      (listVal (ccldZeroList entries cover base origin limit gsq d0 d1)) ccldBody False
      (fun rs => rs = [d0, d1]) := by
  simp only [ccldBody, List.cons_append, List.nil_append, Stmt.HoldsListB,
    Stmt.HoldsB, Atom.HoldsB, true_and, List.map_cons, List.map_nil]
  have h11 : (1 : E) + word 1 0 0 = 0 := by rw [word_one, e_add_self]
  refine ⟨rfl, rfl, ?_, fun _ => ?_, fun h => ?_⟩
  · show IsInK ((1 : E) + word 1 0 0)
    rw [h11, ← ofK_zero]; exact ofK_isInK _
  · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl⟩
    show CM.sem.check ![word 0 0 0, word 0 0 0, word 0 0 0, word 0 0 0]
      (word 13503953895743350343 11912009169889063794 0)
      (word 11170449402626986623 6620516960021240235 0) d0 d1 (word 0 4294967295 0)
    rw [word_zero, iv0_word, iv1_word, md_final_word, show d0 = (d0, d1).1 from rfl,
      show d1 = (d0, d1).2 from rfl, hd]
    exact CM.check_empty hH
  · exfalso; apply h; show (1 : E) + word 1 0 0 = 0; exact h11

/-- **`child_claim_list_digest`'s body holds over a completeness model** (`ccld_holds_pos`),
`n ≥ 1`, at its honest values, on a memory defined below `2^16` holding the squares table, the
reads and the windows' scratch table of the model's states at `c`, when the model answers the
claims' bytes. -/
theorem ccld_holds_posC {CM : CompModel} {rd : Reader} (hl : Low16 rd) {gsq : E} (hT : SquaresAt rd gsq)
    {entries cover base origin c : E} {L n : ℕ} (hL16 : L ≤ 2 ^ 16) (hn : n < 2 ^ 16) (hn1 : 0 < n)
    {off : ℕ → ℕ} {cs : List E} (hlen : cs.length = 4 * n)
    (hR : ChildReads rd entries cover base origin (gen ^ L) off cs n) (hcan : ∀ x ∈ cs, IsCanonical128 x)
    (hscr : ChildScratchC CM rd c cs ((n - 1) / 32)) {d0 d1 : E} {d : Digest}
    (hH : CM.H (cs.flatMap cellBytes) = some d) (hd : (d0, d1) = digestScalars d) :
    ∃ t1 t2 t3 t4 t5 t6, Stmt.HoldsListB CM.sem (coreProgram.RelB CM.sem rd) rd
      (listVal (cclListS entries cover base origin (gen ^ L) gsq c d0 d1 cs (off (n - 1)) L n
        ((n - 1) / 32) ((n - 1) % 32) t1 t2 t3 t4 t5 t6
        (CM.st (prefixAt (cs.flatMap cellBytes) (32 * ((n - 1) / 32))))
        (CM.st (prefixAt (cs.flatMap cellBytes) (n - 1))))) ccldBody False (fun rs => rs = [d0, d1]) := by
  set w := (n - 1) / 32 with hw
  set t := (n - 1) % 32 with ht
  have hwt : n = 32 * w + t + 1 := by omega
  have ht32 : t < 32 := by omega
  have hw2 : w < 2048 := by omega
  have hoff : ∀ j < n, off j < L := fun j hj => by
    obtain ⟨⟨L', hL', hlim', ho⟩, -⟩ := hR j hj
    have := gen_pow_inj (a := L) (b := L') (by omega) (by omega) hlim'
    omega
  obtain ⟨t1, t2, l22, -, l23⟩ := rangeCheck_complete_low hl (e := t) (e' := 31 - t) (by omega) (by omega)
  obtain ⟨t3, t4, l26, -, l27⟩ := rangeCheck_complete_low hl (e := w) (e' := 2047 - w) (by omega) (by omega)
  obtain ⟨t5, t6, l65, -, l66⟩ := rangeCheck_complete_low hl (e := off (n - 1)) (e' := L - 1 - off (n - 1))
    (lt_of_lt_of_le (hoff _ (by omega)) hL16) (by omega)
  have hS := fun q (hq : q ≤ w) => cellsAt_three.mp (hscr q hq)
  obtain ⟨s00, s01, s02⟩ := hS 0 (by omega)
  obtain ⟨sw0, sw1, sw2⟩ := hS w le_rfl
  simp only [Nat.mul_zero, pow_zero, mul_one, eOfNat_zero, prefixAt_zero, CM.st_nil] at s00 s01 s02
  rw [← pow4_eq _ w rfl] at sw0 sw1 sw2
  have hb := blocks_canonical hlen hcan
  have hsteps := l87_steps_lowC hl hT hL16 hn (w := w) (by omega) hlen hR hcan hH hscr
  have hlast : ![cs.getD (4 * (n - 1) + 0) 0, cs.getD (4 * (n - 1) + 1) 0,
      cs.getD (4 * (n - 1) + 2) 0, cs.getD (4 * (n - 1) + 3) 0] = blocksOf cs (n - 1) := by
    simp [blocksOf]
  have hmd : eOfNat (2 ^ 6 * n) + word 0 4294967295 0 = metadataCell (64 * n) true := by
    rw [md_final_word, eOfNat_add_metadataCell, Nat.xor_zero]; rfl
  have hinv : gen ^ n * wInv = gen ^ (n - 1) := by
    rw [show gen ^ n = gen ^ (n - 1) * gen by rw [← pow_succ]; congr 1; omega, mul_assoc, mul_comm gen,
      ginv_mul_gen, mul_one]
  obtain ⟨-, hmark, hcl⟩ := hR (n - 1) (by omega)
  refine ⟨t1, t2, t3, t4, t5, t6, ?_⟩
  simp only [ccldBody, List.cons_append, List.nil_append, Stmt.HoldsListB,
    Stmt.HoldsB, Atom.HoldsB, true_and, List.map_cons, List.map_nil]
  refine ⟨rfl, rfl, ?_, fun h => ?_, fun _ => ?_⟩
  · show IsInK (gen ^ n + word 1 0 0)
    rw [word_one, gen_pow_eq_ofK, ← ofK_one, ← ofK_add]; exact ofK_isInK _
  · exfalso
    have h' : gen ^ n + word 1 0 0 = 0 := h
    rw [word_one] at h'
    have := (gen_pow_eq_one_iff (by omega)).mp (e_add_eq_zero_iff.mp h')
    omega
  refine ⟨rfl, ⟨l22, ?_, l23⟩, rfl, ⟨l26, ?_, l27⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_,
    rfl, rfl, rfl, rfl, rfl, ?_, rfl, ?_, rfl, ?_, rfl, rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, rfl, rfl, ⟨l65, ?_, l66⟩, rfl, rfl, rfl, rfl, rfl, ?_, rfl,
    rfl, rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_⟩
  all_goals simp only [listVal, cclListS, List.getD_cons_succ, List.getD_cons_zero]
  · rw [word_g31, ← pow_add]; congr 1; omega
  · rw [word_g2047, ← pow_add]; congr 1; omega
  · rw [pow32_eq, hinv, ← pow_add, show 32 * w + t = n - 1 by omega, e_add_self]
  · rw [iv0_word]; exact s00
  · rw [iv1_word]; exact s01
  · rw [word_zero]; exact s02
  · rw [word_one, gen_pow_eq_ofK, ← ofK_one, ← ofK_add]; exact ofK_isInK _
  · intro h
    rw [word_one, ← pow_zero gen]
    have hw0 : 0 < w := by
      rcases Nat.eq_zero_or_pos w with h0 | h0
      · exfalso; apply h; rw [h0, word_one, pow_zero, e_add_self]
      · exact h0
    exact loopB_bwd (B := L87Step rd c base entries cover origin (gen ^ L) gsq
        (coreProgram.RelB CM.sem rd))
      (fun x hB hK hnext => l87_step_bwdB rd (gen ^ w) c base entries cover origin (gen ^ L) gsq x
        hB hK hnext) hw0 rfl (fun j _ h2 => hsteps j h2)
  · exact sw0
  · exact sw1
  · exact sw2
  · refine ⟨t, by simp [cctNames]; omega, gen_pow_eq_ofK t, ?_⟩
    rw [← List.getD_eq_getElem _ "" (by simp [cctNames]; omega)]
    refine cct_relB_low hl t ht32 hL16 rfl (by rw [pow32_eq]; exact childReads_slice hR (32 * w) t (by omega))
      ?_
    have := chainSteps_cells CM hlen hH hcan (k := 32 * w) (m := t) (by omega)
      (blocksOf_sliceOf cs (32 * w) t) (fun j hj => baseMd_eq w j (by omega))
    rwa [show 32 * w + t = n - 1 by omega] at this
  · exact limit_mul_inv (hoff _ (by omega))
  · rw [hinv]; exact hmark
  · exact (scaled_log_6_iffB hT _ _).mpr ⟨_, rfl, n, hn, rfl, rfl⟩
  all_goals try (rw [pow4_eq _ (off (n - 1)) rfl])
  · exact (cellsAt_four.mp hcl).1
  · exact (cellsAt_four.mp hcl).2.1
  · exact (cellsAt_four.mp hcl).2.2.1
  · exact (cellsAt_four.mp hcl).2.2.2
  · rw [hlast, hmd, show d0 = (d0, d1).1 from rfl, show d1 = (d0, d1).2 from rfl, hd]
    exact final_cells CM hlen (by omega) hH (hb (n - 1) (by omega))

/-! ## `child_claim_list_digest`, placed over the model -/

/-- `child_claim_list_digest`'s precondition over `H` (`CclPreAt`): the claims' digest answered. -/
def CclPreAtC (H : List UInt8 → Option Digest) (off : ℕ → ℕ) (cs : List E) (rd : Reader) :
    List E → List E → Prop
  | [entries, cover, base, origin, limit, ng, gsq], [d0, d1] => SquaresAt rd gsq ∧
      (∃ L ≤ 2 ^ 16, limit = gen ^ L) ∧ ∃ n < 2 ^ 16, ng = gen ^ n ∧
        cs.length = 4 * n ∧ ChildReads rd entries cover base origin limit off cs n ∧
        (∀ c ∈ cs, IsCanonical128 c) ∧
          ∃ d, H (cs.flatMap cellBytes) = some d ∧ (d0, d1) = digestScalars d
  | _, _ => False

theorem cclPreAtC_shape {H : List UInt8 → Option Digest} {off : ℕ → ℕ} {cs : List E} {rd : Reader}
    {args rets : List E} (h : CclPreAtC H off cs rd args rets) :
    ∃ entries cover base origin limit ng gsq d0 d1, args = [entries, cover, base, origin, limit, ng, gsq] ∧
      rets = [d0, d1] := by
  unfold CclPreAtC at h
  split at h
  · exact ⟨_, _, _, _, _, _, _, _, _, rfl, rfl⟩
  · exact h.elim

/-- At the deployed hash, `CclPreAtC` is `CclPreAt`. -/
theorem cclPreAtC_deployed (off : ℕ → ℕ) (cs : List E) (rd : Reader) (args rets : List E) :
    CclPreAtC CompModel.deployed.H off cs rd args rets ↔ CclPreAt off cs rd args rets := by
  constructor
  · intro h
    obtain ⟨_, _, _, _, _, _, _, _, _, rfl, rfl⟩ := cclPreAtC_shape h
    obtain ⟨hT, hL, n, hn, hng, hlen, hR, hcan, d, hdd, hd⟩ := h
    simp only [show CompModel.deployed.H = fun x ↦ some (blake2sBytes x) from rfl,
      Option.some.injEq] at hdd
    exact ⟨hT, hL, n, hn, hng, hlen, hR, hcan, by rw [hdd]; exact hd⟩
  · intro h
    obtain ⟨_, _, _, _, _, _, _, _, _, rfl, rfl⟩ := cclPreAt_shape h
    obtain ⟨hT, hL, n, hn, hng, hlen, hR, hcan, hd⟩ := h
    exact ⟨hT, hL, n, hn, hng, hlen, hR, hcan, _, rfl, hd⟩

/-- The windows' scratch table of a child's list at `b` over the model (`cclScratchL`). -/
def cclScratchLC (CM : CompModel) (cs : List E) (b w : ℕ) : Layout :=
  (List.range (w + 1)).map fun q => (b + 4 * q, cclSlotC CM cs q)

theorem cclScratchLC_disj {CM : CompModel} {cs : List E} {b w : ℕ} : DisjL (cclScratchLC CM cs b w) := by
  unfold DisjL cclScratchLC
  rw [List.pairwise_map]
  exact (List.pairwise_lt_range (n := w + 1)).imp fun {a c} h => Or.inl (by simp only [cclSlotC]; simp; omega)

theorem cclScratchC_slot {CM : CompModel} {cs : List E} {b w q r : ℕ} (hq : q ≤ w) (hr : r < 3) :
    RegionL (cclScratchLC CM cs b w) (b + 4 * q + r) :=
  ⟨(b + 4 * q, cclSlotC CM cs q), List.mem_map.mpr ⟨q, List.mem_range.mpr (by omega), rfl⟩, by omega,
    by simp only [cclSlotC, List.length_cons, List.length_nil]; omega⟩

theorem cclScratchC_region {CM : CompModel} {cs : List E} {b w i : ℕ}
    (h : RegionL (cclScratchLC CM cs b w) i) : b ≤ i ∧ i < b + 4 * (w + 1) := by
  obtain ⟨q, hq, h1, h2⟩ := h
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
  have := List.mem_range.mp hj
  simp only [cclSlotC, List.length_cons, List.length_nil] at h1 h2
  omega

theorem cclScratchC_of_memL {CM : CompModel} {rd : Reader} {L : Layout} (h : MemL rd L) {cs : List E}
    {b w : ℕ} (hs : ∀ q ∈ cclScratchLC CM cs b w, q ∈ L) : ChildScratchC CM rd (gen ^ b) cs w :=
  fun q hq => by
    rw [← pow_add]
    exact cells_of_memL h (hs _ (List.mem_map.mpr ⟨q, List.mem_range.mpr (by omega), rfl⟩))

/-- **`child_claim_list_digest` is complete over a completeness model, uniformly placed, at the
indices `off` and the claims `cs`** (`ccld_completeRelAtB`): on a memory defined below `2^κ`,
`κ ≥ 16`, at claims whose digest the model answers, by trees within `ccldBound`. -/
theorem ccld_completeRelBS {CM : CompModel} (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ}
    (hκ : 16 ≤ κ) (off : ℕ → ℕ) (cs : List E) (Bsl Bsl6 : ℕ)
    (hsl : TotalLeB CM.sem coreProgram fs "scaled_log__L11" fun _ => Bsl)
    (hsl6 : TotalLeB CM.sem coreProgram fs "scaled_log__L6" fun _ => Bsl6) :
    CompleteRelBS CM.sem fs cert κ "child_claim_list_digest" (CclPreAtC CM.H off cs)
      (ccldBound fs (fs "child_claims_window" + Bsl) Bsl6 (cs.length / 4)) := by
  intro args rets Lin hpre fp
  classical
  by_cases hex : ∃ rd1, LowDef κ rd1 ∧ MemL rd1 Lin
  swap
  · refine ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, Nat.zero_le _,
      fun rd hl hL => absurd ⟨rd, hl, ?_⟩ hex⟩
    simpa using hL
  obtain ⟨rd1, hl1, hL1⟩ := hex
  obtain ⟨entries, cover, base, origin, limit, ng, gsq, d0, d1, rfl, rfl⟩ := cclPreAtC_shape (hpre rd1 hl1 hL1)
  obtain ⟨hT1, ⟨L, hL16, rfl⟩, n, hn, rfl, hlen, hR1, hcan, d, hH, hd⟩ := hpre rd1 hl1 hL1
  have hpre' : ∀ rd, LowDef κ rd → MemL rd Lin →
      SquaresAt rd gsq ∧ ChildReads rd entries cover base origin (gen ^ L) off cs n := by
    intro rd hl hL
    obtain ⟨hT, -, n', hn', hng', -, hR', -, -⟩ := hpre rd hl hL
    obtain rfl : n = n' := gen_pow_inj' (by omega) (by omega) hng'
    exact ⟨hT, hR'⟩
  have hFc : ∀ j r, ∃ i, j < n → r < 4 →
      (entries * gen ^ (4 * off j)).limb 0 * gpow r = gpow i ∧ RegionL Lin i := by
    intro j r
    by_cases h : j < n ∧ r < 4
    · obtain ⟨hj, hr⟩ := h
      have hall : ∀ rd, LowDef κ rd → MemL rd Lin →
          LoadHolds rd (entries * gen ^ (4 * off j)) r (cs.getD (4 * j + r) 0) := by
        intro rd hl hL
        have hc4 := ((hpre' rd hl hL).2 j hj).2.2
        exact match r, hr with
          | 0, _ => by simpa using hc4 0 (by simp)
          | 1, _ => by simpa using hc4 1 (by simp)
          | 2, _ => by simpa using hc4 2 (by simp)
          | 3, _ => by simpa using hc4 3 (by simp)
          | _ + 4, hr => absurd hr (by omega)
      obtain ⟨i, hi⟩ := forced_load hall hl1 hL1
      exact ⟨i, fun _ _ => hi⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose cidx hcidx using hFc
  have hFm : ∀ j, ∃ i, j < n → (cover * (origin * gen ^ off j)).limb 0 * gpow 0 = gpow i ∧
      RegionL Lin i := by
    intro j
    by_cases h : j < n
    · obtain ⟨i, hi⟩ := forced_load (fun rd hl hL => ((hpre' rd hl hL).2 j h).2.1) hl1 hL1
      exact ⟨i, fun _ => hi⟩
    · exact ⟨0, fun h1 => absurd h1 h⟩
  choose midx hmidx using hFm
  have hSq : ∀ j, ∃ i, j < 16 → gsq.limb 0 * gpow j = gpow i ∧ RegionL Lin i := by
    intro j
    by_cases hj : j < 16
    · obtain ⟨i, hi⟩ := forced_load (fun rd hl hL => (hpre' rd hl hL).1 j hj) hl1 hL1
      exact ⟨i, fun _ => hi⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose sidx hsidx using hSq
  have hgK : IsInK gsq := (hT1 0 (by norm_num)).1
  have hlow : ∀ rd, LowDef κ rd → Low16 rd := fun rd hl i hi =>
    hl i (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hκ))
  set PL : Layout := ccldPins cs base n cidx midx ++ pinL (fun j => gen ^ 2 ^ j) sidx 16 with hPL
  -- the pins read back as the reads and the squares table
  have hPLr : ∀ rd', MemL rd' PL →
      SquaresAt rd' gsq ∧ ChildReads rd' entries cover base origin (gen ^ L) off cs n := by
    intro rd' h
    refine ⟨fun j hj => pin_loads h hgK (fun j hj => (hsidx j hj).1)
        (fun q hq => List.mem_append_right _ hq) j hj,
      fun j hj => ⟨(hR1 j hj).1, load_of_pin h (hR1 j hj).2.1.1 (hmidx j hj).1
        (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))),
        fun r hr => ?_⟩⟩
    have hr4 : r < 4 := by simpa using hr
    have := load_of_pin h ((hR1 j hj).2.2 0 (by simp)).1 (hcidx j r hj hr4).1 (v := cs.getD (4 * j + r) 0)
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj,
        List.mem_map.mpr ⟨r, List.mem_range.mpr hr4, rfl⟩⟩)))
    have key : ([cs.getD (4 * j) 0, cs.getD (4 * j + 1) 0, cs.getD (4 * j + 2) 0, cs.getD (4 * j + 3) 0] :
        List E)[r]'hr = cs.getD (4 * j + r) 0 := getElem_four cs j r hr4
    rw [key]; exact this
  have hPLm : ∀ rd, MemL rd Lin → MemL rd PL := by
    intro rd hL q hq k hk
    have e : ∀ {i : ℕ} {v : E}, RegionL Lin i → rd1 (gpow i) = some v → q = (i, [v]) →
        LoadHolds rd (ofK (gpow q.1)) k (q.2[k]'hk) := fun {i v} hR hv hqe => by
      subst hqe
      simp only [List.length_cons, List.length_nil] at hk
      obtain rfl : k = 0 := by omega
      refine ⟨ofK_isInK _, ?_⟩
      rw [Main.addr_ofK, Nat.add_zero, Main.memL_agree hL hL1 _ hR, hv]
      rfl
    rw [hPL, List.mem_append, ccldPins, List.mem_append] at hq
    rcases hq with (hq | hq) | hq
    · obtain ⟨j, hj, hq⟩ := List.mem_flatMap.mp hq
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
      have hj := List.mem_range.mp hj
      have hr := List.mem_range.mp hr
      refine e (hcidx j r hj hr).2 ?_ rfl
      have := ((hR1 j hj).2.2 r (by simp; omega)).2
      rw [(hcidx j r hj hr).1] at this
      rw [this]
      exact match r, hr with
        | 0, _ => by simp
        | 1, _ => by simp
        | 2, _ => by simp
        | 3, _ => by simp
        | _ + 4, hr => absurd hr (by omega)
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
      have hj := List.mem_range.mp hj
      refine e (hmidx j hj).2 ?_ rfl
      have := (hR1 j hj).2.1.2
      rwa [(hmidx j hj).1] at this
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
      have hj := List.mem_range.mp hj
      refine e (hsidx j hj).2 ?_ rfl
      have := (hT1 j hj).2
      rwa [(hsidx j hj).1] at this
  have hPLR : ∀ i, RegionL PL i → RegionL Lin i := by
    intro i ⟨q, hq, h1, h2⟩
    rw [hPL, List.mem_append, ccldPins, List.mem_append] at hq
    rcases hq with (hq | hq) | hq
    · obtain ⟨j, hj, hq⟩ := List.mem_flatMap.mp hq
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
      simp only [List.length_cons, List.length_nil] at h1 h2
      rw [show i = cidx j r by omega]
      exact (hcidx j r (List.mem_range.mp hj) (List.mem_range.mp hr)).2
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
      simp only [List.length_cons, List.length_nil] at h1 h2
      rw [show i = midx j by omega]
      exact (hmidx j (List.mem_range.mp hj)).2
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
      simp only [List.length_cons, List.length_nil] at h1 h2
      rw [show i = sidx j by omega]
      exact (hsidx j (List.mem_range.mp hj)).2
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · obtain rfl : cs = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
    refine ⟨fs "child_claim_list_digest", [], [d0, d1], [], ⟨rfl, rfl⟩, by simp [Within], disj_nil,
      by unfold ccldBound; omega, fun rd hl hL => ?_⟩
    have h8 : listVal (ccldZeroList entries cover base origin (gen ^ L) gsq d0 d1) (.n 8) = 0 := by
      show (1 : E) + word 1 0 0 = 0; rw [word_one, e_add_self]
    have hw := walk_ccld_zero _ h8
    have hev := holdsB_of_holdsList find_child_claim_list_digest
      (ccld_holds_zeroC (CM := CM) rd entries cover base origin (gen ^ L) gsq hH hd) hw
    obtain ⟨e1, e2, e3, e4, e5⟩ :=
      ccld_zero_events (listVal (ccldZeroList entries cover base origin (gen ^ L) gsq d0 d1))
    have h := relAtInB_of_walk (S := CM.sem) (P := coreProgram) (fs := fs) (cert := cert) (rd := rd)
      coreProgram_wf (R := RegionL Lin) (D := RegionL []) (Dk := fun _ => False) (fp := fp) (N := 0)
      find_child_claim_list_digest (Or.inl (by decide +kernel)) rfl hw rfl hev (by rw [e1, e2]; rfl)
      (by rw [e3]; simp) (by rw [e4]; exact ⟨rfl, fun _ h => h⟩) (by rw [e5]; simp)
      (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
    rwa [e2, List.sum_nil, Nat.add_zero, Nat.add_zero] at h
  obtain ⟨w, hw⟩ : ∃ w, w = (n - 1) / 32 := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = (n - 1) % 32 := ⟨_, rfl⟩
  have ht32 : t < 32 := by omega
  have hwt : n = 32 * w + t + 1 := by omega
  let KL : ℕ → Layout := fun fp => cclScratchLC CM cs (fp + fs "child_claim_list_digest") w ++ PL
  have hKL : ∀ fp rd', MemL rd' (KL fp) → SquaresAt rd' gsq ∧
      ChildReads rd' entries cover base origin (gen ^ L) off cs n ∧
        ChildScratchC CM rd' (gen ^ (fp + fs "child_claim_list_digest")) cs w :=
    fun fp rd' h => ⟨(hPLr rd' (Main.memL_append.mp h).2).1, (hPLr rd' (Main.memL_append.mp h).2).2,
      cclScratchC_of_memL h fun q hq => List.mem_append_left _ hq⟩
  have hKLreg : ∀ fp i, RegionL (KL fp) i →
      RegionL (cclScratchLC CM cs (fp + fs "child_claim_list_digest") w) i ∨ RegionL Lin i := by
    intro fp i ⟨q, hq, h1, h2⟩
    rcases List.mem_append.mp hq with hq | hq
    · exact Or.inl ⟨q, hq, h1, h2⟩
    · exact Or.inr (hPLR i ⟨q, hq, h1, h2⟩)
  have hregKL : ∀ fp A, ChildLoad entries cover origin off n A → ∃ i, A = gpow i ∧ RegionL (KL fp) i := by
    intro fp A hA
    rcases hA with ⟨j, hj, rfl⟩ | ⟨j, hj, r, hr, rfl⟩
    · refine ⟨midx j, (hmidx j hj).1, ⟨(midx j, [base * gen ^ j]), ?_, le_refl _, by simp⟩⟩
      exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))
    · refine ⟨cidx j r, (hcidx j r hj hr).1, ⟨(cidx j r, [cs.getD (4 * j + r) 0]), ?_, le_refl _, by simp⟩⟩
      exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, List.mem_map.mpr ⟨r, List.mem_range.mpr hr, rfl⟩⟩)))
  have hch : ChainSteps CM.sem (CM.st (prefixAt (cs.flatMap cellBytes) (32 * w)))
      (blocksOf (sliceOf cs (32 * w) t)) (baseMd (eOfNat (2 ^ 11 * w))) t
      (CM.st (prefixAt (cs.flatMap cellBytes) (n - 1))) := by
    have := chainSteps_cells CM hlen hH hcan (k := 32 * w) (m := t) (by omega)
      (blocksOf_sliceOf cs (32 * w) t) (fun j hj => baseMd_eq w j (by omega))
    rwa [show 32 * w + t = n - 1 by omega] at this
  refine completeAtS_nodeB find_child_claim_list_digest (by
      rw [Program.loop_of_find? find_child_claim_list_digest]; decide +kernel) κ Lin _ _ [4 * (w + 1)]
    (fun fp => cclScratchLC CM cs (fp + fs "child_claim_list_digest") w)
    (fun fp i hi => ⟨(4 * (w + 1), fp + fs "child_claim_list_digest"), List.mem_singleton_self _,
      (cclScratchC_region hi).1, (cclScratchC_region hi).2⟩)
    (fun fp q hq => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
      have := List.mem_range.mp hj
      simp only [cclSlotC, List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
      omega) (fun _ => cclScratchLC_disj)
    (fun fp => [⟨"__loop87", decide (word 1 0 0 + gen ^ w ≠ 0),
        [gen ^ 0, gen ^ w, gen ^ (fp + fs "child_claim_list_digest"), base, entries, cover, origin, gen ^ L,
          gsq], KL fp, []⟩,
      ⟨cctNames[t]!, true, cclSlotC CM cs w ++ [entries, cover, base * pow32 (gen ^ w), origin, gen ^ L],
        KL fp, [(CM.st (prefixAt (cs.flatMap cellBytes) (n - 1))).1,
          (CM.st (prefixAt (cs.flatMap cellBytes) (n - 1))).2]⟩,
      ⟨"scaled_log__L6", true, [gen ^ n, gsq], KL fp, [eOfNat (2 ^ 6 * n)]⟩])
    (fun k => if k.f = "__loop87" then l87Bound fs (fs "child_claims_window" + Bsl) w 0
      else if k.f = "scaled_log__L6" then Bsl6 else fs k.f) ?_ ?_
    (ccldBound fs (fs "child_claims_window" + Bsl) Bsl6 (cs.length / 4)) ?_ ?_ fp
  · intro fp k hk htk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    · have hw0 : 0 < w := by
        rcases Nat.eq_zero_or_pos w with h0 | h0
        · simp [h0, word_one, e_add_self] at htk
        · exact h0
      refine (l87_completeAtBS fs cert hκ (KL fp) hL16 hn (by omega) hlen hcan hH
        (fun rd _ h => (hKL fp rd h).2.1)
        (fun rd h => (hKL fp rd h).1) (fun rd h => (hKL fp rd h).2.2) (hregKL fp)
        (fun q hq r hr => by
          obtain ⟨e, he, h1, h2⟩ := cclScratchC_slot (CM := CM) (cs := cs)
            (b := fp + fs "child_claim_list_digest") (w := w) hq hr
          exact ⟨e, List.mem_append_left _ he, h1, h2⟩) Bsl hsl 0 hw0).mono le_rfl (by simp [KidR.kid])
    · show CompleteAtBS CM.sem fs cert κ cctNames[t]! _ _ _ _
      have hne := cct_ne t ht32
      rw [cctNames_getElem! ht32] at hne ⊢
      refine (cct_completeAtBS fs cert hκ t ht32 (KL fp) hL16 rfl (off := fun k => off (32 * w + k))
        (cs := sliceOf cs (32 * w) t)
        (fun rd _ h => by rw [pow32_eq]; exact childReads_slice (hKL fp rd h).2.1 (32 * w) t (by omega))
        (fun A hA => hregKL fp A (childLoad_shift (by omega) hA)) hch).mono le_rfl
        (by simp only [hne.1, hne.2, ↓reduceIte, KidR.kid, le_refl])
    · exact LeanVM.Guest.B1.completeAtS_of_rel_pureB cldKid_pure (by simp [cldKidSet])
        (fun rd h => (scaled_log_6_iffB (hKL fp rd h).1 _ _).mpr ⟨_, rfl, n, hn, rfl, rfl⟩) κ hsl6
  · intro fp k hk _ i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl <;> exact hKLreg fp i hi
  · intro fp
    obtain ⟨hw0, hl87⟩ : True ∧ fs "__loop87" ≤ l87Bound fs (fs "child_claims_window" + Bsl) w 0 :=
      ⟨trivial, by unfold l87Bound; omega⟩
    have hc : n = cs.length / 4 := by omega
    have hw' : w = (n - 1) / 32 := hw
    simp only [kidsBound, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, KidR.kid, ccldBound,
      ← hc, ← hw']
    have hne := cct_ne t ht32
    have e1 : ("scaled_log__L6" = "__loop87") = False := by decide
    rw [show (n - 1) % 32 = t from ht.symm, cctNames_getElem! ht32] at *
    simp only [↓reduceIte, hne.1, hne.2, e1, Nat.add_zero]
    split <;> omega
  · intro fp' rd hl hLb hLin
    have hPL := hPLm rd hLin
    refine ⟨fun k hk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl <;> exact Main.memL_append.mpr ⟨hLb, hPL⟩, ?_⟩
    obtain ⟨hT, hR⟩ := hpre' rd hl hLin
    have hscr : ChildScratchC CM rd (gen ^ (fp' + fs "child_claim_list_digest")) cs ((n - 1) / 32) := by
      rw [← hw]; exact cclScratchC_of_memL hLb fun q hq => hq
    obtain ⟨t1, t2, t3, t4, t5, t6, hh⟩ := ccld_holds_posC (hlow rd hl) hT hL16 hn hn1 hlen hR hcan hscr hH hd
    rw [← hw, ← ht] at hh
    set σ := listVal (cclListS entries cover base origin (gen ^ L) gsq (gen ^ (fp' + fs "child_claim_list_digest"))
      d0 d1 cs (off (n - 1)) L n w t t1 t2 t3 t4 t5 t6 (CM.st (prefixAt (cs.flatMap cellBytes) (32 * w)))
      (CM.st (prefixAt (cs.flatMap cellBytes) (n - 1)))) with hσ
    have h8 : σ (.n 8) ≠ 0 := fun h' => by
      have h'' : gen ^ n + word 1 0 0 = 0 := h'
      rw [word_one] at h''
      have := (gen_pow_eq_one_iff (by omega)).mp (e_add_eq_zero_iff.mp h'')
      omega
    have hw' := walk_ccld_pos σ h8 ht32 (gen_pow_eq_ofK t)
    have hev := holdsB_of_holdsList find_child_claim_list_digest hh hw'
    obtain ⟨e1, e2, e3, e4, e5⟩ := ccld_pos_events σ t
    have h39 : logG (σ (.n 39)) = 4 * (w + 1) := by
      rw [show σ (.n 39) = gen ^ (4 * (w + 1)) by
        show gen ^ w * word 2 0 0 * (gen ^ w * word 2 0 0) * (gen ^ w * word 2 0 0 * (gen ^ w * word 2 0 0)) = _
        rw [word_gen]; ring]
      exact logG_gen_pow (by omega)
    refine ⟨σ, _, _, rfl, hw', rfl, hev, ?_, e3, by rw [e2, h39], ?_, fun A hA => ?_⟩
    · rw [e4]
      refine ⟨rfl, rfl, fun _ => ⟨?_, rfl⟩, rfl, rfl, fun _ => ⟨rfl, rfl⟩, rfl, rfl, fun _ => ⟨rfl, rfl⟩,
        trivial⟩
      show [word 1 0 0, gen ^ w, gen ^ (fp' + fs "child_claim_list_digest"), base, entries, cover, origin,
        gen ^ L, gsq] = _
      rw [word_one, pow_zero]
    · rw [e1]
      simp only [List.map_cons, List.map_nil, bases]
      rw [← gen_pow_eq_ofK]; rfl
    · rw [e5] at hA
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
      set cx := fp' + fs "child_claim_list_digest" with hcx
      have g40 : σ (.n 40) = gen ^ cx := rfl
      have g49 : σ (.n 49) = gen ^ (cx + 4 * w) := by
        show gen ^ cx * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w)) = _
        ring
      have g71 : σ (.n 71) = cover * (origin * gen ^ off (n - 1)) := rfl
      have g74 : σ (.n 74) = entries * gen ^ (4 * off (n - 1)) := by
        show entries * (gen ^ off (n - 1) * gen ^ off (n - 1) * (gen ^ off (n - 1) * gen ^ off (n - 1))) = _
        rw [pow4_eq _ _ rfl]
      have sl : ∀ q r, q ≤ w → r < 3 → RegionL (cclScratchLC CM cs cx w) (cx + 4 * q + r) :=
        fun q r hq hr => cclScratchC_slot hq hr
      rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨cx + 4 * 0 + 0, by rw [g40, limb0_gen_pow, gpow_add'], Or.inl (sl 0 0 (by omega) (by omega))⟩
      · exact ⟨cx + 4 * 0 + 1, by rw [g40, limb0_gen_pow, gpow_add'], Or.inl (sl 0 1 (by omega) (by omega))⟩
      · exact ⟨cx + 4 * 0 + 2, by rw [g40, limb0_gen_pow, gpow_add'], Or.inl (sl 0 2 (by omega) (by omega))⟩
      · exact ⟨cx + 4 * w + 0, by rw [g49, limb0_gen_pow, gpow_add'], Or.inl (sl w 0 le_rfl (by omega))⟩
      · exact ⟨cx + 4 * w + 1, by rw [g49, limb0_gen_pow, gpow_add'], Or.inl (sl w 1 le_rfl (by omega))⟩
      · exact ⟨cx + 4 * w + 2, by rw [g49, limb0_gen_pow, gpow_add'], Or.inl (sl w 2 le_rfl (by omega))⟩
      · exact ⟨_, by rw [g71]; exact (hmidx (n - 1) (by omega)).1, Or.inr (hmidx (n - 1) (by omega)).2⟩
      · exact ⟨_, by rw [g74]; exact (hcidx (n - 1) 0 (by omega) (by omega)).1,
          Or.inr (hcidx (n - 1) 0 (by omega) (by omega)).2⟩
      · exact ⟨_, by rw [g74]; exact (hcidx (n - 1) 1 (by omega) (by omega)).1,
          Or.inr (hcidx (n - 1) 1 (by omega) (by omega)).2⟩
      · exact ⟨_, by rw [g74]; exact (hcidx (n - 1) 2 (by omega) (by omega)).1,
          Or.inr (hcidx (n - 1) 2 (by omega) (by omega)).2⟩
      · exact ⟨_, by rw [g74]; exact (hcidx (n - 1) 3 (by omega) (by omega)).1,
          Or.inr (hcidx (n - 1) 3 (by omega) (by omega)).2⟩

/-- The deployed `ccld_completeRelAtB`, from `ccld_completeRelBS` at `CompModel.deployed`. -/
theorem ccld_completeRelB_of_comp (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 16 ≤ κ)
    (off : ℕ → ℕ) (cs : List E) (Bsl Bsl6 : ℕ)
    (hsl : TotalLe coreProgram fs "scaled_log__L11" fun _ => Bsl)
    (hsl6 : TotalLe coreProgram fs "scaled_log__L6" fun _ => Bsl6) :
    CompleteRelB fs cert κ "child_claim_list_digest" (CclPreAt off cs)
      (ccldBound fs (fs "child_claims_window" + Bsl) Bsl6 (cs.length / 4)) := by
  have h := ccld_completeRelBS (CM := CompModel.deployed) fs cert hκ off cs Bsl Bsl6
    (by rw [show CompModel.deployed.sem = blakeDeployed from rfl, totalLeB_deployed]; exact hsl)
    (by rw [show CompModel.deployed.sem = blakeDeployed from rfl, totalLeB_deployed]; exact hsl6)
  rw [show CompModel.deployed.sem = blakeDeployed from rfl, completeRelBS_deployed] at h
  exact fun args rets Lin hpre =>
    h args rets Lin fun rd hl hL => (cclPreAtC_deployed off cs rd args rets).mpr (hpre rd hl hL)

end
end LeanVM.Guest.B1.Digest
