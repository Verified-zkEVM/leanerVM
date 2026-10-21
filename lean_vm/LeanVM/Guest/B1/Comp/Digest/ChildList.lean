/-
  LeanVM.Guest.B1.Comp.Digest.ChildList

  The child claim lists over a completeness model: `child_claims_tail__L{k}` and
  `child_claims_window` under any semantics, `__loop87` and `child_claim_list_digest` over the
  model's chain of the claims' bytes.
-/

module

public import LeanVM.Guest.B1.Comp.Digest.ClaimList
public import LeanVM.Guest.B1.Digest.ChildListM

/-!
# Child claim lists over a completeness model

The child list (`ChildList.lean`) reads its claims through the table (`ChildReads`), in windows of
32 blocks and a tail, chained as the parent's claim list (`Comp/Digest/ClaimList.lean`):

* `cBlk0B_bwd`, `cBlkB_bwd`, `cBlkHeadB_bwd`: the blocks under any semantics;
* `child_tail_bwdB`, `child_claims_tail_compB`, `child_window_bwdB`: the tail and the window from
  their rows (`Meaning_child_claims_tailB S`, `Meaning_child_claims_windowB S`, W2's), any
  semantics;
* `l87_step_bwdB`, `ChildScratchC`, `child_claim_list_digest_comp` from
  `Meaning_child_claim_list_digestComp CM`, `child_claim_list_digest_completeC`; at
  `CompModel.deployed` the deployed backward direction (`child_claim_list_digest_of_comp`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.E2E.Complete

@[expose] public section

/-! ## The blocks, backward, under any semantics -/

section Blocks

variable {Sem : BlakeSem} {rd : Reader} {σ : Val}

theorem cBlkHeadB_bwd {b j e L : ℕ} {t1 t2 c0 c1 c2 c3 : E} (hj : j < 64)
    (he : e < L) (hlim : σ (.n 7) = gen ^ L) (h1 : LoadHolds rd (gen ^ e) 0 t1)
    (h2 : LoadHolds rd (gen ^ (L - 1 - e)) 0 t2)
    (hs : LoadHolds rd (σ (.n 4) * (σ (.n 6) * gen ^ e)) 0 (σ (.n 5) * gen ^ j))
    (hc : CellsAt rd (σ (.n 3) * gen ^ (4 * e)) [c0, c1, c2, c3])
    (hv : ∀ r < 17, σ (.n (b + r)) = (cHeadVals σ e L t1 t2 j c0 c1 c2 c3).getD r 0) :
    ∀ a ∈ cBlkHead b j, a.HoldsB Sem rd σ :=
  (forall_holdsB_noBlake (by simp [cBlkHead, atomNoBlake])).mpr
    (cBlkHead_bwd hj he hlim h1 h2 hs hc hv)

theorem cBlk0B_bwd {o e L : ℕ} {t1 t2 c0 c1 c2 c3 : E} {out : E × E}
    (he : e < L) (hlim : σ (.n 7) = gen ^ L) (h1 : LoadHolds rd (gen ^ e) 0 t1)
    (h2 : LoadHolds rd (gen ^ (L - 1 - e)) 0 t2)
    (hs : LoadHolds rd (σ (.n 4) * (σ (.n 6) * gen ^ e)) 0 (σ (.n 5)))
    (hc : CellsAt rd (σ (.n 3) * gen ^ (4 * e)) [c0, c1, c2, c3])
    (hcc : Sem.check ![c0, c1, c2, c3] (σ (.n o)) (σ (.n (o + 1))) out.1 out.2
      (baseMd (σ (.n 2)) 0))
    (hv : ∀ r < 19, σ (.n (o + 2 + r)) = (cBlk0Vals σ e L t1 t2 c0 c1 c2 c3 out).getD r 0) :
    ∀ a ∈ cBlk0 o, a.HoldsB Sem rd σ := by
  have hv' : ∀ r, 2 ≤ r → r < 21 → σ (.n (o + r)) = (cBlk0Vals σ e L t1 t2 c0 c1 c2 c3 out).getD (r - 2) 0 :=
    fun r h1 h2 => by rw [← hv (r - 2) (by omega)]; congr 2; omega
  rw [cellsAt_four, ← pow4_eq _ e rfl] at hc
  rw [baseMd, ← word_md] at hcc
  simp only [cBlk0, List.forall_mem_cons, Atom.HoldsB, forall_mem_nil_iff, and_true,
    hv' 2 (by omega) (by omega), hv' 3 (by omega) (by omega), hv' 4 (by omega) (by omega),
    hv' 5 (by omega) (by omega), hv' 6 (by omega) (by omega), hv' 7 (by omega) (by omega),
    hv' 8 (by omega) (by omega), hv' 9 (by omega) (by omega), hv' 10 (by omega) (by omega),
    hv' 11 (by omega) (by omega), hv' 12 (by omega) (by omega), hv' 13 (by omega) (by omega),
    hv' 14 (by omega) (by omega), hv' 15 (by omega) (by omega), hv' 16 (by omega) (by omega),
    hv' 17 (by omega) (by omega), hv' 18 (by omega) (by omega), hv' 19 (by omega) (by omega),
    hv' 20 (by omega) (by omega), Nat.reduceSub, cBlk0Vals, List.getD_cons_succ,
    List.getD_cons_zero, true_and]
  rw [hlim, limit_mul_inv he]
  exact ⟨⟨h1, rfl, h2⟩, hs, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, hcc⟩

theorem cBlkB_bwd {o j e L : ℕ} {t1 t2 c0 c1 c2 c3 : E} {out : E × E}
    (hj : j < 64) (he : e < L) (hlim : σ (.n 7) = gen ^ L)
    (h1 : LoadHolds rd (gen ^ e) 0 t1) (h2 : LoadHolds rd (gen ^ (L - 1 - e)) 0 t2)
    (hs : LoadHolds rd (σ (.n 4) * (σ (.n 6) * gen ^ e)) 0 (σ (.n 5) * gen ^ j))
    (hc : CellsAt rd (σ (.n 3) * gen ^ (4 * e)) [c0, c1, c2, c3])
    (hcc : Sem.check ![c0, c1, c2, c3] (σ (.n (o + 21 * j - 2))) (σ (.n (o + 21 * j - 1)))
      out.1 out.2 (baseMd (σ (.n 2)) j))
    (hv : ∀ r < 17, σ (.n (o + 21 * j + r)) = (cHeadVals σ e L t1 t2 j c0 c1 c2 c3).getD r 0)
    (h17 : σ (.n (o + 21 * j + 17)) = word (64 * (j + 1)) 0 0)
    (h18 : σ (.n (o + 21 * j + 18)) = σ (.n 2) + word (64 * (j + 1)) 0 0)
    (h19 : σ (.n (o + 21 * j + 19)) = out.1) (h20 : σ (.n (o + 21 * j + 20)) = out.2) :
    ∀ a ∈ cBlk o j, a.HoldsB Sem rd σ := by
  rw [cBlk, List.forall_mem_append]
  refine ⟨cBlkHeadB_bwd hj he hlim h1 h2 hs hc hv, ?_⟩
  simp only [List.forall_mem_cons, Atom.HoldsB, forall_mem_nil_iff, and_true]
  rw [h17, h18, h19, h20, hv 13 (by omega), hv 14 (by omega), hv 15 (by omega), hv 16 (by omega)]
  rw [baseMd, ← word_md] at hcc
  exact ⟨rfl, rfl, hcc⟩

end Blocks

/-! ## `child_claims_tail__L{k}` and `child_claims_window`, backward, under any semantics -/

theorem child_tail_bwdB {Sem : BlakeSem} {rd : Reader} (hm : MemOk rd) (k : ℕ) (hk1 : 1 ≤ k)
    (hk : k < 32) (name : String) {s0 s1 base entries cover marks origin limit : E} (rets : List E)
    (hL : ∃ L ≤ 2 ^ 16, limit = gen ^ L)
    (h : Meaning_child_claims_tailB Sem k rd [s0, s1, base, entries, cover, marks, origin, limit]
      rets) :
    Fn.SemB Sem (coreProgram.RelB Sem rd) rd ⟨name, [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7],
      cctBody k⟩ [s0, s1, base, entries, cover, marks, origin, limit] rets := by
  obtain ⟨_, _, _, _, _, _, _, _, o0, o1, hargs, rfl, off, cs, hlen, hR, hch⟩ := h
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hargs
  obtain ⟨sts, hst, hout, hsteps⟩ := hch
  obtain ⟨L, hL16, hlim⟩ := hL
  have hoff : ∀ j < k, off j < L := fun j hj => by
    obtain ⟨⟨L', hL', hlim', ho⟩, -⟩ := hR j hj
    have := gen_pow_inj (a := L) (b := L') (by omega) (by omega) (hlim.symm.trans hlim')
    omega
  have hw : ∀ j, ∃ t1 t2, j < k → LoadHolds rd (gen ^ off j) 0 t1 ∧
      LoadHolds rd (gen ^ (L - 1 - off j)) 0 t2 := fun j => by
    by_cases hj : j < k
    · obtain ⟨t1, t2, l1, -, l2⟩ := rangeCheck_complete hm (e := off j) (e' := L - 1 - off j)
        (by have := hoff j hj; omega) (by omega)
      exact ⟨t1, t2, fun _ => ⟨l1, l2⟩⟩
    · exact ⟨0, 0, fun h => absurd h hj⟩
  choose T1 T2 hT using hw
  set P := listVal [s0, s1, base, entries, cover, marks, origin, limit] with hP
  set S := sts with hS
  have hS0 : S 0 = (s0, s1) := hst
  simp only [Fn.SemB, cctBody, holdsListB_atoms, holdsListB_ret, List.forall_mem_append,
    forall_mem_flatMap_range, List.forall_mem_cons, Atom.HoldsB, forall_mem_nil_iff, and_true,
    List.map_cons, List.map_nil]
  obtain ⟨e8, e8k, e6⟩ := cctVals_end k P off L T1 T2 cs S
  obtain ⟨t8, t9⟩ := cctVals_st0 k P off L T1 T2 cs S
  refine ⟨fun v => cctVals k P off L T1 T2 cs S v.idx, rfl, ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, fun i hi => ?_⟩, ?_, ?_⟩, ?_⟩
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


theorem child_tail_zero_compB {Sem : BlakeSem} (rd : Reader) (name : String) (args rets : List E)
    (h : Meaning_child_claims_tailB Sem 0 rd args rets) :
    Fn.SemB Sem (coreProgram.RelB Sem rd) rd ⟨name, [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7],
      cctBody0⟩ args rets := by
  simp only [Fn.SemB, cctBody0, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB]
  obtain ⟨s0, s1, base, entries, cover, marks, origin, limit, o0, o1, rfl, rfl, off, cs, -, -, hch⟩ := h
  have hout := chainSteps_zero hch
  refine ⟨listVal [s0, s1, base, entries, cover, marks, origin, limit, s0, s1, s0, s1], rfl,
    rfl, rfl, rfl, rfl, ?_⟩
  simp only [Prod.mk.injEq] at hout
  show [s0, s1] = [o0, o1]
  rw [hout.1, hout.2]

/-- **`child_claims_tail__L{k}` is complete under any semantics**, `k < 32`, for a table of at
most `2^16` slots: its rows give the relation. -/
theorem child_claims_tail_compB {Sem : BlakeSem} {rd : Reader} (hm : MemOk rd) (k : ℕ)
    (hk : k < 32) {s0 s1 base entries cover marks origin limit : E} (rets : List E)
    (hL : ∃ L ≤ 2 ^ 16, limit = gen ^ L)
    (h : Meaning_child_claims_tailB Sem k rd [s0, s1, base, entries, cover, marks, origin, limit]
      rets) :
    coreProgram.RelB Sem rd (cctNames.getD k "") [s0, s1, base, entries, cover, marks, origin, limit]
      rets := by
  rw [relB_of_find (find_child_claims_tail k hk)]
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · exact child_tail_zero_compB rd _ _ rets h
  · simp only [show k ≠ 0 by omega, ↓reduceIte]
    exact child_tail_bwdB hm k hk1 hk _ rets hL h

theorem child_window_bwdB {Sem : BlakeSem} {rd : Reader} (hm : MemOk rd) {gsq : E}
    (hT : SquaresAt rd gsq)
    {s0 s1 base entries cover marks origin limit xq : E} {rets : List E}
    (hL : ∃ L ≤ 2 ^ 16, limit = gen ^ L)
    (h : Meaning_child_claims_windowB Sem rd
      [s0, s1, base, entries, cover, marks, origin, limit, xq, gsq] rets) :
    coreProgram.RelB Sem rd "child_claims_window"
      [s0, s1, base, entries, cover, marks, origin, limit, xq, gsq] rets := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, o0, o1, nxt, hargs, rfl, N, hN, hxq, hnxt, off, cs, hlen, hR,
    hch⟩ := h
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hargs
  obtain ⟨sts, hst, hout, hsteps⟩ := hch
  obtain ⟨L, hL16, hlim⟩ := hL
  have hoff : ∀ j < 32, off j < L := fun j hj => by
    obtain ⟨⟨L', hL', hlim', ho⟩, -⟩ := hR j hj
    have := gen_pow_inj (a := L) (b := L') (by omega) (by omega) (hlim.symm.trans hlim')
    omega
  have hw : ∀ j, ∃ t1 t2, j < 32 → LoadHolds rd (gen ^ off j) 0 t1 ∧
      LoadHolds rd (gen ^ (L - 1 - off j)) 0 t2 := fun j => by
    by_cases hj : j < 32
    · obtain ⟨t1, t2, l1, -, l2⟩ := rangeCheck_complete hm (e := off j) (e' := L - 1 - off j)
        (lt_of_lt_of_le (hoff j hj) hL16) (by omega)
      exact ⟨t1, t2, fun _ => ⟨l1, l2⟩⟩
    · exact ⟨0, 0, fun h => absurd h hj⟩
  choose T1 T2 hT' using hw
  set P := listVal [s0, s1, base, entries, cover, marks, origin, limit, xq, gsq] with hP
  set S := sts with hS
  have hS0 : S 0 = (s0, s1) := hst
  rw [relB_of_find find_child_claims_window]
  simp only [Fn.SemB, ccwBody, ccwLast, holdsListB_atoms, List.cons_append, List.nil_append,
    Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.forall_mem_append, forall_mem_flatMap_range,
    List.forall_mem_cons, forall_mem_nil_iff, and_true, List.map_cons, List.map_nil]
  obtain ⟨e681, e682, e683, e684, e685⟩ := ccwVals_end P off L T1 T2 cs S xq nxt
  refine ⟨fun v => ccwVals P off L T1 T2 cs S xq nxt v.idx, rfl, rfl, rfl, ?_, ?_, ?_,
    ⟨⟨⟨?_, fun i hi => ?_⟩, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
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



/-! ## `__loop87` -/

/-- One iteration of `__loop87` under any semantics, backward (`l87_step`'s backward half). -/
theorem l87_step_bwdB {Sem : BlakeSem} (rd : Reader) (W c base entries cover origin limit gsq x : E)
    (h : L87Step rd c base entries cover origin limit gsq (coreProgram.RelB Sem rd) x)
    (hk : IsInK (x * gen + W))
    (hnext : x * gen + W ≠ 0 →
      coreProgram.RelB Sem rd "__loop87" (x * gen :: [W, c, base, entries, cover, origin, limit, gsq]) []) :
    ∃ fn, coreProgram.find? "__loop87" = some fn ∧
      fn.SemB Sem (coreProgram.RelB Sem rd) rd (x :: [W, c, base, entries, cover, origin, limit, gsq]) [] := by
  refine ⟨_, find_loop87, ?_⟩
  simp only [Fn.SemB, l87Body, List.cons_append, List.nil_append, Stmt.HoldsListB,
    Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil]
  obtain ⟨s0, s1, bs, o0, o1, nxt, hin, hcall, hout⟩ := h
  rw [cellsAt_three] at hin hout
  obtain ⟨l18, l19, l20⟩ := hin
  obtain ⟨l21, l22, l23⟩ := hout
  rw [← word_gen] at l21 l22 l23 hk hnext
  refine ⟨listVal [x, W, c, base, entries, cover, origin, limit, gsq, x * x, x * x * (x * x),
    c * (x * x * (x * x)), x * x, x * x * (x * x), x * x * (x * x) * (x * x * (x * x)),
    x * x * (x * x) * (x * x * (x * x)) * (x * x * (x * x) * (x * x * (x * x))), pow32 x,
    base * pow32 x, s0, s1, bs, o0, o1, nxt, word 2 0 0, x * word 2 0 0,
    x * word 2 0 0 * (x * word 2 0 0),
    x * word 2 0 0 * (x * word 2 0 0) * (x * word 2 0 0 * (x * word 2 0 0)),
    c * (x * word 2 0 0 * (x * word 2 0 0) * (x * word 2 0 0 * (x * word 2 0 0))), word 2 0 0,
    x * word 2 0 0, x * word 2 0 0 + W, word 2 0 0, x * word 2 0 0], rfl, ?_⟩
  simp only [listVal, List.getD_cons_succ, List.getD_cons_zero, true_and]
  exact ⟨rfl, l18, l19, l20, hcall, l21, l22, l23, hk, hnext, trivial⟩

/-! ## `child_claim_list_digest` -/

/-- **The child list's scratch table over a completeness model**: window `q ≤ w` at `chain·g^(4q)`,
the model's cells after `32q` blocks of the claims' bytes and its base `E(2^11·q)`
(`ChildScratch`). -/
def ChildScratchC (CM : CompModel) (rd : Reader) (chain : E) (cs : List E) (w : ℕ) : Prop :=
  ∀ q ≤ w, CellsAt rd (chain * gen ^ (4 * q)) [(CM.st (prefixAt (cs.flatMap cellBytes) (32 * q))).1,
    (CM.st (prefixAt (cs.flatMap cellBytes) (32 * q))).2, eOfNat (2 ^ 11 * q)]

/-- **`child_claim_list_digest` over a completeness model** (`Meaning_child_claim_list_digest`,
the digest the model's answer for the claims' bytes, the scratch table the model's states). -/
def Meaning_child_claim_list_digestComp (CM : CompModel) (rd : Reader) (args rets : List E) :
    Prop :=
  ∃ entries cover base origin limit n_g gsq d0 d1,
    args = [entries, cover, base, origin, limit, n_g, gsq] ∧ rets = [d0, d1] ∧
    ∃ n < 2 ^ 16, n_g = gen ^ n ∧ ∃ (off : ℕ → ℕ) (cs : List E), cs.length = 4 * n ∧
      ChildReads rd entries cover base origin limit off cs n ∧ (∀ c ∈ cs, IsCanonical128 c) ∧
      ∃ d, CM.H (cs.flatMap cellBytes) = some d ∧ (d0, d1) = digestScalars d ∧
        (n = 0 ∨ ∃ chain, ChildScratchC CM rd chain cs ((n - 1) / 32))

noncomputable def cclListS (entries cover base origin limit gsq c d0 d1 : E) (cs : List E) (eL L n w t : ℕ)
    (t1 t2 t3 t4 t5 t6 : E) (sw sl : E × E) : List E :=
  [entries, cover, base, origin, limit, gen ^ n, gsq, word 1 0 0, gen ^ n + word 1 0 0, 0, 0, 0, 0, 0,
   0, 0, d0, d1, gen ^ w, gen ^ t, word 2147483648 0 0, gen ^ (31 - t), t1, t2, word 55834575010 0 0,
   gen ^ (2047 - w), t3, t4, gen ^ w * gen ^ w, gen ^ w * gen ^ w * (gen ^ w * gen ^ w),
   gen ^ w * gen ^ w * (gen ^ w * gen ^ w) * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w)),
   gen ^ w * gen ^ w * (gen ^ w * gen ^ w) * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w)) *
     (gen ^ w * gen ^ w * (gen ^ w * gen ^ w) * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w))),
   pow32 (gen ^ w), pow32 (gen ^ w) * gen ^ t, wInv, gen ^ n * wInv, word 2 0 0,
   gen ^ w * word 2 0 0, gen ^ w * word 2 0 0 * (gen ^ w * word 2 0 0),
   gen ^ w * word 2 0 0 * (gen ^ w * word 2 0 0) * (gen ^ w * word 2 0 0 * (gen ^ w * word 2 0 0)),
   c, word 13503953895743350343 11912009169889063794 0,
   word 11170449402626986623 6620516960021240235 0, word 0 0 0, word 1 0 0, word 1 0 0 + gen ^ w,
   word 1 0 0, gen ^ w * gen ^ w, gen ^ w * gen ^ w * (gen ^ w * gen ^ w),
   c * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w)), gen ^ w * gen ^ w,
   gen ^ w * gen ^ w * (gen ^ w * gen ^ w),
   gen ^ w * gen ^ w * (gen ^ w * gen ^ w) * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w)),
   gen ^ w * gen ^ w * (gen ^ w * gen ^ w) * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w)) *
     (gen ^ w * gen ^ w * (gen ^ w * gen ^ w) * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w))),
   pow32 (gen ^ w), base * pow32 (gen ^ w), sw.1,
   sw.2, eOfNat (2 ^ 11 * w),
   sl.1, sl.2,
   gen ^ eL, wInv, limit * wInv, gen ^ (L - 1 - eL), t5, t6, wInv, gen ^ n * wInv,
   base * (gen ^ n * wInv), origin * gen ^ eL, cover * (origin * gen ^ eL), gen ^ eL * gen ^ eL,
   gen ^ eL * gen ^ eL * (gen ^ eL * gen ^ eL), entries * (gen ^ eL * gen ^ eL * (gen ^ eL * gen ^ eL)),
   eOfNat (2 ^ 6 * n), word 0 4294967295 0, eOfNat (2 ^ 6 * n) + word 0 4294967295 0,
   cs.getD (4 * (n - 1) + 0) 0, cs.getD (4 * (n - 1) + 1) 0, cs.getD (4 * (n - 1) + 2) 0,
   cs.getD (4 * (n - 1) + 3) 0, d0, d1]


/-- **`child_claim_list_digest` is complete over a completeness model**, for a table of at most
`2^16` slots. -/
theorem child_claim_list_digest_comp {CM : CompModel} {rd : Reader} (hm : MemOk rd) {gsq : E}
    (hT : SquaresAt rd gsq) {entries cover base origin limit n_g : E} {rets : List E}
    (hL : ∃ L ≤ 2 ^ 16, limit = gen ^ L)
    (h : Meaning_child_claim_list_digestComp CM rd [entries, cover, base, origin, limit, n_g, gsq]
      rets) :
    coreProgram.RelB CM.sem rd "child_claim_list_digest"
      [entries, cover, base, origin, limit, n_g, gsq] rets := by
  obtain ⟨_, _, _, _, _, _, _, d0, d1, hargs, rfl, n, hn, hng, off, cs, hlen, hR, hcan, d, hH, hd,
    hscr⟩ := h
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hargs
  rw [relB_of_find find_child_claim_list_digest]
  simp only [Fn.SemB, ccldBody, List.cons_append, List.nil_append, Stmt.HoldsListB,
    Stmt.HoldsB, Atom.HoldsB, true_and, List.map_cons, List.map_nil]
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · rw [pow_zero] at hng
    subst hng
    rw [Nat.mul_zero, List.length_eq_zero_iff] at hlen
    subst hlen
    have h11 : (1 : E) + word 1 0 0 = 0 := by rw [word_one, e_add_self]
    refine ⟨listVal ([entries, cover, base, origin, limit, 1, gsq, word 1 0 0, 1 + word 1 0 0,
      word 0 0 0, word 0 0 0, word 0 0 0, word 0 0 0, word 13503953895743350343 11912009169889063794 0,
      word 11170449402626986623 6620516960021240235 0, word 0 4294967295 0, d0, d1] ++
      List.replicate 64 0 ++ [d0, d1]), rfl, rfl, rfl, ?_, fun _ => ?_, fun h => ?_⟩
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
  rcases hscr with h0 | ⟨c, hscr⟩
  · omega
  subst hng
  obtain ⟨L, hL16, hlim⟩ := hL
  subst hlim
  set w := (n - 1) / 32 with hw
  set t := (n - 1) % 32 with ht
  have hwt : n = 32 * w + t + 1 := by omega
  have ht32 : t < 32 := by omega
  have hw2 : w < 2048 := by omega
  have hoff : ∀ j < n, off j < L := fun j hj => by
    obtain ⟨⟨L', hL', hlim', ho⟩, -⟩ := hR j hj
    have := gen_pow_inj (a := L) (b := L') (by omega) (by omega) hlim'
    omega
  obtain ⟨t1, t2, l22, -, l23⟩ := rangeCheck_complete hm (e := t) (e' := 31 - t) (by omega) (by omega)
  obtain ⟨t3, t4, l26, -, l27⟩ := rangeCheck_complete hm (e := w) (e' := 2047 - w) (by omega) (by omega)
  obtain ⟨t5, t6, l65, -, l66⟩ := rangeCheck_complete hm (e := off (n - 1)) (e' := L - 1 - off (n - 1))
    (lt_of_lt_of_le (hoff _ (by omega)) hL16) (by omega)
  have hS := fun q (hq : q ≤ w) => cellsAt_three.mp (hscr q hq)
  obtain ⟨s00, s01, s02⟩ := hS 0 (by omega)
  obtain ⟨sw0, sw1, sw2⟩ := hS w le_rfl
  simp only [Nat.mul_zero, pow_zero, mul_one, eOfNat_zero, prefixAt_zero, CM.st_nil] at s00 s01 s02
  rw [← pow4_eq _ w rfl] at sw0 sw1 sw2
  have hb := blocks_canonical hlen hcan
  -- the loop's iterations
  have hsteps : ∀ j < w, L87Step rd c base entries cover origin (gen ^ L) gsq
      (coreProgram.RelB CM.sem rd) (gen ^ j) := by
    intro j hj
    have h0 := cellsAt_three.mp (hscr j (by omega))
    have h1 := hscr (j + 1) (by omega)
    rw [show 32 * (j + 1) = 32 * j + 32 by ring] at h1
    refine ⟨_, _, _, (CM.st (prefixAt (cs.flatMap cellBytes) (32 * j + 32))).1,
      (CM.st (prefixAt (cs.flatMap cellBytes) (32 * j + 32))).2, eOfNat (2 ^ 11 * (j + 1)),
      by rw [pow4_eq _ j rfl]; exact cellsAt_three.mpr h0, ?_,
      by rw [← pow_succ, pow4_eq _ (j + 1) rfl]; exact h1⟩
    refine child_window_bwdB hm hT ⟨L, hL16, rfl⟩ ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl, rfl,
      j + 1, by omega, (pow_succ gen j).symm, rfl, fun k => off (32 * j + k), sliceOf cs (32 * j) 32,
      length_sliceOf _ _ _, ?_, ?_⟩
    · rw [pow32_eq]
      exact childReads_slice hR (32 * j) 32 (by omega)
    · exact chainSteps_cells CM hlen hH hcan (k := 32 * j) (m := 32) (by omega)
        (blocksOf_sliceOf cs (32 * j) 32) (fun i hi => windowMd_eq j i hi)
  have hlast : ![cs.getD (4 * (n - 1) + 0) 0, cs.getD (4 * (n - 1) + 1) 0,
      cs.getD (4 * (n - 1) + 2) 0, cs.getD (4 * (n - 1) + 3) 0] = blocksOf cs (n - 1) := by
    simp [blocksOf]
  have hmd : eOfNat (2 ^ 6 * n) + word 0 4294967295 0 = metadataCell (64 * n) true := by
    rw [md_final_word, eOfNat_add_metadataCell, Nat.xor_zero]; rfl
  have hinv : gen ^ n * wInv = gen ^ (n - 1) := by
    rw [show gen ^ n = gen ^ (n - 1) * gen by rw [← pow_succ]; congr 1; omega, mul_assoc, mul_comm gen,
      ginv_mul_gen, mul_one]
  obtain ⟨-, hmark, hcl⟩ := hR (n - 1) (by omega)
  refine ⟨listVal (cclListS entries cover base origin (gen ^ L) gsq c d0 d1 cs (off (n - 1)) L n w t
    t1 t2 t3 t4 t5 t6 (CM.st (prefixAt (cs.flatMap cellBytes) (32 * w)))
    (CM.st (prefixAt (cs.flatMap cellBytes) (n - 1)))), rfl, rfl, rfl, ?_, fun h => ?_,
    fun _ => ?_⟩
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
    refine child_claims_tail_compB hm t ht32 _ ⟨L, hL16, rfl⟩ ⟨_, _, _, _, _, _, _, _, _, _,
      rfl, rfl, fun k => off (32 * w + k), sliceOf cs (32 * w) t, length_sliceOf _ _ _, ?_, ?_⟩
    · rw [pow32_eq]
      exact childReads_slice hR (32 * w) t (by omega)
    · have := chainSteps_cells CM hlen hH hcan (k := 32 * w) (m := t) (by omega)
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


/-- **Completeness over a completeness model** (`child_claim_list_digest_complete`), for every
pointer `chain` of the windows' `HeapBuf` holding the model's states. -/
theorem child_claim_list_digest_completeC {CM : CompModel} {rd : Reader} (hm : MemOk rd) {gsq : E}
    (hT : SquaresAt rd gsq) (chain : E) {entries cover base origin limit : E}
    (hL : ∃ L ≤ 2 ^ 16, limit = gen ^ L) {n : ℕ} (hn : n < 2 ^ 16) (off : ℕ → ℕ) {cs : List E}
    (hlen : cs.length = 4 * n) (hR : ChildReads rd entries cover base origin limit off cs n)
    (hcan : ∀ c ∈ cs, IsCanonical128 c) {d : Digest} (hH : CM.H (cs.flatMap cellBytes) = some d)
    (hS : 0 < n → ChildScratchC CM rd chain cs ((n - 1) / 32)) :
    coreProgram.RelB CM.sem rd "child_claim_list_digest"
      [entries, cover, base, origin, limit, gen ^ n, gsq] [(digestScalars d).1, (digestScalars d).2] :=
  child_claim_list_digest_comp hm hT hL ⟨entries, cover, base, origin, limit, _, gsq, _, _, rfl, rfl,
    n, hn, rfl, off, cs, hlen, hR, hcan, d, hH, rfl, (Nat.eq_zero_or_pos n).imp id fun h => ⟨chain, hS h⟩⟩

/-! ## At the deployed model -/

/-- At the deployed model the child list's scratch table is the deployed one. -/
theorem childScratchC_deployed {rd : Reader} {chain : E} {cs : List E} {n w : ℕ}
    (hlen : cs.length = 4 * n) (hw : 32 * w ≤ n) :
    ChildScratchC CompModel.deployed rd chain cs w ↔ ChildScratch rd chain cs w := by
  have e : ∀ q ≤ w, CompModel.deployed.st (prefixAt (cs.flatMap cellBytes) (32 * q)) =
      digestScalars (prefixDigest cs (32 * q)) := fun q hq => by
    show digestScalars (absorbBlocks paramIv 0 _) = _
    rw [prefixAt_cells hlen (by omega)]
    rfl
  constructor
  · intro h q hq
    rw [← e q hq]; exact h q hq
  · intro h q hq
    rw [e q hq]; exact h q hq

theorem child_claim_list_digest_of_comp {rd : Reader} (hm : MemOk rd) {gsq : E}
    (hT : SquaresAt rd gsq) {entries cover base origin limit n_g : E} {rets : List E}
    (hL : ∃ L ≤ 2 ^ 16, limit = gen ^ L)
    (h : Meaning_child_claim_list_digest rd [entries, cover, base, origin, limit, n_g, gsq] rets) :
    coreProgram.Rel rd "child_claim_list_digest" [entries, cover, base, origin, limit, n_g, gsq]
      rets := by
  rw [← relB_deployed]
  obtain ⟨a, b, c, d', e, f, g, d0, d1, ha, hr, n, hn, hng, off, cs, hlen, hR, hcan, hd, hscr⟩ := h
  refine child_claim_list_digest_comp (CM := CompModel.deployed) hm hT hL
    ⟨a, b, c, d', e, f, g, d0, d1, ha, hr, n, hn, hng, off, cs, hlen, hR, hcan, _, rfl, hd, ?_⟩
  rcases hscr with h0 | ⟨chain, hc⟩
  · exact Or.inl h0
  · rcases Nat.eq_zero_or_pos n with h0 | hn1
    · exact Or.inl h0
    · exact Or.inr ⟨chain, (childScratchC_deployed hlen (by omega)).mpr hc⟩

end
end LeanVM.Guest.B1.Digest
