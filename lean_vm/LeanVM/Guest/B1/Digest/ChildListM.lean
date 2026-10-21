/-
  LeanVM.Guest.B1.Digest.ChildListM

  `child_claims_tail`, `child_claims_window` and `child_claim_list_digest` under a hash model:
  the rows each window and tail checked, the windows extending a prefix from the IV, and the last
  block the answered hash of the child's claim list.
-/

module

public import LeanVM.Guest.B1.Digest.ChildList
public import LeanVM.Guest.B1.Digest.ClaimListM

/-!
# A child's claim list over a hash model

As for `claim_list_digest` (`ClaimListM.lean`, pattern C): a child's tail and window state the
rows they checked from the state handed to them (`Meaning_child_claims_tailB`,
`Meaning_child_claims_windowB`, over `ChainSteps S`), the windows carry a prefix through the
scratch table (`cwins_fwdM`), and `child_claim_list_digest_model` concludes the answered hash
`M.H (cs.flatMap cellBytes) = some d` of the claims read at the hinted table indices.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-! ## The blocks, forward, under any semantics -/

section Blocks

variable {S : BlakeSem}

/-- The facts of block `0` under `S`. -/
theorem cBlk0B_fwd {rd : Reader} (hm : MemOk rd) {σ : Val} {o : ℕ}
    (h : ∀ a ∈ cBlk0 o, a.HoldsB S rd σ) :
    ∃ e, (∃ L ≤ 2 ^ 33, σ (.n 7) = gen ^ L ∧ e < L) ∧
      LoadHolds rd (σ (.n 4) * (σ (.n 6) * gen ^ e)) 0 (σ (.n 5) * gen ^ 0) ∧
      CellsAt rd (σ (.n 3) * gen ^ (4 * e))
        [σ (.n (o + 13)), σ (.n (o + 14)), σ (.n (o + 15)), σ (.n (o + 16))] ∧
      σ (.n (o + 18)) = baseMd (σ (.n 2)) 0 ∧
      S.check ![σ (.n (o + 13)), σ (.n (o + 14)), σ (.n (o + 15)), σ (.n (o + 16))]
        (σ (.n o)) (σ (.n (o + 1))) (σ (.n (o + 19))) (σ (.n (o + 20))) (σ (.n (o + 18))) := by
  simp only [cBlk0, List.forall_mem_cons, Atom.HoldsB, forall_mem_nil_iff, and_true,
    true_and] at h
  obtain ⟨c3, m4, rc, m8, m9, l5, m10, m11, m12, l13, l14, l15, l16, c17, a18, hc⟩ := h
  rw [m4, c3] at rc
  obtain ⟨e, hx, hL⟩ := limit_of_rc hm rc
  rw [m9, m8, hx] at l5
  rw [m12, m11, m10, pow4_eq _ e hx] at l13 l14 l15 l16
  refine ⟨e, hL, by rw [pow_zero, mul_one]; exact l5, cellsAt_four.mpr ⟨l13, l14, l15, l16⟩,
    by rw [a18, c17, baseMd, word_md], hc⟩

/-- The facts of a child's claim block `j ≥ 1` under `S` (`cBlk_fwd`). -/
theorem cBlkB_fwd {rd : Reader} (hm : MemOk rd) {σ : Val} {o j : ℕ} (hj : j < 64)
    (h : ∀ a ∈ cBlk o j, a.HoldsB S rd σ) :
    ∃ e, (∃ L ≤ 2 ^ 33, σ (.n 7) = gen ^ L ∧ e < L) ∧
      LoadHolds rd (σ (.n 4) * (σ (.n 6) * gen ^ e)) 0 (σ (.n 5) * gen ^ j) ∧
      CellsAt rd (σ (.n 3) * gen ^ (4 * e))
        [σ (.n (o + 21 * j + 13)), σ (.n (o + 21 * j + 14)), σ (.n (o + 21 * j + 15)),
          σ (.n (o + 21 * j + 16))] ∧
      σ (.n (o + 21 * j + 18)) = baseMd (σ (.n 2)) j ∧
      S.check ![σ (.n (o + 21 * j + 13)), σ (.n (o + 21 * j + 14)), σ (.n (o + 21 * j + 15)),
          σ (.n (o + 21 * j + 16))] (σ (.n (o + 21 * j - 2))) (σ (.n (o + 21 * j - 1)))
        (σ (.n (o + 21 * j + 19))) (σ (.n (o + 21 * j + 20))) (σ (.n (o + 21 * j + 18))) := by
  rw [cBlk, List.forall_mem_append] at h
  obtain ⟨e, hL, hs, hc⟩ := cBlkHead_fwd hm hj
    ((forall_holdsB_noBlake (by simp [cBlkHead, atomNoBlake])).mp h.1)
  have h2 := h.2
  simp only [List.forall_mem_cons, Atom.HoldsB, forall_mem_nil_iff, and_true] at h2
  obtain ⟨c17, a18, hb⟩ := h2
  exact ⟨e, hL, hs, hc, by rw [a18, c17, baseMd, word_md], hb⟩

end Blocks

/-! ## `child_claims_tail__L{k}` -/

/-- **`child_claims_tail__L{k}` under `S`**: `k` blocks read and marked as `ChildReads`, their
rows chained from the state under `baseMd base`. -/
def Meaning_child_claims_tailB (S : BlakeSem) (k : ℕ) (rd : Reader) (args rets : List E) :
    Prop :=
  ∃ s0 s1 base entries cover marks origin limit o0 o1,
    args = [s0, s1, base, entries, cover, marks, origin, limit] ∧ rets = [o0, o1] ∧
    ∃ (off : ℕ → ℕ) (cs : List E), cs.length = 4 * k ∧
      ChildReads rd entries cover marks origin limit off cs k ∧
      ChainSteps S (s0, s1) (blocksOf cs) (baseMd base) k (o0, o1)

section Tail

variable {S : BlakeSem}

/-- `child_claims_tail__L{k}`'s body under `S`, `k ≥ 1`, gives its meaning. -/
theorem child_tail_succB {rd : Reader} (hm : MemOk rd) (k : ℕ) (hk1 : 1 ≤ k) (hk : k < 32)
    (name : String) (args rets : List E)
    (h : Fn.SemB S (coreProgram.RelB S rd) rd
      ⟨name, [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7], cctBody k⟩ args rets) :
    Meaning_child_claims_tailB S k rd args rets := by
  simp only [Fn.SemB, cctBody, holdsListB_atoms, holdsListB_ret, List.forall_mem_append,
    forall_mem_flatMap_range, List.forall_mem_cons, Atom.HoldsB, forall_mem_nil_iff, and_true,
    List.map_cons, List.map_nil] at h
  obtain ⟨σ, hp, ⟨⟨⟨⟨c8, c9⟩, hb0⟩, hblk⟩, c8k, c9k⟩, hr⟩ := h
  -- every block, uniformly
  have hB : ∀ j, ∃ e, j < k → ((∃ L ≤ 2 ^ 33, σ (.n 7) = gen ^ L ∧ e < L) ∧
      LoadHolds rd (σ (.n 4) * (σ (.n 6) * gen ^ e)) 0 (σ (.n 5) * gen ^ j) ∧
      CellsAt rd (σ (.n 3) * gen ^ (4 * e))
        [σ (.n (21 + 21 * j)), σ (.n (21 + 21 * j + 1)), σ (.n (21 + 21 * j + 2)),
          σ (.n (21 + 21 * j + 3))]) ∧
      σ (.n (26 + 21 * j)) = baseMd (σ (.n 2)) j ∧
      S.check ![σ (.n (21 + 21 * j)), σ (.n (21 + 21 * j + 1)), σ (.n (21 + 21 * j + 2)),
          σ (.n (21 + 21 * j + 3))]
        (if j = 0 then σ (.n 8) else σ (.n (6 + 21 * j)))
        (if j = 0 then σ (.n 9) else σ (.n (7 + 21 * j)))
        (σ (.n (27 + 21 * j))) (σ (.n (28 + 21 * j))) (σ (.n (26 + 21 * j))) := by
    intro j
    by_cases hj : j < k
    swap
    · exact ⟨0, fun h => absurd h hj⟩
    refine (?_ : ∃ e, _).imp fun e h _ => h
    rcases j with _ | i
    · obtain ⟨e, hL, hs, hc, hmd, hcc⟩ := cBlk0B_fwd hm hb0
      exact ⟨e, ⟨hL, hs, hc⟩, hmd, hcc⟩
    · obtain ⟨e, hL, hs, hc, hmd, hcc⟩ := cBlkB_fwd (o := 8) (j := i + 1) hm (by omega)
        (hblk i (by omega))
      rw [show 8 + 21 * (i + 1) + 13 = 21 + 21 * (i + 1) by ring,
        show 8 + 21 * (i + 1) + 14 = 21 + 21 * (i + 1) + 1 by ring,
        show 8 + 21 * (i + 1) + 15 = 21 + 21 * (i + 1) + 2 by ring,
        show 8 + 21 * (i + 1) + 16 = 21 + 21 * (i + 1) + 3 by ring] at hc hcc
      rw [show 8 + 21 * (i + 1) + 18 = 26 + 21 * (i + 1) by ring] at hmd hcc
      rw [show 8 + 21 * (i + 1) - 2 = 6 + 21 * (i + 1) by omega,
        show 8 + 21 * (i + 1) - 1 = 7 + 21 * (i + 1) by omega,
        show 8 + 21 * (i + 1) + 19 = 27 + 21 * (i + 1) by ring,
        show 8 + 21 * (i + 1) + 20 = 28 + 21 * (i + 1) by ring] at hcc
      exact ⟨e, ⟨hL, hs, hc⟩, hmd, by simpa using hcc⟩
  choose off hoff using hB
  have hch := chainSteps_of_steps (S := S) (n := k)
    (blocks := fun j => ![σ (.n (21 + 21 * j)), σ (.n (21 + 21 * j + 1)), σ (.n (21 + 21 * j + 2)),
      σ (.n (21 + 21 * j + 3))]) (md := fun j => σ (.n (26 + 21 * j)))
    (st := fun j => (if j = 0 then σ (.n 8) else σ (.n (6 + 21 * j)),
      if j = 0 then σ (.n 9) else σ (.n (7 + 21 * j))))
    (fun j hj => by
      have := (hoff j hj).2.2
      simp only [show j + 1 ≠ 0 by omega, ↓reduceIte]
      rw [show 6 + 21 * (j + 1) = 27 + 21 * j by ring, show 7 + 21 * (j + 1) = 28 + 21 * j by ring]
      exact this)
  simp only [↓reduceIte, show k ≠ 0 by omega] at hch
  set cs := (List.range (4 * k)).map (fun i => σ (.n (21 + 21 * (i / 4) + i % 4))) with hcs
  have hcsg : ∀ j r, j < k → r < 4 → cs.getD (4 * j + r) 0 = σ (.n (21 + 21 * j + r)) := by
    intro j r hj hr
    rw [hcs, List.getD_eq_getElem _ _ (by simp; omega)]
    simp only [List.getElem_map, List.getElem_range]
    congr 2
    omega
  refine ⟨σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7),
    σ (.n (8 + 21 * k)), σ (.n (9 + 21 * k)), hp.symm, hr.symm, off, cs,
    by rw [hcs, List.length_map, List.length_range], ?_, ?_⟩
  · intro j hj
    obtain ⟨⟨hL, hs, hc⟩, -⟩ := hoff j hj
    refine ⟨hL, hs, ?_⟩
    have e0 := hcsg j 0 hj (by omega)
    rw [Nat.add_zero, Nat.add_zero] at e0
    rw [e0, hcsg j 1 hj (by omega), hcsg j 2 hj (by omega), hcsg j 3 hj (by omega)]
    exact hc
  · rw [chainSteps_congr (b' := fun j => ![σ (.n (21 + 21 * j)), σ (.n (21 + 21 * j + 1)),
        σ (.n (21 + 21 * j + 2)), σ (.n (21 + 21 * j + 3))]) (md' := fun j => σ (.n (26 + 21 * j)))
        (fun j hj => ?_) (fun j hj => (hoff j hj).2.1.symm), ← c8, ← c9, c8k, c9k]
    · exact hch
    · have e0 := hcsg j 0 hj (by omega)
      rw [Nat.add_zero, Nat.add_zero] at e0
      simp only [blocksOf, e0, hcsg j 1 hj (by omega), hcsg j 2 hj (by omega),
        hcsg j 3 hj (by omega)]

/-- `child_claims_tail__L0`'s body under `S` gives its meaning. -/
theorem child_tail_zeroB (rd : Reader) (name : String) (args rets : List E)
    (h : Fn.SemB S (coreProgram.RelB S rd) rd
      ⟨name, [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7], cctBody0⟩ args rets) :
    Meaning_child_claims_tailB S 0 rd args rets := by
  simp only [Fn.SemB, cctBody0, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB] at h
  obtain ⟨σ, hp, h8, h9, h10, h11, hr⟩ := h
  refine ⟨σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7),
    σ (.n 10), σ (.n 11), hp.symm, hr.symm, fun _ => 0, [], rfl,
    fun j hj => absurd hj (by omega),
    ⟨fun _ => (σ (.n 0), σ (.n 1)), rfl, ?_, fun j hj => absurd hj (by omega)⟩⟩
  rw [h10, h11, h8, h9]

/-- **`child_claims_tail__L{k}` is sound under any semantics**, `k < 32`. -/
theorem child_claims_tail_B {rd : Reader} (hm : MemOk rd) (k : ℕ) (hk : k < 32)
    (args rets : List E) (h : coreProgram.RelB S rd (cctNames.getD k "") args rets) :
    Meaning_child_claims_tailB S k rd args rets := by
  rw [relB_of_find (find_child_claims_tail k hk)] at h
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · exact child_tail_zeroB rd _ args rets h
  · simp only [show k ≠ 0 by omega, ↓reduceIte] at h
    exact child_tail_succB hm k hk1 hk _ args rets h

end Tail

/-! ## `child_claims_window` -/

/-- **`child_claims_window` under `S`**: `x_q·g = g^N`, `N < 2^16`, `nxt = E(2^11·N)`, and 32
blocks read and marked as `ChildReads`, their rows chained from the state under
`windowMd base nxt`. -/
def Meaning_child_claims_windowB (S : BlakeSem) (rd : Reader) (args rets : List E) : Prop :=
  ∃ s0 s1 base entries cover marks origin limit xq gsq o0 o1 nxt,
    args = [s0, s1, base, entries, cover, marks, origin, limit, xq, gsq] ∧ rets = [o0, o1, nxt] ∧
    ∃ N < 2 ^ 16, xq * gen = gen ^ N ∧ nxt = eOfNat (2 ^ 11 * N) ∧
    ∃ (off : ℕ → ℕ) (cs : List E), cs.length = 128 ∧
      ChildReads rd entries cover marks origin limit off cs 32 ∧
      ChainSteps S (s0, s1) (blocksOf cs) (windowMd base nxt) 32 (o0, o1)

/-- **`child_claims_window` is sound under any semantics.** -/
theorem child_window_B {S : BlakeSem} {rd : Reader} (hm : MemOk rd) {gsq : E}
    (hT : SquaresAt rd gsq) {s0 s1 base entries cover marks origin limit xq : E} {rets : List E}
    (h : coreProgram.RelB S rd "child_claims_window"
      [s0, s1, base, entries, cover, marks, origin, limit, xq, gsq] rets) :
    Meaning_child_claims_windowB S rd [s0, s1, base, entries, cover, marks, origin, limit, xq, gsq]
      rets := by
  rw [relB_of_find find_child_claims_window] at h
  simp only [Fn.SemB, ccwBody, ccwLast, holdsListB_atoms, List.cons_append, List.nil_append,
    Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.forall_mem_append, forall_mem_flatMap_range,
    List.forall_mem_cons, forall_mem_nil_iff, and_true, List.map_cons, List.map_nil] at h
  obtain ⟨σ, hp, c10, m11, hcall, c13, c14, ⟨⟨⟨hb0, hblk⟩, hlh, hlc⟩, c683, c684, c685⟩, hr⟩ := h
  simp only [List.cons.injEq, and_true] at hp
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hp
  obtain ⟨v, hv, N, hN, hN11, hN12⟩ := (scaled_log_11_iffB hT _ _).mp hcall
  simp only [List.cons.injEq, and_true] at hv
  have hlh : ∀ a ∈ cBlkHead 664 31, a.Holds rd σ :=
    (forall_holdsB_noBlake (by simp [cBlkHead, atomNoBlake])).mp hlh
  have hB : ∀ j, ∃ e, j < 32 → ((∃ L ≤ 2 ^ 33, σ (.n 7) = gen ^ L ∧ e < L) ∧
      LoadHolds rd (σ (.n 4) * (σ (.n 6) * gen ^ e)) 0 (σ (.n 5) * gen ^ j) ∧
      CellsAt rd (σ (.n 3) * gen ^ (4 * e))
        [σ (.n (26 + 21 * j)), σ (.n (26 + 21 * j + 1)), σ (.n (26 + 21 * j + 2)),
          σ (.n (26 + 21 * j + 3))]) := by
    intro j
    by_cases hj : j < 32
    swap
    · exact ⟨0, fun h => absurd h hj⟩
    refine (?_ : ∃ e, _).imp fun e h _ => h
    rcases (show j = 0 ∨ (1 ≤ j ∧ j < 31) ∨ j = 31 by omega) with rfl | ⟨h1, h2⟩ | rfl
    · obtain ⟨e, hL, hs, hc, -⟩ := cBlk0B_fwd hm hb0
      exact ⟨e, hL, hs, hc⟩
    · obtain ⟨e, hL, hs, hc, -⟩ := cBlkB_fwd (o := 13) (j := j) hm (by omega)
        (by have := hblk (j - 1) (by omega); rwa [show j - 1 + 1 = j by omega] at this)
      rw [show 13 + 21 * j + 13 = 26 + 21 * j by ring,
        show 13 + 21 * j + 14 = 26 + 21 * j + 1 by ring,
        show 13 + 21 * j + 15 = 26 + 21 * j + 2 by ring,
        show 13 + 21 * j + 16 = 26 + 21 * j + 3 by ring] at hc
      exact ⟨e, hL, hs, hc⟩
    · exact cBlkHead_fwd hm (by omega) hlh
  choose off hoff using hB
  have hmd : ∀ j < 31, σ (.n (31 + 21 * j)) = baseMd (σ (.n 2)) j := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | h1
    · exact (cBlk0B_fwd hm hb0).choose_spec.2.2.2.1
    · have := (cBlkB_fwd (o := 13) (j := j) hm (by omega)
        (by have := hblk (j - 1) (by omega); rwa [show j - 1 + 1 = j by omega] at this)).choose_spec.2.2.2.1
      rwa [show 13 + 21 * j + 18 = 31 + 21 * j by ring] at this
  have hch := chainSteps_of_steps (S := S) (n := 32)
    (blocks := fun j => ![σ (.n (26 + 21 * j)), σ (.n (26 + 21 * j + 1)), σ (.n (26 + 21 * j + 2)),
      σ (.n (26 + 21 * j + 3))]) (md := fun j => if j < 31 then σ (.n (31 + 21 * j)) else σ (.n 12))
    (st := fun j => if j = 0 then (σ (.n 13), σ (.n 14)) else if j = 32 then (σ (.n 681), σ (.n 682))
      else (σ (.n (11 + 21 * j)), σ (.n (12 + 21 * j))))
    (fun j hj => by
      rcases (show j = 0 ∨ (1 ≤ j ∧ j < 31) ∨ j = 31 by omega) with rfl | ⟨h1, h2⟩ | rfl
      · exact (cBlk0B_fwd hm hb0).choose_spec.2.2.2.2
      · have := (cBlkB_fwd (o := 13) (j := j) hm (by omega)
          (by have := hblk (j - 1) (by omega); rwa [show j - 1 + 1 = j by omega] at this)).choose_spec.2.2.2.2
        simp only [show j ≠ 0 by omega, show j ≠ 32 by omega, show j + 1 ≠ 0 by omega,
          show j + 1 ≠ 32 by omega, h2, ↓reduceIte]
        rw [show 13 + 21 * j + 13 = 26 + 21 * j by ring,
          show 13 + 21 * j + 14 = 26 + 21 * j + 1 by ring,
          show 13 + 21 * j + 15 = 26 + 21 * j + 2 by ring,
          show 13 + 21 * j + 16 = 26 + 21 * j + 3 by ring,
          show 13 + 21 * j - 2 = 11 + 21 * j by omega, show 13 + 21 * j - 1 = 12 + 21 * j by omega,
          show 13 + 21 * j + 19 = 11 + 21 * (j + 1) by ring,
          show 13 + 21 * j + 20 = 12 + 21 * (j + 1) by ring,
          show 13 + 21 * j + 18 = 31 + 21 * j by ring] at this
        exact this
      · simpa using hlc)
  simp only [↓reduceIte] at hch
  set cs := (List.range (4 * 32)).map (fun i => σ (.n (26 + 21 * (i / 4) + i % 4))) with hcs
  have hcsg : ∀ j r, j < 32 → r < 4 → cs.getD (4 * j + r) 0 = σ (.n (26 + 21 * j + r)) := by
    intro j r hj hr
    rw [hcs, List.getD_eq_getElem _ _ (by simp; omega)]
    simp only [List.getElem_map, List.getElem_range]
    congr 2
    omega
  refine ⟨_, _, _, _, _, _, _, _, _, _, σ (.n 683), σ (.n 684), σ (.n 685), rfl, hr.symm, N, hN,
    by rw [← hN11, m11, c10, word_gen], by rw [c685, hv, hN12], off, cs,
    by rw [hcs, List.length_map, List.length_range], ?_, ?_⟩
  · intro j hj
    obtain ⟨hL, hs, hc⟩ := hoff j hj
    refine ⟨hL, hs, ?_⟩
    have e0 := hcsg j 0 hj (by omega)
    rw [Nat.add_zero, Nat.add_zero] at e0
    rw [e0, hcsg j 1 hj (by omega), hcsg j 2 hj (by omega), hcsg j 3 hj (by omega)]
    exact hc
  · rw [chainSteps_congr (b' := fun j => ![σ (.n (26 + 21 * j)), σ (.n (26 + 21 * j + 1)),
        σ (.n (26 + 21 * j + 2)), σ (.n (26 + 21 * j + 3))])
        (md' := fun j => if j < 31 then σ (.n (31 + 21 * j)) else σ (.n 12))
        (fun j hj => ?_) (fun j hj => ?_), ← c13, ← c14, c683, c684]
    · exact hch
    · have e0 := hcsg j 0 hj (by omega)
      rw [Nat.add_zero, Nat.add_zero] at e0
      simp only [blocksOf, e0, hcsg j 1 hj (by omega), hcsg j 2 hj (by omega),
        hcsg j 3 hj (by omega)]
    · unfold windowMd
      split_ifs with h1
      · exact (hmd j h1).symm
      · rw [c685]

/-! ## `__loop87` -/

theorem l87_stepB {S : BlakeSem} (rd : Reader) (W c base entries cover origin limit gsq : E)
    (C : CallRel) (x : E)
    (h : ∃ fn, coreProgram.find? "__loop87" = some fn ∧
      fn.SemB S C rd (x :: [W, c, base, entries, cover, origin, limit, gsq]) []) :
    L87Step rd c base entries cover origin limit gsq C x ∧ IsInK (x * gen + W) ∧
      (x * gen + W ≠ 0 →
        C "__loop87" (x * gen :: [W, c, base, entries, cover, origin, limit, gsq]) []) := by
  obtain ⟨fn, hfn, h⟩ := h
  rw [find_loop87, Option.some.injEq] at hfn
  subst hfn
  simp only [Fn.SemB, l87Body, List.cons_append, List.nil_append, Stmt.HoldsListB,
    Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, L87Step, cellsAt_three,
    ← word_gen] at h ⊢
  obtain ⟨σ, hp, m9, m10, m11, m12, m13, m14, m15, m16, m17, l18, l19, l20, hcall, c24, m25, m26,
    m27, m28, l21, l22, l23, c29, m30, a31, c32, m33, hk, hnext, -⟩ := h
  simp only [List.cons.injEq, and_true] at hp
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hp
  rw [m11, m10, m9] at l18 l19 l20
  rw [m28, m27, m26, m25, c24] at l21 l22 l23
  rw [m17, m16, m15, m14, m13, m12] at hcall
  rw [a31, m30, c29] at hk hnext
  rw [m33, c32] at hnext
  exact ⟨⟨_, _, _, _, _, _, ⟨l18, l19, l20⟩, hcall, ⟨l21, l22, l23⟩⟩, hk, hnext⟩

/-- The loop's iterations under `S`, from the entry `callIf`: `w` of them, at `g^j`, `j < w`. -/
theorem loop87_itersB {S : BlakeSem} {rd : Reader} {W c base entries cover origin limit gsq : E}
    {w : ℕ} (hW : W = gen ^ w) (hw : w < 2 ^ 33)
    (h : coreProgram.RelB S rd "__loop87"
      [gen ^ 0, W, c, base, entries, cover, origin, limit, gsq] []) :
    ∀ j < w, L87Step rd c base entries cover origin limit gsq (coreProgram.RelB S rd) (gen ^ j) := by
  intro j hj
  obtain ⟨m, hm0, hmN, hfirst, hall⟩ :=
    loopB_fwd (l87Step_mono rd c base entries cover origin limit gsq)
      (l87_stepB rd W c base entries cover origin limit gsq) 0 h
  have hmw : m = w := by
    rcases Nat.lt_or_ge w m with hlt | hge
    · exact absurd hW.symm (hfirst w (by omega) hlt)
    · exact gen_pow_inj' (by omega) hw (hmN.symm.trans hW)
  exact hall j (by omega) (by omega)

/-! ## `child_claim_list_digest` -/

/-- **The child's windows, forward, under a model**: with the indices `off` of the windows'
reads, `w` loop iterations establish a prefix in each slot of the scratch table, the canonicity
and the reads of the first `32w` blocks of the table's cells. -/
theorem cwins_fwdM {M : HashModel} {rd : Reader} {c base entries cover origin limit : E}
    {len w : ℕ} {off : ℕ → ℕ} (hw : 128 * w ≤ len)
    (h0 : CellsAt rd c [(digestScalars paramIv).1, (digestScalars paramIv).2, 0])
    (hW : ∀ q < w, ∃ s0 s1 bs o0 o1 nxt csq, CellsAt rd (c * gen ^ (4 * q)) [s0, s1, bs] ∧
      CellsAt rd (c * gen ^ (4 * (q + 1))) [o0, o1, nxt] ∧ csq.length = 128 ∧
      ChildReads rd entries cover (base * gen ^ (32 * q)) origin limit (fun j => off (32 * q + j))
        csq 32 ∧
      ChainSteps M.sem (s0, s1) (blocksOf csq) (windowMd bs nxt) 32 (o0, o1) ∧
      nxt = eOfNat (2 ^ 11 * (q + 1))) :
    ∀ q ≤ w, (∃ st : E × E, M.Prefix (prefixBlocks (csOf rd entries off len) (32 * q)) st ∧
        CellsAt rd (c * gen ^ (4 * q)) [st.1, st.2, eOfNat (2 ^ 11 * q)]) ∧
      (∀ j < 32 * q, ∀ r, IsCanonical128 (blocksOf (csOf rd entries off len) j r)) ∧
      ChildReads rd entries cover base origin limit off (csOf rd entries off len) (32 * q) := by
  intro q hq
  induction q with
  | zero =>
    refine ⟨⟨ivCells, M.prefix_nil, ?_⟩, fun j hj => absurd hj (by omega),
      fun j hj => absurd hj (by omega)⟩
    show CellsAt rd (c * gen ^ (4 * 0)) [(digestScalars paramIv).1, (digestScalars paramIv).2,
      eOfNat (2 ^ 11 * 0)]
    simpa [eOfNat_zero] using h0
  | succ q ih =>
    obtain ⟨⟨st, hpre, hI⟩, hcan, hR⟩ := ih (by omega)
    obtain ⟨s0, s1, bs, o0, o1, nxt, csq, hslot, hstore, hlen, hRq, hch, hnxt⟩ := hW q (by omega)
    rw [cellsAt_three] at hslot hI
    have e0 := loadHolds_unique hslot.1 hI.1
    have e1 := loadHolds_unique hslot.2.1 hI.2.1
    have e2 := loadHolds_unique hslot.2.2 hI.2.2
    subst e2
    have hb : ∀ j < 32, blocksOf csq j = blocksOf (csOf rd entries off len) (32 * q + j) := by
      intro j hj
      obtain ⟨-, -, hc⟩ := hRq j hj
      obtain ⟨a0, a1, a2, a3⟩ := block_of_entry hc
      rw [blocksOf_csOf (by omega), blocksOf_getD, a0, a1, a2, a3]
    have hst : (s0, s1) = st := by rw [e0, e1]
    rw [hst] at hch
    obtain ⟨hcan', hpre'⟩ := chainSteps_prefix (k := 32 * q) hpre hb
      (fun j hj => by rw [hnxt]; exact windowMd_eq q j hj) hch
    refine ⟨⟨(o0, o1), by rw [show 32 * (q + 1) = 32 * q + 32 by ring]; exact hpre', ?_⟩,
      fun j hj => ?_, fun i hi => ?_⟩
    · rw [← hnxt]
      exact hstore
    · rcases Nat.lt_or_ge j (32 * q) with h | h
      · exact hcan j h
      · have := hcan' (j - 32 * q) (by omega)
        rwa [show 32 * q + (j - 32 * q) = j by omega] at this
    · rcases Nat.lt_or_ge i (32 * q) with h | h
      · exact hR i h
      · obtain ⟨hL, hs, hc⟩ := hRq (i - 32 * q) (by omega)
        dsimp only at hL hs hc
        rw [show 32 * q + (i - 32 * q) = i by omega] at hL hs hc
        rw [mul_assoc, ← pow_add, show 32 * q + (i - 32 * q) = i by omega] at hs
        refine ⟨hL, hs, ?_⟩
        have hc' := entry_of_reads hc
        have e0 : (csOf rd entries off len).getD (4 * i) 0 = cellAt rd entries (4 * off i) := by
          simpa using csOf_getD (j := i) (r := 0) (off := off) (rd := rd) (entries := entries)
            (by omega) (by omega)
        rw [e0, csOf_getD (by omega) (by omega), csOf_getD (by omega) (by omega),
          csOf_getD (by omega) (by omega)]
        exact hc'

/-- **`child_claim_list_digest` over a hash model**: `n_g = g^n`, `n < 2^16`, and the digest is
the answered hash of `n` canonical claims, claim `i` read at the table index `off i` below
`log limit` and marking its slot with `base·g^i` (`ChildReads … base … n`). -/
def Meaning_child_claim_list_digestWith (M : HashModel) (rd : Reader) (args rets : List E) :
    Prop :=
  ∃ entries cover base origin limit n_g gsq d0 d1,
    args = [entries, cover, base, origin, limit, n_g, gsq] ∧ rets = [d0, d1] ∧
    ∃ n < 2 ^ 16, n_g = gen ^ n ∧ ∃ (off : ℕ → ℕ) (cs : List E), cs.length = 4 * n ∧
      ChildReads rd entries cover base origin limit off cs n ∧ (∀ c ∈ cs, IsCanonical128 c) ∧
      ∃ d, M.H (cs.flatMap cellBytes) = some d ∧ (d0, d1) = digestScalars d

/-- The deployed meaning, its scratch table dropped, is the meaning at the deployed model. -/
theorem meaning_child_claim_list_digestWith_of_deployed {rd : Reader} {args rets : List E}
    (h : Meaning_child_claim_list_digest rd args rets) :
    Meaning_child_claim_list_digestWith HashModel.deployed rd args rets := by
  obtain ⟨a, b, c, d, e, f, g, d0, d1, ha, hr, n, hn, hng, off, cs, hlen, hR, hcan, hd, -⟩ := h
  exact ⟨a, b, c, d, e, f, g, d0, d1, ha, hr, n, hn, hng, off, cs, hlen, hR, hcan, _, rfl, hd⟩

/-- **`child_claim_list_digest` is sound under a hash model** (G:2844-2885): its relation under
the model's semantics gives the answered hash of the child's claims. -/
theorem child_claim_list_digest_model {M : HashModel} {rd : Reader} (hm : MemOk rd) {gsq : E}
    (hT : SquaresAt rd gsq) {entries cover base origin limit n_g : E} {rets : List E}
    (h : coreProgram.RelB M.sem rd "child_claim_list_digest"
      [entries, cover, base, origin, limit, n_g, gsq] rets) :
    Meaning_child_claim_list_digestWith M rd [entries, cover, base, origin, limit, n_g, gsq]
      rets := by
  rw [relB_of_find find_child_claim_list_digest] at h
  simp only [Fn.SemB, ccldBody, List.cons_append, List.nil_append, Stmt.HoldsListB,
    Stmt.HoldsB, Atom.HoldsB, true_and, List.map_cons, List.map_nil] at h
  obtain ⟨σ, hp, c7, a8, hk8, hz, hnz⟩ := h
  simp only [List.cons.injEq, and_true] at hp
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hp
  by_cases h8 : σ (.n 8) = 0
  · obtain ⟨c9, c10, c11, c12, c13, c14, c15, hc, h82, h83, hr⟩ := hz h8
    have h1 : σ (.n 5) = 1 := by
      rw [a8, c7, word_one] at h8; exact e_add_eq_zero_iff.mp h8
    rw [c9, c10, c11, c12, c13, c14, c15, word_zero, iv0_word, iv1_word, md_final_word] at hc
    obtain ⟨d, hd, hout⟩ := HashModel.empty (M := M) hc
    refine ⟨_, _, _, _, _, _, _, σ (.n 82), σ (.n 83), rfl, hr.symm, 0, by norm_num,
      by rw [h1, pow_zero], fun _ => 0, [], rfl, fun j hj => absurd hj (by omega), by simp, d,
      by simpa using hd, ?_⟩
    rw [h82, h83]
    exact hout
  obtain ⟨c20, rc19, c24, rc18, m28, m29, m30, m31, m32, m33, c34, m35, ae, c36, m37, m38, m39,
    c41, l41, c42, l42, c43, l43, c44, a45, c46, hk45, hloop, m47, m48, m49, m50, m51, m52, m53,
    m54, m55, l56, l57, l58, ⟨t, ht, h19, htail⟩, c62, m63, rc61, c67, m68, m69, m70, m71, lmark,
    m72, m73, m74, hsl, c76, a77, l78, l79, l80, l81, hfin, h82, h83, hr⟩ := hnz h8
  -- the counts
  obtain ⟨w, e', hw32, he', h18, h25, h24⟩ := rangeCheck_sound hm rc18
  rw [c24, word_g2047] at h24
  have hw : w < 2048 := by have := gen_pow_inj' (by norm_num) (by omega) h24; omega
  have ht32 : t < 32 := by simpa [cctNames] using ht
  have h19' : σ (.n 19) = gen ^ t := by rw [h19, gen_pow_eq_ofK]
  have h32 : σ (.n 32) = gen ^ (32 * w) := by
    rw [m32, m31, m30, m29, m28, h18]; ring
  set n := 32 * w + t + 1 with hn
  have hng : σ (.n 5) = gen ^ n := by
    have e1 := e_add_eq_zero_iff.mp ae
    rw [m33, m35, c34, h32, h19'] at e1
    have : σ (.n 5) = σ (.n 5) * (word 9223372036854775821 0 0 * gen) := by
      rw [ginv_mul_gen, mul_one]
    rw [this, ← mul_assoc, ← e1, ← pow_add, ← pow_succ]
  obtain ⟨v, hv, N, hN, hN1, hN75⟩ := (scaled_log_6_iffB hT _ _).mp hsl
  simp only [List.cons.injEq, and_true] at hv
  have hNn : N = n := gen_pow_inj' (lt_trans hN (by norm_num)) (by omega) (hN1.symm.trans hng)
  subst hNn
  -- the windows
  have h0c : CellsAt rd (σ (.n 40)) [(digestScalars paramIv).1, (digestScalars paramIv).2, 0] := by
    rw [cellsAt_three, ← iv0_word, ← iv1_word, ← word_zero, ← c41, ← c42, ← c43]
    exact ⟨l41, l42, l43⟩
  have hsteps : ∀ j < w, L87Step rd (σ (.n 40)) (σ (.n 2)) (σ (.n 0)) (σ (.n 1)) (σ (.n 3))
      (σ (.n 4)) (σ (.n 6)) (coreProgram.RelB M.sem rd) (gen ^ j) := by
    intro j hj
    have hne : σ (.n 45) ≠ 0 := by
      rw [a45, c44, word_one, h18]
      intro h
      have := (gen_pow_eq_one_iff (by omega)).mp (e_add_eq_zero_iff.mp h).symm
      omega
    have hl := hloop hne
    rw [c46, word_one, ← pow_zero gen] at hl
    exact loop87_itersB h18 (by omega) hl j hj
  have hW : ∀ q, ∃ offq : ℕ → ℕ, q < w → ∃ s0 s1 bs o0 o1 nxt csq,
      CellsAt rd (σ (.n 40) * gen ^ (4 * q)) [s0, s1, bs] ∧
      CellsAt rd (σ (.n 40) * gen ^ (4 * (q + 1))) [o0, o1, nxt] ∧ csq.length = 128 ∧
      ChildReads rd (σ (.n 0)) (σ (.n 1)) (σ (.n 2) * gen ^ (32 * q)) (σ (.n 3)) (σ (.n 4)) offq
        csq 32 ∧
      ChainSteps M.sem (s0, s1) (blocksOf csq) (windowMd bs nxt) 32 (o0, o1) ∧
      nxt = eOfNat (2 ^ 11 * (q + 1)) := by
    intro q
    by_cases hq : q < w
    swap
    · exact ⟨fun _ => 0, fun h => absurd h hq⟩
    obtain ⟨s0, s1, bs, o0, o1, nxt, hslot, hwin, hstore⟩ := hsteps q hq
    obtain ⟨_, _, _, _, _, _, _, _, _, _, o0', o1', nxt', hargs, hrets, N', hN', hxq, hnxt, offq,
      csq, hlen, hRq, hch⟩ := child_window_B hm hT hwin
    simp only [List.cons.injEq, and_true] at hargs hrets
    obtain ⟨rfl, rfl, rfl, rfl, rfl, hmk, rfl, rfl, rfl, rfl⟩ := hargs
    obtain ⟨rfl, rfl, rfl⟩ := hrets
    rw [← pow_succ] at hxq
    have hNq : N' = q + 1 := (gen_pow_inj' (by omega) (lt_trans hN' (by norm_num)) hxq).symm
    subst hNq
    subst hmk
    simp only [pow32_eq] at hRq
    rw [pow4_eq _ q rfl] at hslot
    rw [← pow_succ, pow4_eq _ (q + 1) rfl] at hstore
    exact ⟨offq, fun _ => ⟨_, _, _, _, _, _, csq, hslot, hstore, hlen, hRq, hch, hnxt⟩⟩
  choose offW hW using hW
  -- the tail
  rw [← List.getD_eq_getElem _ "" ht] at htail
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hargs, hrets, offT, cst, hlent, hRt, hcht⟩ :=
    child_claims_tail_B hm t ht32 _ _ htail
  simp only [List.cons.injEq, and_true] at hargs hrets
  obtain ⟨rfl, rfl, rfl, rfl, rfl, hmk, rfl, rfl⟩ := hargs
  obtain ⟨rfl, rfl⟩ := hrets
  rw [m55, m54, m53, m52, m51, m50, h18] at hmk
  have hmk' : σ (.n 2) * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w) *
      (gen ^ w * gen ^ w * (gen ^ w * gen ^ w)) * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w) *
      (gen ^ w * gen ^ w * (gen ^ w * gen ^ w))) * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w) *
      (gen ^ w * gen ^ w * (gen ^ w * gen ^ w)) * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w) *
      (gen ^ w * gen ^ w * (gen ^ w * gen ^ w))))) = σ (.n 2) * gen ^ (32 * w) := by ring
  rw [hmk'] at hmk
  rw [← hmk] at hRt
  -- the last claim
  rw [m63, c62] at rc61
  obtain ⟨eL, hx61, hLl⟩ := limit_of_rc hm rc61
  rw [m71, m70, hx61] at lmark
  rw [m69, m68, c67, hng,
    show gen ^ n * word 9223372036854775821 0 0 = gen ^ (n - 1) by
      rw [show gen ^ n = gen ^ (n - 1) * gen by rw [← pow_succ]; congr 1, mul_assoc,
        mul_comm gen, ginv_mul_gen, mul_one]] at lmark
  rw [m74, m73, m72, pow4_eq _ eL hx61] at l78 l79 l80 l81
  -- the indices and the cells
  set off : ℕ → ℕ := fun i => if i < 32 * w then offW (i / 32) (i % 32) else
    if i < 32 * w + t then offT (i - 32 * w) else eL with hoffdef
  set cs := csOf rd (σ (.n 0)) off (4 * n) with hcs
  have hwin := cwins_fwdM (M := M) (c := σ (.n 40)) (base := σ (.n 2)) (entries := σ (.n 0))
    (cover := σ (.n 1)) (origin := σ (.n 3)) (limit := σ (.n 4)) (len := 4 * n) (w := w)
    (off := off) (by omega) h0c
    (fun q hq => by
      obtain ⟨s0, s1, bs, o0, o1, nxt, csq, a, b, c, d, e, f⟩ := hW q hq
      refine ⟨s0, s1, bs, o0, o1, nxt, csq, a, b, c, ?_, e, f⟩
      refine (childReads_congr fun j hj => ?_).mp d
      simp only [hoffdef, show 32 * q + j < 32 * w by omega, ↓reduceIte,
        show (32 * q + j) / 32 = q by omega, show (32 * q + j) % 32 = j by omega])
  obtain ⟨⟨st, hpre, hIw⟩, hcanw, hRw⟩ := hwin w le_rfl
  have h49 : σ (.n 49) = σ (.n 40) * gen ^ (4 * w) := by rw [m49, m48, m47, pow4_eq _ w h18]
  rw [h49] at l56 l57 l58
  rw [cellsAt_three] at hIw
  have e56 := loadHolds_unique l56 hIw.1
  have e57 := loadHolds_unique l57 hIw.2.1
  have e58 := loadHolds_unique l58 hIw.2.2
  have hoT : ∀ j < t, off (32 * w + j) = offT j := fun j hj => by
    simp only [hoffdef, show ¬(32 * w + j < 32 * w) by omega,
      show 32 * w + j < 32 * w + t by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  have hoL : off (n - 1) = eL := by
    simp only [hoffdef, show ¬(n - 1 < 32 * w) by omega, show ¬(n - 1 < 32 * w + t) by omega,
      ↓reduceIte]
  have hbt : ∀ j < t, blocksOf cst j = blocksOf cs (32 * w + j) := by
    intro j hj
    obtain ⟨-, -, hc⟩ := hRt j hj
    obtain ⟨a0, a1, a2, a3⟩ := block_of_entry hc
    rw [blocksOf_csOf (by omega), blocksOf_getD, a0, a1, a2, a3, hoT j hj]
  rw [e56, e57, e58] at hcht
  obtain ⟨hcant, hpret⟩ := chainSteps_prefix (k := 32 * w) hpre hbt
    (fun j hj => baseMd_eq w j (by omega)) hcht
  rw [show 32 * w + t = n - 1 by omega] at hpret
  have hlast : blocksOf cs (n - 1) = ![σ (.n 78), σ (.n 79), σ (.n 80), σ (.n 81)] := by
    obtain ⟨a0, a1, a2, a3⟩ := block_of_entry (cellsAt_four.mpr ⟨l78, l79, l80, l81⟩)
    rw [blocksOf_csOf (by omega), hoL, a0, a1, a2, a3]
  have h77 : σ (.n 77) = metadataCell (64 * n) true := by
    rw [a77, c76, hv, hN75, md_final_word, eOfNat_add_metadataCell, Nat.xor_zero]; rfl
  rw [← hlast, h77] at hfin
  have hcanl := (M.canonical hfin).1
  have hcan : ∀ j < n, ∀ r, IsCanonical128 (blocksOf cs j r) := by
    intro j hj
    rcases (show j < 32 * w ∨ 32 * w ≤ j ∧ j < 32 * w + t ∨ j = n - 1 by omega) with
      h | ⟨h1, h2⟩ | rfl
    · exact hcanw j h
    · have := hcant (j - 32 * w) (by omega)
      rwa [show 32 * w + (j - 32 * w) = j by omega] at this
    · exact hcanl
  have hlen : cs.length = 4 * n := length_csOf _ _ _ _
  obtain ⟨d, hd, hout⟩ := final_model (st := (σ (.n 59), σ (.n 60))) hlen (by omega) hpret hfin
  refine ⟨_, _, _, _, _, _, _, σ (.n 82), σ (.n 83), rfl, hr.symm, n, hN, hng, off, cs, hlen, ?_,
    canonical_of_blocks hlen hcan, d, hd, by rw [h82, h83]; exact hout⟩
  intro i hi
  rcases (show i < 32 * w ∨ 32 * w ≤ i ∧ i < 32 * w + t ∨ i = n - 1 by omega) with
    h | ⟨h1, h2⟩ | rfl
  · exact hRw i h
  · obtain ⟨hL, hs, hc⟩ := hRt (i - 32 * w) (by omega)
    rw [← hoT _ (by omega), show 32 * w + (i - 32 * w) = i by omega] at hL hs hc
    rw [mul_assoc, ← pow_add, show 32 * w + (i - 32 * w) = i by omega] at hs
    refine ⟨hL, hs, ?_⟩
    have hc' := entry_of_reads hc
    have e0 : cs.getD (4 * i) 0 = cellAt rd (σ (.n 0)) (4 * off i) := by
      simpa using csOf_getD (j := i) (r := 0) (off := off) (rd := rd) (entries := σ (.n 0))
        (by omega) (by omega)
    rw [e0, csOf_getD (by omega) (by omega), csOf_getD (by omega) (by omega),
      csOf_getD (by omega) (by omega)]
    exact hc'
  · refine ⟨by rw [hoL]; exact hLl, by rw [hoL]; exact lmark, ?_⟩
    have hc' := entry_of_reads (cellsAt_four.mpr ⟨l78, l79, l80, l81⟩)
    have e0 : cs.getD (4 * (n - 1)) 0 = cellAt rd (σ (.n 0)) (4 * off (n - 1)) := by
      simpa using csOf_getD (j := n - 1) (r := 0) (off := off) (rd := rd) (entries := σ (.n 0))
        (by omega) (by omega)
    rw [e0, csOf_getD (by omega) (by omega), csOf_getD (by omega) (by omega),
      csOf_getD (by omega) (by omega), hoL]
    exact hc'

end
end LeanVM.Guest.B1.Digest
