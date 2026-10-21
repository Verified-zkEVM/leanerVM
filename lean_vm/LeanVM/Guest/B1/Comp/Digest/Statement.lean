/-
  LeanVM.Guest.B1.Comp.Digest.Statement

  `statement_digest` over a completeness model: when the model answers the statement's bytes,
  the relation holds under the model's semantics.
-/

module

public import LeanVM.Guest.B1.Comp.Basic
public import LeanVM.Guest.B1.Digest.StatementM

/-!
# `statement_digest` over a completeness model

The backward half of `statement_digest_iff` over a `CompModel`: from the meaning over the model's
answers (`Meaning_statement_digestWith CM.hm`: `CM.H` answers the statement's bytes `stmtBytes`
by `pi`), the 22 blocks check through the model's chain (`CompModel.chain_checks_blocks`), the
cells after block `b` being `chainSt` of the bytes (the IV before the first, `pi`'s after the
last), every other value the deployed honest one (`sdCore`). `statement_digest_comp`; at
`CompModel.deployed` it gives the deployed backward direction (`statement_digest_of_comp`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Node LeanVM.E2E.Complete

@[expose] public section

section
variable (args hdr cells : List E) (S : ℕ → E × E)

/-- The values of `statement_digest` with the chain's cells `S` (`sdVals` at the deployed chain). -/
def sdValsC (k : ℕ) : E :=
  if k < 741 then sdCore args hdr cells k else
  if k < 809 then [(S ((k - 741) / 3)).1, (S ((k - 741) / 3)).2,
    sdMd ((k - 741) / 3)].getD ((k - 741) % 3) 0 else
  [(S 22).1, (S 22).2].getD (k - 809) 0

theorem sdValsC_core {k : ℕ} (hk : k < 741) : sdValsC args hdr cells S k = sdCore args hdr cells k := by
  simp [sdValsC, hk]

theorem sdValsC_bv (b r : ℕ) (hr : r < 3) (hb : 741 + 3 * b + r < 809) :
    sdValsC args hdr cells S (741 + 3 * b + r) =
      [(S b).1, (S b).2, sdMd b].getD r 0 := by
  unfold sdValsC
  rw [ite_neg' (by omega), ite_pos' hb, show (741 + 3 * b + r - 741) / 3 = b by omega,
    show (741 + 3 * b + r - 741) % 3 = r by omega]

end

/-- Block `b` of the chain under any semantics, backward (`sdBlk_bwd`). -/
theorem sdBlkB_bwd {S : BlakeSem} {rd : Reader} {σ : Val} {b : ℕ}
    (h1 : σ (bv b 2) = word (64 * (b + 1)) (if b + 1 = 22 then 4294967295 else 0) 0)
    (h2 : S.check ![σ (.n (cellIdx (4 * b))), σ (.n (cellIdx (4 * b + 1))),
        σ (.n (cellIdx (4 * b + 2))), σ (.n (cellIdx (4 * b + 3)))] (σ (bv b 0)) (σ (bv b 1))
        (σ (bv (b + 1) 0)) (σ (bv (b + 1) 1)) (σ (bv b 2))) :
    ∀ a ∈ sdBlk b, a.HoldsB S rd σ := by
  simpa only [sdBlk, List.forall_mem_cons, Atom.HoldsB, forall_mem_nil_iff, and_true] using
    And.intro h1 h2

/-- **`statement_digest` is complete over a completeness model** (G:2664-2703): when the model
answers the statement's bytes, its relation holds under the model's semantics. -/
theorem statement_digest_comp {CM : CompModel} (rd : Reader) (args rets : List E)
    (hm : Meaning_statement_digestWith CM.hm rd args rets) :
    coreProgram.RelB CM.sem rd "statement_digest" args rets := by
  rw [relB_of_find find_statement_digest]
  simp only [Fn.SemB, sdBody, holdsListB_atoms, holdsListB_ret, List.forall_mem_append,
    forall_mem_flatMap_range, List.forall_mem_cons, Atom.HoldsB, forall_mem_nil_iff, and_true,
    List.map_cons, List.map_nil]
  obtain ⟨seed0, seed1, sigp, da0, da1, dp, d0, d1, rfl, rfl, seed, sig, da, cells, hlen, hseed,
    hs0, hs1, hda, hcells, pi, hpi, hd⟩ := hm
  change cells.length = 53 at hlen
  set args := [seed0, seed1, sigp, da0, da1, dp] with hargs
  set hdr := [seed0, seed1, (digestScalars sig).1, (digestScalars sig).2, da0, da1] with hhdr
  have hDq : ∀ q (hq : q < 53), sdD cells q = cells[q]'(by omega) := by
    intro q hq
    rw [sdD, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left]
  have hD53 : sdD cells 53 = 0 := by
    rw [sdD, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_right (by omega)]
    simp [hlen]
  have hload : ∀ q < 53, LoadHolds rd dp q (sdD cells q) := fun q hq => by
    rw [hDq q hq]; exact hcells q (by omega)
  let c := fun k => sdCore args hdr cells (cellIdx k)
  have cA : ∀ p < 26, c (6 + 3 * p) =
      E.ofLimbs ((sdD cells (2 * p)).limb 0) ((sdD cells (2 * p)).limb 1) 0 := fun p hp => by
    show sdCore args hdr cells (cellIdx (6 + 3 * p)) = _
    rw [cellIdx_A p hp, sdCore_pair args hdr cells p 8 hp (by omega)]
    simp only [pairVals, List.getD_cons_succ, List.getD_cons_zero]
    exact (pair_cells (sdD cells (2 * p)) (sdD cells (2 * p + 1))).1
  have cB : ∀ p < 26, c (6 + 3 * p + 1) =
      E.ofLimbs ((sdD cells (2 * p)).limb 2) ((sdD cells (2 * p + 1)).limb 0) 0 := fun p hp => by
    show sdCore args hdr cells (cellIdx (6 + 3 * p + 1)) = _
    rw [cellIdx_B p hp, sdCore_pair args hdr cells p 17 hp (by omega)]
    simp only [pairVals, List.getD_cons_succ, List.getD_cons_zero]
    exact (pair_cells (sdD cells (2 * p)) (sdD cells (2 * p + 1))).2.1
  have cC : ∀ p < 26, c (6 + 3 * p + 2) =
      E.ofLimbs ((sdD cells (2 * p + 1)).limb 1) ((sdD cells (2 * p + 1)).limb 2) 0 := fun p hp => by
    show sdCore args hdr cells (cellIdx (6 + 3 * p + 2)) = _
    rw [cellIdx_C p hp, sdCore_pair args hdr cells p 26 hp (by omega)]
    simp only [pairVals, List.getD_cons_succ, List.getD_cons_zero]
    exact (pair_cells (sdD cells (2 * p)) (sdD cells (2 * p + 1))).2.2
  have cL : c 84 = E.ofLimbs ((sdD cells 52).limb 0) ((sdD cells 52).limb 1) 0 ∧
      c 85 = E.ofLimbs ((sdD cells 52).limb 2) ((0 : E).limb 0) 0 ∧
      c 86 = E.ofLimbs ((0 : E).limb 1) ((0 : E).limb 2) 0 := by
    refine ⟨?_, ?_, ?_⟩
    · show sdCore args hdr cells (714 + 8) = _
      rw [sdCore_last args hdr cells 8 (by omega)]
      simp only [lastVals, List.getD_cons_succ, List.getD_cons_zero]
      exact (pair_cells (sdD cells 52) 0).1
    · show sdCore args hdr cells (714 + 17) = _
      rw [sdCore_last args hdr cells 17 (by omega)]
      simp only [lastVals, List.getD_cons_succ, List.getD_cons_zero]
      have := (pair_cells (sdD cells 52) 0).2.1
      exact this
    · show sdCore args hdr cells (714 + 25) = _
      rw [sdCore_last args hdr cells 25 (by omega)]
      simp only [lastVals, List.getD_cons_succ, List.getD_cons_zero]
      have := (pair_cells (sdD cells 52) 0).2.2
      rwa [zero_add] at this
  have cH : ∀ k < 6, c k = hdr.getD k 0 := fun k hk => by
    show sdCore args hdr cells (cellIdx k) = _
    rw [cellIdx_hdr k hk]
    simp [sdCore, show ¬(6 + k < 6) by omega, show 6 + k < 12 by omega]
  have c87 : c 87 = 0 := by
    show sdCore args hdr cells 740 = 0
    simp [sdCore]
  have hcs := isCanonical128_digestScalars seed
  have hcg := isCanonical128_digestScalars sig
  have hcd := isCanonical128_digestScalars da
  rw [← hseed] at hcs
  rw [← hda] at hcd
  have hcan : ∀ k < 88, IsCanonical128 (c k) := by
    intro k hk
    rcases (show k < 6 ∨ 6 ≤ k ∧ k < 87 ∨ k = 87 by omega) with h | ⟨h1, h2⟩ | rfl
    · rw [cH k h]
      interval_cases k
      exacts [hcs.1, hcs.2, hcg.1, hcg.2, hcd.1, hcd.2]
    · obtain ⟨p, r, hr3, rfl⟩ : ∃ p r, r < 3 ∧ k = 6 + 3 * p + r :=
        ⟨(k - 6) / 3, (k - 6) % 3, by omega, by omega⟩
      rcases (show p < 26 ∨ p = 26 by omega) with hp | rfl
      · interval_cases r
        · rw [Nat.add_zero, cA p hp]; rfl
        · rw [cB p hp]; rfl
        · rw [cC p hp]; rfl
      · interval_cases r
        · rw [cL.1]; rfl
        · rw [cL.2.1]; rfl
        · rw [cL.2.2]; rfl
    · rw [c87]; exact isCanonical128_zero
  have hpq : ∀ p < 27, cellBytes (c (6 + 3 * p)) ++ cellBytes (c (6 + 3 * p + 1)) ++
      cellBytes (c (6 + 3 * p + 2)) =
        Node.eBytes ((cells ++ [0]).getD (2 * p) 0) ++ Node.eBytes ((cells ++ [0]).getD (2 * p + 1) 0) := by
    intro p hp27
    rcases (show p < 26 ∨ p = 26 by omega) with hp | rfl
    · rw [cA p hp, cB p hp, cC p hp, pair_bytes]; rfl
    · rw [cL.1, cL.2.1, cL.2.2, pair_bytes]
      show _ = Node.eBytes (sdD cells 52) ++ Node.eBytes (sdD cells 53)
      rw [hD53]
  -- the chain: the model's rows of the statement's bytes
  let blocks : ℕ → Fin 4 → E := fun b => ![c (4 * b), c (4 * b + 1), c (4 * b + 2), c (4 * b + 3)]
  have hbytes : (List.range (21 + 1)).flatMap (fun j => blockBytes (blocks j)) =
      stmtBytes seed sig da cells := by
    rw [stmtBytes_eq seed sig da cells hlen]
    exact sd_bytes c seed sig da cells hlen
      (by rw [cH 0 (by omega), cH 1 (by omega), digestBytes_eq, ← hseed]; rfl)
      (by rw [cH 2 (by omega), cH 3 (by omega), digestBytes_eq]; rfl)
      (by rw [cH 4 (by omega), cH 5 (by omega), digestBytes_eq, ← hda]; rfl) hpq c87
  have hH : CM.H ((List.range (21 + 1)).flatMap fun j => blockBytes (blocks j)) = some pi := by
    rw [hbytes]; exact hpi
  have hchk := CM.chain_checks_blocks (md := sdMd) hH
    (fun j hj r => by
      fin_cases r
      · exact hcan _ (by omega)
      · exact hcan _ (by omega)
      · exact hcan _ (by omega)
      · exact hcan _ (by omega))
    (fun j hj => by
      simp only [sdMd]
      congr 1
      simp only [decide_eq_false_iff_not]
      omega)
    (by simp [sdMd])
  set X := (List.range (21 + 1)).flatMap fun j => blockBytes (blocks j) with hX
  let S := CM.chainSt X pi
  have hlenX : X.length = 64 * 22 := by
    rw [hX, List.length_flatMap]
    simp [length_blockBytes]
  have hS0 : S 0 = ivCells := CM.chainSt_zero X pi
  have hS22 : S 22 = (d0, d1) := by
    rw [hd]
    exact CM.chainSt_succ_of pi (n := 21) (by rw [hlenX])
  have h5 : sdValsC args hdr cells S 5 = dp := by simp [sdValsC, sdCore, args]
  refine ⟨fun v => sdValsC args hdr cells S v.idx, rfl,
    ⟨⟨⟨⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun p hp => ?_⟩, ?_⟩, ?_, ?_, ?_⟩, fun b hb => ?_⟩, ?_, ?_⟩, ?_⟩
  · simp [sdValsC, sdCore, args, hdr]
  · simp [sdValsC, sdCore, args, hdr]
  · show LoadHolds rd (sdValsC args hdr cells S 2) 0 (sdValsC args hdr cells S 8)
    simpa [sdValsC, sdCore, args, hdr] using hs0
  · show LoadHolds rd (sdValsC args hdr cells S 2) 1 (sdValsC args hdr cells S 9)
    simpa [sdValsC, sdCore, args, hdr] using hs1
  · simp [sdValsC, sdCore, args, hdr]
  · simp [sdValsC, sdCore, args, hdr]
  · refine (forall_holdsB_noBlake (by simp [sdPair, atomNoBlake])).mpr
      (sdPair_bwd (s := sdD cells (2 * p)) (t := sdD cells (2 * p + 1)) (dp := dp)
        (fun r hr => ?_) h5 (hload _ (by omega)) (hload _ (by omega)))
    show sdValsC args hdr cells S (12 + 27 * p + r) = _
    rw [sdValsC_core args hdr cells S (by omega), sdCore_pair args hdr cells p r hp hr]
  · refine (forall_holdsB_noBlake (by simp [sdLast, atomNoBlake])).mpr
      (sdLast_bwd (s := sdD cells 52) (dp := dp) (fun r hr => ?_) h5 (hload 52 (by omega)))
    show sdValsC args hdr cells S (714 + r) = _
    rw [sdValsC_core args hdr cells S (by omega), sdCore_last args hdr cells r hr]
  · show sdValsC args hdr cells S 740 = _
    rw [sdValsC_core args hdr cells S (by omega), word_zero]
    simp [sdCore]
  · show sdValsC args hdr cells S (741 + 3 * 0 + 0) = _
    rw [sdValsC_bv args hdr cells S 0 0 (by omega) (by omega), iv0_word]
    simp only [List.getD_cons_zero, hS0]
    rfl
  · show sdValsC args hdr cells S (741 + 3 * 0 + 1) = _
    rw [sdValsC_bv args hdr cells S 0 1 (by omega) (by omega), iv1_word]
    simp only [List.getD_cons_succ, List.getD_cons_zero, hS0]
    rfl
  · have hc : ∀ r < 4, sdValsC args hdr cells S (cellIdx (4 * b + r)) = c (4 * b + r) := by
      intro r hr
      rcases cellIdx_lt (4 * b + r) with h | h
      · exact sdValsC_core args hdr cells S h
      · omega
    refine sdBlkB_bwd ?_ ?_
    · show sdValsC args hdr cells S (741 + 3 * b + 2) = _
      rw [sdValsC_bv args hdr cells S b 2 (by omega) (by omega), word_metadata]
      rfl
    · show CM.sem.check ![sdValsC args hdr cells S (cellIdx (4 * b + 0)),
        sdValsC args hdr cells S (cellIdx (4 * b + 1)), sdValsC args hdr cells S (cellIdx (4 * b + 2)),
        sdValsC args hdr cells S (cellIdx (4 * b + 3))] (sdValsC args hdr cells S (741 + 3 * b + 0))
        (sdValsC args hdr cells S (741 + 3 * b + 1)) (sdValsC args hdr cells S (741 + 3 * (b + 1) + 0))
        (sdValsC args hdr cells S (741 + 3 * (b + 1) + 1)) (sdValsC args hdr cells S (741 + 3 * b + 2))
      rw [hc 0 (by omega), hc 1 (by omega), hc 2 (by omega), hc 3 (by omega),
        sdValsC_bv args hdr cells S b 0 (by omega) (by omega),
        sdValsC_bv args hdr cells S b 1 (by omega) (by omega),
        sdValsC_bv args hdr cells S (b + 1) 0 (by omega) (by omega),
        sdValsC_bv args hdr cells S (b + 1) 1 (by omega) (by omega),
        sdValsC_bv args hdr cells S b 2 (by omega) (by omega)]
      exact hchk b (by omega)
  · show sdValsC args hdr cells S 809 = sdValsC args hdr cells S (741 + 3 * 22 + 0)
    rw [sdValsC_bv args hdr cells S 22 0 (by omega) (by omega)]
    simp [sdValsC]
  · show sdValsC args hdr cells S 810 = sdValsC args hdr cells S (741 + 3 * 22 + 1)
    rw [sdValsC_bv args hdr cells S 22 1 (by omega) (by omega)]
    simp [sdValsC]
  · show [sdValsC args hdr cells S 809, sdValsC args hdr cells S 810] = _
    simp [sdValsC, hS22]

/-- The deployed backward direction of `statement_digest_iff`, from the generic one. -/
theorem statement_digest_of_comp (rd : Reader) (args rets : List E)
    (h : Meaning_statement_digest rd args rets) :
    coreProgram.Rel rd "statement_digest" args rets := by
  rw [← relB_deployed]
  exact statement_digest_comp (CM := CompModel.deployed) rd args rets
    ((meaning_statement_digestWith_deployed rd args rets).mpr h)

end
end LeanVM.Guest.B1.Digest
