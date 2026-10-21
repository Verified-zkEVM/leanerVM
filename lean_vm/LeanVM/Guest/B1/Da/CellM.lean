/-
  LeanVM.Guest.B1.Da.CellM

  `da_verify_cell` under a hash model: the answered hash of the cell's symbols.
-/

module

public import LeanVM.Guest.B1.Da.Cell
public import LeanVM.Guest.B1.Digest.CommonM

/-!
# `da_verify_cell` over a hash model

`da_verify_cell` hashes its 128 packed cells as one chain of 32 blocks from the IV (`Cell.lean`).
Under a `HashModel` the chain is `HashModel.chain_blocks`: the model answers the hash of the
symbols' bytes (`Ans M (syms.flatMap kBytes) (d0, d1)`, `da_verify_cell_model`); the inner product
and the reads are hash-free and as deployed.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- **`da_verify_cell(lvals)` over a hash model**: 256 symbols, the 256 words at `lvals`, the
answered hash of the symbols' bytes and the inner product `∑ lvals[k]·sym[k]`. -/
def Meaning_da_verify_cellWith (M : HashModel) (rd : Reader) (args rets : List E) : Prop :=
  ∃ lv d0 d1 s, args = [lv] ∧ rets = [d0, d1, s] ∧ ∃ (syms : List K) (ws : List E),
    syms.length = 256 ∧ ws.length = 256 ∧ CellsAt rd lv ws ∧
    Ans M (syms.flatMap kBytes) (d0, d1) ∧
    s = ∑ k ∈ Finset.range 256, ws.getD k 0 * ofK (syms.getD k 0)

/-- The facts of block `b` of `da_verify_cell`'s chain under `S`. -/
theorem vcBlkB_fwd {S : BlakeSem} {rd : Reader} {σ : Val} {b : ℕ}
    (h : ∀ a ∈ vcBlk b, a.HoldsB S rd σ) :
    σ (.n (1410 + 3 * b)) = word (64 * (b + 1)) (if b + 1 = 32 then 4294967295 else 0) 0 ∧
      S.check ![σ (.n (vcP (4 * b))), σ (.n (vcP (4 * b + 1))), σ (.n (vcP (4 * b + 2))),
        σ (.n (vcP (4 * b + 3)))] (σ (.n (1408 + 3 * b))) (σ (.n (1409 + 3 * b)))
        (σ (.n (1411 + 3 * b))) (σ (.n (1412 + 3 * b))) (σ (.n (1410 + 3 * b))) := by
  simpa only [vcBlk, List.forall_mem_cons, Atom.HoldsB, forall_mem_nil_iff, and_true] using h

/-- **`da_verify_cell`'s outcome over a model, its symbols named** `syms` (`CellOut`). -/
def CellOutM (M : HashModel) (rd : Reader) (args rets : List E) (syms : List K) : Prop :=
  ∃ lv d0 d1 s, args = [lv] ∧ rets = [d0, d1, s] ∧ syms.length = 256 ∧ ∃ ws : List E,
    ws.length = 256 ∧ CellsAt rd lv ws ∧ Ans M (syms.flatMap kBytes) (d0, d1) ∧
    s = ∑ k ∈ Finset.range 256, ws.getD k 0 * ofK (syms.getD k 0)

/-- The outcome with its symbols named gives the meaning. -/
theorem meaning_of_cellOutM {M : HashModel} {rd : Reader} {args rets : List E} {syms : List K}
    (h : CellOutM M rd args rets syms) : Meaning_da_verify_cellWith M rd args rets := by
  obtain ⟨lv, d0, d1, s, ha, hr, hl, ws, hw, hc, hd, hs⟩ := h
  exact ⟨lv, d0, d1, s, ha, hr, syms, ws, hl, hw, hc, hd, hs⟩

/-- **`da_verify_cell` on a valuation of its body, under a model, its witness named**: the
outcome holds of the symbols the valuation hints (`vcSyms`). -/
theorem da_verify_cell_outM {M : HashModel} {C : CallRel} {rd : Reader} {σ : Val}
    {args rets : List E} (hp : ([.n 0] : List V).map σ = args)
    (hb : Stmt.HoldsListB M.sem C rd σ vcBody False (fun rs => rs = rets)) :
    CellOutM M rd args rets (vcSyms σ) := by
  simp only [vcBody, holdsListB_atoms, holdsListB_ret, List.forall_mem_append,
    forall_mem_flatMap_range, List.forall_mem_cons, Atom.HoldsB, forall_mem_nil_iff, and_true,
    true_and, List.map_cons, List.map_nil] at hb hp
  obtain ⟨⟨⟨⟨⟨hP0, hPs⟩, h1408, h1409⟩, hblk⟩, h1506, h1507, h1508⟩, hr⟩ := hb
  have hP0 : ∀ a ∈ vcPair0, a.Holds rd σ :=
    (forall_holdsB_noBlake (by simp [vcPair0, atomNoBlake])).mp hP0
  have hPs : ∀ i < 127, ∀ a ∈ vcPair (i + 1), a.Holds rd σ := fun i hi =>
    (forall_holdsB_noBlake (by simp [vcPair, atomNoBlake])).mp (hPs i hi)
  set lv := σ (.n 0) with hlv
  let x : ℕ → E := fun k => σ (.n (k + 1))
  obtain ⟨k0, k1, p0, l0, l1, s0⟩ := vcPair0_fwd hP0
  -- every pair, uniformly
  have hP : ∀ e < 128, IsInK (x (2 * e)) ∧ IsInK (x (2 * e + 1)) ∧
      σ (.n (vcP e)) = x (2 * e) + wY * x (2 * e + 1) ∧
      (∃ v, LoadHolds rd lv (2 * e) v) ∧ (∃ v, LoadHolds rd lv (2 * e + 1) v) := by
    intro e he
    rcases Nat.eq_zero_or_pos e with rfl | hpos
    · exact ⟨k0, k1, p0, ⟨_, l0⟩, ⟨_, l1⟩⟩
    · obtain ⟨i, rfl⟩ : ∃ i, e = i + 1 := ⟨e - 1, by omega⟩
      obtain ⟨a, b, c, d, f, -⟩ := vcPair_fwd (hPs i (by omega))
      have e1 : vcP (i + 1) = 256 + 9 * (i + 1) + 2 := by
        unfold vcP; rw [ite_neg' (by omega)]; omega
      refine ⟨a, b, by rw [e1]; exact c, ⟨_, d⟩, ⟨_, f⟩⟩
  have hL : ∀ k < 256, ∃ v, LoadHolds rd lv k v := by
    intro k hk
    obtain ⟨e, r, hr2, rfl⟩ : ∃ e r, r < 2 ∧ k = 2 * e + r := ⟨k / 2, k % 2, by omega, by omega⟩
    interval_cases r
    · exact (hP e (by omega)).2.2.2.1
    · exact (hP e (by omega)).2.2.2.2
  -- the inner product
  have hS : ∀ e < 128, σ (.n (264 + 9 * e)) =
      ∑ k ∈ Finset.range (2 * e + 2), cellAt rd lv k * x k := by
    intro e he
    induction e with
    | zero =>
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      rw [s0, cellAt_of_load l0, cellAt_of_load l1]
    | succ i ih =>
      obtain ⟨-, -, -, d, f, g⟩ := vcPair_fwd (hPs i (by omega))
      rw [show 264 + 9 * (i + 1) = 256 + 9 * (i + 1) + 8 by omega, g,
        show 255 + 9 * (i + 1) = 264 + 9 * i by omega, ih (by omega),
        show 2 * (i + 1) + 2 = 2 * i + 2 + 1 + 1 by omega, Finset.sum_range_succ _ (2 * i + 2 + 1),
        Finset.sum_range_succ _ (2 * i + 2), ← cellAt_of_load d, ← cellAt_of_load f]
      rfl
  -- the chain
  let sy : ℕ → K := fun k => (x k).limb 0
  have hx : ∀ k < 256, x k = ofK (sy k) := fun k hk => by
    obtain ⟨e, r, hr2, rfl⟩ : ∃ e r, r < 2 ∧ k = 2 * e + r := ⟨k / 2, k % 2, by omega, by omega⟩
    interval_cases r
    · exact eq_ofK_limb (hP e (by omega)).1
    · exact eq_ofK_limb (hP e (by omega)).2.1
  have hcell : ∀ e < 128, σ (.n (vcP e)) = vcCell sy e := fun e he => by
    rw [(hP e he).2.2.1, vc_pack (hP e he).1 (hP e he).2.1]; rfl
  obtain ⟨d, hd, hst⟩ := HashModel.chain_blocks (M := M) (n := 31)
    (blocks := fun b => ![σ (.n (vcP (4 * b))), σ (.n (vcP (4 * b + 1))),
      σ (.n (vcP (4 * b + 2))), σ (.n (vcP (4 * b + 3)))])
    (md := fun b => σ (.n (1410 + 3 * b)))
    (st := fun b => (σ (.n (1408 + 3 * b)), σ (.n (1409 + 3 * b))))
    (by simp only [Nat.mul_zero, Nat.add_zero]; rw [h1408, h1409, iv0_word, iv1_word]; rfl)
    (fun j hj => by
      rw [(vcBlkB_fwd (hblk j (by omega))).1, word_metadata]
      congr 1
      simp only [decide_eq_false_iff_not]
      omega)
    (by rw [(vcBlkB_fwd (hblk 31 (by omega))).1, word_metadata]; rfl)
    (fun j hj => by
      simp only [show 1408 + 3 * (j + 1) = 1411 + 3 * j by omega,
        show 1409 + 3 * (j + 1) = 1412 + 3 * j by omega]
      exact (vcBlkB_fwd (hblk j (by omega))).2)
  have hbytes : (List.range (31 + 1)).flatMap (fun b => blockBytes ![σ (.n (vcP (4 * b))),
      σ (.n (vcP (4 * b + 1))), σ (.n (vcP (4 * b + 2))), σ (.n (vcP (4 * b + 3)))]) =
      ((List.range 256).map sy).flatMap kBytes := by
    rw [← vc_bytes sy]
    refine List.flatMap_congr fun b hb => ?_
    have hb' := List.mem_range.mp hb
    simp only [vcBlocks]
    rw [hcell _ (by omega), hcell _ (by omega), hcell _ (by omega), hcell _ (by omega)]
  rw [hbytes] at hd
  have hsy : vcSyms σ = (List.range 256).map sy := rfl
  rw [hsy]
  refine ⟨lv, σ (.n 1506), σ (.n 1507), σ (.n 1508), hp.symm, hr.symm, by simp,
    (List.range 256).map (cellAt rd lv), by simp, fun k hk => ?_, ⟨d, hd, ?_⟩, ?_⟩
  · simp only [List.length_map, List.length_range] at hk
    simp only [List.getElem_map, List.getElem_range]
    exact load_cellAt (hL k hk).choose_spec
  · rw [h1506, h1507]
    simpa using hst
  · rw [h1508, show 1407 = 264 + 9 * 127 from rfl, hS 127 (by omega)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [List.getD_eq_getElem _ _ (by simpa using hk'),
      List.getD_eq_getElem _ _ (by simpa using hk')]
    simp only [List.getElem_map, List.getElem_range]
    rw [hx k hk']

/-- **`da_verify_cell` is sound under a hash model** (G:2959-2968). -/
theorem da_verify_cell_model {M : HashModel} {rd : Reader} {args rets : List E}
    (h : coreProgram.RelB M.sem rd "da_verify_cell" args rets) :
    Meaning_da_verify_cellWith M rd args rets := by
  rw [relB_of_find find_da_verify_cell] at h
  obtain ⟨σ, hp, hb⟩ := h
  exact meaning_of_cellOutM (da_verify_cell_outM hp hb)

end
end LeanVM.Guest.B1.Digest
