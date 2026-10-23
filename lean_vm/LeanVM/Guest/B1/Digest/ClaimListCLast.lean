/-
  LeanVM.Guest.B1.Digest.ClaimListCLast

  `claim_list_last__L{k}` and `__loop16`'s block, completely.
-/

module

public import LeanVM.Guest.B1.Digest.ClaimListCChk
public import LeanVM.Guest.B1.Digest.ChainFilter
public import LeanVM.Guest.B1.Digest.PairComplete

/-!
# The last claims and a group of claims, completely

`claimLast_complete`: from a state at `sp` after whole blocks `pre` and `4k` canonical cells at
`blk`, `claim_list_last__L{k}` returns the digest of `pre ++` the cells: its evaluated valuation
(`Fwd.ev`) loads them, every atom holds (`Fwd.atoms_holds`), and soundness (`claimLast_sound`)
names the returns. `l16_block`: `__loop16`'s block at the counter `x` holds when the state after
`pre` is at `chain · x^13`, the 68 cells at `entries · x^68`, and the state after them at offset
`13` (its stores, `chain_whole` on the block without them, `check_filter`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

variable {rd : Reader}

theorem clc_all {k : ℕ} (hk : k < 17) : clcOk k (coreProgram.getD (324 + k) default) = true := by
  rcases Nat.lt_or_ge k 9 with h | h
  · exact clc_lo k h
  · have := clc_hi (k - 9) (by omega)
    rwa [show 9 + (k - 9) = k by omega, show 333 + (k - 9) = 324 + k by omega] at this

/-- A load found in the atoms, not a store, reads memory. -/
theorem load_val {S : List Atom} {w : ℕ → E} {σ : Val} {atoms : List Atom} {x p : V} {o : ℕ}
    (h : atoms.any (isLoadAt x p o) = true) (hg : ∀ a ∈ atoms, Good rd S w σ a)
    (hS : Atom.load x p o ∉ S) : σ x = rdAt rd (σ p) o := by
  obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp h
  cases a <;> simp only [isLoadAt, Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hp
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hp
  rcases hg _ ha with h' | h'
  · exact absurd h' hS
  · exact h'

/-- A load, not a store, of a word in memory holds. -/
theorem load_holds_of {S : List Atom} {w : ℕ → E} {σ : Val} {d p : V} {o : ℕ} {v : E}
    (hS : Atom.load d p o ∉ S) (hg : Good rd S w σ (.load d p o)) (hv : LoadHolds rd (σ p) o v) :
    (Atom.load d p o).Holds rd σ := by
  rcases hg with h | h
  · exact absurd h hS
  · show LoadHolds rd (σ p) o (σ d)
    rw [h, rdAt_of_load hv]; exact hv

theorem cl_cells_unique {blk : E} {cells cells' : List E} (h : ReadsAt rd blk cells)
    (h' : ReadsAt rd blk cells') (hl : cells.length = cells'.length) : cells' = cells := by
  rw [readsAt_memRun h, readsAt_memRun h', hl]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
/-- **`claim_list_last__L{k}` is complete**: from the state after whole blocks `pre` at `sp` and
`4k` canonical cells at `blk`, it returns the digest of `pre ++` the cells. -/
theorem claimLast_complete {k : ℕ} (hk : k < 17) {sp blk : E} {n : ℕ} {pre : List UInt8}
    (hpre : pre.length = rate * n) (hS : StateAt rd sp 0 (absorbChunks n zeroState pre))
    {cells : List E} (hl : cells.length = 4 * k) (hr : ReadsAt rd blk cells)
    (hc : AllCanonical cells) :
    coreProgram.Rel rd (clNames.getD k "") [sp, blk]
      (digestCells (keccak256 (pre ++ cellsBytes cells))) := by
  have hf := find_of_idx (cl_idx k hk) (by rw [coreProgram_length]; omega)
  have hok := cl_all k hk
  have hcok := clc_all hk
  set fn := coreProgram.getD (324 + k) default
  simp only [clOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hpar, hok⟩ := hok
  simp only [clcOk, Bool.and_eq_true, Option.isSome_iff_exists, List.isEmpty_iff] at hcok
  obtain ⟨⟨⟨c', hchk⟩, hS0⟩, hcok⟩ := hcok
  split at hok
  · rename_i atoms r0 r1 hsb
    rw [hsb] at hcok
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hok hcok
    obtain ⟨⟨⟨-, -⟩, hl1⟩, hst⟩ := hok
    obtain ⟨hcan, hneeds⟩ := hcok
    let args : List E := [sp, blk]
    obtain ⟨σ, hσ⟩ : ∃ σ : Val, σ = B1.Val.ofArgs (ev rd (fun _ => 0) args fn.body) := ⟨_, rfl⟩
    have hidx : ∀ v, σ v = σ (.n v.idx) := fun v => by rw [hσ]; rfl
    obtain ⟨-, -, hgs⟩ := ev_spec rd (fun _ => 0) fn.body args hchk
    rw [show args.length = 2 from rfl, hS0, ← hσ] at hgs
    have hbody := splitBody_eq hsb
    have hg : ∀ a ∈ atoms, Good rd [] (fun _ => 0) σ a := fun a ha =>
      hgs (.atom a) (by rw [hbody]; exact List.mem_append_left _ (List.mem_map_of_mem ha))
    have e0 : σ (.n 0) = sp := by rw [hσ]; exact ev_params rd _ (l := args) hchk (by simp [args])
    have e1 : σ (.n 1) = blk := by rw [hσ]; exact ev_params rd _ (l := args) hchk (by simp [args])
    have vst : ∀ c : Fin 13, σ ((clSt k).getD c default) =
        cellsOfState (absorbChunks n zeroState pre) false c := by
      intro c
      simp only [stLoadsOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hst
      rw [load_val (hst.2 c c.isLt) hg (by simp), e0, rdAt_of_load (hS c)]
    have vc : ∀ i < 4 * k, σ (.n (i + 2)) = cells.getD i 0 := by
      intro i hi
      simp only [loadsOk, List.all_eq_true, List.mem_range] at hl1
      have := hl1 i (by simp [clSpec]; omega)
      simp only [clSpec, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
        Option.map_some, Option.getD_some] at this
      rw [load_val this hg (by simp), e1, rdAt_of_load (hr i (by omega)),
        List.getD_eq_getElem _ _ (by omega)]
    have hA : ∀ i ∈ (clSt k).map V.idx ++ (List.range (4 * k)).map (· + 2),
        IsCanonical128 (σ (.n i)) := by
      intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hi
        obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hv
        have hc13 := List.mem_range.mp hc'
        have := vst ⟨c, hc13⟩
        simp only [clSt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hc13,
          Option.map_some, Option.getD_some] at this
        rw [← hidx, this]
        exact canon_cellsOfState _ _ _
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
        have hj' := List.mem_range.mp hj
        rw [vc j hj', List.getD_eq_getElem _ _ (by omega)]
        exact hc _ (List.getElem_mem _)
    have hat : ∀ a ∈ atoms, a.Holds rd σ := by
      refine atoms_holds hidx hcan hg hA fun a ha hn => Or.inl ?_
      rcases hneeds a ha with (h | h) | h
      · rw [hn] at h; exact absurd h (by simp)
      · cases a <;> simp only [isLoadBelow, Bool.false_eq_true, Bool.and_eq_true,
          decide_eq_true_eq] at h
        rename_i d p o
        obtain ⟨rfl, ho⟩ := h
        have hv := hS ⟨o, ho⟩
        rw [Nat.zero_add, ← e0] at hv
        exact load_holds_of (by simp) (hg _ ha) hv
      · cases a <;> simp only [isLoadBelow, Bool.false_eq_true, Bool.and_eq_true,
          decide_eq_true_eq] at h
        rename_i d p o
        obtain ⟨rfl, ho⟩ := h
        have hv := hr o (by omega)
        rw [← e1] at hv
        exact load_holds_of (by simp) (hg _ ha) hv
    have hrel : coreProgram.Rel rd (clNames.getD k "") [sp, blk] [σ r0, σ r1] := by
      refine (rel_iff_sem hf _ _).mpr ⟨σ, ?_, ?_⟩
      · rw [hpar]
        simp only [List.map_cons, List.map_nil, e0, e1]
      · rw [hbody, holdsList_atoms_ret]
        exact ⟨hat, rfl⟩
    obtain ⟨sp', blk', hargs, hlast⟩ := claimLast_sound hk hrel
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨rfl, rfl⟩ := hargs
    obtain ⟨cells', hl', hr', -, hd⟩ := hlast n pre hpre hS
    rw [cl_cells_unique hr hr' (by rw [hl, hl'])] at hd
    rw [← hd]
    exact hrel
  · exact absurd hok (by simp)

end
end LeanVM.Guest.B1.Digest
