/-
  LeanVM.Guest.B1.Da.VerifyL23Complete

  `__loop23` (a row's digest), completely.
-/

module

public import LeanVM.Guest.B1.Da.VerifyL23CChk
public import LeanVM.Guest.B1.Da.ColumnComplete
public import LeanVM.Guest.B1.Digest.ChainFilter
public import LeanVM.Guest.B1.Digest.PairComplete

/-!
# A row's digest, completely

`l23_block`: `__loop23`'s block at row `x` holds on the evaluated valuation (`Fwd.ev`) when the
row's prefix base at `prefix_bases·x` points to the row's `128` canonical cells and the row tree
holds their digest at `rowtree·x²`: its loads read the cells, its chain is their digest
(`chain_final` on the block without its stores, `check_filter`), which its stores find.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main LeanVM.Guest.B1.Fwd

@[expose] public section

variable {rd : Reader}

theorem good_mul {S : List Atom} {w : ℕ → E} {σ : Val} {d x y : ℕ} (hx : x < d) (hy : y < d)
    (h : Good rd S w σ (.mul (.n d) (.n x) (.n y))) : σ (.n d) = σ (.n x) * σ (.n y) := by
  simp only [Good] at h
  rwa [ite_pos' ⟨hx, hy⟩] at h

theorem good_load {S : List Atom} {w : ℕ → E} {σ : Val} {d p : V} {o : ℕ}
    (hS : Atom.load d p o ∉ S) (h : Good rd S w σ (.load d p o)) : σ d = rdAt rd (σ p) o := by
  rcases h with h | h
  · exact absurd h hS
  · exact h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
/-- **A row's digest** (`__loop23`). -/
theorem l23_block {x N pb rt run : E} {cells : List E} (hrun : LoadHolds rd (pb * x) 0 run)
    (hcells : ReadsAt rd run cells) (hlen : cells.length = 128) (hcan : AllCanonical cells)
    (hd0 : LoadHolds rd (rt * (x * x)) 0 (digestScalars (keccak256 (cellsBytes cells))).1)
    (hd1 : LoadHolds rd (rt * (x * x)) 1 (digestScalars (keccak256 (cellsBytes cells))).2) :
    LoopBlock rd (coreProgram.getD 365 default) x N [pb, rt] := by
  have hok := l23_ok
  have hcok := l23c_ok
  simp only [l23Ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hshape, hplen⟩, -⟩, -⟩, -⟩, hchkR⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hok
  simp only [l23COk, Bool.and_eq_true, Option.isSome_iff_exists, decide_eq_true_eq,
    List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true'] at hcok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c', hchk⟩, hatoms⟩, hS⟩, hcan2⟩, hneeds⟩, hm4⟩, hm5⟩, hmc⟩, hm477⟩, hm478⟩,
    ho0⟩, ho1⟩ := hcok
  set fn := coreProgram.getD 365 default
  set A := atomsIn (loopPre fn)
  set S := storesOf 4 fn.body with hSdef
  let args : List E := [x, N, pb, rt]
  obtain ⟨σ, hσ⟩ : ∃ σ : Val, σ = B1.Val.ofArgs (ev rd (fun _ => 0) args fn.body) := ⟨_, rfl⟩
  have hidx : ∀ v, σ v = σ (.n v.idx) := fun v => by rw [hσ]; rfl
  obtain ⟨-, -, hgs⟩ := ev_spec rd (fun _ => 0) fn.body args hchk
  rw [show args.length = 4 from rfl, ← hσ] at hgs
  have hg : ∀ a ∈ A, Good rd S (fun _ => 0) σ a := fun a ha =>
    hgs (.atom a) (loopPre_mem (atom_mem_of_atomsIn ha))
  have hpar : fn.params = [.n 0, .n 1, .n 2, .n 3] := by
    rw [params_of_shape hshape hplen]; rfl
  have par : ∀ i (hi : i < 4), σ (.n i) = args.getD i 0 := fun i hi => by
    rw [hσ]; exact ev_params rd _ (l := args) hchk (by simp [args]; omega)
  have e0 : σ (.n 0) = x := par 0 (by omega)
  have e2 : σ (.n 2) = pb := par 2 (by omega)
  have e3 : σ (.n 3) = rt := par 3 (by omega)
  have hnS : ∀ d p o, Atom.load d p o ∈ A → (d = .n 464 ∨ d = .n 465 → False) →
      Atom.load d p o ∉ S := by
    intro d p o _ hd hm
    rw [hS] at hm
    simp only [List.mem_cons, Atom.load.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩
    · exact hd (Or.inl rfl)
    · exact hd (Or.inr rfl)
  have v4 : σ (.n 4) = pb * x := by
    rw [good_mul (by omega) (by omega) (hg _ hm4), e2, e0]
  have v5 : σ (.n 5) = run := by
    rw [good_load (hnS _ _ _ hm5 (by simp)) (hg _ hm5), v4, rdAt_of_load hrun]
  have vc : ∀ i < 128, σ (.n (6 + i)) = cells.getD i 0 := by
    intro i hi
    have hm := hmc i hi
    rw [good_load (hnS _ _ _ hm (by
      rintro (h | h) <;> simp only [V.mk.injEq] at h <;> omega)) (hg _ hm), v5,
      rdAt_of_load (hcells i (by omega)), List.getD_eq_getElem _ _ (by omega)]
  have v478 : σ (.n 478) = rt * (x * x) := by
    rw [good_mul (by omega) (by omega) (hg _ hm478), good_mul (by omega) (by omega) (hg _ hm477),
      e3, e0]
  have hA : ∀ i ∈ (List.range 128).map (6 + ·), IsCanonical128 (σ (.n i)) := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    have hj' := List.mem_range.mp hj
    rw [vc j hj', List.getD_eq_getElem _ _ (by omega)]
    exact hcan _ (List.getElem_mem _)
  have hq : ∀ a, isLoadB a = false → decide (a ∉ S) = true := by
    intro a ha
    simp only [decide_eq_true_eq]
    intro hm
    rw [hS] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> simp [isLoadB] at ha
  have hat : ∀ a ∈ A, a.Holds rd σ := by
    refine atoms_holds_stores (S := S) (w := fun _ => 0) hidx hcan2 hg hA
      (fun a ha hnS' hns => Or.inl ?_) (fun h1 a ha haS => ?_)
    · rcases hneeds a ha with ((h | h) | h) | h
      · rw [hns] at h; exact absurd h (by simp)
      · exact absurd h hnS'
      · subst h
        show LoadHolds rd (σ (.n 4)) 0 (σ (.n 5))
        rw [v4, v5]; exact hrun
      · cases a <;> simp only [isRowCellLoad, Bool.false_eq_true, Bool.and_eq_true,
          decide_eq_true_eq] at h
        rename_i d p o
        obtain ⟨⟨rfl, rfl⟩, ho⟩ := h
        show LoadHolds rd (σ (.n 5)) o (σ (.n (6 + o)))
        rw [v5, vc o ho, List.getD_eq_getElem _ _ (by omega)]
        exact hcells o (by omega)
    · have hA' : ∀ b ∈ A.filter (fun a => decide (a ∉ S)), b.Holds rd σ :=
        fun b hb => h1 b (List.mem_filter.mp hb).1 (by simpa using (List.mem_filter.mp hb).2)
      have hchk' : (rowSpec A).check (A.filter (fun a => decide (a ∉ S))) = true := by
        rw [check_filter hq]; exact hchkR
      obtain ⟨hd, -⟩ := chain_final hchk' rfl hA' (pre := []) (n := 0) rfl
        (fun c => (cellsOfState_zero false c).symm)
      have hv : ((rowSpec A).vals σ).take ((rowSpec A).len / 16) = cells := by
        refine List.ext_getElem (by simp [rowSpec, ChainSpec.vals, hlen]) fun i h1 h2 => ?_
        have hi : i < 128 := by omega
        simp only [rowSpec, ChainSpec.vals, List.getElem_take, List.getElem_map,
          List.getElem_range, srcVal]
        rw [vc i hi, List.getD_eq_getElem _ _ h2]
      rw [hv, List.nil_append, ho0, ho1] at hd
      simp only [Prod.ext_iff] at hd
      rw [hS] at haS
      simp only [List.mem_cons, List.not_mem_nil, or_false] at haS
      rcases haS with rfl | rfl
      · show LoadHolds rd (σ (.n 478)) 0 (σ (.n 464))
        rw [v478, hd.1]; exact hd0
      · show LoadHolds rd (σ (.n 478)) 1 (σ (.n 465))
        rw [v478, hd.2]; exact hd1
  refine ⟨σ, ?_, fun s hs => ?_⟩
  · rw [hpar]
    simp only [List.map_cons, List.map_nil]
    rw [e0, e2, e3, par 1 (by omega)]
    rfl
  · have := hatoms s hs
    cases s <;> simp only [Bool.false_eq_true] at this
    rename_i a
    exact ⟨hat a (mem_atomsIn hs), trivial⟩

end
end LeanVM.Guest.B1.Da
