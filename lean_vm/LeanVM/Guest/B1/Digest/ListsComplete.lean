/-
  LeanVM.Guest.B1.Digest.ListsComplete

  `da_list_digest`, completely: the DA list's digest of canonical cells in memory gives its core IR
  relation, through each `da_hash_roots__L{n}`.
-/

module

public import LeanVM.Guest.B1.Digest.ListsChk
public import LeanVM.Guest.B1.Digest.PairComplete
public import LeanVM.Guest.B1.Digest.Steps

/-!
# `da_list_digest`, completely

* `claimListOut_unique`: the cells of `ClaimListOut` are the memory's, so its returns are
  determined.
* `hashRoots_complete`: `da_hash_roots__L{n}`, `n ≤ 16`, evaluated on its argument (`Fwd.ev`, its
  checks `hrc_all`): its loads read the canonical cells, so every atom holds; soundness makes its
  returns the digest.
* `da_list_digest_complete : da_list_digest_complete_Spec`: the dispatch to `n`.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

variable {rd : Reader}

/-- **The claim list's returns are determined** by the memory. -/
theorem claimListOut_unique {p : E} {n : ℕ} {r r' : List E} (h : ClaimListOut rd p n r)
    (h' : ClaimListOut rd p n r') : r = r' := by
  obtain ⟨cells, hl, hr, -, hd⟩ := h
  obtain ⟨cells', hl', hr', -, hd'⟩ := h'
  have hc : cells = cells' := by rw [readsAt_memRun hr, readsAt_memRun hr', hl, hl']
  rw [hd, hd', hc]

theorem good_load_of_any {S : List Atom} {w : ℕ → E} {σ : Val} {atoms : List Atom} {x p : V}
    {o : ℕ} (hS : S = []) (hg : ∀ a ∈ atoms, Good rd S w σ a) (h : atoms.any (isLoadAt x p o) = true) :
    σ x = rdAt rd (σ p) o := by
  obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp h
  cases a <;> simp only [isLoadAt, Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hp
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hp
  rcases (hg _ ha : Good rd S w σ (.load _ _ _)) with h | h
  · rw [hS] at h; exact absurd h (by simp)
  · exact h

/-- **`da_hash_roots__L{n}` is complete.** -/
theorem hashRoots_complete {n : ℕ} (hn : n < 17) {p : E} {rets : List E}
    (h : ClaimListOut rd p n rets) : coreProgram.Rel rd (hrNames.getD n "") [p] rets := by
  have hf := find_of_idx (hr_idx n hn) (by rw [coreProgram_length]; omega)
  have hok := hr_all n hn
  have hc := hrc_all n hn
  set f := coreProgram.getD (377 + n) default
  obtain ⟨cells, hlen, hreads, hcan, hd⟩ := h
  simp only [hrOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hpar, hok⟩ := hok
  simp only [hrcOk, Bool.and_eq_true, Option.isSome_iff_exists, List.isEmpty_iff] at hc
  obtain ⟨⟨⟨c', hchk⟩, hst⟩, hc⟩ := hc
  split at hok
  · rename_i atoms r0 r1 hsb
    rw [hsb] at hc
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hok hc
    obtain ⟨⟨-, -⟩, hl⟩ := hok
    obtain ⟨hcanon, hneeds⟩ := hc
    have hbody := splitBody_eq hsb
    let σ : Val := B1.Val.ofArgs (ev rd (fun _ => 0) [p] f.body)
    obtain ⟨-, -, hgs⟩ := ev_spec rd (fun _ => 0) f.body [p] hchk
    rw [show [p].length = 1 from rfl, hst] at hgs
    have hg : ∀ a ∈ atoms, Good rd [] (fun _ => 0) σ a := fun a ha =>
      hgs (.atom a) (by rw [hbody]; exact List.mem_append_left _ (List.mem_map_of_mem ha))
    have e0 : σ (.n 0) = p := ev_params rd _ (l := [p]) hchk (by simp)
    -- the cells
    have hcell : ∀ j < 4 * n, σ (.n (j + 1)) = cells.getD j 0 := by
      intro j hj
      simp only [loadsOk, List.all_eq_true, List.mem_range] at hl
      have hj' : j < (hrSpec n atoms).msg.length := by simp [hrSpec]; omega
      have := hl j hj'
      simp only [hrSpec, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range (show j < 4 * n by omega), Option.map_some, Option.getD_some] at this
      rw [good_load_of_any rfl hg this, e0, rdAt_of_load (hreads j (by omega)),
        List.getD_eq_getElem _ _ (by omega)]
    have hA : ∀ i ∈ (List.range (4 * n)).map (· + 1), IsCanonical128 (σ (.n i)) := by
      intro i hi
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      have hj' := List.mem_range.mp hj
      rw [hcell j hj', List.getD_eq_getElem _ _ (by omega)]
      exact hcan _ (List.getElem_mem _)
    have hat : ∀ a ∈ atoms, a.Holds rd σ := by
      refine atoms_holds (fun v => rfl) hcanon hg hA fun a ha hns => Or.inl ?_
      have hl : isLoadHR n a = true := by
        rcases hneeds a ha with h | h
        · rw [hns] at h; exact absurd h (by simp)
        · exact h
      cases a <;> simp only [isLoadHR, Bool.false_eq_true, Bool.and_eq_true,
        decide_eq_true_eq] at hl
      rename_i d q off
      obtain ⟨⟨rfl, rfl⟩, hoff⟩ := hl
      show LoadHolds rd (σ (.n 0)) off (σ (.n (off + 1)))
      rw [e0, hcell off hoff, List.getD_eq_getElem _ _ (by omega)]
      exact hreads off (by omega)
    have hrel : coreProgram.Rel rd (hrNames.getD n "") [p] [σ r0, σ r1] := by
      refine (rel_iff_sem hf _ _).mpr ⟨σ, ?_, ?_⟩
      · rw [hpar]; simp only [List.map_cons, List.map_nil, e0]
      · rw [hbody, holdsList_atoms_ret]
        exact ⟨hat, rfl⟩
    obtain ⟨p', hp', hout⟩ := hashRoots_sound hn hrel
    simp only [List.cons.injEq, and_true] at hp'
    subst hp'
    have hmine : ClaimListOut rd p n rets := ⟨cells, hlen, hreads, hcan, hd⟩
    rw [claimListOut_unique hmine hout]
    exact hrel
  · exact absurd hok (by simp)

/-- **`da_list_digest` is complete.** -/
theorem da_list_digest_complete : da_list_digest_complete_Spec := by
  intro rd args rets h
  match args, h with
  | [roots, ng], h =>
    obtain ⟨n, hn, hng, hout⟩ := h
    have hr2 : rets = [rets.getD 0 0, rets.getD 1 0] := by
      obtain ⟨_, -, -, -, hd⟩ := hout
      rw [hd]; rfl
    refine (rel_iff_sem find_da_list_digest _ _).mpr
      ⟨Val.ofArgs [roots, ng, rets.getD 0 0, rets.getD 1 0, rets.getD 0 0, rets.getD 1 0], rfl, ?_⟩
    rw [core29_body]
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, ofArgs_n,
      List.getD_cons_succ, List.getD_cons_zero]
    have hlt : n < hrNames.length := by
      simp only [hrNames, List.length_cons, List.length_nil]; simp only [maxDaRoots] at hn; omega
    refine ⟨⟨n, hlt, by rw [hng, gen_pow_eq_ofK], ?_⟩, trivial, trivial, hr2.symm⟩
    rw [← List.getD_eq_getElem hrNames "" hlt, ← hr2]
    exact hashRoots_complete (by simp only [maxDaRoots] at hn; omega) hout
  | [], h => exact h.elim
  | [_], h => exact h.elim
  | _ :: _ :: _ :: _, h => exact h.elim

end
end LeanVM.Guest.B1.Digest
