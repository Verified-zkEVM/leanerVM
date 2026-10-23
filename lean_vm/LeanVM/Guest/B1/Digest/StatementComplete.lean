/-
  LeanVM.Guest.B1.Digest.StatementComplete

  `statement_digest`, completely: its meaning gives its core IR relation.
-/

module

public import LeanVM.Guest.B1.Digest.StatementChk
public import LeanVM.Guest.B1.Digest.PairComplete
public import LeanVM.Guest.B1.Digest.Steps
public import LeanVM.Guest.B1.Digest.Chain

/-!
# `statement_digest`, completely

The honest valuation is the template evaluated on the arguments (`Fwd.ev`, its checks in
`StatementChk`): the header's two loads and the pairs' (`pair_holds`) hold on the words the
meaning reads, the `KECCAK` inputs are canonical (the header cells by the meaning, the pairs' cells
packed, the constants), so every atom holds (`Fwd.atoms_holds`). The relation then holds at the
valuation's returns, which soundness makes the meaning's digest; the meaning's words are the
memory's, so its returns are these.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

theorem mem_sd_pair {p : ℕ} (hp : p < 12) {a : Atom} (ha : a ∈ pairAtoms (.n 5) (2 * p) (12 + 27 * p)) :
    a ∈ sdAtoms := by
  unfold sdAtoms
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_)))))
  exact List.mem_flatMap.mpr ⟨p, List.mem_range.mpr hp, ha⟩

theorem mem_sd_hdr {a : Atom} (ha : a ∈ sdHdr) : a ∈ sdAtoms := by
  unfold sdAtoms
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ha)))))

theorem mem_sd_const {a : Atom} (ha : a ∈ sdConsts) : a ∈ sdAtoms := by
  unfold sdAtoms
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_right _ ha))))

theorem mem_sd_blk4 {a : Atom} (ha : a ∈ sdBlk4) : a ∈ sdAtoms := by
  unfold sdAtoms
  exact List.mem_append_left _ (List.mem_append_right _ ha)

/-- The meaning's words are the memory's: its returns are determined. -/
theorem statement_digest_unique {rd : Reader} {args r r' : List E}
    (h : MeaningStatementDigest rd args r) (h' : MeaningStatementDigest rd args r') : r = r' := by
  match args, h, h' with
  | [s0, s1, sp, a0, a1, dp], h, h' =>
    obtain ⟨h0, h1, cells, l0, l1, hlen, hreads, -, hr⟩ := h
    obtain ⟨h0', h1', cells', l0', l1', hlen', hreads', -, hr'⟩ := h'
    rw [loadHolds_unique l0' l0, loadHolds_unique l1' l1] at hr'
    have hc : cells' = cells := by
      rw [readsAt_memRun hreads, readsAt_memRun hreads', hlen, hlen']
    rw [hr, hr', hc]

set_option maxRecDepth 10000 in
/-- **`statement_digest` is complete.** -/
theorem statement_digest_complete : statement_digest_complete_Spec := by
  intro rd args rets h
  match args, h with
  | [s0, s1, sp, a0, a1, dp], h =>
    have hM := h
    obtain ⟨h0, h1, cells, l0, l1, hlen, hreads, hcan, -⟩ := h
    let args : List E := [s0, s1, sp, a0, a1, dp]
    let σ : Val := B1.Val.ofArgs (ev rd (fun _ => 0) args sdBody)
    obtain ⟨-, -, hgs⟩ := ev_spec rd (fun _ => 0) sdBody args sd_chk
    rw [show args.length = 6 from rfl, sd_stores] at hgs
    have hg : ∀ a ∈ sdAtoms, Good rd [] (fun _ => 0) σ a := fun a ha =>
      hgs (.atom a) (List.mem_append_left _ (List.mem_map_of_mem ha))
    have hpar : ∀ i < 6, σ (.n i) = args.getD i 0 := fun i hi => ev_params rd _ (l := args) sd_chk hi
    have e0 : σ (.n 0) = s0 := hpar 0 (by omega)
    have e1 : σ (.n 1) = s1 := hpar 1 (by omega)
    have e2 : σ (.n 2) = sp := hpar 2 (by omega)
    have e3 : σ (.n 3) = a0 := hpar 3 (by omega)
    have e4 : σ (.n 4) = a1 := hpar 4 (by omega)
    have e5 : σ (.n 5) = dp := hpar 5 (by omega)
    have hl24 : cells.length = 24 := hlen
    -- the pairs
    have hP : ∀ p < 12, ∀ a ∈ pairAtoms (.n 5) (2 * p) (12 + 27 * p), a.Holds rd σ := by
      intro p hp
      refine pair_holds (fun a ha => hg a (mem_sd_pair hp ha)) (fun a ha => absurd ha (by simp))
        (s := cells[2 * p]'(by omega)) (t := cells[2 * p + 1]'(by omega)) ?_ ?_
      · rw [e5]; exact hreads _ _
      · rw [e5]; exact hreads _ _
    -- the header
    have hH : ∀ a ∈ sdHdr, a.Holds rd σ := by
      have g := fun a (ha : a ∈ sdHdr) => hg a (mem_sd_hdr ha)
      simp only [sdHdr, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
        implies_true, and_true] at g ⊢
      obtain ⟨g6, g7, g8, g9, g10, g11⟩ := g
      simp only [Good, List.not_mem_nil, false_or] at g6 g7 g8 g9 g10 g11
      refine ⟨g6, g7, ?_, ?_, g10, g11⟩
      · show LoadHolds rd (σ (.n 2)) 0 (σ (.n 8))
        rw [g8, e2, rdAt_of_load l0]; exact l0
      · show LoadHolds rd (σ (.n 2)) 1 (σ (.n 9))
        rw [g9, e2, rdAt_of_load l1]; exact l1
    -- the canonical values
    have hA : ∀ i ∈ sdA, IsCanonical128 (σ (.n i)) := by
      have hc := fun x (hx : x ∈ [s0, s1, h0, h1, a0, a1]) => hcan x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hc
      obtain ⟨c0, c1, c2, c3, c4, c5⟩ := hc
      have g := fun a (ha : a ∈ sdHdr) => hg a (mem_sd_hdr ha)
      simp only [sdHdr, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
        implies_true, and_true] at g
      obtain ⟨g6, g7, g8, g9, g10, g11⟩ := g
      simp only [Good, List.not_mem_nil, false_or] at g6 g7 g8 g9 g10 g11
      have gc := fun a (ha : a ∈ sdConsts) => hg a (mem_sd_const ha)
      simp only [sdConsts, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
        implies_true, and_true, Good] at gc
      obtain ⟨k336, k337, k338, k339, k340⟩ := gc
      have g4 := fun a (ha : a ∈ sdBlk4) => hg a (mem_sd_blk4 ha)
      simp only [sdBlk4, List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil,
        IsEmpty.forall_iff, implies_true, and_true, Good] at g4
      obtain ⟨-, k428, -, -⟩ := g4
      intro i hi
      simp only [sdA, List.mem_append] at hi
      rcases hi with (hi | hi) | hi
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
        · rw [g6, e0]; exact c0
        · rw [g7, e1]; exact c1
        · rw [g8, e2, rdAt_of_load l0]; exact c2
        · rw [g9, e2, rdAt_of_load l1]; exact c3
        · rw [g10, e3]; exact c4
        · rw [g11, e4]; exact c5
      · obtain ⟨p, hp, hi⟩ := List.mem_flatMap.mp hi
        obtain ⟨-, -, hc3⟩ := pair_fwd (hP p (List.mem_range.mp hp))
        have hm : σ (.n i) ∈ [σ (.n (12 + 27 * p + 8)), σ (.n (12 + 27 * p + 17)),
            σ (.n (12 + 27 * p + 26))] := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
          rcases hi with rfl | rfl | rfl <;> simp
        rw [hc3] at hm
        exact pairCells_canonical _ _ _ hm
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
        · rw [k336]; exact isCanonical128_word _ _
        · rw [k337]; exact isCanonical128_word _ _
        · rw [k338]; exact isCanonical128_word _ _
        · rw [k339]; exact isCanonical128_word _ _
        · rw [k340]; exact isCanonical128_word _ _
        · rw [k428]; exact isCanonical128_word _ _
    -- every atom
    have hat : ∀ a ∈ sdAtoms, a.Holds rd σ := by
      refine atoms_holds (fun v => rfl) sd_canon hg hA fun a ha hn => Or.inl ?_
      have hf : a ∈ sdAtoms.filter needsSide := List.mem_filter.mpr ⟨ha, hn⟩
      rw [sd_needs] at hf
      rcases List.mem_append.mp hf with hf | hf
      · exact hH a (List.mem_filter.mp hf).1
      · obtain ⟨p, hp, hf⟩ := List.mem_flatMap.mp hf
        exact hP p (List.mem_range.mp hp) a (List.mem_filter.mp hf).1
    -- the relation, and its returns
    have hrel : coreProgram.Rel rd "statement_digest" args [σ (.n 443), σ (.n 444)] := by
      refine (rel_iff_sem find_statement_digest _ _).mpr ⟨σ, ?_, ?_⟩
      · rw [core21_params]
        simp only [List.map_cons, List.map_nil]
        rw [hpar 0 (by omega), hpar 1 (by omega), hpar 2 (by omega), hpar 3 (by omega),
          hpar 4 (by omega), hpar 5 (by omega)]
        rfl
      · rw [core21_body, holdsList_atoms_ret]
        exact ⟨hat, rfl⟩
    rw [statement_digest_unique hM (statement_digest_sound rd _ _ hrel)]
    exact hrel
  | [], h => exact h.elim
  | [_], h => exact h.elim
  | [_, _], h => exact h.elim
  | [_, _, _], h => exact h.elim
  | [_, _, _, _], h => exact h.elim
  | [_, _, _, _, _], h => exact h.elim
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, h => exact h.elim

end
end LeanVM.Guest.B1.Digest
