/-
  LeanVM.Guest.B1.Tables.Vt.Fresh

  `verify_tables`' bus stream: the five framework column values read from the stream into the
  carried sponge, and the table sumcheck's batching challenge squeezed after them.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.CountTotal
public import LeanVM.Guest.B1.Gkr.Odd

/-!
# The bus's stream words (G:2082-2118, 2183)

The framework decomposition reads, in block order, the memory block's three values (push side),
the final memory count and the final bytecode count (pull side), each `fs_next` into the rate
(`vt_fresh`): a permutation after the fourth, the fifth left waiting. The table sumcheck's
`zc_xi` is the squeeze after them. In the specification's terms: from the carried capacity, the
five words absorbed, then one squeeze.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The five words, in their stream order: the memory values, the final memory and bytecode
counts. -/
def vtFreshWords (σ : Val) : List E :=
  [σ (.n 2914), σ (.n 2927), σ (.n 2940), σ (.n 4444), σ (.n 4502)]

/-- The carried sponge after them. -/
def vtFreshFs (σ : Val) : Fs :=
  (⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], []⟩ : Fs).absorbAll (vtFreshWords σ)
    dsObserve

theorem vt_pack_cells {σ : Val} {b : ℕ} (hp : FsPackOk σ (.n b) (b + 1) dsObserve)
    (hc : IsCanonical128 (σ (.n (b + 7)))) :
    σ (.n (b + 7)) = (Keccak.scalarCells (σ (.n b)) dsObserve).1 ∧
      σ (.n (b + 9)) = (Keccak.scalarCells (σ (.n b)) dsObserve).2 :=
  tb_pack_cells hp hc

set_option maxRecDepth 10000 in
/-- **The bus's stream words** and the batching challenge. -/
theorem vt_fresh {rd : Reader} {σ : Val} (h : VtH rd σ) :
    TbReadsAt rd (σ (.n 5)) (vtFreshWords σ) ∧
      (∀ k < 5, FsPackOk σ (.n ([2914, 2927, 2940, 4444, 4502].getD k 0))
        ([2914, 2927, 2940, 4444, 4502].getD k 0 + 1) dsObserve) ∧
      σ (.n 5895) = (vtFreshFs σ).squeeze.1 ∧
      ((List.range 5).map fun k ↦ σ (.n (5884 + k))) = (vtFreshFs σ).squeeze.2.cap := by
  obtain ⟨_, f0⟩ := h.slice 2462 (fsNextT (.n 5) 0 2914) (by decide +kernel)
  obtain ⟨_, f1⟩ := h.slice 2476 (fsNextT (.n 5) 1 2927) (by decide +kernel)
  obtain ⟨_, f2⟩ := h.slice 2490 (fsNextT (.n 5) 2 2940) (by decide +kernel)
  obtain ⟨_, f3⟩ := h.slice 3938 (fsNextT (.n 5) 3 4444) (by decide +kernel)
  obtain ⟨_, f4⟩ := h.slice 3983 (fsNextT (.n 5) 4 4502) (by decide +kernel)
  rw [holds_fsNextT] at f0 f1 f2 f3 f4
  obtain ⟨⟨l0, p0⟩, -⟩ := f0
  obtain ⟨⟨l1, p1⟩, -⟩ := f1
  obtain ⟨⟨l2, p2⟩, -⟩ := f2
  obtain ⟨⟨l3, p3⟩, -⟩ := f3
  obtain ⟨⟨l4, p4⟩, -⟩ := f4
  have c22 := h.atom 0 (.copy (.n 22) (.n 0)) (by decide +kernel)
  have c23 := h.atom 1 (.copy (.n 23) (.n 1)) (by decide +kernel)
  have c24 := h.atom 2 (.copy (.n 24) (.n 2)) (by decide +kernel)
  have c25 := h.atom 3 (.copy (.n 25) (.n 3)) (by decide +kernel)
  have c26 := h.atom 4 (.copy (.n 26) (.n 4)) (by decide +kernel)
  have k1 := h.atom 3982 (.keccak [.n 2921, .n 2923, .n 2934, .n 2936, .n 2947, .n 2949, .n 4451,
    .n 4453, .n 22, .n 23, .n 24, .n 25, .n 26] (lyOuts 4489) false false) (by decide +kernel)
  have z2 := h.atom 5194 (.const (.n 5872) (word 0 0 0)) (by decide +kernel)
  have z3 := h.atom 5195 (.const (.n 5873) (word 0 0 0)) (by decide +kernel)
  have z4 := h.atom 5196 (.const (.n 5874) (word 0 0 0)) (by decide +kernel)
  have z5 := h.atom 5197 (.const (.n 5875) (word 0 0 0)) (by decide +kernel)
  have k2 := h.atom 5198 (.keccak [.n 4509, .n 4511, .n 5872, .n 5872, .n 5872, .n 5873, .n 5874,
    .n 5875, .n 4497, .n 4498, .n 4499, .n 4500, .n 4501] (lyOuts 5876) false false)
    (by decide +kernel)
  obtain ⟨_, hch⟩ := h.slice 5199 (challengeT (.n 5876) (.n 5877) 5889) (by decide +kernel)
  rw [holds_challengeT] at hch
  simp only [Atom.Holds, tb_word_zero] at c22 c23 c24 c25 c26 z2 z3 z4 z5
  obtain ⟨hcan1, hP1, hC1⟩ := ly_keccak k1
  obtain ⟨hcan2, hP2, hC2⟩ := ly_keccak k2
  have cn1 : ∀ x ∈ [2921, 2934, 2947, 4451], IsCanonical128 (σ (.n x)) := by
    intro x hx; apply hcan1; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp
  have e0 := vt_pack_cells p0 (cn1 2921 (by simp))
  have e1 := vt_pack_cells p1 (cn1 2934 (by simp))
  have e2 := vt_pack_cells p2 (cn1 2947 (by simp))
  have e3 := vt_pack_cells p3 (cn1 4451 (by simp))
  have e4 := vt_pack_cells p4 (hcan2 _ (by simp))
  -- the sponge after the four, and its permutation
  have hS4 : (⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], []⟩ : Fs).absorbAll
      [σ (.n 2914), σ (.n 2927), σ (.n 2940), σ (.n 4444)] dsObserve =
      ⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], [(σ (.n 2914), dsObserve),
        (σ (.n 2927), dsObserve), (σ (.n 2940), dsObserve), (σ (.n 4444), dsObserve)]⟩ := by
    rw [absorbAll_short _ _ _ (by simp)]; rfl
  set S4 : Fs := ⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], [(σ (.n 2914), dsObserve),
    (σ (.n 2927), dsObserve), (σ (.n 2940), dsObserve), (σ (.n 4444), dsObserve)]⟩ with hS4d
  have hin1 : ([.n 2921, .n 2923, .n 2934, .n 2936, .n 2947, .n 2949, .n 4451, .n 4453, .n 22,
      .n 23, .n 24, .n 25, .n 26] : List V).map σ = rateOf S4.pend ++ S4.cap := by
    rw [rateOf_eq_cells _ (by simp [hS4d])]
    simp only [hS4d, List.map_cons, List.map_nil, pendCells, List.flatMap_cons, List.flatMap_nil,
      List.length_cons, List.length_nil, List.cons_append, List.nil_append, List.append_nil,
      e0.1, e0.2, e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, c22, c23, c24, c25, c26]
    rfl
  rw [hin1] at hC1
  have hS5 : vtFreshFs σ = ⟨(lyCap 4489).map σ, [(σ (.n 4502), dsObserve)]⟩ := by
    have hsplit : vtFreshWords σ = [σ (.n 2914), σ (.n 2927), σ (.n 2940), σ (.n 4444)] ++
        [σ (.n 4502)] := rfl
    have happ : ∀ (s : Fs) (l1 l2 : List E) (t : ℕ),
        s.absorbAll (l1 ++ l2) t = (s.absorbAll l1 t).absorbAll l2 t := by
      intro s l1 l2 t; simp [Fs.absorbAll, List.foldl_append]
    rw [vtFreshFs, hsplit, happ, hS4, hC1]
    simp [Fs.absorbAll, Fs.absorb, Fs.perm, rateScalars, hS4d]
  have hin2 : ([.n 4509, .n 4511, .n 5872, .n 5872, .n 5872, .n 5873, .n 5874, .n 5875, .n 4497,
      .n 4498, .n 4499, .n 4500, .n 4501] : List V).map σ =
      rateOf (vtFreshFs σ).pend ++ (vtFreshFs σ).cap := by
    rw [hS5, rateOf_eq_cells _ (by simp)]
    simp only [List.map_cons, List.map_nil, pendCells, List.flatMap_cons, List.flatMap_nil,
      List.length_cons, List.length_nil, List.cons_append, List.nil_append, List.append_nil,
      e4.1, e4.2, z2, z3, z4, z5]
    rfl
  rw [hin2] at hP2 hC2
  refine ⟨fun k hk => ?_, fun k hk => ?_, ?_, ?_⟩
  · simp only [vtFreshWords, List.length_cons, List.length_nil] at hk
    interval_cases k
    · exact l0
    · exact l1
    · exact l2
    · exact l3
    · exact l4
  · interval_cases k
    · exact p0
    · exact p1
    · exact p2
    · exact p3
    · exact p4
  · exact challengeT_value hch.1 (hP2 0 (by omega)) (hP2 1 (by omega))
  · show _ = capOf (permOf (rateOf (vtFreshFs σ).pend ++ (vtFreshFs σ).cap))
    rw [← hC2]; simp [lyCap]

end
end LeanVM.Guest.B1.Tables
