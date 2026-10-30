/-
  LeanVM.Guest.B1.Whir.LamPows

  A level's query weights: the powers of the batching challenge, stored.
-/

module

public import LeanVM.Guest.B1.Whir.Flat

/-!
# The query weights (G:1448-1451)

`osLamPows lam base k Q` stores `query_weights[base + i] = lam^i`, `i < Q`, and leaves `lam^Q` (at
`k + Q - 1`) for `opening_queries`' `lam_n` (`osLamPows_sound`, `2 ≤ Q`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- **The query weights**: `lam^i` at `qw·g^(base + i)`, `i < Q`, and `lam^Q` at `k + Q - 1`. -/
theorem osLamPows_sound {lam base k Q : ℕ} (hQ : 2 ≤ Q)
    (h : AllOk C rd σ (osLamPows lam base k Q)) :
    (∀ i < Q, LoadHolds rd (σ (.n osQw)) (base + i) (σ (.n lam) ^ i)) ∧
      σ (.n (k + Q - 1)) = σ (.n lam) ^ Q := by
  obtain ⟨q, rfl⟩ : ∃ q, Q = q + 2 := ⟨Q - 2, by omega⟩
  simp only [osLamPows, Nat.add_one_ne_zero, ↓reduceIte,
    allOk_append, allOk_cons, allOk_nil, and_true, allOk_flatten, StmtOk, Atom.Holds,
    List.mem_map, List.mem_range, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    Nat.add_sub_cancel] at h
  obtain ⟨⟨c1, l0⟩, l1, m2, hrest⟩ := h
  have hv : ∀ i < q + 1, σ (.n (k + 1 + i)) = σ (.n lam) ^ (i + 2) := by
    intro i
    induction i with
    | zero => intro _; rw [Nat.add_zero, m2]; ring
    | succ i ih =>
      intro hi
      obtain ⟨-, hm⟩ := hrest i (by omega)
      rw [show k + 1 + (i + 1) = k + 2 + i by ring, hm, ih (by omega)]; ring
  refine ⟨fun i hi ↦ ?_, ?_⟩
  · rcases i with _ | _ | i
    · rw [c1] at l0; simpa [word_one] using l0
    · simpa using l1
    · obtain ⟨hl, -⟩ := hrest i (by omega)
      rw [hv i (by omega)] at hl
      simpa [show base + (i + 2) = base + 2 + i by ring] using hl
  · rw [show k + (q + 2) - 1 = k + 1 + q by omega, hv q (by omega)]

end
end LeanVM.Guest.B1.Whir
