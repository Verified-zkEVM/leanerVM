/-
  LeanVM.Guest.B1.Digest.CoverComplete

  `cover_da_root`, completely: a marked DA slot below a bound within the memory gives its core IR
  relation.
-/

module

public import LeanVM.Guest.B1.Digest.CompleteSmall

/-!
# `cover_da_root`, completely

`cover_da_root(roots, cover, g^n, mark)` hints the slot `i`, range-checks `g^i` against `g^n`
(two reads, at `g^i` and `g^(n-1-i)`, defined on a memory image of at least `2^16` words when
`n ≤ 2^16`), reads `mark` at `cover·g^i` and returns the four words at `roots·g^(4i)`.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `cover_da_root`'s meaning, for a slot within the memory, gives its core IR. -/
def cover_da_root_complete_Spec : Prop :=
  ∀ (rd : Reader), MemOk rd → ∀ (roots cover mark : E) (n i : ℕ) (rets : List E),
    n ≤ 2 ^ 16 → i < n → LoadHolds rd cover i mark → rets.length = 4 →
    (∀ c < 4, LoadHolds rd roots (4 * i + c) (rets.getD c 0)) →
    coreProgram.Rel rd "cover_da_root" [roots, cover, gen ^ n, mark] rets

theorem gen_pow_mul_ginv {n : ℕ} (hn : 1 ≤ n) : gen ^ n * ginvW = gen ^ (n - 1) := by
  conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ, mul_assoc, mul_comm gen, ginvW_mul_gen,
    mul_one]

/-- **`cover_da_root` is complete.** -/
theorem cover_da_root_complete : cover_da_root_complete_Spec := by
  intro rd hm roots cover mark n i rets hn hi hmark hl hrets
  match rets, hl, hrets with
  | [r0, r1, r2, r3], _, hrets =>
    obtain ⟨t1, h1⟩ := load_gen hm (i := i) (by omega)
    obtain ⟨t2, h2⟩ := load_gen hm (i := n - 1 - i) (by omega)
    have h4 : roots * ((gen ^ i * gen ^ i) * (gen ^ i * gen ^ i)) = roots * gen ^ (4 * i) := by
      simp only [← pow_add]; congr 2; ring
    have hload : ∀ c < 4, LoadHolds rd (roots * ((gen ^ i * gen ^ i) * (gen ^ i * gen ^ i))) c
        ([r0, r1, r2, r3].getD c 0) := by
      intro c hc
      rw [h4, loadHolds_mul_gen_pow]
      exact hrets c hc
    refine (rel_iff_sem find_cover_da_root _ _).mpr ⟨Val.ofArgs [roots, cover, gen ^ n, mark,
      gen ^ i, ginvW, gen ^ n * ginvW, gen ^ (n - 1 - i), t1, t2, cover * gen ^ i,
      gen ^ i * gen ^ i, (gen ^ i * gen ^ i) * (gen ^ i * gen ^ i),
      roots * ((gen ^ i * gen ^ i) * (gen ^ i * gen ^ i)), r0, r1, r2, r3], rfl, ?_⟩
    rw [core30_body]
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, ofArgs_n,
      List.getD_cons_succ, List.getD_cons_zero]
    refine ⟨trivial, trivial, trivial, ⟨h1, ?_, h2⟩, trivial, ?_, trivial, trivial, trivial,
      hload 0 (by omega), hload 1 (by omega), hload 2 (by omega), hload 3 (by omega), trivial⟩
    · rw [gen_pow_mul_ginv (by omega), ← pow_add]; congr 1; omega
    · rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact hmark

end
end LeanVM.Guest.B1.Digest
