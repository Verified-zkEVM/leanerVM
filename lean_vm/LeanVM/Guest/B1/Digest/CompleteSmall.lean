/-
  LeanVM.Guest.B1.Digest.CompleteSmall

  Completeness of the small digest functions: a meaning (and the memory an honest run reads) gives
  the core IR relation.
-/

module

public import LeanVM.Guest.B1.Digest.Range
public import LeanVM.Guest.B1.Sig.CwComplete

/-!
# Small functions, completely

* `memOK_of_memOk`: a memory image of `2^κ ≥ 2^16` words is defined at every `g^i`, `i < 2^16`
  (B1-e's `MemOK`), so a range check of `g^k` against `g^(K-1)`, `K ≤ 2^16`, reads defined words
  (`rc_holds`);
* `list_split_complete : list_split_complete_Spec`.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

theorem memOK_of_memOk (hm : MemOk rd) : Sig.MemOK rd (2 ^ 16) := by
  obtain ⟨κ, h16, hκ, L, rfl⟩ := hm
  intro i hi
  have hi' : i < 2 ^ κ := lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) h16)
  exact Option.isSome_iff_exists.mpr ⟨L ⟨i, hi'⟩, (read_some_iff (by omega) L _ _).mpr ⟨⟨i, hi'⟩, rfl, rfl⟩⟩

/-- **A range check of `g^k` against `g^K` holds** on a memory defined below `2^16`, `k ≤ K < 2^16`,
its witness `g^(K - k)`. -/
theorem rc_holds' (hm : Sig.MemOK rd (2 ^ 16)) {k K : ℕ} (hk : k ≤ K) (hK : K < 2 ^ 16) :
    ∃ t1 t2, LoadHolds rd (gen ^ k) 0 t1 ∧ gen ^ K = gen ^ k * gen ^ (K - k) ∧
      LoadHolds rd (gen ^ (K - k)) 0 t2 := by
  obtain ⟨t1, h1⟩ : ∃ w, LoadHolds rd (gen ^ k) 0 w := by
    rw [gen_pow_eq_ofK]; exact Sig.load_gpow hm (show k < 2 ^ 16 by omega)
  obtain ⟨t2, h2⟩ : ∃ w, LoadHolds rd (gen ^ (K - k)) 0 w := by
    rw [gen_pow_eq_ofK]; exact Sig.load_gpow hm (show K - k < 2 ^ 16 by omega)
  exact ⟨t1, t2, h1, by rw [← pow_add]; congr 1; omega, h2⟩

/-- **`list_split` is complete** on a memory defined below `2^16`. -/
theorem list_split_complete' (rd : Reader) (hm : Sig.MemOK rd (2 ^ 16)) (args rets : List E)
    (h : MeaningListSplit args rets) : coreProgram.Rel rd "list_split" args rets := by
  match args, h with
  | [ng], h =>
    obtain ⟨a, ha, b, hb, hng, hrets⟩ := h
    simp only [maxKeys] at ha
    simp only [claimGroup] at hb hng
    obtain ⟨t1, t2, h1, e1, h2⟩ := rc_holds' hm (k := b) (K := 16) (by omega) (by norm_num)
    obtain ⟨t3, t4, h3, e2, h4⟩ := rc_holds' hm (k := a) (K := 65535) (by omega) (by norm_num)
    refine (rel_iff_sem find_list_split _ _).mpr ⟨Val.ofArgs [ng, gen ^ a, gen ^ b, word 65536 0 0,
      gen ^ (16 - b), t1, t2, word 9272771591053052074 0 0, gen ^ (65535 - a), t3, t4, gen ^ (2 * a),
      gen ^ (4 * a), gen ^ (8 * a), gen ^ (16 * a), gen ^ (17 * a), gen ^ (17 * a + b), gen ^ a,
      gen ^ b], rfl, ?_⟩
    rw [core22_body]
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, ofArgs_n]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    refine ⟨trivial, trivial, ⟨h1, by rw [word_g16, e1], h2⟩, trivial, ⟨h3, by rw [word_gmax, e2], h4⟩,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial, trivial, ?_⟩
    · rw [← pow_add]; congr 1; ring
    · rw [← pow_add]; congr 1; ring
    · rw [← pow_add]; congr 1; ring
    · rw [← pow_add]; congr 1; ring
    · rw [← pow_add]; congr 1; ring
    · rw [← pow_add]
    · rw [hng]; exact e_add_eq_zero_iff.mpr rfl
    · exact hrets.symm
  | [], h => exact h.elim
  | _ :: _ :: _, h => exact h.elim

end
end LeanVM.Guest.B1.Digest
