/-
  LeanVM.Guest.B1.Bits.Tables

  B1 for `exponent_tables`: the two read-only tables over the exponent domain.
-/

module

public import LeanVM.Guest.B1.Bits.Meaning

/-!
# `exponent_tables` (G:645-660, TRIAGE #16)

`exponent_tables()` fills two fresh `HeapBuf(34)` tables: `g_logs_pow2[g^j] = E(2^j)` and
`g_squares[g^j] = g^(2^j)`, the second's constants folded by the compiler (`gSquaresBits`,
checked against the squares of `g` by kernel decision, through `squares`, one squaring an entry).
Ported from the BLAKE2s-era `Value/Tables.lean` and `B1/Tables.lean` (the function is unchanged).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The squares of `g` -/

/-- `n` successive squares from `x`: `x, x², x⁴, …`, as `sq_run *= sq_run` computes them. -/
def squares {R : Type} [Mul R] : ℕ → R → List R
  | 0, _ => []
  | n + 1, x => x :: squares n (x * x)

theorem length_squares {R : Type} [Mul R] (n : ℕ) (x : R) : (squares n x).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [squares, ih]

/-- Entry `j` of the squares from `x` is `x^(2^j)`. -/
theorem getElem_squares {R : Type} [Monoid R] (n : ℕ) (x : R) (j : ℕ)
    (hj : j < (squares n x).length) : (squares n x)[j] = x ^ 2 ^ j := by
  induction n generalizing x j with
  | zero => simp [squares] at hj
  | succ n ih =>
    cases j with
    | zero => simp [squares]
    | succ j =>
      simp only [squares, List.getElem_cons_succ]
      rw [ih (x * x) j (by simpa [squares] using hj), ← sq, ← pow_mul, pow_succ, Nat.mul_comm]

/-- `g^(2^j)` for `j < 34`, as 64-bit words. -/
def gSquaresBits : List ℕ := [
  0x2, 0x4, 0x10, 0x100, 0x10000, 0x100000000, 0x1b, 0x145, 0x11011, 0x101000101,
  0x100000001001a, 0x1a00000144, 0x10dbc, 0x100514550, 0x11011011111b, 0x10001011a1a015e,
  0x15f0144001a114f, 0x1aad43011ba1e5, 0x11cefef6be466, 0x5455145e48670f13,
  0xbaf1bebe1ae4ad02, 0xb0ef530df44bb042, 0xe2170b43ee771735, 0x48380fd207a3b527,
  0xb6d535c542116f62, 0xa6df6baa62f965f5, 0xb9df3947cea0ffe7, 0xe1882807248fe588,
  0x180d86953ed141c6, 0x1894566cd1db8abf, 0x4cc78bf4ea999e25, 0xe333308087e402ba,
  0x5c62236777028505, 0xb964dc682c67ddcd]

/-- The words are the squares of `g`, decided by the kernel over `squares`. -/
theorem gSquaresBits_eq : gSquaresBits.map K.ofBits = squares sizeBits g := by decide +kernel

theorem length_gSquaresBits : gSquaresBits.length = sizeBits := rfl

/-- **The `g_squares` constants**: word `j < 34` is `g^(2^j)` in `K`. -/
theorem ofBits_gSquaresBits (j : ℕ) (hj : j < sizeBits) :
    K.ofBits (gSquaresBits.getD j 0) = g ^ 2 ^ j := by
  have h := congrArg (fun l : List K ↦ l[j]?) gSquaresBits_eq
  have hj1 : j < gSquaresBits.length := by rw [length_gSquaresBits]; exact hj
  have hj2 : j < (squares sizeBits g).length := by rw [length_squares]; exact hj
  simp only [List.getElem?_map, List.getElem?_eq_getElem hj1, List.getElem?_eq_getElem hj2,
    Option.map_some, Option.some.injEq, getElem_squares] at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj1, Option.getD_some, h]

/-- The same in `E`: the cell `E(word j)` is `GEN^(2^j)`. -/
theorem eOfNat_gSquaresBits (j : ℕ) (hj : j < sizeBits) :
    eOfNat (gSquaresBits.getD j 0) = gen ^ 2 ^ j := by
  rw [eOfNat, ofBits_gSquaresBits j hj, ofK_pow]
  rfl

/-! ## The function -/

/-- `g_logs_pow2[g^j] = 2^j`. -/
def etBlk1 (j : ℕ) : List Stmt :=
  [.atom (.const (.n (1 + j)) (word (2 ^ j) 0 0)), .atom (.load (.n (1 + j)) (.n 0) j)]

/-- `g_squares[g^j] = g^(2^j)`, folded. -/
def etBlk2 (j : ℕ) : List Stmt :=
  [.atom (.const (.n (36 + j)) (word (gSquaresBits.getD j 0) 0 0)),
    .atom (.load (.n (36 + j)) (.n 35) j)]

/-- The expansion of `exponent_tables`. -/
def etBody : List Stmt :=
  [.atom (.hint (.alloc (.n 0) 34))] ++ ((List.range 34).map etBlk1).flatten ++
  [.atom (.hint (.alloc (.n 35) 34))] ++ ((List.range 34).map etBlk2).flatten ++
  [.atom (.copy (.n 70) (.n 0)), .atom (.copy (.n 71) (.n 35)), .ret [.n 70, .n 71]]

theorem core2_body : Fn.body Data.core2 = etBody := stmtsEqb_sound (by decide +kernel)

theorem find_exponent_tables : coreProgram.find? "exponent_tables" = some Data.core2 :=
  Program.find?_of_indexOf? (j := 2) (by decide +kernel) rfl

/-- **`exponent_tables`' core IR is its meaning.** -/
theorem exponent_tables_holds : exponent_tables_Spec := by
  intro rd args rets
  rw [rel_iff_sem find_exponent_tables, core2_body, show Fn.params Data.core2 = [] from rfl, etBody]
  simp only [holdsList_append, Stmt.HoldsList]
  simp only [holdsList_range_flatten 34 etBlk1 (fun _ => rfl),
    holdsList_range_flatten 34 etBlk2 (fun _ => rfl), etBlk1, etBlk2]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, true_and,
    and_true]
  constructor
  · rintro ⟨σ, hp, ht1, ht2, h70, h71, hret⟩
    subst hp hret
    intro j hj
    obtain ⟨c1, l1⟩ := ht1 j hj
    obtain ⟨c2, l2⟩ := ht2 j hj
    rw [h70, h71]
    rw [c1, word_eOfNat] at l1
    rw [c2, word_eOfNat, eOfNat_gSquaresBits j hj] at l2
    exact ⟨l1, l2⟩
  · intro hm
    obtain ⟨rfl, p, q, rfl, ht⟩ : args = [] ∧ ∃ p q, rets = [p, q] ∧ ExpTables rd p q := by
      match args, rets, hm with
      | [], [p, q], h => exact ⟨rfl, p, q, rfl, h⟩
    refine ⟨setl (setv (setl (setv (setl (Val.ofArgs []) 0 [p]) 1 34 fun j => word (2 ^ j) 0 0) 35
      [q]) 36 34 fun j => word (gSquaresBits.getD j 0) 0 0) 70 [p, q], rfl, fun j hj => ?_,
      fun j hj => ?_, ?_, ?_, ?_⟩
    all_goals (try b1_look)
    · rw [word_eOfNat]; exact ⟨trivial, (ht j hj).1⟩
    · rw [word_eOfNat, eOfNat_gSquaresBits j hj]; exact ⟨trivial, (ht j hj).2⟩

end
end LeanVM.Guest.B1
