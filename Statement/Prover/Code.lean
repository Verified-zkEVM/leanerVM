module

public import Statement.Field
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Pi

/-!
# The code's formulas

leanVM's binary Reed-Solomon code (Annex D, `doc/leanvm/body/d-novel-basis.tex:2-46` at leanVM
pin `127510d14c98ade4e8a97646c44fa7f1ff5e752d`) as the formulas that define its codewords at every
position: the subspace polynomials `W_i`, their normalizations `Ŵ_i`, the novel basis
`X_j = ∏_i Ŵ_i^{j_i}`, the encoder `Enc(g)` at `x_p = K.ofBits p`, and a WHIR level's word. The
committed words (`Ntt.lean`) take these values above the positions a run reads, which they never
evaluate (`O(4^κ)` per position).
-/

@[expose] public section

namespace LeanVM.Protocol.Whir

open LeanVM.Parameters

/-- `e_c = x^c`, the word with the single bit `c`. -/
def basisVec (c : ℕ) : K := K.ofBits (2 ^ c)

/-- `W_i(a)`, the subspace polynomial `W_i(X) = ∏_{u ∈ U_i} (X + u)` of
`U_i = ⟨e_0, …, e_{i-1}⟩_{F₂}` at `a`, as the product over the words `v < 2^i`. -/
def vanishingAt (i : ℕ) (a : K) : K := ∏ v ∈ Finset.range (2 ^ i), (a + K.ofBits v)

/-- `Ŵ_i(a) = W_i(a) / W_i(e_i)`. The hat is normalization, not multilinear extension. -/
def normVanishingAt (i : ℕ) (a : K) : K := vanishingAt i a * (vanishingAt i (basisVec i))⁻¹

/-- `⟨u⟩ = Σ_i u_i 2^i`, the integer whose bits are `u`, bit `0` first. -/
def bitsToNat {κ : ℕ} (u : Fin κ → Bool) : ℕ := ∑ i, (u i).toNat * 2 ^ (i : ℕ)

/-- `X_j(a)`, the novel basis polynomial `X_j = ∏_i Ŵ_i^{j_i}` at `a`, over the 64 bits a word
can have. -/
def novelAt (j : ℕ) (a : K) : K :=
  ∏ i ∈ Finset.range 64, if j.testBit i then normVanishingAt i a else 1

end LeanVM.Protocol.Whir

namespace LeanVM.Protocol.Whir.Complete

open LeanVM.Parameters LeanVM.Protocol.Whir

/-- `Enc(g)` at the domain point `x_p = K.ofBits p`, for every `p`. -/
def encAt (κ : ℕ) (g : (Fin κ → Bool) → E) (p : ℕ) : E :=
  ∑ u, g u * ofK (novelAt (bitsToNat u) (K.ofBits p))

/-- The encoder on a `K`-valued message, at a position. -/
def encKAt (κ : ℕ) (g : (Fin κ → Bool) → K) (p : ℕ) : K :=
  ∑ u, g u * novelAt (bitsToNat u) (K.ofBits p)

/-- Lane `j` of a table cut along its first `k` variables: `x ↦ t[j + 2^k·⟨x⟩]`. -/
def laneMsg (κ k : ℕ) (t : List E) (j : ℕ) : (Fin κ → Bool) → E :=
  fun x ↦ t.getD (j + 2 ^ k * bitsToNat x) 0

/-- The `2^k` lanes' codeword entries at the position `p`. -/
def laneCodes (κ k : ℕ) (t : List E) (p : ℕ) : List E :=
  (List.range (2 ^ k)).map fun j ↦ encAt κ (laneMsg κ k t j) p

/-- The three limbs of an entry, the order `_ext_row` reads them. -/
def limbsOf (e : E) : List K := [e.limb 0, e.limb 1, e.limb 2]

/-- A deeper level's word (a `Word`): leaf `p` holds the `2^k` lanes' entries at `x_p`, three
limbs each. -/
def levelWord (κ k : ℕ) (g : List E) : ℕ → List K :=
  fun p ↦ (laneCodes κ k g p).flatMap limbsOf

end LeanVM.Protocol.Whir.Complete

end
