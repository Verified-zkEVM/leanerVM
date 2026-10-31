module

public import Statement.Keccak
public import CompPoly.Fields.Binary.BF64
public import CompPoly.Fields.Extension
public import Statement.Fast.FieldWords
public import Statement.Fast.CubicExt
public import Statement.Fast.Keccak

/-!
# The fields

`K = GF(2^64)`, `E = GF(2^192)` and the generator `g` of leanVM (specification §2,
`doc/leanvm/body/02-vm-specification.tex:6-12`), on CompPoly's computable carriers:

```text
K = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)      CompPoly's BF64
E = K[y]/(y^3 + y + 1)                       CompPoly's BF64.Ext3
g = x                                        a generator of K^× (order 2^64 - 1)
```

`K` wraps a `BitVec 64` whose bit `i` is the coefficient of `x^i`; `E` is a `Vector K 3` whose
limb `i` is the coefficient of `y^i`. Natural-number casts follow characteristic two
(`2 : K = 0`); wire words go through `K.ofBits`. Then the field encodings of Keccak
(`verifier.py`): a lane as a `K` word, a `K` word as bytes, the Merkle leaf hash of words, and a
digest as two `E` elements.
-/

@[expose] public section

namespace LeanVM.Parameters

open CompPoly.Extension

/-- `K = GF(2^64)`, CompPoly's `BF64`. -/
abbrev K : Type := BF64

/-- Decode a polynomial-basis word, reducing its integer representation modulo `2^64`.
This is a wire encoding, distinct from the characteristic-two natural-number cast. -/
def K.ofBits (n : ℕ) : K := BF64.ofBitVec (BitVec.ofNat 64 n)

/-- Decide equality through bit coordinates, keeping kernel comparisons of computed words
free of the dependent transport introduced by the upstream derived instance. -/
instance instDecidableEqK : DecidableEq K := fun a b ↦
  decidable_of_iff (a.toBitVec = b.toBitVec) BF64.toBitVec_injective.eq_iff

/-- `E = K[y]/(y^3 + y + 1)`, CompPoly's `BF64.Ext3`. -/
abbrev E : Type := BF64.Ext3

/-- The embedding `K ↪ E` as the `y^0` limb; it is `algebraMap K E` by `rfl`. -/
abbrev ofK (a : K) : E := Ext.ofBase a

/-- Limb `i` of a word: the coefficient of `y^i`. -/
abbrev E.limb (x : E) (i : Fin 3) : K := Ext.coeff x i

/-- The word `c0 + c1·y + c2·y²`. -/
def E.ofLimbs (c0 c1 c2 : K) : E := Ext.ofVector #v[c0, c1, c2]

/-- A word lies in `K`: its `y` and `y²` limbs are zero. -/
def IsInK (x : E) : Prop := x.limb 1 = 0 ∧ x.limb 2 = 0

/-- A canonical 128-bit word: its `y²` limb is zero. -/
def IsCanonical128 (x : E) : Prop := x.limb 2 = 0

instance : DecidablePred IsInK :=
  fun x ↦ inferInstanceAs (Decidable (x.limb 1 = 0 ∧ x.limb 2 = 0))

instance : DecidablePred IsCanonical128 :=
  fun x ↦ inferInstanceAs (Decidable (x.limb 2 = 0))

/-- `g = x`, the word `0x2` (`crates/primitives/src/field/gf2_64.rs:25`, `F64::G = F64(2)`;
`python-verifier/verifier.py:181`, `GEN = E(2)`). Its order `2^64 - 1` is proved
(`orderOf_g`), not assumed. -/
def g : K := K.ofBits 0x2

/-- Exponent addressing: index `i` is the address `g ^ i`. -/
abbrev gpow (i : ℕ) : K := g ^ i

/-- A `K` word from a 64-bit lane: bit `i` of the lane is the coefficient of `x^i`. -/
def K.ofLane (w : UInt64) : K := BF64.ofBitVec w.toBitVec

/-- The 64-bit lane of a `K` word (`K.__index__`). -/
def K.lane (a : K) : UInt64 := ⟨a.toBitVec⟩

end LeanVM.Parameters

namespace LeanVM.Protocol.KeccakHash

open LeanVM.Parameters LeanVM.Semantics

/-- The eight little-endian bytes of a `K` word (`K.to_bytes`, `verifier.py:50-52`). -/
def kBytes (a : K) : List UInt8 := wordBytes a.lane

/-- The digest of a Merkle leaf: Keccak-256 of its words as bytes (`Transcript.merkle`,
`verifier.py:433-445`). -/
def hashWords (words : List K) : Digest := keccak256 (words.flatMap kBytes)

/-- A digest as the two field elements a transcript carries it in, its 128-bit halves
`E(w0, w1)`, `E(w2, w3)` (`Digest.halves`, `verifier.py:225-228`). -/
def digestScalars (d : Digest) : E × E :=
  (E.ofLimbs (K.ofLane d[0]) (K.ofLane d[1]) 0, E.ofLimbs (K.ofLane d[2]) (K.ofLane d[3]) 0)

/-- The digest two field elements encode, or `none` if either has a nonzero top limb
(`Digest.from_halves`, `verifier.py:230-233`). -/
def digestOfScalars (s : E × E) : Option Digest :=
  if IsCanonical128 s.1 ∧ IsCanonical128 s.2 then
    some #v[(s.1.limb 0).lane, (s.1.limb 1).lane, (s.2.limb 0).lane, (s.2.limb 1).lane]
  else none

end LeanVM.Protocol.KeccakHash

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters

/-- The Python `E(n)`: the 64-bit word `n` in limb `0` (`verifier.py:97-100`). -/
def eOfNat (n : ℕ) : E := ofK (K.ofBits n)

/-- `GEN = E(2)`, the generator `x` whose powers index the bytecode and the memory
(`verifier.py:181`): `g` in limb `0`. -/
def gen : E := eOfNat 2

end LeanVM.Protocol.Verifier

end
