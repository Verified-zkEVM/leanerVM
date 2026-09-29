import LeanerVM.Parameters.Field
import LeanerVM.Parameters.Generator

/-!
Probe `FieldFidelity`: leanerVM's `K` and `E` compute the same products as the pinned Rust on
the Rust's own reference vectors (`crates/primitives/src/field/gf2_64.rs:271-275`,
`gf2_64x3.rs:991-1016`), and the numerals of `K` are bit patterns.
-/

open LeanerVM.Parameters

/-! ## Base field: the three `(a, b, a·b)` vectors of `gf2_64.rs:271-275` -/

#guard (0x01090913877ed8ed : K) * 0x66ab35ac2768468f = 0x50c4519dc383744a
#guard (0xa7715ae18f12a3b5 : K) * 0x05743059f43fa4f5 = 0xeb64cd9cd9cda6df
#guard (0xbd3efb4705e79ddd : K) * 0x3aff618604de4ae0 = 0xc3d7a95fa9cb59bb
-- a mutated product is rejected
#guard (0x01090913877ed8ed : K) * 0x66ab35ac2768468f ≠ 0x50c4519dc383744b
-- the reduction constant: x^63 · x = x^64 = x^4 + x^3 + x + 1 = 0x1B
#guard (0x8000000000000000 : K) * 0x2 = 0x1B
-- addition is XOR
#guard (0x01090913877ed8ed : K) + 0x66ab35ac2768468f = 0x01090913877ed8ed ^^^ 0x66ab35ac2768468f
-- inversion, and `0⁻¹ = 0` as in the Rust (`gf2_64.rs:42`, `:318`)
#guard (0x01090913877ed8ed : K) * (0x01090913877ed8ed : K)⁻¹ = 1
#guard (0 : K)⁻¹ = 0

/-! ## Extension: the four `(a, b, a·b, a·a)` vectors of `gf2_64x3.rs:991-1016` -/

def a1 : E := E.ofLimbs 0x950e87d7f5606615 0x2c61275c9e6b6cf8 0x1f00bca0042db923
def b1 : E := E.ofLimbs 0x6dbca290a9eab706 0x4c10a4fe30cffdda 0xf26fff4cc4fd394d
def c1 : E := E.ofLimbs 0x888a0fc35abaf5f6 0x68a84cbc132b0649 0x9fdeaf613003cabe
def s1 : E := E.ofLimbs 0x8fba131ad5d46b8c 0x1c170457f537a805 0x3632cc098ca15135
def a2 : E := E.ofLimbs 0x6814a2bc786a6d2d 0xa26b351e6c8042c5 0x54760e7fbc051c6c
def b2 : E := E.ofLimbs 0xd4c08880a5a4666d 0x29610ae0eed8f1e7 0xc34bd8e2fe5213e5
def c2 : E := E.ofLimbs 0x2ad322ebf2f9043b 0x8ac800aa67154c80 0x6d0f76651d3c4d0c
def s2 : E := E.ofLimbs 0xcf800ef2b83bb43a 0xefe1c6cd064dd44c 0x57dc5c7a60e2981b
def a3 : E := E.ofLimbs 0x6c50afb6e9fb123d 0x6f28d015a2aa0b9d 0x4e385994ebac94af
def b3 : E := E.ofLimbs 0x194f9545adba52ce 0xc675ce05588f882f 0x57de8c051d4b7ef2
def c3 : E := E.ofLimbs 0xea6b9f9d23d4a1ff 0xd82aa6058c431457 0x5fd4d8fda2f1e74a
def s3 : E := E.ofLimbs 0x8f30fe43aa05b396 0xe3593591eccd9efe 0x7c5a1b128788c51f
def a4 : E := E.ofLimbs 0xd998efd82733e933 0x6df216c33f8f3201 0x11dc6f3fcb57d5d8
def b4 : E := E.ofLimbs 0x8860a84722025e05 0x33176469aa6ef630 0x607507ebc5b864d7
def c4 : E := E.ofLimbs 0xfa3a0d66cdfbc1b3 0xbd47bd3343aad307 0xdaf50186477f6a77
def s4 : E := E.ofLimbs 0x69c8d8c24f416884 0x4b597d648a162147 0x95603a5d95c9512a

#guard a1 * b1 = c1
#guard a1 * a1 = s1
#guard a2 * b2 = c2
#guard a2 * a2 = s2
#guard a3 * b3 = c3
#guard a3 * a3 = s3
#guard a4 * b4 = c4
#guard a4 * a4 = s4
-- a mutated limb is rejected
def c1' : E := E.ofLimbs 0x888a0fc35abaf5f6 0x68a84cbc132b0649 0x9fdeaf613003cabf
#guard a1 * b1 ≠ c1'
-- the defining relation, as the Rust checks it (`gf2_64x3.rs:1026`)
#guard y * y * y = y + 1
-- `y` is the limb vector `(0, 1, 0)` (`F192::Y`, `gf2_64x3.rs:45`)
def yLimbs : E := E.ofLimbs 0 1 0
#guard y = yLimbs
-- the inverse in `E`
#guard a1 * a1⁻¹ = 1

/-! ## The generator -/

#guard g = (2 : K)
#guard g * g = (4 : K)

/-! ## Numerals of `K` are bit patterns, not casts of natural numbers -/

-- the numeral `2 : K` is the element `x`, and is not zero
#guard (2 : K) ≠ 0
-- whereas the cast of the natural number two is zero (characteristic two)
#guard ((2 : ℕ) : K) = 0
#guard (1 : K) + 1 = 0
#guard (2 : K) ≠ ((2 : ℕ) : K)
#guard (3 : K) = (2 : K) + 1
-- the numeral elaborates through `BitVec`'s instance
set_option pp.explicit true in
#check (2 : K)

/-! ## `K` is `BitVec 64` to instance search: which `+` does a `BitVec 64` get? -/

def u : BitVec 64 := 3
def v : BitVec 64 := 5
-- with CompPoly's field in scope, `+` on `BitVec 64` is XOR (3 + 5 = 6), not addition mod 2^64 (8)
#eval u + v
#eval (u + v == 8, u + v == 6)
#eval u * v
set_option pp.explicit true in
#check u + v
-- at another width the core instance is found
def u32 : BitVec 32 := 3
def v32 : BitVec 32 := 5
#eval u32 + v32

#synth Add (BitVec 64)
#synth Mul (BitVec 64)
#synth Add (BitVec 32)
#synth Fintype (BitVec 64)
#synth LawfulBEq K
#synth LawfulBEq E
