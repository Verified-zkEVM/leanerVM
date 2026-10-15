/-
  LeanerVMTests.Protocol.NovelBasis

  The subspace roots, the normalized subspace polynomials, the encoder and the column weights
  against the pinned Python verifier, and the readings that compile and are wrong.
-/

module

public import LeanerVM.Protocol.NovelBasis
meta import LeanerVM.Protocol.NovelBasis

/-!
# Novel basis, encoder and column weights: tests

The tables below are the output of the pinned verifier (`python-verifier/verifier.py` at leanVM
`a386121f84292f6fa663aaa3e570c15bc0240ea2`), run on the functions the module transcribes:
`_subspace_roots` for the roots `V_k(e_k)`, the loop of `_induced_weight` for `Ŵ_k(x)`, and
`_induced_weight` itself, one query with weight one, for the column weight's extension at a
random point of `E^κ` (seed `20261015`). The deployed Rust (`AdditiveNttF64::standard`) is the
other implementation of the roots and is not run here.
-/

namespace LeanerVMTests.Protocol

open LeanerVM.Parameters LeanerVM.Protocol CompPoly

public section

/-! ## The pinned verifier's output -/

/-- `V_k(e_k)` for `k = 0 .. 8`: `_subspace_roots(9)` of the pinned verifier. -/
def pythonRoots : List K :=
  [K.ofBits 0x1, K.ofBits 0x6, K.ofBits 0x168, K.ofBits 0x1166880, K.ofBits 0x11616686880801b, K.ofBits 0x726b6e3c6e39234e, K.ofBits 0x796adf34d64462c2, K.ofBits 0xf1060866be6fa9c, K.ofBits 0x6a06f1b0a76acb05, K.ofBits 0xd2d14e471a7186d9]

/-- `(x, [Ŵ_0(x), ..., Ŵ_7(x)])`, the `basis * inverse` of `_induced_weight`'s loop. -/
def pythonNormW : List (ℕ × List K) :=
  [
  (0x0, [K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0]),
  (0x1, [K.ofBits 0x1, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0]),
  (0x2, [K.ofBits 0x2, K.ofBits 0x1, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0]),
  (0x3, [K.ofBits 0x3, K.ofBits 0x1, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0]),
  (0x5, [K.ofBits 0x5, K.ofBits 0x6, K.ofBits 0x1, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0]),
  (0x1f, [K.ofBits 0x1f, K.ofBits 0x63, K.ofBits 0x16b, K.ofBits 0x117, K.ofBits 0x1, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0]),
  (0x123456789abcdef, [K.ofBits 0x123456789abcdef, K.ofBits 0x9f946d99ec181e18, K.ofBits 0x81568a22d86fe025, K.ofBits 0xd7bf72d10f546b54, K.ofBits 0xb8d9cc984af7499b, K.ofBits 0x539079febe7a07ab, K.ofBits 0xdf89cdbf0a1cf71, K.ofBits 0x60677f7b98939edc]),
  (0xdeadbeefcafef00d, [K.ofBits 0xdeadbeefcafef00d, K.ofBits 0xd0d76026f2ae5372, K.ofBits 0x70f320f5fc74343d, K.ofBits 0xf304ad68421141bd, K.ofBits 0x117bc68020dfb8c4, K.ofBits 0x8ca90c0117334e6a, K.ofBits 0x5e72f934d646183e, K.ofBits 0x4d0062a94408d3b8]),
  (0x8000000000000001, [K.ofBits 0x8000000000000001, K.ofBits 0xe000000000000012, K.ofBits 0x8e0000000000001a, K.ofBits 0xe38e000000000009, K.ofBits 0x8e38e38e0000000d, K.ofBits 0xe38e38e38e38e386, K.ofBits 0x2e12e12e12e12e11, K.ofBits 0xb50c27b50c27b503]),
  (0xffffffffffffffff, [K.ofBits 0xffffffffffffffff, K.ofBits 0xccccccccccccccdb, K.ofBits 0x1d1d1d1d1d1d1d0a, K.ofBits 0xf4e9f4e9f4e9f4e1, K.ofBits 0xce9d3a74ce9d3a7f, K.ofBits 0x1d3a74e9d3a74e9c, K.ofBits 0x3b25ec97b25ec979, K.ofBits 0x13912ba83912ba82])]

/-- `(κ, query, point, value)`: `_induced_weight(κ, [query], [1], point)`. -/
def pythonWeights : List (ℕ × ℕ × List E × E) :=
  [
  (3, 0x5,
    [E.ofLimbs (K.ofBits 0x361424b1ea125c50) (K.ofBits 0x70b50ecb32ccd896) (K.ofBits 0x2ae66617b21822c), E.ofLimbs (K.ofBits 0xd2db9299d1e8e1ba) (K.ofBits 0x7a615de0a514e83) (K.ofBits 0x31b066ce9c2b9de1), E.ofLimbs (K.ofBits 0xd3e9b4ad86719d9f) (K.ofBits 0xe33fcca66c2aaff5) (K.ofBits 0x928c1b4a654f8125)],
    E.ofLimbs (K.ofBits 0x7afb3eb1c12f4c00) (K.ofBits 0xa08169897fb5127a) (K.ofBits 0xe413e39f7c1dea7a)),
  (4, 0x2b,
    [E.ofLimbs (K.ofBits 0xb06dcebba7113812) (K.ofBits 0xcb49fc7dfaf5c15c) (K.ofBits 0xa72b8bd5a19692a6), E.ofLimbs (K.ofBits 0xe6950292a732c6f1) (K.ofBits 0x648115bcfec2e632) (K.ofBits 0x3b993d36d4a45401), E.ofLimbs (K.ofBits 0xfa7802bbca2a86a8) (K.ofBits 0xafc725d37f66a51a) (K.ofBits 0xe8016b4eda3eab41), E.ofLimbs (K.ofBits 0xfd23dfb60ede7050) (K.ofBits 0x8d4129f93bf22a2e) (K.ofBits 0xfb7a0722e128074)],
    E.ofLimbs (K.ofBits 0xbcf506d443b56fce) (K.ofBits 0x9d5472d89886eda3) (K.ofBits 0xd9799a1eb237160f)),
  (6, 0x1d3,
    [E.ofLimbs (K.ofBits 0xa88bd675fda43ae7) (K.ofBits 0x111b0bb9456c00bc) (K.ofBits 0xad69f59859edf9ae), E.ofLimbs (K.ofBits 0x3ce7fcb2ee1d8531) (K.ofBits 0x9e607c80452118b5) (K.ofBits 0x2d1874c9640e77fc), E.ofLimbs (K.ofBits 0x60177bdd90292e1) (K.ofBits 0xb006b9c20ba36864) (K.ofBits 0xf0722929d091aa6e), E.ofLimbs (K.ofBits 0xe5c97947ecb13eb4) (K.ofBits 0x6614e2cd2c76d7) (K.ofBits 0x708929ef89a332da), E.ofLimbs (K.ofBits 0x2aaa21516cda3f0c) (K.ofBits 0x3452eb3e2dae1ec) (K.ofBits 0x9c2f44bfa55e0c92), E.ofLimbs (K.ofBits 0x721efeaba9019582) (K.ofBits 0xeb7d6cb7f10daa7) (K.ofBits 0xb8af88f41d45c180)],
    E.ofLimbs (K.ofBits 0xdcc5264744c821d3) (K.ofBits 0x5f3b77cafcde177f) (K.ofBits 0x22bf9deddc893a11)),
  (8, 0xdeadbeefcafef00d,
    [E.ofLimbs (K.ofBits 0xdbd58b9a11bec511) (K.ofBits 0x889416c630c77ba8) (K.ofBits 0xf518dcbe09842215), E.ofLimbs (K.ofBits 0x8eeea67c70e211f7) (K.ofBits 0xc336656ae155fccc) (K.ofBits 0x792ef24334339aaf), E.ofLimbs (K.ofBits 0x77f8c46004b3fd27) (K.ofBits 0xea7ddb3ef1de3787) (K.ofBits 0x2f452ba38fb87e6e), E.ofLimbs (K.ofBits 0x45ac9a94950adf49) (K.ofBits 0xd36a2a60b6372aec) (K.ofBits 0xd0d8d794fa3721db), E.ofLimbs (K.ofBits 0x3f6aa289fe870dba) (K.ofBits 0x2234504961382b72) (K.ofBits 0xf0bf1ab5ed7eaac5), E.ofLimbs (K.ofBits 0xd33c1920b741f9da) (K.ofBits 0x1905af2e221bfb18) (K.ofBits 0x8421ae84e1f5e4e), E.ofLimbs (K.ofBits 0x62ac6354086afd9d) (K.ofBits 0xfcfab40e839e1ee2) (K.ofBits 0xda1720d35a351b8b), E.ofLimbs (K.ofBits 0x69c301913d617ead) (K.ofBits 0xb33c5fc79cc9eaf1) (K.ofBits 0x7744ca7074615814)],
    E.ofLimbs (K.ofBits 0x7aca7d4f3f697e27) (K.ofBits 0xd2876edc18e32c2d) (K.ofBits 0x9996395f39f9afa)),
  (8, 0xffffffffffffffff,
    [E.ofLimbs (K.ofBits 0x2db3d9db98dd7b1) (K.ofBits 0x34c991334b93f1b7) (K.ofBits 0xf32f680a0a085475), E.ofLimbs (K.ofBits 0x950997b6b83f54be) (K.ofBits 0x227d6acb4d372a7f) (K.ofBits 0x794ef9b83e81fc5b), E.ofLimbs (K.ofBits 0xb2415354a0924723) (K.ofBits 0x8257c033715edab0) (K.ofBits 0x64fabe66d7a24b16), E.ofLimbs (K.ofBits 0xd194bc1b444ef19f) (K.ofBits 0x3ea4957ac218abaf) (K.ofBits 0xd36f8062bf656150), E.ofLimbs (K.ofBits 0xbcdec03bded15928) (K.ofBits 0x2fb4815a93616368) (K.ofBits 0x6b35efe1e60b02eb), E.ofLimbs (K.ofBits 0xa98ba903e9e7c893) (K.ofBits 0xc4690356fb35d45d) (K.ofBits 0xb592677d035d1a32), E.ofLimbs (K.ofBits 0x6c01ff2bc645e851) (K.ofBits 0xf422c8069a6a0668) (K.ofBits 0xede3afe61fde0464), E.ofLimbs (K.ofBits 0xcd849183650dab7c) (K.ofBits 0x8e72f8ab79a1325e) (K.ofBits 0xef0996f21c7af481)],
    E.ofLimbs (K.ofBits 0x653c47605bf70921) (K.ofBits 0xb0a43677160877ed) (K.ofBits 0xa4ea1e656d330362))]


/-! ## Agreement with the pinned verifier -/

#guard (List.range 10).map subspaceRoot = pythonRoots

#guard pythonNormW.all fun (x, ws) ↦ (List.range 8).map (fun k ↦ normW k (K.ofBits x)) = ws

/-- The extension of the column weight at the position `q`, `κ + R = 64`. -/
def weightAt (κ q : ℕ) (pt : List E) : E :=
  (columnWeight (algebraMap K E) κ (64 - κ)
    ⟨q % 2 ^ (κ + (64 - κ)), Nat.mod_lt _ (Nat.two_pow_pos _)⟩).mle
    (Vector.ofFn fun i : Fin κ ↦ pt.getD i 0)

#guard pythonWeights.all fun (κ, q, pt, w) ↦ weightAt κ q pt = w

/-! ## The normalization and the domain -/

/- `Ŵ_k(e_k) = 1` and `Ŵ_k` vanishes on `e_0, ..., e_{k-1}`, for `k` up to the table's width. -/
#guard (List.range 8).all fun k ↦ normW k (basisElt k) = 1
#guard (List.range 8).all fun k ↦ (List.range k).all fun c ↦ normW k (basisElt c) = 0

/- The first normalized polynomial is the identity, since `e_0 = 1`. -/
#guard (List.range 40).all fun x ↦ normW 0 (K.ofBits x) = K.ofBits x

/- `Ŵ_k` is `F_2`-linear: its value at `x_v` is the sum over the bits of `v`. -/
#guard (List.range 64).all fun v ↦ (List.range 6).all fun k ↦
  normW k (K.ofBits v) =
    (List.range 6).foldl (fun acc c ↦ if v.testBit c then acc + normW k (basisElt c) else acc) 0

/-! ## Nearby false statements -/

/- The normalization is load-bearing: the unnormalized `V_1(e_1)` is `6`, not `1`. -/
#guard subspaceRoot 1 = K.ofBits 6 ∧ subspaceRoot 1 ≠ 1

/- The novel basis is not the monomial basis: `X_2 = Ŵ_1` takes the value `6` at `x_5`, while
`x_5 ^ 2` is `0x11`. A reading of the message as monomial coefficients is a different code. -/
#guard normW 1 (K.ofBits 5) = K.ofBits 6 ∧ normW 1 (K.ofBits 5) ≠ K.ofBits 5 ^ 2

/- The root of stage `2` is the diagonal entry `V_2(e_2) = 0x168` of the layer; the entry one
index off, `V_2(e_3)`, is another element, so a table read at the wrong index is a wrong code. -/
#guard subspaceRoot 2 = K.ofBits 0x168 ∧ (subspaceLayer 2).getD 3 0 ≠ K.ofBits 0x168

/-- Coordinate `k` of the weight is bit `k` of the index, low bit first: the entry at index `1`
is `Ŵ_0(x)`, at index `2` it is `Ŵ_1(x)`, at index `3` their product, and the value at index `2`
is not `Ŵ_0(x)`. -/
def weightCell (κ R q i : ℕ) : K :=
  (columnWeight (RingHom.id K) κ R ⟨q % 2 ^ (κ + R), Nat.mod_lt _ (Nat.two_pow_pos _)⟩).onCube.getD i 0

#guard weightCell 3 2 5 0 = 1
#guard weightCell 3 2 5 1 = normW 0 (K.ofBits 5)
#guard weightCell 3 2 5 2 = normW 1 (K.ofBits 5)
#guard weightCell 3 2 5 3 = normW 0 (K.ofBits 5) * normW 1 (K.ofBits 5)
#guard weightCell 3 2 5 2 ≠ normW 0 (K.ofBits 5)
#guard weightCell 3 2 5 7 = normW 0 (K.ofBits 5) * normW 1 (K.ofBits 5) * normW 2 (K.ofBits 5)

/-- The encoder of a unit message at index `j` is `X_j(x_v)`: `X_3 = Ŵ_0 Ŵ_1`. -/
def unitMessage (κ j : ℕ) : CMlPolynomialEval K κ :=
  Vector.ofFn fun i : Fin (2 ^ κ) ↦ if i.val = j then 1 else 0

/-- The encoder at `κ = 3`, `R = 2`, over `K`, at the position `v < 32`. -/
def enc32 (m : CMlPolynomialEval K 3) (v : ℕ) : K :=
  encode (RingHom.id K) 3 2 m ⟨v % 2 ^ (3 + 2), Nat.mod_lt _ (Nat.two_pow_pos _)⟩

#guard (List.range 32).all fun v ↦
  enc32 (unitMessage 3 3) v =
    normW 0 (K.ofBits v) * normW 1 (K.ofBits v)

/- The mutation that reads index `3` as the monomial `x ^ 3` differs from the encoder. -/
#guard ¬ (List.range 32).all fun v ↦
  enc32 (unitMessage 3 3) v = K.ofBits v ^ 3

/- The encoder is `F_2`-linear in the message (`def:enc`), on a sample. -/
#guard (List.range 32).all fun v ↦
  enc32 (unitMessage 3 1 + unitMessage 3 6) v =
    enc32 (unitMessage 3 1) v +
      enc32 (unitMessage 3 6) v

/-! ## The theorems -/

example : ∀ k < 64, basisElt k = domainPt (2 ^ k) := basisElt_eq_domainPt

/-- The recursion computes the Annex's product, at every stage a query uses. -/
example (x : K) : vanish x 5 = ∏ m ∈ Finset.range 32, (x + domainPt m) :=
  vanish_eq (by norm_num) x

/-- The root is nonzero at every stage below `64`. -/
example : subspaceRoot 63 ≠ 0 := subspaceRoot_ne_zero (by norm_num)

example (κ R : ℕ) (m : CMlPolynomialEval K κ) (v : Fin (2 ^ (κ + R))) :
    IsInK (encode (algebraMap K E) κ R (CMlPolynomialEval.map (algebraMap K E) m) v) :=
  isInK_encode_ofK κ R m v

/-- The encoder is injective over `K` and over `E`, at every `κ` the domain holds (`def:enc`). -/
example (κ R : ℕ) (h : κ ≤ 64) : Function.Injective (encode (RingHom.id K) κ R) :=
  encode_injective _ h Function.injective_id

example (κ R : ℕ) (h : κ ≤ 64) : Function.Injective (encode (algebraMap K E) κ R) :=
  encode_injective _ h (algebraMap K E).injective

/-- The encoder is linear in the message, over `E` as well: the linear map's laws apply. -/
example (κ R : ℕ) (m m' : CMlPolynomialEval E κ) (c : E) : True := by
  have _ := (encodeLinear (algebraMap K E) κ R).map_add m m'
  have _ := (encodeLinear (algebraMap K E) κ R).map_smul c m
  trivial

/-- The novel polynomial has degree `j`, and the encoder's table entry is its value. -/
example : (novelPoly 3 5).natDegree = 5 := natDegree_novelPoly (by norm_num) (by norm_num)

/- Distinct unit messages have distinct words, at the positions of the first `2 ^ κ` points:
`X_1 = Ŵ_0` and `X_2 = Ŵ_1` differ at `x_5`. -/
#guard enc32 (unitMessage 3 1) 5 ≠ enc32 (unitMessage 3 2) 5

end
end LeanerVMTests.Protocol
