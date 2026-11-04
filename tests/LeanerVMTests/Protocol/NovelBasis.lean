/-
  LeanerVMTests.Protocol.NovelBasis

  The subspace roots, the normalized subspace polynomials, the encoder and the column weights
  against the pinned Python verifier, and the readings that compile and are wrong.
-/

import LeanerVM.Protocol.NovelBasis

/-!
# Novel basis, encoder and column weights: tests

The tables below are the output of the pinned verifier (`python-verifier/verifier.py` at leanVM
`a386121f84292f6fa663aaa3e570c15bc0240ea2`), run on the functions the module transcribes:
`_subspace_roots` for the roots `V_k(e_k)`, the loop of `_induced_weight` for `Ŵ_k(x)`, and
`_induced_weight` itself, one query with weight one, for the column weight's extension at a
random point of `E^κ` (seed `20261015`), and at the deployed level shapes, among them level 0
of the largest stack (seed `20261019`). The deployed Rust (`AdditiveNttF64::standard`) is the
other implementation of the roots and is not run here.
-/

namespace LeanerVMTests.Protocol

open LeanerVM.Parameters LeanerVM.Protocol CompPoly

section

/-! ## The pinned verifier's output -/

/-- `V_k(e_k)` for `k = 0 .. 8`: `_subspace_roots(9)` of the pinned verifier. -/
def pythonRoots : List K :=
  [K.ofBits 0x1, K.ofBits 0x6, K.ofBits 0x168, K.ofBits 0x1166880, K.ofBits 0x11616686880801b,
    K.ofBits 0x726b6e3c6e39234e, K.ofBits 0x796adf34d64462c2, K.ofBits 0xf1060866be6fa9c,
    K.ofBits 0x6a06f1b0a76acb05, K.ofBits 0xd2d14e471a7186d9]

/-- `(x, [Ŵ_0(x), ..., Ŵ_7(x)])`, the `basis * inverse` of `_induced_weight`'s loop. -/
def pythonNormW : List (ℕ × List K) :=
  [
  (0x0, [K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0,
    K.ofBits 0x0, K.ofBits 0x0]),
  (0x1, [K.ofBits 0x1, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0,
    K.ofBits 0x0, K.ofBits 0x0]),
  (0x2, [K.ofBits 0x2, K.ofBits 0x1, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0,
    K.ofBits 0x0, K.ofBits 0x0]),
  (0x3, [K.ofBits 0x3, K.ofBits 0x1, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0,
    K.ofBits 0x0, K.ofBits 0x0]),
  (0x5, [K.ofBits 0x5, K.ofBits 0x6, K.ofBits 0x1, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0,
    K.ofBits 0x0, K.ofBits 0x0]),
  (0x1f, [K.ofBits 0x1f, K.ofBits 0x63, K.ofBits 0x16b, K.ofBits 0x117, K.ofBits 0x1, K.ofBits 0x0,
    K.ofBits 0x0, K.ofBits 0x0]),
  (0x123456789abcdef, [K.ofBits 0x123456789abcdef, K.ofBits 0x9f946d99ec181e18,
    K.ofBits 0x81568a22d86fe025, K.ofBits 0xd7bf72d10f546b54, K.ofBits 0xb8d9cc984af7499b,
    K.ofBits 0x539079febe7a07ab, K.ofBits 0xdf89cdbf0a1cf71, K.ofBits 0x60677f7b98939edc]),
  (0xdeadbeefcafef00d, [K.ofBits 0xdeadbeefcafef00d, K.ofBits 0xd0d76026f2ae5372,
    K.ofBits 0x70f320f5fc74343d, K.ofBits 0xf304ad68421141bd, K.ofBits 0x117bc68020dfb8c4,
    K.ofBits 0x8ca90c0117334e6a, K.ofBits 0x5e72f934d646183e, K.ofBits 0x4d0062a94408d3b8]),
  (0x8000000000000001, [K.ofBits 0x8000000000000001, K.ofBits 0xe000000000000012,
    K.ofBits 0x8e0000000000001a, K.ofBits 0xe38e000000000009, K.ofBits 0x8e38e38e0000000d,
    K.ofBits 0xe38e38e38e38e386, K.ofBits 0x2e12e12e12e12e11, K.ofBits 0xb50c27b50c27b503]),
  (0xffffffffffffffff, [K.ofBits 0xffffffffffffffff, K.ofBits 0xccccccccccccccdb,
    K.ofBits 0x1d1d1d1d1d1d1d0a, K.ofBits 0xf4e9f4e9f4e9f4e1, K.ofBits 0xce9d3a74ce9d3a7f,
    K.ofBits 0x1d3a74e9d3a74e9c, K.ofBits 0x3b25ec97b25ec979, K.ofBits 0x13912ba83912ba82])]

/-- `(κ, query, point, value)`: `_induced_weight(κ, [query], [1], point)`. -/
def pythonWeights : List (ℕ × ℕ × List E × E) :=
  [
  (3, 0x5,
    [E.ofLimbs (K.ofBits 0x361424b1ea125c50) (K.ofBits 0x70b50ecb32ccd896)
        (K.ofBits 0x2ae66617b21822c),
      E.ofLimbs (K.ofBits 0xd2db9299d1e8e1ba) (K.ofBits 0x7a615de0a514e83)
        (K.ofBits 0x31b066ce9c2b9de1),
      E.ofLimbs (K.ofBits 0xd3e9b4ad86719d9f) (K.ofBits 0xe33fcca66c2aaff5)
        (K.ofBits 0x928c1b4a654f8125)],
    E.ofLimbs (K.ofBits 0x7afb3eb1c12f4c00) (K.ofBits 0xa08169897fb5127a)
        (K.ofBits 0xe413e39f7c1dea7a)),
  (4, 0x2b,
    [E.ofLimbs (K.ofBits 0xb06dcebba7113812) (K.ofBits 0xcb49fc7dfaf5c15c)
        (K.ofBits 0xa72b8bd5a19692a6),
      E.ofLimbs (K.ofBits 0xe6950292a732c6f1) (K.ofBits 0x648115bcfec2e632)
        (K.ofBits 0x3b993d36d4a45401),
      E.ofLimbs (K.ofBits 0xfa7802bbca2a86a8) (K.ofBits 0xafc725d37f66a51a)
        (K.ofBits 0xe8016b4eda3eab41),
      E.ofLimbs (K.ofBits 0xfd23dfb60ede7050) (K.ofBits 0x8d4129f93bf22a2e)
        (K.ofBits 0xfb7a0722e128074)],
    E.ofLimbs (K.ofBits 0xbcf506d443b56fce) (K.ofBits 0x9d5472d89886eda3)
        (K.ofBits 0xd9799a1eb237160f)),
  (6, 0x1d3,
    [E.ofLimbs (K.ofBits 0xa88bd675fda43ae7) (K.ofBits 0x111b0bb9456c00bc)
        (K.ofBits 0xad69f59859edf9ae),
      E.ofLimbs (K.ofBits 0x3ce7fcb2ee1d8531) (K.ofBits 0x9e607c80452118b5)
        (K.ofBits 0x2d1874c9640e77fc),
      E.ofLimbs (K.ofBits 0x60177bdd90292e1) (K.ofBits 0xb006b9c20ba36864)
        (K.ofBits 0xf0722929d091aa6e),
      E.ofLimbs (K.ofBits 0xe5c97947ecb13eb4) (K.ofBits 0x6614e2cd2c76d7)
        (K.ofBits 0x708929ef89a332da),
      E.ofLimbs (K.ofBits 0x2aaa21516cda3f0c) (K.ofBits 0x3452eb3e2dae1ec)
        (K.ofBits 0x9c2f44bfa55e0c92),
      E.ofLimbs (K.ofBits 0x721efeaba9019582) (K.ofBits 0xeb7d6cb7f10daa7)
        (K.ofBits 0xb8af88f41d45c180)],
    E.ofLimbs (K.ofBits 0xdcc5264744c821d3) (K.ofBits 0x5f3b77cafcde177f)
        (K.ofBits 0x22bf9deddc893a11)),
  (8, 0xdeadbeefcafef00d,
    [E.ofLimbs (K.ofBits 0xdbd58b9a11bec511) (K.ofBits 0x889416c630c77ba8)
        (K.ofBits 0xf518dcbe09842215),
      E.ofLimbs (K.ofBits 0x8eeea67c70e211f7) (K.ofBits 0xc336656ae155fccc)
        (K.ofBits 0x792ef24334339aaf),
      E.ofLimbs (K.ofBits 0x77f8c46004b3fd27) (K.ofBits 0xea7ddb3ef1de3787)
        (K.ofBits 0x2f452ba38fb87e6e),
      E.ofLimbs (K.ofBits 0x45ac9a94950adf49) (K.ofBits 0xd36a2a60b6372aec)
        (K.ofBits 0xd0d8d794fa3721db),
      E.ofLimbs (K.ofBits 0x3f6aa289fe870dba) (K.ofBits 0x2234504961382b72)
        (K.ofBits 0xf0bf1ab5ed7eaac5),
      E.ofLimbs (K.ofBits 0xd33c1920b741f9da) (K.ofBits 0x1905af2e221bfb18)
        (K.ofBits 0x8421ae84e1f5e4e),
      E.ofLimbs (K.ofBits 0x62ac6354086afd9d) (K.ofBits 0xfcfab40e839e1ee2)
        (K.ofBits 0xda1720d35a351b8b),
      E.ofLimbs (K.ofBits 0x69c301913d617ead) (K.ofBits 0xb33c5fc79cc9eaf1)
        (K.ofBits 0x7744ca7074615814)],
    E.ofLimbs (K.ofBits 0x7aca7d4f3f697e27) (K.ofBits 0xd2876edc18e32c2d)
        (K.ofBits 0x9996395f39f9afa)),
  (8, 0xffffffffffffffff,
    [E.ofLimbs (K.ofBits 0x2db3d9db98dd7b1) (K.ofBits 0x34c991334b93f1b7)
        (K.ofBits 0xf32f680a0a085475),
      E.ofLimbs (K.ofBits 0x950997b6b83f54be) (K.ofBits 0x227d6acb4d372a7f)
        (K.ofBits 0x794ef9b83e81fc5b),
      E.ofLimbs (K.ofBits 0xb2415354a0924723) (K.ofBits 0x8257c033715edab0)
        (K.ofBits 0x64fabe66d7a24b16),
      E.ofLimbs (K.ofBits 0xd194bc1b444ef19f) (K.ofBits 0x3ea4957ac218abaf)
        (K.ofBits 0xd36f8062bf656150),
      E.ofLimbs (K.ofBits 0xbcdec03bded15928) (K.ofBits 0x2fb4815a93616368)
        (K.ofBits 0x6b35efe1e60b02eb),
      E.ofLimbs (K.ofBits 0xa98ba903e9e7c893) (K.ofBits 0xc4690356fb35d45d)
        (K.ofBits 0xb592677d035d1a32),
      E.ofLimbs (K.ofBits 0x6c01ff2bc645e851) (K.ofBits 0xf422c8069a6a0668)
        (K.ofBits 0xede3afe61fde0464),
      E.ofLimbs (K.ofBits 0xcd849183650dab7c) (K.ofBits 0x8e72f8ab79a1325e)
        (K.ofBits 0xef0996f21c7af481)],
    E.ofLimbs (K.ofBits 0x653c47605bf70921) (K.ofBits 0xb0a43677160877ed)
        (K.ofBits 0xa4ea1e656d330362))]


/-- `V_k(e_k)` for `k = 0 .. 30`: `_subspace_roots(30)` of the pinned verifier. -/
def pythonRootsDeployed : List K := [
  K.ofBits 0x1,
  K.ofBits 0x6,
  K.ofBits 0x168,
  K.ofBits 0x1166880,
  K.ofBits 0x11616686880801b,
  K.ofBits 0x726b6e3c6e39234e,
  K.ofBits 0x796adf34d64462c2,
  K.ofBits 0xf1060866be6fa9c,
  K.ofBits 0x6a06f1b0a76acb05,
  K.ofBits 0xd2d14e471a7186d9,
  K.ofBits 0x6d55ab94bb5f9605,
  K.ofBits 0xd08c5570c6423a2a,
  K.ofBits 0xa0ca298b954731,
  K.ofBits 0x3c0e5429ac5cd413,
  K.ofBits 0x60d6932e7d924b1,
  K.ofBits 0xaa1f2d87fa7d5331,
  K.ofBits 0x39eab2a541e0176a,
  K.ofBits 0x822a438a8d849036,
  K.ofBits 0xb1d89a290a5d7b51,
  K.ofBits 0xb162289ed2f5d150,
  K.ofBits 0x3c900abc5e73699d,
  K.ofBits 0x43c96339f7c81f62,
  K.ofBits 0xde75749717d86ed9,
  K.ofBits 0x54ab3da4d6fc8f15,
  K.ofBits 0x468db779f09dce70,
  K.ofBits 0x889083674461466a,
  K.ofBits 0xe46e28bbf8a14d92,
  K.ofBits 0xd000c404b4fc3163,
  K.ofBits 0xaba2e8dbd19e6b79,
  K.ofBits 0x564d16097c604d40,
  K.ofBits 0x5192f58c592a9c21]

/-- `(κ, R, query, point, value)` at deployed level shapes:
`_induced_weight(κ, [query], [1], point)`. -/
def pythonWeightsDeployed : List (ℕ × ℕ × ℕ × List E × E) := [
  (22, 1, 0x4b60ca,
   [
    E.ofLimbs (K.ofBits 0xf6c8d93b529ed281) (K.ofBits 0xf3fe8045b92f5e7c)
        (K.ofBits 0x364210a01ecb363f),
    E.ofLimbs (K.ofBits 0x8a0e5fe07856cb89) (K.ofBits 0x444db03c4ae957c1)
        (K.ofBits 0x716a048b76ebd72),
    E.ofLimbs (K.ofBits 0x2345c1f35946f6d1) (K.ofBits 0xb9cea9d6016b1625)
        (K.ofBits 0x4b48845f8b99d640),
    E.ofLimbs (K.ofBits 0xa48e2e6170b153aa) (K.ofBits 0x4576fdcff4086205)
        (K.ofBits 0x50d920728e7ee438),
    E.ofLimbs (K.ofBits 0x142dd61d13c0b723) (K.ofBits 0xa4988a35628c83f7)
        (K.ofBits 0x3aced0e140e3b449),
    E.ofLimbs (K.ofBits 0x148f93b9739f5d2f) (K.ofBits 0x6738e9632fd63476)
        (K.ofBits 0xd858cf9eea9b8812),
    E.ofLimbs (K.ofBits 0x50022d156dcea6b) (K.ofBits 0x8dd9d6b8d93ba347)
        (K.ofBits 0xaa3d90fedd2b901f),
    E.ofLimbs (K.ofBits 0x55f3102fe901e8fc) (K.ofBits 0xd09ae08544cf2888)
        (K.ofBits 0x92decd542f57e38a),
    E.ofLimbs (K.ofBits 0xe87a5be61913457b) (K.ofBits 0x5e2506eec4b27f44)
        (K.ofBits 0x9b1373f9ee6abe2),
    E.ofLimbs (K.ofBits 0x9558bff5ef54817e) (K.ofBits 0x382663e8916c) (K.ofBits 0xb7ea57c6c42ce658),
    E.ofLimbs (K.ofBits 0xddb86dd95aaecadd) (K.ofBits 0x53a958ceee7005d4)
        (K.ofBits 0x94358f677d3d7291),
    E.ofLimbs (K.ofBits 0x443e08aab35f0f7a) (K.ofBits 0x4db5ce868b461168)
        (K.ofBits 0x4021c63053531845),
    E.ofLimbs (K.ofBits 0x1b93775f9bb473fa) (K.ofBits 0xb378499da80e78af)
        (K.ofBits 0x7e8eec2622cee550),
    E.ofLimbs (K.ofBits 0x783272caf6093a12) (K.ofBits 0x3cc1338b11d3b3d0)
        (K.ofBits 0x36e2c01ebe9db611),
    E.ofLimbs (K.ofBits 0xc77f4dd60602d40) (K.ofBits 0x59492f1add106503)
        (K.ofBits 0xfeb4c9424f30036a),
    E.ofLimbs (K.ofBits 0x9756012efedf7be8) (K.ofBits 0x3ea79c30efc35eb5)
        (K.ofBits 0x97360ed20a88201a),
    E.ofLimbs (K.ofBits 0xb66a15a1c4f6bf69) (K.ofBits 0xf24950ace09b7565)
        (K.ofBits 0x63385d583d8a81a2),
    E.ofLimbs (K.ofBits 0xbac56f51dba6faca) (K.ofBits 0x41619e46b2d708fb)
        (K.ofBits 0x5122b3471b5126cd),
    E.ofLimbs (K.ofBits 0x86e2a395051b7e45) (K.ofBits 0xa979d17767a1501f)
        (K.ofBits 0xce6d8a932a1ed865),
    E.ofLimbs (K.ofBits 0x97c09fb2d03619e9) (K.ofBits 0xf20940a092ba3528)
        (K.ofBits 0x451b82f1e28c3a05),
    E.ofLimbs (K.ofBits 0xe2bdfa48855db8cf) (K.ofBits 0xefaaac47109f25fd)
        (K.ofBits 0x4cb11d6f8060bab3),
    E.ofLimbs (K.ofBits 0xf2977d1e30c41e50) (K.ofBits 0x7da5780f562748bc)
        (K.ofBits 0x19163502e2070b59)],
   E.ofLimbs (K.ofBits 0x973a409d418b55f5) (K.ofBits 0xc86551d340597c73)
       (K.ofBits 0x43a260b18d51bb43)),
  (9, 1, 0x147,
   [
    E.ofLimbs (K.ofBits 0x297577bda1460908) (K.ofBits 0xff0c593f4d45aab2)
        (K.ofBits 0xd794f8afb57281ac),
    E.ofLimbs (K.ofBits 0x93ea85c7d0b1db9c) (K.ofBits 0x32691dc654034369)
        (K.ofBits 0xbcfe6b7b430bf3a4),
    E.ofLimbs (K.ofBits 0x615653809c2335a6) (K.ofBits 0xdb1147a840beb268)
        (K.ofBits 0xc467ef1bf27267b),
    E.ofLimbs (K.ofBits 0xad411bb52daa9aa) (K.ofBits 0xa189ca4b8fb48386)
        (K.ofBits 0x5157452bdaccf391),
    E.ofLimbs (K.ofBits 0x8f9ba12cf69955e5) (K.ofBits 0x72418008b3f69556)
        (K.ofBits 0xb4e204562632b0ff),
    E.ofLimbs (K.ofBits 0xbb3fb8a6f29e2c63) (K.ofBits 0x1764881b85808969)
        (K.ofBits 0x7ef4affd6d8b2853),
    E.ofLimbs (K.ofBits 0x747f7b334d90598b) (K.ofBits 0x34ce0941f07fdafe)
        (K.ofBits 0xeaf3514893d2625e),
    E.ofLimbs (K.ofBits 0x3fa39e3343b274e1) (K.ofBits 0x3683f6ee5ad46141)
        (K.ofBits 0x5e653ea113f1f06),
    E.ofLimbs (K.ofBits 0x26c874265b419adb) (K.ofBits 0x44910af81e8321b8)
        (K.ofBits 0x4e463552d0218748)],
   E.ofLimbs (K.ofBits 0xb408fe47f92b91f7) (K.ofBits 0x5d5b452bfeacccf9)
       (K.ofBits 0x34092976e63dc630)),
  (16, 4, 0xff990,
   [
    E.ofLimbs (K.ofBits 0xf4a85695ca3cf335) (K.ofBits 0x388bb0c9407b25e8)
        (K.ofBits 0xdab57d3327d47cee),
    E.ofLimbs (K.ofBits 0x35c8e25df87ff3e1) (K.ofBits 0xd389529df6c873bc)
        (K.ofBits 0xdba789af9f0519e2),
    E.ofLimbs (K.ofBits 0xb75d11c857af3068) (K.ofBits 0xfd81f5f68cc3129a)
        (K.ofBits 0x3043270b2dce55a6),
    E.ofLimbs (K.ofBits 0x75fe1b232b768f42) (K.ofBits 0x825484eacd9a1e9c)
        (K.ofBits 0x48ca779d766419b),
    E.ofLimbs (K.ofBits 0x799b475bd0f34316) (K.ofBits 0xa279a23619c81009)
        (K.ofBits 0x2da50588ce8e0e02),
    E.ofLimbs (K.ofBits 0xa54ad8819dc1378e) (K.ofBits 0x5cec4b63ce8637ad)
        (K.ofBits 0xc04fbd4d48f7a31a),
    E.ofLimbs (K.ofBits 0x52302f80d400d15) (K.ofBits 0x1353f0025921a4d1)
        (K.ofBits 0x1f398ac39c8e6fc4),
    E.ofLimbs (K.ofBits 0xfc5f5b27110a6eea) (K.ofBits 0xe691ee15dbc4f50b)
        (K.ofBits 0x7d64499a835b85f),
    E.ofLimbs (K.ofBits 0x6eeaa92b1c98c18d) (K.ofBits 0xaaa581ba7b0eaf67)
        (K.ofBits 0xc5bd42feb6fbb997),
    E.ofLimbs (K.ofBits 0xa8dba797dc7d4bc2) (K.ofBits 0xf870e6a26cfb3f3)
        (K.ofBits 0xe8bb673f8f1973df),
    E.ofLimbs (K.ofBits 0x8b4a64587b618ebc) (K.ofBits 0x9ac9f21b6b28fdc4)
        (K.ofBits 0x54cd9391c3d372d1),
    E.ofLimbs (K.ofBits 0x87b97a0bdb611439) (K.ofBits 0xf4743ca38dde39e4)
        (K.ofBits 0x454eeea3729a2614),
    E.ofLimbs (K.ofBits 0xd58f1571e873464d) (K.ofBits 0x709770382a5b04d3)
        (K.ofBits 0x5c9b1a0335a737e0),
    E.ofLimbs (K.ofBits 0x75d170332c638c0a) (K.ofBits 0x2ec556a8d4296db1)
        (K.ofBits 0x8ca7a41256045a40),
    E.ofLimbs (K.ofBits 0x93736f60b317fd3a) (K.ofBits 0x58e4d4baecb2b53a)
        (K.ofBits 0xe89a621199c3f6cd),
    E.ofLimbs (K.ofBits 0xa379fa8ff373d73d) (K.ofBits 0x1a68429e189b8bf0)
        (K.ofBits 0x71b22802ef0a949)],
   E.ofLimbs (K.ofBits 0xf25ecd17a0a45269) (K.ofBits 0x482c2b6d0de8b83a)
       (K.ofBits 0x39bac6cee4a7c971)),
  (6, 19, 0x134a4e7,
   [
    E.ofLimbs (K.ofBits 0x3de5634387bbf56c) (K.ofBits 0x572b5248323eb4c4)
        (K.ofBits 0x3f80eedd55a53f46),
    E.ofLimbs (K.ofBits 0x3804dc99221cd4a8) (K.ofBits 0xed8e335f85ad9cb7)
        (K.ofBits 0xe4958149cbd74b33),
    E.ofLimbs (K.ofBits 0xf5c2ce903ce30180) (K.ofBits 0x9c949712fd53dd25)
        (K.ofBits 0xe41248e9a539351a),
    E.ofLimbs (K.ofBits 0x6482ddaf0ec3c6d8) (K.ofBits 0x93ee57637d1e904f)
        (K.ofBits 0xa88d66831fa6e2fe),
    E.ofLimbs (K.ofBits 0x10db47e8a99531c0) (K.ofBits 0x91386ad490c5a54)
        (K.ofBits 0xaf41fa6108268530),
    E.ofLimbs (K.ofBits 0x702c683a1d557516) (K.ofBits 0xe8f421c08789708e)
        (K.ofBits 0x2b4225c4e2043d89)],
   E.ofLimbs (K.ofBits 0x6453a182d1efa24) (K.ofBits 0x31d5d1a312689df9)
       (K.ofBits 0x8fdb672f8c686921)),
  (2, 16, 0x1d321,
   [
    E.ofLimbs (K.ofBits 0xe94bba3c4c7dbcc8) (K.ofBits 0x7ef45e8469d33d9f)
        (K.ofBits 0xa7fc131b5251900),
    E.ofLimbs (K.ofBits 0xa832c535409971f6) (K.ofBits 0x6d98b9baecc8d678)
        (K.ofBits 0xb0677b839b139e9d)],
   E.ofLimbs (K.ofBits 0x23b27d0fb140d54d) (K.ofBits 0xb9516b95d29cda53)
       (K.ofBits 0xb24473673dc5a939))]


/-! ## Agreement with the pinned verifier -/

#guard (List.range 10).map subspaceRoot = pythonRoots

#guard pythonNormW.all fun (x, ws) ↦ (List.range 8).map (fun k ↦ normW k (K.ofBits x)) = ws

/-- The extension of the column weight at the position `q`, `κ + R = 64`. -/
def weightAt (κ q : ℕ) (pt : List E) : E :=
  (columnWeight (algebraMap K E) κ (64 - κ)
    ⟨q % 2 ^ (κ + (64 - κ)), Nat.mod_lt _ (Nat.two_pow_pos _)⟩).mle
    (Vector.ofFn fun i : Fin κ ↦ pt.getD i 0)

#guard pythonWeights.all fun (κ, q, pt, w) ↦ weightAt κ q pt = w

/- The roots to stage 30, past the largest deployed block log (26), and the column weight's
extension at five deployed level shapes, `(22, 1)` the largest, evaluated as a verifier does,
through `columnWeightMle`, in under a second. -/
#guard (List.range 31).map subspaceRoot = pythonRootsDeployed

#guard pythonWeightsDeployed.all fun (κ, R, q, pt, w) ↦
  columnWeightMle (algebraMap K E) κ R ⟨q % 2 ^ (κ + R), Nat.mod_lt _ (Nat.two_pow_pos _)⟩
    (Vector.ofFn fun i : Fin κ ↦ pt.getD i 0) = w

/- From stage `64` on the root is `0`, where `U_k` is all of `K`; the theorems bound the stage. -/
#guard subspaceRoot 63 ≠ 0 ∧ subspaceRoot 64 = 0

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
  (columnWeight (RingHom.id K) κ R ⟨q % 2 ^ (κ + R),
    Nat.mod_lt _ (Nat.two_pow_pos _)⟩).onCube.getD i 0

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

/-- Two words that agree on `2 ^ κ` positions encode one message, over `E`, at a deployed level
shape. -/
example (m m' : CMlPolynomialEval E 22) (T : Finset (Fin (2 ^ (22 + 1)))) (hT : 2 ^ 22 ≤ T.card)
    (h : ∀ v ∈ T, encode (algebraMap K E) 22 1 m v = encode (algebraMap K E) 22 1 m' v) :
    m = m' :=
  encode_eq_of_agree _ (by norm_num) (algebraMap K E).injective T hT h

/-- The encoder at `κ = 1`, `R = 1`, over `K`, at the position `v < 4`. -/
def enc4 (m : CMlPolynomialEval K 1) (v : ℕ) : K :=
  encode (RingHom.id K) 1 1 m ⟨v % 4, Nat.mod_lt _ (by decide)⟩

/- The distance is attained: the message `(1, 1)`, the polynomial `1 + X_1 = 1 + x`, and the zero
message agree exactly at `x_1 = 1`, so `2 ^ κ - 1` agreeing positions do not fix a message. -/
#guard (List.range 4).filter (fun v ↦ enc4 #v[1, 1] v = enc4 #v[0, 0] v) = [1]

/- Distinct unit messages have distinct words, at the positions of the first `2 ^ κ` points:
`X_1 = Ŵ_0` and `X_2 = Ŵ_1` differ at `x_5`. -/
#guard enc32 (unitMessage 3 1) 5 ≠ enc32 (unitMessage 3 2) 5

/-! ## The compiled indexed recurrence -/

/-- An independently assembled copy of the reference product. It deliberately does not call
`columnWeightMle`, whose compiled call sites the new `csimp` theorem replaces. -/
private def referenceWeight (κ R q seed : ℕ) : E :=
  let v : Fin (2 ^ (κ + R)) := ⟨q % 2 ^ (κ + R), Nat.mod_lt _ (Nat.two_pow_pos _)⟩
  let r : Vector E κ := Vector.ofFn fun i ↦
    E.ofLimbs (K.ofBits (seed + i + 1)) (K.ofBits (3 * i + 5)) (K.ofBits (seed + 7))
  ∏ k : Fin κ, ((1 - r[k]) + r[k] * (algebraMap K E) (normW k (domainPt v)))

/-- The public evaluator route used by a column-weight consumer. -/
private def fastWeight (κ R q seed : ℕ) : E :=
  let v : Fin (2 ^ (κ + R)) := ⟨q % 2 ^ (κ + R), Nat.mod_lt _ (Nat.two_pow_pos _)⟩
  let r : Vector E κ := Vector.ofFn fun i ↦
    E.ofLimbs (K.ofBits (seed + i + 1)) (K.ofBits (3 * i + 5)) (K.ofBits (seed + 7))
  (columnWeight (algebraMap K E) κ R v).mle r

-- Ordinary sizes, the basis boundary, and the reference function's zero-root default.
#guard [0, 1, 2, 8, 22, 64, 65].all fun κ ↦
  [0, 1, 5, 0x1234].all fun q ↦
    [0, 17].all fun seed ↦ fastWeight κ 1 q seed = referenceWeight κ 1 q seed

/-- A wrong root index is observable at an ordinary non-Boolean point. -/
private def shiftedWeight : E :=
  let r : Vector E 2 := #v[E.ofLimbs (K.ofBits 3) (K.ofBits 5) 0,
    E.ofLimbs (K.ofBits 7) (K.ofBits 11) 0]
  ∏ k : Fin 2, ((1 - r[k]) + r[k] * (algebraMap K E) (normW (k + 1) (K.ofBits 5)))

private def indexedWeight : E :=
  let r : Vector E 2 := #v[E.ofLimbs (K.ofBits 3) (K.ofBits 5) 0,
    E.ofLimbs (K.ofBits 7) (K.ofBits 11) 0]
  columnWeightMleFast (algebraMap K E) 2 1 ⟨5, by decide⟩ r

#guard indexedWeight ≠ shiftedWeight

-- The universal equation carries no size bound or extra certificate assumption.
example {S : Type*} [CommRing S] (φ : K →+* S) (κ R : ℕ)
    (v : Fin (2 ^ (κ + R))) (r : Vector S κ) :
    columnWeightMleFast φ κ R v r = columnWeightMle φ κ R v r :=
  columnWeightMleFast_eq φ κ R v r

end
end LeanerVMTests.Protocol
