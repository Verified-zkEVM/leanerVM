module

public import Statement.Prover.Code
public import Statement.Prover.Script

/-!
# The additive NTT and the committed words

The encoder of leanVM's binary Reed-Solomon code in the Lin–Chung–Han novel basis
(`Statement/Prover/Code.lean`), computed for all `2^(κ+R)` domain points at once in
`O((κ+R)·2^(κ+R))` operations (the Rust reference: `crates/pcs/src/ntt/additive_ntt_f64.rs`,
`AdditiveNttF64::standard`, at leanVM pin `127510d14c98ade4e8a97646c44fa7f1ff5e752d`).

`Enc(g)(x_p) = Σ_u g(u)·∏_{i : u_i} Ŵ_i(x_p)`, and `Ŵ_i(x_p)` depends only on `p >>> i` (`Ŵ_i` is
additive and vanishes on `U_i`). The transform folds the message's variables from the top: after
the variables `κ-1, …, i` are folded, position `p` holds the fold of the lane `p mod 2^i` of the
message at the values `Ŵ_{i}(x_p), …, Ŵ_{κ-1}(x_p)`, which depend only on `p >>> i`. A stage is
the butterfly `(u, v) ↦ (u + t·v, u + (t + 1)·v)` with the twiddle `t = Ŵ_i(x_{b·2^(i+1)})` of
the block `b`, since `Ŵ_i(e_i) = 1`. The twiddles come from the table of `Ŵ_c(e_m)`, `c, m < 64`,
by additivity, the table from the recurrence `W_{c+1}(a) = W_c(a)·(W_c(a) + W_c(e_c))`.

* `ntt (nttTwiddles (κ+R) κ) κ R msg`: the codeword of the `K`-valued message `msg` (`2^κ`
  entries), `2^(κ+R)` entries.
* `stackWordFast μ R stack`: the stack's level-0 word (`stackWord` in `lean_vm`), the 64 lanes'
  codewords computed once.
* `levelWordFast κ k R g`: a deeper level's word (`levelWord`), each `E` lane encoded limb by
  limb.

A committed word is a function on every position. These words hold the computed codewords below
`2^height`, the only positions the run reads (`Run.lean`: the Merkle tree of a commitment of
height `h` reads the positions `p < 2^h`), and the encoder's formula above, never evaluated by the
run: so they are the specification's words at every position.
-/

@[expose] public section

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Complete
open LeanVM.Protocol.Compile

/-! ## The subspace polynomials on the basis -/

/-- Row `c` of the subspace polynomials on the basis, `W_c(e_m)` for `m < 64`: `W_0(a) = a`,
`W_{c+1}(a) = W_c(a)^2 + W_c(e_c)·W_c(a)`. -/
def vanRow : ℕ → Array K
  | 0 => Array.ofFn (n := 64) fun m ↦ basisVec m
  | c + 1 =>
    let r := vanRow c
    let root := r.getD c 0
    r.map fun v ↦ v * v + root * v

/-- Row `c` of the normalized subspace polynomials on the basis, `Ŵ_c(e_m)` for `m < 64`. -/
def hatRow (c : ℕ) : Array K :=
  let r := vanRow c
  let inv := (r.getD c 0)⁻¹
  r.map (· * inv)

/-- The table of `Ŵ_c(e_m)`, `c, m < 64`. -/
def hatTable : Array (Array K) := Array.ofFn (n := 64) fun c ↦ hatRow c

/-- `Ŵ_c(x_n)` for `c < 64`: `Ŵ_c` is additive and `x_n = Σ_{m < 64} n_m e_m`. -/
def hatAt (c n : ℕ) : K :=
  let row := hatTable.getD c #[]
  (List.range 64).foldl (fun acc m ↦ if n.testBit m then acc + row.getD m 0 else acc) 0

/-! ## The transform -/

/-- The twiddles of stage `i` of a transform on `2^N` positions: `Ŵ_i(x_{b·2^(i+1)})` for the
block `b < 2^(N-i-1)` of `2^(i+1)` positions. -/
def stageTwiddles (N i : ℕ) : Array K :=
  Array.ofFn (n := 2 ^ (N - (i + 1))) fun b ↦ hatAt i (b.val * 2 ^ (i + 1))

/-- The twiddles of the stages `i < κ` of a transform on `2^N` positions. -/
def nttTwiddles (N κ : ℕ) : Array (Array K) := Array.ofFn (n := κ) fun i ↦ stageTwiddles N i.val

/-- Stage `i` of the transform on `2^N` positions, with the stage's twiddles `tw`: in the block
`b` the pair `(u, v)` at `lo = b·2^(i+1) + j` and `lo + 2^i` (`j < 2^i`) becomes
`(u + t·v, u + t·v + v)`, `t = tw[b]`. The products `t·v` are computed once per pair. -/
def nttStage (N i : ℕ) (tw : Array K) (a : Array K) : Array K :=
  nttStageAt N (2 ^ i) (2 ^ (i + 1)) tw a
where
  /-- The stage with `2^i` and `2^(i+1)` computed once (`pi`, `pi1`). -/
  nttStageAt (N pi pi1 : ℕ) (tw : Array K) (a : Array K) : Array K :=
    let half : Array K := Array.ofFn (n := 2 ^ (N - 1)) fun q ↦
      let b := q.val / pi
      tw.getD b 0 * a.getD (b * pi1 + pi + q.val % pi) 0
    Array.ofFn (n := 2 ^ N) fun p ↦
      let b := p.val / pi1
      let r := p.val % pi1
      let j := r % pi
      let lo := b * pi1 + j
      let u := a.getD lo 0 + half.getD (b * pi + j) 0
      if r < pi then u else u + a.getD (lo + pi) 0

/-- **The additive NTT** of a message of `2^κ` entries on `2^(κ+R)` positions, with the twiddles
`tws = nttTwiddles (κ + R) κ`: the message repeated `2^R` times, then the stages
`κ - 1, …, 0`. -/
def ntt (tws : Array (Array K)) (κ R : ℕ) (msg : Array K) : Array K :=
  go κ (Array.ofFn (n := 2 ^ (κ + R)) fun p ↦ msg.getD (p.val % 2 ^ κ) 0)
where
  /-- The stages `i - 1, …, 0`. -/
  go : ℕ → Array K → Array K
    | 0, a => a
    | i + 1, a => go i (nttStage (κ + R) i (tws.getD i #[]) a)

/-! ## The committed words -/

/-- The codewords of the stack's 64 lanes: lane `u` encodes the block of `2^(μ-6)` cells at
`u·2^(μ-6)`. -/
def stackCodes (μ R : ℕ) (stack : Array K) : Array (Array K) :=
  let κ := μ - 6
  let tws := nttTwiddles (κ + R) κ
  Array.ofFn (n := 64) fun u ↦
    ntt tws κ R (Array.ofFn (n := 2 ^ κ) fun v ↦ stack.getD (v.val + 2 ^ κ * u.val) 0)

/-- **The stack's level-0 word**: leaf `p` holds the 64 lanes' codeword entries at `x_p`, in
reverse lane order; computed below `2^(μ-6+R)`, the encoder's formula above (never read by the
run). -/
@[macro_inline] def stackWordFast (μ R : ℕ) (stack : Array K) : Word :=
  stackWordOf μ R stack (stackCodes μ R stack)
where
  /-- The word from the lanes' codewords `codes`, computed once: the word is a closure over
  them (`stackWordFast` is inlined where it is used, so that `codes` is evaluated before the
  closure is formed). -/
  stackWordOf (μ R : ℕ) (stack : Array K) (codes : Array (Array K)) (p : ℕ) : List K :=
    if p < 2 ^ (μ - 6 + R) then ((List.range 64).map fun u ↦ (codes.getD u #[]).getD p 0).reverse
    else ((List.range 64).map fun u ↦
      encKAt (μ - 6) (fun x ↦ stack.getD (bitsToNat x + 2 ^ (μ - 6) * u) 0) p).reverse

/-- Limb `l` of an entry, `l < 3` (the last limb for larger `l`). -/
def limbAt (e : E) (l : ℕ) : K := if l = 0 then e.limb 0 else if l = 1 then e.limb 1 else e.limb 2

/-- The codewords of a level's lanes, limb by limb: entry `3j + l` encodes limb `l` of the lane
`j`, `x ↦ g[j + 2^k·x]`. -/
def levelCodes (κ k R : ℕ) (g : Array E) : Array (Array K) :=
  let tws := nttTwiddles (κ + R) κ
  Array.ofFn (n := 3 * 2 ^ k) fun jl ↦
    ntt tws κ R (Array.ofFn (n := 2 ^ κ) fun v ↦
      limbAt (g.getD (jl.val / 3 + 2 ^ k * v.val) 0) (jl.val % 3))

/-- **A deeper level's word**: leaf `p` holds the `2^k` lanes' entries at `x_p`, three limbs
each; computed below `2^(κ+R)`, the encoder's formula above (never read by the run). -/
@[macro_inline] def levelWordFast (κ k R : ℕ) (g : Array E) : Word :=
  levelWordOf κ k R g (levelCodes κ k R g)
where
  /-- The word from the lanes' codewords `codes`, computed once (as for `stackWordFast`). -/
  levelWordOf (κ k R : ℕ) (g : Array E) (codes : Array (Array K)) (p : ℕ) : List K :=
    if p < 2 ^ (κ + R) then
      (List.range (2 ^ k)).flatMap fun j ↦
        [(codes.getD (3 * j) #[]).getD p 0, (codes.getD (3 * j + 1) #[]).getD p 0,
          (codes.getD (3 * j + 2) #[]).getD p 0]
    else levelWord κ k g.toList p

end LeanVM.Prover

end
