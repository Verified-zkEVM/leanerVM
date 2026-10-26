module

public import Statement.Prover.Sumcheck

/-!
# Tables for the Keccak prover

Array helpers of the executable Keccak GKR prover (`KeccakLayer.lean`, `Keccak.lean`):

* `sumRange n f`: `Σ_{i < n} f i` as a loop;
* `eqTable pt`: the equality weights `eqKernel pt` built on arrays;
* `foldTab c t`: a table folded on its lowest coordinate at the challenge `c`;
* `addCoeffs`, `sumCoeffs`, `scaleCoeffs`: coefficient lists (constant first) added and scaled,
  the round polynomials of the sumchecks assembled from their summands';
* `packBits f n`: `n` booleans as the bits of a number; `byteSums v`: the `256` subset sums of
  eight values (a sum of weights selected by a byte is one table read);
* `addBits x g n acc`: `x` added to the entries of `acc` at the set bits of `g` below `n`.
-/

@[expose] public section

namespace LeanVM.Prover.KeccakGkr

open LeanVM.Parameters LeanVM.Protocol.Verifier

/-- `Σ_{i < n} f i`, as a loop. -/
def sumRange (n : ℕ) (f : ℕ → E) : E := (List.range n).foldl (fun acc i ↦ acc + f i) 0

/-- `eq_kernel(pt)` on arrays: the `2^|pt|` equality weights, the first coordinate the lowest
bit. -/
def eqTable (pt : List E) : Array E :=
  pt.foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) #[1]

/-- A table folded on its lowest coordinate at `c`: entry `u` is `t[2u] + c·(t[2u] + t[2u+1])`,
`(1 + c)·t[2u] + c·t[2u+1]`. -/
def foldTab (c : E) (t : Array E) : Array E :=
  Array.ofFn (n := t.size / 2) fun u ↦
    t.getD (2 * u.val) 0 + c * (t.getD (2 * u.val) 0 + t.getD (2 * u.val + 1) 0)

/-! ## Coefficient lists -/

/-- The sum of two coefficient lists of the same length. -/
def addCoeffs (a b : List E) : List E := List.zipWith (· + ·) a b

/-- `Σ_{i < n} v i` for coefficient lists of `k` entries. -/
def sumCoeffs (k n : ℕ) (v : ℕ → List E) : List E :=
  (List.range n).foldl (fun acc i ↦ addCoeffs acc (v i)) (List.replicate k 0)

/-- A coefficient list scaled. -/
def scaleCoeffs (s : E) (a : List E) : List E := a.map (s * ·)

/-! ## Bits -/

/-- The booleans `f 0, …, f (n - 1)` as the bits of a number. -/
def packBits (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => packBits f n ||| (if f n then 1 <<< n else 0)

/-- The `256` subset sums of `v 0, …, v 7`: entry `b` is `Σ_{t < 8, bit t of b} v t`. -/
def byteSums (v : ℕ → E) : Array E :=
  Array.ofFn (n := 256) fun b ↦
    (List.range 8).foldl (fun acc t ↦ if b.val.testBit t then acc + v t else acc) 0

/-- `Σ_{t < 64} [bit t of word]·v(t)` by eight reads of byte tables, `tabs[k]` the table of
`v(8k), …, v(8k + 7)`. -/
def wordDot (tabs : Array (Array E)) (word : ℕ) : E :=
  sumRange 8 fun k ↦ (tabs.getD k #[]).getD ((word >>> (8 * k)) % 256) 0

/-- The byte tables of `v(64·l + ·)`, for `wordDot`. -/
def laneTabs (v : ℕ → E) (l : ℕ) : Array (Array E) :=
  Array.ofFn (n := 8) fun k ↦ byteSums fun t ↦ v (64 * l + 8 * k.val + t)

/-- `x` added to the entries of `acc` at the set bits of `g` below `n`. -/
def addBits (x : E) (g : ℕ) : ℕ → Array E → Array E
  | 0, acc => acc
  | n + 1, acc => addBits x g n (if g.testBit n then acc.modify n (· + x) else acc)

end LeanVM.Prover.KeccakGkr

end
