module

public import Statement.LeanVmVerifier

/-!
# Tables as arrays

The verifier's list operations on tables (`LeanVmVerifier.lean`: `eqKernel`, `foldPairs`,
`multilinearEval`), on arrays, for the prover's tables of up to `2^D` entries:

* `eqTable point`: the `2^|point|` equality weights, the first coordinate the lowest bit
  (`eqKernel`);
* `foldPairsA r t`: one fold of `multilinear_eval`, adjacent pairs `(a, b)` becoming
  `a·(1 + r) + b·r` (`foldPairs`);
* `mleA t point`: the table's multilinear extension at the point (`multilinearEval`), one fold
  per coordinate;
* `mleK t point`: the same for a table over `K`, lifted to `E`.
-/

@[expose] public section

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Protocol.Verifier

/-- `eq_kernel(point)` on an array: the `2^|point|` equality weights, the first coordinate the
lowest bit. -/
def eqTable (point : List E) : Array E :=
  point.foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) #[1]

/-- One fold of `multilinear_eval` on an array: adjacent pairs `(a, b)` become `a·(1 + r) + b·r`
(a last odd entry is dropped). -/
def foldPairsA (r : E) (t : Array E) : Array E :=
  Array.ofFn (n := t.size / 2) fun i ↦
    t[2 * i.1]'(by omega) * (1 + r) + t[2 * i.1 + 1]'(by omega) * r

/-- `multilinear_eval(mle, point)` on an array: one fold per coordinate, the first coordinate
folding adjacent entries; `0` for an empty result. -/
def mleA (t : Array E) (point : List E) : E :=
  (point.foldl (fun cur r ↦ foldPairsA r cur) t).getD 0 0

/-- The multilinear extension of a table over `K`, lifted to `E`. -/
def mleK (t : Array K) (point : List E) : E := mleA (t.map ofK) point

end LeanVM.Prover

end
