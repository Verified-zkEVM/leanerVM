module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# PM-basis's price: the definitions

The price of CompPoly's divide-and-conquer approximant basis (`pmBasisWithFuelCore`,
`CompPoly/LinearAlgebra/PolynomialMatrix/Approximant/PMBasis/Recursion.lean:82`) as a function of
the problem's maximal order, for a node price `N` and a leaf price `L` given as functions (the
compiled code's prices are not yet known: these are the shapes its bounds will be instantiated
at). Here, apart from their proofs (`Bounds/PMBasis/Tree.lean`, `Recursion.lean`), so that the
numbers' checks (`Bounds/PMBasis/Values.lean`) import only what they evaluate.

* `pmTree c L N o`: the recursion's own tree on the maximal order `o`: a leaf (`o ≤ c` or
  `o ≤ 1`) at `L`, else `N o` and the two halves `⌊o/2⌋` (the lower orders) and `o − ⌊o/2⌋`
  (the residual orders), as `pmBasisWithFuelCore` splits;
* `pmTreePair c L N f q = (pmTree q, pmTree (q + 1))`, its evaluation in `f` steps (the orders at a
  depth are two consecutive numbers), for kernel evaluation (`pmTreePair_eq`);
* `pmLevels N K o = Σ_{k<K} 2^k·N(⌈o/2^k⌉)`, the per-level closed form
  (`pmTree_le_levels`: `pmTree ≤ pmLevels + L·o` for a monotone `N`, `o ≤ 2^K`);
* the price model of the FFT-based recursion (`evalMatPrice`, `pmNodePrice`, `pmLeafPrice`,
  `pmRootPrice`): stated per-operation prices, not yet a compiled function's.
-/

namespace LeanVM.Cost.Bounds.PMBasis

public section

/-! ## The recursion's tree -/

/-- **The divide-and-conquer tree on the maximal order** `o`, a leaf at most `c` (the leaf
cutoff) or at most `1` costing `L`, an inner node `N o` and its two children at the lower half
`o / 2` and the residual half `o − o / 2` (`pmBasisWithFuelCore`'s `d₁ := order / 2`,
`lowerOrders`, `residualOrders`). -/
@[expose] def pmTree (c L : ℕ) (N : ℕ → ℕ) (o : ℕ) : ℕ :=
  if o ≤ c ∨ o ≤ 1 then L else N o + pmTree c L N (o / 2) + pmTree c L N (o - o / 2)
termination_by o
decreasing_by all_goals omega

/-- One node of `pmTree` from its children's two possible values: at `x ∈ {q, q + 1}`, children
in `{h, h + 1}`, `h = q / 2`, priced `a` and `b`. -/
@[expose] def pmTreeStep (c L : ℕ) (N : ℕ → ℕ) (h a b x : ℕ) : ℕ :=
  if x ≤ c ∨ x ≤ 1 then L
  else N x + (if x / 2 = h then a else b) + (if x - x / 2 = h then a else b)

/-- `(pmTree q, pmTree (q + 1))` in `f` halvings (`q + 1 ≤ 2^f`): the orders at one depth of the
tree are two consecutive numbers, so the tree is evaluated in `log₂ q` steps. -/
@[expose] def pmTreePair (c L : ℕ) (N : ℕ → ℕ) : ℕ → ℕ → ℕ × ℕ
  | 0, _ => (L, L)
  | f + 1, q =>
    let ab := pmTreePair c L N f (q / 2)
    (pmTreeStep c L N (q / 2) ab.1 ab.2 q, pmTreeStep c L N (q / 2) ab.1 ab.2 (q + 1))

/-- **The per-level sum** `Σ_{k<K} 2^k·N(⌈o/2^k⌉)` (`pmLevels_eq_sum`), by its recurrence. -/
@[expose] def pmLevels (N : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | K + 1, o => N o + 2 * pmLevels N K ((o + 1) / 2)

/-! ## The price model -/

/-- The least `j` with `x ≤ 2^j` (`fuel ≥ x`). -/
@[expose] def clog2Aux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, x => if x ≤ 1 then 0 else clog2Aux f ((x + 1) / 2) + 1

/-- The least `j` with `x ≤ 2^j` (`le_two_pow_clog2`). -/
@[expose] def clog2 (x : ℕ) : ℕ := clog2Aux x x

/-- **The forward additive NTT over `2^j` points**: `novelFwd_cost` (`Bounds/FastPath.lean`) at
`κ = j`, `R = 0`, as `lean_vm` proves it of its compiled `novelFwd`. -/
@[expose] def nttFwdPrice (j : ℕ) : ℕ := j * (760 * 2 ^ j + 19793) + 30 * 2 ^ j + 42

/-- **The inverse additive NTT over `2^j` points**: `novelInv_cost` (`Bounds/FastPath.lean`). -/
@[expose] def nttInvPrice (j : ℕ) : ℕ := j * (760 * 2 ^ j + 19773) + 3

/-- **The conversion monomial ↔ novel basis** of `2^j` coefficients (model): at level `i < j`,
`2^(j−i−1)` divisions by the linearized `Ŵ_i` (`i + 1` terms, degree `2^i`), `2^i·(i + 1)`
multiply-adds each: `2^j·j(j + 1)/4` multiply-adds at `mac` each. -/
@[expose] def basisConvPrice (mac j : ℕ) : ℕ := mac * (j * (j + 1) * 2 ^ j / 4)

/-- **An evaluation-domain matrix product** (model): `R × S` of degree `≤ dA` by `S × T` of
degree `≤ dB` over `N = 2^j` points, `j = clog2 (dA + dB + 1)` (the doubling at exact powers of
two): `(R·S + S·T)` forward transforms, `R·T` inverse ones (each with its basis conversion), and
`R·S·T·N` pointwise multiply-adds. -/
@[expose] def evalMatPrice (mac R S T dA dB : ℕ) : ℕ :=
  (R * S + S * T) * (nttFwdPrice (clog2 (dA + dB + 1)) + basisConvPrice mac (clog2 (dA + dB + 1))) +
    R * T * (nttInvPrice (clog2 (dA + dB + 1)) + basisConvPrice mac (clog2 (dA + dB + 1))) +
    R * S * T * 2 ^ clog2 (dA + dB + 1) * mac

/-- **An inner node's own price** (model), at maximal order `o`, `d₁ = o / 2`, `r` rows, `m`
columns, the degree ≤ order invariant: the composition `P₂·P₁` (`r × r` of degree
`≤ o − d₁` by `r × r` of degree `≤ d₁`), the residual product `P₁·A` (`r × r` of degree `≤ d₁` by
`r × m` truncated to degree `< o`), and `ovh` per coefficient of the node's matrices read or
written besides (the residual's `divXTrunc`, the shift update, the row compaction), `2^20` per
node for the rest (orders, folds). -/
@[expose] def pmNodePrice (mac ovh r m o : ℕ) : ℕ :=
  evalMatPrice mac r r r (o - o / 2) (o / 2) + evalMatPrice mac r r m (o / 2) (o - 1) +
    ovh * (r * (2 * r + m) * (o + 1)) + 2 ^ 20

/-- **A leaf's price** (model): an order-`1` leaf of `r` rows, `8·r³` multiply-adds. -/
@[expose] def pmLeafPrice (mac r : ℕ) : ℕ := 8 * r ^ 3 * mac

/-- **The root pass** (model; `pmBasisNormalizeRoot` once weak Popov form is kept through the
compositions): `O(r²)` row scans of `r` rows of degree `≤ o`, `ovh` per coefficient. -/
@[expose] def pmRootPrice (ovh r o : ℕ) : ℕ := ovh * (r * r * (o + 1))

/-- **PM-basis's whole price** (model): the fuel's fold over the `m` orders, the recursion
(`pmTree`, cutoff `1`), the root pass. -/
@[expose] def pmBasisPrice (mac ovh rootOvh r m o : ℕ) : ℕ :=
  (64 * m + 100) + pmTree 1 (pmLeafPrice mac r) (pmNodePrice mac ovh r m) o + pmRootPrice rootOvh r o

end

end LeanVM.Cost.Bounds.PMBasis
