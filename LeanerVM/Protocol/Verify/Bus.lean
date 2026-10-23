/-
  LeanerVM.Protocol.Verify.Bus

  The executable verifier's bus phase: the chain walk's reads of the fingerprint challenges, the
  roots, the grand-product layers and the boundary values, and the algebra on them, which
  replays the layers and hands on the bus phase's output.
-/

module

public import LeanerVM.Protocol.Verify.Setup

/-!
# The bus phase of the verifier

Written from the specification's bus phase (§5.2–§5.4, the oracle verifier of
`LeanerVM.Protocol.Bus`) and transcribed for the stream order from the pinned leanVM
(`a386121f84292f6fa663aaa3e570c15bc0240ea2`): `crates/lean_vm/src/leaf.rs:864-935`
(`verify_balance`), `crates/lean_vm/src/gkr.rs:358-430` (`verify_product_triple`), and the second
verifier, `python-verifier/verifier.py:463-574` (`verify_gkr_grand_products`,
`verify_bus_balance`).

**The walk** (`walkBus`): the four fingerprint challenges `α` and `β`; the shared root of the
push and pull trees and the count root, two scalars; the first combiner; the layers from the root
down (`gkrRadices`: one binary layer first when the depth `μ_bus` is odd, quaternary layers
after); then the values of the boundary columns at the final point, one scalar per column of
`I.boundaryColumns`. A layer at depth `j` (`walkLayer`) is `j` normalized sumcheck rounds, each
`2^ρ` wire coefficients and a challenge (the cofactor of degree `2^ρ`, its constant coefficient
dropped), then the `2^ρ` descendants of each of the three trees, tree by tree, then the `ρ`
combination challenges, low bit first, and the next combiner. The last combiner is drawn too.

**The algebra** (`busStep`): the count root must not be zero; each layer combines the trees'
claims by the powers of its combiner (`powerBatch`), decodes its rounds against the running
claim with the equality weights of the point so far (`replayRounds`), checks the final claim
against the combination of the descendants' products (the oracle verifier's
`Gkr.combineCheck`), and moves to the point `(u, c)` with each tree's descendants interpolated at
`u` (`Gkr.interpDone`). The final point `ζ`, the three values and the boundary values make the
grand product's last statement, and the bus phase's output is the oracle verifier's
`Bus.busOut` of it, generic over the instance: the point `ζ_{<τ_max}`, the forms and totals of
the three sides and the boundary columns' claims.

**Differences from the Rust.** None in what is accepted. The Rust checks each layer as it reads
it; here every layer is read first and checked after, which rejects the same proofs.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics Blake2sHash LeanIsa CompPoly CMlPolynomialEval

@[expose] public section

namespace Verify

/-- A list as a vector of the given length, if it has that length. -/
def vec? {α : Type} (n : ℕ) (l : List α) : Option (Vector α n) :=
  if h : l.length = n then some ⟨l.toArray, by simpa using h⟩ else none

/-! ## The wire -/

/-- One layer of the grand product as read: its rounds, the descendants of the three trees, the
combination challenges and the combiner drawn after it. -/
structure GkrLayer where
  /-- The normalized sumcheck rounds. -/
  rounds : List Round
  /-- The descendants of each tree. -/
  children : List (List E)
  /-- The combination challenges, low bit first. -/
  combos : List E
  /-- The combiner drawn after the layer. -/
  combiner : E
  deriving Inhabited

/-- The bus phase as read. -/
structure BusWire where
  /-- The four fingerprint challenges `α`. -/
  alpha : List E
  /-- The fingerprint challenge `β`. -/
  beta : E
  /-- The root shared by the push and pull trees. -/
  shared : E
  /-- The count tree's root. -/
  count : E
  /-- The combiner drawn after the roots. -/
  combiner : E
  /-- The layers, from the root down. -/
  layers : List GkrLayer
  /-- The boundary columns' values at the final point. -/
  values : List E
  deriving Inhabited

/-- The radix exponents of the layers from the root down: one binary layer first when the depth
is odd, quaternary layers after (`gkr.rs:373-427`). -/
def gkrRadices (μ : ℕ) : List ℕ := (if μ % 2 = 1 then [1] else []) ++ List.replicate (μ / 2) 2

/-! ## The walk -/

section Walk

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest)

/-- The layer of radix `2 ^ ρ` at depth `j`: `j` rounds of `2 ^ ρ` wire coefficients, the
`2 ^ ρ` descendants of each tree, `ρ` combination challenges and the next combiner. -/
def walkLayer (ρ j : ℕ) : Walk m GkrLayer := do
  let rounds ← readRounds H (2 ^ ρ) j
  let c₀ ← Reader.nextScalars H (2 ^ ρ)
  let c₁ ← Reader.nextScalars H (2 ^ ρ)
  let c₂ ← Reader.nextScalars H (2 ^ ρ)
  let combos ← samples H ρ
  let combiner ← Reader.sample H
  return ⟨rounds, [c₀, c₁, c₂], combos, combiner⟩

/-- The layers of the given radix exponents, from depth `j` down. -/
def walkLayers : List ℕ → ℕ → Walk m (List GkrLayer)
  | [], _ => pure []
  | ρ :: rest, j => do
    let l ← walkLayer H ρ j
    let ls ← walkLayers rest (j + ρ)
    return l :: ls

/-- The bus phase's reads, at the leaf stacks' depth `μBus` and with `nValues` boundary
columns. -/
def walkBus (μBus nValues : ℕ) : Walk m BusWire := do
  let alpha ← samples H 4
  let beta ← Reader.sample H
  let shared ← Reader.nextScalar H
  let count ← Reader.nextScalar H
  let combiner ← Reader.sample H
  let layers ← walkLayers H (gkrRadices μBus) 0
  let values ← Reader.nextScalars H nValues
  return ⟨alpha, beta, shared, count, combiner, layers, values⟩

end Walk

/-! ## The algebra -/

/-- The descendants of the three trees, each a table on `ρ` variables. -/
def childTables (ρ : ℕ) : List (List E) → Option (Fin 3 → CMlPolynomialEval E ρ)
  | [a, b, c] => do
    let ta ← vec? (2 ^ ρ) a
    let tb ← vec? (2 ^ ρ) b
    let tc ← vec? (2 ^ ρ) c
    return ![ta, tb, tc]
  | _ => none

/-- The layers replayed from a point, the trees' claims there and a combiner: each layer's rounds
decoded against the combined claim with the point's equality weights, its descendants checked
against the final claim, and the next point and claims. Returns the final point and claims, or
`none` at the first failed check. -/
def replayGkr : List E → (Fin 3 → E) → E → List GkrLayer → Option (List E × (Fin 3 → E))
  | point, values, _, [] => some (point, values)
  | point, values, lam, l :: ls => do
    let ρ := l.combos.length
    let (final, xs) ← replayRounds (2 ^ ρ) (fun j ↦ point[j]?) 0 (powerBatch values lam)
      l.rounds
    let ch ← childTables ρ l.children
    if final ≠ powerBatch (fun t ↦ ∏ c : Fin (2 ^ ρ), (ch t)[c]) lam then none
    let u : Vector E ρ := ⟨l.combos.toArray, by simp [ρ]⟩
    replayGkr (l.combos ++ xs) (fun t ↦ evalMle (ch t) u) l.combiner ls

/-- The bus phase's algebra on its wire, for the statement `input` of an instance meeting the
bus phase's conditions: a nonzero count root, the layers replayed, and the bus phase's output,
`Bus.busOut` of the grand product's last statement and the boundary values. -/
def busStep (I : M3Instance) (h : Bus.Conditions I) (input : I.Stmt) (w : BusWire) :
    Option (I.Stmt × BusOut I) := do
  let α ← vec? 4 w.alpha
  if w.count = 0 then none
  let (ζ, vs) ← replayGkr [] ![w.shared, w.shared, w.count] w.combiner w.layers
  let ζ ← vec? I.μBus ζ
  let vals ← vec? I.busClaims w.values
  let ℓ : Gkr.LayerStmt (Bus.Data I) E 3 I.μBus := ((input, (fun i ↦ α[i], w.beta)), (ζ, vs))
  return (input, Bus.busOut h ℓ vals)

/-- The bus phase's algebra for leanVM's instance. -/
def leanVmBus (prog : Program) (s : Sizes) (input : PublicInput) (w : BusWire) :
    Option (PublicInput × BusOut (leanVm prog s)) :=
  busStep (leanVm prog s) (leanIsa_conditions _ prog s) input w

end Verify

end
end LeanerVM.Protocol
