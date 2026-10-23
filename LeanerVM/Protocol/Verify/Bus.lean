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

**The algebra** (`busReplay`, `busStep`): the count root must not be zero; the layers have the
shapes the depth fixes (`gkrRadices`, `m` rounds and `ρ` combination challenges at depth `m`);
each layer combines the trees' claims by the powers of its combiner (`powerBatch`), decodes its
rounds against the running claim with the equality weights of the point so far
(`replayRounds`), checks the final claim against the combination of the descendants' products
(the oracle verifier's `Gkr.combineCheck`), and moves to the point `(u, c)` with each tree's
descendants interpolated at `u` (the oracle verifier's `Gkr.interpDone`). The final point `ζ`,
the three values and the boundary values make the grand product's last statement, and the bus
phase's output is the oracle verifier's `Bus.busOut` of it, generic over the instance: the point
`ζ_{<τ_max}`, the forms and totals of the three sides and the boundary columns' claims.

**The program's share** (`leanVmBus`). At leanVM's instance the two bytecode blocks' entry
coordinates, slots `3` to `10`, are the program's columns; their part of the totals is one value,
the bytecode multilinear `B̃(ζ_{<κ_bc}, α) = Σ_k eq(α, 3 + k)·P̃_k(ζ_{<κ_bc})`
(`bytecodeShare_eq`). The verifier settles it by evaluating the multilinear
(`settleFixedClaims`) and hands it to the totals (`busOutWith`), which evaluate every other
coordinate as `Bus.busOut` does; a recursive verifier defers that one claim instead.

**Differences from the Rust.** None in what is accepted. The Rust checks each layer as it reads
it; here every layer is read first and checked after, which rejects the same proofs. The Rust's
totals evaluate the entry columns one by one (`leaf.rs:453`); here they take the program's share
as one multilinear, the same value (`bytecodeShare_eq`).
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics Blake2sHash LeanIsa CompPoly CMlPolynomialEval

@[expose] public section

namespace Verify

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
    let ta ← RoundPoly.ofList? (2 ^ ρ) a
    let tb ← RoundPoly.ofList? (2 ^ ρ) b
    let tc ← RoundPoly.ofList? (2 ^ ρ) c
    return ![ta, tb, tc]
  | _ => none

/-- The layers replayed from the layer statement `ℓ` on `m` variables and a combiner, at the
radix exponents `ρs` the depth fixes (`gkrRadices`): a layer has `m` rounds and `ρ` combination
challenges, its rounds are decoded against the combined claim with the point's equality weights,
its descendants are checked by the oracle verifier's `Gkr.combineCheck`, and the next statement
is its `Gkr.interpDone`. The last statement, or `none` at the first failed check or a layer of
another shape. -/
def replayGkr {X : Type} : List ℕ → (m : ℕ) → Gkr.LayerStmt X E 3 m → E → List GkrLayer →
    Option (Σ n, Gkr.LayerStmt X E 3 n)
  | [], m, ℓ, _, [] => some ⟨m, ℓ⟩
  | ρ :: ρs, m, ℓ, lam, l :: ls => do
    let (final, xs) ← replayRounds (2 ^ ρ) (fun j ↦ ℓ.2.1[j]?) 0 (powerBatch ℓ.2.2 lam) l.rounds
    let c ← RoundPoly.ofList? m xs
    let u ← RoundPoly.ofList? ρ l.combos
    let ch ← childTables ρ l.children
    let st : SumcheckRound.Stmt (Gkr.LayerX X E 3 m) E m := ((ℓ, lam), (c, final))
    if !Gkr.combineCheck 3 ρ m st ch then none
    replayGkr ρs (m + ρ) (Gkr.interpDone 3 ρ m ((ℓ.1, (c, ch)), u)) l.combiner ls
  | _, _, _, _, _ => none

/-- The grand product replayed for the statement `input` of an instance: a nonzero count root,
the layers from the roots, and the grand product's last statement on `μ_bus` variables with the
boundary values. -/
def busReplay (I : M3Instance) (input : I.Stmt) (w : BusWire) :
    Option (Gkr.LayerStmt (Bus.Data I) E 3 I.μBus × Vector E I.busClaims) := do
  let α ← RoundPoly.ofList? 4 w.alpha
  if w.count = 0 then none
  let x : Bus.Data I := (input, (fun i ↦ α[i], w.beta))
  let ⟨n, ℓ⟩ ← replayGkr (gkrRadices I.μBus) 0 (x, (#v[], ![w.shared, w.shared, w.count]))
    w.combiner w.layers
  if hn : n = I.μBus then
    let vals ← RoundPoly.ofList? I.busClaims w.values
    return (by subst hn; exact ℓ, vals)
  else none

/-- The bus phase's algebra on its wire, for the statement `input` of an instance meeting the
bus phase's conditions: the grand product replayed (`busReplay`), and the bus phase's output,
`Bus.busOut` of its last statement and the boundary values. -/
def busStep (I : M3Instance) (h : Bus.Conditions I) (input : I.Stmt) (w : BusWire) :
    Option (I.Stmt × BusOut I) := do
  let (ℓ, vals) ← busReplay I input w
  return (input, Bus.busOut h ℓ vals)

/-! ## The program's share -/

/-- The bytecode multilinear at `(z, α)`, `B̃(z, α)` (`leaf.rs:627-637`, `bytecode_claim`;
`verifier.py:563`). -/
def bytecodeShare (prog : Program) (z : Vector E prog.logSize) (α : Fin 4 → E) : E :=
  eval₂Mle (bytecodeColumn prog).values (algebraMap K E) (z ++ Vector.ofFn α)

/-- **The program's share is the known columns' evaluation**: the bytecode multilinear at
`(z, α)` is `Σ_k eq(α, 3 + k)·P̃_k(z)`, the eight entry columns at the slots `3` to `10` of the
fingerprint, which the leanISA instance's bytecode blocks evaluate column by column
(`LeanIsa.entryCoord`). -/
theorem bytecodeShare_eq (prog : Program) (z : Vector E prog.logSize) (α : Fin 4 → E) :
    bytecodeShare prog z α = ∑ k : Fin 8, (fingerprintWeights α)[3 + k.val] *
      eval₂Mle (entryColumn prog k).values (algebraMap K E) z := by
  rw [bytecodeShare, bytecodeColumn_eval, bytecodeColumnEval]
  simp only [fingerprintWeights]
  have hk : ∀ k : Fin 8, eval₂Mle (entryColumn prog k).values (algebraMap K E) z =
      ∑ i : Fin (2 ^ prog.logSize), algebraMap K E
        ((Arithmetization.encodeSlots (prog.code i))[3 + k.val]'(by omega)) *
          (lagrangeBasis z)[i] := by
    intro k
    rw [eval₂Mle, evalMle_eq_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [CMlPolynomialEval.map, entryColumn, Vector.getElem_map, Vector.getElem_ofFn,
      Fin.getElem_fin]
    congr 2
    fin_cases k <;> rfl
  simp only [hk]
  simp [Fin.sum_univ_succ, Arithmetization.encodeSlots]

/-- The claims on the fixed public polynomials. -/
structure FixedClaims where
  /-- The program's share of the bytecode blocks at the bus point, `B̃(ζ_{<κ_bc}, α)`. -/
  bytecode : E

/-- The claims on the fixed public polynomials, settled by evaluating them: the bytecode
multilinear at the bus point `ζ` and the fingerprint challenges `α` (`bytecodeShare`). A
recursive verifier replaces this one function by a deferred claim (`VerifySummary`,
`cpu/mod.rs:683-700`); `none` if `ζ` is shorter than the program's index. -/
def settleFixedClaims (prog : Program) {μ : ℕ} (ζ : Vector E μ) (α : Fin 4 → E) :
    Option FixedClaims := do
  let z ← RoundPoly.ofList? prog.logSize (ζ.toList.take prog.logSize)
  return ⟨bytecodeShare prog z α⟩

/-- The bytecode's two boundary blocks, read off their channel coordinate (`LeanIsa.boundary`);
their slots `3` to `10` are the program's entry columns. -/
def isBytecodeBlock {S : Shape} {κ : ℕ} (cs : Vector (Coord S κ) 16) : Bool :=
  match cs[0] with
  | .const c => c == Arithmetization.channelSep Arithmetization.BytecodePush.toRaw ||
      c == Arithmetization.channelSep Arithmetization.BytecodePull.toRaw
  | _ => false

/-- A block's part evaluated from the values sent (`Bus.Source.boundaryValue`), the program's
share `share` standing for a bytecode block's entry columns, which are not evaluated. -/
def boundaryValueWith {I : M3Instance} (share : E) (α : Fin 4 → E) (β : E)
    (vals : Vector E I.busClaims) : (src : Bus.Source I) → Vector E src.κ → E
  | .boundary b, z =>
    let w := fingerprintWeights α
    if isBytecodeBlock b.coords then
      β - ((∑ i : Fin 16, if 3 ≤ i.val ∧ i.val < 11 then 0
        else w[i.val] * Bus.coordValue vals b.coords[i] z) + share)
    else β - ∑ i : Fin 16, w[i.val] * Bus.coordValue vals b.coords[i] z
  | .flush _ _, _ | .count _ _, _ => 0

/-- Side `k`'s total (`Bus.total`), the program's share supplied. -/
def totalWith {I : M3Instance} (h : Bus.Conditions I) (share : E) (k : Fin 3) (α : Fin 4 → E)
    (β : E) (ζ : Vector E I.μBus) (v : E) (vals : Vector E I.busClaims) : E :=
  v - ((∑ b, Bus.weight h k b ζ *
      boundaryValueWith share α β vals (Bus.src I k b) (Bus.lowAt h k b ζ)) +
    (1 + ∑ b, Bus.weight h k b ζ))

/-- The bus phase's output (`Bus.busOut`), its totals with the program's share `share` supplied
for the bytecode blocks' entry columns. -/
def busOutWith {I : M3Instance} (h : Bus.Conditions I) (share : E)
    (ℓ : Gkr.LayerStmt (Bus.Data I) E 3 I.μBus) (vals : Vector E I.busClaims) : BusOut I :=
  { Bus.busOut h ℓ vals with
    totals := fun k ↦ totalWith h share k ℓ.1.2.1 ℓ.1.2.2 ℓ.2.1 (ℓ.2.2 k) vals }

/-- The bus phase's algebra for leanVM's instance: the grand product replayed, the program's
share settled at its last point (`settleFixedClaims`), and the output with that share. -/
def leanVmBus (prog : Program) (s : Sizes) (input : PublicInput) (w : BusWire) :
    Option (PublicInput × BusOut (leanVm prog s)) := do
  let (ℓ, vals) ← busReplay (leanVm prog s) input w
  let fixed ← settleFixedClaims prog ℓ.2.1 ℓ.1.2.1
  return (input,
    busOutWith (I := leanVm prog s) (leanIsa_conditions _ prog s) fixed.bytecode ℓ vals)

end Verify

end
end LeanerVM.Protocol
