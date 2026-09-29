/-
  LeanerVM.Protocol.Field

  The instances that make leanVM's fields usable by ArkLib's oracle-reduction framework: uniform
  sampling of challenges in `E`, and the evaluation oracle on a committed column.
-/

module

public import LeanerVM.Parameters.Field
public import CompPoly.Multilinear.Basic
public import ArkLib.OracleReduction.OracleInterface
public import VCVio.OracleComp.Constructions.SampleableType

/-!
# Fields for the proof system

Protocol roadmap Layer 0 (`docs/roadmap/protocol-blueprint.md`). This is the first consumer of
ArkLib (pin `fa14552d40e793f2ea26e65c440306aae0c08a26`) and of VCVio through it
(`7a4d7ee254165f2fcf3282c7d2e6f204056e5121`). Category A: nothing here transcribes a source; the
field and its cardinality are the leanISA Layer 0 declarations and CompPoly's `card_ext3`.

Four things are supplied.

* `SampleableType K` and `SampleableType E`: the uniform samplers ArkLib requires of every
  challenge type (`[∀ i, SampleableType (pSpec.Challenge i)]` on its security definitions).
  `K` is sampled as a uniform `Fin (2^64)` through `BitVec.ofFin` and `BF64.ofBitVec`, and `E`
  as three independent limbs through `Ext.ofVector`; neither enumerates the field.
  `Fintype K` is proof-only; compiled sampling uses the explicit equivalences (leanISA status
  finding P3). The shape follows ArkLib's
  own `KoalaBear.Ext6.sampleableType`.
* `card_E`: `Fintype.card E = 2^192`, the one cardinality fact every error bound of the roadmap
  rewrites with.
* `evalOracle`: the `OracleInterface` on a column `Column n = CMlPolynomialEval K n`, the value
  table of a multilinear on `n` variables. A query is a point of `E^n`, as CompPoly's
  `Vector E n`, and the answer is the multilinear extension there, lifted from `K` to `E` by
  `algebraMap`. This is the interface of the one committed oracle of the oracle protocol
  (roadmap convention *The oracle*); the Reed–Solomon codeword oracles of Layer 11 are a
  different instance on a different type.
* `OracleInterface E` and `OracleInterface (List E)`: the trivial oracle, ArkLib's
  `OracleInterface.instDefault` (the query is `Unit`, the answer is the whole message), for the
  scalars and coefficient lists a phase sends. ArkLib registers that default for no type, and
  every component's schedule needs an interface on each prover message.

## Wrong readings excluded

* A sampler built from `Fintype E` (`SampleableType.ofFintype`) is noncomputable and, on `K`,
  enumerates `2^64` elements at initialization; `samplerProbe` in the tests fails to compile if
  either instance stops having compiler IR.
* The oracle answers `q̃(r)` for `r ∈ E^n`, not `q(r)` for `r` on the cube; on a cube point the
  two agree (`CMlPolynomialEval.eval_mle_eq_eval`).
* `Column n` is not `Vector K (2^n)`: were it an abbreviation, instance search would also find
  ArkLib's `OracleInterface (Vector α m)`, whose queries are positions, and a column could be
  queried as a codeword.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly OracleComp

@[expose] public section

/-! ## Columns -/

/-- A column of height `2^n`: the values of a `K`-multilinear on the cube, low bit first. A
structure rather than an abbreviation so that its evaluation oracle below does not overlap
ArkLib's position-query interface on `Vector`, which Layer 11's codeword oracles use. -/
structure Column (n : ℕ) where
  /-- The value table, CompPoly's hypercube representation. -/
  values : CMlPolynomialEval K n

/-! ## Sampling -/

/-- `K` as the `2^64` bit patterns, the `BitVec` view of `Fin (2^64)`. -/
def finEquivK : Fin (2 ^ 64) ≃ K where
  toFun := fun i ↦ BF64.ofBitVec (BitVec.ofFin i)
  invFun := fun x ↦ x.toBitVec.toFin
  left_inv _ := rfl
  right_inv _ := rfl

/-- Uniform sampling of `K`: a uniform `Fin (2^64)` read as a bit pattern. -/
instance instSampleableTypeK : SampleableType K :=
  haveI : NeZero (2 ^ 64) := ⟨by norm_num⟩
  SampleableType.ofEquiv finEquivK

/-- `E` as its three limbs, CompPoly's carrier view. -/
def limbsEquiv : Vector K 3 ≃ E where
  toFun := fun v ↦ CompPoly.Extension.Ext.ofVector (P := BF64.ext3Params) v
  invFun := fun x ↦ CompPoly.Extension.Ext.coeffs (P := BF64.ext3Params) x
  left_inv _ := rfl
  right_inv _ := rfl

/-- Uniform sampling of `E`: three independent uniform limbs. -/
instance instSampleableTypeE : SampleableType E := SampleableType.ofEquiv limbsEquiv

/-- `|E| = 2^192`: the size of the challenge space in every error bound. -/
theorem card_E : Fintype.card E = 2 ^ 192 := BF64.card_ext3

/-! ## The evaluation oracle -/

/-- A column as an oracle: a query is a point `r ∈ E^n`, the answer is the multilinear extension
`q̃(r)`, lifted from `K` to `E`. -/
instance evalOracle (n : ℕ) : OracleInterface (Column n) where
  Query := Vector E n
  toOC :=
    { spec := (Vector E n) →ₒ E
      impl := fun r ↦ do return CMlPolynomialEval.eval₂Mle (← read).values (algebraMap K E) r }

/-- The oracle answers the lifted multilinear extension. -/
theorem evalOracle_answer (n : ℕ) (q : Column n) (r : Vector E n) :
    OracleInterface.answer q r = CMlPolynomialEval.eval₂Mle q.values (algebraMap K E) r := rfl

/-! ## Scalar messages -/

/-- A scalar the prover sends is queried trivially: the answer is the scalar. -/
instance instOracleInterfaceE : OracleInterface E := OracleInterface.instDefault

/-- A list of scalars the prover sends is queried trivially: the answer is the list. -/
instance instOracleInterfaceListE : OracleInterface (List E) := OracleInterface.instDefault

end
end LeanerVM.Protocol
