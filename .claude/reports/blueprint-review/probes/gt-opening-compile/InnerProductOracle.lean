/-
Probe (task gt-opening-compile): is alternative (ii) expressible at the pins?

(ii) gives the stack an inner-product oracle interface: a query is a weight `W` on the cube, the
answer is `Σ_w W(w)·q(w)` (specification Definition 3.13). The probe checks that
  1. ArkLib's `OracleInterface` accepts `Weight n` (leanerVM's structure, in `Type`) as a query type;
  2. the evaluation query is the special case of the equality weight, by the built lemma
     `eqWeight_pair`;
  3. ArkLib's `Commitment.Scheme` over that interface has as opening statement
     (commitment, weight, claimed value): an inner-product commitment scheme;
  4. the opening phase "one challenge λ, then one weighted query" is an ArkLib `OracleVerifier`
     over a one-round schedule.
A wrapper `Stack` is used so that the probe's instance does not overlap the built `evalOracle`.
-/
import LeanerVM.Protocol.ClaimWeights
import LeanerVM.Protocol.ToArkLib.KeepOracles
import ArkLib.OracleReduction.Security.Basic

open LeanerVM.Protocol LeanerVM.Parameters CompPoly OracleComp OracleSpec ProtocolSpec

namespace Probe

structure Stack (n : ℕ) where
  col : Column n

/-- (ii): a query is a weight, the answer is the pairing. -/
instance innerProductOracle (n : ℕ) : OracleInterface (Stack n) where
  Query := Weight n
  toOC :=
    { spec := (Weight n) →ₒ E
      impl := fun W ↦ do return W.pair (← read).col }

theorem answer_eq (n : ℕ) (q : Stack n) (W : Weight n) :
    OracleInterface.answer q W = W.pair q.col := rfl

/-- The evaluation oracle of Layer 0 is the special case `W = eq(p, ·)`. -/
theorem answer_eqWeight (n : ℕ) (q : Stack n) (p : Vector E n) :
    OracleInterface.answer q (eqWeight p)
      = CMlPolynomialEval.eval₂Mle q.col.values (algebraMap K E) p :=
  eqWeight_pair p q.col

/-- Verbatim copy of `Commitment.Opening` (ArkLib `dca90385`,
`ArkLib/Commitments/Functional/Basic.lean:59-64`), whose module the build of `main` did not
compile (no leanerVM module imports it). -/
structure OpeningCopy {ι : Type} (oSpec : OracleSpec ι) (Data Commitment Decommitment ComKey VerifKey : Type)
    [O : OracleInterface Data] {n : ℕ} (pSpec : ProtocolSpec n) where
  opening : (ComKey × VerifKey) →
    Proof oSpec (Commitment × (q : O.Query) × O.Response q) (Data × Decommitment) pSpec

/-- Over the inner-product interface the statement of the opening is a commitment, a weight and
a claimed value: ArkLib's functional commitment scheme is then an inner-product commitment
scheme. -/
example (n : ℕ) {ι : Type} (oSpec : OracleSpec ι) (Cm Dec CK VK : Type) {m : ℕ}
    (pSpec : ProtocolSpec m)
    (S : OpeningCopy oSpec (Stack n) Cm Dec CK VK pSpec) (ck : CK) (vk : VK) :
    Proof oSpec (Cm × (W : Weight n) × E) (Stack n × Dec) pSpec :=
  S.opening (ck, vk)

/-! ## The opening phase as "λ, then one weighted query" -/

/-- One verifier message, the batching challenge. -/
@[reducible]
def openSpec : ProtocolSpec 1 := ⟨!v[.V_to_P], !v[E]⟩

instance : ∀ i, OracleInterface (openSpec.Message i)
  | ⟨0, h⟩ => nomatch h

instance : ∀ i, SampleableType (openSpec.Challenge i)
  | ⟨0, _⟩ => (inferInstance : SampleableType E)

abbrev OneStack (n : ℕ) : Fin 1 → Type := fun _ ↦ Stack n

/-- A pooled claim. -/
structure Claim (n : ℕ) where
  weight : Weight n
  value : E

/-- `W_λ = Σ_j λ^j W_j` on the cube. (The probe takes the extension as the evaluator; the closed
form the compiled verifier runs is `Σ_j λ^j W_j.mle`, equal to it by linearity.) -/
def batchWeight {n : ℕ} (lam : E) (cs : List (Claim n)) : Weight n where
  onCube := Vector.ofFn fun i ↦ (cs.zipIdx.map fun c ↦ lam ^ c.2 * c.1.weight.onCube.get i).sum
  mle := fun r ↦ CMlPolynomialEval.evalMle _ r
  mle_eq := fun _ ↦ rfl

/-- `C_λ = Σ_j λ^j c_j`. -/
def batchValue {n : ℕ} (lam : E) (cs : List (Claim n)) : E :=
  (cs.zipIdx.map fun c ↦ lam ^ c.2 * c.1.value).sum

/-- The one query of the opening phase. -/
def queryStack {n : ℕ} (W : Weight n) : OracleComp [OneStack n]ₒ E :=
  liftM <| OracleSpec.query (show [OneStack n]ₒ.Domain from ⟨0, W⟩)

/-- The opening verifier of (ii): read λ, query the stack at `W_λ`, compare with `C_λ`. -/
def openVerifier (n : ℕ) :
    OracleVerifier []ₒ (List (Claim n)) (OneStack n) Unit (OneStack n) openSpec where
  verify := fun cs chals ↦ do
    let lam : E := chals ⟨0, rfl⟩
    let a ← liftM (queryStack (batchWeight lam cs))
    if a = batchValue lam cs then pure () else failure
  outputOracle := .inl (keepOracles (OneStack n) openSpec)

#check @openVerifier
#print axioms openVerifier
#print axioms answer_eqWeight

end Probe
