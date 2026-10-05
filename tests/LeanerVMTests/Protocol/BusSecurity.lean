import LeanerVM.Protocol.BusSecurity
import LeanerVMTests.Protocol.Bus

/-!
# Bus phase knowledge-soundness tests

* **The theorem has an inhabitant that computes** at the slot's error `busError`: `busSecurity`
  on the bus tests' instance and on the spine's toy is a `def` without `noncomputable`, and so is
  its extraction, the extractor and the knowledge state function the spine's composition reads.

* **The challenges' bound rests on the products.** A stack whose only failing clause is the
  balance (`a = [1, 0]`: the push tuple `(0, x + 1)` is pulled as `(1, x + 1)`) has different
  products at the tests' challenge: the state after the challenges is false there, and true only
  at a collision.

The refutation of the check `R_c ≠ 0` is in the bus tests (`roots_unchecked_no_stateFunction`).
-/

namespace LeanerVMTests.Protocol.BusSecurity

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Bus LeanerVMTests.Protocol.Bus
  CompPoly CMlPolynomialEval

/-! ## The theorem has an inhabitant -/

/-- Knowledge soundness of the bus phase on the bus tests' instance, at the slot's error. -/
def security : Phase.Security busToy (busPhase busToy conditions).toDef (Seam.commit busToy)
    (Seam.bus busToy) (busError busToy) :=
  busSecurity busToy conditions

/-- Its extraction. -/
def extraction : Component.Extraction (busPhase busToy conditions).toDef (Seam.commit busToy)
    (Seam.bus busToy) :=
  security.toExtraction

/-- Knowledge soundness of the bus phase on the spine's toy. -/
def toySecurity : Phase.Security Toy.toy (busPhase Toy.toy toyConditions).toDef
    (Seam.commit Toy.toy) (Seam.bus Toy.toy) (busError Toy.toy) :=
  busSecurity Toy.toy toyConditions

/-! ## The challenges' bound rests on the products -/

/-- `a = [1, 0]`: Boolean, counts nonzero, but unbalanced. -/
def unbalanced : Column 2 := ⟨#v[1, 0, K.ofBits 2, K.ofBits 3]⟩

#guard busToy.ConstraintsVanish unbalanced ∧ busToy.CountsNonzero unbalanced
#guard ¬ busToy.Balanced unbalanced
#guard ¬ M3Holds busToy () unbalanced

/-- Its push and pull leaf stacks at the tests' challenge. -/
def pushUnbalanced : CMlPolynomialEval E busToy.μBus := pushLeaves busToy α β unbalanced
def pullUnbalanced : CMlPolynomialEval E busToy.μBus := pullLeaves busToy α β unbalanced

#guard (∏ x : Fin (2 ^ busToy.μBus), pushUnbalanced[x]) ≠
  ∏ x : Fin (2 ^ busToy.μBus), pullUnbalanced[x]

end LeanerVMTests.Protocol.BusSecurity
