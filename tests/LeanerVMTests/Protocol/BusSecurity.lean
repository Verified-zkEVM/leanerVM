import LeanerVM.Protocol.BusSecurity
import LeanerVMTests.Protocol.Bus

/-!
# Bus phase knowledge-soundness tests

* **The theorem has an inhabitant that computes** at the slot's error `busError`: `busSecurity`
  on the bus tests' instance and on the spine's toy is a `def` without `noncomputable`, and so is
  its extraction, the extractor and the knowledge state function the spine's composition reads.

The refutation of the check `R_c ≠ 0` is in the bus tests (`roots_unchecked_no_stateFunction`).
-/

namespace LeanerVMTests.Protocol.BusSecurity

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Bus LeanerVMTests.Protocol.Bus

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

end LeanerVMTests.Protocol.BusSecurity
