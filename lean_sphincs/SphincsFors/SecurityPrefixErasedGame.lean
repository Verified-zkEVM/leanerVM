import SphincsFors.SecurityPrefixErasedKeygen

/-! The fixed-function cost world (`fixedWorldCost`: private draws are free, hash queries cost one
each), and how mapping the base monad commutes with query logging and with lifting. -/

open OracleComp OracleSpec

namespace SphincsFors.Security.Prefix
open Concrete Completeness SeedModel PreparedScheme MaterialGameCoupling
open SeedCoupling
open SphincsBase.QueryCap

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000
attribute [local irreducible] PreparedScheme.sign PreparedScheme.keygen
  Randomized.sign digestAttemptLimit encodingAttemptLimit erasedMaterialSign
  preparedOracle answer

noncomputable def fixedWorldCost (f : QueryImpl HashSpec Id) :
    QueryImpl OracleWorld (AddWriterT Nat PMF) :=
  (fixedHashWorld f).withAddCost (fun | .inl _ => 0 | .inr _ => 1)

end SphincsFors.Security.Prefix
