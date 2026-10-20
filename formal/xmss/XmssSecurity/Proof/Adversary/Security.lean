import XmssSecurity.Proof.Adversary.Embedding
import XmssSecurity.Proof.Deterministic.Security

open OracleComp OracleSpec ENNReal
namespace XmssSecurity.Security

set_option backward.isDefEq.respectTransparency false

/-- The embedding preserves both the winning event and the complete hash-query budget. -/
theorem security127 : HasClassicalSecurityBits 127 := by
  intro q hq adversary hbound
  rw [← advantage_embed]
  apply Seeded.scheme_has_127_bits_of_classical_security q hq
  change ∀ result ∈ support ((simulateQ countedRomImpl
    (XmssSecurity.gameCore Seeded.scheme (embed adversary))).run.run' ∅), result.2 ≤ q
  rw [experiment_embed]
  exact hbound

end XmssSecurity.Security
