import LeanVM.Guest.B2C.Cpl
import LeanVM.Guest.B2C.ShareStatic
import LeanVM.Guest.CheckWinC

/-! **The compiled functions' certificates do not read the verifier's statement.** The
certificates of `B2C/Cplw`, `B2C/Shared` and `Checked` (about 7.5 CPU-h of kernel evaluation)
read the guest's code, the ISA and the field (`Statement.Field`, with `eOfNat` and `gen`), not
the verifier (`Statement.LeanVmVerifier`), so that an edit of the verifier's statement rebuilds
none of them (`CertFirewall.lean` guards the rest of their imports; the memory layer's
certificates read the verifier's numbers through `Value.Tower`). This module, which imports their
three bases, fails to build if their imports reach the verifier or the guest's values. -/

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let forbidden := [`Statement.LeanVmVerifier, `LeanVM.Guest.Value]
  let reached := (← getEnv).header.moduleNames.filter fun m ↦ forbidden.any (·.isPrefixOf m)
  unless reached.isEmpty do
    throwError m!"the compiled functions' certificates import {reached.toList}: keep the \
      functions they evaluate in modules that do not (see \
      `LeanVM/Guest/B2C/CertFirewallVerifier.lean`)"
