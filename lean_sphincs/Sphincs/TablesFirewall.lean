import Sphincs.LifetimeCertificates

/-! **The kernel-checked tables read numbers alone.** `H0FTab`, `H0PTab`, `H0NTab` and
`LifetimeCertificates` take most of this project's build (minutes each, kernel evaluation), and a
module is rebuilt whenever anything it imports changes. So they import only the functions they
evaluate and their numeric facts (`LayeredForest`, the moment chain `H0Moments` … `H0Tables`,
`H0MomCert`, `H0NearMom`, `SphincsFors.H0Round`, `LifetimeCheck`, `H0Fill`), and none of the scheme
(`Sphincs.Layered`), the statement, `common` or the security proofs: an edit there rebuilds no
table. This module, which imports the last table alone, fails to build if its imports reach any
of them. -/

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let forbidden := [`Statement, `Common, `LeanXmss, `VCVio, `Sphincs.Layered]
  let reached := (← getEnv).header.moduleNames.filter fun m ↦ forbidden.any (·.isPrefixOf m)
  unless reached.isEmpty do
    throwError m!"the kernel-checked tables import {reached.toList}: keep the functions they \
      evaluate in modules that do not (see `Sphincs/TablesFirewall.lean`)"
