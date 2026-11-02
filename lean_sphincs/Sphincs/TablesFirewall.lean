import Sphincs.H0FTab.F
import Sphincs.H0FTab.F2_0
import Sphincs.H0FTab.F2_1
import Sphincs.H0FTab.F2
import Sphincs.H0FTab
import Sphincs.H0PTab.Mu
import Sphincs.H0PTab.H
import Sphincs.H0PTab.NuTab
import Sphincs.H0PTab.Nu0
import Sphincs.H0PTab.Nu1
import Sphincs.H0PTab.G
import Sphincs.H0PTab.P1
import Sphincs.H0PTab.P2Tab
import Sphincs.H0PTab.P2_0
import Sphincs.H0PTab.P2_1
import Sphincs.H0PTab
import Sphincs.H0NTab.PH
import Sphincs.H0NTab
import Sphincs.LifetimeCertificates.B26
import Sphincs.LifetimeCertificates.B20
import Sphincs.LifetimeCertificates.B14
import Sphincs.LifetimeCertificates.B13
import Sphincs.LifetimeCertificates.B12
import Sphincs.LifetimeCertificates.B10
import Sphincs.LifetimeCertificates.B8
import Sphincs.LifetimeCertificates

/-! **The kernel-checked tables read numbers alone.** The tables (`H0FTab/`, `H0PTab/`, `H0NTab/`,
`LifetimeCertificates/`, one module per table, per stage of the moment tables or per range of a
table's rows, joined by `H0FTab`, `H0PTab`, `H0NTab` and `LifetimeCertificates`) take most of this
project's build (kernel evaluation), and a module is rebuilt whenever anything it imports changes. So
they import only the functions they evaluate and their numeric facts (`LayeredForest`, the moment
chain `H0Moments` … `H0Tables`, `H0MomCert`, `H0MomTabs`, `H0NearMom`, `SphincsFors.H0Round`,
`LifetimeCheck`, `H0Fill`), and none of the scheme (`Sphincs.Layered`), the statement, `common` or the
security proofs: an edit there rebuilds no table. This module, which imports every table module,
fails to build if their imports reach any of them. -/

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let forbidden := [`Statement, `Common, `LeanXmss, `VCVio, `Sphincs.Layered]
  let reached := (← getEnv).header.moduleNames.filter fun m ↦ forbidden.any (·.isPrefixOf m)
  unless reached.isEmpty do
    throwError m!"the kernel-checked tables import {reached.toList}: keep the functions they \
      evaluate in modules that do not (see `Sphincs/TablesFirewall.lean`)"
