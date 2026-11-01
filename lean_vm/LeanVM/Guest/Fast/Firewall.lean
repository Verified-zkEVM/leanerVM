import LeanVM.Guest.Fast.GLanesCheck
import LeanVM.Guest.Fast.XmssTablesCheck
import LeanVM.Guest.Fast.SphincsTablesCheck
import LeanVM.Guest.Fast.WhirTablesCheck
import LeanVM.Guest.Fast.PreTable

/-! **The kernel-checked tables of the decoder's readers read the templates alone.** The checks
of `Fast/*TablesCheck.lean` evaluate the template generators in the kernel (`WhirTablesCheck` most
of a minute), and a module is rebuilt whenever what a module it imports exports changes. So they
import the literal tables, the numbers they are checked against (`Fast/Numbers.lean`) and the
templates (`B1/Sig/XmssT`, `SphincsTail`, `SphincsCoords`, `B1/Whir/InterfaceW`; the functions'
preconditions, `Fast/PreTable`, the certificates and `Fast/PreSig`), not the readers
(`Fast/Xmss`, `Sphincs`, `Whir`), the lemmas proving the numbers equal to the generators
(`Fast/Wots`, `SphincsN`, `LogG`), the schemes' soundness, `verify_sub`'s, `main`'s, the cost
compiler or the statement's end: an edit there rebuilds no table. This module, which imports the
five checks, fails to build if their imports reach any of those. -/

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let forbidden := [`LeanVM.Guest.Fast.Xmss, `LeanVM.Guest.Fast.Sphincs, `LeanVM.Guest.Fast.Whir,
    `LeanVM.Guest.Fast.Wots, `LeanVM.Guest.Fast.SphincsN, `LeanVM.Guest.Fast.LogG,
    `LeanVM.Guest.Fast.Common, `LeanVM.Guest.Fast.PreTest, `LeanVM.Guest.B1.Sig.XmssSound,
    `LeanVM.Guest.B1.Sig.SphincsSound,
    `LeanVM.Guest.B1.VerifySub, `LeanVM.Guest.B1.Main.SoundV, `LeanVM.Guest.B1.Main.Interface,
    `LeanVM.Cost, `LeanVM.Guest.End, `LeanVM.Guest.EndFinal, `Statement.Theorems,
    `Statement.Corollaries]
  let reached := (← getEnv).header.moduleNames.filter fun m ↦ forbidden.any (·.isPrefixOf m)
  unless reached.isEmpty do
    throwError m!"the decoder's table checks import {reached.toList}: keep the functions they \
      evaluate in modules that do not (see `LeanVM/Guest/Fast/Firewall.lean`)"
