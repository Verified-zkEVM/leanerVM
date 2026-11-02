import LeanVM.Cost.Bounds.DecoderShapes

/-! **The decoder's shape check reads numbers alone.** `DecoderShapes`' kernel evaluation
(Roth–Ruckenstein's search at `(28, 4)`) is slow, and a module is rebuilt whenever anything it
imports changes. So it imports only the functions they evaluate (the extractor's parameter search,
`LeanVM.Protocol.Extraction.Extractor`), the bounds as definitions
(`Bounds/Decoder/ShapeDefs.lean`) and the prices they are checked against (`Cost/Prices.lean`,
definitions over the statement alone), none of the cost compiler, the compiled extractor or the
bounds' proofs: an edit there rebuilds no check. This module, which imports the check alone,
fails to build if its imports reach any other `LeanVM.Cost` module. -/

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let allowed := [`LeanVM.Cost.Bounds.Decoder.ShapeDefs, `LeanVM.Cost.Bounds.DecoderShapes,
    `LeanVM.Cost.Prices]
  let reached := (← getEnv).header.moduleNames.filter fun m ↦
    (`LeanVM.Cost).isPrefixOf m && !allowed.contains m
  unless reached.isEmpty do
    throwError m!"the decoder's shape checks import {reached.toList}: keep the definitions they \
      evaluate in modules that do not (see `Bounds/DecoderShapesFirewall.lean`)"
