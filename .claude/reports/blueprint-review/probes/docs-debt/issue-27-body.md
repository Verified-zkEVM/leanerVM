Tracks #12, Layer 1/A6; implementation #26, with the catalogue correction in #25. This claims the coefficient-transport extension of #18, not its existing algebra or the whole layer.

Targets in `LeanerVM.Protocol.Blocks`: `map`, `map_offsetNat`, `map_offset`, `map_total`, `map_stackAt`, `stack_eval₂`. Transport maps both data and padding without injectivity or a fit premise; mixed-ring selection retains the fit premise.

Consumer: the `K`-column/`E`-challenge readout used by Layers 3 and 10. Prerequisite: scaraven's #18 (`41b79b3`); its owner retains the rebase and adoption. Natural upstream: [ArkLib #900](https://github.com/Verified-zkEVM/ArkLib/issues/900).

Source: [leanth PR #16 at 23929f8c](https://github.com/Verified-zkEVM/leanth/pull/16/commits/23929f8c922cd4461ab22dbfaa6520f3ad23a3b2), adapted to the current little-endian CompPoly tables. Category A algebra, following the blueprint's stack convention; no deployed-verifier correspondence claim.

Acceptance: `./scripts/validate.sh`; focused Stacking tests for noninjective maps, transported padding, extension points and empty layouts; transitive axiom checks for new definitions/theorems and test proofs. Current header repairs are under review. #25 changes catalogue/source descriptions only and is checked separately.
