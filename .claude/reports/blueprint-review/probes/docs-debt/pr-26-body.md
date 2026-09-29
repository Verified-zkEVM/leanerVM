Add coefficient transport and mixed-ring selection for aligned stacks (Layer 1). Transport maps padding and data without injectivity or fit; selection retains fit. Targets #18; tracks #27, #12 and [ArkLib #900](https://github.com/Verified-zkEVM/ArkLib/issues/900).

Ports [leanth PR #16 at 23929f8c](https://github.com/Verified-zkEVM/leanth/pull/16/commits/23929f8c922cd4461ab22dbfaa6520f3ad23a3b2) to the little-endian CompPoly API, preserving source attribution.

Local validation at `40746d8`: `./scripts/validate.sh`, focused stacking tests and module/test axiom audits pass. Controls cover noninjective maps, padding, extension points and empty layouts. GitHub has no Lean check on this base.
