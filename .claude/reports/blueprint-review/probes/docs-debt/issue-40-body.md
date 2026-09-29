Prove the ambient evaluation formula for aligned stacks with arbitrary padding and coefficient transport. The formula includes the uncovered padding weight, so it supports both zero-padded witnesses and one-padded product trees for the Layer 6 leaf decomposition.

Built on #18 for #36 and [ArkLib #900](https://github.com/Verified-zkEVM/ArkLib/issues/900), following leanVM §5.4. Extends the zero-padding result from [leanth #16 at `23929f8`](https://github.com/Verified-zkEVM/leanth/blob/23929f8c922cd4461ab22dbfaa6520f3ad23a3b2/Leanth/LeanVM/Protocol.lean#L9818).
