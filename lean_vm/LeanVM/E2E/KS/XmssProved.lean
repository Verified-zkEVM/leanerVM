import LeanVM.E2E.KS.Xmss
import XmssSecurity

/-!
# A known leanXMSS forgery, at leanXMSS's proved security

`prEvent_knownForgedX_le` at leanXMSS's proved multi-user security
(`XmssSecurity.leanXmss_has_multi_user_security`): in the deployed game before verification, a
known leanXMSS forgery has probability at most `xmssMultiError n_x (preQueries + 384)`, whenever
`preQueries + 384 < 2^126`. The lean_xmss endpoint lives in a non-module file, so this file is not
a module.
-/

namespace LeanVM.E2E.KS

open LeanVM.E2E
open scoped ENNReal

/-- **A known leanXMSS forgery is at most leanXMSS's proved multi-user bound.** In the deployed
game before verification, against an adversary making at most `qH` hash queries, `sX` leanXMSS
and `sS` leanSPHINCS signing requests, with `preQueries + 384 < 2^126`, a known leanXMSS forgery
has probability at most `xmssMultiError n_x (preQueries + 384)`. -/
theorem prEvent_knownForgedX_le_proved [Sphincs.Params] {nx ns : ℕ} (A : DAdversary nx ns)
    {qH sX sS : ℕ} (hA : DAdvBounds A qH sX sS)
    (hq : preQueries nx ns qH sX sS + 384 < 2 ^ 126) :
    Pr{let z ← pGame A}[KnownForgedX z.1] ≤
      xmssMultiError nx (preQueries nx ns qH sX sS + 384) :=
  prEvent_knownForgedX_le XmssSecurity.leanXmss_has_multi_user_security A hA hq

end LeanVM.E2E.KS
