import Sphincs.H0PTab.H
import Sphincs.H0PTab.NuTab

/-! **The rows `i < 107` of `νTab`, checked by the kernel** (the rows cost about `i` each: the two
ranges `[0, 107)` and `[107, 151)` cost about the same; `H0PTab.lean` joins them). -/

namespace SphincsLayered.Security.H0

set_option maxRecDepth 1000000

theorem νTab_rows_0 : (List.range' 0 107).map (νQOf hTab) = νTab.take 107 := by decide +kernel

end SphincsLayered.Security.H0
