import Sphincs.H0PTab.NuTab
import Sphincs.H0PTab.G
import Sphincs.H0PTab.P2Tab

/-! **The rows `n < 107` of `P2tab`, checked by the kernel** (the rows cost about `n` each: the two
ranges `[0, 107)` and `[107, 151)` cost about the same; `H0PTab.lean` joins them). -/

namespace SphincsLayered.Security.H0

set_option maxRecDepth 1000000

theorem P2tab_rows_0 : (List.range' 0 107).map (P2QOf νTab gTab) = P2tab.take 107 := by decide +kernel

end SphincsLayered.Security.H0
