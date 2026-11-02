import Sphincs.H0PTab.NuTab
import Sphincs.H0PTab.G
import Sphincs.H0PTab.P2Tab

/-! **The rows `107 ≤ n ≤ 150` of `P2tab`, checked by the kernel** (`H0PTab/P2_0.lean`). -/

namespace SphincsLayered.Security.H0

set_option maxRecDepth 1000000

theorem P2tab_rows_1 : (List.range' 107 44).map (P2QOf νTab gTab) = P2tab.drop 107 := by decide +kernel

end SphincsLayered.Security.H0
