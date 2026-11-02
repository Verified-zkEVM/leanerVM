import Sphincs.H0PTab.H
import Sphincs.H0PTab.NuTab

/-! **The rows `107 ≤ i ≤ 150` of `νTab`, checked by the kernel** (`H0PTab/Nu0.lean`). -/

namespace SphincsLayered.Security.H0

set_option maxRecDepth 1000000

theorem νTab_rows_1 : (List.range' 107 44).map (νQOf hTab) = νTab.drop 107 := by decide +kernel

end SphincsLayered.Security.H0
