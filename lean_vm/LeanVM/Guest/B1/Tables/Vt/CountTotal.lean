/-
  LeanVM.Guest.B1.Tables.Vt.CountTotal

  `verify_tables`' count side total: the padding sum over its blocks, the selector sum and the GKR
  count value.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.PullTotal

/-!
# The count side's total (G:2131-2163)

The count side has no framework blocks and its blocks' padding coefficient is `1`.
`vt_count_total`: `bus_table_total[COUNT]`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- The count side's blocks: block, table, copy value, no padding terms. -/
def vtCountPadData : List (ℕ × ℕ × ℕ × List (ℕ × ℕ)) :=
  [(108, 0, 4938, []), (109, 0, 4953, []), (110, 0, 4968, []), (111, 0, 4983, []),
    (112, 1, 5002, []), (113, 1, 5021, []), (114, 1, 5040, []), (115, 1, 5059, []),
    (116, 2, 5078, []), (117, 2, 5097, []), (118, 3, 5116, []), (119, 3, 5135, []),
    (120, 3, 5154, []), (121, 3, 5173, []), (122, 4, 5192, []), (123, 4, 5211, []),
    (124, 4, 5230, []), (125, 4, 5249, []), (126, 5, 5268, []), (127, 5, 5287, []),
    (128, 5, 5306, []), (129, 5, 5325, []), (130, 5, 5344, []), (131, 5, 5363, []),
    (132, 5, 5382, []), (133, 5, 5401, []), (134, 5, 5420, []), (135, 5, 5439, []),
    (136, 5, 5458, []), (137, 5, 5477, []), (138, 5, 5496, []), (139, 5, 5515, []),
    (140, 5, 5534, []), (141, 5, 5553, []), (142, 5, 5572, []), (143, 5, 5591, []),
    (144, 5, 5610, []), (145, 5, 5629, []), (146, 5, 5648, []), (147, 5, 5667, []),
    (148, 5, 5686, []), (149, 5, 5705, []), (150, 5, 5724, []), (151, 5, 5743, []),
    (152, 5, 5762, [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The count side's total.** -/
theorem vt_count_total {rd : Reader} {σ : Val} (h : VtH rd σ) (W : ℕ → E) :
    σ (.n 5816) = vtPadSum (fun c ↦ σ (.n c)) (fun t ↦ σ (.n (vtPadV t))) W 1 vtCountPadData +
      (1 + σ (.n 5761)) + σ (.n 29) := by
  have a5098 := h.atom 5098 (.add (.n 5763) (.n 4938) (.n 4953)) (by decide +kernel)
  have a5099 := h.atom 5099 (.add (.n 5764) (.n 5763) (.n 4968)) (by decide +kernel)
  have a5100 := h.atom 5100 (.add (.n 5765) (.n 5764) (.n 4983)) (by decide +kernel)
  have a5101 := h.atom 5101 (.mul (.n 5766) (.n 2646) (.n 5765)) (by decide +kernel)
  have a5102 := h.atom 5102 (.add (.n 5767) (.n 5002) (.n 5021)) (by decide +kernel)
  have a5103 := h.atom 5103 (.add (.n 5768) (.n 5767) (.n 5040)) (by decide +kernel)
  have a5104 := h.atom 5104 (.add (.n 5769) (.n 5768) (.n 5059)) (by decide +kernel)
  have a5105 := h.atom 5105 (.mul (.n 5770) (.n 2660) (.n 5769)) (by decide +kernel)
  have a5106 := h.atom 5106 (.add (.n 5771) (.n 5766) (.n 5770)) (by decide +kernel)
  have a5107 := h.atom 5107 (.add (.n 5772) (.n 5078) (.n 5097)) (by decide +kernel)
  have a5108 := h.atom 5108 (.mul (.n 5773) (.n 2674) (.n 5772)) (by decide +kernel)
  have a5109 := h.atom 5109 (.add (.n 5774) (.n 5771) (.n 5773)) (by decide +kernel)
  have a5110 := h.atom 5110 (.add (.n 5775) (.n 5116) (.n 5135)) (by decide +kernel)
  have a5111 := h.atom 5111 (.add (.n 5776) (.n 5775) (.n 5154)) (by decide +kernel)
  have a5112 := h.atom 5112 (.add (.n 5777) (.n 5776) (.n 5173)) (by decide +kernel)
  have a5113 := h.atom 5113 (.mul (.n 5778) (.n 2688) (.n 5777)) (by decide +kernel)
  have a5114 := h.atom 5114 (.add (.n 5779) (.n 5774) (.n 5778)) (by decide +kernel)
  have a5115 := h.atom 5115 (.add (.n 5780) (.n 5192) (.n 5211)) (by decide +kernel)
  have a5116 := h.atom 5116 (.add (.n 5781) (.n 5780) (.n 5230)) (by decide +kernel)
  have a5117 := h.atom 5117 (.add (.n 5782) (.n 5781) (.n 5249)) (by decide +kernel)
  have a5118 := h.atom 5118 (.mul (.n 5783) (.n 2702) (.n 5782)) (by decide +kernel)
  have a5119 := h.atom 5119 (.add (.n 5784) (.n 5779) (.n 5783)) (by decide +kernel)
  have a5120 := h.atom 5120 (.add (.n 5785) (.n 5268) (.n 5287)) (by decide +kernel)
  have a5121 := h.atom 5121 (.add (.n 5786) (.n 5785) (.n 5306)) (by decide +kernel)
  have a5122 := h.atom 5122 (.add (.n 5787) (.n 5786) (.n 5325)) (by decide +kernel)
  have a5123 := h.atom 5123 (.add (.n 5788) (.n 5787) (.n 5344)) (by decide +kernel)
  have a5124 := h.atom 5124 (.add (.n 5789) (.n 5788) (.n 5363)) (by decide +kernel)
  have a5125 := h.atom 5125 (.add (.n 5790) (.n 5789) (.n 5382)) (by decide +kernel)
  have a5126 := h.atom 5126 (.add (.n 5791) (.n 5790) (.n 5401)) (by decide +kernel)
  have a5127 := h.atom 5127 (.add (.n 5792) (.n 5791) (.n 5420)) (by decide +kernel)
  have a5128 := h.atom 5128 (.add (.n 5793) (.n 5792) (.n 5439)) (by decide +kernel)
  have a5129 := h.atom 5129 (.add (.n 5794) (.n 5793) (.n 5458)) (by decide +kernel)
  have a5130 := h.atom 5130 (.add (.n 5795) (.n 5794) (.n 5477)) (by decide +kernel)
  have a5131 := h.atom 5131 (.add (.n 5796) (.n 5795) (.n 5496)) (by decide +kernel)
  have a5132 := h.atom 5132 (.add (.n 5797) (.n 5796) (.n 5515)) (by decide +kernel)
  have a5133 := h.atom 5133 (.add (.n 5798) (.n 5797) (.n 5534)) (by decide +kernel)
  have a5134 := h.atom 5134 (.add (.n 5799) (.n 5798) (.n 5553)) (by decide +kernel)
  have a5135 := h.atom 5135 (.add (.n 5800) (.n 5799) (.n 5572)) (by decide +kernel)
  have a5136 := h.atom 5136 (.add (.n 5801) (.n 5800) (.n 5591)) (by decide +kernel)
  have a5137 := h.atom 5137 (.add (.n 5802) (.n 5801) (.n 5610)) (by decide +kernel)
  have a5138 := h.atom 5138 (.add (.n 5803) (.n 5802) (.n 5629)) (by decide +kernel)
  have a5139 := h.atom 5139 (.add (.n 5804) (.n 5803) (.n 5648)) (by decide +kernel)
  have a5140 := h.atom 5140 (.add (.n 5805) (.n 5804) (.n 5667)) (by decide +kernel)
  have a5141 := h.atom 5141 (.add (.n 5806) (.n 5805) (.n 5686)) (by decide +kernel)
  have a5142 := h.atom 5142 (.add (.n 5807) (.n 5806) (.n 5705)) (by decide +kernel)
  have a5143 := h.atom 5143 (.add (.n 5808) (.n 5807) (.n 5724)) (by decide +kernel)
  have a5144 := h.atom 5144 (.add (.n 5809) (.n 5808) (.n 5743)) (by decide +kernel)
  have a5145 := h.atom 5145 (.add (.n 5810) (.n 5809) (.n 5762)) (by decide +kernel)
  have a5146 := h.atom 5146 (.mul (.n 5811) (.n 2716) (.n 5810)) (by decide +kernel)
  have a5147 := h.atom 5147 (.add (.n 5812) (.n 5784) (.n 5811)) (by decide +kernel)
  have a5148 := h.atom 5148 (.const (.n 5813) (word 1 0 0)) (by decide +kernel)
  have a5149 := h.atom 5149 (.add (.n 5814) (.n 5813) (.n 5761)) (by decide +kernel)
  have a5150 := h.atom 5150 (.add (.n 5815) (.n 5812) (.n 5814)) (by decide +kernel)
  have a5151 := h.atom 5151 (.add (.n 5816) (.n 5815) (.n 29)) (by decide +kernel)
  simp only [Atom.Holds] at a5098 a5099 a5100 a5101 a5102 a5103 a5104 a5105 a5106 a5107
  simp only [Atom.Holds] at a5108 a5109 a5110 a5111 a5112 a5113 a5114 a5115 a5116 a5117
  simp only [Atom.Holds] at a5118 a5119 a5120 a5121 a5122 a5123 a5124 a5125 a5126 a5127
  simp only [Atom.Holds] at a5128 a5129 a5130 a5131 a5132 a5133 a5134 a5135 a5136 a5137
  simp only [Atom.Holds] at a5138 a5139 a5140 a5141 a5142 a5143 a5144 a5145 a5146 a5147
  simp only [Atom.Holds] at a5148 a5149 a5150 a5151
  simp only [a5098, a5099, a5100, a5101, a5102, a5103, a5104, a5105, a5106, a5107, a5108, a5109, a5110,
    a5111, a5112, a5113, a5114, a5115, a5116, a5117, a5118, a5119, a5120, a5121, a5122, a5123,
    a5124, a5125, a5126, a5127, a5128, a5129, a5130, a5131, a5132, a5133, a5134, a5135, a5136,
    a5137, a5138, a5139, a5140, a5141, a5142, a5143, a5144, a5145, a5146, a5147, a5148, a5149,
    a5150, a5151]
  simp (config := { decide := true }) only [vtPadSum, vtPadTable, vtCountPadData, vtPadV,
    List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    ↓reduceIte, add_zero, mul_one]
  rw [tb_word_one]
  ring

end
end LeanVM.Guest.B1.Tables
