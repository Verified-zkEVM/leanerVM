/-
  LeanVM.Guest.B1.Tables.Vt.CountTotal

  `verify_tables`' count side total: the padding sum over its blocks, the selector sum and the GKR
  count value.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.PullTotal

/-!
# The count side's total (G:2344-2376)

The count side has no framework blocks and its blocks' padding coefficient is `1`.
`vt_count_total`: `bus_table_total[COUNT]`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- The count side's blocks: block, table, copy value, no padding terms. -/
def vtCountPadData : List (ℕ × ℕ × ℕ × List (ℕ × ℕ)) :=
  [(108, 0, 2061, []), (109, 0, 2066, []), (110, 0, 2071, []), (111, 0, 2076, []),
    (112, 1, 2085, []), (113, 1, 2094, []), (114, 1, 2103, []), (115, 1, 2112, []),
    (116, 2, 2121, []), (117, 2, 2130, []), (118, 3, 2139, []), (119, 3, 2148, []),
    (120, 3, 2157, []), (121, 3, 2166, []), (122, 4, 2175, []), (123, 4, 2184, []),
    (124, 4, 2193, []), (125, 4, 2202, []), (126, 5, 2211, []), (127, 5, 2220, []),
    (128, 5, 2229, []), (129, 5, 2238, []), (130, 5, 2247, []), (131, 5, 2256, []),
    (132, 5, 2265, []), (133, 5, 2274, []), (134, 5, 2283, []), (135, 5, 2292, []),
    (136, 5, 2301, []), (137, 5, 2310, []), (138, 5, 2319, []), (139, 5, 2328, []),
    (140, 5, 2337, []), (141, 5, 2346, []), (142, 5, 2355, []), (143, 5, 2364, []),
    (144, 5, 2373, []), (145, 5, 2382, []), (146, 5, 2391, []), (147, 5, 2400, []),
    (148, 5, 2409, []), (149, 5, 2418, []), (150, 5, 2427, []), (151, 5, 2436, []),
    (152, 5, 2445, [])]

set_option maxRecDepth 100000 in
/-- **The count side's total.** -/
theorem vt_count_total {rd : Reader} {σ : Val} (h : VtH rd σ) (W : ℕ → E) :
    σ (.n 2499) = vtPadSum (fun c ↦ σ (.n c)) (fun t ↦ σ (.n (vtPadV t))) W 1 vtCountPadData +
      (1 + σ (.n 2444)) + σ (.n 27) := by
  have a5098 := h.atomAt 2517 (.add (.n 2446) (.n 2061) (.n 2066)) (by decide +kernel)
  have a5099 := h.atomAt 2518 (.add (.n 2447) (.n 2446) (.n 2071)) (by decide +kernel)
  have a5100 := h.atomAt 2519 (.add (.n 2448) (.n 2447) (.n 2076)) (by decide +kernel)
  have a5101 := h.atomAt 2520 (.mul (.n 2449) (.n 587) (.n 2448)) (by decide +kernel)
  have a5102 := h.atomAt 2521 (.add (.n 2450) (.n 2085) (.n 2094)) (by decide +kernel)
  have a5103 := h.atomAt 2522 (.add (.n 2451) (.n 2450) (.n 2103)) (by decide +kernel)
  have a5104 := h.atomAt 2523 (.add (.n 2452) (.n 2451) (.n 2112)) (by decide +kernel)
  have a5105 := h.atomAt 2524 (.mul (.n 2453) (.n 600) (.n 2452)) (by decide +kernel)
  have a5106 := h.atomAt 2525 (.add (.n 2454) (.n 2449) (.n 2453)) (by decide +kernel)
  have a5107 := h.atomAt 2526 (.add (.n 2455) (.n 2121) (.n 2130)) (by decide +kernel)
  have a5108 := h.atomAt 2527 (.mul (.n 2456) (.n 613) (.n 2455)) (by decide +kernel)
  have a5109 := h.atomAt 2528 (.add (.n 2457) (.n 2454) (.n 2456)) (by decide +kernel)
  have a5110 := h.atomAt 2529 (.add (.n 2458) (.n 2139) (.n 2148)) (by decide +kernel)
  have a5111 := h.atomAt 2530 (.add (.n 2459) (.n 2458) (.n 2157)) (by decide +kernel)
  have a5112 := h.atomAt 2531 (.add (.n 2460) (.n 2459) (.n 2166)) (by decide +kernel)
  have a5113 := h.atomAt 2532 (.mul (.n 2461) (.n 626) (.n 2460)) (by decide +kernel)
  have a5114 := h.atomAt 2533 (.add (.n 2462) (.n 2457) (.n 2461)) (by decide +kernel)
  have a5115 := h.atomAt 2534 (.add (.n 2463) (.n 2175) (.n 2184)) (by decide +kernel)
  have a5116 := h.atomAt 2535 (.add (.n 2464) (.n 2463) (.n 2193)) (by decide +kernel)
  have a5117 := h.atomAt 2536 (.add (.n 2465) (.n 2464) (.n 2202)) (by decide +kernel)
  have a5118 := h.atomAt 2537 (.mul (.n 2466) (.n 639) (.n 2465)) (by decide +kernel)
  have a5119 := h.atomAt 2538 (.add (.n 2467) (.n 2462) (.n 2466)) (by decide +kernel)
  have a5120 := h.atomAt 2539 (.add (.n 2468) (.n 2211) (.n 2220)) (by decide +kernel)
  have a5121 := h.atomAt 2540 (.add (.n 2469) (.n 2468) (.n 2229)) (by decide +kernel)
  have a5122 := h.atomAt 2541 (.add (.n 2470) (.n 2469) (.n 2238)) (by decide +kernel)
  have a5123 := h.atomAt 2542 (.add (.n 2471) (.n 2470) (.n 2247)) (by decide +kernel)
  have a5124 := h.atomAt 2543 (.add (.n 2472) (.n 2471) (.n 2256)) (by decide +kernel)
  have a5125 := h.atomAt 2544 (.add (.n 2473) (.n 2472) (.n 2265)) (by decide +kernel)
  have a5126 := h.atomAt 2545 (.add (.n 2474) (.n 2473) (.n 2274)) (by decide +kernel)
  have a5127 := h.atomAt 2546 (.add (.n 2475) (.n 2474) (.n 2283)) (by decide +kernel)
  have a5128 := h.atomAt 2547 (.add (.n 2476) (.n 2475) (.n 2292)) (by decide +kernel)
  have a5129 := h.atomAt 2548 (.add (.n 2477) (.n 2476) (.n 2301)) (by decide +kernel)
  have a5130 := h.atomAt 2549 (.add (.n 2478) (.n 2477) (.n 2310)) (by decide +kernel)
  have a5131 := h.atomAt 2550 (.add (.n 2479) (.n 2478) (.n 2319)) (by decide +kernel)
  have a5132 := h.atomAt 2551 (.add (.n 2480) (.n 2479) (.n 2328)) (by decide +kernel)
  have a5133 := h.atomAt 2552 (.add (.n 2481) (.n 2480) (.n 2337)) (by decide +kernel)
  have a5134 := h.atomAt 2553 (.add (.n 2482) (.n 2481) (.n 2346)) (by decide +kernel)
  have a5135 := h.atomAt 2554 (.add (.n 2483) (.n 2482) (.n 2355)) (by decide +kernel)
  have a5136 := h.atomAt 2555 (.add (.n 2484) (.n 2483) (.n 2364)) (by decide +kernel)
  have a5137 := h.atomAt 2556 (.add (.n 2485) (.n 2484) (.n 2373)) (by decide +kernel)
  have a5138 := h.atomAt 2557 (.add (.n 2486) (.n 2485) (.n 2382)) (by decide +kernel)
  have a5139 := h.atomAt 2558 (.add (.n 2487) (.n 2486) (.n 2391)) (by decide +kernel)
  have a5140 := h.atomAt 2559 (.add (.n 2488) (.n 2487) (.n 2400)) (by decide +kernel)
  have a5141 := h.atomAt 2560 (.add (.n 2489) (.n 2488) (.n 2409)) (by decide +kernel)
  have a5142 := h.atomAt 2561 (.add (.n 2490) (.n 2489) (.n 2418)) (by decide +kernel)
  have a5143 := h.atomAt 2562 (.add (.n 2491) (.n 2490) (.n 2427)) (by decide +kernel)
  have a5144 := h.atomAt 2563 (.add (.n 2492) (.n 2491) (.n 2436)) (by decide +kernel)
  have a5145 := h.atomAt 2564 (.add (.n 2493) (.n 2492) (.n 2445)) (by decide +kernel)
  have a5146 := h.atomAt 2565 (.mul (.n 2494) (.n 652) (.n 2493)) (by decide +kernel)
  have a5147 := h.atomAt 2566 (.add (.n 2495) (.n 2467) (.n 2494)) (by decide +kernel)
  have a5148 := h.atomAt 2567 (.const (.n 2496) (word 1 0 0)) (by decide +kernel)
  have a5149 := h.atomAt 2568 (.add (.n 2497) (.n 2496) (.n 2444)) (by decide +kernel)
  have a5150 := h.atomAt 2569 (.add (.n 2498) (.n 2495) (.n 2497)) (by decide +kernel)
  have a5151 := h.atomAt 2570 (.add (.n 2499) (.n 2498) (.n 27)) (by decide +kernel)
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
