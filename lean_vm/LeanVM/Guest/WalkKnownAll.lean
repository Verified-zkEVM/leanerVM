/-
  LeanVM.Guest.WalkKnownAll

  The walks' obligations, proved: every function the certificates hand something on at its cuts,
  but `main` and `verify_sub`.
-/

module

public import LeanVM.Guest.WalkOq0
public import LeanVM.Guest.WalkOq1
public import LeanVM.Guest.WalkOq2
public import LeanVM.Guest.WalkOq3
public import LeanVM.Guest.WalkWp
public import LeanVM.Guest.WalkOs0
public import LeanVM.Guest.WalkOs1
public import LeanVM.Guest.WalkOs2
public import LeanVM.Guest.WalkOs3
public import LeanVM.Guest.WalkGkr

/-!
# `WalkKnown`, proved

`walkKnown_proved : WalkKnown`: the cut obligations (`CutsKnown`) of every function of
`Checked.oblFns` but `main` (`1`) and `verify_sub` (`19`): `opening_queries`' specializations and
loops (`WalkOq0.lean` to `WalkOq3.lean`, whir's `QueriesWalk` through b2's `WalkKnown.lean`),
`open_stacked`'s candidates (`WalkOs0.lean` to `WalkOs3.lean`, from the decodes before each level's
call, `WalkOsPre.lean`), `walk_path`'s specializations (`WalkWp.lean`, from their windows' tag),
and `verify_bus_gkr` (`10`) and its layer loop `__loop6` (`90`), whose
obligations (the layers' parities, `GkrPar`) the gkr track proves (`WalkGkr.lean`;
`walkKnown_of_gkr`).
-/

namespace LeanVM.Guest.End

@[expose] public section

set_option maxRecDepth 4000 in
/-- **The walks' obligations**, given `verify_bus_gkr`'s and its layer loop's. -/
theorem walkKnown_of_gkr (h10 : CutsKnown 10) (h91 : CutsKnown 90) : WalkKnown := by
  intro j hj h1 h19
  simp only [Checked.oblFns, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [absurd rfl h1, h10, absurd rfl h19, h91, walk_303, walk_304, walk_305, walk_306, walk_307,
    walk_308, walk_309, walk_310, walk_311, walk_312, walk_313, walk_314, walk_315, walk_316,
    walk_317, walk_318, walk_319, walk_320, walk_321, walk_322, walk_323, walk_324, walk_325,
    walk_326, walk_327, walk_328, walk_329, walk_330, walk_435, walk_440, walk_444, walk_447,
    walk_455, walk_458, walk_461, walk_471, walk_474, walk_477, walk_490, walk_493, walk_496,
    walk_509, walk_511, walk_513, walk_523, walk_525, walk_527, walk_537, walk_539, walk_541,
    walk_546, walk_555, walk_564, walk_573, walk_578, walk_585, walk_590, walk_597, walk_608,
    walk_613, walk_620, walk_622, walk_624, walk_627, walk_636, walk_645, walk_654, walk_665,
    walk_676, walk_687, walk_698, walk_700, walk_702, walk_705, walk_714, walk_723, walk_732,
    walk_743, walk_754, walk_765, walk_767, walk_777, walk_779, walk_783, walk_847, walk_849,
    walk_851, walk_853, walk_855, walk_857, walk_859, walk_861, walk_863, walk_865, walk_867,
    walk_869, walk_871, walk_873, walk_875, walk_877, walk_879, walk_880, walk_882, walk_884,
    walk_886, walk_887, walk_889, walk_891, walk_893, walk_895, walk_897, walk_899, walk_901,
    walk_903, walk_905, walk_907, walk_909, walk_911, walk_913, walk_915, walk_917, walk_919,
    walk_920, walk_921, walk_922, walk_923, walk_924, walk_925, walk_926, walk_927, walk_928,
    walk_929, walk_930, walk_931, walk_933, walk_934, walk_936, walk_938, walk_940, walk_941,
    walk_942, walk_943, walk_944, walk_945, walk_947, walk_949, walk_951, walk_953, walk_955,
    walk_956, walk_957, walk_958, walk_959, walk_960, walk_961, walk_962, walk_963, walk_964,
    walk_965, walk_966, walk_967, walk_968, walk_969, walk_970, walk_971, walk_972, walk_973,
    walk_974, walk_975, walk_976, walk_977, walk_978, walk_979, walk_980, walk_981, walk_982,
    walk_983, walk_984, walk_985, walk_986, walk_987, walk_988, walk_989, walk_990, walk_991]

/-- **The walks' obligations, proved.** -/
theorem walkKnown_proved : WalkKnown := walkKnown_of_gkr gkrBus_cutsKnown gkrLoop_cutsKnown

end
end LeanVM.Guest.End
