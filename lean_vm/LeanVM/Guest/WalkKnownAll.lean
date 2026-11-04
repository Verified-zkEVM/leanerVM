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
    rfl | rfl
  exacts [absurd rfl h1, h10, absurd rfl h19, walk_91, walk_304, walk_305, walk_306, walk_307,
    walk_308, walk_309, walk_310, walk_311, walk_312, walk_313, walk_314, walk_315, walk_316,
    walk_317, walk_318, walk_319, walk_320, walk_321, walk_322, walk_323, walk_324, walk_325,
    walk_326, walk_327, walk_328, walk_329, walk_330, walk_331, walk_436, walk_441, walk_445,
    walk_448, walk_456, walk_459, walk_462, walk_472, walk_475, walk_478, walk_491, walk_494,
    walk_497, walk_510, walk_512, walk_514, walk_524, walk_526, walk_528, walk_538, walk_540,
    walk_542, walk_547, walk_556, walk_565, walk_574, walk_579, walk_586, walk_591, walk_598,
    walk_609, walk_614, walk_621, walk_623, walk_625, walk_628, walk_637, walk_646, walk_655,
    walk_666, walk_677, walk_688, walk_699, walk_701, walk_703, walk_706, walk_715, walk_724,
    walk_733, walk_744, walk_755, walk_766, walk_768, walk_778, walk_780, walk_784, walk_848,
    walk_850, walk_852, walk_854, walk_856, walk_858, walk_860, walk_862, walk_864, walk_866,
    walk_868, walk_870, walk_872, walk_874, walk_876, walk_878, walk_880, walk_882, walk_884,
    walk_886, walk_888, walk_890, walk_892, walk_894, walk_896, walk_898, walk_900, walk_902,
    walk_904, walk_906, walk_908, walk_910, walk_912, walk_914, walk_916, walk_918, walk_919,
    walk_920, walk_921, walk_922, walk_923, walk_924, walk_926, walk_928, walk_930, walk_932,
    walk_933, walk_934, walk_935, walk_936, walk_937, walk_939, walk_941, walk_943, walk_945,
    walk_947]

/-- **The walks' obligations, proved.** -/
theorem walkKnown_proved : WalkKnown := walkKnown_of_gkr gkrBus_cutsKnown gkrLoop_cutsKnown

end
end LeanVM.Guest.End
