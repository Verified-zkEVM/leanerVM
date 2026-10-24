/-
  LeanVM.Guest.Count.VsWords

  `verify_sub`'s callees' words at the deployed frame sizes (`VsWords B2C.fs`), from the words
  certificates (`wSB`, `wSK`), B1-d's terminal words (`TermWordsFs`) and B1-c's
  `shared_selector_tables` bound (`ss_totalLeOn`).
-/

module

public import LeanVM.Guest.Count.Instances
public import LeanVM.Guest.B1.VerifySub.CompleteB
public import LeanVM.Guest.B1.Terminal.TermWordsFs
public import LeanVM.Guest.B1.Selectors.SharedTotal

namespace LeanVM.Guest.Count

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest

@[expose] public section

/-- **`open_stacked`'s named callees' words**: `wSB` on the names `osKindOf` knows, `0` on the
others (the queries' callees and the loops, which `osBk` bounds by `osSpB`). -/
noncomputable def osBnd (f : String) : ℕ := if (B1.osKindOf f).isSome then wSB f else 0

theorem osLeafBoundsB : B1.OsLeafBounds B2C.fs osBnd := fun f K hK => by
  have h := osLeafBounds f K hK
  simpa [osBnd, hK] using h

/-- `verify_tables`' callees but `__loop10` and `shared_selector_tables`, with their core
indices. -/
def vtPairs : List (String × ℕ) :=
  [("block_selector__L0", 150), ("block_selector__L1", 151),
    ("block_selector__L10", 160), ("block_selector__L11", 161), ("block_selector__L12", 162),
    ("block_selector__L13", 163), ("block_selector__L14", 164), ("block_selector__L15", 165),
    ("block_selector__L16", 166), ("block_selector__L17", 167), ("block_selector__L18", 168),
    ("block_selector__L19", 169), ("block_selector__L2", 152), ("block_selector__L20", 170),
    ("block_selector__L21", 171), ("block_selector__L22", 172), ("block_selector__L23", 173),
    ("block_selector__L24", 174), ("block_selector__L25", 175), ("block_selector__L26", 176),
    ("block_selector__L27", 177), ("block_selector__L28", 178), ("block_selector__L29", 179),
    ("block_selector__L3", 153), ("block_selector__L30", 180), ("block_selector__L31", 181),
    ("block_selector__L32", 182), ("block_selector__L33", 183), ("block_selector__L4", 154),
    ("block_selector__L5", 155), ("block_selector__L6", 156), ("block_selector__L7", 157),
    ("block_selector__L8", 158), ("block_selector__L9", 159), ("block_selector_tab__L0", 218),
    ("block_selector_tab__L1", 219), ("block_selector_tab__L10", 228),
    ("block_selector_tab__L11", 229), ("block_selector_tab__L12", 230),
    ("block_selector_tab__L13", 231), ("block_selector_tab__L14", 232),
    ("block_selector_tab__L15", 233), ("block_selector_tab__L16", 234),
    ("block_selector_tab__L17", 235), ("block_selector_tab__L18", 236),
    ("block_selector_tab__L19", 237), ("block_selector_tab__L2", 220),
    ("block_selector_tab__L20", 238), ("block_selector_tab__L21", 239),
    ("block_selector_tab__L22", 240), ("block_selector_tab__L23", 241),
    ("block_selector_tab__L24", 242), ("block_selector_tab__L25", 243),
    ("block_selector_tab__L26", 244), ("block_selector_tab__L27", 245),
    ("block_selector_tab__L28", 246), ("block_selector_tab__L29", 247),
    ("block_selector_tab__L3", 221), ("block_selector_tab__L30", 248),
    ("block_selector_tab__L31", 249), ("block_selector_tab__L32", 250),
    ("block_selector_tab__L33", 251), ("block_selector_tab__L4", 222),
    ("block_selector_tab__L5", 223), ("block_selector_tab__L6", 224),
    ("block_selector_tab__L7", 225), ("block_selector_tab__L8", 226),
    ("block_selector_tab__L9", 227), ("eq_prefix_chain", 4), ("eq_prefix_run__L0", 38),
    ("eq_prefix_run__L1", 39), ("eq_prefix_run__L10", 48), ("eq_prefix_run__L11", 49),
    ("eq_prefix_run__L12", 50), ("eq_prefix_run__L13", 51), ("eq_prefix_run__L14", 52),
    ("eq_prefix_run__L15", 53), ("eq_prefix_run__L16", 54), ("eq_prefix_run__L17", 55),
    ("eq_prefix_run__L18", 56), ("eq_prefix_run__L19", 57), ("eq_prefix_run__L2", 40),
    ("eq_prefix_run__L20", 58), ("eq_prefix_run__L21", 59), ("eq_prefix_run__L22", 60),
    ("eq_prefix_run__L23", 61), ("eq_prefix_run__L24", 62), ("eq_prefix_run__L25", 63),
    ("eq_prefix_run__L26", 64), ("eq_prefix_run__L27", 65), ("eq_prefix_run__L28", 66),
    ("eq_prefix_run__L29", 67), ("eq_prefix_run__L3", 41), ("eq_prefix_run__L30", 68),
    ("eq_prefix_run__L31", 69), ("eq_prefix_run__L32", 70), ("eq_prefix_run__L33", 71),
    ("eq_prefix_run__L34", 72), ("eq_prefix_run__L35", 73), ("eq_prefix_run__L36", 74),
    ("eq_prefix_run__L37", 75), ("eq_prefix_run__L38", 76), ("eq_prefix_run__L39", 77),
    ("eq_prefix_run__L4", 42), ("eq_prefix_run__L40", 78), ("eq_prefix_run__L5", 43),
    ("eq_prefix_run__L6", 44), ("eq_prefix_run__L7", 45), ("eq_prefix_run__L8", 46),
    ("eq_prefix_run__L9", 47), ("index_mle__L0", 184), ("index_mle__L1", 185),
    ("index_mle__L10", 194), ("index_mle__L11", 195), ("index_mle__L12", 196),
    ("index_mle__L13", 197), ("index_mle__L14", 198), ("index_mle__L15", 199),
    ("index_mle__L16", 200), ("index_mle__L17", 201), ("index_mle__L18", 202),
    ("index_mle__L19", 203), ("index_mle__L2", 186), ("index_mle__L20", 204),
    ("index_mle__L21", 205), ("index_mle__L22", 206), ("index_mle__L23", 207),
    ("index_mle__L24", 208), ("index_mle__L25", 209), ("index_mle__L26", 210),
    ("index_mle__L27", 211), ("index_mle__L28", 212), ("index_mle__L29", 213),
    ("index_mle__L3", 187), ("index_mle__L30", 214), ("index_mle__L31", 215),
    ("index_mle__L32", 216), ("index_mle__L33", 217), ("index_mle__L4", 188),
    ("index_mle__L5", 189), ("index_mle__L6", 190), ("index_mle__L7", 191), ("index_mle__L8", 192),
    ("index_mle__L9", 193), ("padding_weight__L0", 87), ("padding_weight__L1", 88),
    ("padding_weight__L10", 97), ("padding_weight__L11", 98), ("padding_weight__L12", 99),
    ("padding_weight__L13", 100), ("padding_weight__L14", 101), ("padding_weight__L15", 102),
    ("padding_weight__L16", 103), ("padding_weight__L17", 104), ("padding_weight__L18", 105),
    ("padding_weight__L19", 106), ("padding_weight__L2", 89), ("padding_weight__L20", 107),
    ("padding_weight__L21", 108), ("padding_weight__L22", 109), ("padding_weight__L23", 110),
    ("padding_weight__L24", 111), ("padding_weight__L25", 112), ("padding_weight__L26", 113),
    ("padding_weight__L27", 114), ("padding_weight__L28", 115), ("padding_weight__L3", 90),
    ("padding_weight__L4", 91), ("padding_weight__L5", 92), ("padding_weight__L6", 93),
    ("padding_weight__L7", 94), ("padding_weight__L8", 95), ("padding_weight__L9", 96),
    ("plus_one_run__L0", 116), ("plus_one_run__L1", 117), ("plus_one_run__L10", 126),
    ("plus_one_run__L11", 127), ("plus_one_run__L12", 128), ("plus_one_run__L13", 129),
    ("plus_one_run__L14", 130), ("plus_one_run__L15", 131), ("plus_one_run__L16", 132),
    ("plus_one_run__L17", 133), ("plus_one_run__L18", 134), ("plus_one_run__L19", 135),
    ("plus_one_run__L2", 118), ("plus_one_run__L20", 136), ("plus_one_run__L21", 137),
    ("plus_one_run__L22", 138), ("plus_one_run__L23", 139), ("plus_one_run__L24", 140),
    ("plus_one_run__L25", 141), ("plus_one_run__L26", 142), ("plus_one_run__L27", 143),
    ("plus_one_run__L28", 144), ("plus_one_run__L29", 145), ("plus_one_run__L3", 119),
    ("plus_one_run__L30", 146), ("plus_one_run__L31", 147), ("plus_one_run__L32", 148),
    ("plus_one_run__L33", 149), ("plus_one_run__L4", 120), ("plus_one_run__L5", 121),
    ("plus_one_run__L6", 122), ("plus_one_run__L7", 123), ("plus_one_run__L8", 124),
    ("plus_one_run__L9", 125), ("sel_partial_nibble__L0", 83), ("sel_partial_nibble__L1", 84),
    ("sel_partial_nibble__L2", 85), ("sel_partial_nibble__L3", 86), ("sumcheck_round4", 6)]

theorem vtPairs_ok : (vtPairs.all fun p => wOkB p.2 p.1) = true := by decide +kernel

theorem vtPairs_names : B1.Tables.vtKidS.filter (fun g => g != "__loop10" && g != "shared_selector_tables" && g != "__loop9") =
    vtPairs.map Prod.fst := by decide +kernel

theorem vt_kids_totalLe : ∀ g ∈ B1.Tables.vtKidS, g ≠ "__loop10" → g ≠ "__loop9" →
    g ≠ "shared_selector_tables" → TotalLe coreProgram B2C.fs g (fun _ => wSB g) := by
  intro g hg h1 h3 h2
  have hm : g ∈ vtPairs.map Prod.fst := by
    rw [← vtPairs_names, List.mem_filter]
    exact ⟨hg, by simp [h1, h2, h3]⟩
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
  exact wSB_totalLe (List.all_eq_true.mp vtPairs_ok p hp)

/-- The four partial nibble selectors' words, at most. -/
noncomputable def kSp : ℕ :=
  max (max (wSB "sel_partial_nibble__L0") (wSB "sel_partial_nibble__L1"))
    (max (wSB "sel_partial_nibble__L2") (wSB "sel_partial_nibble__L3"))

theorem totalLe_mono {f : String} {B B' : ℕ} (h : TotalLe coreProgram B2C.fs f fun _ => B)
    (hB : B ≤ B') : TotalLe coreProgram B2C.fs f fun _ => B' :=
  fun rd t args rets hn hv hb => (h rd t args rets hn hv hb).trans hB

theorem sp_totalLe : ∀ j < 4,
    TotalLe coreProgram B2C.fs (B1.Tables.lName "sel_partial_nibble" j) (fun _ => kSp) := by
  intro j hj
  interval_cases j
  · rw [show B1.Tables.lName "sel_partial_nibble" 0 = "sel_partial_nibble__L0" by decide]
    exact totalLe_mono (wSB_totalLe (j := 83) (by decide +kernel)) (by unfold kSp; omega)
  · rw [show B1.Tables.lName "sel_partial_nibble" 1 = "sel_partial_nibble__L1" by decide]
    exact totalLe_mono (wSB_totalLe (j := 84) (by decide +kernel)) (by unfold kSp; omega)
  · rw [show B1.Tables.lName "sel_partial_nibble" 2 = "sel_partial_nibble__L2" by decide]
    exact totalLe_mono (wSB_totalLe (j := 85) (by decide +kernel)) (by unfold kSp; omega)
  · rw [show B1.Tables.lName "sel_partial_nibble" 3 = "sel_partial_nibble__L3" by decide]
    exact totalLe_mono (wSB_totalLe (j := 86) (by decide +kernel)) (by unfold kSp; omega)

/-- **`verify_sub`'s callees' words at `B2C.fs`.** -/
noncomputable def vsWords : B1.VerifySub.VsWords B2C.fs where
  Bg := wSB "g_power_of_word"
  hg := wSB_totalLe (j := 3) (by decide +kernel)
  Ba := wSB "assert_canonical"
  ha := wSB_totalLe (j := 1) (by decide +kernel)
  K29 := wSK "__loop29"
  R := max (wSB "gkr_rounds__L1") (wSB "gkr_rounds__L2")
  K8 := wSK "__loop8"
  h29 := wSK_totalLeOn (j := 399) (by decide +kernel)
  hR1 := totalLe_mono (wSB_totalLe (j := 401) (by decide +kernel)) (le_max_left _ _)
  hR2 := totalLe_mono (wSB_totalLe (j := 400) (by decide +kernel)) (le_max_right _ _)
  h8 := wSK_totalLeOn (j := 81) (by decide +kernel)
  Kf := wSB
  Ksh := B2C.fs "shared_selector_tables" + (B2C.fs "__loop9" + 15 * wSK "__loop9") + kSp
  K10 := wSK "__loop10"
  hKf := vt_kids_totalLe
  hsh := B1.Tables.ss_totalLeOn (wSK "__loop9") kSp (wSK_totalLeOn (j := 82) (by decide +kernel))
    sp_totalLe
  h10 := wSK_totalLeOn (j := 252) (by decide +kernel)
  B14 := 10576
  hl14 := B1.VerifySub.l14_totalLeOn_fs
  Bnd := osBnd
  Kr := wSK
  hleaf := osLeafBoundsB
  hloop := fun μ r h1 h2 h3 h4 => osLoopBounds _ (by unfold B1.Whir.candidate; omega)
  Beqc := 184
  K15 := 38
  Bcs := 157
  Brs := 16433
  hEqc := B1.VerifySub.eqc_totalLe_fs
  hL15 := B1.VerifySub.l15_totalLeOn_fs
  hCs := B1.VerifySub.cs_totalLe_fs
  hCsF := B1.VerifySub.cs_fs_le
  hrs := B1.VerifySub.rs_totalLeOn_fs

end
end LeanVM.Guest.Count
