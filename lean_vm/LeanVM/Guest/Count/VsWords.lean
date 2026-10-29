/-
  LeanVM.Guest.Count.VsWords

  `verify_sub`'s callees' words at the deployed frame sizes (`VsWords B2C.fs`), from the words
  certificates (`wSB`, `wSK`), B1-d's terminal words (`TermWordsFs`) and B1-c's
  `shared_selector_tables` bound (`ss_totalLeOn`); `verify_tables`' and the terminal's callees'
  weights from the `W` count certificates (`kuSB`, `kuSK`), `ss_weightLeOn` and the ratios of
  `__loop14` and `ring_switch_weight` (`Count/RatioV`).
-/

module

public import LeanVM.Guest.Count.Instances
public import LeanVM.Guest.B1.VerifySub.CompleteB
public import LeanVM.Guest.B1.Terminal.TermWordsFs
public import LeanVM.Guest.B1.Selectors.SharedTotal
public import LeanVM.Guest.Count.StaticW
public import LeanVM.Guest.Count.RatioV

namespace LeanVM.Guest.Count

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest

@[expose] public section

/-- **`open_stacked`'s named callees' words**: `wSB` on the names `osKindOf` knows, `0` on the
others (the queries' callees and the loops, which `osBk` bounds by `osSpB`). -/
noncomputable def osBnd (f : String) : ℕ := if (B1.osKindOf f).isSome then wSB f else 0

theorem osLeafBoundsB : B1.OsLeafBounds B2C.fs osBnd := fun f K hK => by
  have h := osLeafBounds f K hK
  simpa [osBnd, hK] using h

/-- `verify_tables`' callees but `__loop9` and `shared_selector_tables`, with their core
indices. -/
def vtPairs : List (String × ℕ) :=
  [("block_selector__L0", 147), ("block_selector__L1", 148),
    ("block_selector__L10", 157), ("block_selector__L11", 158), ("block_selector__L12", 159),
    ("block_selector__L13", 160), ("block_selector__L14", 161), ("block_selector__L15", 162),
    ("block_selector__L16", 163), ("block_selector__L17", 164), ("block_selector__L18", 165),
    ("block_selector__L19", 166), ("block_selector__L2", 149), ("block_selector__L20", 167),
    ("block_selector__L21", 168), ("block_selector__L22", 169), ("block_selector__L23", 170),
    ("block_selector__L24", 171), ("block_selector__L25", 172), ("block_selector__L26", 173),
    ("block_selector__L27", 174), ("block_selector__L28", 175), ("block_selector__L29", 176),
    ("block_selector__L3", 150), ("block_selector__L30", 177), ("block_selector__L31", 178),
    ("block_selector__L32", 179), ("block_selector__L33", 180), ("block_selector__L4", 151),
    ("block_selector__L5", 152), ("block_selector__L6", 153), ("block_selector__L7", 154),
    ("block_selector__L8", 155), ("block_selector__L9", 156), ("block_selector_tab__L0", 215),
    ("block_selector_tab__L1", 216), ("block_selector_tab__L10", 225),
    ("block_selector_tab__L11", 226), ("block_selector_tab__L12", 227),
    ("block_selector_tab__L13", 228), ("block_selector_tab__L14", 229),
    ("block_selector_tab__L15", 230), ("block_selector_tab__L16", 231),
    ("block_selector_tab__L17", 232), ("block_selector_tab__L18", 233),
    ("block_selector_tab__L19", 234), ("block_selector_tab__L2", 217),
    ("block_selector_tab__L20", 235), ("block_selector_tab__L21", 236),
    ("block_selector_tab__L22", 237), ("block_selector_tab__L23", 238),
    ("block_selector_tab__L24", 239), ("block_selector_tab__L25", 240),
    ("block_selector_tab__L26", 241), ("block_selector_tab__L27", 242),
    ("block_selector_tab__L28", 243), ("block_selector_tab__L29", 244),
    ("block_selector_tab__L3", 218), ("block_selector_tab__L30", 245),
    ("block_selector_tab__L31", 246), ("block_selector_tab__L32", 247),
    ("block_selector_tab__L33", 248), ("block_selector_tab__L4", 219),
    ("block_selector_tab__L5", 220), ("block_selector_tab__L6", 221),
    ("block_selector_tab__L7", 222), ("block_selector_tab__L8", 223),
    ("block_selector_tab__L9", 224), ("eq_prefix_chain", 4), ("eq_prefix_run__L0", 35),
    ("eq_prefix_run__L1", 36), ("eq_prefix_run__L10", 45), ("eq_prefix_run__L11", 46),
    ("eq_prefix_run__L12", 47), ("eq_prefix_run__L13", 48), ("eq_prefix_run__L14", 49),
    ("eq_prefix_run__L15", 50), ("eq_prefix_run__L16", 51), ("eq_prefix_run__L17", 52),
    ("eq_prefix_run__L18", 53), ("eq_prefix_run__L19", 54), ("eq_prefix_run__L2", 37),
    ("eq_prefix_run__L20", 55), ("eq_prefix_run__L21", 56), ("eq_prefix_run__L22", 57),
    ("eq_prefix_run__L23", 58), ("eq_prefix_run__L24", 59), ("eq_prefix_run__L25", 60),
    ("eq_prefix_run__L26", 61), ("eq_prefix_run__L27", 62), ("eq_prefix_run__L28", 63),
    ("eq_prefix_run__L29", 64), ("eq_prefix_run__L3", 38), ("eq_prefix_run__L30", 65),
    ("eq_prefix_run__L31", 66), ("eq_prefix_run__L32", 67), ("eq_prefix_run__L33", 68),
    ("eq_prefix_run__L34", 69), ("eq_prefix_run__L35", 70), ("eq_prefix_run__L36", 71),
    ("eq_prefix_run__L37", 72), ("eq_prefix_run__L38", 73), ("eq_prefix_run__L39", 74),
    ("eq_prefix_run__L4", 39), ("eq_prefix_run__L40", 75), ("eq_prefix_run__L5", 40),
    ("eq_prefix_run__L6", 41), ("eq_prefix_run__L7", 42), ("eq_prefix_run__L8", 43),
    ("eq_prefix_run__L9", 44), ("index_mle__L0", 181), ("index_mle__L1", 182),
    ("index_mle__L10", 191), ("index_mle__L11", 192), ("index_mle__L12", 193),
    ("index_mle__L13", 194), ("index_mle__L14", 195), ("index_mle__L15", 196),
    ("index_mle__L16", 197), ("index_mle__L17", 198), ("index_mle__L18", 199),
    ("index_mle__L19", 200), ("index_mle__L2", 183), ("index_mle__L20", 201),
    ("index_mle__L21", 202), ("index_mle__L22", 203), ("index_mle__L23", 204),
    ("index_mle__L24", 205), ("index_mle__L25", 206), ("index_mle__L26", 207),
    ("index_mle__L27", 208), ("index_mle__L28", 209), ("index_mle__L29", 210),
    ("index_mle__L3", 184), ("index_mle__L30", 211), ("index_mle__L31", 212),
    ("index_mle__L32", 213), ("index_mle__L33", 214), ("index_mle__L4", 185),
    ("index_mle__L5", 186), ("index_mle__L6", 187), ("index_mle__L7", 188), ("index_mle__L8", 189),
    ("index_mle__L9", 190), ("padding_weight__L0", 84), ("padding_weight__L1", 85),
    ("padding_weight__L10", 94), ("padding_weight__L11", 95), ("padding_weight__L12", 96),
    ("padding_weight__L13", 97), ("padding_weight__L14", 98), ("padding_weight__L15", 99),
    ("padding_weight__L16", 100), ("padding_weight__L17", 101), ("padding_weight__L18", 102),
    ("padding_weight__L19", 103), ("padding_weight__L2", 86), ("padding_weight__L20", 104),
    ("padding_weight__L21", 105), ("padding_weight__L22", 106), ("padding_weight__L23", 107),
    ("padding_weight__L24", 108), ("padding_weight__L25", 109), ("padding_weight__L26", 110),
    ("padding_weight__L27", 111), ("padding_weight__L28", 112), ("padding_weight__L3", 87),
    ("padding_weight__L4", 88), ("padding_weight__L5", 89), ("padding_weight__L6", 90),
    ("padding_weight__L7", 91), ("padding_weight__L8", 92), ("padding_weight__L9", 93),
    ("plus_one_run__L0", 113), ("plus_one_run__L1", 114), ("plus_one_run__L10", 123),
    ("plus_one_run__L11", 124), ("plus_one_run__L12", 125), ("plus_one_run__L13", 126),
    ("plus_one_run__L14", 127), ("plus_one_run__L15", 128), ("plus_one_run__L16", 129),
    ("plus_one_run__L17", 130), ("plus_one_run__L18", 131), ("plus_one_run__L19", 132),
    ("plus_one_run__L2", 115), ("plus_one_run__L20", 133), ("plus_one_run__L21", 134),
    ("plus_one_run__L22", 135), ("plus_one_run__L23", 136), ("plus_one_run__L24", 137),
    ("plus_one_run__L25", 138), ("plus_one_run__L26", 139), ("plus_one_run__L27", 140),
    ("plus_one_run__L28", 141), ("plus_one_run__L29", 142), ("plus_one_run__L3", 116),
    ("plus_one_run__L30", 143), ("plus_one_run__L31", 144), ("plus_one_run__L32", 145),
    ("plus_one_run__L33", 146), ("plus_one_run__L4", 117), ("plus_one_run__L5", 118),
    ("plus_one_run__L6", 119), ("plus_one_run__L7", 120), ("plus_one_run__L8", 121),
    ("plus_one_run__L9", 122), ("sel_partial_nibble__L0", 80), ("sel_partial_nibble__L1", 81),
    ("sel_partial_nibble__L2", 82), ("sel_partial_nibble__L3", 83), ("sumcheck_round4", 6)]

theorem vtPairs_ok : (vtPairs.all fun p => wOkB p.2 p.1) = true := by decide +kernel

theorem vtPairs_names : B1.Tables.vtKidS.filter (fun g => g != "__loop9" && g != "shared_selector_tables" && g != "__loop8") =
    vtPairs.map Prod.fst := by decide +kernel

theorem vt_kids_totalLe : ∀ g ∈ B1.Tables.vtKidS, g ≠ "__loop9" → g ≠ "__loop8" →
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
    exact totalLe_mono (wSB_totalLe (j := 80) (by decide +kernel)) (by unfold kSp; omega)
  · rw [show B1.Tables.lName "sel_partial_nibble" 1 = "sel_partial_nibble__L1" by decide]
    exact totalLe_mono (wSB_totalLe (j := 81) (by decide +kernel)) (by unfold kSp; omega)
  · rw [show B1.Tables.lName "sel_partial_nibble" 2 = "sel_partial_nibble__L2" by decide]
    exact totalLe_mono (wSB_totalLe (j := 82) (by decide +kernel)) (by unfold kSp; omega)
  · rw [show B1.Tables.lName "sel_partial_nibble" 3 = "sel_partial_nibble__L3" by decide]
    exact totalLe_mono (wSB_totalLe (j := 83) (by decide +kernel)) (by unfold kSp; omega)

/-! ## The weights of `verify_tables`' and the terminal's callees -/

theorem vtPairs_okW (op : Opcode) : (vtPairs.all fun p => kuOkB op p.2 p.1) = true := by
  cases op <;> decide +kernel

theorem vt_kids_weightLe (op : Opcode) : ∀ g ∈ B1.Tables.vtKidS, g ≠ "__loop9" → g ≠ "__loop8" →
    g ≠ "shared_selector_tables" →
      WeightLe coreProgram (B2C.ωArm B2C.xmssArmC op) g (fun _ => kuSB op g) := by
  intro g hg h1 h3 h2
  have hm : g ∈ vtPairs.map Prod.fst := by
    rw [← vtPairs_names, List.mem_filter]
    exact ⟨hg, by simp [h1, h2, h3]⟩
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
  exact kuSB_weightLe (List.all_eq_true.mp (vtPairs_okW op) p hp)

/-- A loop's certificate per iteration, as `Budget.LoopW`. -/
theorem loopW_of {ω : String → ℕ} {f : String} {K : ℕ} (h : LoopWeightLe ω f K) :
    Budget.LoopW ω f K := fun rd t args rets a e hn hv hb ha he hae heo =>
  h rd t args rets a e hn hv hb ha he hae heo

/-- The four partial nibble selectors' weights, at most. -/
noncomputable def kSpW (op : Opcode) : ℕ :=
  max (max (kuSB op "sel_partial_nibble__L0") (kuSB op "sel_partial_nibble__L1"))
    (max (kuSB op "sel_partial_nibble__L2") (kuSB op "sel_partial_nibble__L3"))

theorem weightLe_mono {ω : String → ℕ} {f : String} {B B' : ℕ}
    (h : WeightLe coreProgram ω f fun _ => B) (hB : B ≤ B') : WeightLe coreProgram ω f fun _ => B' :=
  fun rd t args rets hn hv hb => (h rd t args rets hn hv hb).trans hB

theorem sp_weightLe (op : Opcode) : ∀ j < 4, WeightLe coreProgram (B2C.ωArm B2C.xmssArmC op)
    (B1.Tables.lName "sel_partial_nibble" j) (fun _ => kSpW op) := by
  intro j hj
  interval_cases j
  · rw [show B1.Tables.lName "sel_partial_nibble" 0 = "sel_partial_nibble__L0" by decide]
    exact weightLe_mono (kuSB_weightLe (j := 80) (by cases op <;> decide +kernel)) (by unfold kSpW; omega)
  · rw [show B1.Tables.lName "sel_partial_nibble" 1 = "sel_partial_nibble__L1" by decide]
    exact weightLe_mono (kuSB_weightLe (j := 81) (by cases op <;> decide +kernel)) (by unfold kSpW; omega)
  · rw [show B1.Tables.lName "sel_partial_nibble" 2 = "sel_partial_nibble__L2" by decide]
    exact weightLe_mono (kuSB_weightLe (j := 82) (by cases op <;> decide +kernel)) (by unfold kSpW; omega)
  · rw [show B1.Tables.lName "sel_partial_nibble" 3 = "sel_partial_nibble__L3" by decide]
    exact weightLe_mono (kuSB_weightLe (j := 83) (by cases op <;> decide +kernel)) (by unfold kSpW; omega)

/-- The column selectors' weights, at most. -/
noncomputable def kCsW (op : Opcode) : ℕ :=
  ((List.range 29).map fun κ => kuSB op (B1.Tables.lName "column_selector" κ)).foldr max 0

theorem cs_okW (op : Opcode) : (List.range 29).all (fun κ =>
    kuOkB op (261 + κ) (B1.Tables.lName "column_selector" κ)) = true := by
  cases op <;> decide +kernel

theorem cs_weightLe (op : Opcode) : ∀ κ < 29, WeightLe coreProgram (B2C.ωArm B2C.xmssArmC op)
    (B1.Tables.lName "column_selector" κ) (fun _ => kCsW op) := by
  intro κ hκ
  refine weightLe_mono (kuSB_weightLe (List.all_eq_true.mp (cs_okW op) κ (List.mem_range.mpr hκ))) ?_
  exact B1.Tables.le_foldr_max (List.mem_map.mpr ⟨κ, List.mem_range.mpr hκ, rfl⟩)

theorem ratio_le {w A t B : ℕ} (h : 1000 * w ≤ A * t) (ht : t ≤ B) : w ≤ A * B / 1000 :=
  (Nat.le_div_iff_mul_le (by norm_num)).mpr (by
    have := Nat.mul_le_mul_left A ht; rw [Nat.mul_comm w]; omega)

/-- **`verify_sub`'s callees' words at `B2C.fs`.** -/
noncomputable def vsWords : B1.VerifySub.VsWords B2C.fs where
  Bg := wSB "g_power_of_word"
  hg := wSB_totalLe (j := 3) (by decide +kernel)
  Ba := wSB "assert_canonical"
  ha := wSB_totalLe (j := 1) (by decide +kernel)
  K29 := wSK "__loop27"
  R := max (wSB "gkr_rounds__L1") (wSB "gkr_rounds__L2")
  K8 := wSK "__loop7"
  h29 := wSK_totalLeOn (j := 378) (by decide +kernel)
  hR1 := totalLe_mono (wSB_totalLe (j := 380) (by decide +kernel)) (le_max_left _ _)
  hR2 := totalLe_mono (wSB_totalLe (j := 379) (by decide +kernel)) (le_max_right _ _)
  h8 := wSK_totalLeOn (j := 78) (by decide +kernel)
  Kf := wSB
  Ksh := B2C.fs "shared_selector_tables" + (B2C.fs "__loop8" + 15 * wSK "__loop8") + kSp
  K10 := wSK "__loop9"
  hKf := vt_kids_totalLe
  hsh := B1.Tables.ss_totalLeOn (wSK "__loop8") kSp (wSK_totalLeOn (j := 79) (by decide +kernel))
    sp_totalLe
  h10 := wSK_totalLeOn (j := 249) (by decide +kernel)
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
  ωv := fun op => B2C.ωArm B2C.xmssArmC op
  Kvw := kuSB
  Wss := fun op => B2C.ωArm B2C.xmssArmC op "shared_selector_tables" + 15 * kuSK op "__loop8" +
    kSpW op
  Kw10 := fun op => kuSK op "__loop9"
  hKvw := vt_kids_weightLe
  hssw := fun op => B1.Tables.ss_weightLeOn _ _ _
    (loopW_of (kuSK_loop (j := 79) (by cases op <;> decide +kernel))) (sp_weightLe op)
  h10w := fun op => loopW_of (kuSK_loop (j := 249) (by cases op <;> decide +kernel))
  Weqc := fun op => kuSB op "eq_prefix_chain"
  W15 := fun op => krVl15A op * max (B2C.fs "__loop14") (32 * 38) / 1000
  Wst := fun op => kuSB op "selector_tables"
  Wcs := kCsW
  Wrsw := fun op => krVrswA op * (B2C.fs "ring_switch_weight" + 2240 + 16433) / 1000
  hEqcW := fun op => kuSB_weightLe (j := 4) (by cases op <;> decide +kernel)
  hStW := fun op => kuSB_weightLe (j := 16) (by cases op <;> decide +kernel)
  hCsW := cs_weightLe
  h15W := fun op rd t args rets hn hv hb ht => ratio_le (krVl15_weight op rd t args rets hn hv hb) ht
  hrswW := fun op rd t args rets hn hv hb ht => ratio_le (krVrsw_weight op rd t args rets hn hv hb) ht

end
end LeanVM.Guest.Count
