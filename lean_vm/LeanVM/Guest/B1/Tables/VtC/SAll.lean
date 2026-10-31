/-
  LeanVM.Guest.B1.Tables.VtC.SAll

  `verify_tables`' statements `0 ..< 2404` hold on the honest valuation (fork S of B1-c's
  completeness).
-/

module

public import LeanVM.Guest.B1.Tables.VtC.SP2

/-!
# Statements `0 ..< 2404` (G:1948-2030)

`vtS_complete`: for the blocks' log-sizes `κ` (`block_kappa`), the bus point at `zeta`
(`g_bus_mu = g^|point|`, `|point| < 33`), the tables' row counts `n` and heights
`τ t = max (log2Ceil (n t)) floor < 29`, `τ t ≤ |point|`, on a memory defined below `2^8` holding
`block_kappa`, the squares, `dims_g`, `table_rows`, and the own buffers' honest words
(`sort_order`: `vtSortW κ`, `block_side_tab`: `vtSideW`, `block_off_g`: `vtOffW κ`, `idxc_tab`:
`vtIdxcW`, `zeta1`: `1 + ζ`, the shared tables: `RunTables`), the oracle returning
`padding_weight`'s outcomes and `plus_one_run`'s `0`: every statement before the bus sides holds,
and the values later statements read are the honest ones.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

theorem vtS_copies_check : tbStmtsEqb [.atom (.copy (.n 22) (.n 0)), .atom (.copy (.n 23) (.n 1)),
    .atom (.copy (.n 24) (.n 2)), .atom (.copy (.n 25) (.n 3)), .atom (.copy (.n 26) (.n 4)),
    .atom (.copy (.n 27) (.n 19)), .atom (.copy (.n 28) (.n 20)), .atom (.copy (.n 29) (.n 21))]
    ((vtPre.drop 0).take 8) = true := by simp only [vtPre_drop]; decide +kernel

section
variable {rd : Reader} {w : ℕ → E} {args : List E}

/-- **`verify_tables`' statements `0 ..< 2404` complete.** -/
theorem vtS_complete (hl : args.length = 22) (hlow : LowDefB 8 rd)
    (κ : ℕ → ℕ) (hκ : ∀ b < 153, κ b < 34) (point : List E) (hμ33 : point.length < 33)
    (τ n : ℕ → ℕ) (hτ : ∀ t < 6, τ t = max (log2Ceil (n t)) (tableLogFloors.getD t 0))
    (hτ29 : ∀ t < 6, τ t < 29) (hτμ : ∀ t < 6, τ t ≤ point.length)
    -- the arguments' buffers
    (hz : TbReadsAt rd (args.getD 8 0) point) (h9 : args.getD 9 0 = gen ^ point.length)
    (hdims : ∀ t < 6, LoadHolds rd (args.getD 10 0) (t + 1) (gen ^ τ t))
    (hrows : ∀ t < 6, LoadHolds rd (args.getD 11 0) t (eOfNat (n t)))
    (hbk : ∀ b < 153, LoadHolds rd (args.getD 12 0) b (gen ^ κ b))
    (hsq : TbReadsAt rd (args.getD 13 0) gSquaresList)
    -- the own buffers
    (hso : TbReadsAt rd (w 30) (vtSortW κ)) (hst : TbReadsAt rd (w 31) vtSideW)
    (hoff : TbReadsAt rd (w 185) (vtOffW κ)) (hidxc : TbReadsAt rd (w 2732) vtIdxcW)
    (hz1 : TbReadsAt rd (w 2767) (point.map (1 + ·)))
    (hrun : ∀ t < 6, RunTables rd (w 2769 * gen ^ (288 * t)) (w 2770 * gen ^ (144 * t))
      (point.length - τ t) (point.drop (τ t)) ((point.map (1 + ·)).drop (τ t))
      ((gSquaresList.drop (τ t)).take (point.length - τ t)))
    -- the callees' returns
    (hwp : ∀ t < 6, w (vtPadV t) = paddingWeight (point.take (τ t)) (n t) ∧
      w (vtPadV t + 1) = PadLead (τ t) (n t) ∧ w (vtPadV t + 2) = PadRest (τ t) (n t))
    (hw2768 : w 2768 = 0) :
    (∀ s ∈ (vtPre.drop 0).take 2404, VSH (coreProgram.Rel rd) rd (vtσ rd w args) s) ∧
      (∀ i < 5, vtσ rd w args (.n (22 + i)) = args.getD i 0) ∧
      (∀ i < 3, vtσ rd w args (.n (27 + i)) = args.getD (19 + i) 0) ∧
      vtσ rd w args (.n 30) = w 30 ∧ vtσ rd w args (.n 31) = w 31 ∧
      vtσ rd w args (.n 185) = w 185 ∧
      (∀ t < 6, vtσ rd w args (.n (vtPadV t)) = paddingWeight (point.take (τ t)) (n t)) ∧
      (∀ t < 6, vtσ rd w args (.n (vtShLen t)) = gen ^ (point.length - τ t)) ∧
      vtσ rd w args (.n 2639) = w 2639 ∧ vtσ rd w args (.n 2732) = w 2732 ∧
      vtσ rd w args (.n 2767) = w 2767 ∧ vtσ rd w args (.n 2769) = w 2769 ∧
      vtσ rd w args (.n 2770) = w 2770 := by
  have hsq' : ∀ j < 34, LoadHolds rd (args.getD 13 0) j (gen ^ 2 ^ j) := fun j hj => by
    have := hsq j (by simp [gSquaresList]; exact hj)
    simpa [gSquaresList] using this
  obtain ⟨p2, hpw, hsl, e2639, e2732, e2767, e2769, e2770⟩ := vtS_p2 hl hlow point hμ33 τ n hτ
    hτ29 hτμ hz h9 hdims hrows hsq hwp hidxc hz1 hw2768 hrun
  have hc := vt_goodL (rd := rd) (w := w) hl 0 _ vtS_copies_check
  simp only [GoodL, GoodS, fixNe, Good, and_true] at hc
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := hc
  have p := fun i (hi : i < 22) => vt_param (rd := rd) (w := w) hl hi
  refine ⟨forall_slice_split 0 2189 215 (vtS_sort hl hlow κ hκ hbk hsq' hso hst hoff) p2,
    fun i hi => ?_, fun i hi => ?_, vt_alloc hl 8 (sz := 153) (by decide +kernel),
    vt_alloc hl 10 (sz := 153) (by decide +kernel), vt_alloc hl 317 vtSort_alloc185, hpw, hsl,
    e2639, e2732, e2767, e2769, e2770⟩
  · interval_cases i
    · rw [c0, p 0 (by norm_num)]
    · rw [c1, p 1 (by norm_num)]
    · rw [c2, p 2 (by norm_num)]
    · rw [c3, p 3 (by norm_num)]
    · rw [c4, p 4 (by norm_num)]
  · interval_cases i
    · rw [c5, p 19 (by norm_num)]
    · rw [c6, p 20 (by norm_num)]
    · rw [c7, p 21 (by norm_num)]

end

end
end LeanVM.Guest.B1.Tables
