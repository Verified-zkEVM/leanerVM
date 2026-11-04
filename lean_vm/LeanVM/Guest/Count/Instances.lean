/-
  LeanVM.Guest.Count.Instances

  The budget's static hypotheses at the deployed frame sizes, from the certificate families: the
  words of `main`'s statically bounded callees and of its non-static callees' static callees
  (`mainStatics`), and `open_stacked`'s named callees and residual loops (`osLeafBounds`,
  `osLoopBounds`). `main`'s callees' instruction counts (`mainCounts`) are `Budget/MvCount`'s.
-/

module

public import LeanVM.Guest.Count.Words
public import LeanVM.Guest.Budget.MainCount
public import LeanVM.Guest.B1.Main.MainHonestBudgetB
public import LeanVM.Guest.B1.Place.OsFinalB

/-!
# The budget's static hypotheses

Words at `B2C.fs` by name (`Count.Words`): `wSB f`, `f`'s constant, and `wSK f`, a loop helper's
words per iteration, each function found by `wIdx` (`wIdxL` for `__loop{n}`) and checked by
`decide +kernel`.
-/

namespace LeanVM.Guest.Count

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest

@[expose] public section

/-- **`main`'s statically bounded callees' words.** -/
theorem mainStaticsMain : B1.Main.MainStaticsMain B2C.fs wSB wSK where
  l1 := wSK_totalLeOn (j := wIdxL 0) (by decide +kernel)
  l2 := wSK_totalLeOn (j := wIdxL 1) (by decide +kernel)
  l3 := wSK_totalLeOn (j := wIdxL 2) (by decide +kernel)
  l4 := wSK_totalLeOn (j := wIdxL 3) (by decide +kernel)
  st := wSB_totalLe (j := wIdx "statement_digest") (by decide +kernel)

/-- `da_levels__L{2^k}_L{k}`, `k ≤ 10`, checked. -/
theorem dlNames_ok : (List.range 11).all (fun k => wOkB (wIdx B1.Da.dlNames[k]!) B1.Da.dlNames[k]!) = true := by
  decide +kernel

/-- The column offsets' doubling loops `__loop{22 + b}`, checked. -/
theorem offLoops_ok :
    (List.range 7).all (fun b => wOkK (wIdxL (22 + b)) (B1.Da.offLoopName b)) = true := by
  decide +kernel

/-- **`da_vector`'s words within its static bound**: its frame and buffers, its callees' frames
and buffers, the doublings' iterations. -/
theorem vec_le : B2C.fs "da_vector" + 30 + (B2C.fs "da_factors__L14_L7_L0" + 256 +
    (B2C.fs "da_expand__L14_L7" + (B2C.fs "da_factors__L7_L8_L128" + 256 +
      (B2C.fs "da_column_offsets" + 1080 +
        ((List.range 7).map fun b => 2 ^ b * wSK (B1.Da.offLoopName b)).sum + 0)))) ≤
    wSB "da_vector" := by
  decide +kernel

theorem exp_le : B2C.fs "da_expand__L7_L8" ≤ wSB "da_expand__L7_L8" := by decide +kernel

/-- **`da_verify`'s static bounds**, at the deployed frame sizes. -/
theorem dvStatic : B1.Da.DvStaticB B2C.fs wSB wSK where
  l17 := wSK_totalLeOn (j := wIdxL 17) (by decide +kernel)
  l19 := wSK_totalLeOn (j := wIdxL 19) (by decide +kernel)
  l20 := wSK_totalLeOn (j := wIdxL 20) (by decide +kernel)
  l21 := wSK_totalLeOn (j := wIdxL 21) (by decide +kernel)
  off := fun _ hb => wSK_totalLeOn (all_range_get offLoops_ok hb)
  dl := fun _ hk => wSB_totalLe (all_range_get dlNames_ok (Nat.lt_succ_of_le hk))
  vec := vec_le
  exp := exp_le

/-- `claim_list_last__L{k}`, `k < 17`, checked. -/
theorem clNames_ok :
    (List.range 17).all (fun k => wOkB (wIdx B1.Digest.clNames[k]!) B1.Digest.clNames[k]!) = true := by
  decide +kernel

/-- **The words of the static callees of `main`'s non-static callees**, at `B2C.fs`. -/
theorem mainStatics : B1.Main.MainStatics B2C.fs wSB wSK where
  main := mainStaticsMain
  dv := dvStatic
  ls := wSB_totalLe (j := wIdx "list_split") (by decide +kernel)
  l16 := wSK_totalLeOn (j := wIdxL 15) (by decide +kernel)
  cl := fun _ hk => wSB_totalLe (all_range_get clNames_ok hk)
  l25 := wSK_totalLeOn (j := wIdxL 29) (by decide +kernel)
  l26 := wSK_totalLeOn (j := wIdxL 30) (by decide +kernel)
  l27 := wSK_totalLeOn (j := wIdxL 31) (by decide +kernel)
  bs := wSB_totalLe (j := wIdx "batch_sumcheck__L23") (by decide +kernel)

/-- `open_stacked`'s named callees, checked. -/
theorem osKind_ok : B1.osKindTable.all (fun p => wOkB (wIdx p.1) p.1) = true := by
  decide +kernel

/-- **`open_stacked`'s named callees within `wSB`.** -/
theorem osLeafBounds : B1.OsLeafBounds B2C.fs wSB := fun f K hK =>
  wSB_totalLe (List.all_eq_true.mp osKind_ok (f, K) (B1.os_mem_of_lookup B1.osKindTable hK))

set_option maxRecDepth 100000 in
/-- The residual loops of the candidates, checked. -/
theorem osRes_ok : ∀ m < 28, ∀ l < (B1.Whir.osCfg m).levels.length,
    wOkK (wIdxL ((B1.Whir.osCfg m).loopBase + (B1.Whir.osCfg m).levels.length + l))
      ((B1.Whir.osCfg m).resLoop l) = true := by
  decide +kernel

/-- **Each candidate's residual loops within `wSK` per iteration.** -/
theorem osLoopBounds : ∀ m < 28, B1.OsLoopBounds B2C.fs wSK (B1.Whir.osCfg m) :=
  fun m hm l hl => wSK_totalLeOn (osRes_ok m hm l hl)

end
end LeanVM.Guest.Count
