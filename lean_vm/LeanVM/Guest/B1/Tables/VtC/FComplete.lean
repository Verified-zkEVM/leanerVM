/-
  LeanVM.Guest.B1.Tables.VtC.FComplete

  `verify_tables`' table evaluations, forms, air terms and final check (statements
  `5259 ..< 10209`) complete: on the honest memory, every one holds of the honest valuation.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.FWin
public import LeanVM.Guest.B1.Tables.VtC.FFinal

/-!
# The table phase's evaluations and final check, complete (G:2231-2290)

`vtF_complete`: the window (`vtF_window`) and the final check `assert air_acc == claim`, which
holds since `air_acc` is `termsPure`'s terminal value over the six tables (`vt_asm_finalF`) and
the table sumcheck's final claim `σ 5933` is it (`hfin`, the specification's check of the honest
run). It also gives what follows: the evaluations' values, the sponge after them
(`vt_evals_fsF`), and `VtF`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (blockSel termsPure)

@[expose] public section

theorem vtF_split : tbStmtsEqb ((vtPre.drop vtFLo).take (10209 - vtFLo))
    ((vtPre.drop vtFLo).take (vtFHi - vtFLo) ++ [.atom (.assertEq (.n 11197) (.n 5933))]) =
      true := by
  decide +kernel

section
variable {rd : Reader} {w : ℕ → E} {args : List E}

set_option maxHeartbeats 1000000 in
/-- **Statements `5259 ..< 10209` complete**, and what they leave: `VtF`, the evaluations' values
and the sponge after them. -/
theorem vtF_complete (hl : args.length = 22) (bc : List K) (hbc : bc.length = 2 ^ 23)
    {point : List E} {lm : ℕ} {rows : List ℕ} (hr : rows.length = 6)
    (hdim : ∀ t < 6, LoadHolds rd (vtσ rd w args (.n 10)) (t + 1) (gen ^ vtHt rows t))
    (hP : ∀ i < 51, vtσ rd w args (.n (vtPushPadData.getD i default).2.2.1) =
      blockSel (vtSizesP lm (vtHt rows)) point.length (3 + i) point)
    (hC : ∀ i < 45, vtσ rd w args (.n (vtCountPadData.getD i default).2.2.1) =
      blockSel (vtSizesC (vtHt rows)) point.length i point)
    (hpull : VtPullSelsH (vtσ rd w args))
    (hz1 : TbReadsAt rd (vtσ rd w args (.n 2767)) (point.map (1 + ·)))
    (hxi : vtσ rd w args (.n 5896) = 1 ∧ vtσ rd w args (.n 5897) = vtσ rd w args (.n 5895) ∧
      vtσ rd w args (.n 5898) = vtσ rd w args (.n 5895) ^ 2 ∧
      vtσ rd w args (.n 5899) = vtσ rd w args (.n 5895) ^ 3 ∧
      vtσ rd w args (.n 5900) = vtσ rd w args (.n 5895) ^ 4)
    {alphas : List E} (hal : alphas.length = 4)
    (hW : TbReadsAt rd (vtσ rd w args (.n 14)) (eqKernel alphas)) {n : ℕ}
    (hgn : vtσ rd w args (.n 5817) = gen ^ n) (hhn : ∀ t < 6, vtHt rows t ≤ n)
    (hnp : n ≤ point.length) {pts : List E} (hpl : pts.length = n)
    (hcp : ∀ j ≤ n, LoadHolds rd (vtσ rd w args (.n 5915)) j (pts.take j).prod)
    (hpe : EqPrefix rd (vtσ rd w args (.n 5936)) 1 (vtσ rd w args (.n 18))
      (vtσ rd w args (.n 2767)) n)
    (hchi : ∀ i < n, LoadHolds rd (vtσ rd w args (.n 18)) (n - 1 - i) (pts.getD i 0))
    {evs : List E} (hevl : evs.length = 157)
    (hcur : TbReadsAt rd (vtσ rd w args (.n 5932)) evs)
    (hpool : ∀ k < 157, LoadHolds rd (vtσ rd w args (.n 16)) (5 + k) (evs.getD k 0))
    (hcpl : ∀ k < 157, LoadHolds rd (vtσ rd w args (.n 17)) (5 + k)
      (gen ^ vtHt rows (vtEvTab k)))
    (hcap : ∀ i < 5, IsCanonical128 (vtσ rd w args (.n (5927 + i))))
    (hfin : (termsPure ((powers (vtσ rd w args (.n 5895)) 5).take 2)
      ((powers (vtσ rd w args (.n 5895)) 5).drop 2) pts.reverse
      (List.zip (vtRows (tableHeightsOf rows)
        (vtAcc2 (layoutOf bc lm rows) alphas (vtσ rd w args (.n 15)) point
          [vtσ rd w args (.n 2914), vtσ rd w args (.n 2927), vtσ rd w args (.n 2940)]
          (vtσ rd w args (.n 4444)) (vtσ rd w args (.n 4502)) (vtσ rd w args (.n 2639))
          (vtσ rd w args (.n 27)) (vtσ rd w args (.n 28)) (vtσ rd w args (.n 29))).1
            point pts) (vtEvsT (vtσ rd w args))) 0 0 []).1 = vtσ rd w args (.n 5933)) :
    (∀ s ∈ (vtPre.drop 5259).take (10209 - 5259),
        VSH (coreProgram.Rel rd) rd (vtσ rd w args) s) ∧
      VtF rd (vtσ rd w args) ∧ vtEvs (vtσ rd w args) = evs ∧
      (∀ j < 39, (⟨vtCapV (vtσ rd w args) 0, []⟩ : Fs).absorbAll
          ((vtEvs (vtσ rd w args)).take (4 * (j + 1))) dsObserve =
        ⟨vtCapV (vtσ rd w args) j,
          (((vtEvs (vtσ rd w args)).drop (4 * j)).take 4).map (·, dsObserve)⟩ ∧
        vtCapV (vtσ rd w args) (j + 1) = capOf (Fs.perm ⟨vtCapV (vtσ rd w args) j,
          (((vtEvs (vtσ rd w args)).drop (4 * j)).take 4).map (·, dsObserve)⟩)) ∧
      vtσ rd w args (.n 11197) = vtσ rd w args (.n 5933) := by
  have hkl : (eqKernel alphas).length = 16 := by
    rw [show (16 : ℕ) = 2 ^ alphas.length by rw [hal]; rfl]
    exact vt_length_eqKernel alphas
  obtain ⟨as, bs, -, -, -, -, hpre⟩ := id hpe
  have hwin := vtF_window (w := w) hl (by omega) hcur hW (by omega) hdim hgn hhn hcp
    (pe := prefixProd 1 as bs) (fun j hj ↦ hpre j hj) hpool hcpl hcap
  have hV := vtF_of_vsh hwin
  have hfinG := vt_asm_finalF hV bc hbc hr hdim hP hC hpull hz1 hxi hal hW hgn hhn hnp hpl hcp
    hpe hchi
  have e11197 : vtσ rd w args (.n 11197) = vtσ rd w args (.n 5933) := hfinG.symm.trans hfin
  refine ⟨?_, hV, ?_, vt_evals_fsF hV, e11197⟩
  · rw [tbStmtsEqb_sound vtF_split]
    intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact hwin s hs
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      subst hs
      show vtσ rd w args (.n 11197) + vtσ rd w args (.n 5933) = 0
      rw [e11197]
      exact CharTwo.add_self_eq_zero _
  · apply List.ext_getElem (by rw [vtEvs_length, hevl])
    intro k h1 _
    have hk : k < 157 := by simpa [vtEvs] using h1
    rw [← List.getD_eq_getElem _ 0 h1, vtEvs_getD _ hk,
      (vtF_evRead (w := w) hl hcur (by omega) hk).2, List.getD_eq_getElem _ _ (by omega)]

end

end
end LeanVM.Guest.B1.Tables
