/-
  LeanVM.Guest.B1.Tables.VerifyTablesRunM

  The specification's run of `tablesSeg` over a hash model, phase by phase.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesRun
public import LeanVM.Guest.B1.Tables.GkrBaseM
public import LeanVM.Guest.B1.VerifySub.InterfaceM

/-!
# `tablesSeg` over a hash model

`VerifyTablesRun.lean` over a hash model `M`, every hash answered: `busRest` with the bytecode's
value from an `ev` taking it over the model (`runsToM_busRest`), `tableTerms` and
`tableSumcheck` (`runsToM_tableTerms`, `runsToM_tableSumcheck`), `tablePhase`,
`publicInputPhase` and `tablesSeg`, the chain's steps given by `obsAllM`, `sqCvM`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {M : HashModel}

/-- The bytecode's value over the model, consuming nothing (`runsTo_bytecodeAt`). -/
theorem runsToM_bytecodeAt {ev : Evaluations} {words : List K} {point : List E} {value : E}
    (h : BytecodeAtM M ev words point value) (cv : Digest) :
    RunsToM M (ev.bytecode words point) cv [] value cv := fun _ _ _ => h _

/-- **`busRest`'s run over the model**: the three memory limbs and the two final counters read,
the bytecode's value from `ev` (`runsTo_busRest`). -/
theorem runsToM_busRest {ev : Evaluations} {layout : Layout} {alphas : List E} {beta : E}
    {point treeValues : List E} {cv cv' : Digest} {memory : List E} (hm : memory.length = 3)
    {memoryFinal bytecodeFinal bytecodeValue : E}
    (ho : obsAllM M cv (memory ++ [memoryFinal, bytecodeFinal]) = some cv')
    (hbv : BytecodeAtM M ev layout.bytecode (point.take layout.logBytecode ++ alphas)
      bytecodeValue) :
    RunsToM M (busRest ev layout alphas beta point treeValues) cv
      (memory ++ [memoryFinal, bytecodeFinal])
      (busVal layout alphas beta point treeValues memory memoryFinal bytecodeFinal bytecodeValue)
      cv' := by
  rw [obsAllM_append_eq] at ho
  obtain ⟨c1, h1, ho⟩ := Option.bind_eq_some_iff.mp ho
  obtain ⟨c2, h2, ho⟩ := Option.bind_eq_some_iff.mp ho
  obtain ⟨c3, h3, ho⟩ := Option.bind_eq_some_iff.mp ho
  obtain rfl : c3 = cv' := Option.some.inj ho
  have h : RunsToM M (busRest ev layout alphas beta point treeValues) cv
      (memory ++ ([memoryFinal] ++ ([bytecodeFinal] ++ ([] ++ []))))
      (busVal layout alphas beta point treeValues memory memoryFinal bytecodeFinal bytecodeValue)
      c3 := by
    unfold busRest
    refine (runsToM_readN_of_length hm h1).bind ?_
    refine (runsToM_readE h2).bind ?_
    refine (runsToM_readE h3).bind ?_
    refine (runsToM_bytecodeAt hbv _).bind ?_
    exact runsToM_ret _ _
  exact h.of_eq (by simp) rfl rfl

/-- **`tableTerms`' run over the model** (`runsTo_tableTerms`). -/
theorem runsToM_tableTerms (constraintPowers formPowers point : List E) :
    ∀ (rows : List (Table × ℕ × List Form × E)) (evss : List (List E)), evss.length = rows.length →
      (∀ i (hi : i < rows.length) (he : i < evss.length), evss[i].length = rows[i].1.width) →
      ∀ (cursor : ℕ) (final : E) (claims : List ColumnClaim) (cv cv' : Digest),
      obsAllM M cv evss.flatten = some cv' →
      RunsToM M (tableTerms constraintPowers formPowers point rows cursor final claims) cv
        evss.flatten (ttVal constraintPowers formPowers point rows evss cursor final claims) cv'
  | [], [], _, _, cursor, final, claims, cv, cv', ho => by
    obtain rfl : cv = cv' := Option.some.inj ho
    exact runsToM_ret _ _
  | (table, height, forms, weight) :: rest, evs :: evss, hl, hw, cursor, final, claims, cv, cv',
      ho => by
    have hw0 := hw 0 (by simp) (by simp)
    simp only [List.getElem_cons_zero] at hw0
    have ih := runsToM_tableTerms constraintPowers formPowers point rest evss (by simpa using hl)
      (fun i hi he => by have := hw (i + 1) (by simp; omega) (by simp; omega); simpa using this)
    rw [List.flatten_cons, obsAllM_append_eq] at ho
    obtain ⟨c1, h1, ho⟩ := Option.bind_eq_some_iff.mp ho
    unfold tableTerms
    exact ((runsToM_readN_of_length hw0 h1).bind (ih _ _ _ _ _ ho)).of_eq (by simp) rfl rfl

/-- **`tableSumcheck`'s run over the model** (`runsTo_tableSumcheck`). -/
theorem runsToM_tableSumcheck {heights : List ℕ} {busForms : List (List Form)}
    {constraintPowers formPowers equalityPoint : List E} {target : E} {cv cv1 cv2 : Digest}
    {ws rs : List E} {cl : E}
    (hsc : RunsToM M (sumcheck target 4 (List.replicate (heights.foldl max 0) none)) cv ws (rs, cl)
      cv1)
    {evss : List (List E)} (ho : obsAllM M cv1 evss.flatten = some cv2)
    (hl : evss.length = (List.zip tables (List.zip heights (List.zip busForms
      (tableWeights heights equalityPoint rs.reverse)))).length)
    (hw : ∀ i (hi : i < (List.zip tables (List.zip heights (List.zip busForms
      (tableWeights heights equalityPoint rs.reverse)))).length) (he : i < evss.length),
      evss[i].length = (List.zip tables (List.zip heights (List.zip busForms
        (tableWeights heights equalityPoint rs.reverse))))[i].1.width)
    (hfin : (ttVal constraintPowers formPowers rs.reverse (List.zip tables (List.zip heights
      (List.zip busForms (tableWeights heights equalityPoint rs.reverse)))) evss 0 0 []).1 = cl) :
    RunsToM M (tableSumcheck heights busForms constraintPowers formPowers equalityPoint target) cv
      (ws ++ evss.flatten)
      (ttVal constraintPowers formPowers rs.reverse (List.zip tables (List.zip heights
        (List.zip busForms (tableWeights heights equalityPoint rs.reverse)))) evss 0 0 []).2
      cv2 := by
  refine RunsToM.of_eq (xs := ws ++ (evss.flatten ++ ([] ++ []))) ?_ (by simp) rfl rfl
  unfold tableSumcheck
  refine hsc.bind ?_
  refine (runsToM_tableTerms constraintPowers formPowers rs.reverse _ evss hl hw 0 0 [] cv1 cv2
    ho).bind ?_
  refine (runsToM_require hfin _).bind ?_
  exact runsToM_ret _ _

/-- **`tablePhase`'s run over the model**: `ξ` squeezed, then the table sumcheck
(`runsTo_tablePhase`). -/
theorem runsToM_tablePhase {layout : Layout} {bus : BusResult} {cv cξ cv' : Digest} {xs : List E}
    {tc : List ColumnClaim} (hξ : sqCvM M cv = some cξ)
    (h : RunsToM M (tableSumcheck layout.tableLogHeights bus.forms
      ((powers (challengeOf cξ) ((tables.map Table.nConstraints).sum + 3)).take
        (tables.map Table.nConstraints).sum)
      ((powers (challengeOf cξ) ((tables.map Table.nConstraints).sum + 3)).drop
        (tables.map Table.nConstraints).sum) bus.point
      (dot ((powers (challengeOf cξ) ((tables.map Table.nConstraints).sum + 3)).drop
        (tables.map Table.nConstraints).sum) bus.totals)) cξ xs tc cv') :
    RunsToM M (tablePhase layout bus) cv xs (bus.claims ++ tc) cv' := by
  refine RunsToM.of_eq (xs := [] ++ (xs ++ [])) ?_ (by simp) rfl rfl
  unfold tablePhase
  refine (runsToM_sampleE hξ).bind ?_
  refine h.bind ?_
  exact runsToM_ret _ _

/-- `publicInputPhase`'s run over the model (`runsTo_publicInputPhase`). -/
theorem runsToM_publicInputPhase (layout : Layout) (publicInput : Digest) {cv cr : Digest}
    (hr : sqCvM M cv = some cr) :
    RunsToM M (publicInputPhase layout publicInput) cv []
      (piClaims layout publicInput (challengeOf cr)) cr := by
  refine RunsToM.of_eq (xs := [] ++ []) ?_ rfl rfl rfl
  unfold publicInputPhase
  refine (runsToM_sampleE hr).bind ?_
  exact runsToM_ret _ _

/-- **`tablesSeg`'s run over the model**, from its three phases' (`runsTo_tablesSeg`). -/
theorem runsToM_tablesSeg {ev : Evaluations} {layout : Layout} {publicInput : Digest}
    {alphas : List E} {beta : E} {point treeValues : List E} {cv cv1 cv2 cr : Digest}
    {xs ys : List E} {bus : BusResult} {tc : List ColumnClaim}
    (h1 : RunsToM M (busRest ev layout alphas beta point treeValues) cv xs bus cv1)
    (h2 : RunsToM M (tablePhase layout bus) cv1 ys tc cv2) (hr : sqCvM M cv2 = some cr) :
    RunsToM M (tablesSeg ev layout publicInput alphas beta point treeValues) cv (xs ++ ys)
      (bus, tc ++ piClaims layout publicInput (challengeOf cr)) cr := by
  refine RunsToM.of_eq (xs := xs ++ (ys ++ ([] ++ []))) ?_ (by simp) rfl rfl
  unfold tablesSeg
  refine h1.bind ?_
  refine h2.bind ?_
  refine (runsToM_publicInputPhase layout publicInput hr).bind ?_
  exact runsToM_ret _ _

end
end LeanVM.Guest.B1.VerifySub
