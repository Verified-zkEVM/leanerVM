/-
  LeanVM.Guest.B1.Comp.Tables.VtLoopsC

  `verify_tables`' table sumcheck loop over a completeness model, backward.
-/

module

public import LeanVM.Guest.B1.Comp.Tables.FwdIC
public import LeanVM.Guest.B1.Comp.FiatShamir
public import LeanVM.Guest.B1.Comp.Digest.Common
public import LeanVM.Guest.B1.Tables.VerifyTablesHashM
public import LeanVM.Guest.B1.Tables.VerifyTablesCLoops

/-!
# The table sumcheck's rounds over a completeness model

`__loop79` (`VerifyTablesCLoops.lean`) under a completeness model's semantics: `loop79_stepC`, one
round backward, its `sumcheck_round4` the model's on the round's answered run
(`sumcheck_round4_comp`); `loop79_completeC`: the rounds from their answered runs
(`ZcRoundM CM.hm`, `loop79_complete` over the model).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.E2E.Complete

@[expose] public section

/-- **`__loop79`, one round, backward, over a completeness model** (`loop79_back`). -/
theorem loop79_stepC {CM : CompModel} {rd : Reader} {N rounds chi gn cprod x : E}
    (hb : ZcRoundM CM.hm rd rounds chi gn cprod x) (hK : IsInK (x * gen + N))
    (hnext : x * gen + N ≠ 0 →
      coreProgram.RelB CM.sem rd "__loop79" [x * gen, N, rounds, chi, gn, cprod] []) :
    ∃ fn, coreProgram.find? "__loop79" = some fn ∧
      fn.SemB CM.sem (coreProgram.RelB CM.sem rd) rd [x, N, rounds, chi, gn, cprod] [] := by
  obtain ⟨cv, cur, claim, c0, c2, c3, claim', rk, cv', q, c, h0, h1, h2, h3, hrd, hrun, hq, hrk,
    h4, h5, h6, h7, hc0, hc1⟩ := hb
  have hsc : coreProgram.RelB CM.sem rd "sumcheck_round4"
      [(digestScalars cv).1, (digestScalars cv).2, cur, claim]
      [(digestScalars cv').1, (digestScalars cv').2, cur * gen ^ 3, claim', rk] :=
    sumcheck_round4_comp rd _ _ ⟨cv, c0, c2, c3, claim', rk, cv', rfl, hrd, hrun, rfl⟩
  have e8 : rounds * (x * x * (x * x)) = rounds * x ^ 4 := by ring
  refine ⟨Data.core138, find_loop79, setl (Val.ofArgs [x, N, rounds, chi, gn, cprod]) 6
    [x * x, x * x * (x * x),
    rounds * (x * x * (x * x)), (digestScalars cv).1, (digestScalars cv).2, cur, claim,
    (digestScalars cv').1, (digestScalars cv').2, cur * gen ^ 3, claim', rk, wInvG, gn * wInvG, q,
    chi * q, cprod * x, c, c * rk, cprod * x, word 2 0 0, x * word 2 0 0, x * word 2 0 0 + N,
    word 2 0 0, x * word 2 0 0], by
      simp only [show Fn.params Data.core138 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5] from rfl,
        List.map_cons, List.map_nil]; b1_look, ?_⟩
  simp only [show Fn.body Data.core138 = Data.core138.body from rfl, Data.core138.body,
    Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, word_gen]
  b1_look
  simp only [true_and, and_true, e8]
  exact ⟨h0, h1, h2, h3, hsc, hq, hrk, h4, h5, h6, h7, hc0, hc1, hK, hnext⟩

/-- **`__loop79` over a completeness model**, the table sumcheck's rounds from their answered
runs (`loop79_complete`). -/
theorem loop79_completeC {CM : CompModel} {rd : Reader} {rounds chi gn cprod : E} {m : ℕ}
    (hm0 : 0 < m) (hB : ∀ j < m, ZcRoundM CM.hm rd rounds chi gn cprod (gen ^ j)) :
    coreProgram.RelB CM.sem rd "__loop79" [1, gen ^ m, rounds, chi, gn, cprod] [] := by
  have := Digest.loopB_bwd (S := CM.sem) (B := ZcRoundM CM.hm rd rounds chi gn cprod)
    (fun x hb hK hcall => loop79_stepC hb hK hcall) (k := 0) (m := m) hm0 rfl
    (fun j _ hj => hB j hj)
  rwa [pow_zero] at this

end
end LeanVM.Guest.B1.VerifySub
