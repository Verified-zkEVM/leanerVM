/-
  LeanVM.Guest.B1.Terminal.TermFacts

  `check_opening_terminal`'s body, checked by the kernel for its completeness: its evaluation
  pattern, its stores, its buffers, its calls.
-/

module

public import LeanVM.Guest.B1.Terminal.Holds
public import LeanVM.Guest.B1.Fwd.Canon
public import LeanVM.Guest.B1.Tables.FlatAt

/-!
# `check_opening_terminal`'s body, for completeness

`termPre`, the body before its `ret` (`term_body'`): the head, the selectors, the claims' blocks
and the tail before its `ret`. By kernel evaluation: it defines its values in order (`term_chk`,
`2009` values), its only stores are the public input's chain's first two words (`term_stores`), it
is flat, takes no address, allocates its four buffers (`term_allocs`: the prefix chains at `zeta`
and `chi`, the public input's chain, the outputs' chain) and makes its 105 calls in order
(`term_callSF`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd

@[expose] public section

/-- The tail before its `ret`. -/
def termTailPre : List Stmt := (termTailT 1990).dropLast

/-- The claims' blocks. -/
def termClaims : List Stmt := (claimsT (List.range 165) claimsStart 16).1

/-- **`check_opening_terminal`'s statements before its `ret`.** -/
def termPre : List Stmt := termHeadT ++ selsT ++ termClaims ++ termTailPre

theorem termTail_split : termTailT 1990 = termTailPre ++ [.ret []] := by
  simp only [termTailPre, termTailT]; rfl

theorem termT_split : termT = termPre ++ [.ret []] := by
  rw [termT, show (claimsT (List.range 165) claimsStart 16).2.1 = 1990 by rw [claimsT_end],
    termTail_split, termPre, termClaims]
  simp only [List.append_assoc]

theorem term_body' : Data.core17.body = termPre ++ [.ret []] := by rw [term_body, termT_split]

theorem term_params : Data.core17.params = (List.range 19).map Core.V.n := rfl

theorem term_chk : chk 19 termT = some 2009 := by decide +kernel

theorem term_stores : storesOf 19 termT =
    [.load (.n 26) (.n 25) 0, .load (.n 28) (.n 25) 1] := by decide +kernel

theorem term_flat : termPre.all Stmt.flat = true := by decide +kernel

theorem term_addrs : termPre.filterMap Main.Stmt.addrS = [] := by decide +kernel

theorem term_allocs : termPre.filterMap Main.Stmt.allocSz =
    [(.n 19, .inl 35), (.n 21, .inl 35), (.n 25, .inl 35), (.n 1993, .inl 41)] := by decide +kernel

theorem term_not_loop : coreProgram.loop "check_opening_terminal" = false := by decide +kernel

/-! ## The calls -/

/-- No dispatch. -/
def noDispB : Stmt → Bool
  | .dispatch .. => false
  | _ => true

theorem callSF_of_noDisp (σ : Val) {l : List Stmt} (h : l.all noDispB = true) :
    l.filterMap (Stmt.callSF σ) = l.filterMap Main.Stmt.callS :=
  List.filterMap_congr fun s hs => by
    have := List.all_eq_true.mp h s hs
    cases s <;> simp_all [Stmt.callSF, noDispB]

theorem head_noDisp : termHeadT.all noDispB = true := by decide +kernel

theorem claims_noDisp : termClaims.all noDispB = true := by decide +kernel

theorem tail_noDisp : termTailPre.all noDispB = true := by decide +kernel

theorem head_callS : termHeadT.filterMap Main.Stmt.callS =
    [(none, "eq_prefix_chain", [.n 19, .n 20, .n 0, .n 15, .n 3], []),
      (none, "eq_prefix_chain", [.n 21, .n 22, .n 1, .n 15, .n 4], []),
      (some (.n 30), "__loop15", [.n 31, .n 5, .n 25, .n 15], []),
      (none, "selector_tables", [.n 14, .n 15], [.n 34, .n 35])] := by decide +kernel

theorem claims_callS : termClaims.filterMap Main.Stmt.callS = [] := by decide +kernel

theorem tail_callS : termTailPre.filterMap Main.Stmt.callS =
    [(none, "eq_prefix_chain", [.n 1993, .n 1994, .n 12, .n 15, .n 1996], []),
      (none, "ring_switch_weight", [.n 1998, .n 15, .n 13, .n 2000], [.n 2001])] := by
  decide +kernel

/-- Committed column `c`'s selector's call. -/
noncomputable def selCall (σ : Val) (c : ℕ) : Option V × String × List V × List V :=
  (none, colSelNames.getD (logG (σ (.n (37 + 3 * c)))) "", [.n (36 + 3 * c), .n 34, .n 35],
    [.n (selV c)])

theorem sels_callSF (σ : Val) :
    selsT.filterMap (Stmt.callSF σ) = (List.range Tables.nCommittedCols).map (selCall σ) := by
  rw [selsT, List.filterMap_flatMap,
    show (fun c => (selBlockT c).filterMap (Stmt.callSF σ)) = fun c => [selCall σ c] from
      funext fun _ => rfl]
  generalize List.range Tables.nCommittedCols = l
  induction l with
  | nil => rfl
  | cons c l ih => simp only [List.flatMap_cons, List.map_cons, ih, List.singleton_append]

/-- **The calls, in order.** -/
theorem term_callSF (σ : Val) : termPre.filterMap (Stmt.callSF σ) =
    [(none, "eq_prefix_chain", [.n 19, .n 20, .n 0, .n 15, .n 3], []),
      (none, "eq_prefix_chain", [.n 21, .n 22, .n 1, .n 15, .n 4], []),
      (some (.n 30), "__loop15", [.n 31, .n 5, .n 25, .n 15], []),
      (none, "selector_tables", [.n 14, .n 15], [.n 34, .n 35])] ++
    (List.range Tables.nCommittedCols).map (selCall σ) ++
    [(none, "eq_prefix_chain", [.n 1993, .n 1994, .n 12, .n 15, .n 1996], []),
      (none, "ring_switch_weight", [.n 1998, .n 15, .n 13, .n 2000], [.n 2001])] := by
  rw [termPre, List.filterMap_append, List.filterMap_append, List.filterMap_append,
    callSF_of_noDisp σ head_noDisp, head_callS, sels_callSF, callSF_of_noDisp σ claims_noDisp,
    claims_callS, callSF_of_noDisp σ tail_noDisp, tail_callS, List.append_nil]

end
end LeanVM.Guest.B1.VerifySub
