/-
  LeanVM.Guest.B1.Digest.ClaimListCChk

  `claim_list_digest`'s branches and `__loop15`, evaluated (by kernel evaluation), for its
  completeness.
-/

module

public import LeanVM.Guest.B1.Digest.ClaimList
public import LeanVM.Guest.B1.Digest.LoopComplete
public import LeanVM.Guest.B1.Fwd.Canon

/-!
# `claim_list_digest`, evaluated

`l16cOk`: `__loop15`'s block evaluates in order (`Fwd.chk`), its atoms are `loopAtoms`, its stores
write the chain's last state at `.n 9` from offset `13`, the chain's inputs are canonical from the
state and the cells it loads, its other side conditions are those loads. `clBrOk`: each branch of
`claim_list_digest`, its values padded by hints up to the final copies (`fillH`), evaluates in
order; the nonempty branch's stores are the zero state's, its other atoms need nothing.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1.Fwd

@[expose] public section

/-- A load through `.n p` at an offset below `bound`. -/
def isLoadBelow (p bound : ℕ) : Atom → Bool
  | .load _ q o => decide (q = .n p) && decide (o < bound)
  | _ => false

/-- A statement is an atom. -/
def isAtomS : Stmt → Bool
  | .atom _ => true
  | _ => false

/-- Atom lists compared, words limb by limb. -/
def atomsEqbL : List Atom → List Atom → Bool
  | [], [] => true
  | x :: xs, y :: ys => atomEqb x y && atomsEqbL xs ys
  | _, _ => false

theorem atomsEqbL_sound : ∀ {xs ys : List Atom}, atomsEqbL xs ys = true → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [atomsEqbL] at h
  | _ :: _, [], h => by simp [atomsEqbL] at h
  | x :: xs, y :: ys, h => by
    simp only [atomsEqbL, Bool.and_eq_true] at h
    rw [atomEqb_sound h.1, atomsEqbL_sound h.2]

/-- Hints defining the values `.n c`, …, `.n (m - 1)`. -/
def fillH (c m : ℕ) : List Stmt := (List.range (m - c)).map fun i => .atom (.hint (.alloc (.n (c + i)) 0))

/-- **`claim_list_last__L{k}`, evaluated**: in order, no store, the chain's inputs canonical from
the state and the cells it loads, its side conditions those loads. -/
def clcOk (k : ℕ) (f : Fn) : Bool :=
  (chk 2 f.body).isSome && (storesOf 2 f.body).isEmpty &&
  match splitBody f.body with
  | some (atoms, _) =>
    canonChk ((clSt k).map V.idx ++ (List.range (4 * k)).map (· + 2)) atoms &&
      atoms.all (fun a => !needsSide a || isLoadBelow 0 13 a || isLoadBelow 1 (4 * k) a)
  | none => false

/-- **`__loop15`, evaluated**: in order, its atoms `loopAtoms`, its stores the next state's cells,
the chain's inputs canonical from the state and the cells it loads, its offsets and pointers
products of pure atoms. -/
def l16cOk (fn : Fn) : Bool :=
  let A := loopAtoms fn
  let S := storesOf 4 fn.body
  let F := A.filter fun a => decide (a ∉ S)
  loopShapeF fn "__loop15" && (chk 4 fn.body).isSome && (loopPre fn).all isAtomS &&
  atomsEqbL (atomsIn (loopPre fn)) A &&
  S.all (fun a => (List.range 13).any fun c =>
    atomEqb a (.load ((l16Spec A).outV ((l16Spec A).nb - 1) c) (.n 9) (13 + c))) &&
  canonChk (l16St.map V.idx ++ (List.range 68).map (· + 18)) F &&
  A.all (fun a => !needsSide a || decide (a ∈ S) || isLoadBelow 9 13 a || isLoadBelow 17 68 a) &&
  stLoadsOk F (.n 9) l16St 0 &&
  monoIs (A.filter pureB) (.n 9) (.n 2) (.n 0) 13 && monoIs (A.filter pureB) (.n 17) (.n 3) (.n 0) 68

/-- The nonempty branch but its two final copies. -/
noncomputable def clElsePre : List Stmt := cl23Else.dropLast.dropLast

/-- The head of `claim_list_digest`'s body. -/
def clHead : List Stmt := [.atom (.const (.n 2) (word 1 0 0)), .atom (.add (.n 3) (.n 1) (.n 2))]

/-- The final copies of `claim_list_digest`. -/
def clTail : List Stmt := [.atom (.copy (.n 65) (.n 10)), .atom (.copy (.n 66) (.n 11))]

/-- The empty list's run, evaluated. -/
noncomputable def clZEval : List Stmt :=
  clHead ++ cl23Zero ++ fillH ((chk 2 (clHead ++ cl23Zero)).getD 0) 65 ++ clTail

/-- The nonempty list's run, evaluated: the empty branch's values hinted (the digest at `.n 10`,
`.n 11`). -/
noncomputable def clEEval : List Stmt := clHead ++ fillH 4 23 ++ clElsePre ++ clTail

/-- **`claim_list_digest`'s branches, evaluated.** -/
noncomputable def clBrOk : Bool :=
  let SE := storesOf 2 clEEval
  stmtsEqb cl23Else (clElsePre ++ [.atom (.copy (.n 10) (.n 63)), .atom (.copy (.n 11) (.n 64))]) &&
  (chk 2 clEEval).isSome &&
  SE.all (fun a => (List.range 13).any fun c => atomEqb a (.load (.n (33 + c)) (.n 32) c)) &&
  (atomsIn clEEval).all (fun a => !needsSide a || decide (a ∈ SE)) &&
  canonChk [] ((atomsIn clEEval).filter fun a => decide (a ∉ SE)) &&
  clElsePre.all (fun s => isAtomS s || stmtEqb s (.call "list_split" [.n 1] [.n 23, .n 24]) ||
    stmtEqb s (.callIf (.n 47) "__loop15" [.n 48, .n 23, .n 32, .n 0]) ||
    stmtEqb s (.dispatch (.n 24) clNames [.n 54, .n 62] [.n 63, .n 64])) &&
  clElsePre.any (stmtEqb · (.call "list_split" [.n 1] [.n 23, .n 24])) &&
  clElsePre.any (stmtEqb · (.callIf (.n 47) "__loop15" [.n 48, .n 23, .n 32, .n 0])) &&
  clElsePre.any (stmtEqb · (.dispatch (.n 24) clNames [.n 54, .n 62] [.n 63, .n 64])) &&
  (List.range 13).all (fun c => (atomsIn clElsePre).any (isConstAt (.n (33 + c)) 0 0)) &&
  (atomsIn clElsePre).any (fun a => match a with
    | .hint (.allocDyn d _) => decide (d = .n 32)
    | _ => false) &&
  (chk 2 clZEval).isSome && (storesOf 2 clZEval).isEmpty && canonChk [] (atomsIn clZEval) &&
  (atomsIn clZEval).all (fun a => !needsSide a) && cl23Zero.all isAtomS

set_option maxRecDepth 100000 in
theorem clbr_ok : clBrOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l16c_ok : l16cOk (coreProgram.getD 320 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem clc_lo : ∀ k < 9, clcOk k (coreProgram.getD (324 + k) default) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem clc_hi : ∀ k < 8, clcOk (9 + k) (coreProgram.getD (333 + k) default) = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Digest
