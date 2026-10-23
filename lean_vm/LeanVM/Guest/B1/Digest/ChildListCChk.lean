/-
  LeanVM.Guest.B1.Digest.ChildListCChk

  `child_claim_list_digest`'s branches and `__loop17`, evaluated (by kernel evaluation), for its
  completeness.
-/

module

public import LeanVM.Guest.B1.Digest.ChildList
public import LeanVM.Guest.B1.Digest.ClaimListCChk
public import LeanVM.Guest.B1.Digest.ChainFilter

/-!
# `child_claim_list_digest`, evaluated

A claim record (`ChildList`), evaluated: its slot hinted (`isWitO`), its range check forward
against `limit · g⁻¹` (`isLimK`), its mark `marks · E(2^j)` (`markC`) stored at
`cover · origin · o`, its four cells read at `entries · o^4` (`recC`), the products by the pure
atoms (`Fwd.pureB`). `recSide`: an atom with a side condition is one of these. `l17cOk`,
`cccOk k`, `ccBrOk`: `__loop17`, `child_claim_list_last__L{k}` and the two branches of
`child_claim_list_digest` evaluate in order, their side atoms the records', the state's and the
chain's.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1.Fwd

@[expose] public section

/-- `o`'s witness hint. -/
def isWitO (o : V) : Atom → Bool
  | .hint (.witness _ (.stack [v])) => decide (v = o)
  | _ => false

/-- `k = limit · g⁻¹`, by the pure atoms `F`. -/
def isLimK (F : List Atom) (P : ClaimVs) (k : V) : Bool :=
  match mulOf F k with
  | some (l, gi) => decide (l = P.limit) && F.any (isConstAt gi 9223372036854775821 0)
  | none => false

/-- Claim `j`'s mark is `marks · E(2^j)`, by the pure atoms `F`. -/
def markC (F : List Atom) (P : ClaimVs) (j : ℕ) (mark : V) : Bool :=
  if j = 0 then decide (mark = P.marks) else
    match mulOf F mark with
    | some (m, c) => decide (m = P.marks) && F.any (isConstAt c (2 ^ j) 0)
    | none => false

/-- Claim `j`'s cell `c`, read (not stored) through `entries · o^4`. -/
def isCellRead (F S : List Atom) (P : ClaimVs) (o0 j c : ℕ) : Atom → Bool
  | .load d p off => decide (d = .n (ccCell o0 j c)) && decide (off = c) &&
      (monoOf F 40 p).isPerm (P.entries :: List.replicate 4 (ccOV o0 j)) &&
      !decide (Atom.load d p off ∈ S)
  | _ => false

/-- **Claim `j`'s record, evaluated.** -/
def recC (A F S : List Atom) (P : ClaimVs) (o0 j : ℕ) : Bool :=
  A.any (isWitO (ccOV o0 j)) && markC F P j (ccMark o0 P.marks j) &&
    (List.range 4).all fun c => A.any (isCellRead F S P o0 j c)

/-- The side atoms of `K` records: a forward range check of a slot against `limit · g⁻¹`, a store
of a mark at `cover · origin · o`, a read at `entries · o^4`. -/
def recSide (F : List Atom) (P : ClaimVs) (o0 K : ℕ) (S : List Atom) : Atom → Bool
  | .rangeCheck x y _ _ k => decide (k.idx < y.idx) && isLimK F P k &&
      (List.range K).any fun j => decide (x = ccOV o0 j)
  | .load d p off =>
    if decide (Atom.load d p off ∈ S) then
      decide (off = 0) && (List.range K).any fun j =>
        decide (d = ccMark o0 P.marks j) && (monoOf F 40 p).isPerm [P.cover, P.origin, ccOV o0 j]
    else
      decide (off < 4) && (List.range K).any fun j =>
        (monoOf F 40 p).isPerm (P.entries :: List.replicate 4 (ccOV o0 j))
  | _ => false

/-- The canonical values of `K` records' cells and the state `st`. -/
def ccA (st : List V) (o0 K : ℕ) : List ℕ :=
  st.map V.idx ++ (List.range K).flatMap fun j => (List.range 4).map (ccCell o0 j)

/-- **`child_claim_list_last__L{k}`, evaluated.** -/
def cccOk (k : ℕ) (f : Fn) : Bool :=
  let S := storesOf 6 f.body
  (chk 6 f.body).isSome &&
  match splitBody f.body with
  | some (A, _) =>
    let F := A.filter pureB
    canonChk (ccA (cclSt k) 6 k) (A.filter fun a => decide (a ∉ S)) &&
      A.all (fun a => !needsSide a || (isLoadBelow 0 13 a && decide (a ∉ S)) ||
        recSide F cclP 6 k S a) &&
      (List.range k).all (fun j => recC A F S cclP 6 j)
  | none => false

/-- **`__loop17`, evaluated.** -/
def l17cOk (fn : Fn) : Bool :=
  let A := loopAtoms fn
  let S := storesOf 8 fn.body
  let F := A.filter pureB
  let G := A.filter fun a => decide (a ∉ S)
  loopShapeF fn "__loop17" && (chk 8 fn.body).isSome && (loopPre fn).all isAtomS &&
  atomsEqbL (atomsIn (loopPre fn)) A && S.all isLoadB &&
  canonChk (ccA l17St 20 17) G &&
  A.all (fun a => !needsSide a || (isLoadBelow 13 13 a && decide (a ∉ S)) ||
    (List.range 13).any (fun c =>
      atomEqb a (.load ((l17Spec A).outV ((l17Spec A).nb - 1) c) (.n 13) (13 + c))) ||
    recSide F l17P 20 17 S a) &&
  (List.range 17).all (fun j => recC A F S l17P 20 j) &&
  stLoadsOk G (.n 13) l17St 0 &&
  monoIs F (.n 13) (.n 2) (.n 0) 13 && monoIs F (.n 19) (.n 5) (.n 0) 17

/-- The nonempty branch but its two final copies. -/
noncomputable def ccElsePre : List Stmt := cc24Else.dropLast.dropLast

/-- The head of `child_claim_list_digest`'s body. -/
def ccHead : List Stmt := [.atom (.const (.n 6) (word 1 0 0)), .atom (.add (.n 7) (.n 5) (.n 6))]

/-- The final copies of `child_claim_list_digest`. -/
def ccTail : List Stmt := [.atom (.copy (.n 67) (.n 14)), .atom (.copy (.n 68) (.n 15))]

/-- The empty list's run, evaluated. -/
noncomputable def ccZEval : List Stmt :=
  ccHead ++ cc24Zero ++ fillH ((chk 6 (ccHead ++ cc24Zero)).getD 0) 67 ++ ccTail

/-- The nonempty list's run, evaluated: the empty branch's values hinted (the digest at `.n 14`,
`.n 15`). -/
noncomputable def ccEEval : List Stmt := ccHead ++ fillH 8 27 ++ ccElsePre ++ ccTail

/-- **`child_claim_list_digest`'s branches, evaluated.** -/
noncomputable def ccBrOk : Bool :=
  let SE := storesOf 6 ccEEval
  stmtsEqb cc24Else (ccElsePre ++ [.atom (.copy (.n 14) (.n 65)), .atom (.copy (.n 15) (.n 66))]) &&
  (chk 6 ccEEval).isSome &&
  SE.all (fun a => (List.range 13).any fun c => atomEqb a (.load (.n (37 + c)) (.n 36) c)) &&
  (atomsIn ccEEval).all (fun a => !needsSide a || decide (a ∈ SE)) &&
  canonChk [] ((atomsIn ccEEval).filter fun a => decide (a ∉ SE)) &&
  ccElsePre.all (fun s => isAtomS s || stmtEqb s (.call "list_split" [.n 5] [.n 27, .n 28]) ||
    stmtEqb s (.callIf (.n 51) "__loop17" [.n 52, .n 27, .n 36, .n 0, .n 1, .n 2, .n 3, .n 4]) ||
    stmtEqb s (.dispatch (.n 28) cclNames [.n 58, .n 0, .n 1, .n 64, .n 3, .n 4] [.n 65, .n 66])) &&
  ccElsePre.any (stmtEqb · (.call "list_split" [.n 5] [.n 27, .n 28])) &&
  ccElsePre.any (stmtEqb · (.callIf (.n 51) "__loop17"
    [.n 52, .n 27, .n 36, .n 0, .n 1, .n 2, .n 3, .n 4])) &&
  ccElsePre.any (stmtEqb · (.dispatch (.n 28) cclNames [.n 58, .n 0, .n 1, .n 64, .n 3, .n 4]
    [.n 65, .n 66])) &&
  (List.range 13).all (fun c => (atomsIn ccElsePre).any (isConstAt (.n (37 + c)) 0 0)) &&
  (atomsIn ccElsePre).any (fun a => match a with
    | .hint (.allocDyn d _) => decide (d = .n 36)
    | _ => false) &&
  (chk 6 ccZEval).isSome && (storesOf 6 ccZEval).isEmpty && canonChk [] (atomsIn ccZEval) &&
  (atomsIn ccZEval).all (fun a => !needsSide a) && cc24Zero.all isAtomS

set_option maxRecDepth 100000 in
theorem ccbr_ok : ccBrOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l17c_ok : l17cOk (coreProgram.getD 341 default) = true := by decide +kernel

end
end LeanVM.Guest.B1.Digest
