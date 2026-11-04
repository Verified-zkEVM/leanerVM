/-
  LeanVM.Guest.B1.Digest.ChildListCChk

  `child_claim_list_any`'s records, frame loops (`__loop17`, `__loop18`) and
  `child_claim_list_last__L{k}`, evaluated (by kernel evaluation), for their completeness.
-/

module

public import LeanVM.Guest.B1.Digest.ChildList
public import LeanVM.Guest.B1.Digest.ClaimListCChk
public import LeanVM.Guest.B1.Digest.ChainFilter
public import LeanVM.Guest.B1.Fwd.CanonB

/-!
# `child_claim_list_any`, evaluated

A claim record (`ChildListDefs.claimOk`), evaluated: its slot hinted (`isWitO`), range-checked
forward against `last` (the record values' `P.last`), its mark `marks` (claim `0`) or the previous
claim's mark times `g` (`markC`) stored at `region · o`, its four cells read at `entries · o^4`
(`isCellRead`), the products by the pure atoms (`Fwd.pureB`). `recSide`: an atom with a side
condition is one of these. `cccOk k`: `child_claim_list_last__L{k}` evaluates in order, its side
atoms the records' and the state's. `anycOk`: a frame loop of `m` records (`anyOk`'s loop) the
same, its stores the next state at `chain · x^13` from offset `13`; its parts (`anycHead`,
`anycCanon`, `anycSide`, `anycRecs`) are kernel checks of their own.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1.Fwd

@[expose] public section

/-- `o`'s witness hint. -/
def isWitO (o : V) : Atom → Bool
  | .hint (.witness _ (.stack [v])) => decide (v = o)
  | _ => false

/-- Claim `j`'s mark: `marks` for claim `0`, else the previous claim's mark times `g` (by the pure
atoms `F`). -/
def markC (F : List Atom) (P : ClaimVs) (o0 j : ℕ) : Bool :=
  if j = 0 then true else
    match mulOf F (ccMark o0 P.marks j) with
    | some (m, c) => decide (m = ccMark o0 P.marks (j - 1)) && F.any (isConstAt c 2 0)
    | none => false

/-- Claim `j`'s cell `c`, read (not stored) through `entries · o^4`. -/
def isCellRead (F S : List Atom) (P : ClaimVs) (o0 j c : ℕ) : Atom → Bool
  | .load d p off => decide (d = .n (ccCell o0 j c)) && decide (off = c) &&
      (monoOf F 40 p).isPerm (P.entries :: List.replicate 4 (.n (ccOV o0 j))) &&
      !decide (Atom.load d p off ∈ S)
  | _ => false

/-- **Claim `j`'s record, evaluated.** -/
def recC (A F S : List Atom) (P : ClaimVs) (o0 j : ℕ) : Bool :=
  A.any (isWitO (.n (ccOV o0 j))) && markC F P o0 j &&
    (List.range 4).all fun c => A.any (isCellRead F S P o0 j c)

/-- The side atoms of `K` records: a forward range check of a slot against `last`, a store of a
mark at `region · o`, a read at `entries · o^4`. -/
def recSide (F : List Atom) (P : ClaimVs) (o0 K : ℕ) (S : List Atom) : Atom → Bool
  | .rangeCheck x y _ _ k => decide (k.idx < y.idx) && decide (k = P.last) &&
      (List.range K).any fun j => decide (x = .n (ccOV o0 j))
  | .load d p off =>
    if decide (Atom.load d p off ∈ S) then
      decide (off = 0) && (List.range K).any fun j =>
        decide (d = ccMark o0 P.marks j) && (monoOf F 40 p).isPerm [P.region, .n (ccOV o0 j)]
    else
      decide (off < 4) && (List.range K).any fun j =>
        (monoOf F 40 p).isPerm (P.entries :: List.replicate 4 (.n (ccOV o0 j)))
  | _ => false

/-- The canonical values of `K` records' cells and the state `st`. -/
def ccA (st : List V) (o0 K : ℕ) : List ℕ :=
  st.map V.idx ++ (List.range K).flatMap fun j => (List.range 4).map (ccCell o0 j)

/-- **`child_claim_list_last__L{k}`, evaluated** (`[state, entries, region, marks, last]`). -/
def cccOk (k : ℕ) (f : Fn) : Bool :=
  let S := storesOf 5 f.body
  (chk 5 f.body).isSome &&
  match splitBody f.body with
  | some (A, _) =>
    let F := A.filter pureB
    canonChk (ccA (cclSt k) 5 k) (A.filter fun a => decide (a ∉ S)) &&
      A.all (fun a => !needsSide a || (isLoadBelow 0 13 a && decide (a ∉ S)) ||
        recSide F cclP 5 k S a) &&
      (List.range k).all (fun j => recC A F S cclP 5 j) &&
      stLoadsOk (A.filter fun a => decide (a ∉ S)) (.n 0) (cclSt k) 0
  | none => false

/-- A frame loop's shape: in order, its block atoms, its stores loads. -/
def anycHead (fn : Fn) (f : String) : Bool :=
  loopShapeF fn f && (chk 7 fn.body).isSome && (loopPre fn).all isAtomS &&
    atomsEqbL (atomsIn (loopPre fn)) (loopAtoms fn) && (storesOf 7 fn.body).all isLoadB

/-- A frame loop's chain inputs, canonical from the state and the records' cells (on a mask, over
all its atoms: the stores are loads, which the walk skips, `canonGo_filter`). -/
def anycCanon (fn : Fn) (m o0 st0 : ℕ) : Bool :=
  canonGoB (maskOf (ccA (anySt st0) o0 m)) (loopAtoms fn)

/-- A frame loop's side atoms: the state's loads, the next state's stores, the records'. -/
def anycSide (fn : Fn) (m o0 mk st0 : ℕ) : Bool :=
  let A := loopAtoms fn
  let S := storesOf 7 fn.body
  A.all (fun a => !needsSide a || (isLoadBelow 12 13 a && decide (a ∉ S)) ||
    (List.range 13).any (fun c => atomEqb a
      (.load ((anySpec m o0 st0 A).outV ((anySpec m o0 st0 A).nb - 1) c) (.n 12) (13 + c))) ||
    recSide (A.filter pureB) (anyP mk) o0 m S a)

/-- A frame loop's records, its state's loads and its pointers. -/
def anycRecs (fn : Fn) (m o0 mk st0 : ℕ) : Bool :=
  let A := loopAtoms fn
  let S := storesOf 7 fn.body
  (List.range m).all (fun j => recC A (A.filter pureB) S (anyP mk) o0 j) &&
    stLoadsOk (A.filter fun a => decide (a ∉ S)) (.n 12) (anySt st0) 0 &&
    monoIs (A.filter pureB) (.n 12) (.n 2) (.n 0) 13 && monoIs (A.filter pureB) (.n mk) (.n 5) (.n 0) m

/-- **A frame loop of `m` records, evaluated** (`[x, N, chain, entries, region, base, last]`). -/
def anycOk (fn : Fn) (f : String) (m o0 mk st0 : ℕ) : Bool :=
  anycHead fn f && anycCanon fn m o0 st0 && anycSide fn m o0 mk st0 && anycRecs fn m o0 mk st0

set_option maxRecDepth 100000 in
theorem ccc_lo : ∀ k < 9, cccOk k (coreProgram.getD (352 + k) default) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ccc_hi : ∀ k < 8, cccOk (9 + k) (coreProgram.getD (361 + k) default) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem any17c_ok : anycOk (coreProgram.getD 351 default) "__loop18" 17 19 18 255 = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Digest
