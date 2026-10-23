/-
  LeanVM.Guest.B1.Sig.SphincsCoordComplete

  A coordinate of `verify_sig_lean_sphincs`'s forest completes: its super-child hinted and range
  checked, its leaf's address, its two sub-trees, the super-child's hash, the top fold's dispatch
  and the bound updated.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsSubComplete

/-!
# A coordinate, complete

* `CoordH`: a coordinate's hints: its super-child `s`, the top fold's siblings (the other level-3
  node last) and its two sub-trees';
* `CoordPost`: what a coordinate's valuation holds; `sCoord_complete`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

attribute [local irreducible] fkArms foldArms sSubtree

variable {C : CallRel} {rd : Reader}

/-- A coordinate's hints. -/
structure CoordH where
  s : Nat
  sibs : Nat → E
  sub0 : SubH
  sub1 : SubH

def CoordH.OK (h : CoordH) : Prop := h.s < 16 ∧ (∀ l, IsCanonical128 (h.sibs l)) ∧ h.sub0.OK ∧ h.sub1.OK

/-- The mark a coordinate's top fold checks, its leaf's address offset. -/
def coordMark (c s : Nat) : E := word (c * hiMul + s * 2 ^ 35) 0 0

/-- The encoding's terms of a coordinate's hints. -/
def hEnc (c : Nat) (h : CoordH) : E := fkWeight h.sub0.t (2 * c) + fkWeight h.sub1.t (2 * c + 1)

/-- The bound's terms of a coordinate's hints. -/
def hBound (c : Nat) (h : CoordH) : E :=
  cbMul h.sub0.a (58 + 3 * (2 * c)) + cbMul h.sub1.a (58 + 3 * (2 * c + 1)) + cbMul h.s (26 + 4 * c)

theorem coordFd_eq (c b f : Nat) : coordFd c b f = foldArms (.n (b + 6)) coordAdr 4 (.n (f + 5)) (.n (b + 1))
    (coordMark c) (fun s => cbMul s (26 + 4 * c)) (f + 18) := rfl

theorem coordAdr_ok (s : Nat) : AdrOK (coordAdr s) (4 - 1) := by
  intro l _ a h
  simp [coordAdr] at h

/-- What a coordinate's valuation holds. -/
def CoordPost (encIn boundIn : E) (c : Nat) (enc : Option V) (bound : V) (b : Nat) (h : CoordH)
    (σ : Val) : Prop :=
  σ (.n b) = ofK (gpow h.s) ∧ σ (.n (b + 1)) = coordMark c h.s ∧
    SubPost encIn boundIn c 0 enc (b + 10) h.sub0 σ ∧
    SubPost (encIn + fkWeight h.sub0.t (2 * c)) (boundIn + cbMul h.sub0.a (58 + 3 * (2 * c))) c 1
      (some (coordS0 c enc bound b).2.2.1) (coordS0 c enc bound b).2.1 h.sub1 σ ∧
    (∀ l < 3, σ (.n (flBase (coordAdr h.s) 0 l (foAB (.n (b + 6)) coordAdr 4
      (.n ((coordS1 c enc bound b).2.1 + 5)) (.n (b + 1)) (coordMark c) (fun s => cbMul s (26 + 4 * c))
      ((coordS1 c enc bound b).2.1 + 18) h.s))) = h.sibs l) ∧
    σ (if h.s / 2 ^ 3 = 0 then (coordFd c b (coordS1 c enc bound b).2.1).2.2.2.1
      else (coordFd c b (coordS1 c enc bound b).2.1).2.2.1) = h.sibs 3 ∧
    IsCanonical128 (σ (coordFd c b (coordS1 c enc bound b).2.1).2.2.1) ∧
    IsCanonical128 (σ (coordFd c b (coordS1 c enc bound b).2.1).2.2.2.1) ∧
    σ (sCoord c enc bound b).2.2.1 = encIn + hEnc c h ∧
    σ (sCoord c enc bound b).2.2.2.1 = boundIn + hBound c h

theorem coordS0_eq (c : Nat) (enc : Option V) (bound : V) (b : Nat) :
    coordS0 c enc bound b = sSubtree c 0 (.n (b + 6)) enc bound (b + 10) := rfl

theorem coordS1_eq (c : Nat) (enc : Option V) (bound : V) (b : Nat) :
    coordS1 c enc bound b = sSubtree c 1 (.n (b + 6)) (some (coordS0 c enc bound b).2.2.1)
      (coordS0 c enc bound b).2.2.2.1 (coordS0 c enc bound b).2.1 := rfl

theorem sCoord_split (c : Nat) (enc : Option V) (bound : V) (b : Nat) :
    (sCoord c enc bound b).1 =
      [hintW "sp_leaves" [.n b, .n (b + 1)]] ++ (rangeS (.n b) g15W (b + 2) ++
        ([addS (.n (b + 6)) (sNode 0) (.n (b + 1)), copyS (.n (b + 7)) sPP, cst (b + 8) (word (tw 18) 0 0),
          addS (.n (b + 9)) (.n (b + 6)) (.n (b + 8))] ++
        ((coordS0 c enc bound b).1 ++ ((coordS1 c enc bound b).1 ++
        ([copyS (.n (coordS1 c enc bound b).2.1) (coordS1 c enc bound b).2.2.2.2.1,
          copyS (.n ((coordS1 c enc bound b).2.1 + 1)) (coordS1 c enc bound b).2.2.2.2.2,
          cst ((coordS1 c enc bound b).2.1 + 2) (word 1 0 0),
          cst ((coordS1 c enc bound b).2.1 + 3) (word 0 0 0),
          cst ((coordS1 c enc bound b).2.1 + 4) (word (2 ^ 63) 0 0)] ++
        ([kecS [.n (b + 7), .n (b + 9), (coordS0 c enc bound b).2.2.2.2.1,
            (coordS0 c enc bound b).2.2.2.2.2, .n (coordS1 c enc bound b).2.1,
            .n ((coordS1 c enc bound b).2.1 + 1), .n ((coordS1 c enc bound b).2.1 + 2),
            .n ((coordS1 c enc bound b).2.1 + 3), .n ((coordS1 c enc bound b).2.1 + 4),
            .n (sPad + 1), .n (sPad + 2), .n (sPad + 3), .n (sPad + 4)]
            (runV ((coordS1 c enc bound b).2.1 + 5) 13) false false] ++
        ([.match_ (.n b) (coordFd c b (coordS1 c enc bound b).2.1).1] ++
          [addS (if c + 1 = 8 then .n 18 else .n (coordFd c b (coordS1 c enc bound b).2.1).2.1)
            (coordS1 c enc bound b).2.2.2.1 (coordFd c b (coordS1 c enc bound b).2.1).2.2.2.2]))))))) := by
  rw [sCoord_eq]
  simp

end
end LeanVM.Guest.B1.Sig
