module

public import LeanVM.Guest.Fast.SphincsTables
public import LeanVM.Guest.Fast.Numbers
public import LeanVM.Guest.B1.Sig.SphincsTail
public import LeanVM.Guest.B1.Sig.SphincsCoords

/-!
# leanSPHINCS's tables, checked

The literal tables of `Fast/SphincsTables.lean` are the template generators' numbers, by kernel
evaluation: the counter's cell, the encoding's base and the leaf's (`sStatic`), the codeword's
selector cells (`selN 3`) and the tree's path bases, the chain starts' tables (`offTab 3`), the
forest keys' chain cells (`fkOffN`), and each coordinate's positions (`coordCheck`: its bases from
`cSt`, `coordS0`, `coordS1`, `subE`, its fold outputs those of `subFd` and `coordFd`).
-/

namespace LeanVM.Guest.Fast

open LeanVM.Guest.Core LeanVM.Guest.B1.Sig

@[expose] public section

theorem sStatic : sFb.2.1 = 412448 ∧ sEnc.2.1 = 412503 ∧ sLeaf.2.1 = 437917 := by
  decide +kernel

theorem sSel_eq : sSel = (List.range 22).map (selN 3 412513) := by decide +kernel

theorem sPath_eq : sPath = (List.range 26).map fun l ↦ mBase sNodeOf 0 l 437917 := by decide +kernel

theorem sTabs : WotsTabs 3 sFirst sRest sLast :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem fkOff_eq : fkOff = (List.range 256).map fun t ↦ (List.range 6).map (fkOffN t) := by
  decide +kernel

/-- Coordinate `c`'s positions are `r`'s. -/
def coordCheck (c : ℕ) (r : SCoord) : Bool :=
  let enc := (cSt c).1
  let bound := (cSt c).2.1
  let s0 := coordS0 c enc bound r.b
  let s1 := (coordS1 c enc bound r.b).2.1
  (cSt c).2.2 == r.b && (subE c 0 enc (r.b + 10)).2.2 == r.f0 &&
    (subFd c 0 enc (r.b + 10)).2.2.2.1 == .n r.p00 &&
    (subFd c 0 enc (r.b + 10)).2.2.1 == .n r.p01 &&
    s0.2.1 == r.s1 && (subE c 1 (some s0.2.2.1) r.s1).2.2 == r.f1 &&
    (subFd c 1 (some s0.2.2.1) r.s1).2.2.2.1 == .n r.p10 &&
    (subFd c 1 (some s0.2.2.1) r.s1).2.2.1 == .n r.p11 &&
    s1 + 18 == r.top && (coordFd c r.b s1).2.2.2.1 == .n r.q0 && (coordFd c r.b s1).2.2.1 == .n r.q1

theorem sCoordTab_ok :
    ((List.range 8).all fun c ↦ coordCheck c (sCoordTab.getD c sCoord0)) = true := by
  decide +kernel

end
end LeanVM.Guest.Fast
