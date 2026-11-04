/-
  LeanVM.Guest.B1.VerifySub.Back

  `verify_sub` after its three calls, assembled: the ring map, `c_table`, the batching and the
  tail.
-/

module

public import LeanVM.Guest.B1.VerifySub.SoundLib
public import LeanVM.Guest.B1.VerifySub.Lam
public import LeanVM.Guest.B1.VerifySub.Proof

/-!
# The back of `verify_sub`

`vs_back`: from the zero cells and the pooled claims, the statements after the calls (G:3246-3318)
give the ring map's challenges and their coefficients, the batching challenge, its powers and
the target, and the tail's facts (`vsTailT_holds`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- The ring map's five squeezed challenges. -/
def vsChs (σ : Val) : List E := [σ (.n 685), σ (.n 705), σ (.n 725), σ (.n 745), σ (.n 765)]

/-- The claims the opening batches, off the output lanes. -/
def notLanes (claims : List ColumnClaim) : List ColumnClaim :=
  claims.filter fun c ↦ c.column ∉ keccakOutputColumns

/-- **The back of `verify_sub`.** -/
theorem vs_back (h10 : σ (.n 8) = 0) (h11 : σ (.n 9) = 0) (h12 : σ (.n 10) = 0)
    (h13 : σ (.n 11) = 0) {claims : List ColumnClaim}
    (hcol : claims.map (·.column) = Tables.claimColumns)
    (hval : ReadsAt rd (σ (.n 6)) (claims.map (·.value)))
    (h : Stmt.HoldsList C rd σ (vsMapsT ++ (vsCtabT ++ (vsLamT ++ vsTailT))) False kret) :
    -- the ring map
    (⟨[σ (.n 659), σ (.n 660), σ (.n 661), σ (.n 662), σ (.n 663)], []⟩ : Fs).squeezeN 5 =
      (vsChs σ, ⟨[σ (.n 754), σ (.n 755), σ (.n 756), σ (.n 757), σ (.n 758)], []⟩) ∧
    ReadsAt rd (σ (.n 664)) (σ (.n 658) :: vsChs σ) ∧
    ReadsAt rd (σ (.n 665)) (ringCoefficients (σ (.n 658) :: vsChs σ)) ∧
    C "ring_switch_target" [σ (.n 648), σ (.n 664)] [σ (.n 1091)] ∧
    -- the batching
    (⟨[σ (.n 754), σ (.n 755), σ (.n 756), σ (.n 757), σ (.n 758)], []⟩ : Fs).squeeze =
      (σ (.n 1111), ⟨[σ (.n 1100), σ (.n 1101), σ (.n 1102), σ (.n 1103), σ (.n 1104)], []⟩) ∧
    (∀ j < Tables.nClaims, Tables.claimColumns.getD j 0 ∉ keccakOutputColumns →
      LoadHolds rd (σ (.n XLAMPOOL)) j (σ (.n 1111) ^ (1 + poolRank j))) ∧
    σ (.n 1671) = σ (.n 1111) ^ (1 + poolRank Tables.nClaims) ∧
    σ (.n 1673) = dot (powers (σ (.n 1111)) ((notLanes claims).length + 2))
      (σ (.n 1091) :: ((notLanes claims).map (·.value) ++ [σ (.n 657)])) ∧
    -- the tail
    C "certify_placement" [σ (.n 139), σ (.n 4)] [σ (.n 1674), σ (.n 1675), σ (.n XCOLKAPPAS)] ∧
    C "log2_ceil_in_the_exponent__L15_L34" [σ (.n 1674), σ (.n XGLP), σ (.n 4)] [σ (.n 1676)] ∧
    σ (.n 1678) = σ (.n 1676) * word 8198552432976855044 0 0 ∧
    (LoadHolds rd (σ (.n 1678)) 0 (σ (.n 1681)) ∧ word 64 0 0 = σ (.n 1678) * σ (.n 1680) ∧
      LoadHolds rd (σ (.n 1680)) 0 (σ (.n 1682))) ∧
    σ (.n 1687) = σ (.n 1678) * (σ (.n 122) * σ (.n 122) * σ (.n 122) *
      (σ (.n 122) * σ (.n 122) * σ (.n 122)) * σ (.n 122)) ∧
    (LoadHolds rd (σ (.n 1687)) 0 (σ (.n 1690)) ∧ word 134217728 0 0 = σ (.n 1687) * σ (.n 1689) ∧
      LoadHolds rd (σ (.n 1689)) 0 (σ (.n 1691))) ∧
    (∃ (j : ℕ) (hj : j < vsOpenNames.length), σ (.n 1687) = ofK (addressOfIndex j) ∧
      C vsOpenNames[j] (vsOsArgs σ) (vsOsRets σ)) ∧
    C "check_opening_terminal" [σ (.n 310), σ (.n 635), σ (.n 644), σ (.n 309), σ (.n 642),
      σ (.n 128), σ (.n 646), σ (.n XCPLEN), σ (.n 1671), σ (.n XLAMPOOL), σ (.n 1675), σ (.n XCOLKAPPAS),
      σ (.n 647), σ (.n 665), σ (.n 1693), σ (.n 1694), σ (.n 1695), σ (.n 1696), σ (.n 1692)] [] ∧
    (∀ k < 19, ∃ v, LoadHolds rd (σ (.n 310)) k v ∧ LoadHolds rd (σ (.n 5)) k v) ∧
    (∀ k < 4, ∃ v, LoadHolds rd (σ (.n 346)) k v ∧ LoadHolds rd (σ (.n 5)) (19 + k) v) ∧
    LoadHolds rd (σ (.n 5)) 23 (σ (.n 643)) ∧ kret [] := by
  rw [holdsList_append, holdsList_append, holdsList_append] at h
  obtain ⟨hm, hmR, h⟩ := vsMapsT_holds h10 h11 h12 h13 h
  obtain ⟨hct, hrst, h⟩ := vsCtabT_holds (chs := σ (.n 658) :: vsChs σ) rfl hmR h
  obtain ⟨hlam, hpw, h1884, h1886, h⟩ := vsLamT_holds h10 h11 h12 h13 hcol hval h
  exact ⟨hm, hmR, hct, hrst, hlam, hpw, h1884, h1886, vsTailT_holds h⟩

end
end LeanVM.Guest.B1.VerifySub
