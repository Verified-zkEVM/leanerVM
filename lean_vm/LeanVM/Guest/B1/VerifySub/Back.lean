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

`vs_back`: from the zero cells and the pooled claims, the statements after the calls (G:3262-3334)
give the ring map's challenges and their coefficients, the batching challenge, its powers and
the target, and the tail's facts (`vsTailT_holds`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- The ring map's five squeezed challenges. -/
def vsChs (σ : Val) : List E := [σ (.n 897), σ (.n 917), σ (.n 937), σ (.n 957), σ (.n 977)]

/-- The claims the opening batches, off the output lanes. -/
def notLanes (claims : List ColumnClaim) : List ColumnClaim :=
  claims.filter fun c ↦ c.column ∉ keccakOutputColumns

/-- **The back of `verify_sub`.** -/
theorem vs_back (h10 : σ (.n 10) = 0) (h11 : σ (.n 11) = 0) (h12 : σ (.n 12) = 0)
    (h13 : σ (.n 13) = 0) {claims : List ColumnClaim}
    (hcol : claims.map (·.column) = Tables.claimColumns)
    (hval : ReadsAt rd (σ (.n 7)) (claims.map (·.value)))
    (h : Stmt.HoldsList C rd σ (vsMapsT ++ (vsCtabT ++ (vsLamT ++ vsTailT))) False kret) :
    -- the ring map
    (⟨[σ (.n 871), σ (.n 872), σ (.n 873), σ (.n 874), σ (.n 875)], []⟩ : Fs).squeezeN 5 =
      (vsChs σ, ⟨[σ (.n 966), σ (.n 967), σ (.n 968), σ (.n 969), σ (.n 970)], []⟩) ∧
    ReadsAt rd (σ (.n 876)) (σ (.n 870) :: vsChs σ) ∧
    ReadsAt rd (σ (.n 877)) (ringCoefficients (σ (.n 870) :: vsChs σ)) ∧
    C "ring_switch_target" [σ (.n 860), σ (.n 876)] [σ (.n 1303)] ∧
    -- the batching
    (⟨[σ (.n 966), σ (.n 967), σ (.n 968), σ (.n 969), σ (.n 970)], []⟩ : Fs).squeeze =
      (σ (.n 1323), ⟨[σ (.n 1312), σ (.n 1313), σ (.n 1314), σ (.n 1315), σ (.n 1316)], []⟩) ∧
    (∀ j < Tables.nClaims, Tables.claimColumns.getD j 0 ∉ keccakOutputColumns →
      LoadHolds rd (σ (.n 1324)) j (σ (.n 1323) ^ (1 + poolRank j))) ∧
    σ (.n 1884) = σ (.n 1323) ^ (1 + poolRank Tables.nClaims) ∧
    σ (.n 1886) = dot (powers (σ (.n 1323)) ((notLanes claims).length + 2))
      (σ (.n 1303) :: ((notLanes claims).map (·.value) ++ [σ (.n 869)])) ∧
    -- the tail
    C "certify_placement" [σ (.n 141), σ (.n 5)] [σ (.n 1887), σ (.n 1888), σ (.n 1889)] ∧
    C "log2_ceil_in_the_exponent__L15_L34" [σ (.n 1887), σ (.n 4), σ (.n 5)] [σ (.n 1890)] ∧
    σ (.n 1892) = σ (.n 1890) * word 8198552432976855044 0 0 ∧
    (LoadHolds rd (σ (.n 1892)) 0 (σ (.n 1895)) ∧ word 64 0 0 = σ (.n 1892) * σ (.n 1894) ∧
      LoadHolds rd (σ (.n 1894)) 0 (σ (.n 1896))) ∧
    σ (.n 1901) = σ (.n 1892) * (σ (.n 124) * σ (.n 124) * σ (.n 124) *
      (σ (.n 124) * σ (.n 124) * σ (.n 124)) * σ (.n 124)) ∧
    (LoadHolds rd (σ (.n 1901)) 0 (σ (.n 1904)) ∧ word 134217728 0 0 = σ (.n 1901) * σ (.n 1903) ∧
      LoadHolds rd (σ (.n 1903)) 0 (σ (.n 1905))) ∧
    (∃ (j : ℕ) (hj : j < vsOpenNames.length), σ (.n 1901) = ofK (gpow j) ∧
      C vsOpenNames[j] (vsOsArgs σ) (vsOsRets σ)) ∧
    C "check_opening_terminal" [σ (.n 523), σ (.n 848), σ (.n 857), σ (.n 522), σ (.n 855),
      σ (.n 130), σ (.n 858), σ (.n 8), σ (.n 1884), σ (.n 1324), σ (.n 1888), σ (.n 1889),
      σ (.n 859), σ (.n 877), σ (.n 1907), σ (.n 1908), σ (.n 1909), σ (.n 1910), σ (.n 1906)] [] ∧
    (∀ k < 19, ∃ v, LoadHolds rd (σ (.n 523)) k v ∧ LoadHolds rd (σ (.n 6)) k v) ∧
    (∀ k < 4, ∃ v, LoadHolds rd (σ (.n 559)) k v ∧ LoadHolds rd (σ (.n 6)) (19 + k) v) ∧
    LoadHolds rd (σ (.n 6)) 23 (σ (.n 856)) ∧ kret [] := by
  rw [holdsList_append, holdsList_append, holdsList_append] at h
  obtain ⟨hm, hmR, h⟩ := vsMapsT_holds h10 h11 h12 h13 h
  obtain ⟨hct, hrst, h⟩ := vsCtabT_holds (chs := σ (.n 870) :: vsChs σ) rfl hmR h
  obtain ⟨hlam, hpw, h1884, h1886, h⟩ := vsLamT_holds h10 h11 h12 h13 hcol hval h
  exact ⟨hm, hmR, hct, hrst, hlam, hpw, h1884, h1886, vsTailT_holds h⟩

end
end LeanVM.Guest.B1.VerifySub
