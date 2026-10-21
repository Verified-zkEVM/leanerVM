/-
  LeanVM.Guest.B1.Comp.Whir.Loc.OsKidsB

  The kids of `open_stacked`, levels, over a completeness model (`Whir/OsKidsB.lean`)
-/

module

public import LeanVM.Guest.B1.Whir.OsKidsB
public import LeanVM.Guest.B1.Comp.Whir.Loc.CapAt
public import LeanVM.Guest.B1.Comp.Whir.Loc.QueriesAt

/-!
# The kids of `open_stacked`, levels, over a completeness model (`Whir/OsKidsB.lean`)
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub
open LeanVM.Guest.B1.Main (MemL RegionL)
open LeanVM.E2E.Complete
open LeanVM.Protocol.Compile (Bytes)
open LeanVM.Protocol (Digest)

@[expose] public section

variable {Ht : Bytes → Digest} {CM : CompModel}

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

/-- **Where the queries' words lie**, from what every memory holding them reads. -/
theorem os_oqTopReg_ofC {Lin : Main.Layout} {I pd cd : ℕ} {rew qw qbp flags cap : E} {wts qwV dbpV : ℕ → E}
    {leaf : ℕ → List K} {pos : ℕ → ℕ} {sibs : ℕ → List Digest} {n : ℕ}
    (h : ∀ rd, LowDef κ rd → MemL rd Lin → OqTopMemW Ht rd I pd cd rew qw qbp flags cap wts qwV dbpV leaf pos sibs n)
    {rd0 : Reader} (h1 : LowDef κ rd0) (h2 : MemL rd0 Lin) :
    OqTopReg (RegionL Lin) I pd cd rew qw qbp flags cap dbpV pos n := by
  refine ⟨fun jw hjw => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj l hl => ?_, fun j hj => ?_, fun j hj => ⟨?_, ?_⟩⟩
  · exact os_addr_in_regionL (fun rd hlw hm => ((h rd hlw hm).1 jw hjw).2) h1 h2
  · exact os_addr_in_regionL (fun rd hlw hm => ((h rd hlw hm).2.1 j hj).2) h1 h2
  · exact os_addr_in_regionL (fun rd hlw hm => ((h rd hlw hm).2.2.1 j hj).2) h1 h2
  · exact os_addr_in_regionL (fun rd hlw hm => ((h rd hlw hm).2.2.2.1 j hj l hl).2) h1 h2
  · exact os_addr_in_regionL (fun rd hlw hm => ((h rd hlw hm).2.2.2.2.1 j hj).2) h1 h2
  · exact os_addr_in_regionL (fun rd hlw hm => ((h rd hlw hm).2.2.2.2.2 j hj).1.2) h1 h2
  · exact os_addr_in_regionL (fun rd hlw hm => ((h rd hlw hm).2.2.2.2.2 j hj).2.2) h1 h2

end
end LeanVM.Guest.B1
