/-
  LeanVM.Guest.B1.Comp.Whir.Loc.CapAt

  `verify_merkle_cap`, placed, over a completeness model (`Whir/CapAt.lean`)
-/

module

public import LeanVM.Guest.Memory.SizeB
public import LeanVM.Guest.B1.Whir.CapAt
public import LeanVM.Guest.B1.Comp.CompleteAtB
public import LeanVM.Guest.B1.Comp.Whir.Cap

/-!
# `verify_merkle_cap`, placed, over a completeness model (`Whir/CapAt.lean`)
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (MemL)
open LeanVM.E2E.Complete
open LeanVM.Protocol.Compile (Bytes)
open LeanVM.Protocol (Digest)

@[expose] public section

variable {Ht : Bytes → Digest} {CM : CompModel}

/-- `VmcCompleteAt` by trees of at most `B` words. -/
def VmcCompleteAtBC (CM : CompModel) (fs : String → ℕ) (cert : String → V → ℕ) (k D : ℕ) (name : String) (B : ℕ) : Prop :=
  ∀ (Lin : Main.Layout) (cap flags : E) (rets : List E),
    (∀ rd, MemL rd Lin → MeaningVerifyMerkleCapComp CM D rd [cap, flags] rets) →
      CompleteAtBS CM.sem fs cert k name Lin [cap, flags] (Returns rets) B

theorem vmc_completeAtBC {fs : String → ℕ} {cert : String → V → ℕ} {k D : ℕ} {name loop : String}
    (hS : coreProgram.PureIn [name, loop])
    (hrel : ∀ rd args rets, MeaningVerifyMerkleCapComp CM D rd args rets → coreProgram.RelB CM.sem rd name args rets) {B : ℕ}
    (hB : TotalLeB CM.sem coreProgram fs name fun _ => B) : VmcCompleteAtBC CM fs cert k D name B := fun _ _ _ _ h =>
  completeAtS_of_rel_pureBat hS (by simp) (fun rd hL => hrel rd _ _ (h rd hL)) k
    fun rd t hn hv hb => hB rd t _ _ hn hv hb

theorem vmc_completeAtB_L4C (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) {B : ℕ}
    (hB : TotalLeB CM.sem coreProgram fs "verify_merkle_cap__L4" fun _ => B) :
    VmcCompleteAtBC CM fs cert k 4 "verify_merkle_cap__L4" B :=
  vmc_completeAtBC (CM := CM) vmc_pure_L4 verify_merkle_cap_L4_comp hB

theorem vmc_completeAtB_L5C (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) {B : ℕ}
    (hB : TotalLeB CM.sem coreProgram fs "verify_merkle_cap__L5" fun _ => B) :
    VmcCompleteAtBC CM fs cert k 5 "verify_merkle_cap__L5" B :=
  vmc_completeAtBC (CM := CM) vmc_pure_L5 verify_merkle_cap_L5_comp hB

theorem vmc_completeAtB_L6C (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) {B : ℕ}
    (hB : TotalLeB CM.sem coreProgram fs "verify_merkle_cap__L6" fun _ => B) :
    VmcCompleteAtBC CM fs cert k 6 "verify_merkle_cap__L6" B :=
  vmc_completeAtBC (CM := CM) vmc_pure_L6 verify_merkle_cap_L6_comp hB

theorem vmc_completeAtB_L7C (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) {B : ℕ}
    (hB : TotalLeB CM.sem coreProgram fs "verify_merkle_cap__L7" fun _ => B) :
    VmcCompleteAtBC CM fs cert k 7 "verify_merkle_cap__L7" B :=
  vmc_completeAtBC (CM := CM) vmc_pure_L7 verify_merkle_cap_L7_comp hB

theorem vmc_completeAtB_L8C (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) {B : ℕ}
    (hB : TotalLeB CM.sem coreProgram fs "verify_merkle_cap__L8" fun _ => B) :
    VmcCompleteAtBC CM fs cert k 8 "verify_merkle_cap__L8" B :=
  vmc_completeAtBC (CM := CM) vmc_pure_L8 verify_merkle_cap_L8_comp hB

end
end LeanVM.Guest.B1
