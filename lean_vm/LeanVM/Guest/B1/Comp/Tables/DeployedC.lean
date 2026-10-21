/-
  LeanVM.Guest.B1.Comp.Tables.DeployedC

  At the deployed completeness model: the total hash is BLAKE2s, every hash is answered, and
  completeness under its semantics is the deployed one.
-/

module

public import LeanVM.Guest.B1.Comp.Tables.RunInv
public import LeanVM.Guest.B1.Comp.Tables.CompletesB

/-!
# At the deployed model

`CompModel.deployed`'s answers as a hash model (`CompModel.deployed.hm`): its total hash is
BLAKE2s (`sqCvT_hm_deployed`, `obsCvT_hm_deployed`, `obsAllT_hm_deployed`), every absorb is
answered (`obsAns_hm_deployed`), and completeness under its semantics at the program's relation
under it is the deployed one (`CompletesB.toDeployed`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig LeanVM.E2E.Complete

@[expose] public section

theorem sqCvT_hm_deployed : sqCvT CompModel.deployed.hm = sqCv := rfl

theorem obsCvT_hm_deployed : obsCvT CompModel.deployed.hm = obsCv := rfl

theorem obsAllT_hm_deployed : obsAllT CompModel.deployed.hm = obsAll := rfl

/-- At the deployed model every absorb is answered. -/
theorem obsAns_hm_deployed (c : Digest) (l : List E) : ObsAns CompModel.deployed.hm c l :=
  fun _ hi => by rw [obsAllT_take_succ _ _ hi]; rfl

/-- **Completeness under the deployed semantics is the deployed one.** -/
theorem _root_.LeanVM.Guest.B1.Sig.CompletesB.toDeployed {rd : Reader} {lo hi : ℕ} {ss : List Stmt}
    {σ : Val} {P : Val → Prop}
    (h : CompletesB CompModel.deployed.sem (coreProgram.RelB CompModel.deployed.sem rd) rd lo hi ss
      σ P) : Completes (coreProgram.Rel rd) rd lo hi ss σ P := by
  obtain ⟨σ', he, hp, hh⟩ := h
  refine ⟨σ', he, hp, fun next kret hn => ?_⟩
  have := hh next kret hn
  rw [show CompModel.deployed.sem = blakeDeployed from rfl, relB_deployed, holdsListB_deployed]
    at this
  exact this

end
end LeanVM.Guest.B1
