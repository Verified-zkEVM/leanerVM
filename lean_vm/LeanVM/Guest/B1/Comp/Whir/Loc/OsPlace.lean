/-
  LeanVM.Guest.B1.Comp.Whir.Loc.OsPlace

  Placing `open_stacked` over a completeness model (`Whir/OsPlace.lean`)
-/

module

public import LeanVM.Guest.B1.Whir.OsPlaceB
public import LeanVM.Guest.B1.UniformS
public import LeanVM.Guest.B1.Comp.Whir.OsCapC

/-!
# Placing `open_stacked` over a completeness model (`Whir/OsPlace.lean`)
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.E2E.Complete
open LeanVM.Protocol.Compile (Bytes)
open LeanVM.Protocol (Digest)

@[expose] public section

variable {Ht : Bytes → Digest} {CM : CompModel}

variable {fs : String → ℕ} {cert : String → V → ℕ}

theorem os_kidsFromIn_rmonoC {rd : Reader} {σ : Val} {R R' : ℕ → Prop} (hR : ∀ i, R i → R' i) :
    ∀ (cs : List Call) (Dacc : ℕ → Prop) (b n : ℕ) (D : ℕ → Prop),
      KidsFromInB CM.sem coreProgram fs cert rd σ R Dacc cs b n D → KidsFromInB CM.sem coreProgram fs cert rd σ R' Dacc cs b n D
  | [], _, _, _, _, h => h
  | _ :: cs, _, _, _, _, ⟨m, n', Rk, Dk, hn, hRk, hc, hk⟩ =>
    ⟨m, n', Rk, Dk, hn, fun i hi => (hRk i hi).imp_left (hR i), hc, os_kidsFromIn_rmonoC hR cs _ _ _ _ hk⟩

end
end LeanVM.Guest.B1
