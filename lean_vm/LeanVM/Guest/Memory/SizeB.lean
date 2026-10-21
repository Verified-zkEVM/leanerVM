/-
  LeanVM.Guest.Memory.SizeB

  Weight and word bounds over the valid trees of a function (`Size.lean`) under any
  semantics of `BLAKE2S`.
-/

module

public import LeanVM.Guest.Memory.Size
public import LeanVM.Guest.Memory.RetempB

/-!
# Weight bounds under any `BLAKE2S` semantics

`Size.lean`'s `WeightLe` and `TotalLe` quantify over the valid trees of a function; here they
are over the trees valid under `S : BlakeSem` (`WeightLeB`, `TotalLeB`). The weights themselves
(`Tree.weight`, `Tree.total`) are `Size.lean`'s.

* `weightLeB_deployed`, `totalLeB_deployed`: at `blakeDeployed`, they are `Size.lean`'s.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

variable {S : BlakeSem}

variable (S) in
/-- Every valid tree of `f` on `args`, its `HeapBuf`s its paths', weighs at most `B args`. -/
def WeightLeB (P : Core.Program) (ω : String → ℕ) (f : String) (B : List E → ℕ) : Prop :=
  ∀ (rd : Reader) (t : Tree) (args rets : List E), t.name = f → t.ValidB S P rd args rets →
    t.BufsOk P → t.weight ω ≤ B args

variable (S) in
/-- Every valid tree of `f` on `args`, its `HeapBuf`s its paths', allocates at most `B args` words
(`Tree.ValidB` leaves the sizes free, `Tree.BufsOk` fixes them). -/
def TotalLeB (P : Core.Program) (fs : String → ℕ) (f : String) (B : List E → ℕ) : Prop :=
  ∀ (rd : Reader) (t : Tree) (args rets : List E), t.name = f → t.ValidB S P rd args rets →
    t.BufsOk P → t.total fs ≤ B args

/-! ## At the deployed semantics -/

section Deployed

variable {P : Core.Program}

/-- At the deployed semantics, `WeightLeB` is `Size.lean`'s `WeightLe`. -/
theorem weightLeB_deployed (ω : String → ℕ) (f : String) (B : List E → ℕ) :
    WeightLeB blakeDeployed P ω f B = WeightLe P ω f B := by
  simp only [WeightLeB, WeightLe, validB_deployed]

/-- **At the deployed semantics, `TotalLeB` is `Size.lean`'s `TotalLe`.** -/
theorem totalLeB_deployed (fs : String → ℕ) (f : String) (B : List E → ℕ) :
    TotalLeB blakeDeployed P fs f B = TotalLe P fs f B := by
  simp only [TotalLeB, TotalLe, validB_deployed]

end Deployed

end
end LeanVM.Guest.Memory
