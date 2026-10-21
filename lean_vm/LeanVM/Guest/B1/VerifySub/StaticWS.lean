/-
  LeanVM.Guest.B1.VerifySub.StaticWS

  `StaticW.lean` under any semantics of `BLAKE2S` (`S : BlakeSem`).
-/

module

public import LeanVM.Guest.B1.VerifySub.StaticW
public import LeanVM.Guest.B1.Main.WeightAtS

/-!
# `StaticW.lean` under any `BLAKE2S` semantics

Each definition and lemma of `StaticW.lean` that mentions the semantics, with `S : BlakeSem` a
parameter and a `S` in its name.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Semantics (BlakeSem blakeDeployed)

@[expose] public section

variable {S : BlakeSem}

variable (S) in
/-- **Every valid tree of `verify_sub`'s statically bounded callees is within `c` at `ω`.** -/
structure VsStatOkS (ω : String → ℕ) (c : VsStat) : Prop where
  gpw : WeightLeB S coreProgram ω "g_power_of_word__L6" fun _ => c.gpw
  l2a : WeightLeB S coreProgram ω "log2_ceil_in_the_exponent__L0_L34" fun _ => c.l2a
  l2b : WeightLeB S coreProgram ω "log2_ceil_in_the_exponent__L15_L34" fun _ => c.l2b
  ac : WeightLeB S coreProgram ω "assert_canonical" fun _ => c.ac
  pl : WeightLeB S coreProgram ω "certify_placement" fun _ => c.pl
  os : ∀ μ r, 22 ≤ μ → μ ≤ 28 → 1 ≤ r → r ≤ 4 → WeightLeB S coreProgram ω (openName μ r) fun _ => c.os

end
end LeanVM.Guest.B1.VerifySub
