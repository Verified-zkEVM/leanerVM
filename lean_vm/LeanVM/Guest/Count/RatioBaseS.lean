/-
  LeanVM.Guest.Count.RatioBaseS

  `RatioBase.lean` under any semantics of `BLAKE2S` (`S : BlakeSem`).
-/

module

public import LeanVM.Guest.Count.RatioBase
public import LeanVM.Guest.Memory.WeightRatioB

/-!
# `RatioBase.lean` under any `BLAKE2S` semantics

Each definition and lemma of `RatioBase.lean` that mentions the semantics, with `S : BlakeSem` a
parameter and a `S` in its name.
-/

namespace LeanVM.Guest.Count

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B2C

@[expose] public section

variable {S : BlakeSem}

/-- **A valid tree of a function of `J` within the ratios of its words.** -/
theorem krS_weight {J : List ℕ} {C : ℕ → List ℕ} {A : Opcode → ℕ} (hc : J.all (krClosedAt J C) = true)
    (hr : J.all (krRatioAt A) = true) (h16 : 16 ∉ J) {f : String} (hf : krIn J f) (op : Opcode)
    {rd : Reader} {t : Tree} {args rets : List E} (hn : t.name = f) (hv : t.ValidB S coreProgram rd args rets) :
    1000 * t.weight (kcOm op) ≤ A op * t.total fs :=
  weightB_le_ratio (Sz := krIn J) (kr_callsIn hc) (kr_ratio_om hr h16 op) t (hn ▸ hf) hv

end
end LeanVM.Guest.Count
