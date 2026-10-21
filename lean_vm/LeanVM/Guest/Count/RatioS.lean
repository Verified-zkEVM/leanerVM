/-
  LeanVM.Guest.Count.RatioS

  `Ratio.lean` under any semantics of `BLAKE2S` (`S : BlakeSem`).
-/

module

public import LeanVM.Guest.Count.Ratio
public import LeanVM.Guest.Count.RatioBaseS

/-!
# `Ratio.lean` under any `BLAKE2S` semantics

Each definition and lemma of `Ratio.lean` that mentions the semantics, with `S : BlakeSem` a
parameter and a `S` in its name.
-/

namespace LeanVM.Guest.Count

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B2C

@[expose] public section

variable {S : BlakeSem}

/-- **`claim_list_digest`'s counts within its ratios of its words.** -/
theorem krClS_weight (op : Opcode) : ∀ (rd : Reader) (t : Tree) (args rets : List E), t.name = "claim_list_digest" →
    t.ValidB S coreProgram rd args rets → t.BufsOk coreProgram →
      1000 * t.weight (kcOm op) ≤ krClA op * t.total fs :=
  fun _ _ _ _ hn hv _ => krS_weight krCl_closed krCl_ratio (by decide +kernel) ⟨20, by decide +kernel, by decide +kernel⟩ op hn hv

/-- **`child_claim_list_digest`'s counts within its ratios of its words.** -/
theorem krCclS_weight (op : Opcode) : ∀ (rd : Reader) (t : Tree) (args rets : List E), t.name = "child_claim_list_digest" →
    t.ValidB S coreProgram rd args rets → t.BufsOk coreProgram →
      1000 * t.weight (kcOm op) ≤ krCclA op * t.total fs :=
  fun _ _ _ _ hn hv _ => krS_weight krCcl_closed krCcl_ratio (by decide +kernel) ⟨22, by decide +kernel, by decide +kernel⟩ op hn hv

end
end LeanVM.Guest.Count
