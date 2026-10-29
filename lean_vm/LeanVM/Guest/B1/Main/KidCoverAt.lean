/-
  LeanVM.Guest.B1.Main.KidCoverAt

  A child's statement digest in the uniform placed form: the pure `statement_digest`.
-/

module

public import LeanVM.Guest.Memory.Uniform
public import LeanVM.Guest.B1.Digest.StatementComplete

/-!
# A child's statement digest, placed

* `statement_completeAt`: the pure digest, from its completeness on every memory holding the
  caller's words.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1 (CompleteAtD Returns completeAt_of_rel_pureD)

@[expose] public section

variable (fs : String → ℕ) (cert : String → V → ℕ)

/-! ## The pure digests -/

set_option maxRecDepth 100000 in
theorem sd_pure : coreProgram.PureIn ["statement_digest"] := by
  intro g hg fn hf
  rw [List.mem_singleton] at hg
  subst hg
  rw [find_statement_digest, Option.some.injEq] at hf
  subst hf
  decide +kernel

/-- **`statement_digest` is complete, placed**, on every memory holding the caller's words
`MeaningStatementDigest` reads. -/
theorem statement_completeAt {Lin : Layout} {args rets : List E}
    (h : ∀ rd, MemL rd Lin → MeaningStatementDigest rd args rets) :
    CompleteAtD fs cert 16 "statement_digest" Lin args (Returns rets) :=
  completeAt_of_rel_pureD sd_pure (List.mem_singleton_self _)
    (fun rd hm => statement_digest_complete rd args rets (h rd hm)) 16

end
end LeanVM.Guest.B1.Main
