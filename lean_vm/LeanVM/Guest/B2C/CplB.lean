/-
  LeanVM.Guest.B2C.CplB

  What the completeness check gives of one compiled function (`Cpl.lean`) under any semantics
  of `BLAKE2S`.
-/

module

public import LeanVM.Guest.B2C.Cpl
public import LeanVM.Guest.B2C.CountB
public import LeanVM.Guest.Memory.EvalB

/-!
# The completeness check's conclusion under any `BLAKE2S` semantics

The check itself (`cplWin`, `CplOk`) and what it reads of the memory (`FrameHolds`) are
`Cpl.lean`'s: they read code and cells, not the semantics. What mentions the semantics is the
runs: the callees' (`KidsRunB`) and the function's (`CplRunB`), counted runs under `S : BlakeSem`
(`RunCB`) on paths whose events hold under `S` (`Ev.HoldsB`).

* `kidsRunB_deployed`, `cplRunB_deployed`: at `blakeDeployed`, they are `Cpl.lean`'s.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Exec LeanVM.Guest.Check

@[expose] public section

variable {S : BlakeSem}

variable (S) in
/-- **The callees on a path run** under `S`: each call entered, from its callee's entry at its
frame to its return registers, executing `ck[i] op` instructions of each opcode, its returns left
in its frame's cells after its arguments. -/
def KidsRunB {κ : ℕ} (L : MemImage κ) (σ : Val) (es : List Ev) (kfps : List ℕ) (ck : List (Opcode → ℕ)) :
    Prop :=
  ck.length = (calls es).length ∧ ∀ (i : ℕ) (c : Call) (kfp : ℕ), (calls es)[i]? = some c → kfps[i]? = some kfp →
    c.taken = true → (∃ r, retRegs L (gpow kfp) = some r ∧
      RunCB S guest L ⟨gpow (entryOf c.f), gpow kfp⟩ r (ck.getD i 0)) ∧
      ∀ k (hk : k < c.rets.length), L.read (gpow (kfp + (2 + c.args.length + k))) = some (σ c.rets[k])

variable (S) in
/-- **What the completeness check gives of function `j`** under `S` (`CplRun` under `S`): on a
memory holding the jump table, from an instance's frame holding what the check reads
(`FrameHolds`), its path's events holding under `S` and its callees' runs under `S` (`KidsRunB`),
a counted run under `S` from its entry to its return registers (`main`: the final ones), with at
most `pathMax` instructions of each opcode besides its callees', its returned values left in its
frame's cells after its arguments. -/
def CplRunB (j : ℕ) : Prop :=
  ∀ {κ : ℕ} (L : MemImage κ), κ ≤ 32 → JTHolds glob L →
    (∀ q ∈ Memory.tableCells, L.read (gpow q.1) = some q.2) → ∀ (fp : ℕ), (j = 1 → fp = 0) →
    ∀ (σ : Val) (es : List Ev) (vs : List V), walk σ (coreOf j).body = .ret es vs →
    (∀ e ∈ es, e.HoldsB S L.read σ) → ∀ (kfps : List ℕ) (hdr : E × E),
    FrameHolds L j fp σ es vs kfps hdr → ∀ ck : List (Opcode → ℕ), KidsRunB S L σ es kfps ck →
    ∃ (r : Regs K) (c : Opcode → ℕ), (if j = 1 then r = Regs.final guest else retRegs L (gpow fp) = some r) ∧
      RunCB S guest L ⟨gpow (fnOf j).entry, gpow fp⟩ r c ∧
      (∀ op, c op ≤ pathCount j σ op + (ck.map (· op)).sum) ∧
      ∀ k (hk : k < vs.length),
        L.read (gpow (fp + (2 + (coreOf j).params.length + k))) = some (σ vs[k])

/-! ## At the deployed semantics -/

section Deployed

/-- At the deployed semantics, `KidsRunB` is `Cpl.lean`'s `KidsRun`. -/
theorem kidsRunB_deployed {κ : ℕ} (L : MemImage κ) (σ : Val) (es : List Ev) (kfps : List ℕ)
    (ck : List (Opcode → ℕ)) : KidsRunB blakeDeployed L σ es kfps ck = KidsRun L σ es kfps ck := by
  simp only [KidsRunB, KidsRun, runCB_deployed]

/-- **At the deployed semantics, `CplRunB` is `Cpl.lean`'s `CplRun`.** -/
theorem cplRunB_deployed (j : ℕ) : CplRunB blakeDeployed j = CplRun j := by
  simp only [CplRunB, CplRun, kidsRunB_deployed, runCB_deployed, ev_holdsB_deployed]

end Deployed

end
end LeanVM.Guest.B2C
