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

**The callees' entries on the run** (`KidsOn`): the first `n` callees the path enters are
entered on the run, at their entries and frames, and return to registers from which the run goes
on. `CplRunKB` is `CplRunB` with the callees' entries on the run to the return registers and the
path's returns as many as the certificate's (`nret`); `CplRunKB.cplRunB` forgets them. The
completeness check gives `CplRunKB` (`CplCompB.lean`'s `cplB_run`): T6-det's decoding needs every
honest instance entered on the honest run (`RunsOn.lean`).

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

/-! ## The callees' entries on a run -/

variable (S) in
/-- **The first `n` callees on the path were entered on the run from `W0` to `Y`**: each call
entered, at its callee's entry and frame, is reached from `W0`, and its return registers reach
`Y`. -/
def KidsOn {κ : ℕ} (L : MemImage κ) (es : List Ev) (kfps : List ℕ) (n : ℕ) (W0 Y : Regs K) : Prop :=
  ∀ i < n, ∀ (c : Call) (kfp : ℕ), (calls es)[i]? = some c → kfps[i]? = some kfp → c.taken = true →
    ReachB S guest L W0 ⟨gpow (entryOf c.f), gpow kfp⟩ ∧
      ∃ r, retRegs L (gpow kfp) = some r ∧ ReachB S guest L r Y

section KidsOn

variable {κ : ℕ} {L : MemImage κ} {es : List Ev} {kfps : List ℕ}

theorem KidsOn.zero (W0 Y : Regs K) : KidsOn S L es kfps 0 W0 Y :=
  fun _ h ↦ absurd h (Nat.not_lt_zero _)

/-- The run going on from `Y` to `Z`. -/
theorem KidsOn.reach {n : ℕ} {W0 Y Z : Regs K} (h : KidsOn S L es kfps n W0 Y)
    (hr : ReachB S guest L Y Z) : KidsOn S L es kfps n W0 Z := fun i hi c kfp hc hk ht ↦
  let ⟨h1, r, hr', h2⟩ := h i hi c kfp hc hk ht
  ⟨h1, r, hr', h2.trans hr⟩

/-- Fewer callees. -/
theorem KidsOn.le {n m : ℕ} {W0 Y : Regs K} (h : KidsOn S L es kfps n W0 Y) (hm : m ≤ n) :
    KidsOn S L es kfps m W0 Y := fun i hi ↦ h i (by omega)

/-- **One more callee**: the `n`-th, if entered, entered on the run and returning to `Y`. -/
theorem KidsOn.succ {n : ℕ} {W0 Y : Regs K} (h : KidsOn S L es kfps n W0 Y)
    (hn : ∀ (c : Call) (kfp : ℕ), (calls es)[n]? = some c → kfps[n]? = some kfp → c.taken = true →
      ReachB S guest L W0 ⟨gpow (entryOf c.f), gpow kfp⟩ ∧
        ∃ r, retRegs L (gpow kfp) = some r ∧ ReachB S guest L r Y) :
    KidsOn S L es kfps (n + 1) W0 Y := fun i hi ↦ by
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · exact h i hi
  · exact hn

end KidsOn

variable (S) in
/-- **`CplRunB` with the callees' entries**: as `CplRunB`, and every callee the path enters is
entered on the run, at its entry and frame, and returns to registers from which the run reaches
the function's return registers (`KidsOn`); the path returns as many values as the certificate
says (`nret`). -/
def CplRunKB (j : ℕ) : Prop :=
  ∀ {κ : ℕ} (L : MemImage κ), κ ≤ 32 → JTHolds glob L →
    (∀ q ∈ Memory.tableCells, L.read (gpow q.1) = some q.2) → ∀ (fp : ℕ), (j = 1 → fp = 0) →
    ∀ (σ : Val) (es : List Ev) (vs : List V), walk σ (coreOf j).body = .ret es vs →
    (∀ e ∈ es, e.HoldsB S L.read σ) → ∀ (kfps : List ℕ) (hdr : E × E),
    FrameHolds L j fp σ es vs kfps hdr → ∀ ck : List (Opcode → ℕ), KidsRunB S L σ es kfps ck →
    ∃ (r : Regs K) (c : Opcode → ℕ), (if j = 1 then r = Regs.final guest else retRegs L (gpow fp) = some r) ∧
      RunCB S guest L ⟨gpow (fnOf j).entry, gpow fp⟩ r c ∧
      (∀ op, c op ≤ pathCount j σ op + (ck.map (· op)).sum) ∧
      (∀ k (hk : k < vs.length),
        L.read (gpow (fp + (2 + (coreOf j).params.length + k))) = some (σ vs[k])) ∧
      KidsOn S L es kfps (calls es).length ⟨gpow (fnOf j).entry, gpow fp⟩ r ∧
      vs.length = (certOf j).nret

/-- `CplRunKB` gives `CplRunB`. -/
theorem CplRunKB.cplRunB {j : ℕ} (h : CplRunKB S j) : CplRunB S j :=
  fun L h32 hjt htab fp hm σ es vs hw hev kfps hdr hF ck hK ↦
    let ⟨r, c, hr, hrun, hle, hrets, _, _⟩ := h L h32 hjt htab fp hm σ es vs hw hev kfps hdr hF ck hK
    ⟨r, c, hr, hrun, hle, hrets⟩

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
