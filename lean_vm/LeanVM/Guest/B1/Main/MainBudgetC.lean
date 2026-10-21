/-
  LeanVM.Guest.B1.Main.MainBudgetC

  End's `MainCompleteC` from `mainC_completeW`: `main` within the budget under a semantics `S`
  over an answered hash.
-/

module

public import LeanVM.Guest.B1.Main.HonestAllC
public import LeanVM.Guest.EndCompleteC

/-!
# `main` within the budget over an answered hash

`MainBudget.lean`'s `mainComplete_of` under `S : BlakeSem` over the answered hash `Ha`, the honest
words over a total `Ht` agreeing with `Ha` where it answers: `mainCompleteC_of` gives
`End.MainCompleteC S Ha Ht fs cert cnt b` from the callees' completeness `CalleesAtC Ha S`, the
inline rows `FsRowsC S Ha`, the batching sumchecks `BsRowsC S Ha`, every child's run and fresh
shape, and the budget's clauses at `honestWordsC Ht`, the counts within the weights on every tree
valid under `S`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.End (MainCompleteC Limits Budget work hdrOf bytecode bytecode_length words_le_of_size)
open LeanVM.Guest.B1 (LowDef DisjL Within)

@[expose] public section

/-- **`main` is complete within the budget under `S` over the answered hash `Ha`**
(`mainComplete_of`). -/
theorem mainCompleteC_of {S : BlakeSem} {Ha : List UInt8 → Option Digest} {Ht : List UInt8 → Digest}
    (hag : ∀ x d, Ha x = some d → d = Ht x) (fs : String → ℕ) (cert : String → V → ℕ)
    (cnt : Tree → Opcode → ℕ) (b : Budget) {VsGood : VerifySub.VsData → Prop} {Bd : CalleeBounds}
    (H : CalleesAtC Ha S fs cert 16 VsGood Bd) (hF : FsRowsC S Ha) (hBs : BsRowsC S Ha)
    (ω : Opcode → String → ℕ) (Wt : ∀ op, MainWeightHypsS S fs (ω op)) (jt : Opcode → ℕ)
    (hfs : 2 ≤ fs "main")
    (hacc : ∀ seed s w pi, statementDigestWith Ha seed s = some pi →
      NodeRelWith Ha aggSeedD daPadCell daPadRow bytecode seed s w → Limits s w →
      E2E.Complete.CapsAgreeWith Ht seed w →
      ∀ c ∈ w.children, FreshShaped c.fresh ∧ ∃ D : VerifySub.VsData, VsGood D ∧
        D.pi = statementDigestH Ht seed c.statement ∧ D.seed = seed ∧ D.fresh = c.fresh)
    (hwords : ∀ seed s w, NodeRelWith Ha aggSeedD daPadCell daPadRow bytecode seed s w →
      Limits s w → mainBound fs Bd (honestWordsC Ht seed s w) ≤ b.words.eval (work s w))
    (hcnt : ∀ (rd : Reader) (t : Tree), t.ValidB S coreProgram rd [] [] → ∀ op,
      cnt t op ≤ t.weight (ω op) + jt op)
    (hinstrs : ∀ seed s w, NodeRelWith Ha aggSeedD daPadCell daPadRow bytecode seed s w →
      Limits s w → ∀ op,
      mainWeightS S (ω op) Bd (Wt op) (honestWordsC Ht seed s w) + jt op ≤ (b.instrs op).eval (work s w)) :
    MainCompleteC S Ha Ht fs cert cnt b := by
  intro seed s w pi hpi hN hlim hcaps hbs
  have hc := hacc seed s w pi hpi hN hlim hcaps
  obtain ⟨m, L, hW, hD, hmB, hrel⟩ := mainC_completeW fs Ht H hF hBs hag Wt le_rfl bytecode_length hN
    hpi hlim (fun c hc' => (hc c hc').1) (fun c hc' => (hc c hc').2) 0
  rw [Nat.zero_add] at hW
  have hbw := hwords seed s w hN hlim
  have hb32 : b.words.eval (work s w) ≤ 2 ^ 32 := le_trans (words_le_of_size hbs) (by norm_num)
  have hin : ∀ q ∈ L, 2 ≤ q.1 ∧ q.1 + q.2.length ≤ fs "main" + m := fun q hq => by
    have := hW q hq; omega
  refine ⟨fs "main" + m, L, lConsistent_of_pairwise hD, hin, le_trans (le_trans hmB hbw) hb32,
    le_trans hmB hbw, fun rd hl hL h0 h1 => ?_⟩
  obtain ⟨t, hn, hv, hb, hp, ht, hl', -, hw⟩ := hrel rd hl hL h0 h1
  exact ⟨t, hn, hv, hb, hp, ht, hl', fun op =>
    le_trans (hcnt rd t hv op) (le_trans (Nat.add_le_add_right (hw op) _) (hinstrs seed s w hN hlim op))⟩

end
end LeanVM.Guest.B1.Main
