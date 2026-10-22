/-
  LeanVM.E2E.Complete.Count.Node

  L17's count, proved: under the deployed limits and the node relation, the node's log of hashed
  strings has fewer than `2^64` block prefixes.
-/

module

public import LeanVM.E2E.Complete.Count.Whir
public import LeanVM.E2E.Complete.Count.Stmt
public import LeanVM.E2E.Complete.Count.Da
public import LeanVM.E2E.Complete.Count.Xmss
public import LeanVM.E2E.Complete.Count.Sphincs

/-!
# The node's count

`nodeLog H s w` (`NodeLog.lean`) is the statement's digest, every child's digest and deferring
verifier, the held signatures' and DA openings' verifications, the children's claims and the
batching. Each part is bounded (`docs/roadmap/l17-count.md`):

* a statement's digest by `stmtBlocks` (`Count/Stmt.lean`): its lists and its deferred claim's
  cells, `53` of them when the claim has the bytecode's shape;
* a deferring verifier by `whirLeaves * leafBlocks whirLeafWidth` (`Count/Prog.lean`,
  `Count/Whir.lean`);
* a held signature by `xmssVerifyBlocks`, `sphincsVerifyBlocks` (`Count/Xmss.lean`,
  `Count/Sphincs.lean`), a held DA opening by `daOpenBlocks` (`Count/Da.lean`);
* the batching by `0`.

`prefixCount_nodeLog_le` adds them up under the node relation (whose DA openings have at most
`1024` rows and a vector of `2^15` scalars), and `nodeLog_count_lt` evaluates the sum under the
deployed limits (at most `16` children, lists below `2^16`, at most `16` DA claims): it is below
`2^38`.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Blake2sHash LeanVM.Node LeanVM.Guest

@[expose] public section

variable {H : Bytes → Digest}

/-- The holders' checks: at most `c` each, for every claim held directly. -/
theorem prefixCount_holdersLog_le {α W : Type} (f : α → W → List Bytes)
    {Q : α → Holder W → Prop} (c : ℕ) (hf : ∀ a w, Q a (.direct w) → prefixCount (f a w) ≤ c) :
    ∀ {as : List α} {hs : List (Holder W)}, List.Forall₂ Q as hs →
      prefixCount (holdersLog f as hs) ≤ as.length * c
  | _, _, .nil => Nat.zero_le _
  | a :: as, h :: hs, .cons hq hrest => by
    have ih := prefixCount_holdersLog_le f c hf hrest
    have h1 : prefixCount (holderLog f a h) ≤ c := by
      cases h with
      | direct w => exact hf a w hq
      | child i => exact Nat.zero_le _
    simp only [holdersLog, List.zipWith_cons_cons, List.flatten_cons, prefixCount_append,
      List.length_cons, Nat.succ_mul] at ih ⊢
    omega

/-- A child's checks: its statement's digest and its deferring verifier. -/
theorem prefixCount_childLog_le (bytecode : List K) (seed : Digest) (c : Child) :
    prefixCount (childLog H bytecode seed c) ≤
      stmtBlocks c.statement + whirLeaves * leafBlocks whirLeafWidth := by
  rw [childLog, prefixCount_append]
  exact Nat.add_le_add (prefixCount_statementDigestWith_le H _ _)
    (prefixCount_verifyDeferredWith_le H (leafBound_deferredProgram _ _ _) _ _)

/-- A sum bounded term by term. -/
theorem sum_map_le_mul_count {γ : Type} (g : γ → ℕ) (c : ℕ) :
    ∀ l : List γ, (∀ a ∈ l, g a ≤ c) → (l.map g).sum ≤ l.length * c
  | [], _ => Nat.zero_le _
  | a :: l, h => by
    rw [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have := sum_map_le_mul_count g c l fun b hb ↦ h b (List.mem_cons_of_mem _ hb)
    have := h a List.mem_cons_self
    omega

/-- **The count of the node's log, part by part**, under the node relation. -/
theorem prefixCount_nodeLog_le {s : NodeStatement} {w : NodeWitness}
    (hrel : NodeRelWith (fun x ↦ some (H x)) B1.Main.aggSeedD B1.Main.daPadCell B1.Main.daPadRow
      End.bytecode (seedOf H) s w) :
    prefixCount (nodeLog H s w) ≤ stmtBlocks s +
      (w.children.map fun c ↦ stmtBlocks c.statement + whirLeaves * leafBlocks whirLeafWidth).sum +
      s.claims.xmss.length * xmssVerifyBlocks + s.claims.sphincs.length * sphincsVerifyBlocks +
      s.claims.da.length * daOpenBlocks + (w.children.map (stmtBlocks ·.statement)).sum := by
  obtain ⟨-, -, hx, hs, hda, -⟩ := hrel
  unfold nodeLog nodeLogWith
  simp only [prefixCount_append, prefixCount_batchWith, Nat.add_zero]
  have h1 := prefixCount_statementDigestWith_le H (seedOf H) s
  have h2 := prefixCount_flatMap_le (childLog H End.bytecode (seedOf H))
    (fun c ↦ stmtBlocks c.statement + whirLeaves * leafBlocks whirLeafWidth) w.children
    fun c _ ↦ prefixCount_childLog_le _ _ c
  have h3 := prefixCount_holdersLog_le
    (fun c σ ↦ (xmssVerifyWith (LogM.hash H) c.1 c.2 σ).log) xmssVerifyBlocks
    (fun a σ _ ↦ prefixCount_xmssVerifyWith_le H a.1 a.2 σ) hx
  have h4 := prefixCount_holdersLog_le
    (fun c σ ↦ (sphincsVerifyWith (LogM.hash H) c.1 c.2 σ).log) sphincsVerifyBlocks
    (fun a σ _ ↦ prefixCount_sphincsVerifyWith_le H a.1 a.2 σ) hs
  have h5 := prefixCount_holdersLog_le (fun (_ : DaClaim) ↦ daLog H B1.Main.daPadCell B1.Main.daPadRow)
    daOpenBlocks (fun _ dw hq ↦ prefixCount_daLog_le H _ _ dw hq.2.1 hq.2.2.2.2.1) hda
  have h6 := prefixCount_childClaimsM_le H (seedOf H) w.children
  omega

/-- A deferred claim of the bytecode's shape has `53` cells. -/
theorem length_cells_of_shaped {d : DeferredClaim} (h : d.Shaped End.bytecode) :
    d.cells.length = 53 := by
  simp only [DeferredClaim.cells, List.length_append, List.length_cons, List.length_nil, h.1, h.2,
    End.bytecode_length, Nat.log2_two_pow, blake2sR1csLogSize]

/-- **L17's count, proved**: under the deployed limits and the node relation, the node's log of
hashed strings has fewer than `2^64` block prefixes. -/
theorem nodeLog_count_lt {s : NodeStatement} {w : NodeWitness} (hlim : End.Limits s w)
    (hrel : NodeRelWith (fun x ↦ some (H x)) B1.Main.aggSeedD B1.Main.daPadCell B1.Main.daPadRow
      End.bytecode (seedOf H) s w) :
    (prefixesOf (nodeLog H s w)).length < 2 ^ 64 := by
  have hsum := prefixCount_nodeLog_le hrel
  have hcov : s.claims.xmss.length + s.claims.sphincs.length + s.claims.da.length < 2 ^ 16 := by
    have := hlim.coverage
    dsimp only [End.coverage] at this
    omega
  have hs : stmtBlocks s ≤ 2 ^ 16 + 56 := by
    unfold stmtBlocks
    rw [length_cells_of_shaped hrel.1]
    omega
  have hc : ∀ c ∈ w.children, stmtBlocks c.statement ≤ 2 ^ 17 + 72 := fun c hc ↦ by
    unfold stmtBlocks
    rw [length_cells_of_shaped (hrel.2.1 c hc).1]
    have := hlim.lists c hc
    have := hlim.daRoots.2 c hc
    omega
  have hk := hlim.children
  have hw : whirLeaves * leafBlocks whirLeafWidth = 8464 := by decide
  have h2 := sum_map_le_mul_count
    (fun c : Child ↦ stmtBlocks c.statement + whirLeaves * leafBlocks whirLeafWidth)
    (2 ^ 17 + 72 + 8464) w.children fun c hm ↦ by
      have := hc c hm
      omega
  have h6 := sum_map_le_mul_count (fun c : Child ↦ stmtBlocks c.statement) (2 ^ 17 + 72)
    w.children hc
  have h2' : w.children.length * (2 ^ 17 + 72 + 8464) ≤ 16 * (2 ^ 17 + 72 + 8464) :=
    Nat.mul_le_mul_right _ hk
  have h6' : w.children.length * (2 ^ 17 + 72) ≤ 16 * (2 ^ 17 + 72) := Nat.mul_le_mul_right _ hk
  have h3 : s.claims.xmss.length * xmssVerifyBlocks ≤ 2 ^ 16 * 2 ^ 20 :=
    Nat.mul_le_mul (by omega) xmssVerifyBlocks_le
  have h4 : s.claims.sphincs.length * sphincsVerifyBlocks ≤ 2 ^ 16 * 2 ^ 20 :=
    Nat.mul_le_mul (by omega) sphincsVerifyBlocks_le
  have h5 : s.claims.da.length * daOpenBlocks ≤ 16 * 2 ^ 30 :=
    Nat.mul_le_mul hlim.daRoots.1 daOpenBlocks_le
  show prefixCount (nodeLog H s w) < 2 ^ 64
  omega

end
end LeanVM.E2E.Complete
