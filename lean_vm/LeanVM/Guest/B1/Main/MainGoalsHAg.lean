/-
  LeanVM.Guest.B1.Main.MainGoalsHAg

  `main`'s honest `aggregate_claims` call: complete at `main`'s words (`MainGoalAg`).
-/

module

public import LeanVM.Guest.B1.Main.MainGoals
public import LeanVM.Guest.B1.Main.AggAt
public import LeanVM.Protocol.Verifier.DeferredShape
public import LeanVM.Guest.Batch.Node

/-!
# `aggregate_claims` on an honest run

`mem_hLmain`: buffer `i` of `main`'s honest words sits at its base. `kid_shapes`: under
`NodeRelation`, every child's two claims on the bytecode have `bytecodeVars` coordinates (the fresh
one because the deferring verifier accepts its proof). `hkids_words`: `main`'s words hold each
child's words where `aggregate_claims` reads them. `mainGoalAg`: the children's batching is the
statement's deferred claim, which `main`'s words hold at `defer_stmt`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest (Limits)
open LeanVM.Guest.B1 (CompleteAtD Returns bufL)

@[expose] public section

/-- Buffer `i` of `bufL` sits at its base. -/
theorem mem_bufL {b : ℕ} {sizes : List ℕ} {cs : List (List E)} {i : ℕ} (h1 : i < sizes.length)
    (h2 : i < cs.length) : ((bases b sizes).getD i 0, cs.getD i []) ∈ bufL b sizes cs := by
  have h1' : i < (bases b sizes).length := by rw [length_bases]; exact h1
  have hl : i < (bufL b sizes cs).length := by simp only [bufL, List.length_zip]; omega
  have he : (bufL b sizes cs)[i]'hl = ((bases b sizes)[i]'h1', cs[i]'h2) := List.getElem_zip
  rw [List.getD_eq_getElem _ _ h1', List.getD_eq_getElem _ _ h2, ← he]
  exact List.getElem_mem hl

variable (fs : String → ℕ) (fp : ℕ) (seed : Digest) (s : NodeStatement) (w : NodeWitness)

/-- **Buffer `i` of `main`'s honest words** sits at its base. -/
theorem mem_hLmain {i : ℕ} (hi : i < 10) :
    ((mPos (hData seed s w) (fp + fs "main")).getD i 0, (hOwn seed s w).getD i []) ∈
      hLmain fs fp seed s w :=
  List.mem_append_left _ (mem_bufL (by simp [mSizes]; omega) (by simp [hOwn]; omega))

/-- `main`'s words read buffer `i` at `g` to its base. -/
theorem reads_hLmain {rd : Reader} (hM : B1.Main.MemL rd (hLmain fs fp seed s w)) {i : ℕ}
    (hi : i < 10) : ReadsAt rd (gen ^ (mPos (hData seed s w) (fp + fs "main")).getD i 0)
      ((hOwn seed s w).getD i []) :=
  B1.Da.reads_of_memL hM (mem_hLmain fs fp seed s w hi)

variable {seed s w}

/-- **The children's claims' shapes**: `bytecodeVars` coordinates each. -/
theorem kid_shapes {bytecode : List K} (hbl : bytecode.length = 2 ^ bytecodeVars)
    (hrel : NodeRelation bytecode seed s w) : ∀ c ∈ w.children,
      c.freshClaim.bytecodePoint.length = bytecodeVars ∧
        c.statement.deferredClaim.bytecodePoint.length = bytecodeVars := by
  have hlog : Nat.log2 bytecode.length = bytecodeVars := by rw [hbl, Nat.log2_two_pow]
  intro c hc
  obtain ⟨hsh, hv⟩ := hrel.2.1 c hc
  exact ⟨by rw [verifyDeferred_shaped hv, hlog], by rw [← hlog]; exact hsh⟩

/-- The children's claims as `aggregate_claims` batches them. -/
abbrev hKids (seed : Digest) (w : NodeWitness) : List ChildClaims :=
  w.children.map fun c ↦ ⟨statementDigest seed c.statement, c.freshClaim, c.statement.deferredClaim⟩

/-- **`main`'s words hold every child's words** where `aggregate_claims` reads them. -/
theorem hkids_words {bytecode : List K} (hbl : bytecode.length = 2 ^ bytecodeVars)
    (hrel : NodeRelation bytecode seed s w) {rd : Reader}
    (hM : B1.Main.MemL rd (hLmain fs fp seed s w)) :
    ∀ c (hc : c < (hKids seed w).length), ChildWordsAt rd (hm fs fp seed s w).a394
      (hm fs fp seed s w).a400 (hm fs fp seed s w).a406 c (hKids seed w)[c] := by
  have hsh := kid_shapes hbl hrel
  have hb : bytecodeVars = 23 := rfl
  intro c hc
  rw [List.length_map] at hc
  have hmem := List.getElem_mem hc
  obtain ⟨hf, hd⟩ := hsh _ hmem
  have r6 := reads_hLmain fs fp seed s w hM (i := 5) (by omega)
  have r7 := reads_hLmain fs fp seed s w hM (i := 6) (by omega)
  have r8 := reads_hLmain fs fp seed s w hM (i := 7) (by omega)
  simp only [hOwn, List.getD_cons_succ, List.getD_cons_zero] at r6 r7 r8
  have p6 := readsAt_flatMap_of (w := 2) w.children (fun _ _ => rfl) r6 c hc
  have p7 := readsAt_flatMap_of (w := 24) w.children
    (fun a ha => by simp [DeferredClaim.cells, (hsh a ha).1, hb]) r7 c hc
  have p8 := readsAt_flatMap_of (w := 24) w.children
    (fun a ha => by simp [DeferredClaim.cells, (hsh a ha).2, hb]) r8 c hc
  simp only [hKids, List.getElem_map]
  refine ⟨hf, hd, ?_, ?_, p7, p8⟩
  · have := p6 0 (by simp [B1.Digest.digestCells])
    rwa [loadHolds_mul_gen_pow, Nat.add_zero] at this
  · have := p6 1 (by simp [B1.Digest.digestCells])
    rwa [loadHolds_mul_gen_pow] at this

/-- **`main`'s honest `aggregate_claims` call is complete**: under `NodeRelation` and `Limits`, for a
bytecode of `2^bytecodeVars` words. -/
theorem mainGoalAg (cert : String → V → ℕ) {bytecode : List K}
    (hbl : bytecode.length = 2 ^ bytecodeVars) (hrel : NodeRelation bytecode seed s w)
    (hl : Limits s w) : MainGoalAg fs cert fp seed s w := by
  intro hnc
  have hnc' : w.children.length ≠ 0 := hnc
  have hne : w.children ≠ [] := fun h => hnc' (by rw [h, List.length_nil])
  have hb := (nodeRel_iff.mp hrel).2.2.2.2.2
  simp only [hne, ↓reduceIte] at hb
  have hlog : Nat.log2 bytecode.length = bytecodeVars := by rw [hbl, Nat.log2_two_pow]
  have hrl : w.batchingHints.sumcheckMessages.length = 23 := by
    have hpt : s.deferredClaim.bytecodePoint.length = 23 := by rw [hrel.1, hlog]
    rw [(batch_out hb).1, aggOut, aggRun, bsRun_len] at hpt
    exact hpt
  have hdst := mem_hLmain fs fp seed s w (i := 9) (by omega)
  simp only [hOwn, List.getD_cons_succ, List.getD_cons_zero] at hdst
  have := aggregate_claims_completeAt fs cert (m := w.children.length) (by omega) hl.children
    (cs := hKids seed w) (by rw [List.length_map]) hrl hb
    (fun rd hM => hkids_words fs fp hbl hrel hM) hdst
  exact this
