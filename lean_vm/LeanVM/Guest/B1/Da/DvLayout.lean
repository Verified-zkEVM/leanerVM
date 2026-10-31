/-
  LeanVM.Guest.B1.Da.DvLayout

  `da_verify`'s own buffers as the bump allocator places them, holding the words an honest run
  leaves (`dvOwn`), and the memory `DaMem`/`ColMem` describe read off a memory holding them.
-/

module

public import LeanVM.Guest.B1.Da.AtBase
public import LeanVM.Guest.B1.Da.VerifyColComplete

/-!
# `da_verify`'s buffers, placed

From `b0 = fp + fs "da_verify"`, `da_verify` allocates `prefix_digests` (`128·2^L` words),
`prefix_bases` (`r`), the column digests (`256`), the running sums (`129r`), their bases (`r`),
the column tree (`512`) and the row tree (`4·2^L`) (`dvSizes`); `dvConts` are the words an honest
run leaves in them, `dvOwn` the layout. `dvPtrsAt` is `DaPtrs` at those buffers (the columns' node trees
and weights given), and `colMem_of_memL` reads `ColMem` off a memory holding `dvOwn` and a
column's node tree and weights.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Digest
open LeanVM.Guest.B1 (bufL bufL_within bufL_disj Within DisjL)
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable (r L : ℕ) (syms : ℕ → ℕ → List K) (ws : ℕ → List E) (b0 : ℕ)

/-- `da_verify`'s `HeapBuf` sizes. -/
def dvSizes : List ℕ := [128 * 2 ^ L, r, 256, 129 * r, r, 512, 4 * 2 ^ L]

/-- The buffers' first words. -/
def dxP : ℕ := b0 + 128 * 2 ^ L
def dxC : ℕ := dxP L b0 + r
def dxA : ℕ := dxC r L b0 + 256
def dxB : ℕ := dxA r L b0 + 129 * r
def dxT : ℕ := dxB r L b0 + r
def dxW : ℕ := dxT r L b0 + 512

/-- **The words an honest run leaves in `da_verify`'s buffers.** -/
def dvConts : List (List E) :=
  [(List.range r).flatMap (prefixCells syms), (List.range r).map fun i => gen ^ (b0 + 128 * i),
    cdCells ws, (List.range r).flatMap fun i => (List.range 129).map (accSum syms ws i),
    (List.range r).map fun i => gen ^ (dxA r L b0 + 129 * i), treeCells (colLeaves r L syms) 7,
    treeCells (rowLeaves r L syms) L]

/-- **`da_verify`'s own buffers' layout.** -/
def dvOwn : Layout := bufL b0 (dvSizes r L) (dvConts r L syms ws b0)

theorem dvOwn_eq : dvOwn r L syms ws b0 =
    [(b0, (List.range r).flatMap (prefixCells syms)),
      (dxP L b0, (List.range r).map fun i => gen ^ (b0 + 128 * i)), (dxC r L b0, cdCells ws),
      (dxA r L b0, (List.range r).flatMap fun i => (List.range 129).map (accSum syms ws i)),
      (dxB r L b0, (List.range r).map fun i => gen ^ (dxA r L b0 + 129 * i)),
      (dxT r L b0, treeCells (colLeaves r L syms) 7), (dxW r L b0, treeCells (rowLeaves r L syms) L)] :=
  rfl

/-- `da_verify`'s pointers at its buffers, the columns' node trees and weights given. -/
def dvPtrsAt (node lv : ℕ → E) : DaPtrs :=
  ⟨gen ^ dxP L b0, gen ^ b0, gen ^ dxC r L b0, gen ^ dxA r L b0, gen ^ dxB r L b0, gen ^ dxT r L b0,
    gen ^ dxW r L b0, node, lv⟩

variable {r L syms ws b0}

theorem length_prefixCells (i : ℕ) : (prefixCells syms i).length = 128 := by
  rw [prefixCells, length_flatMap_range _ 2 _ (fun j => rfl)]

theorem length_colLeaves : (colLeaves r L syms).length = 2 ^ 7 := by simp [colLeaves]

theorem length_rowLeaves : (rowLeaves r L syms).length = 2 ^ L := by simp [rowLeaves]

/-- The buffers' words fit their sizes. -/
theorem dvConts_fit (hrL : r ≤ 2 ^ L) :
    List.Forall₂ (fun c s => c.length ≤ s) (dvConts r L syms ws b0) (dvSizes r L) := by
  simp only [dvConts, dvSizes, List.forall₂_cons, List.Forall₂.nil, and_true]
  refine ⟨?_, by simp, by rw [cdCells_length], ?_, by simp, ?_, ?_⟩
  · rw [length_flatMap_range _ 128 _ length_prefixCells]; omega
  · rw [length_flatMap_range _ 129 _ (fun i => by simp)]; omega
  · rw [length_treeCells length_colLeaves]; omega
  · rw [length_treeCells length_rowLeaves]; omega

/-- **The memory `da_verify` and its callees read in its own buffers.** -/
structure DvBufMem (r L : ℕ) (syms : ℕ → ℕ → List K) (ws : ℕ → List E) (rd : Reader) (P : DaPtrs) :
    Prop where
  pbase : ∀ i < r, LoadHolds rd (P.pb * gen ^ i) 0 (P.pd * (gen ^ i) ^ 128)
  pcells : ∀ i < r, ReadsAt rd (P.pd * (gen ^ i) ^ 128) (prefixCells syms i)
  cd : ReadsAt rd P.cd (cdCells ws)
  rbase : ∀ i < r, LoadHolds rd (P.rb * gen ^ i) 0 (P.acc * (gen ^ i) ^ 129)
  acc : ∀ i < r, ReadsAt rd (P.acc * (gen ^ i) ^ 129) ((List.range 129).map (accSum syms ws i))
  ct : TreeMem rd P.ct 7 (colLeaves r L syms)
  rt : TreeMem rd P.rt L (rowLeaves r L syms)

/-- **`DvBufMem` off a memory holding `da_verify`'s buffers.** -/
theorem dvBufMem_of_memL {rd : Reader} {node lv : ℕ → E} (hm : MemL rd (dvOwn r L syms ws b0)) :
    DvBufMem r L syms ws rd (dvPtrsAt r L b0 node lv) := by
  rw [dvOwn_eq] at hm
  have m : ∀ {q}, q ∈ [(b0, (List.range r).flatMap (prefixCells syms)),
      (dxP L b0, (List.range r).map fun i => gen ^ (b0 + 128 * i)), (dxC r L b0, cdCells ws),
      (dxA r L b0, (List.range r).flatMap fun i => (List.range 129).map (accSum syms ws i)),
      (dxB r L b0, (List.range r).map fun i => gen ^ (dxA r L b0 + 129 * i)),
      (dxT r L b0, treeCells (colLeaves r L syms) 7), (dxW r L b0, treeCells (rowLeaves r L syms) L)] →
      ReadsAt rd (gen ^ q.1) q.2 := fun hq => by rw [gen_pow_eq_ofK]; exact hm _ hq
  refine ⟨fun i hi => ?_, fun i hi => ?_, m (q := (dxC r L b0, cdCells ws)) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
    fun i hi => ?_, fun i hi => ?_,
    treeMem_of_reads length_colLeaves (m (q := (dxT r L b0, treeCells (colLeaves r L syms) 7)) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))),
    treeMem_of_reads length_rowLeaves (m (q := (dxW r L b0, treeCells (rowLeaves r L syms) L)) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))))⟩
  · have h := m (q := (dxP L b0, (List.range r).map fun i => gen ^ (b0 + 128 * i))) (List.mem_cons_of_mem _ List.mem_cons_self) i
      (by simpa using hi)
    simp only [List.getElem_map, List.getElem_range] at h
    show LoadHolds rd (gen ^ dxP L b0 * gen ^ i) 0 (gen ^ b0 * (gen ^ i) ^ 128)
    rw [loadHolds_mul_gen_pow, Nat.add_zero, ← pow_mul, ← pow_add, Nat.mul_comm i]
    exact h
  · have h := Main.readsAt_flatMap_of (List.range r) (fun i _ => length_prefixCells i)
      (m (q := (b0, (List.range r).flatMap (prefixCells syms))) List.mem_cons_self) i (by simpa using hi)
    simp only [List.getElem_range] at h
    show ReadsAt rd (gen ^ b0 * (gen ^ i) ^ 128) (prefixCells syms i)
    rwa [← pow_mul, Nat.mul_comm i]
  · have h := m (q := (dxB r L b0, (List.range r).map fun i => gen ^ (dxA r L b0 + 129 * i))) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))) i
      (by simpa using hi)
    simp only [List.getElem_map, List.getElem_range] at h
    show LoadHolds rd (gen ^ dxB r L b0 * gen ^ i) 0 (gen ^ dxA r L b0 * (gen ^ i) ^ 129)
    rw [loadHolds_mul_gen_pow, Nat.add_zero, ← pow_mul, ← pow_add, Nat.mul_comm i]
    exact h
  · have h := Main.readsAt_flatMap_of (List.range r) (fun i _ => by simp)
      (m (q := (dxA r L b0, (List.range r).flatMap fun i => (List.range 129).map (accSum syms ws i)))
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))) i (by simpa using hi) (w := 129)
    simp only [List.getElem_range] at h
    show ReadsAt rd (gen ^ dxA r L b0 * (gen ^ i) ^ 129) _
    rwa [← pow_mul, Nat.mul_comm i]

/-- **`ColMem` off a memory holding `da_verify`'s buffers and column `j`'s node tree and
weights.** -/
theorem colMem_of_memL {rd : Reader} {node lv : ℕ → E} {j : ℕ}
    (hm : MemL rd (dvOwn r L syms ws b0)) (hnode : TreeMem rd (node j) L (nodeLeaves r L syms j))
    (hlvK : IsInK (lv j)) (hlv : ReadsAt rd (lv j) (ws j)) :
    ColMem r L syms ws rd (dvPtrsAt r L b0 node lv) j :=
  have h := dvBufMem_of_memL (node := node) (lv := lv) hm
  ⟨h.pbase, h.pcells, h.cd, h.rbase, h.acc, h.ct, hnode, hlvK, hlv⟩

end
end LeanVM.Guest.B1.Da
