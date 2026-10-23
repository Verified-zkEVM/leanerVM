/-
  LeanVM.Guest.B1.Main.MainGoalsF

  `main`'s callees on an honest run, the first ones: the loops writing the hinted claims
  (`__loop0`, `__loop1`, `__loop2`), the DA list's digest and the statement's digest; the claim
  lists' cells and bytes (their digests in `MainGoalsFCl`).
-/

module

public import LeanVM.Guest.B1.Main.MainGoals
public import LeanVM.Guest.B1.Main.MainGoalsFChk
public import LeanVM.Guest.B1.Main.KidCoverAt
public import LeanVM.Guest.B1.Main.Digests
public import LeanVM.Guest.B1.Digest.ClaimListAt
public import LeanVM.Guest.Limits
public import LeanVM.Protocol.Verifier.Load

/-!
# `main`'s first callees on an honest run

* `mainGoalL0`, `mainGoalL1`, `mainGoalL2`: the loops are atoms and a heap hint, so they hold on
  every memory (`loopF_complete` at an explicit valuation of each block) and place nothing
  (`mfLoop_pure`);
* `mainGoalDl`: the DA table's declared claims are their cells (`daCells`), canonical, whose
  bytes are the bytes the Spec's list digest hashes (`mf_da_digest`); at most `16` (`Limits`).
  The claim tables' cells (`claimCells`) likewise (`mf_xmss_digest`, `mf_sphincs_digest`);
* `mf_reads`, `mf_region`: buffer `i` of `hLmain` holds `hOwn`'s list `i`;
* `mainGoalSt`: the signer set's cells and the deferred claim's `24` cells (`NodeRel`'s shape on
  a bytecode of `2^23` words) hash, with the seed and the DA list's digest, to the statement's
  digest (`statementDigest_parts`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1.Digest
open LeanVM.Guest.Hints (claimCells cellsOfBytes cellOfBytes)
open LeanVM.Guest.B1 (CompleteAtD Returns bufL completeAt_of_rel_pureD)

@[expose] public section

/-! ## The loops -/

/-- `__loop0`'s valuation at the counter `x`, the end `N`, the DA table `a`. -/
def mfσ0 (x N a : E) : Val :=
  B1.Val.ofArgs [x, N, a, x * x, x * x * (x * x), a * (x * x * (x * x)), word 2 0 0,
    x * word 2 0 0, x * word 2 0 0 + N, word 2 0 0, x * word 2 0 0]

/-- `__loop1`'s and `__loop2`'s valuation at the counter `x`, the end `N`, the table `a` and the
declared count's `b`. -/
def mfσ1 (x N a b : E) : Val :=
  B1.Val.ofArgs [x, N, a, b, b * x, b * x * (b * x), b * x * (b * x) * (b * x * (b * x)),
    a * (b * x * (b * x) * (b * x * (b * x))), word 2 0 0, x * word 2 0 0, x * word 2 0 0 + N,
    word 2 0 0, x * word 2 0 0]

theorem mfL0_rel (rd : Reader) (a : E) {m : ℕ} (hm : m ≠ 0) :
    coreProgram.Rel rd "__loop0" [1, gen ^ m, a] [] := by
  have hf := find_of_idx mfL0_idx (by rw [coreProgram_length]; omega)
  have hblk : ∀ j < m, LoopBlock rd (coreProgram.getD 32 default) (gen ^ j) (gen ^ m) [a] := by
    intro j _
    refine ⟨mfσ0 (gen ^ j) (gen ^ m) a, rfl, ?_⟩
    rw [show loopPre (coreProgram.getD 32 default) = Data.core32.body.take 9 from rfl]
    intro t ht
    simp only [Data.core32.body, List.take_succ_cons, List.take_zero, List.mem_cons,
      List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact And.intro rfl trivial | exact And.intro trivial trivial
  have h := loopF_complete hf mfL0_shape rfl hblk 0 (by omega)
  rwa [pow_zero] at h

theorem mfL1_rel (rd : Reader) (a b : E) {m : ℕ} (hm : m ≠ 0) :
    coreProgram.Rel rd "__loop1" [1, gen ^ m, a, b] [] := by
  have hf := find_of_idx mfL1_idx (by rw [coreProgram_length]; omega)
  have hblk : ∀ j < m, LoopBlock rd (coreProgram.getD 33 default) (gen ^ j) (gen ^ m) [a, b] := by
    intro j _
    refine ⟨mfσ1 (gen ^ j) (gen ^ m) a b, rfl, ?_⟩
    rw [show loopPre (coreProgram.getD 33 default) = Data.core33.body.take 10 from rfl]
    intro t ht
    simp only [Data.core33.body, List.take_succ_cons, List.take_zero, List.mem_cons,
      List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact And.intro rfl trivial | exact And.intro trivial trivial
  have h := loopF_complete hf mfL1_shape rfl hblk 0 (by omega)
  rwa [pow_zero] at h

theorem mfL2_rel (rd : Reader) (a b : E) {m : ℕ} (hm : m ≠ 0) :
    coreProgram.Rel rd "__loop2" [1, gen ^ m, a, b] [] := by
  have hf := find_of_idx mfL2_idx (by rw [coreProgram_length]; omega)
  have hblk : ∀ j < m, LoopBlock rd (coreProgram.getD 34 default) (gen ^ j) (gen ^ m) [a, b] := by
    intro j _
    refine ⟨mfσ1 (gen ^ j) (gen ^ m) a b, rfl, ?_⟩
    rw [show loopPre (coreProgram.getD 34 default) = Data.core34.body.take 10 from rfl]
    intro t ht
    simp only [Data.core34.body, List.take_succ_cons, List.take_zero, List.mem_cons,
      List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact And.intro rfl trivial | exact And.intro trivial trivial
  have h := loopF_complete hf mfL2_shape rfl hblk 0 (by omega)
  rwa [pow_zero] at h

/-! ## Cells and bytes -/

theorem mf_lane_ofLane (w : UInt64) : K.lane (K.ofLane w) = w := rfl

/-- A cell read off 16 bytes has them as its bytes. -/
theorem mf_cellBytes_ofBytes {b : List UInt8} (h : 16 ≤ b.length) :
    cellBytes (cellOfBytes b) = b.take 16 := by
  simp only [cellBytes, cellOfBytes, limb_ofLimbs, Matrix.cons_val_zero, Matrix.cons_val_one,
    kBytes, kOfBytes, mf_lane_ofLane]
  rw [wordBytes_laneOfBytes (by omega), wordBytes_laneOfBytes (by simp; omega),
    ← List.take_add]

theorem mf_cellsBytes_aux : ∀ (n : ℕ) (b : List UInt8), b.length = 16 * n →
    ((List.range n).map fun i => cellOfBytes (b.drop (16 * i))).flatMap cellBytes = b
  | 0, b, h => by simp_all
  | n + 1, b, h => by
    rw [List.range_succ_eq_map, List.map_cons, List.flatMap_cons, List.map_map]
    have e : ((fun i => cellOfBytes (b.drop (16 * i))) ∘ Nat.succ) =
        fun i => cellOfBytes ((b.drop 16).drop (16 * i)) := by
      funext i
      simp only [Function.comp, List.drop_drop]
      congr 2
      omega
    rw [e, mf_cellsBytes_aux n (b.drop 16) (by simp; omega), Nat.mul_zero, List.drop_zero,
      mf_cellBytes_ofBytes (by omega), List.take_append_drop]

/-- **Bytes of a multiple of 16 are the bytes of their cells.** -/
theorem mf_cellsBytes_ofBytes {b : List UInt8} {n : ℕ} (h : b.length = 16 * n) :
    cellsBytes (cellsOfBytes b) = b := by
  unfold cellsOfBytes cellsBytes
  rw [h, Nat.mul_div_cancel_left _ (by omega)]
  exact mf_cellsBytes_aux n b h

theorem mf_cellsBytes_flatMap {α : Type} (l : List α) (f : α → List E) :
    cellsBytes (l.flatMap f) = l.flatMap fun a => cellsBytes (f a) := by
  simp only [cellsBytes, List.flatMap_assoc]

theorem mf_length_flatMap {α : Type} {k : ℕ} (f : α → List E) (hf : ∀ a, (f a).length = k) :
    ∀ l : List α, (l.flatMap f).length = k * l.length
  | [] => by simp
  | a :: l => by
    simp only [List.flatMap_cons, List.length_append, List.length_cons, hf,
      mf_length_flatMap f hf l, Nat.mul_add, Nat.mul_one]
    omega

theorem mf_canon_flatMap {α : Type} (f : α → List E) (hf : ∀ a, AllCanonical (f a)) (l : List α) :
    AllCanonical (l.flatMap f) := by
  intro c hc
  obtain ⟨a, -, hc⟩ := List.mem_flatMap.mp hc
  exact hf a c hc

theorem mf_digestCells_canon (d : Digest) : AllCanonical (digestCells d) := by
  intro c hc
  simp only [digestCells, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  exacts [(digestScalars_canonical d).1, (digestScalars_canonical d).2]

/-! ### The DA claims -/

theorem mf_daCells_length (c : DaClaim) : (daCells c).length = 4 := by
  simp [daCells, digestCells]

theorem mf_daCells_canon (c : DaClaim) : AllCanonical (daCells c) := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  exacts [mf_digestCells_canon _ x h, mf_digestCells_canon _ x h]

theorem mf_daCells_bytes (c : DaClaim) : cellsBytes (daCells c) = digestBytes c.1 ++ digestBytes c.2 := by
  rw [digestBytes_eq_cells, digestBytes_eq_cells]
  simp [daCells, digestCells, cellsBytes]

/-- **The DA list's digest is its cells'.** -/
theorem mf_da_digest (l : List DaClaim) : daListDigest l = keccak256 (cellsBytes (l.flatMap daCells)) := by
  rw [daListDigest, mf_cellsBytes_flatMap]
  simp only [mf_daCells_bytes]

/-! ### The signature claims -/

theorem mf_claimBytes_length (r p : BitVec 128) (m : BitVec 256) : (claimBytes r p m).length = 64 := by
  simp [claimBytes, bytes16, LeanXmss.bytesLE]

theorem mf_claimCells_length (r p : BitVec 128) (m : BitVec 256) : (claimCells r p m).length = 4 := by
  simp [claimCells, cellsOfBytes, mf_claimBytes_length]

theorem mf_claimCells_canon (r p : BitVec 128) (m : BitVec 256) : AllCanonical (claimCells r p m) := by
  intro c hc
  simp only [claimCells, cellsOfBytes, List.mem_map] at hc
  obtain ⟨i, -, rfl⟩ := hc
  simp [IsCanonical128, cellOfBytes]

theorem mf_claimCells_bytes (r p : BitVec 128) (m : BitVec 256) :
    cellsBytes (claimCells r p m) = claimBytes r p m :=
  mf_cellsBytes_ofBytes (n := 4) (by rw [mf_claimBytes_length])

/-- **The leanXMSS list's digest is its cells'.** -/
theorem mf_xmss_digest (l : List XmssClaim) :
    xmssListDigest l = keccak256 (cellsBytes (l.flatMap fun c => claimCells c.1.root c.1.parameter c.2)) := by
  rw [xmssListDigest, mf_cellsBytes_flatMap]
  congr 2
  funext c
  exact (mf_claimCells_bytes _ _ _).symm

/-- **The leanSPHINCS list's digest is its cells'.** -/
theorem mf_sphincs_digest (l : List SphincsClaim) :
    sphincsListDigest l =
      keccak256 (cellsBytes (l.flatMap fun c => claimCells c.1.root c.1.parameter c.2)) := by
  rw [sphincsListDigest, mf_cellsBytes_flatMap]
  congr 2
  funext c
  exact (mf_claimCells_bytes _ _ _).symm

/-! ## `main`'s buffers -/

theorem mf_mem_bufL : ∀ (b : ℕ) (sizes : List ℕ) (cs : List (List E)) (i : ℕ),
    i < sizes.length → i < cs.length →
      ((Memory.bases b sizes).getD i 0, cs.getD i []) ∈ bufL b sizes cs
  | _, [], _, _, h, _ => absurd h (by simp)
  | _, _ :: _, [], _, _, h => absurd h (by simp)
  | b, s :: ss, c :: cs, 0, _, _ => by simp [bufL, Memory.bases]
  | b, s :: ss, c :: cs, i + 1, h1, h2 => by
    have := mf_mem_bufL (b + s) ss cs i (by simpa using h1) (by simpa using h2)
    simp only [bufL, Memory.bases, List.zip_cons_cons, List.getD_cons_succ, List.mem_cons] at this ⊢
    exact Or.inr this

variable (fs : String → ℕ) (cert : String → V → ℕ) (fp : ℕ) (seed : Digest) (s : NodeStatement)
  (w : NodeWitness)

/-- `main`'s buffer `i`'s first word. -/
abbrev mfB (i : ℕ) : ℕ := (Memory.bases (fp + fs "main") (mSizes (hData seed s w))).getD i 0

theorem mf_mem {i : ℕ} (hi : i < 11) :
    (mfB fs fp seed s w i, (hOwn seed s w).getD i []) ∈ bufL (fp + fs "main") (mSizes (hData seed s w))
      (hOwn seed s w) :=
  mf_mem_bufL _ _ _ i (by simp only [mSizes, List.length_cons, List.length_nil]; omega)
    (by simp only [hOwn, List.length_cons, List.length_nil]; omega)

/-- **Buffer `i` holds `main`'s honest words.** -/
theorem mf_reads {rd : Reader} (h : MemL rd (hLmain fs fp seed s w)) {i : ℕ} (hi : i < 11) :
    ReadsAt rd (gen ^ mfB fs fp seed s w i) ((hOwn seed s w).getD i []) :=
  Da.reads_of_memL (memL_append.mp h).1 (mf_mem fs fp seed s w hi)

theorem mf_region {i : ℕ} (hi : i < 11) {k : ℕ} (hk : k < ((hOwn seed s w).getD i []).length) :
    RegionL (hLmain fs fp seed s w) (mfB fs fp seed s w i + k) := by
  obtain ⟨q, hq, h⟩ := Da.regionL_of_mem (mf_mem fs fp seed s w hi) hk
  exact ⟨q, List.mem_append_left _ hq, h⟩

/-! ## The goals -/

theorem mainGoalL0 : MainGoalL0 fs cert fp seed s w := fun hne =>
  completeAt_of_rel_pureD mfLoop_pure (by simp [mfLoopSet]) (fun rd _ => mfL0_rel rd _ hne) 16

theorem mainGoalL1 : MainGoalL1 fs cert fp seed s w := fun hne =>
  completeAt_of_rel_pureD mfLoop_pure (by simp [mfLoopSet]) (fun rd _ => mfL1_rel rd _ _ hne) 16

theorem mainGoalL2 : MainGoalL2 fs cert fp seed s w := fun hne =>
  completeAt_of_rel_pureD mfLoop_pure (by simp [mfLoopSet]) (fun rd _ => mfL2_rel rd _ _ hne) 16

/-- **`da_list_digest` on the DA table's declared claims.** -/
theorem mainGoalDl {bytecode : List K} (hL : Limits bytecode s w) : MainGoalDl fs cert fp seed s w := by
  refine daList_completeAt fs cert fun rd h => ?_
  have h0 := mf_reads fs fp seed s w h (i := 0) (by omega)
  rw [show (hOwn seed s w).getD 0 [] = s.claims.da.flatMap daCells ++ (dPlan s w).dups.flatMap daCells
    by rw [← List.flatMap_append]; rfl] at h0
  refine ⟨s.claims.da.length, hL.daRoots.1, rfl, s.claims.da.flatMap daCells,
    mf_length_flatMap _ mf_daCells_length _, (readsAt_append'.mp h0).1,
    mf_canon_flatMap _ mf_daCells_canon _, ?_⟩
  exact congrArg digestCells (mf_da_digest s.claims.da)

/-- **`statement_digest` on the signer set's cells and the deferred claim**, a bytecode of `2^23`
words making the deferred claim `24` cells. -/
theorem mainGoalSt {bytecode : List K} (hR : NodeRel bytecode seed s w)
    (hbl : bytecode.length = 2 ^ bytecodeVars) : MainGoalSt fs cert fp seed s w := by
  have hlen : s.defer.cells.length = 24 := by
    have h1 : s.defer.bytecodePoint.length = Nat.log2 bytecode.length := hR.1
    rw [hbl, Nat.log2_two_pow] at h1
    simp [DeferredClaim.cells, h1, bytecodeVars]
  refine statement_completeAt fs cert fun rd h => ?_
  have h3 := mf_reads fs fp seed s w h (i := 3) (by omega)
  have h10 := mf_reads fs fp seed s w h (i := 10) (by omega)
  refine ⟨(digestScalars (signersDigest s.claims.xmss s.claims.sphincs)).1,
    (digestScalars (signersDigest s.claims.xmss s.claims.sphincs)).2, s.defer.cells,
    h3 0 (by simp [hOwn, digestCells]), h3 1 (by simp [hOwn, digestCells]), hlen, h10, ?_, ?_⟩
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact (digestScalars_canonical _).1 | exact (digestScalars_canonical _).2
  · exact congrArg digestCells (statementDigest_parts (digestBytes_eq_cells _)
      (digestBytes_eq_cells _) (digestBytes_eq_cells _) rfl hlen)

end
end LeanVM.Guest.B1.Main
