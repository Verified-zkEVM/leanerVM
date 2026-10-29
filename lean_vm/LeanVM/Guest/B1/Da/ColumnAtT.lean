/-
  LeanVM.Guest.B1.Da.ColumnAtT

  A column of `da_verify` placed, by a tree of its honest shape (`Budget.NodeHonest`): its node
  tree's `HeapBuf` of `4·2^L` words, its calls, and the words its loops end at.

  `da_verify` checks Benedikt Wagner's LeanDA witnesses (`Da.Witness.Opens`), as ported here.
-/

module

public import LeanVM.Guest.B1.Da.ColumnAt
public import LeanVM.Guest.B1.Da.AtT

/-!
# A column, its honest shape

`colNH fname rl gl r L`: the column's node at a valuation with `v1 = g^r` (its row loop's end),
`v3 = g^(2^L - r)` (its padding loop's end), `v13 = g^(4·2^L)` (its node tree's size) and
`v17 = v20 = 1` (its loops' starts, read by the budget's counts), its
calls `colCalls` (the vector cell, the row loop, the padding loop when `2^L > r`, the tree's
levels), its `HeapBuf`s `[4·2^L]`, no predicate on its callees. `col_completeAtT`:
`col_completeAt` (same proof) by such a tree.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd
open LeanVM.Guest.Budget (NodeHonest)
open LeanVM.Guest.B1 (CompleteAtD CompleteAtDT Returns Kid OutsOk CallsMatch RegionsOk outRegion
  DisjL Within disj_append disj_nil kidsFromIn_of_kidsD completeAt_of_rel_pureD regionsOk_of
  within_append)
open LeanVM.Guest.B1.Main (Layout MemL RegionL memL_append)

@[expose] public section

/-- The words a column's loops start and end at and its node tree's size. -/
def colQ (r L : ℕ) (σ : Val) : Prop :=
  σ (.n 1) = gen ^ r ∧ σ (.n 3) = gen ^ (2 ^ L - r) ∧ σ (.n 13) = gen ^ (4 * 2 ^ L) ∧
    σ (.n 17) = 1 ∧ σ (.n 20) = 1

/-- A column's calls. -/
def colCalls (rl gl : String) (r L : ℕ) : List Call :=
  [⟨"da_vector_cell", [.n 10], [.n 11], true⟩,
    ⟨rl, [.n 17, .n 1, .n 11, .n 7, .n 0, .n 14, .n 5], [], true⟩,
    ⟨gl, [.n 20, .n 3, .n 14, .n 1], [], decide (2 ^ L - r ≠ 0)⟩,
    ⟨dlNames[L]!, [.n 14], [.n 21, .n 22], true⟩]

/-- **A column's honest shape.** -/
def colNH (fname rl gl : String) (r L : ℕ) : Tree → Prop :=
  NodeHonest coreProgram fname (colQ r L) (fun _ => colCalls rl gl r L) (fun _ => [4 * 2 ^ L])
    (List.replicate 4 fun _ => True)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **A column is complete, placed, by a tree of its honest shape** (`colNH`). -/
theorem col_completeAtT (fs : String → ℕ) (cert : String → V → ℕ)
    (hcv : cert "da_vector_cell" (.n 1) + 256 ≤ fs "da_vector_cell")
    {fname rl gl : String} {jc jr jg : ℕ}
    (hfc : coreProgram.find? fname = some (coreProgram.getD jc default))
    (hbody : Fn.body (coreProgram.getD jc default) = colBody rl gl)
    (hpar : (coreProgram.getD jc default).params = (List.range 9).map V.n)
    (hlf : coreProgram.loop fname = false)
    (hfr : coreProgram.find? rl = some (coreProgram.getD jr default))
    (hsr : loopShapeF (coreProgram.getD jr default) rl = true)
    (hfg : coreProgram.find? gl = some (coreProgram.getD jg default))
    (hsg : loopShapeF (coreProgram.getD jg default) gl = true)
    (hrl : rl ∈ daPureSet) (hgl : gl ∈ daPureSet)
    {r L : ℕ} {syms : ℕ → ℕ → List K} {ws : ℕ → List E} {b0 j : ℕ}
    (hrowsM : ∀ rd node lv, ColMem r L syms ws rd (dvPtrsAt r L b0 (fun _ => node) (fun _ => lv)) j →
      ∀ i < r, LoopBlock rd (coreProgram.getD jr default) (gen ^ i) (gen ^ r)
        [lv, gen ^ dxB r L b0, gen ^ j, node, gen ^ dxP L b0])
    (hgapsM : ∀ rd node lv, ColMem r L syms ws rd (dvPtrsAt r L b0 (fun _ => node) (fun _ => lv)) j →
      ∀ d < 2 ^ L - r, LoopBlock rd (coreProgram.getD jg default) (gen ^ d) (gen ^ (2 ^ L - r))
        [node, gen ^ r])
    (hr1 : 1 ≤ r) (hrL : r ≤ 2 ^ L) (hL : L ≤ 10) (hwl : ∀ j, (ws j).length = 256)
    (hj : j < 128) :
    CompleteAtDT fs cert 16 fname (dvOwn r L syms ws b0)
      [gen ^ j, gen ^ r, gen ^ 2 ^ L, gen ^ (2 ^ L - r), gen ^ L, gen ^ dxP L b0, gen ^ dxT r L b0,
        gen ^ dxB r L b0, gen ^ dxC r L b0] (Returns []) (colNH fname rl gl r L) := by
  intro fp
  have hN : 2 ^ L ≤ 1024 :=
    le_trans (Nat.pow_le_pow_right (by norm_num) hL) (by norm_num)
  set N := 2 ^ L with hNd
  set nodeP := fp + fs fname with hnodeP
  set K := nodeP + 4 * N with hK
  set runP := vecRun cert K with hrunP
  set nodeC := treeCells (nodeLeaves r L syms j) L with hnodeC
  set cr := cellRoot L (nodeLeaves r L syms j) with hcr
  set Lin := dvOwn r L syms ws b0 with hLin
  set A : Layout := [(nodeP, nodeC), (runP, ws j)] with hA
  have hnodeCl : nodeC.length = 4 * N - 2 := length_treeCells (length_nodeLeaves r L syms j)
  have hN1 : 1 ≤ N := Nat.one_le_two_pow
  -- the memory the callees read
  have hCM : ∀ rd, MemL rd (Lin ++ A) →
      ColMem r L syms ws rd (dvPtrsAt r L b0 (fun _ => gen ^ nodeP) (fun _ => ofK (gpow runP))) j := by
    intro rd hm
    obtain ⟨h1, h2⟩ := memL_append.mp hm
    exact colMem_of_memL h1 (treeMem_of_reads (length_nodeLeaves r L syms j)
      (reads_of_memL h2 (b := nodeP) (xs := nodeC) (by simp [hA])))
      ((isInK_iff _).mpr ⟨_, rfl⟩) (h2 (runP, ws j) (by simp [hA]))
  -- the pure callees
  let ks : List Kid :=
    [⟨rl, true, [word 1 0 0, gen ^ r, ofK (gpow runP), gen ^ dxB r L b0, gen ^ j, gen ^ nodeP,
        gen ^ dxP L b0], Lin ++ A, Returns []⟩,
      ⟨gl, decide (N - r ≠ 0), [word 1 0 0, gen ^ (N - r), gen ^ nodeP, gen ^ r], Lin ++ A, Returns []⟩,
      ⟨dlNames[L]!, true, [gen ^ nodeP], Lin ++ A, Returns [cr.1, cr.2]⟩]
  have hok : ∀ k ∈ ks, k.taken = true → CompleteAtD fs cert 16 k.f k.Lin k.args k.Out := by
    intro k hk ht
    simp only [ks, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    · refine completeAt_of_rel_pureD daPure hrl (fun rd hm => ?_) 16
      have g := (guard_complete hfr hsr (hrowsM rd _ _ (hCM rd hm))).2
        ((one_add_gen_pow_ne (a := r) (by omega)).mpr (by omega) |> fun h => by rwa [word_one] at h)
      rwa [← word_one] at g
    · simp only [decide_eq_true_eq] at ht
      refine completeAt_of_rel_pureD daPure hgl (fun rd hm => ?_) 16
      have g := (guard_complete hfg hsg (hgapsM rd _ _ (hCM rd hm))).2
        ((one_add_gen_pow_ne (a := N - r) (by omega)).mpr ht |> fun h => by rwa [word_one] at h)
      rwa [← word_one] at g
    · refine completeAt_of_rel_pureD daPure (dlNames_mem_pure hL) (fun rd hm => ?_) 16
      rw [dlNames_get hL]
      exact colm_lev (hCM rd hm) hL
  obtain ⟨Nk, Lk, outs, hoo, hW, hD, -, hKids⟩ :=
    kidsFromIn_of_kidsD (fs := fs) (cert := cert) 16 ks hok (K + fs "da_vector_cell")
  have hl0 : outs.length = 3 := hoo.length
  obtain ⟨o1, t1, rfl, hl1⟩ := exists_of_length_succ hl0
  obtain ⟨o2, t2, rfl, hl2⟩ := exists_of_length_succ hl1
  obtain ⟨o3, t3, rfl, hl3⟩ := exists_of_length_succ hl2
  obtain rfl := List.eq_nil_of_length_eq_zero hl3
  obtain ⟨ho1, ho2, ho3, -⟩ := hoo
  have e1 : o1.1 = [] := (ho1 rfl).1
  have e3 : o3.1 = [cr.1, cr.2] := (ho3 rfl).1
  have e2 : decide (N - r ≠ 0) = true → o2.1 = [] := fun h => (ho2 h).1
  -- the size and the layout
  have hwA : Within A nodeP (4 * N + fs "da_vector_cell") := by
    intro q hq
    simp only [hA, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · simp only [hnodeCl]; omega
    · simp only [hwl j, hrunP, vecRun]; omega
  have hdA : DisjL A := List.Pairwise.cons
    (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact Or.inl (by simp only [hnodeCl, hrunP, vecRun]; omega))
    (List.pairwise_singleton _ _)
  refine ⟨fs fname + 4 * N + fs "da_vector_cell" + Nk, A ++ Lk, [], [], ⟨rfl, rfl⟩, ?_,
    by simpa using disj_append hdA hD hwA hW (by omega), fun rd hlow hm => ?_⟩
  · rw [List.nil_append, within_append]
    exact ⟨hwA.mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
  simp only [List.nil_append] at hm
  obtain ⟨hm1, hLin'⟩ := memL_append.mp hm
  obtain ⟨hmA, hLk⟩ := memL_append.mp hm1
  have hmK : MemL rd (Lin ++ A) := memL_append.mpr ⟨hLin', hmA⟩
  have hcm := hCM rd hmK
  have hct := colm_ct hcm hj
  have hholds := col_holds hfr hsr hfg hsg hL (colm_vec hcm hwl hj) (hrowsM rd _ _ hcm)
    (hgapsM rd _ _ hcm) (colm_lev hcm hL) hct.1 hct.2
  set σ := colσ (gen ^ j) r (N - r) L (gen ^ dxP L b0) (gen ^ dxT r L b0) (gen ^ dxB r L b0)
    (gen ^ dxC r L b0) (ofK (gpow runP)) (gen ^ nodeP) cr.1 cr.2 with hσ
  -- the path
  have hx : σ (.n 4) = ofK (gpow L) := by rw [← gen_pow_eq_ofK]; rfl
  have hw := walk_dispatch σ (colPre rl gl) colPost (colPre_straight rl gl) colPost_straight (.n 4)
    dlNames [.n 14] [.n 21, .n 22] [] (i := L) (by simp [dlNames]; omega) (by simp [dlNames]) hx
  rw [← colBody_split, ← hbody] at hw
  set es := (colPre rl gl).flatMap (Main.slEvs σ) ++
    .call dlNames[L]! [.n 14] [.n 21, .n 22] :: colPost.flatMap (Main.slEvs σ) with hes
  have hev := holds_of_holdsList hfc (by rw [hbody]; exact hholds) hw
  obtain ⟨hpd, hpa, hpad, hpc⟩ := Main.straight_parts σ _ (colPre_straight rl gl)
  obtain ⟨hqd, hqa, hqad, hqc⟩ := Main.straight_parts σ _ colPost_straight
  have h13 : σ (.n 13) = gen ^ (4 * N) := by
    show gen ^ N * gen ^ N * (gen ^ N * gen ^ N) = _; ring
  have hal : allocs σ es = [4 * N] := by
    rw [hes, allocs_append, show allocs σ (.call dlNames[L]! [.n 14] [.n 21, .n 22] ::
      colPost.flatMap (Main.slEvs σ)) = allocs σ (colPost.flatMap (Main.slEvs σ)) from rfl, hpa, hqa,
      show (colPre rl gl).filterMap Main.Stmt.allocSz = [(.n 14, .inr (.n 13))] from rfl,
      show colPost.filterMap Main.Stmt.allocSz = [] from rfl]
    simp only [List.map_cons, List.map_nil, Sum.elim_inr, h13,
      logG_gen_pow (show 4 * N < 2 ^ 64 - 1 by omega), List.append_nil]
  have h16 : decide (σ (.n 16) ≠ 0) = true :=
    decide_eq_true ((one_add_gen_pow_ne (a := r) (by omega)).mpr (by omega))
  have h19 : decide (σ (.n 19) ≠ 0) = decide (N - r ≠ 0) :=
    decide_eq_decide.mpr (one_add_gen_pow_ne (a := N - r) (by omega))
  have hcalls : calls es = [⟨"da_vector_cell", [.n 10], [.n 11], true⟩,
      ⟨rl, [.n 17, .n 1, .n 11, .n 7, .n 0, .n 14, .n 5], [], true⟩,
      ⟨gl, [.n 20, .n 3, .n 14, .n 1], [], decide (N - r ≠ 0)⟩,
      ⟨dlNames[L]!, [.n 14], [.n 21, .n 22], true⟩] := by
    rw [hes, calls_append, show calls (.call dlNames[L]! [.n 14] [.n 21, .n 22] ::
      colPost.flatMap (Main.slEvs σ)) = ⟨dlNames[L]!, [.n 14], [.n 21, .n 22], true⟩ ::
        calls (colPost.flatMap (Main.slEvs σ)) from rfl, hpc, hqc,
      show (colPre rl gl).filterMap Main.Stmt.callS = [(none, "da_vector_cell", [.n 10], [.n 11]),
        (some (.n 16), rl, [.n 17, .n 1, .n 11, .n 7, .n 0, .n 14, .n 5], []),
        (some (.n 19), gl, [.n 20, .n 3, .n 14, .n 1], [])] from rfl,
      show colPost.filterMap Main.Stmt.callS = [] from rfl]
    simp only [List.map_cons, List.map_nil, Main.mkCall, h16, h19, List.nil_append, List.cons_append]
  -- the own data
  have hown : ∀ i, nodeP ≤ i → i < nodeP + 4 * N →
      ownData cert fp (fp + fs fname) fname [4 * N] es i :=
    fun i h1 h2 => Or.inl ⟨(4 * N, nodeP), List.Mem.head _, h1, h2⟩
  have hcdR : ∀ k < 256, RegionL Lin (dxC r L b0 + k) := fun k hk =>
    regionL_of_mem (L := Lin) (xs := cdCells ws) (by
      rw [hLin, dvOwn_eq]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      (by rw [cdCells_length]; exact hk)
  have hctR : ∀ k < 510, RegionL Lin (dxT r L b0 + k) := fun k hk =>
    regionL_of_mem (L := Lin) (xs := treeCells (colLeaves r L syms) 7) (by
      rw [hLin, dvOwn_eq]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))
      (by rw [length_treeCells length_colLeaves]; omega)
  -- the walk
  set Run : ℕ → Prop := fun i => runP ≤ i ∧ i < runP + 256 with hRun
  have h := relAtInWT_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
    (R := RegionL Lin) (D := RegionL []) (fp := fp) (N := fs "da_vector_cell" + Nk)
    (Dk := fun i => ((fun _ => False) i ∨
      ((⟨"da_vector_cell", [.n 10], [.n 11], true⟩ : Call).taken = true ∧ Run i)) ∨
      outRegion ks [o1, o2, o3] i)
    (args := [gen ^ j, gen ^ r, gen ^ 2 ^ L, gen ^ (2 ^ L - r), gen ^ L, gen ^ dxP L b0,
      gen ^ dxT r L b0, gen ^ dxB r L b0, gen ^ dxC r L b0])
    coreProgram_wf hfc (Or.inl hlf) (by rw [hpar]; rfl) hw rfl hev
    (by
      rw [hal, hes, allocDsts_append, show allocDsts (.call dlNames[L]! [.n 14] [.n 21, .n 22] ::
        colPost.flatMap (Main.slEvs σ)) = allocDsts (colPost.flatMap (Main.slEvs σ)) from rfl, hpd, hqd,
        show (colPre rl gl).filterMap Main.Stmt.allocSz = [(.n 14, .inr (.n 13))] from rfl,
        show colPost.filterMap Main.Stmt.allocSz = [] from rfl]
      simp only [List.map_cons, List.map_nil, List.append_nil, bases]
      rw [← gen_pow_eq_ofK]; rfl)
    (fun q hq => by
      rw [hes, addrs_append, show addrs (.call dlNames[L]! [.n 14] [.n 21, .n 22] ::
        colPost.flatMap (Main.slEvs σ)) = addrs (colPost.flatMap (Main.slEvs σ)) from rfl, hpad, hqad,
        show (colPre rl gl).filterMap Main.Stmt.addrS = [] from rfl,
        show colPost.filterMap Main.Stmt.addrS = [] from rfl] at hq
      simp at hq)
    [] ?_ ?_ (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq)
  · have h' := relAtInT_nodeHonest_true (Q := colQ r L) (cs := fun _ => colCalls rl gl r L)
      (bs := fun _ => [4 * 2 ^ L]) (k := 4) h hfc hw ⟨rfl, rfl, h13, word_one, word_one⟩ hcalls hal (by simp [colCalls])
    rw [hal] at h'
    simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at h'
    rwa [show fs fname + 4 * N + (fs "da_vector_cell" + Nk) =
      fs fname + 4 * N + fs "da_vector_cell" + Nk by omega] at h'
  · apply kidsFromInT_nil_of
    rw [hcalls, hal]
    rw [List.sum_cons, List.sum_nil, Nat.add_zero]
    have h10 : σ (.n 10) = gen ^ (dxC r L b0 + 2 * j) := by
      show gen ^ dxC r L b0 * (gen ^ j * gen ^ j) = _
      rw [gen_sq, ← pow_add]
    have hdig : ReadsAt rd (gen ^ (dxC r L b0 + 2 * j))
        (digestCells (keccak256 ((ws j).flatMap Node.eBytes))) := by
      have := Main.readsAt_flatMap_of (f := fun j => digestCells (colD ws j)) (w := 2) (List.range 128)
        (fun _ _ => rfl) hcm.cd j (by simpa using hj)
      simp only [List.getElem_range] at this
      rw [pow_add]
      exact this
    refine ⟨fs "da_vector_cell", Nk, RegionL Lin, Run, rfl, fun i hi => Or.inl (Or.inl hi), ?_, ?_⟩
    · show RelAtIn coreProgram fs cert rd (RegionL Lin) Run K (fs "da_vector_cell") "da_vector_cell"
        [σ (.n 10)] [σ (.n 11)]
      rw [h10]
      exact vec_at fs cert (hwl j) (hmA (runP, ws j) (by simp [hA])) hdig
        ⟨hcdR (2 * j) (by omega), by rw [Nat.add_assoc]; exact hcdR (2 * j + 1) (by omega)⟩
    · refine hKids rd σ _ _ _ ?_ hlow hLk ?_ (regionsOk_of fun k hk _ i hi => ?_)
      · exact ⟨rfl, rfl, fun _ => ⟨rfl, by rw [e1]; rfl⟩, rfl, rfl,
          fun ht => ⟨rfl, by rw [e2 ht]; rfl⟩, rfl, rfl, fun _ => ⟨rfl, by rw [e3]; rfl⟩, trivial⟩
      · intro q hq
        simp only [B1.Kid.lins, ks, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          List.mem_append] at hq
        rcases hq with hq | hq | hq <;> exact hmK q (List.mem_append.mpr hq)
      · simp only [ks, List.mem_cons, List.not_mem_nil, or_false] at hk
        have hkL : k.Lin = Lin ++ A := by rcases hk with rfl | rfl | rfl <;> rfl
        rw [hkL] at hi
        obtain ⟨q, hq, h1, h2⟩ := hi
        rcases List.mem_append.mp hq with hq | hq
        · exact Or.inl (Or.inl ⟨q, hq, h1, h2⟩)
        · simp only [hA, List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl
          · exact Or.inl (Or.inr (hown i h1 (by simp only [hnodeCl] at h2; omega)))
          · exact Or.inr (Or.inr ⟨rfl, h1, by simpa [hwl j] using h2⟩)
  · intro A' hA'
    rw [hes, loadAddrs_append, show loadAddrs σ (.call dlNames[L]! [.n 14] [.n 21, .n 22] ::
      colPost.flatMap (Main.slEvs σ)) = loadAddrs σ (colPost.flatMap (Main.slEvs σ)) from rfl,
      B1.loadAddrs_straight σ _ (colPre_straight rl gl), B1.loadAddrs_straight σ _ colPost_straight,
      show (colPre rl gl).filterMap B1.Stmt.loadS = [] from rfl,
      show colPost.filterMap B1.Stmt.loadS = [(.n 24, 0), (.n 24, 1)] from rfl] at hA'
    have g24 : σ (.n 24) = gen ^ (dxT r L b0 + 2 * j) := by
      show gen ^ dxT r L b0 * (gen ^ j * gen ^ j) = _
      rw [gen_sq, ← pow_add]
    simp only [List.map_cons, List.map_nil, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hA'
    rcases hA' with rfl | rfl
    · exact ⟨_, by rw [g24, limb0_gen_pow_mul]; rfl, Or.inr (Or.inl (hctR (2 * j) (by omega)))⟩
    · refine ⟨_, by rw [g24, limb0_gen_pow_mul], Or.inr (Or.inl ?_)⟩
      rw [Nat.add_assoc]; exact hctR (2 * j + 1) (by omega)


end
end LeanVM.Guest.B1.Da
