/-
  LeanVM.Guest.B1.Comp.Digest.SmallLoads

  `statement_digest` and `cover_da_root` complete over a completeness model in the uniform placed
  form by trees loading the words their preconditions name (`CompleteRelBST`).
-/

module

public import LeanVM.Guest.B1.Comp.Digest.LoadsT
public import LeanVM.Guest.B1.Comp.Digest.SmallAtC

/-!
# `statement_digest` and `cover_da_root`, their trees loading what they read

`SmallAtC.lean`'s `sd_completeRelBS` and `cover_completeRelBS` with the placed tree loading the
words of the precondition:

* `SdLoadsQ sig cells`: the signers' digest's two cells at `sigp` and the deferred cells `cells`
  at `dp` (`SdPreAtC`'s `LoadHolds` and `CellsAt`); every valid tree loads them
  (`sd_tree_loads`: the body is straight-line, each word read by a load of the pointer
  parameter), so `sd_completeRelBST` is `sd_completeRelBS` with `CompleteAtBS.toBST_valid`;
* `CoverLoadsQ i`: the mark at `cover·g^i` and the four root cells at `roots·g^(4i)`
  (`CoverPreAt i`'s words); the slot is hinted, so the honest run's tree loads them
  (`cover_completeRelBST`, `completeAtS_leafBT`).

`…_completeRelBST.toBS` gives back `sd_completeRelBS`, `cover_completeRelBS`.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.Value LeanVM.Node LeanVM.E2E.Complete
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1 (LowDef CompleteAtBS CompleteRelBS CompleteRelBST CompleteAtBST Returns LoadsAt
  LoadsCells LoadsAll CellsEq loadEq_of_load nodeS_straight mem_loadEqns_node mem_slEvs_of
  completeRel_casesBST)
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-! ## `statement_digest` -/

/-- **What `statement_digest`'s tree loads**: the signers' digest's cells at `sigp` and the
deferred cells at `dp` (`SdPreAtC`'s words). -/
def SdLoadsQ (sig : Digest) (cells : List E) : List E → List E → ℕ → Reader → Tree → Prop
  | [_, _, sigp, _, _, dp], _, _, _, t => LoadsAt t sigp 0 (digestScalars sig).1 ∧
      LoadsAt t sigp 1 (digestScalars sig).2 ∧ LoadsCells t dp cells
  | _, _, _, _, _ => True

/-- `statement_digest`'s atoms (`sdBody`). -/
def sdAtomList : List Atom :=
  ([.copy (.n 6) (.n 0), .copy (.n 7) (.n 1), .load (.n 8) (.n 2) 0, .load (.n 9) (.n 2) 1,
      .copy (.n 10) (.n 3), .copy (.n 11) (.n 4)] : List Atom) ++
    (List.range 26).flatMap sdPair ++ sdLast ++
    ([.const (.n 740) (word 0 0 0), .const (.n 741) (word 13503953895743350343 11912009169889063794 0),
      .const (.n 742) (word 11170449402626986623 6620516960021240235 0)] : List Atom) ++
    (List.range 22).flatMap sdBlk ++
    ([.copy (.n 809) (.n 807), .copy (.n 810) (.n 808)] : List Atom)

theorem sdBody_atoms : sdBody = sdAtomList.map .atom ++ [.ret [.n 809, .n 810]] := rfl

theorem sdAtoms_straight : (sdAtomList.map Stmt.atom).all Main.Stmt.straight = true :=
  List.all_eq_true.mpr fun s hs => by obtain ⟨a, -, rfl⟩ := List.mem_map.mp hs; rfl

/-- Each deferred cell `k < 53` is read by a load through `dp` (value `5`) at offset `k`. -/
theorem sd_load_mem (k : ℕ) (hk : k < 53) : ∃ d, Atom.load d (.n 5) k ∈ sdAtomList := by
  have hin : ∀ a, a ∈ (List.range 26).flatMap sdPair ++ sdLast → a ∈ sdAtomList := fun a ha => by
    rcases List.mem_append.mp ha with h | h
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_right _ h))))
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ h)))
  rcases (show k < 52 ∨ k = 52 by omega) with h | rfl
  · obtain ⟨p, rfl | rfl⟩ : ∃ p, k = 2 * p ∨ k = 2 * p + 1 := ⟨k / 2, by omega⟩
    · exact ⟨pv p 0, hin _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨p, List.mem_range.mpr (by omega),
        List.mem_cons_self⟩))⟩
    · exact ⟨pv p 1, hin _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨p, List.mem_range.mpr (by omega),
        List.mem_cons_of_mem _ List.mem_cons_self⟩))⟩
  · exact ⟨.n 714, hin _ (List.mem_append_right _ List.mem_cons_self)⟩

/-- **Every valid tree of `statement_digest` loads the words it reads**: the cells `sigp` holds
at offsets `0`, `1` and the cells `dp` holds (at most 53). -/
theorem sd_tree_loads {S : BlakeSem} {rd : Reader} {t : Tree} {seed0 seed1 sigp da0 da1 dp v0 v1 : E}
    {cells rets : List E} (hlen : cells.length ≤ 53) (h0 : LoadHolds rd sigp 0 v0)
    (h1 : LoadHolds rd sigp 1 v1) (hc : CellsAt rd dp cells) (hn : t.name = "statement_digest")
    (hv : t.ValidB S coreProgram rd [seed0, seed1, sigp, da0, da1, dp] rets) :
    LoadsAt t sigp 0 v0 ∧ LoadsAt t sigp 1 v1 ∧ LoadsCells t dp cells := by
  obtain ⟨σ, bufs, kids, rfl, hp, hw, hes, -⟩ := nodeS_straight (S := S) find_statement_digest
    (pre := sdAtomList.map Stmt.atom) (vs := [.n 809, .n 810]) sdBody_atoms sdAtoms_straight hn hv
  change [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5)] = _ at hp
  simp only [List.cons.injEq] at hp
  obtain ⟨-, -, h2, -, -, h5, -⟩ := hp
  have hm : ∀ a ∈ sdAtomList, Ev.atom a ∈ (sdAtomList.map Stmt.atom).flatMap (Main.slEvs σ) :=
    fun a ha => mem_slEvs_of (List.mem_map_of_mem ha)
  have hfirst : ∀ a, a ∈ ([.copy (.n 6) (.n 0), .copy (.n 7) (.n 1), .load (.n 8) (.n 2) 0,
      .load (.n 9) (.n 2) 1, .copy (.n 10) (.n 3), .copy (.n 11) (.n 4)] : List Atom) → a ∈ sdAtomList :=
    fun a ha => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ ha))))
  refine ⟨mem_loadEqns_node find_statement_digest hw
      (loadEq_of_load hes (hm _ (hfirst _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self)))) h2 h0),
    mem_loadEqns_node find_statement_digest hw (loadEq_of_load hes (hm _ (hfirst _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))) h2 h1),
    fun k hk => ?_⟩
  obtain ⟨d, hd⟩ := sd_load_mem k (by omega)
  exact mem_loadEqns_node find_statement_digest hw (loadEq_of_load hes (hm _ hd) h5 (hc k hk))

/-- **`statement_digest` is complete over the model, uniformly placed, by trees loading its
reads** (`sd_completeRelBS`). -/
theorem sd_completeRelBST {CM : CompModel} (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ}
    (sig : Digest) (cells : List E) {B : ℕ}
    (hB : TotalLeB CM.sem coreProgram fs "statement_digest" fun _ => B) :
    CompleteRelBST CM.sem fs cert κ "statement_digest" (SdPreAtC CM.H sig cells) B (SdLoadsQ sig cells) := by
  intro args rets Lin hpre
  refine (sd_completeRelBS fs cert (κ := κ) sig cells hB args rets Lin hpre).toBST_valid ?_
  intro fp rd t rets' Lout ho hl hL hn hv
  obtain ⟨rfl, -⟩ := ho
  obtain ⟨seed0, seed1, sigp, da0, da1, dp, d0, d1, rfl, rfl⟩ := sdPreAtC_shape (hpre rd hl hL)
  obtain ⟨seed, da, hlen, -, hs0, hs1, -, hc, -⟩ := hpre rd hl hL
  exact sd_tree_loads (by rw [hlen]) hs0 hs1 hc hn hv

/-! ## `cover_da_root` -/

/-- **What `cover_da_root`'s tree loads at the slot `i`**: the mark at `cover·g^i` and the root's
four cells at `roots·g^(4i)` (`CoverPreAt i`'s words). -/
def CoverLoadsQ (i : ℕ) : List E → List E → ℕ → Reader → Tree → Prop
  | [roots, cover, _, mark], [r0, r1, r2, r3], _, _, t => LoadsAt t (cover * gen ^ i) 0 mark ∧
      LoadsCells t (roots * gen ^ (4 * i)) [r0, r1, r2, r3]
  | _, _, _, _, _ => True

/-- **`cover_da_root` is complete under any semantics, uniformly placed, by a tree loading its
reads** (`cover_completeRelBS`), at the slot `i`, on a memory defined below `2^κ`, `κ ≥ 16`. -/
theorem cover_completeRelBST {S : BlakeSem} (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ}
    (hκ : 16 ≤ κ) (i : ℕ) :
    CompleteRelBST S fs cert κ "cover_da_root" (CoverPreAt i) (fs "cover_da_root") (CoverLoadsQ i) := by
  refine completeRel_casesBST fun args rets Lin hpre rd1 hl1 hL1 => ?_
  obtain ⟨roots, cover, nslots, mark, r0, r1, r2, r3, rfl, rfl⟩ := coverPreAt_shape (hpre rd1 hl1 hL1)
  obtain ⟨M, hM, hi, rfl, -, -⟩ := hpre rd1 hl1 hL1
  have hpre' : ∀ rd, LowDef κ rd → MemL rd Lin →
      LoadHolds rd (cover * gen ^ i) 0 mark ∧ CellsAt rd (roots * gen ^ (4 * i)) [r0, r1, r2, r3] := by
    intro rd hl hL
    obtain ⟨M', -, -, -, h1, h2⟩ := hpre rd hl hL
    exact ⟨h1, h2⟩
  obtain ⟨im, him, hRm⟩ := forced_load (fun rd hl hL => (hpre' rd hl hL).1) hl1 hL1
  have hFc : ∀ r, ∃ ic, r < 4 → (roots * gen ^ (4 * i)).limb 0 * gpow r = gpow ic ∧ RegionL Lin ic := by
    intro r
    by_cases hr : r < 4
    · obtain ⟨ic, h⟩ := forced_load (p := roots * gen ^ (4 * i)) (k := r)
        (v := [r0, r1, r2, r3][r]'(by simp; omega))
        (fun rd hl hL => (hpre' rd hl hL).2 r (by simp; omega)) hl1 hL1
      exact ⟨ic, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hr⟩
  choose cidx hcidx using hFc
  have h := LeanVM.Guest.B1.completeAtS_leafBT (S := S) (fs := fs) (cert := cert) find_cover_da_root
    (by rw [Program.loop_of_find? find_cover_da_root]; decide +kernel) κ Lin
    [roots, cover, gen ^ M, mark] [r0, r1, r2, r3] [] (fun _ => [])
    (fun _ => List.Forall₂.nil)
    (fun q => q = ((cover * gen ^ i).limb 0 * gpow 0, mark) ∨ CellsEq (roots * gen ^ (4 * i)) [r0, r1, r2, r3] q)
    (fun fp rd hl _ hL => ?_)
  · refine (h.bmono (by simp)).qmono fun fp rd t ht => ?_
    show LoadsAt t (cover * gen ^ i) 0 mark ∧ LoadsCells t (roots * gen ^ (4 * i)) [r0, r1, r2, r3]
    exact ⟨ht.at (Or.inl rfl), ht.cells fun q hq => Or.inr hq⟩
  obtain ⟨hmark, hroot⟩ := hpre' rd hl hL
  have hroot0 := hroot
  obtain ⟨t1, t2, l1, hk, l2⟩ := rangeCheck_complete_low (fun j hj => hl j (lt_of_lt_of_le hj
    (Nat.pow_le_pow_right (by norm_num) hκ))) (e := i) (e' := M - 1 - i) (by omega) (by omega)
  rw [cellsAt_four] at hroot
  have hk' : gen ^ M * word 9223372036854775821 0 0 = gen ^ i * gen ^ (M - 1 - i) := by
    rw [← hk, show i + (M - 1 - i) = M - 1 by omega,
      show gen ^ M = gen ^ (M - 1) * gen by rw [← pow_succ]; congr 1; omega, mul_assoc,
      mul_comm gen, ginv_mul_gen, mul_one]
  set σ := listVal [roots, cover, gen ^ M, mark, gen ^ i, word 9223372036854775821 0 0,
    gen ^ M * word 9223372036854775821 0 0, gen ^ (M - 1 - i), t1, t2, cover * gen ^ i,
    gen ^ i * gen ^ i, gen ^ i * gen ^ i * (gen ^ i * gen ^ i),
    roots * (gen ^ i * gen ^ i * (gen ^ i * gen ^ i)), r0, r1, r2, r3] with hσ
  have hroot' := hroot
  rw [pow_mul', ← gen_pow_four_mul] at hroot'
  have hH : ∀ a ∈ coverAtoms, a.HoldsB S rd σ := by
    simp only [coverAtoms, List.forall_mem_cons, forall_mem_nil_iff, Atom.HoldsB, hσ, listVal,
      List.getD_cons_succ, List.getD_cons_zero, true_and, and_true]
    exact ⟨⟨l1, hk', l2⟩, hmark, hroot'.1, hroot'.2.1, hroot'.2.2.1, hroot'.2.2.2⟩
  have hes : ∀ e ∈ coverAtoms.map Ev.atom, e.HoldsB S rd σ := fun e he => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    exact hH a ha
  have g13 : σ (.n 13) = roots * gen ^ (4 * i) := by
    show roots * (gen ^ i * gen ^ i * (gen ^ i * gen ^ i)) = _
    rw [pow4_eq _ _ rfl]
  refine ⟨σ, _, [.n 14, .n 15, .n 16, .n 17], rfl, by rw [coverBody_eq]; exact walk_atoms _ _ _, rfl,
    hes, calls_atoms _, by rw [addrs_atoms]; rfl, allocs_atoms _ (by decide),
    by rw [allocDsts_atoms (by decide)]; rfl, fun A hA => ?_, fun q hq => ?_⟩
  · rw [loadAddrs_atoms, show coverAtoms.filterMap atomLoad? = [(.n 10, 0), (.n 13, 0), (.n 13, 1),
      (.n 13, 2), (.n 13, 3)] from rfl] at hA
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
    rcases hA with rfl | rfl | rfl | rfl | rfl
    · exact ⟨im, him, Or.inr hRm⟩
    · exact ⟨_, by rw [g13]; exact (hcidx 0 (by omega)).1, Or.inr (hcidx 0 (by omega)).2⟩
    · exact ⟨_, by rw [g13]; exact (hcidx 1 (by omega)).1, Or.inr (hcidx 1 (by omega)).2⟩
    · exact ⟨_, by rw [g13]; exact (hcidx 2 (by omega)).1, Or.inr (hcidx 2 (by omega)).2⟩
    · exact ⟨_, by rw [g13]; exact (hcidx 3 (by omega)).1, Or.inr (hcidx 3 (by omega)).2⟩
  · rcases hq with rfl | ⟨k, hk, rfl⟩
    · exact loadEq_of_load (d := .n 3) (p := .n 10) hes (List.mem_map_of_mem (by simp [coverAtoms]))
        (show σ (.n 10) = cover * gen ^ i from rfl) hmark
    · have hl := hroot0 k hk
      have hmem : ∀ k < 4, Ev.atom (.load (.n (14 + k)) (.n 13) k) ∈ coverAtoms.map Ev.atom := by
        intro k hk
        refine List.mem_map_of_mem ?_
        rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;>
          simp [coverAtoms]
      exact loadEq_of_load hes (hmem k (by simpa using hk)) g13 hl

/-- `cover_completeRelBS`, forgetting the loads. -/
theorem cover_completeRelBS_of_BST {S : BlakeSem} (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ}
    (hκ : 16 ≤ κ) (i : ℕ) :
    CompleteRelBS S fs cert κ "cover_da_root" (CoverPreAt i) (fs "cover_da_root") :=
  (cover_completeRelBST fs cert hκ i).toBS

/-- `sd_completeRelBS`, forgetting the loads. -/
theorem sd_completeRelBS_of_BST {CM : CompModel} (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ}
    (sig : Digest) (cells : List E) {B : ℕ}
    (hB : TotalLeB CM.sem coreProgram fs "statement_digest" fun _ => B) :
    CompleteRelBS CM.sem fs cert κ "statement_digest" (SdPreAtC CM.H sig cells) B :=
  (sd_completeRelBST fs cert sig cells hB).toBS

end
end LeanVM.Guest.B1.Digest
