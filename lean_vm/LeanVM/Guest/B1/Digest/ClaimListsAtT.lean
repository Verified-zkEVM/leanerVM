/-
  LeanVM.Guest.B1.Digest.ClaimListsAtT

  `claim_list_digest` and `child_claim_list_digest` in the uniform placed form by trees of honest
  shape (`Budget.NodeHonest`): the node's valuation pins the words that end `__loop16` / `__loop17`
  and size the chain buffer, its calls and `HeapBuf` are the honest ones.
-/

module

public import LeanVM.Guest.B1.Digest.ChildListAt
public import LeanVM.Guest.B1.Main.NodeHonestAt

/-!
# The claim lists, by trees of honest shape

`clQ n σ`: the list's length `g^n` at `v1`; when `n ≠ 0`, `list_split`'s returns `g^(n / 17)`,
`g^(n % 17)` at `v23`, `v24` (the first ends `__loop16`), the chain buffer's size
`g^(13 (n / 17 + 1))` at `v31`, `__loop16`'s start `1` at `v48`. `clCalls n`: the calls (none for
the empty list; `list_split`, `__loop16` when `n / 17 ≠ 0`, `claim_list_last__L{n % 17}`).
`clBufs n`: the chain buffer (none for the empty list). `clTs`: no constraint on the callees.
`ccQ`, `ccCalls`: the same for `child_claim_list_digest` (`v5`, `v27`, `v28`, `v35`, `v52`;
`__loop17`). `claim_list_digest_completeAtT`, `child_claim_list_digest_completeAtT`: the placed
completeness (same proofs as `claim_list_digest_completeAt`, `child_claim_list_digest_completeAt`)
by trees of that shape.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1 (CompleteAtD CompleteAtDT KidsDT kidsFromInT_of_kidsDT Returns Kid DisjL Within
  disj_append completeAt_of_rel_pureD regionsOk_of within_append bufL bufL_within bufL_disj
  bufL_region LowDef)
open LeanVM.Guest.B1.Main (Layout MemL RegionL memL_append)
open LeanVM.Guest.B1.Da (SlOk slEvs_holds exists_of_length_succ limb0_gen_pow_mul reads_of_memL
  regionL_of_mem)
open LeanVM.Guest.Budget (NodeHonest)

@[expose] public section

/-- `claim_list_digest`'s words that end its loop and size its buffer. -/
def clQ (n : ℕ) (σ : Val) : Prop :=
  σ (.n 1) = gen ^ n ∧ (n ≠ 0 → σ (.n 23) = gen ^ (n / 17) ∧ σ (.n 24) = gen ^ (n % 17) ∧
    σ (.n 31) = gen ^ (13 * (n / 17 + 1)) ∧ σ (.n 48) = 1)

/-- `claim_list_digest`'s calls. -/
def clCalls (n : ℕ) (_ : Val) : List Call :=
  if n = 0 then [] else
    [⟨"list_split", [.n 1], [.n 23, .n 24], true⟩,
      ⟨"__loop16", [.n 48, .n 23, .n 32, .n 0], [], decide (n / 17 ≠ 0)⟩,
      ⟨clNames[n % 17]!, [.n 54, .n 62], [.n 63, .n 64], true⟩]

/-- The claim lists' `HeapBuf`: the chain buffer. -/
def clBufs (n : ℕ) (_ : Val) : List ℕ := if n = 0 then [] else [13 * (n / 17 + 1)]

/-- No constraint on the claim lists' callees. -/
def clTs : List (Tree → Prop) := [fun _ => True, fun _ => True, fun _ => True]

/-- `child_claim_list_digest`'s words that end its loop and size its buffer. -/
def ccQ (n : ℕ) (σ : Val) : Prop :=
  σ (.n 5) = gen ^ n ∧ (n ≠ 0 → σ (.n 27) = gen ^ (n / 17) ∧ σ (.n 28) = gen ^ (n % 17) ∧
    σ (.n 35) = gen ^ (13 * (n / 17 + 1)) ∧ σ (.n 52) = 1)

/-- `child_claim_list_digest`'s calls. -/
def ccCalls (n : ℕ) (_ : Val) : List Call :=
  if n = 0 then [] else
    [⟨"list_split", [.n 5], [.n 27, .n 28], true⟩,
      ⟨"__loop17", [.n 52, .n 27, .n 36, .n 0, .n 1, .n 2, .n 3, .n 4], [], decide (n / 17 ≠ 0)⟩,
      ⟨cclNames[n % 17]!, [.n 58, .n 0, .n 1, .n 64, .n 3, .n 4], [.n 65, .n 66], true⟩]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **`claim_list_digest` is complete, placed, by a tree of honest shape**: `n < 17 · 2^16` canonical claims' cells at `g^eP`
among the caller's words, its chain buffer after its frame holding the states after each group;
it returns their digest's cells. -/
theorem claim_list_digest_completeAtT (fs : String → ℕ) (cert : String → V → ℕ) {Lin : Main.Layout}
    {eP n : ℕ} {cells : List E} (hn : n < claimGroup * maxKeys) (hl : cells.length = 4 * n)
    (hc : AllCanonical cells) (hLe : ∀ rd, MemL rd Lin → ReadsAt rd (gen ^ eP) cells)
    (hLr : ∀ k < cells.length, RegionL Lin (eP + k)) :
    CompleteAtDT fs cert 16 "claim_list_digest" Lin [gen ^ eP, gen ^ n]
      (Returns (digestCells (keccak256 (cellsBytes cells))))
      (NodeHonest coreProgram "claim_list_digest" (clQ n) (clCalls n) (clBufs n) clTs) := by
  intro fp
  simp only [claimGroup, maxKeys] at hn
  have mH : ∀ s ∈ clHead, isAtomS s = true := by decide
  have mTl : ∀ s ∈ clTail, isAtomS s = true := by decide
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · -- the empty list
    have hcl : cells = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst hcl
    refine ⟨fs "claim_list_digest", [], _, [], ⟨rfl, rfl⟩, fun q hq => by simp at hq, B1.disj_nil,
      fun rd hlow hm => ?_⟩
    obtain ⟨hat, e0, e1, h30, h3, hret⟩ := clz_core (rd := rd) (gen ^ eP)
    set σ := clzσ rd (gen ^ eP) with hσ
    have hb : (if σ (.n 3) = 0 then walk σ cl23Zero else walk σ cl23Else) =
        .fall (cl23Zero.flatMap (Main.slEvs σ)) := by
      simp only [h30, ↓reduceIte]; exact walk_straight_fall σ _ cl23Zero_straight
    have hw := walk_ite σ clTail clTail_straight (.n 3) cl23Zero cl23Else [.n 65, .n 66] _ hb
      clHead clHead_straight
    rw [← cl_body] at hw
    set es := clHead.flatMap (Main.slEvs σ) ++ .inK (.n 3) ::
      (cl23Zero.flatMap (Main.slEvs σ) ++ clTail.flatMap (Main.slEvs σ)) with hes
    have hmZ : ∀ s ∈ clHead ++ cl23Zero ++ clTail, ∀ a, s = .atom a → a.Holds rd σ := by
      intro s hs a rfl
      refine hat a (cl_mem_atoms ?_)
      unfold clZEval
      simp only [List.mem_append] at hs ⊢
      rcases hs with (hs | hs) | hs
      · exact Or.inl (Or.inl (Or.inl hs))
      · exact Or.inl (Or.inl (Or.inr hs))
      · exact Or.inr hs
    have hev : ∀ e ∈ es, e.Holds rd σ := by
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact slEvs_holds (fun s hs => slOk_atomS (mH s hs) (hmZ s (by simp [hs]))) e he
      rcases List.mem_cons.mp he with rfl | he
      · show IsInK (σ (.n 3)); rw [h3]; exact gen_pow_add_isInK 0 0
      rcases List.mem_append.mp he with he | he
      · exact slEvs_holds (fun s hs => slOk_atomS (List.all_eq_true.mp cl23Zero_atoms s hs)
          (hmZ s (by simp [hs]))) e he
      · exact slEvs_holds (fun s hs => slOk_atomS (mTl s hs) (hmZ s (by simp [hs]))) e he
    obtain ⟨hhd, hha, hhad, hhc⟩ := Main.straight_parts σ _ clHead_straight
    obtain ⟨hzd, hza, hzad, hzc⟩ := Main.straight_parts σ _ cl23Zero_straight
    obtain ⟨htd, hta, htad, htc⟩ := Main.straight_parts σ _ clTail_straight
    obtain ⟨z1, z2, z3, z4⟩ := cl23Zero_parts
    have hal : allocs σ es = [] := by
      rw [hes, allocs_append, show allocs σ (.inK (.n 3) :: (cl23Zero.flatMap (Main.slEvs σ) ++
        clTail.flatMap (Main.slEvs σ))) = allocs σ (cl23Zero.flatMap (Main.slEvs σ) ++
        clTail.flatMap (Main.slEvs σ)) from rfl, allocs_append, hha, hza, hta, z1]
      rfl
    have h := relAtInWT_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
      (R := RegionL Lin) (D := RegionL []) (Dk := fun _ => False) (N := 0) (fp := fp)
      (args := [gen ^ eP, gen ^ 0]) (rets := digestCells (keccak256 (cellsBytes [])))
      coreProgram_wf find_claim_list_digest (Or.inl cl_loop) (by rw [cl_param, e0, e1]) hw hret hev
      (by
        rw [hal, hes, allocDsts_append, show allocDsts (.inK (.n 3) :: (cl23Zero.flatMap
          (Main.slEvs σ) ++ clTail.flatMap (Main.slEvs σ))) = allocDsts (cl23Zero.flatMap
          (Main.slEvs σ) ++ clTail.flatMap (Main.slEvs σ)) from rfl, allocDsts_append, hhd, hzd, htd, z1]
        rfl)
      (fun q hq => by
        rw [hes, addrs_append, show addrs (.inK (.n 3) :: (cl23Zero.flatMap (Main.slEvs σ) ++
          clTail.flatMap (Main.slEvs σ))) = addrs (cl23Zero.flatMap (Main.slEvs σ) ++
          clTail.flatMap (Main.slEvs σ)) from rfl, addrs_append, hhad, hzad, htad, z2] at hq
        simp [clHead, clTail, Main.Stmt.addrS] at hq)
      clTs
      (by
        rw [hes, calls_append, show calls (.inK (.n 3) :: (cl23Zero.flatMap (Main.slEvs σ) ++
          clTail.flatMap (Main.slEvs σ))) = calls (cl23Zero.flatMap (Main.slEvs σ) ++
          clTail.flatMap (Main.slEvs σ)) from rfl, calls_append, hhc, hzc, htc, z3]
        exact ⟨rfl, fun _ h => h⟩)
      (fun A hA => by
        rw [hes, loadAddrs_append, show loadAddrs σ (.inK (.n 3) :: (cl23Zero.flatMap
          (Main.slEvs σ) ++ clTail.flatMap (Main.slEvs σ))) = loadAddrs σ (cl23Zero.flatMap
          (Main.slEvs σ) ++ clTail.flatMap (Main.slEvs σ)) from rfl, loadAddrs_append,
          B1.loadAddrs_straight σ _ clHead_straight, B1.loadAddrs_straight σ _ cl23Zero_straight,
          B1.loadAddrs_straight σ _ clTail_straight, z4] at hA
        simp [clHead, clTail, B1.Stmt.loadS] at hA)
      (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq)
    have hce : calls es = [] := by
      rw [hes, calls_append, show calls (.inK (.n 3) :: (cl23Zero.flatMap (Main.slEvs σ) ++
        clTail.flatMap (Main.slEvs σ))) = calls (cl23Zero.flatMap (Main.slEvs σ) ++
        clTail.flatMap (Main.slEvs σ)) from rfl, calls_append, hhc, hzc, htc, z3]
      rfl
    have h' := relAtInT_nodeHonest (Q := clQ 0) (cs := clCalls 0) (bs := clBufs 0) h
      find_claim_list_digest hw ⟨e1, fun h0 => absurd rfl h0⟩ (by rw [hce]; rfl) (by rw [hal]; rfl)
      (by simp [clCalls, clTs])
    rw [hal] at h'
    simpa using h'
  · -- a nonempty list
    set m := n / 17 with hmdef
    set r := n % 17 with hrdef
    have hnm : n = 17 * m + r := (Nat.div_add_mod n 17).symm
    have hm16 : m < 65536 := by omega
    have hr17 : r < 17 := Nat.mod_lt _ (by norm_num)
    set b0 := fp + fs "claim_list_digest" with hb0
    set chain : E := gen ^ b0 with hchain
    set Own : Main.Layout := [(b0, chainCells cells m)] with hOwn
    set D := keccak256 (cellsBytes cells) with hD
    have hfit : List.Forall₂ (fun c s => c.length ≤ s) [chainCells cells m] [13 * (m + 1)] := by
      simp [length_chainCells]
    have hWo : Within Own b0 (13 * (m + 1)) := by
      intro q hq; simp only [hOwn, List.mem_singleton] at hq; subst hq
      simp [length_chainCells]
    have hDo : DisjL Own := List.pairwise_singleton _ _
    have hmOwn : ∀ rd, MemL rd Own → ReadsAt rd chain (chainCells cells m) := fun rd hm =>
      reads_of_memL hm List.mem_cons_self
    -- the callees
    let ks : List Kid :=
      [⟨"list_split", true, [gen ^ n], [], Returns [gen ^ m, gen ^ r]⟩,
        ⟨"__loop16", decide (m ≠ 0), [1, gen ^ m, chain, gen ^ eP], Lin ++ Own, Returns []⟩,
        ⟨clNames[r]!, true, [chain * gen ^ (13 * m), gen ^ eP * gen ^ (68 * m)], Lin ++ Own,
          Returns (digestCells D)⟩]
    have hok : ∀ k ∈ ks, k.taken = true → CompleteAtD fs cert 16 k.f k.Lin k.args k.Out := by
      intro k hk ht
      simp only [ks, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl
      · have := list_split_completeAt fs cert (a := m) (b := r) (by simp [maxKeys]; omega)
          (by simp [claimGroup]; omega)
        rwa [show claimGroup * m + r = n by simp [claimGroup]; omega] at this
      · simp only [decide_eq_true_eq] at ht
        refine completeAt_of_rel_pureD l16_pure (List.mem_singleton_self _) (fun rd hm => ?_) 16
        have hr := hLe rd (memL_append.mp hm).1
        have hmem := claimChainMem_of_reads hl hr (hmOwn rd (memL_append.mp hm).2)
        exact (guard_complete (find_of_idx l16_idx (by rw [coreProgram_length]; omega)) l16_shapeF
          (cl_blocks hl hr hc hmem)).2 ((one_add_gen_ne (by omega)).mpr ht)
      · show CompleteAtD fs cert 16 clNames[r]! (Lin ++ Own) _ _
        rw [clNames_get hr17]
        refine completeAt_of_rel_pureD (cl_pure hr17) (List.mem_singleton_self _) (fun rd hm => ?_) 16
        have hr := hLe rd (memL_append.mp hm).1
        have hS := state_of_reads (hmOwn rd (memL_append.mp hm).2) (le_refl m)
        have hpre : (cellsBytes (cells.take (68 * m))).length = rate * (8 * m) := by
          rw [length_cellsBytes, List.length_take, Nat.min_eq_left (by omega)]
          show 16 * (68 * m) = 136 * (8 * m); omega
        have := claimLast_complete hr17 hpre hS (cells := cells.drop (68 * m)) (by simp; omega)
          (readsAt_drop' hr _) (canon_drop hc _)
        rwa [← cellsBytes_append, List.take_append_drop] at this
    have hokT : KidsDT fs cert 16 ks clTs :=
      ⟨fun ht => (hok _ List.mem_cons_self ht).toT,
        fun ht => (hok _ (List.mem_cons_of_mem _ List.mem_cons_self) ht).toT,
        fun ht => (hok _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) ht).toT,
        trivial⟩
    obtain ⟨Nk, Lk, outs, hoo, hW, hD, -, hKids⟩ :=
      kidsFromInT_of_kidsDT (fs := fs) (cert := cert) 16 ks clTs hokT (b0 + 13 * (m + 1))
    have hl0 : outs.length = 3 := hoo.length
    obtain ⟨o1, t1, rfl, hl1⟩ := exists_of_length_succ hl0
    obtain ⟨o2, t2, rfl, hl2⟩ := exists_of_length_succ hl1
    obtain ⟨o3, t3, rfl, hl3⟩ := exists_of_length_succ hl2
    obtain rfl := List.eq_nil_of_length_eq_zero hl3
    obtain ⟨h1, h2, h3, -⟩ := hoo
    refine ⟨fs "claim_list_digest" + 13 * (m + 1) + Nk, Own ++ Lk, _, [], ⟨rfl, rfl⟩, ?_,
      by rw [List.nil_append]; exact disj_append hDo hD hWo hW le_rfl, fun rd hlow hm => ?_⟩
    · rw [List.nil_append, within_append]
      exact ⟨hWo.mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
    simp only [List.nil_append] at hm
    obtain ⟨hm1, hLin'⟩ := memL_append.mp hm
    obtain ⟨hmO, hLk⟩ := memL_append.mp hm1
    have hch := hmOwn rd hmO
    have hz0 : StateAt rd chain 0 zeroState := by
      have := state_of_reads hch (Nat.zero_le m)
      rw [Nat.mul_zero, pow_zero, mul_one] at this
      exact this
    have hV := cl_core (rd := rd) (entries := gen ^ eP) (n := n) D hz0
    set σ := clσ rd (gen ^ eP) n chain D with hσ
    -- the path
    have h3ne : σ (.n 3) ≠ 0 := by
      rw [hV.v3, Ne, e_add_eq_zero_iff, pow_zero, gen_pow_eq_one_iff (by omega)]; omega
    have hx : σ (.n 24) = ofK (gpow r) := by rw [hV.v24, gen_pow_eq_ofK]
    have hb : (if σ (.n 3) = 0 then walk σ cl23Zero else walk σ cl23Else) =
        .fall (clP1.flatMap (Main.slEvs σ) ++ .call clNames[r]! [.n 54, .n 62] [.n 63, .n 64] ::
          clPost.flatMap (Main.slEvs σ)) := by
      simp only [h3ne, ↓reduceIte]
      rw [cl23Else_split]
      exact walk_dispatch_fall σ clP1 clPost clP1_straight (by rw [clPost_eq]; rfl) (.n 24) clNames
        [.n 54, .n 62] [.n 63, .n 64] (i := r) (by simp [clNames]; omega) (by simp [clNames]) hx
    have hw := walk_ite σ clTail clTail_straight (.n 3) cl23Zero cl23Else [.n 65, .n 66] _ hb
      clHead clHead_straight
    rw [← cl_body] at hw
    set es := clHead.flatMap (Main.slEvs σ) ++ .inK (.n 3) ::
      ((clP1.flatMap (Main.slEvs σ) ++ .call clNames[r]! [.n 54, .n 62] [.n 63, .n 64] ::
        clPost.flatMap (Main.slEvs σ)) ++ clTail.flatMap (Main.slEvs σ)) with hes
    have hmE : ∀ s ∈ clHead ++ clP1 ++ clTail, ∀ a, s = .atom a → a.Holds rd σ := by
      intro s hs a rfl
      refine hV.atoms a (cl_mem_atoms ?_)
      unfold clEEval
      rw [clElsePre_eq]
      simp only [List.mem_append] at hs ⊢
      rcases hs with (hs | hs) | hs <;> simp [hs]
    have hev : ∀ e ∈ es, e.Holds rd σ := by
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact slEvs_holds (fun s hs => slOk_atomS (mH s hs) (hmE s (by simp [hs]))) e he
      rcases List.mem_cons.mp he with rfl | he
      · show IsInK (σ (.n 3)); rw [hV.v3]; exact gen_pow_add_isInK n 0
      rcases List.mem_append.mp he with he | he
      · rcases List.mem_append.mp he with he | he
        · refine slEvs_holds (fun s hs => ?_) e he
          have hk := List.all_eq_true.mp clP1_kinds s hs
          simp only [Bool.or_eq_true] at hk
          rcases hk with (hk | hk) | hk
          · exact slOk_atomS hk (hmE s (by simp [hs]))
          · rw [stmtEqb_sound hk]; trivial
          · rw [stmtEqb_sound hk]
            show IsInK (σ (.n 47)); rw [hV.v47, ← pow_zero gen]; exact gen_pow_add_isInK _ _
        rcases List.mem_cons.mp he with rfl | he
        · trivial
        · refine slEvs_holds (fun s hs => ?_) e he
          rw [clPost_eq] at hs
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with rfl | rfl
          · show σ (.n 10) = σ (.n 63); rw [hV.v10, hV.v63]
          · show σ (.n 11) = σ (.n 64); rw [hV.v11, hV.v64]
      · exact slEvs_holds (fun s hs => slOk_atomS (mTl s hs) (hmE s (by simp [hs]))) e he
    obtain ⟨hhd, hha, hhad, hhc⟩ := Main.straight_parts σ _ clHead_straight
    obtain ⟨hpd, hpa, hpad, hpc⟩ := Main.straight_parts σ _ clP1_straight
    obtain ⟨hqd, hqa, hqad, hqc⟩ := Main.straight_parts σ _ (show clPost.all Main.Stmt.straight = true by rw [clPost_eq]; rfl)
    obtain ⟨htd, hta, htad, htc⟩ := Main.straight_parts σ _ clTail_straight
    have hpostA : clPost.filterMap Main.Stmt.allocSz = [] ∧ clPost.filterMap Main.Stmt.addrS = [] ∧
        clPost.filterMap Main.Stmt.callS = [] ∧ clPost.filterMap B1.Stmt.loadS = [] := by
      rw [clPost_eq]; exact ⟨rfl, rfl, rfl, rfl⟩
    have hal : allocs σ es = [13 * (m + 1)] := by
      rw [hes, es5_allocs, hha, hpa, hqa, hta, clP1_allocs, hpostA.1]
      simp only [clHead, clTail, List.filterMap_cons, List.filterMap_nil, Main.Stmt.allocSz,
        List.map_cons, List.map_nil, Sum.elim_inr, hV.v31,
        logG_gen_pow (show 13 * (n / 17 + 1) < 2 ^ 64 - 1 by omega), List.nil_append, List.append_nil]
      rfl
    have h47 : decide (σ (.n 47) ≠ 0) = decide (m ≠ 0) := by
      rw [hV.v47]; exact decide_eq_decide.mpr (one_add_gen_ne (by omega))
    have hcalls : calls es = [⟨"list_split", [.n 1], [.n 23, .n 24], true⟩,
        ⟨"__loop16", [.n 48, .n 23, .n 32, .n 0], [], decide (m ≠ 0)⟩,
        ⟨clNames[r]!, [.n 54, .n 62], [.n 63, .n 64], true⟩] := by
      rw [hes, es5_calls, hhc, hpc, hqc, htc, clP1_calls, hpostA.2.2.1]
      simp only [List.map_cons, List.map_nil, Main.mkCall, h47, clHead, clTail, List.filterMap_cons,
        List.filterMap_nil, Main.Stmt.callS, List.nil_append, List.cons_append, List.append_nil]
    have hown : ∀ i, b0 ≤ i → i < b0 + 13 * (m + 1) →
        ownData cert fp (fp + fs "claim_list_digest") "claim_list_digest" [13 * (m + 1)] es i :=
      fun i h1 h2 => Or.inl ⟨(13 * (m + 1), b0), List.Mem.head _, h1, h2⟩
    have h := relAtInWT_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
      (R := RegionL Lin) (D := RegionL []) (fp := fp) (N := Nk)
      (args := [gen ^ eP, gen ^ n]) (rets := digestCells D)
      (Dk := fun i => (fun _ => False) i ∨ outRegion ks [o1, o2, o3] i)
      coreProgram_wf find_claim_list_digest (Or.inl cl_loop) (by rw [cl_param, hV.v0, hV.v1]) hw
      (by show [σ (.n 65), σ (.n 66)] = _; rw [hV.v65, hV.v66]; rfl) hev
      (by
        rw [hal, hes, es5_allocDsts, hhd, hpd, hqd, htd, clP1_allocs, hpostA.1]
        simp only [List.map_cons, List.map_nil, clHead, clTail, List.filterMap_cons,
          List.filterMap_nil, Main.Stmt.allocSz, List.nil_append, List.append_nil, bases, hV.v32]
        rw [hchain, gen_pow_eq_ofK])
      (fun q hq => by
        rw [hes, es5_addrs, hhad, hpad, hqad, htad, clP1_addrs, hpostA.2.1] at hq
        simp [clHead, clTail, Main.Stmt.addrS] at hq)
      clTs ?_ ?_ (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq)
    · have h' := relAtInT_nodeHonest (Q := clQ n) (cs := clCalls n) (bs := clBufs n) h
        find_claim_list_digest hw ⟨hV.v1, fun _ => ⟨hV.v23, hV.v24, hV.v31, hV.v48⟩⟩
        (by rw [hcalls]; unfold clCalls; split <;> first | omega | rfl)
        (by rw [hal]; unfold clBufs; split <;> first | omega | rfl)
        (by unfold clCalls; split <;> simp [clTs])
      rw [hal] at h'
      simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at h'
      exact h'
    · rw [hcalls, hal]
      rw [List.sum_cons, List.sum_nil, Nat.add_zero]
      refine hKids rd σ _ _ _ ?_ hlow hLk ?_ (regionsOk_of fun k hk _ i hi => ?_)
      · refine ⟨rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl,
          fun _ => ⟨?_, ?_⟩, trivial⟩
        · show [σ (.n 1)] = _; rw [hV.v1]
        · rw [(h1 rfl).1]; show [σ (.n 23), σ (.n 24)] = _; rw [hV.v23, hV.v24]
        · show [σ (.n 48), σ (.n 23), σ (.n 32), σ (.n 0)] = _
          rw [hV.v48, hV.v23, hV.v32, hV.v0]
        · rename_i ht; rw [(h2 ht).1]; rfl
        · show [σ (.n 54), σ (.n 62)] = _; rw [hV.v54, hV.v62]
        · rw [(h3 rfl).1]; show [σ (.n 63), σ (.n 64)] = _; rw [hV.v63, hV.v64]; rfl
      · intro q hq
        simp only [B1.Kid.lins, ks, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          List.nil_append, List.mem_append] at hq
        rcases hq with (hq | hq) | (hq | hq)
        · exact hLin' q hq
        · exact hmO q hq
        · exact hLin' q hq
        · exact hmO q hq
      · simp only [ks, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl
        · obtain ⟨q, hq, -⟩ := hi; simp at hq
        all_goals
          obtain ⟨q, hq, h1', h2'⟩ := hi
          rcases List.mem_append.mp hq with hq | hq
          · exact Or.inl (Or.inl ⟨q, hq, h1', h2'⟩)
          · simp only [hOwn, List.mem_singleton] at hq
            subst hq
            simp only [length_chainCells] at h2'
            exact Or.inl (Or.inr (hown i h1' h2'))
    · intro A hA
      rw [hes, es5_loads, B1.loadAddrs_straight σ _ clHead_straight,
        B1.loadAddrs_straight σ _ clP1_straight,
        B1.loadAddrs_straight σ _ (show clPost.all Main.Stmt.straight = true by rw [clPost_eq]; rfl),
        B1.loadAddrs_straight σ _ clTail_straight, clP1_loads, hpostA.2.2.2] at hA
      simp only [clHead, clTail, List.filterMap_cons, List.filterMap_nil, B1.Stmt.loadS,
        List.map_nil, List.nil_append, List.append_nil, List.map_map, List.mem_map,
        List.mem_range, Function.comp] at hA
      obtain ⟨c, hc13, rfl⟩ := hA
      refine ⟨b0 + c, by rw [hV.v32, hchain, limb0_gen_pow_mul], Or.inl ?_⟩
      rw [hal]
      exact hown _ (by omega) (by omega)


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **`child_claim_list_digest` is complete, placed, by a tree of honest shape**: `n < 17 · 2^16` honest records among the
caller's words, its chain buffer after its frame holding the states after each group; it returns
their cells' digest. -/
theorem child_claim_list_digest_completeAtT (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ}
    (hκ : 16 ≤ κ) {Lin : Main.Layout} {eP cv og L n : ℕ} {base : E} {o : ℕ → ℕ} {cells : List E}
    (hn : n < claimGroup * maxKeys) (hl : cells.length = 4 * n) (hc : AllCanonical cells)
    (hL33 : L < 2 ^ 33) (hLκ : L ≤ 2 ^ κ)
    (hrec : ∀ rd, MemL rd Lin → RecMem rd (gen ^ cv) (gen ^ og) (gen ^ L) (gen ^ eP) base n o cells)
    (hR2 : ∀ j < n, RegionL Lin (cv + og + o j))
    (hR3 : ∀ j < n, ∀ c < 4, RegionL Lin (eP + 4 * o j + c)) :
    CompleteAtDT fs cert κ "child_claim_list_digest" Lin
      [gen ^ eP, gen ^ cv, base, gen ^ og, gen ^ L, gen ^ n]
      (Returns (digestCells (keccak256 (cellsBytes cells))))
      (NodeHonest coreProgram "child_claim_list_digest" (ccQ n) (ccCalls n) (clBufs n) clTs) := by
  intro fp
  simp only [claimGroup, maxKeys] at hn
  have mH : ∀ s ∈ ccHead, isAtomS s = true := by decide
  have mTl : ∀ s ∈ ccTail, isAtomS s = true := by decide
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · -- the empty list
    have hcl : cells = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst hcl
    refine ⟨fs "child_claim_list_digest", [], _, [], ⟨rfl, rfl⟩, fun q hq => by simp at hq, B1.disj_nil,
      fun rd hlow hm => ?_⟩
    obtain ⟨hat, hpar, h30, h3, hret⟩ := ccz_core (rd := rd) (gen ^ eP) (gen ^ cv) base (gen ^ og) (gen ^ L)
    set σ := cczσ rd [gen ^ eP, gen ^ cv, base, gen ^ og, gen ^ L, gen ^ 0] with hσ
    have hb : (if σ (.n 7) = 0 then walk σ cc24Zero else walk σ cc24Else) =
        .fall (cc24Zero.flatMap (Main.slEvs σ)) := by
      simp only [h30, ↓reduceIte]; exact walk_straight_fall σ _ cc24Zero_straight
    have hw := walk_ite σ ccTail ccTail_straight (.n 7) cc24Zero cc24Else [.n 67, .n 68] _ hb
      ccHead ccHead_straight
    rw [← cc_body] at hw
    set es := ccHead.flatMap (Main.slEvs σ) ++ .inK (.n 7) ::
      (cc24Zero.flatMap (Main.slEvs σ) ++ ccTail.flatMap (Main.slEvs σ)) with hes
    have hmZ : ∀ s ∈ ccHead ++ cc24Zero ++ ccTail, ∀ a, s = .atom a → a.Holds rd σ := by
      intro s hs a rfl
      refine hat a (cl_mem_atoms ?_)
      unfold ccZEval
      simp only [List.mem_append] at hs ⊢
      rcases hs with (hs | hs) | hs
      · exact Or.inl (Or.inl (Or.inl hs))
      · exact Or.inl (Or.inl (Or.inr hs))
      · exact Or.inr hs
    have hev : ∀ e ∈ es, e.Holds rd σ := by
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact slEvs_holds (fun s hs => slOk_atomS (mH s hs) (hmZ s (by simp [hs]))) e he
      rcases List.mem_cons.mp he with rfl | he
      · show IsInK (σ (.n 7)); rw [h3]; exact gen_pow_add_isInK 0 0
      rcases List.mem_append.mp he with he | he
      · exact slEvs_holds (fun s hs => slOk_atomS (List.all_eq_true.mp cc24Zero_atoms s hs)
          (hmZ s (by simp [hs]))) e he
      · exact slEvs_holds (fun s hs => slOk_atomS (mTl s hs) (hmZ s (by simp [hs]))) e he
    obtain ⟨hhd, hha, hhad, hhc⟩ := Main.straight_parts σ _ ccHead_straight
    obtain ⟨hzd, hza, hzad, hzc⟩ := Main.straight_parts σ _ cc24Zero_straight
    obtain ⟨htd, hta, htad, htc⟩ := Main.straight_parts σ _ ccTail_straight
    obtain ⟨z1, z2, z3, z4⟩ := cc24Zero_parts
    have hal : allocs σ es = [] := by
      rw [hes, allocs_append, show allocs σ (.inK (.n 7) :: (cc24Zero.flatMap (Main.slEvs σ) ++
        ccTail.flatMap (Main.slEvs σ))) = allocs σ (cc24Zero.flatMap (Main.slEvs σ) ++
        ccTail.flatMap (Main.slEvs σ)) from rfl, allocs_append, hha, hza, hta, z1]
      rfl
    have h := relAtInWT_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
      (R := RegionL Lin) (D := RegionL []) (Dk := fun _ => False) (N := 0) (fp := fp)
      (args := [gen ^ eP, gen ^ cv, base, gen ^ og, gen ^ L, gen ^ 0]) (rets := digestCells (keccak256 (cellsBytes [])))
      coreProgram_wf find_child_claim_list_digest (Or.inl cc_loop) (by rw [cc_param]; exact hpar) hw hret hev
      (by
        rw [hal, hes, allocDsts_append, show allocDsts (.inK (.n 7) :: (cc24Zero.flatMap
          (Main.slEvs σ) ++ ccTail.flatMap (Main.slEvs σ))) = allocDsts (cc24Zero.flatMap
          (Main.slEvs σ) ++ ccTail.flatMap (Main.slEvs σ)) from rfl, allocDsts_append, hhd, hzd, htd, z1]
        rfl)
      (fun q hq => by
        rw [hes, addrs_append, show addrs (.inK (.n 7) :: (cc24Zero.flatMap (Main.slEvs σ) ++
          ccTail.flatMap (Main.slEvs σ))) = addrs (cc24Zero.flatMap (Main.slEvs σ) ++
          ccTail.flatMap (Main.slEvs σ)) from rfl, addrs_append, hhad, hzad, htad, z2] at hq
        simp [ccHead, ccTail, Main.Stmt.addrS] at hq)
      clTs
      (by
        rw [hes, calls_append, show calls (.inK (.n 7) :: (cc24Zero.flatMap (Main.slEvs σ) ++
          ccTail.flatMap (Main.slEvs σ))) = calls (cc24Zero.flatMap (Main.slEvs σ) ++
          ccTail.flatMap (Main.slEvs σ)) from rfl, calls_append, hhc, hzc, htc, z3]
        exact ⟨rfl, fun _ h => h⟩)
      (fun A hA => by
        rw [hes, loadAddrs_append, show loadAddrs σ (.inK (.n 7) :: (cc24Zero.flatMap
          (Main.slEvs σ) ++ ccTail.flatMap (Main.slEvs σ))) = loadAddrs σ (cc24Zero.flatMap
          (Main.slEvs σ) ++ ccTail.flatMap (Main.slEvs σ)) from rfl, loadAddrs_append,
          B1.loadAddrs_straight σ _ ccHead_straight, B1.loadAddrs_straight σ _ cc24Zero_straight,
          B1.loadAddrs_straight σ _ ccTail_straight, z4] at hA
        simp [ccHead, ccTail, B1.Stmt.loadS] at hA)
      (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq)
    have hce : calls es = [] := by
      rw [hes, calls_append, show calls (.inK (.n 7) :: (cc24Zero.flatMap (Main.slEvs σ) ++
        ccTail.flatMap (Main.slEvs σ))) = calls (cc24Zero.flatMap (Main.slEvs σ) ++
        ccTail.flatMap (Main.slEvs σ)) from rfl, calls_append, hhc, hzc, htc, z3]
      rfl
    have e5 : σ (.n 5) = gen ^ 0 := by
      simp only [List.cons.injEq] at hpar; exact hpar.2.2.2.2.2.1
    have h' := relAtInT_nodeHonest (Q := ccQ 0) (cs := ccCalls 0) (bs := clBufs 0) h
      find_child_claim_list_digest hw ⟨e5, fun h0 => absurd rfl h0⟩ (by rw [hce]; rfl)
      (by rw [hal]; rfl) (by simp [ccCalls, clTs])
    rw [hal] at h'
    simpa using h'
  · -- a nonempty list
    set m := n / 17 with hmdef
    set r := n % 17 with hrdef
    have hnm : n = 17 * m + r := (Nat.div_add_mod n 17).symm
    have hm16 : m < 65536 := by omega
    have hr17 : r < 17 := Nat.mod_lt _ (by norm_num)
    set b0 := fp + fs "child_claim_list_digest" with hb0
    set chain : E := gen ^ b0 with hchain
    set Own : Main.Layout := [(b0, chainCells cells m)] with hOwn
    set D := keccak256 (cellsBytes cells) with hD
    have hWo : Within Own b0 (13 * (m + 1)) := by
      intro q hq; simp only [hOwn, List.mem_singleton] at hq; subst hq
      simp [length_chainCells]
    have hDo : DisjL Own := List.pairwise_singleton _ _
    have hmOwn : ∀ rd, MemL rd Own → ReadsAt rd chain (chainCells cells m) := fun rd hm =>
      reads_of_memL hm List.mem_cons_self
    have hOR : ∀ k < 13 * (m + 1), RegionL (Lin ++ Own) (b0 + k) := fun k hk =>
      regionL_append_right (regionL_of_mem (L := Own) List.mem_cons_self
        (by rw [length_chainCells]; exact hk))
    -- the callees
    let ks : List Kid :=
      [⟨"list_split", true, [gen ^ n], [], Returns [gen ^ m, gen ^ r]⟩,
        ⟨"__loop17", decide (m ≠ 0), [1, gen ^ m, chain, gen ^ eP, gen ^ cv, base, gen ^ og, gen ^ L],
          Lin ++ Own, Returns []⟩,
        ⟨cclNames[r]!, true, [chain * gen ^ (13 * m), gen ^ eP, gen ^ cv, base * gen ^ (17 * m),
          gen ^ og, gen ^ L], Lin ++ Own, Returns (digestCells D)⟩]
    have hok : ∀ k ∈ ks, k.taken = true → CompleteAtD fs cert κ k.f k.Lin k.args k.Out := by
      intro k hk ht
      simp only [ks, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl
      · have := list_split_completeAt fs cert (a := m) (b := r) (by simp [maxKeys]; omega)
          (by simp [claimGroup]; omega)
        rw [show claimGroup * m + r = n by simp [claimGroup]; omega] at this
        exact this.mono hκ
      · simp only [decide_eq_true_eq] at ht
        refine l17_completeAt fs cert hchain rfl rfl rfl rfl (by omega) hc hL33 hLκ (by omega)
          (by omega) (fun rd hm => ⟨fun q hq => state_of_reads (hmOwn rd (memL_append.mp hm).2) hq,
            fun j hj => hrec rd (memL_append.mp hm).1 j (by omega)⟩) (fun j hj c hc => ?_)
          (fun j hj => regionL_append_left (hR2 j (by omega)))
          (fun j hj c hc => regionL_append_left (hR3 j (by omega) c hc))
        rw [Nat.add_assoc]; exact hOR _ (by omega)
      · show CompleteAtD fs cert κ cclNames[r]! (Lin ++ Own) _ _
        rw [cclNames_get hr17]
        have hpre : (cellsBytes (cells.take (68 * m))).length = rate * (8 * m) := by
          rw [length_cellsBytes, List.length_take, Nat.min_eq_left (by omega)]
          show 16 * (68 * m) = 136 * (8 * m); omega
        have := ccl_completeAt fs cert hr17 (Lin := Lin ++ Own) (sP := b0 + 13 * m)
          (os := fun j => o (17 * m + j)) (cells := cells.drop (68 * m)) (n := 8 * m)
          (pre := cellsBytes (cells.take (68 * m))) (marks := base * gen ^ (17 * m))
          (by rw [hchain, ← pow_add]) rfl rfl rfl rfl hpre (by simp; omega) (canon_drop hc _) hL33 hLκ
          (fun rd hm => ⟨state_of_reads (hmOwn rd (memL_append.mp hm).2) (le_refl m), by
            have hr := recMem_group (hrec rd (memL_append.mp hm).1) (s := 17 * m) (k := r) (by omega)
            rwa [show 4 * (17 * m) = 68 * m by ring, List.take_of_length_le (by simp; omega)] at hr⟩)
          (fun c hc => by rw [Nat.add_assoc]; exact hOR _ (by omega))
          (fun j hj => regionL_append_left (hR2 _ (by omega)))
          (fun j hj c hc => regionL_append_left (hR3 _ (by omega) c hc))
        rwa [← cellsBytes_append, List.take_append_drop] at this
    have hokT : KidsDT fs cert κ ks clTs :=
      ⟨fun ht => (hok _ List.mem_cons_self ht).toT,
        fun ht => (hok _ (List.mem_cons_of_mem _ List.mem_cons_self) ht).toT,
        fun ht => (hok _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) ht).toT,
        trivial⟩
    obtain ⟨Nk, Lk, outs, hoo, hW, hD, -, hKids⟩ :=
      kidsFromInT_of_kidsDT (fs := fs) (cert := cert) κ ks clTs hokT (b0 + 13 * (m + 1))
    have hl0 : outs.length = 3 := hoo.length
    obtain ⟨o1, t1, rfl, hl1⟩ := exists_of_length_succ hl0
    obtain ⟨o2, t2, rfl, hl2⟩ := exists_of_length_succ hl1
    obtain ⟨o3, t3, rfl, hl3⟩ := exists_of_length_succ hl2
    obtain rfl := List.eq_nil_of_length_eq_zero hl3
    obtain ⟨h1, h2, h3, -⟩ := hoo
    refine ⟨fs "child_claim_list_digest" + 13 * (m + 1) + Nk, Own ++ Lk, _, [], ⟨rfl, rfl⟩, ?_,
      by rw [List.nil_append]; exact disj_append hDo hD hWo hW le_rfl, fun rd hlow hm => ?_⟩
    · rw [List.nil_append, within_append]
      exact ⟨hWo.mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
    simp only [List.nil_append] at hm
    obtain ⟨hm1, hLin'⟩ := memL_append.mp hm
    obtain ⟨hmO, hLk⟩ := memL_append.mp hm1
    have hch := hmOwn rd hmO
    have hz0 : StateAt rd chain 0 zeroState := by
      have := state_of_reads hch (Nat.zero_le m)
      rw [Nat.mul_zero, pow_zero, mul_one] at this
      exact this
    have hV := cc_core (rd := rd) (entries := gen ^ eP) (cover := gen ^ cv) (base := base)
      (origin := gen ^ og) (limit := gen ^ L) (n := n) D hz0
    set σ := ccσ rd [gen ^ eP, gen ^ cv, base, gen ^ og, gen ^ L, gen ^ n] n chain D with hσ
    have hpar := hV.par
    simp only [List.cons.injEq, and_true] at hpar
    obtain ⟨e0, e1, e2, e3, e4, e5⟩ := hpar
    -- the path
    have h7ne : σ (.n 7) ≠ 0 := by
      rw [hV.v7, Ne, e_add_eq_zero_iff, pow_zero, gen_pow_eq_one_iff (by omega)]; omega
    have hx : σ (.n 28) = ofK (gpow r) := by rw [hV.v28, gen_pow_eq_ofK]
    have hb : (if σ (.n 7) = 0 then walk σ cc24Zero else walk σ cc24Else) =
        .fall (ccP1.flatMap (Main.slEvs σ) ++ .call cclNames[r]! [.n 58, .n 0, .n 1, .n 64, .n 3, .n 4]
          [.n 65, .n 66] :: ccPost.flatMap (Main.slEvs σ)) := by
      simp only [h7ne, ↓reduceIte]
      rw [cc24Else_split]
      exact walk_dispatch_fall σ ccP1 ccPost ccP1_straight (by rw [ccPost_eq]; rfl) (.n 28) cclNames
        [.n 58, .n 0, .n 1, .n 64, .n 3, .n 4] [.n 65, .n 66] (i := r) (by simp [cclNames]; omega)
        (by simp [cclNames]) hx
    have hw := walk_ite σ ccTail ccTail_straight (.n 7) cc24Zero cc24Else [.n 67, .n 68] _ hb
      ccHead ccHead_straight
    rw [← cc_body] at hw
    set es := ccHead.flatMap (Main.slEvs σ) ++ .inK (.n 7) ::
      ((ccP1.flatMap (Main.slEvs σ) ++ .call cclNames[r]! [.n 58, .n 0, .n 1, .n 64, .n 3, .n 4]
        [.n 65, .n 66] :: ccPost.flatMap (Main.slEvs σ)) ++ ccTail.flatMap (Main.slEvs σ)) with hes
    have hmE : ∀ s ∈ ccHead ++ ccP1 ++ ccTail, ∀ a, s = .atom a → a.Holds rd σ := by
      intro s hs a rfl
      refine hV.atoms a (cl_mem_atoms ?_)
      unfold ccEEval
      rw [ccElsePre_eq]
      simp only [List.mem_append] at hs ⊢
      rcases hs with (hs | hs) | hs <;> simp [hs]
    have hev : ∀ e ∈ es, e.Holds rd σ := by
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact slEvs_holds (fun s hs => slOk_atomS (mH s hs) (hmE s (by simp [hs]))) e he
      rcases List.mem_cons.mp he with rfl | he
      · show IsInK (σ (.n 7)); rw [hV.v7]; exact gen_pow_add_isInK n 0
      rcases List.mem_append.mp he with he | he
      · rcases List.mem_append.mp he with he | he
        · refine slEvs_holds (fun s hs => ?_) e he
          have hk := List.all_eq_true.mp ccP1_kinds s hs
          simp only [Bool.or_eq_true] at hk
          rcases hk with (hk | hk) | hk
          · exact slOk_atomS hk (hmE s (by simp [hs]))
          · rw [stmtEqb_sound hk]; trivial
          · rw [stmtEqb_sound hk]
            show IsInK (σ (.n 51)); rw [hV.v51, ← pow_zero gen]; exact gen_pow_add_isInK _ _
        rcases List.mem_cons.mp he with rfl | he
        · trivial
        · refine slEvs_holds (fun s hs => ?_) e he
          rw [ccPost_eq] at hs
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with rfl | rfl
          · show σ (.n 14) = σ (.n 65); rw [hV.v14, hV.v65]
          · show σ (.n 15) = σ (.n 66); rw [hV.v15, hV.v66]
      · exact slEvs_holds (fun s hs => slOk_atomS (mTl s hs) (hmE s (by simp [hs]))) e he
    obtain ⟨hhd, hha, hhad, hhc⟩ := Main.straight_parts σ _ ccHead_straight
    obtain ⟨hpd, hpa, hpad, hpc⟩ := Main.straight_parts σ _ ccP1_straight
    obtain ⟨hqd, hqa, hqad, hqc⟩ := Main.straight_parts σ _
      (show ccPost.all Main.Stmt.straight = true by rw [ccPost_eq]; rfl)
    obtain ⟨htd, hta, htad, htc⟩ := Main.straight_parts σ _ ccTail_straight
    have hpostA : ccPost.filterMap Main.Stmt.allocSz = [] ∧ ccPost.filterMap Main.Stmt.addrS = [] ∧
        ccPost.filterMap Main.Stmt.callS = [] ∧ ccPost.filterMap B1.Stmt.loadS = [] := by
      rw [ccPost_eq]; exact ⟨rfl, rfl, rfl, rfl⟩
    have hal : allocs σ es = [13 * (m + 1)] := by
      rw [hes, es5_allocs, hha, hpa, hqa, hta, ccP1_allocs, hpostA.1]
      simp only [ccHead, ccTail, List.filterMap_cons, List.filterMap_nil, Main.Stmt.allocSz,
        List.map_cons, List.map_nil, Sum.elim_inr, hV.v35,
        logG_gen_pow (show 13 * (n / 17 + 1) < 2 ^ 64 - 1 by omega), List.nil_append, List.append_nil]
      rfl
    have h51 : decide (σ (.n 51) ≠ 0) = decide (m ≠ 0) := by
      rw [hV.v51]; exact decide_eq_decide.mpr (one_add_gen_ne (by omega))
    have hcalls : calls es = [⟨"list_split", [.n 5], [.n 27, .n 28], true⟩,
        ⟨"__loop17", [.n 52, .n 27, .n 36, .n 0, .n 1, .n 2, .n 3, .n 4], [], decide (m ≠ 0)⟩,
        ⟨cclNames[r]!, [.n 58, .n 0, .n 1, .n 64, .n 3, .n 4], [.n 65, .n 66], true⟩] := by
      rw [hes, es5_calls, hhc, hpc, hqc, htc, ccP1_calls, hpostA.2.2.1]
      simp only [List.map_cons, List.map_nil, Main.mkCall, h51, ccHead, ccTail, List.filterMap_cons,
        List.filterMap_nil, Main.Stmt.callS, List.nil_append, List.cons_append, List.append_nil]
    have hown : ∀ i, b0 ≤ i → i < b0 + 13 * (m + 1) →
        ownData cert fp (fp + fs "child_claim_list_digest") "child_claim_list_digest"
          [13 * (m + 1)] es i :=
      fun i h1 h2 => Or.inl ⟨(13 * (m + 1), b0), List.Mem.head _, h1, h2⟩
    have h := relAtInWT_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
      (R := RegionL Lin) (D := RegionL []) (fp := fp) (N := Nk)
      (args := [gen ^ eP, gen ^ cv, base, gen ^ og, gen ^ L, gen ^ n]) (rets := digestCells D)
      (Dk := fun i => (fun _ => False) i ∨ outRegion ks [o1, o2, o3] i)
      coreProgram_wf find_child_claim_list_digest (Or.inl cc_loop)
      (by rw [cc_param, e0, e1, e2, e3, e4, e5]) hw
      (by show [σ (.n 67), σ (.n 68)] = _; rw [hV.v67, hV.v68]; rfl) hev
      (by
        rw [hal, hes, es5_allocDsts, hhd, hpd, hqd, htd, ccP1_allocs, hpostA.1]
        simp only [List.map_cons, List.map_nil, ccHead, ccTail, List.filterMap_cons,
          List.filterMap_nil, Main.Stmt.allocSz, List.nil_append, List.append_nil, bases, hV.v36]
        rw [hchain, gen_pow_eq_ofK])
      (fun q hq => by
        rw [hes, es5_addrs, hhad, hpad, hqad, htad, ccP1_addrs, hpostA.2.1] at hq
        simp [ccHead, ccTail, Main.Stmt.addrS] at hq)
      clTs ?_ ?_ (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq)
    · have h' := relAtInT_nodeHonest (Q := ccQ n) (cs := ccCalls n) (bs := clBufs n) h
        find_child_claim_list_digest hw ⟨e5, fun _ => ⟨hV.v27, hV.v28, hV.v35, hV.v52⟩⟩
        (by rw [hcalls]; unfold ccCalls; split <;> first | omega | rfl)
        (by rw [hal]; unfold clBufs; split <;> first | omega | rfl)
        (by unfold ccCalls; split <;> simp [clTs])
      rw [hal] at h'
      simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at h'
      exact h'
    · rw [hcalls, hal]
      rw [List.sum_cons, List.sum_nil, Nat.add_zero]
      refine hKids rd σ _ _ _ ?_ hlow hLk ?_ (regionsOk_of fun k hk _ i hi => ?_)
      · refine ⟨rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl,
          fun _ => ⟨?_, ?_⟩, trivial⟩
        · show [σ (.n 5)] = _; rw [e5]
        · rw [(h1 rfl).1]; show [σ (.n 27), σ (.n 28)] = _; rw [hV.v27, hV.v28]
        · show [σ (.n 52), σ (.n 27), σ (.n 36), σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)] = _
          rw [hV.v52, hV.v27, hV.v36, e0, e1, e2, e3, e4]
        · rename_i ht; rw [(h2 ht).1]; rfl
        · show [σ (.n 58), σ (.n 0), σ (.n 1), σ (.n 64), σ (.n 3), σ (.n 4)] = _
          rw [hV.v58, hV.v64, e0, e1, e2, e3, e4]
        · rw [(h3 rfl).1]; show [σ (.n 65), σ (.n 66)] = _; rw [hV.v65, hV.v66]; rfl
      · intro q hq
        simp only [B1.Kid.lins, ks, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          List.nil_append, List.mem_append] at hq
        rcases hq with (hq | hq) | (hq | hq)
        · exact hLin' q hq
        · exact hmO q hq
        · exact hLin' q hq
        · exact hmO q hq
      · simp only [ks, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl
        · obtain ⟨q, hq, -⟩ := hi; simp at hq
        all_goals
          obtain ⟨q, hq, h1', h2'⟩ := hi
          rcases List.mem_append.mp hq with hq | hq
          · exact Or.inl (Or.inl ⟨q, hq, h1', h2'⟩)
          · simp only [hOwn, List.mem_singleton] at hq
            subst hq
            simp only [length_chainCells] at h2'
            exact Or.inl (Or.inr (hown i h1' h2'))
    · intro A hA
      rw [hes, es5_loads, B1.loadAddrs_straight σ _ ccHead_straight,
        B1.loadAddrs_straight σ _ ccP1_straight,
        B1.loadAddrs_straight σ _ (show ccPost.all Main.Stmt.straight = true by rw [ccPost_eq]; rfl),
        B1.loadAddrs_straight σ _ ccTail_straight, ccP1_loads, hpostA.2.2.2] at hA
      simp only [ccHead, ccTail, List.filterMap_cons, List.filterMap_nil, B1.Stmt.loadS,
        List.map_nil, List.nil_append, List.append_nil, List.map_map, List.mem_map,
        List.mem_range, Function.comp] at hA
      obtain ⟨c, hc13, rfl⟩ := hA
      refine ⟨b0 + c, by rw [hV.v36, hchain, limb0_gen_pow_mul], Or.inl ?_⟩
      rw [hal]
      exact hown _ (by omega) (by omega)


end
end LeanVM.Guest.B1.Digest
