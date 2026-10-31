/-
  LeanVM.Guest.B1.Digest.ClaimListsAtTB

  `claim_list_digest` and `child_claim_list_digest` by trees of honest shape, within bounds before
  the memory (`CompleteAtDTB`), for the budget's words: `claim_list_digest_completeAtT`,
  `child_claim_list_digest_completeAtT` (same proofs) with their callees' bounds.
-/

module

public import LeanVM.Guest.B1.Digest.ClaimListsAtT
public import LeanVM.Guest.B1.Digest.LoopAtB
public import LeanVM.Guest.Memory.LoopPre

/-!
# The claim lists, within bounds

`clB fs SB SK n`: `claim_list_digest`'s words on `n` claims: its frame; when `n ≠ 0`, its chain
buffer `13 (n / 17 + 1)`, `list_split`'s bound `SB "list_split"`, `__loop15`'s `(n / 17) · SK`
(its frame when not entered), `claim_list_last__L{n % 17}`'s `SB`. `ccB fs SB n`: the same for
`child_claim_list_digest`, `__loop16` within `(n / 17 + 1)` frames, `child_claim_list_last__L*` a
leaf within its frame. The static bounds `SB`, `SK` are hypotheses (`TotalLe`, `TotalLeOn` on
`LoopPre`). `l17_completeAtB`, `ccl_completeAtB`, `list_split_completeAtDTB`: the callees within
their bounds.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1 (CompleteAtD CompleteAtDT CompleteAtDTB KidsDTB kidsFromInT_of_kidsDTB kidsBoundL
  Returns Kid DisjL Within disj_append completeAt_of_rel_pureB completeAt_of_rel_pureBat
  completeAtDTB_of_relIn regionsOk_of within_append bufL bufL_within bufL_disj bufL_region LowDef)
open LeanVM.Guest.B1.Main (Layout MemL RegionL memL_append)
open LeanVM.Guest.B1.Da (SlOk slEvs_holds exists_of_length_succ limb0_gen_pow_mul reads_of_memL
  regionL_of_mem relAtIn_atoms)
open LeanVM.Guest.Budget (NodeHonest)

@[expose] public section

/-- **`claim_list_digest`'s words** on `n` claims. -/
def clB (fs : String → ℕ) (SB SK : String → ℕ) (n : ℕ) : ℕ :=
  if n = 0 then fs "claim_list_digest" else
    fs "claim_list_digest" + 13 * (n / 17 + 1) + (SB "list_split" +
      ((if n / 17 ≠ 0 then n / 17 * SK "__loop15" else fs "__loop15") + (SB clNames[n % 17]! + 0)))

/-- **`child_claim_list_digest`'s words** on `n` claims. -/
def ccB (fs : String → ℕ) (SB : String → ℕ) (n : ℕ) : ℕ :=
  if n = 0 then fs "child_claim_list_digest" else
    fs "child_claim_list_digest" + 13 * (n / 17 + 1) + (SB "list_split" +
      ((if n / 17 ≠ 0 then (n / 17 + 1) * fs "__loop16" else fs "__loop16") +
        (fs (cclNames.getD (n % 17) "") + 0)))

/-- `list_split` within its static bound. -/
theorem list_split_completeAtDTB (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} {a b : ℕ}
    (hκ : 16 ≤ κ) (ha : a < maxKeys) (hb : b < claimGroup) {Bls : ℕ}
    (hT : TotalLe coreProgram fs "list_split" (fun _ => Bls)) :
    CompleteAtDTB fs cert κ "list_split" [] [gen ^ (claimGroup * a + b)] (Returns [gen ^ a, gen ^ b])
      (fun _ => True) Bls :=
  completeAtDTB_of_relIn list_split_pure (List.mem_singleton_self _)
    (fun rd t rets' hn hv hb => hT rd t _ rets' hn hv hb) fun rd hl _ =>
    Lift.relIn_of_leaf find_list_split list_split_leafOk
      (fun σ es vs _ hw A hA => by
        have hall : (Out.ret es vs).All (Lift.EvLeafOk noLoad) := by
          have := Lift.walk_leafOk (σ := σ) Data.core22.body list_split_leafOk
          exact (show walk σ Data.core22.body = .ret es vs from hw) ▸ this
        rw [loads_none hall] at hA
        exact absurd hA List.not_mem_nil)
      (list_split_complete' rd (hl.mono hκ) _ _ ⟨a, ha, b, hb, rfl, rfl⟩)

section Callees
variable {rd : Reader}

/-- **`child_claim_list_last__L{k}` is complete, placed**: the state at `sp = g^sP`, the records'
marks and cells among the caller's words. -/
theorem ccl_completeAtB (fs : String → ℕ) (cert : String → V → ℕ) {k : ℕ} (hk : k < 17) {κ : ℕ}
    {Lin : Main.Layout} {sp entries cover marks origin limit : E} {sP eP cv og L n : ℕ}
    {pre : List UInt8} {os : ℕ → ℕ} {cells : List E}
    (hsp : sp = gen ^ sP) (hen : entries = gen ^ eP) (hcv : cover = gen ^ cv) (hog : origin = gen ^ og)
    (hL : limit = gen ^ L) (hpre : pre.length = rate * n) (hl : cells.length = 4 * k)
    (hc : AllCanonical cells) (hL33 : L < 2 ^ 33) (hLκ : L ≤ 2 ^ κ)
    (hmem : ∀ rd, MemL rd Lin → StateAt rd sp 0 (absorbChunks n zeroState pre) ∧
      RecMem rd cover origin limit entries marks k os cells)
    (hR1 : ∀ o < 13, RegionL Lin (sP + o)) (hR2 : ∀ j < k, RegionL Lin (cv + og + os j))
    (hR3 : ∀ j < k, ∀ c < 4, RegionL Lin (eP + 4 * os j + c)) :
    CompleteAtDTB fs cert κ (cclNames.getD k "") Lin [sp, entries, cover, marks, origin, limit]
      (Returns (digestCells (keccak256 (pre ++ cellsBytes cells)))) (fun _ => True)
      (fs (cclNames.getD k "")) := by
  intro fp
  refine ⟨fs (cclNames.getD k ""), [], _, [], le_rfl, ⟨rfl, rfl⟩, fun q hq => by simp at hq, B1.disj_nil,
    fun rd hlow hm => ?_⟩
  simp only [List.append_nil, List.nil_append] at hm
  obtain ⟨hS, hrec⟩ := hmem rd hm
  obtain ⟨vs, σ, hb, hp, hat, hr, hload⟩ := ccl_core hk hsp hen hcv hog hpre hS hl hc hrec hL hL33
    (boundMem_of_low hlow hLκ)
  refine RelAtIn.relAtInT (relAtIn_atoms (ccl_name hk) hb (ccl_loop hk) (ccl_na hk) hp hat hr
    (fun q hq => by rw [ccl_addr hk] at hq; exact absurd hq List.not_mem_nil) (fun q hq => ?_)
    (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq))
  rcases hload q hq with ⟨o, ho, h⟩ | ⟨j, hj, h⟩ | ⟨j, hj, c, hc4, h⟩
  · exact ⟨_, h, Or.inl (hR1 o ho)⟩
  · exact ⟨_, h, Or.inl (hR2 j hj)⟩
  · exact ⟨_, h, Or.inl (hR3 j hj c hc4)⟩

/-- **`__loop16` is complete, placed**: the chain buffer's states at `g^chP` and the records'
marks and cells among the caller's words, the groups `j < m`. -/
theorem l17_completeAtB (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} {Lin : Main.Layout}
    {chain entries cover base origin limit : E} {chP eP cv og L m : ℕ} {o : ℕ → ℕ}
    {cells : List E} (hch : chain = gen ^ chP) (hen : entries = gen ^ eP)
    (hcv : cover = gen ^ cv) (hog : origin = gen ^ og) (hL : limit = gen ^ L)
    (hl : 68 * m ≤ cells.length) (hc : AllCanonical cells) (hL33 : L < 2 ^ 33) (hLκ : L ≤ 2 ^ κ)
    (hm : m < 2 ^ 34) (hm0 : 0 < m)
    (hmem : ∀ rd, MemL rd Lin → (∀ q ≤ m, StateAt rd (chain * gen ^ (13 * q)) 0
        (absorbChunks (8 * q) zeroState (cellsBytes (cells.take (68 * q))))) ∧
      RecMem rd cover origin limit entries base (17 * m) o cells)
    (hR1 : ∀ j < m, ∀ c < 26, RegionL Lin (chP + 13 * j + c))
    (hR2 : ∀ j < 17 * m, RegionL Lin (cv + og + o j))
    (hR3 : ∀ j < 17 * m, ∀ c < 4, RegionL Lin (eP + 4 * o j + c)) :
    CompleteAtDTB fs cert κ "__loop16" Lin
      [1, gen ^ m, chain, entries, cover, base, origin, limit] (Returns []) (fun _ => True)
      ((m + 1) * fs "__loop16") := by
  have h := loopA_completeAtB fs cert (find_of_idx l17_idx (by rw [coreProgram_length]; omega))
    l17_shapeF l17_atomsS l17_unplaced (Lin := Lin) (κ := κ) (N := gen ^ m)
    (rest := [chain, entries, cover, base, origin, limit]) (m := m) rfl hm ?_
  · have := h 0 hm0
    rwa [pow_zero, Nat.sub_zero] at this
  intro jj hjj rd hlow hLin
  obtain ⟨hS, hrec⟩ := hmem rd hLin
  have hpre : (cellsBytes (cells.take (68 * jj))).length = rate * (8 * jj) := by
    rw [length_cellsBytes, List.length_take, Nat.min_eq_left (by omega)]
    show 16 * (68 * jj) = 136 * (8 * jj); omega
  have hS0 := hS jj (by omega)
  have hS1 := hS (jj + 1) (by omega)
  rw [show 68 * (jj + 1) = 68 * jj + 68 by ring, List.take_add, cellsBytes_append] at hS1
  have hr := recMem_group hrec (s := 17 * jj) (k := 17) (by omega)
  rw [show 4 * (17 * jj) = 68 * jj by ring, show 4 * 17 = 68 by rfl, mul_comm 17 jj, pow_mul] at hr
  obtain ⟨σ, hp, hat, hload⟩ := l17_core (x := gen ^ jj) (N := gen ^ m) rfl hch hen hcv hog hpre
    (by rw [gen_pow_pow]; exact hS0) (cells := ((cells.drop (68 * jj)).take 68)) (by simp; omega)
    (canon_take (canon_drop hc _) _) hr hL hL33 (boundMem_of_low hlow hLκ) (fun c => by
      have := hS1 c
      rw [gen_pow_pow, loadHolds_mul_gen_pow]
      rw [loadHolds_mul_gen_pow, show 13 * (jj + 1) + (0 + c.val) = 13 * jj + (13 + c.val) by ring,
        show 8 * (jj + 1) = 8 * jj + 8 by ring] at this
      exact this)
  refine ⟨σ, hp, hat, fun q hq => ?_⟩
  rcases hload q hq with ⟨c, hc26, h⟩ | ⟨j, hj, h⟩ | ⟨j, hj, c, hc4, h⟩
  · exact ⟨_, h, hR1 jj hjj c hc26⟩
  · exact ⟨_, h, by have := hR2 (17 * jj + j) (by omega); rwa [mul_comm 17 jj] at this⟩
  · exact ⟨_, h, by have := hR3 (17 * jj + j) (by omega) c hc4; rwa [mul_comm 17 jj] at this⟩

end Callees

set_option maxRecDepth 20000 in
/-- **`claim_list_digest` is complete, placed, by a tree of honest shape**: `n < 17 · 2^16` canonical claims' cells at `g^eP`
among the caller's words, its chain buffer after its frame holding the states after each group;
it returns their digest's cells. -/
theorem claim_list_digest_completeAtTB (fs : String → ℕ) (cert : String → V → ℕ) {Lin : Main.Layout}
    {eP n : ℕ} {cells : List E} (hn : n < claimGroup * maxKeys) (hl : cells.length = 4 * n)
    (hc : AllCanonical cells) (hLe : ∀ rd, MemL rd Lin → ReadsAt rd (gen ^ eP) cells)
    (hLr : ∀ k < cells.length, RegionL Lin (eP + k)) {SB SK : String → ℕ}
    (hLS : TotalLe coreProgram fs "list_split" (fun _ => SB "list_split"))
    (hL16 : TotalLeOn coreProgram fs "__loop15" LoopPre (fun a => logG (a.getD 1 0) * SK "__loop15"))
    (hCL : ∀ j < 17, TotalLe coreProgram fs clNames[j]! (fun _ => SB clNames[j]!)) :
    CompleteAtDTB fs cert 16 "claim_list_digest" Lin [gen ^ eP, gen ^ n]
      (Returns (digestCells (keccak256 (cellsBytes cells))))
      (NodeHonest coreProgram "claim_list_digest" (clQ n) (clCalls n) (clBufs n) clTs)
      (clB fs SB SK n) := by
  intro fp
  simp only [claimGroup, maxKeys] at hn
  have mH : ∀ s ∈ clHead, isAtomS s = true := by decide
  have mTl : ∀ s ∈ clTail, isAtomS s = true := by decide
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · -- the empty list
    have hcl : cells = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst hcl
    refine ⟨fs "claim_list_digest", [], _, [], by simp [clB], ⟨rfl, rfl⟩, fun q hq => by simp at hq,
      B1.disj_nil,
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
        ⟨"__loop15", decide (m ≠ 0), [1, gen ^ m, chain, gen ^ eP], Lin ++ Own, Returns []⟩,
        ⟨clNames[r]!, true, [chain * gen ^ (13 * m), gen ^ eP * gen ^ (68 * m)], Lin ++ Own,
          Returns (digestCells D)⟩]
    have hokB : KidsDTB fs cert 16 ks clTs [SB "list_split", m * SK "__loop15", SB clNames[r]!] := by
      refine ⟨fun _ => ?_, fun ht => ?_, fun _ => ?_, trivial⟩
      · have := list_split_completeAtDTB fs cert (a := m) (b := r) le_rfl (by simp [maxKeys]; omega)
          (by simp [claimGroup]; omega) hLS
        rwa [show claimGroup * m + r = n by simp [claimGroup]; omega] at this
      · simp only [decide_eq_true_eq] at ht
        refine (completeAt_of_rel_pureBat l16_pure (List.mem_singleton_self _) (fun rd hm => ?_) 16
          (B := m * SK "__loop15") (fun rd t hn hv hb => ?_)).toDTB
        · have hr := hLe rd (memL_append.mp hm).1
          have hmem := claimChainMem_of_reads hl hr (hmOwn rd (memL_append.mp hm).2)
          exact (guard_complete (find_of_idx l16_idx (by rw [coreProgram_length]; omega)) l16_shapeF
            (cl_blocks hl hr hc hmem)).2 ((one_add_gen_ne (by omega)).mpr ht)
        · have := hL16 rd t _ _ hn (loopPre_gen (m := m) (by omega) (by omega) _) hv hb
          simpa [logG_gen_pow (show m < 2 ^ 64 - 1 by omega)] using this
      · have hT := hCL r hr17
        show CompleteAtDTB fs cert 16 clNames[r]! (Lin ++ Own) _ _ _ (SB clNames[r]!)
        rw [clNames_get hr17] at hT ⊢
        refine (completeAt_of_rel_pureB (cl_pure hr17) (List.mem_singleton_self _) (fun rd hm => ?_) 16
          (B := fun _ => SB (clNames.getD r "")) hT).toDTB
        have hr := hLe rd (memL_append.mp hm).1
        have hS := state_of_reads (hmOwn rd (memL_append.mp hm).2) (le_refl m)
        have hpre : (cellsBytes (cells.take (68 * m))).length = rate * (8 * m) := by
          rw [length_cellsBytes, List.length_take, Nat.min_eq_left (by omega)]
          show 16 * (68 * m) = 136 * (8 * m); omega
        have := claimLast_complete hr17 hpre hS (cells := cells.drop (68 * m)) (by simp; omega)
          (readsAt_drop' hr _) (canon_drop hc _)
        rwa [← cellsBytes_append, List.take_append_drop] at this
    obtain ⟨Nk, Lk, outs, hNk, hoo, hW, hD, -, hKids⟩ :=
      kidsFromInT_of_kidsDTB (fs := fs) (cert := cert) 16 ks clTs
        [SB "list_split", m * SK "__loop15", SB clNames[r]!] hokB (b0 + 13 * (m + 1))
    have hl0 : outs.length = 3 := hoo.length
    obtain ⟨o1, t1, rfl, hl1⟩ := exists_of_length_succ hl0
    obtain ⟨o2, t2, rfl, hl2⟩ := exists_of_length_succ hl1
    obtain ⟨o3, t3, rfl, hl3⟩ := exists_of_length_succ hl2
    obtain rfl := List.eq_nil_of_length_eq_zero hl3
    obtain ⟨h1, h2, h3, -⟩ := hoo
    refine ⟨fs "claim_list_digest" + 13 * (m + 1) + Nk, Own ++ Lk, _, [], ?_, ⟨rfl, rfl⟩, ?_,
      by rw [List.nil_append]; exact disj_append hDo hD hWo hW le_rfl, fun rd hlow hm => ?_⟩
    · have hb := hNk
      simp only [kidsBoundL, ks, List.headD_cons, List.tail_cons, ↓reduceIte, decide_eq_true_eq] at hb
      simp only [clB, show n ≠ 0 by omega, ↓reduceIte, ← hmdef, ← hrdef]
      split at hb <;> split <;> omega
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
        ⟨"__loop15", [.n 48, .n 23, .n 32, .n 0], [], decide (m ≠ 0)⟩,
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
/-- **`child_claim_list_digest` is complete, placed, by a tree of honest shape**: `n < 17 · 2^16` honest records among the
caller's words, its chain buffer after its frame holding the states after each group; it returns
their cells' digest. -/
theorem child_claim_list_digest_completeAtTB (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ}
    (hκ : 16 ≤ κ) {Lin : Main.Layout} {eP cv og L n : ℕ} {base : E} {o : ℕ → ℕ} {cells : List E}
    (hn : n < claimGroup * maxKeys) (hl : cells.length = 4 * n) (hc : AllCanonical cells)
    (hL33 : L < 2 ^ 33) (hLκ : L ≤ 2 ^ κ)
    (hrec : ∀ rd, MemL rd Lin → RecMem rd (gen ^ cv) (gen ^ og) (gen ^ L) (gen ^ eP) base n o cells)
    (hR2 : ∀ j < n, RegionL Lin (cv + og + o j))
    (hR3 : ∀ j < n, ∀ c < 4, RegionL Lin (eP + 4 * o j + c)) {SB : String → ℕ}
    (hLS : TotalLe coreProgram fs "list_split" (fun _ => SB "list_split")) :
    CompleteAtDTB fs cert κ "child_claim_list_digest" Lin
      [gen ^ eP, gen ^ cv, base, gen ^ og, gen ^ L, gen ^ n]
      (Returns (digestCells (keccak256 (cellsBytes cells))))
      (NodeHonest coreProgram "child_claim_list_digest" (ccQ n) (ccCalls n) (clBufs n) clTs)
      (ccB fs SB n) := by
  intro fp
  simp only [claimGroup, maxKeys] at hn
  have mH : ∀ s ∈ ccHead, isAtomS s = true := by decide
  have mTl : ∀ s ∈ ccTail, isAtomS s = true := by decide
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · -- the empty list
    have hcl : cells = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst hcl
    refine ⟨fs "child_claim_list_digest", [], _, [], by simp [ccB], ⟨rfl, rfl⟩, fun q hq => by simp at hq,
      B1.disj_nil,
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
        ⟨"__loop16", decide (m ≠ 0), [1, gen ^ m, chain, gen ^ eP, gen ^ cv, base, gen ^ og, gen ^ L],
          Lin ++ Own, Returns []⟩,
        ⟨cclNames[r]!, true, [chain * gen ^ (13 * m), gen ^ eP, gen ^ cv, base * gen ^ (17 * m),
          gen ^ og, gen ^ L], Lin ++ Own, Returns (digestCells D)⟩]
    have hokB : KidsDTB fs cert κ ks clTs
        [SB "list_split", (m + 1) * fs "__loop16", fs (cclNames.getD r "")] := by
      refine ⟨fun _ => ?_, fun ht => ?_, fun _ => ?_, trivial⟩
      · have := list_split_completeAtDTB fs cert (a := m) (b := r) hκ (by simp [maxKeys]; omega)
          (by simp [claimGroup]; omega) hLS
        rwa [show claimGroup * m + r = n by simp [claimGroup]; omega] at this
      · simp only [decide_eq_true_eq] at ht
        refine l17_completeAtB fs cert hchain rfl rfl rfl rfl (by omega) hc hL33 hLκ (by omega)
          (by omega) (fun rd hm => ⟨fun q hq => state_of_reads (hmOwn rd (memL_append.mp hm).2) hq,
            fun j hj => hrec rd (memL_append.mp hm).1 j (by omega)⟩) (fun j hj c hc => ?_)
          (fun j hj => regionL_append_left (hR2 j (by omega)))
          (fun j hj c hc => regionL_append_left (hR3 j (by omega) c hc))
        rw [Nat.add_assoc]; exact hOR _ (by omega)
      · show CompleteAtDTB fs cert κ cclNames[r]! (Lin ++ Own) _ _ _ _
        rw [cclNames_get hr17]
        have hpre : (cellsBytes (cells.take (68 * m))).length = rate * (8 * m) := by
          rw [length_cellsBytes, List.length_take, Nat.min_eq_left (by omega)]
          show 16 * (68 * m) = 136 * (8 * m); omega
        have := ccl_completeAtB fs cert hr17 (Lin := Lin ++ Own) (sP := b0 + 13 * m)
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
    obtain ⟨Nk, Lk, outs, hNk, hoo, hW, hD, -, hKids⟩ :=
      kidsFromInT_of_kidsDTB (fs := fs) (cert := cert) κ ks clTs
        [SB "list_split", (m + 1) * fs "__loop16", fs (cclNames.getD r "")] hokB (b0 + 13 * (m + 1))
    have hl0 : outs.length = 3 := hoo.length
    obtain ⟨o1, t1, rfl, hl1⟩ := exists_of_length_succ hl0
    obtain ⟨o2, t2, rfl, hl2⟩ := exists_of_length_succ hl1
    obtain ⟨o3, t3, rfl, hl3⟩ := exists_of_length_succ hl2
    obtain rfl := List.eq_nil_of_length_eq_zero hl3
    obtain ⟨h1, h2, h3, -⟩ := hoo
    refine ⟨fs "child_claim_list_digest" + 13 * (m + 1) + Nk, Own ++ Lk, _, [], ?_, ⟨rfl, rfl⟩, ?_,
      by rw [List.nil_append]; exact disj_append hDo hD hWo hW le_rfl, fun rd hlow hm => ?_⟩
    · have hb := hNk
      simp only [kidsBoundL, ks, List.headD_cons, List.tail_cons, ↓reduceIte, decide_eq_true_eq] at hb
      simp only [ccB, show n ≠ 0 by omega, ↓reduceIte, ← hmdef, ← hrdef]
      split at hb <;> split <;> omega
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
        ⟨"__loop16", [.n 52, .n 27, .n 36, .n 0, .n 1, .n 2, .n 3, .n 4], [], decide (m ≠ 0)⟩,
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
