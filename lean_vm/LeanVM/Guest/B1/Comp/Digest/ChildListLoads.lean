/-
  LeanVM.Guest.B1.Comp.Digest.ChildListLoads

  `child_claim_list_digest` complete over a completeness model in the uniform placed form by
  trees loading the child's claim blocks (`CompleteRelBST`).
-/

module

public import LeanVM.Guest.B1.Comp.Digest.ChildLoadsRun

/-!
# `child_claim_list_digest`, its tree loading the child's claims

`ChildListAtC.lean`'s `ccld_completeRelBS` with the placed tree loading the words of
`CclPreAtC`'s `ChildReads`: block `j < n` of the child's list, its mark at
`cover·(origin·g^(off j))` and its claim's four cells at `entries·g^(4·off j)`.

* `WinA … j`, `L87A … w j`: the blocks of window `j` (`32·j, …, 32·j + 31`), of windows
  `j, …, w - 1`; `l87_iterBST`, `l87_completeAtBST`: `__loop87`'s iterations by trees loading
  them (`completeAtS_loopBT`), each window's tree loading its blocks (`ccw_completeAtBST`);
* `ccld_completeRelBST`: the windows by `__loop87`, the tail's `t` blocks by
  `child_claims_tail__L{t}` (`cct_completeAtBST`), the last block by the body's own loads
  (`loadEq_of_addr`), at `CclLoadsQ off cs`: the tree loads `ChildLoads … (cs.length / 4)`;
* `ccld_completeRelBS_of_BST`: forgetting the loads.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.Value LeanVM.E2E.Complete
open LeanVM.Protocol.Verifier (gen eOfNat)
open LeanVM.Guest.B1 (LowDef CompleteAtBS CompleteAtBST CompleteRelBS CompleteRelBST RelAtInBT kidsBound
  DisjL disj_nil disj_append Within Returns LoadsAll completeRel_casesBST)
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- **A path's load reads the memory's word**: an address the path loads from, holding `v`. -/
theorem loadEq_of_addr {S : BlakeSem} {rd : Reader} {σ : Val} {es : List Ev}
    (hes : ∀ e ∈ es, e.HoldsB S rd σ) {A : K} {v : E} (hA : A ∈ loadAddrs σ es) (hv : rd A = some v) :
    (A, v) ∈ evLoadEqns σ es := by
  obtain ⟨e, he, hea⟩ := List.mem_filterMap.mp hA
  cases e with
  | atom a =>
    cases a with
    | load d p off =>
      simp only [Ev.loadAddr?, Option.some.injEq] at hea
      subst hea
      have hl : LoadHolds rd (σ p) off (σ d) := hes _ he
      rw [show v = σ d from Option.some.inj (hv.symm.trans hl.2)]
      exact LeanVM.Guest.B1.mem_evLoadEqns he
    | _ => simp [Ev.loadAddr?] at hea
  | _ => simp [Ev.loadAddr?] at hea

theorem loadsAll_of_eq {A A' : K × E → Prop} {t : Tree} (h : A = A') (ht : LoadsAll A' t) :
    LoadsAll A t := h ▸ ht

theorem relAtInBT_of_relAtInB {S : BlakeSem} {fs : String → ℕ} {cert : String → V → ℕ} {rd : Reader}
    {R D : ℕ → Prop} {fp n : ℕ} {f : String} {args rets : List E} {Q : Tree → Prop}
    (h : RelAtInB S coreProgram fs cert rd R D fp n f args rets) (hQ : ∀ t, Q t) :
    RelAtInBT S fs cert rd R D fp n f args rets Q :=
  let ⟨t, hn, hv, hb, hp, ht, hl, hd⟩ := h
  ⟨t, hQ t, hn, hv, hb, hp, ht, hl, hd⟩

/-! ## The windows -/

/-- The load equations of window `j`: the blocks `32·j, …, 32·j + 31`, as `ccw_completeAtBST`'s
tree at the window's arguments loads them. -/
def WinA (entries cover base origin : E) (off : ℕ → ℕ) (cs : List E) (j : ℕ) : K × E → Prop :=
  ChildLoadsA entries cover (base * pow32 (gen ^ j)) origin (fun k => off (32 * j + k))
    (sliceOf cs (32 * j) 32) 32

/-- The load equations of the windows `j, …, w - 1`. -/
def L87A (entries cover base origin : E) (off : ℕ → ℕ) (cs : List E) (w j : ℕ) (q : K × E) : Prop :=
  ∃ j', j ≤ j' ∧ j' < w ∧ WinA entries cover base origin off cs j' q

/-- **One iteration of `__loop87` over the model, complete, placed, by a tree loading its windows**
(`l87_iterBS`), from the next one's. -/
theorem l87_iterBST {CM : CompModel} (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 16 ≤ κ)
    (KL : Layout)
    {gsq base entries cover origin : E} {cx L n w : ℕ} (hL16 : L ≤ 2 ^ 16) (hn : n < 2 ^ 16)
    (hw : 32 * w < n)
    {off : ℕ → ℕ} {cs : List E} (hlen : cs.length = 4 * n) (hcan : ∀ x ∈ cs, IsCanonical128 x)
    {d : Digest} (hH : CM.H (cs.flatMap cellBytes) = some d)
    (hR : ∀ rd, LowDef κ rd → MemL rd KL → ChildReads rd entries cover base origin (gen ^ L) off cs n)
    (hsq : ∀ rd, MemL rd KL → SquaresAt rd gsq)
    (hscr : ∀ rd, MemL rd KL → ChildScratchC CM rd (gen ^ cx) cs w)
    (hreg : ∀ A, ChildLoad entries cover origin off n A → ∃ i, A = gpow i ∧ RegionL KL i)
    (hsR : ∀ q ≤ w, ∀ r < 3, RegionL KL (cx + 4 * q + r)) (Bsl : ℕ)
    (hsl : TotalLeB CM.sem coreProgram fs "scaled_log__L11" fun _ => Bsl) {j : ℕ} (hj : j < w)
    (hnext : j + 1 < w → CompleteAtBST CM.sem fs cert κ "__loop87" KL
      [gen ^ (j + 1), gen ^ w, gen ^ cx, base, entries, cover, origin, gen ^ L, gsq] (Returns [])
      (l87Bound fs (fs "child_claims_window" + Bsl) w (j + 1))
      fun _ _ t => LoadsAll (L87A entries cover base origin off cs w (j + 1)) t) :
    CompleteAtBST CM.sem fs cert κ "__loop87" KL
      [gen ^ j, gen ^ w, gen ^ cx, base, entries, cover, origin, gen ^ L, gsq] (Returns [])
      (l87Bound fs (fs "child_claims_window" + Bsl) w j)
      fun _ _ t => LoadsAll (L87A entries cover base origin off cs w j) t := by
  have hlow : ∀ rd, LowDef κ rd → Low16 rd := fun rd hl i hi =>
    hl i (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hκ))
  have hch : ChainSteps CM.sem (CM.st (prefixAt (cs.flatMap cellBytes) (32 * j)))
      (blocksOf (sliceOf cs (32 * j) 32)) (windowMd (eOfNat (2 ^ 11 * j)) (eOfNat (2 ^ 11 * (j + 1)))) 32
      (CM.st (prefixAt (cs.flatMap cellBytes) (32 * j + 32))) :=
    chainSteps_cells CM hlen hH hcan (k := 32 * j) (m := 32) (by omega)
      (blocksOf_sliceOf cs (32 * j) 32) (fun i hi => windowMd_eq j i hi)
  have hRj : ∀ rd, LowDef κ rd → MemL rd KL → ChildReads rd entries cover (base * pow32 (gen ^ j)) origin
      (gen ^ L) (fun k => off (32 * j + k)) (sliceOf cs (32 * j) 32) 32 := fun rd hl hL => by
    rw [pow32_eq]; exact childReads_slice (hR rd hl hL) (32 * j) 32 (by omega)
  have htk : j + 1 < w → decide (gen ^ j * word 2 0 0 + gen ^ w ≠ 0) = true := fun h => by
    refine decide_eq_true fun h0 => ?_
    rw [word_gen, ← pow_succ] at h0
    have := gen_pow_inj' (by omega) (by omega) (e_add_eq_zero_iff.mp h0)
    omega
  refine LeanVM.Guest.B1.completeAtS_loopBT find_loop87 (by rw [Program.loop_of_find? find_loop87]; decide +kernel)
    κ KL _ []
    [⟨"child_claims_window", true,
      cclSlotC CM cs j ++ [entries, cover, base * pow32 (gen ^ j), origin, gen ^ L, gen ^ j, gsq],
      KL, [(CM.st (prefixAt (cs.flatMap cellBytes) (32 * j + 32))).1,
        (CM.st (prefixAt (cs.flatMap cellBytes) (32 * j + 32))).2, eOfNat (2 ^ 11 * (j + 1))]⟩]
    ⟨"__loop87", decide (gen ^ j * word 2 0 0 + gen ^ w ≠ 0),
      [gen ^ (j + 1), gen ^ w, gen ^ cx, base, entries, cover, origin, gen ^ L, gsq], KL, []⟩
    (fun _ => fs "child_claims_window" + Bsl) (l87Bound fs (fs "child_claims_window" + Bsl) w (j + 1))
    (fun _ => WinA entries cover base origin off cs j) (L87A entries cover base origin off cs w (j + 1))
    ?_ ?_ (l87Bound fs (fs "child_claims_window" + Bsl) w j)
    (by simpa [kidsBound, KidR.kid] using l87Bound_step fs (fs "child_claims_window" + Bsl) w j hj) ?_
    (L87A entries cover base origin off cs w j) ?_
  · intro k hk _
    simp only [List.mem_singleton] at hk
    subst hk
    exact ccw_completeAtBST fs cert hκ KL hL16 rfl (N := j + 1) (by omega) (pow_succ gen j).symm rfl hRj hsq
      (fun A hA => hreg A (childLoad_shift (by omega) hA)) hch Bsl hsl
  · intro ht
    refine hnext ?_
    have : gen ^ j * word 2 0 0 + gen ^ w ≠ 0 := by simpa using ht
    rw [word_gen, ← pow_succ] at this
    by_contra h
    exact this (by rw [show w = j + 1 by omega]; exact e_add_self _)
  · intro k _ _ i hi
    simp only [List.mem_append, List.mem_singleton] at *
    rcases ‹_ ∨ _› with rfl | rfl <;> exact hi
  intro rd hl hL
  refine ⟨fun k hk => by
    simp only [List.mem_append, List.mem_singleton] at hk; rcases hk with rfl | rfl <;> exact hL, ?_⟩
  have hT := hsq rd hL
  have hs := hscr rd hL j (by omega)
  have ho := hscr rd hL (j + 1) (by omega)
  have hcall := ccw_relB_low (hlow rd hl) hT hL16 rfl (N := j + 1) (by omega) (pow_succ gen j).symm rfl
    (hRj rd hl hL) hch
  have hsteps := l87_steps_lowC (hlow rd hl) hT hL16 hn hw hlen (hR rd hl hL) hcan hH (hscr rd hL)
  have hk : IsInK (gen ^ j * gen + gen ^ w) := by
    rw [← pow_succ, gen_pow_eq_ofK, gen_pow_eq_ofK, ← ofK_add]; exact ofK_isInK _
  have hnx : gen ^ j * gen + gen ^ w ≠ 0 → coreProgram.RelB CM.sem rd "__loop87"
      (gen ^ j * gen :: [gen ^ w, gen ^ cx, base, entries, cover, origin, gen ^ L, gsq]) [] := fun h => by
    rw [← pow_succ] at h ⊢
    have hjw : j + 1 < w := by
      by_contra h'
      exact h (by rw [show w = j + 1 by omega]; exact e_add_self _)
    exact loopB_bwd (B := L87Step rd (gen ^ cx) base entries cover origin (gen ^ L) gsq
        (coreProgram.RelB CM.sem rd))
      (fun x hB hK hnext => l87_step_bwdB rd (gen ^ w) (gen ^ cx) base entries cover origin (gen ^ L) gsq x
        hB hK hnext) hjw rfl (fun i _ h2 => hsteps i h2)
  have hh := l87_holdsB (Sem := CM.sem) (C := coreProgram.RelB CM.sem rd) (W := gen ^ w)
    (by rw [pow4_eq _ j rfl]; exact hs) hcall (by rw [← pow_succ, pow4_eq _ (j + 1) rfl]; exact ho) hk hnx
  set σ := listVal (l87List (gen ^ j) (gen ^ w) (gen ^ cx) base entries cover origin (gen ^ L) gsq
    (CM.st (prefixAt (cs.flatMap cellBytes) (32 * j))).1 (CM.st (prefixAt (cs.flatMap cellBytes) (32 * j))).2
    (eOfNat (2 ^ 11 * j))
    (CM.st (prefixAt (cs.flatMap cellBytes) (32 * j + 32))).1
    (CM.st (prefixAt (cs.flatMap cellBytes) (32 * j + 32))).2
    (eOfNat (2 ^ 11 * (j + 1)))) with hσ
  have hwk : walk σ l87Body = .ret (l87S.flatMap (Main.slEvs σ)) [] := by
    rw [l87Body_eq]; exact Main.walk_straight σ _ _ l87S_straight
  obtain ⟨e1, e2, e3, e4, e5⟩ := l87_events σ
  refine ⟨σ, _, [], rfl, hwk, rfl, holdsB_of_holdsList find_loop87 hh hwk, ?_, e2, e3, e4, fun A hA => ?_,
    fun q ⟨j', hj1, hj2, hq⟩ => ?_⟩
  · rw [e1]
    refine ⟨rfl, rfl, fun _ => ⟨rfl, rfl⟩, rfl, rfl, fun _ => ⟨?_, rfl⟩, trivial⟩
    show [gen ^ j * word 2 0 0, _, _, _, _, _, _, _, _] = _
    rw [word_gen, ← pow_succ]
    rfl
  · rw [e5] at hA
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
    have g11 : σ (.n 11) = gen ^ (cx + 4 * j) := by
      show gen ^ cx * (gen ^ j * gen ^ j * (gen ^ j * gen ^ j)) = _
      rw [pow4_eq _ j rfl, ← pow_add]
    have g28 : σ (.n 28) = gen ^ (cx + 4 * (j + 1)) := by
      show gen ^ cx * (gen ^ j * word 2 0 0 * (gen ^ j * word 2 0 0) *
        (gen ^ j * word 2 0 0 * (gen ^ j * word 2 0 0))) = _
      rw [word_gen, ← pow_succ, pow4_eq _ (j + 1) rfl, ← pow_add]
    rcases hA with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by rw [g11, limb0_gen_pow, gpow_add'], hsR j (by omega) 0 (by omega)⟩
    · exact ⟨_, by rw [g11, limb0_gen_pow, gpow_add'], hsR j (by omega) 1 (by omega)⟩
    · exact ⟨_, by rw [g11, limb0_gen_pow, gpow_add'], hsR j (by omega) 2 (by omega)⟩
    · exact ⟨_, by rw [g28, limb0_gen_pow, gpow_add'], hsR (j + 1) (by omega) 0 (by omega)⟩
    · exact ⟨_, by rw [g28, limb0_gen_pow, gpow_add'], hsR (j + 1) (by omega) 1 (by omega)⟩
    · exact ⟨_, by rw [g28, limb0_gen_pow, gpow_add'], hsR (j + 1) (by omega) 2 (by omega)⟩
  · rcases Nat.eq_or_lt_of_le hj1 with rfl | hlt
    · exact Or.inr (Or.inl ⟨_, List.mem_singleton_self _, rfl, hq⟩)
    · exact Or.inr (Or.inr ⟨htk (by omega), j', by omega, hj2, hq⟩)

/-- **`__loop87`'s iterations over the model are complete, uniformly placed, by trees loading
their windows** (`l87_completeAtBS`). -/
theorem l87_completeAtBST {CM : CompModel} (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ}
    (hκ : 16 ≤ κ) (KL : Layout)
    {gsq base entries cover origin : E} {cx L n w : ℕ} (hL16 : L ≤ 2 ^ 16) (hn : n < 2 ^ 16)
    (hw : 32 * w < n)
    {off : ℕ → ℕ} {cs : List E} (hlen : cs.length = 4 * n) (hcan : ∀ x ∈ cs, IsCanonical128 x)
    {d : Digest} (hH : CM.H (cs.flatMap cellBytes) = some d)
    (hR : ∀ rd, LowDef κ rd → MemL rd KL → ChildReads rd entries cover base origin (gen ^ L) off cs n)
    (hsq : ∀ rd, MemL rd KL → SquaresAt rd gsq)
    (hscr : ∀ rd, MemL rd KL → ChildScratchC CM rd (gen ^ cx) cs w)
    (hreg : ∀ A, ChildLoad entries cover origin off n A → ∃ i, A = gpow i ∧ RegionL KL i)
    (hsR : ∀ q ≤ w, ∀ r < 3, RegionL KL (cx + 4 * q + r)) (Bsl : ℕ)
    (hsl : TotalLeB CM.sem coreProgram fs "scaled_log__L11" fun _ => Bsl) :
    ∀ j < w, CompleteAtBST CM.sem fs cert κ "__loop87" KL
      [gen ^ j, gen ^ w, gen ^ cx, base, entries, cover, origin, gen ^ L, gsq] (Returns [])
      (l87Bound fs (fs "child_claims_window" + Bsl) w j)
      fun _ _ t => LoadsAll (L87A entries cover base origin off cs w j) t := by
  suffices H : ∀ d j, j + d + 1 = w → CompleteAtBST CM.sem fs cert κ "__loop87" KL
      [gen ^ j, gen ^ w, gen ^ cx, base, entries, cover, origin, gen ^ L, gsq] (Returns [])
      (l87Bound fs (fs "child_claims_window" + Bsl) w j)
      (fun _ _ t => LoadsAll (L87A entries cover base origin off cs w j) t) from
    fun j hj => H (w - j - 1) j (by omega)
  intro e
  induction e with
  | zero =>
    exact fun j hj => l87_iterBST fs cert hκ KL hL16 hn hw hlen hcan hH hR hsq hscr hreg hsR Bsl hsl
      (j := j) (by omega) (fun h => absurd h (by omega))
  | succ e ih =>
    exact fun j hj => l87_iterBST fs cert hκ KL hL16 hn hw hlen hcan hH hR hsq hscr hreg hsR Bsl hsl
      (j := j) (by omega) (fun _ => ih (j + 1) (by omega))

/-! ## `child_claim_list_digest` -/

/-- The load equations of `child_claim_list_digest`'s callee `f`: the windows' for `__loop87`, the
tail's `t` blocks (from block `32·w`) for `child_claims_tail__L{t}`, none for `scaled_log__L6`. -/
def cclKidA (entries cover base origin : E) (off : ℕ → ℕ) (cs : List E) (w t : ℕ) (f : String) :
    K × E → Prop :=
  if f = "__loop87" then L87A entries cover base origin off cs w 0
  else if f = "scaled_log__L6" then fun _ => False
  else ChildLoadsA entries cover (base * pow32 (gen ^ w)) origin (fun k => off (32 * w + k))
    (sliceOf cs (32 * w) t) t

theorem cclKidA_l87 {entries cover base origin : E} {off : ℕ → ℕ} {cs : List E} {w t : ℕ} :
    cclKidA entries cover base origin off cs w t "__loop87" = L87A entries cover base origin off cs w 0 :=
  ite_eq_left rfl

theorem cclKidA_sl6 {entries cover base origin : E} {off : ℕ → ℕ} {cs : List E} {w t : ℕ} :
    cclKidA entries cover base origin off cs w t "scaled_log__L6" = fun _ => False := by
  rw [cclKidA, ite_eq_right (by decide), ite_eq_left rfl]

theorem cclKidA_cct {entries cover base origin : E} {off : ℕ → ℕ} {cs : List E} {w t : ℕ} {f : String}
    (h1 : f ≠ "__loop87") (h2 : f ≠ "scaled_log__L6") :
    cclKidA entries cover base origin off cs w t f = ChildLoadsA entries cover (base * pow32 (gen ^ w))
      origin (fun k => off (32 * w + k)) (sliceOf cs (32 * w) t) t := by
  rw [cclKidA, ite_eq_right h1, ite_eq_right h2]

/-- **What `child_claim_list_digest`'s tree loads**: the child's blocks `j < cs.length / 4` (the
marks' slots and the claims' cells of `CclPreAtC`'s `ChildReads`). -/
def CclLoadsQ (off : ℕ → ℕ) (cs : List E) : List E → List E → ℕ → Reader → Tree → Prop
  | [entries, cover, base, origin, _, _, _], _, _, _, t =>
      ChildLoads t entries cover base origin off cs (cs.length / 4)
  | _, _, _, _, _ => True

/-- **`child_claim_list_digest` is complete over a completeness model, uniformly placed, at the
indices `off` and the claims `cs`, by trees loading the child's blocks** (`ccld_completeRelBS`): on a
memory defined below `2^κ`, `κ ≥ 16`, at claims whose digest the model answers, by trees within
`ccldBound` satisfying `CclLoadsQ off cs`. -/
theorem ccld_completeRelBST {CM : CompModel} (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ}
    (hκ : 16 ≤ κ) (off : ℕ → ℕ) (cs : List E) (Bsl Bsl6 : ℕ)
    (hsl : TotalLeB CM.sem coreProgram fs "scaled_log__L11" fun _ => Bsl)
    (hsl6 : TotalLeB CM.sem coreProgram fs "scaled_log__L6" fun _ => Bsl6) :
    CompleteRelBST CM.sem fs cert κ "child_claim_list_digest" (CclPreAtC CM.H off cs)
      (ccldBound fs (fs "child_claims_window" + Bsl) Bsl6 (cs.length / 4)) (CclLoadsQ off cs) := by
  intro args rets Lin hpre
  classical
  by_cases hex : ∃ rd1, LowDef κ rd1 ∧ MemL rd1 Lin
  swap
  · intro fp
    refine ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, Nat.zero_le _,
      fun rd hl hL => absurd ⟨rd, hl, ?_⟩ hex⟩
    simpa using hL
  obtain ⟨rd1, hl1, hL1⟩ := hex
  obtain ⟨entries, cover, base, origin, limit, ng, gsq, d0, d1, rfl, rfl⟩ := cclPreAtC_shape (hpre rd1 hl1 hL1)
  obtain ⟨hT1, ⟨L, hL16, rfl⟩, n, hn, rfl, hlen, hR1, hcan, d, hH, hd⟩ := hpre rd1 hl1 hL1
  refine CompleteAtBST.qmono (Q := fun _ _ t => LoadsAll (ChildLoadsA entries cover base origin off cs n) t) ?_
    fun fp rd t ht => ?_
  swap
  · show ChildLoads t entries cover base origin off cs (cs.length / 4)
    rw [show cs.length / 4 = n by omega]
    exact LoadsAll.childLoads ht
  intro fp
  have hpre' : ∀ rd, LowDef κ rd → MemL rd Lin →
      SquaresAt rd gsq ∧ ChildReads rd entries cover base origin (gen ^ L) off cs n := by
    intro rd hl hL
    obtain ⟨hT, -, n', hn', hng', -, hR', -, -⟩ := hpre rd hl hL
    obtain rfl : n = n' := gen_pow_inj' (by omega) (by omega) hng'
    exact ⟨hT, hR'⟩
  have hFc : ∀ j r, ∃ i, j < n → r < 4 →
      (entries * gen ^ (4 * off j)).limb 0 * gpow r = gpow i ∧ RegionL Lin i := by
    intro j r
    by_cases h : j < n ∧ r < 4
    · obtain ⟨hj, hr⟩ := h
      have hall : ∀ rd, LowDef κ rd → MemL rd Lin →
          LoadHolds rd (entries * gen ^ (4 * off j)) r (cs.getD (4 * j + r) 0) := by
        intro rd hl hL
        have hc4 := ((hpre' rd hl hL).2 j hj).2.2
        exact match r, hr with
          | 0, _ => by simpa using hc4 0 (by simp)
          | 1, _ => by simpa using hc4 1 (by simp)
          | 2, _ => by simpa using hc4 2 (by simp)
          | 3, _ => by simpa using hc4 3 (by simp)
          | _ + 4, hr => absurd hr (by omega)
      obtain ⟨i, hi⟩ := forced_load hall hl1 hL1
      exact ⟨i, fun _ _ => hi⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose cidx hcidx using hFc
  have hFm : ∀ j, ∃ i, j < n → (cover * (origin * gen ^ off j)).limb 0 * gpow 0 = gpow i ∧
      RegionL Lin i := by
    intro j
    by_cases h : j < n
    · obtain ⟨i, hi⟩ := forced_load (fun rd hl hL => ((hpre' rd hl hL).2 j h).2.1) hl1 hL1
      exact ⟨i, fun _ => hi⟩
    · exact ⟨0, fun h1 => absurd h1 h⟩
  choose midx hmidx using hFm
  have hSq : ∀ j, ∃ i, j < 16 → gsq.limb 0 * gpow j = gpow i ∧ RegionL Lin i := by
    intro j
    by_cases hj : j < 16
    · obtain ⟨i, hi⟩ := forced_load (fun rd hl hL => (hpre' rd hl hL).1 j hj) hl1 hL1
      exact ⟨i, fun _ => hi⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose sidx hsidx using hSq
  have hgK : IsInK gsq := (hT1 0 (by norm_num)).1
  have hlow : ∀ rd, LowDef κ rd → Low16 rd := fun rd hl i hi =>
    hl i (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hκ))
  set PL : Layout := ccldPins cs base n cidx midx ++ pinL (fun j => gen ^ 2 ^ j) sidx 16 with hPL
  -- the pins read back as the reads and the squares table
  have hPLr : ∀ rd', MemL rd' PL →
      SquaresAt rd' gsq ∧ ChildReads rd' entries cover base origin (gen ^ L) off cs n := by
    intro rd' h
    refine ⟨fun j hj => pin_loads h hgK (fun j hj => (hsidx j hj).1)
        (fun q hq => List.mem_append_right _ hq) j hj,
      fun j hj => ⟨(hR1 j hj).1, load_of_pin h (hR1 j hj).2.1.1 (hmidx j hj).1
        (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))),
        fun r hr => ?_⟩⟩
    have hr4 : r < 4 := by simpa using hr
    have := load_of_pin h ((hR1 j hj).2.2 0 (by simp)).1 (hcidx j r hj hr4).1 (v := cs.getD (4 * j + r) 0)
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj,
        List.mem_map.mpr ⟨r, List.mem_range.mpr hr4, rfl⟩⟩)))
    have key : ([cs.getD (4 * j) 0, cs.getD (4 * j + 1) 0, cs.getD (4 * j + 2) 0, cs.getD (4 * j + 3) 0] :
        List E)[r]'hr = cs.getD (4 * j + r) 0 := getElem_four cs j r hr4
    rw [key]; exact this
  have hPLm : ∀ rd, MemL rd Lin → MemL rd PL := by
    intro rd hL q hq k hk
    have e : ∀ {i : ℕ} {v : E}, RegionL Lin i → rd1 (gpow i) = some v → q = (i, [v]) →
        LoadHolds rd (ofK (gpow q.1)) k (q.2[k]'hk) := fun {i v} hR hv hqe => by
      subst hqe
      simp only [List.length_cons, List.length_nil] at hk
      obtain rfl : k = 0 := by omega
      refine ⟨ofK_isInK _, ?_⟩
      rw [Main.addr_ofK, Nat.add_zero, Main.memL_agree hL hL1 _ hR, hv]
      rfl
    rw [hPL, List.mem_append, ccldPins, List.mem_append] at hq
    rcases hq with (hq | hq) | hq
    · obtain ⟨j, hj, hq⟩ := List.mem_flatMap.mp hq
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
      have hj := List.mem_range.mp hj
      have hr := List.mem_range.mp hr
      refine e (hcidx j r hj hr).2 ?_ rfl
      have := ((hR1 j hj).2.2 r (by simp; omega)).2
      rw [(hcidx j r hj hr).1] at this
      rw [this]
      exact match r, hr with
        | 0, _ => by simp
        | 1, _ => by simp
        | 2, _ => by simp
        | 3, _ => by simp
        | _ + 4, hr => absurd hr (by omega)
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
      have hj := List.mem_range.mp hj
      refine e (hmidx j hj).2 ?_ rfl
      have := (hR1 j hj).2.1.2
      rwa [(hmidx j hj).1] at this
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
      have hj := List.mem_range.mp hj
      refine e (hsidx j hj).2 ?_ rfl
      have := (hT1 j hj).2
      rwa [(hsidx j hj).1] at this
  have hPLR : ∀ i, RegionL PL i → RegionL Lin i := by
    intro i ⟨q, hq, h1, h2⟩
    rw [hPL, List.mem_append, ccldPins, List.mem_append] at hq
    rcases hq with (hq | hq) | hq
    · obtain ⟨j, hj, hq⟩ := List.mem_flatMap.mp hq
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
      simp only [List.length_cons, List.length_nil] at h1 h2
      rw [show i = cidx j r by omega]
      exact (hcidx j r (List.mem_range.mp hj) (List.mem_range.mp hr)).2
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
      simp only [List.length_cons, List.length_nil] at h1 h2
      rw [show i = midx j by omega]
      exact (hmidx j (List.mem_range.mp hj)).2
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
      simp only [List.length_cons, List.length_nil] at h1 h2
      rw [show i = sidx j by omega]
      exact (hsidx j (List.mem_range.mp hj)).2
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · obtain rfl : cs = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
    refine ⟨fs "child_claim_list_digest", [], [d0, d1], [], ⟨rfl, rfl⟩, by simp [Within], disj_nil,
      by unfold ccldBound; omega, fun rd hl hL => relAtInBT_of_relAtInB ?_
        fun _ _ ⟨j, hj, _⟩ => absurd hj (Nat.not_lt_zero _)⟩
    have h8 : listVal (ccldZeroList entries cover base origin (gen ^ L) gsq d0 d1) (.n 8) = 0 := by
      show (1 : E) + word 1 0 0 = 0; rw [word_one, e_add_self]
    have hw := walk_ccld_zero _ h8
    have hev := holdsB_of_holdsList find_child_claim_list_digest
      (ccld_holds_zeroC (CM := CM) rd entries cover base origin (gen ^ L) gsq hH hd) hw
    obtain ⟨e1, e2, e3, e4, e5⟩ :=
      ccld_zero_events (listVal (ccldZeroList entries cover base origin (gen ^ L) gsq d0 d1))
    have h := relAtInB_of_walk (S := CM.sem) (P := coreProgram) (fs := fs) (cert := cert) (rd := rd)
      coreProgram_wf (R := RegionL Lin) (D := RegionL []) (Dk := fun _ => False) (fp := fp) (N := 0)
      find_child_claim_list_digest (Or.inl (by decide +kernel)) rfl hw rfl hev (by rw [e1, e2]; rfl)
      (by rw [e3]; simp) (by rw [e4]; exact ⟨rfl, fun _ h => h⟩) (by rw [e5]; simp)
      (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
    rwa [e2, List.sum_nil, Nat.add_zero, Nat.add_zero] at h
  obtain ⟨w, hw⟩ : ∃ w, w = (n - 1) / 32 := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = (n - 1) % 32 := ⟨_, rfl⟩
  have ht32 : t < 32 := by omega
  have hwt : n = 32 * w + t + 1 := by omega
  let KL : ℕ → Layout := fun fp => cclScratchLC CM cs (fp + fs "child_claim_list_digest") w ++ PL
  have hKL : ∀ fp rd', MemL rd' (KL fp) → SquaresAt rd' gsq ∧
      ChildReads rd' entries cover base origin (gen ^ L) off cs n ∧
        ChildScratchC CM rd' (gen ^ (fp + fs "child_claim_list_digest")) cs w :=
    fun fp rd' h => ⟨(hPLr rd' (Main.memL_append.mp h).2).1, (hPLr rd' (Main.memL_append.mp h).2).2,
      cclScratchC_of_memL h fun q hq => List.mem_append_left _ hq⟩
  have hKLreg : ∀ fp i, RegionL (KL fp) i →
      RegionL (cclScratchLC CM cs (fp + fs "child_claim_list_digest") w) i ∨ RegionL Lin i := by
    intro fp i ⟨q, hq, h1, h2⟩
    rcases List.mem_append.mp hq with hq | hq
    · exact Or.inl ⟨q, hq, h1, h2⟩
    · exact Or.inr (hPLR i ⟨q, hq, h1, h2⟩)
  have hregKL : ∀ fp A, ChildLoad entries cover origin off n A → ∃ i, A = gpow i ∧ RegionL (KL fp) i := by
    intro fp A hA
    rcases hA with ⟨j, hj, rfl⟩ | ⟨j, hj, r, hr, rfl⟩
    · refine ⟨midx j, (hmidx j hj).1, ⟨(midx j, [base * gen ^ j]), ?_, le_refl _, by simp⟩⟩
      exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))
    · refine ⟨cidx j r, (hcidx j r hj hr).1, ⟨(cidx j r, [cs.getD (4 * j + r) 0]), ?_, le_refl _, by simp⟩⟩
      exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, List.mem_map.mpr ⟨r, List.mem_range.mpr hr, rfl⟩⟩)))
  have hch : ChainSteps CM.sem (CM.st (prefixAt (cs.flatMap cellBytes) (32 * w)))
      (blocksOf (sliceOf cs (32 * w) t)) (baseMd (eOfNat (2 ^ 11 * w))) t
      (CM.st (prefixAt (cs.flatMap cellBytes) (n - 1))) := by
    have := chainSteps_cells CM hlen hH hcan (k := 32 * w) (m := t) (by omega)
      (blocksOf_sliceOf cs (32 * w) t) (fun j hj => baseMd_eq w j (by omega))
    rwa [show 32 * w + t = n - 1 by omega] at this
  refine LeanVM.Guest.B1.completeAtS_nodeBT find_child_claim_list_digest (by
      rw [Program.loop_of_find? find_child_claim_list_digest]; decide +kernel) κ Lin _ _ [4 * (w + 1)]
    (fun fp => cclScratchLC CM cs (fp + fs "child_claim_list_digest") w)
    (fun fp i hi => ⟨(4 * (w + 1), fp + fs "child_claim_list_digest"), List.mem_singleton_self _,
      (cclScratchC_region hi).1, (cclScratchC_region hi).2⟩)
    (fun fp q hq => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
      have := List.mem_range.mp hj
      simp only [cclSlotC, List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
      omega) (fun _ => cclScratchLC_disj)
    (fun fp => [⟨"__loop87", decide (word 1 0 0 + gen ^ w ≠ 0),
        [gen ^ 0, gen ^ w, gen ^ (fp + fs "child_claim_list_digest"), base, entries, cover, origin, gen ^ L,
          gsq], KL fp, []⟩,
      ⟨cctNames[t]!, true, cclSlotC CM cs w ++ [entries, cover, base * pow32 (gen ^ w), origin, gen ^ L],
        KL fp, [(CM.st (prefixAt (cs.flatMap cellBytes) (n - 1))).1,
          (CM.st (prefixAt (cs.flatMap cellBytes) (n - 1))).2]⟩,
      ⟨"scaled_log__L6", true, [gen ^ n, gsq], KL fp, [eOfNat (2 ^ 6 * n)]⟩])
    (fun k => if k.f = "__loop87" then l87Bound fs (fs "child_claims_window" + Bsl) w 0
      else if k.f = "scaled_log__L6" then Bsl6 else fs k.f)
    (fun k => cclKidA entries cover base origin off cs w t k.f) ?_ ?_
    (ccldBound fs (fs "child_claims_window" + Bsl) Bsl6 (cs.length / 4)) ?_
    (ChildLoadsA entries cover base origin off cs n) ?_ fp
  · intro fp k hk htk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    · have hw0 : 0 < w := by
        rcases Nat.eq_zero_or_pos w with h0 | h0
        · simp [h0, word_one, e_add_self] at htk
        · exact h0
      refine CompleteAtBST.qmono (CompleteAtBST.bmono (l87_completeAtBST fs cert hκ (KL fp) hL16 hn (by omega) hlen hcan hH
        (fun rd _ h => (hKL fp rd h).2.1)
        (fun rd h => (hKL fp rd h).1) (fun rd h => (hKL fp rd h).2.2) (hregKL fp)
        (fun q hq r hr => by
          obtain ⟨e, he, h1, h2⟩ := cclScratchC_slot (CM := CM) (cs := cs)
            (b := fp + fs "child_claim_list_digest") (w := w) hq hr
          exact ⟨e, List.mem_append_left _ he, h1, h2⟩) Bsl hsl 0 hw0) (by simp [KidR.kid]))
        fun _ _ tr ht => loadsAll_of_eq (cclKidA_l87) ht
    · show CompleteAtBST CM.sem fs cert κ cctNames[t]! _ _ _ _ _
      have hne := cct_ne t ht32
      rw [cctNames_getElem! ht32] at hne ⊢
      refine CompleteAtBST.qmono (CompleteAtBST.bmono (cct_completeAtBST fs cert hκ t ht32 (KL fp) hL16 rfl (off := fun k => off (32 * w + k))
        (cs := sliceOf cs (32 * w) t)
        (fun rd _ h => by rw [pow32_eq]; exact childReads_slice (hKL fp rd h).2.1 (32 * w) t (by omega))
        (fun A hA => hregKL fp A (childLoad_shift (by omega) hA)) hch)
        (by simp only [hne.1, hne.2, ↓reduceIte, KidR.kid, le_refl]))
        fun _ _ tr ht => loadsAll_of_eq (cclKidA_cct hne.1 hne.2) ht
    · exact (LeanVM.Guest.B1.completeAtS_of_rel_pureB cldKid_pure (by simp [cldKidSet])
        (fun rd h => (scaled_log_6_iffB (hKL fp rd h).1 _ _).mpr ⟨_, rfl, n, hn, rfl, rfl⟩) κ hsl6).toBST.qmono
        fun _ _ _ _ => loadsAll_of_eq (cclKidA_sl6) fun _ h => h.elim
  · intro fp k hk _ i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl <;> exact hKLreg fp i hi
  · intro fp
    obtain ⟨hw0, hl87⟩ : True ∧ fs "__loop87" ≤ l87Bound fs (fs "child_claims_window" + Bsl) w 0 :=
      ⟨trivial, by unfold l87Bound; omega⟩
    have hc : n = cs.length / 4 := by omega
    have hw' : w = (n - 1) / 32 := hw
    simp only [kidsBound, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, KidR.kid, ccldBound,
      ← hc, ← hw']
    have hne := cct_ne t ht32
    have e1 : ("scaled_log__L6" = "__loop87") = False := by decide
    rw [show (n - 1) % 32 = t from ht.symm, cctNames_getElem! ht32] at *
    simp only [↓reduceIte, hne.1, hne.2, e1, Nat.add_zero]
    split <;> omega
  · intro fp' rd hl hLb hLin
    have hPL := hPLm rd hLin
    refine ⟨fun k hk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl <;> exact Main.memL_append.mpr ⟨hLb, hPL⟩, ?_⟩
    obtain ⟨hT, hR⟩ := hpre' rd hl hLin
    have hscr : ChildScratchC CM rd (gen ^ (fp' + fs "child_claim_list_digest")) cs ((n - 1) / 32) := by
      rw [← hw]; exact cclScratchC_of_memL hLb fun q hq => hq
    obtain ⟨t1, t2, t3, t4, t5, t6, hh⟩ := ccld_holds_posC (hlow rd hl) hT hL16 hn hn1 hlen hR hcan hscr hH hd
    rw [← hw, ← ht] at hh
    set σ := listVal (cclListS entries cover base origin (gen ^ L) gsq (gen ^ (fp' + fs "child_claim_list_digest"))
      d0 d1 cs (off (n - 1)) L n w t t1 t2 t3 t4 t5 t6 (CM.st (prefixAt (cs.flatMap cellBytes) (32 * w)))
      (CM.st (prefixAt (cs.flatMap cellBytes) (n - 1)))) with hσ
    have h8 : σ (.n 8) ≠ 0 := fun h' => by
      have h'' : gen ^ n + word 1 0 0 = 0 := h'
      rw [word_one] at h''
      have := (gen_pow_eq_one_iff (by omega)).mp (e_add_eq_zero_iff.mp h'')
      omega
    have hw' := walk_ccld_pos σ h8 ht32 (gen_pow_eq_ofK t)
    have hev := holdsB_of_holdsList find_child_claim_list_digest hh hw'
    obtain ⟨e1, e2, e3, e4, e5⟩ := ccld_pos_events σ t
    have h39 : logG (σ (.n 39)) = 4 * (w + 1) := by
      rw [show σ (.n 39) = gen ^ (4 * (w + 1)) by
        show gen ^ w * word 2 0 0 * (gen ^ w * word 2 0 0) * (gen ^ w * word 2 0 0 * (gen ^ w * word 2 0 0)) = _
        rw [word_gen]; ring]
      exact logG_gen_pow (by omega)
    refine ⟨σ, _, _, rfl, hw', rfl, hev, ?_, e3, by rw [e2, h39], ?_, fun A hA => ?_, fun q hq => ?_⟩
    · rw [e4]
      refine ⟨rfl, rfl, fun _ => ⟨?_, rfl⟩, rfl, rfl, fun _ => ⟨rfl, rfl⟩, rfl, rfl, fun _ => ⟨rfl, rfl⟩,
        trivial⟩
      show [word 1 0 0, gen ^ w, gen ^ (fp' + fs "child_claim_list_digest"), base, entries, cover, origin,
        gen ^ L, gsq] = _
      rw [word_one, pow_zero]
    · rw [e1]
      simp only [List.map_cons, List.map_nil, bases]
      rw [← gen_pow_eq_ofK]; rfl
    · rw [e5] at hA
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
      set cx := fp' + fs "child_claim_list_digest" with hcx
      have g40 : σ (.n 40) = gen ^ cx := rfl
      have g49 : σ (.n 49) = gen ^ (cx + 4 * w) := by
        show gen ^ cx * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w)) = _
        ring
      have g71 : σ (.n 71) = cover * (origin * gen ^ off (n - 1)) := rfl
      have g74 : σ (.n 74) = entries * gen ^ (4 * off (n - 1)) := by
        show entries * (gen ^ off (n - 1) * gen ^ off (n - 1) * (gen ^ off (n - 1) * gen ^ off (n - 1))) = _
        rw [pow4_eq _ _ rfl]
      have sl : ∀ q r, q ≤ w → r < 3 → RegionL (cclScratchLC CM cs cx w) (cx + 4 * q + r) :=
        fun q r hq hr => cclScratchC_slot hq hr
      rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨cx + 4 * 0 + 0, by rw [g40, limb0_gen_pow, gpow_add'], Or.inl (sl 0 0 (by omega) (by omega))⟩
      · exact ⟨cx + 4 * 0 + 1, by rw [g40, limb0_gen_pow, gpow_add'], Or.inl (sl 0 1 (by omega) (by omega))⟩
      · exact ⟨cx + 4 * 0 + 2, by rw [g40, limb0_gen_pow, gpow_add'], Or.inl (sl 0 2 (by omega) (by omega))⟩
      · exact ⟨cx + 4 * w + 0, by rw [g49, limb0_gen_pow, gpow_add'], Or.inl (sl w 0 le_rfl (by omega))⟩
      · exact ⟨cx + 4 * w + 1, by rw [g49, limb0_gen_pow, gpow_add'], Or.inl (sl w 1 le_rfl (by omega))⟩
      · exact ⟨cx + 4 * w + 2, by rw [g49, limb0_gen_pow, gpow_add'], Or.inl (sl w 2 le_rfl (by omega))⟩
      · exact ⟨_, by rw [g71]; exact (hmidx (n - 1) (by omega)).1, Or.inr (hmidx (n - 1) (by omega)).2⟩
      · exact ⟨_, by rw [g74]; exact (hcidx (n - 1) 0 (by omega) (by omega)).1,
          Or.inr (hcidx (n - 1) 0 (by omega) (by omega)).2⟩
      · exact ⟨_, by rw [g74]; exact (hcidx (n - 1) 1 (by omega) (by omega)).1,
          Or.inr (hcidx (n - 1) 1 (by omega) (by omega)).2⟩
      · exact ⟨_, by rw [g74]; exact (hcidx (n - 1) 2 (by omega) (by omega)).1,
          Or.inr (hcidx (n - 1) 2 (by omega) (by omega)).2⟩
      · exact ⟨_, by rw [g74]; exact (hcidx (n - 1) 3 (by omega) (by omega)).1,
          Or.inr (hcidx (n - 1) 3 (by omega) (by omega)).2⟩
    · obtain ⟨i, hi, hb⟩ := hq
      rcases (show i < 32 * w ∨ (32 * w ≤ i ∧ i < 32 * w + t) ∨ i = n - 1 by omega) with
        hiw | ⟨hi1, hi2⟩ | rfl
      · refine Or.inr ⟨_, List.mem_cons_self, ?_, ?_⟩
        · show decide (word 1 0 0 + gen ^ w ≠ 0) = true
          refine decide_eq_true fun h0 => ?_
          rw [word_one] at h0
          have := (gen_pow_eq_one_iff (by omega)).mp (e_add_eq_zero_iff.mp h0).symm
          omega
        · show cclKidA entries cover base origin off cs w t "__loop87" q
          rw [cclKidA_l87]
          refine ⟨i / 32, Nat.zero_le _, by omega, i % 32, by omega, ?_⟩
          rw [pow32_eq]
          exact blockEq_slice (by omega) (by rw [show 32 * (i / 32) + i % 32 = i by omega]; exact hb)
      · refine Or.inr ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, rfl, ?_⟩
        show cclKidA entries cover base origin off cs w t cctNames[t]! q
        rw [cclKidA_cct (cct_ne t ht32).1 (cct_ne t ht32).2]
        refine ⟨i - 32 * w, by omega, ?_⟩
        rw [pow32_eq]
        exact blockEq_slice (by omega) (by rw [show 32 * w + (i - 32 * w) = i by omega]; exact hb)
      · refine Or.inl ?_
        have g71 : σ (.n 71) = cover * (origin * gen ^ off (n - 1)) := rfl
        have g74 : σ (.n 74) = entries * gen ^ (4 * off (n - 1)) := by
          show entries * (gen ^ off (n - 1) * gen ^ off (n - 1) * (gen ^ off (n - 1) * gen ^ off (n - 1))) = _
          rw [pow4_eq _ _ rfl]
        rcases hb with rfl | ⟨r, hr, rfl⟩
        · refine loadEq_of_addr hev ?_ (hR (n - 1) (by omega)).2.1.2
          rw [e5, ← g71]
          exact List.mem_map.mpr ⟨(.n 71, 0), by simp, rfl⟩
        · have hr4 : r < 4 := by simpa using hr
          refine loadEq_of_addr hev ?_ ((hR (n - 1) (by omega)).2.2 r hr).2
          rw [e5, ← g74]
          refine List.mem_map.mpr ⟨(.n 74, r), ?_, rfl⟩
          rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 by omega) with rfl | rfl | rfl | rfl <;> simp

/-- `ccld_completeRelBS`, forgetting the loads. -/
theorem ccld_completeRelBS_of_BST {CM : CompModel} (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ}
    (hκ : 16 ≤ κ) (off : ℕ → ℕ) (cs : List E) (Bsl Bsl6 : ℕ)
    (hsl : TotalLeB CM.sem coreProgram fs "scaled_log__L11" fun _ => Bsl)
    (hsl6 : TotalLeB CM.sem coreProgram fs "scaled_log__L6" fun _ => Bsl6) :
    CompleteRelBS CM.sem fs cert κ "child_claim_list_digest" (CclPreAtC CM.H off cs)
      (ccldBound fs (fs "child_claims_window" + Bsl) Bsl6 (cs.length / 4)) :=
  (ccld_completeRelBST fs cert hκ off cs Bsl Bsl6 hsl hsl6).toBS

end
end LeanVM.Guest.B1.Digest
