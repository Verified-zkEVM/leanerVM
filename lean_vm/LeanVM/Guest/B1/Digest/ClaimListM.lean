/-
  LeanVM.Guest.B1.Digest.ClaimListM

  `claims_tail`, `claims_window` and `claim_list_digest` under a hash model: the rows each window
  and tail checked, the windows extending a prefix from the IV, and the last block the answered
  hash of the claim list.
-/

module

public import LeanVM.Guest.B1.Digest.ClaimList
public import LeanVM.Guest.B1.Digest.CommonM
public import LeanVM.Guest.B1.Digest.ScaledLogM

/-!
# Claim lists over a hash model

The deployed proofs (`ClaimTail`, `ClaimWindow`, `ClaimSpec`, `ClaimList`) name every chaining
value: a window's state is `digestScalars (prefixDigest cs (32q))`. Over a `HashModel` (pattern C
of `docs/roadmap/w2-guest-model.md`):

* a tail and a window state the rows they checked from the state handed to them
  (`Meaning_claims_tailB`, `Meaning_claims_windowB`, over `ChainSteps S`), for any semantics `S`;
* `claim_list_digest`'s windows carry a prefix of the blocks absorbed so far through the scratch
  table (`WinInvM`, `windows_fwdM`), the tail extends it, and the last block reads the answered
  hash (`final_model`): `claim_list_digest_model` concludes `M.H (cs.flatMap cellBytes) = some d`.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-! ## The last block and the empty list -/

section Final

variable {M : HashModel}

/-- **The last block** (`claim_list_digest`, G:2797-2798), forward: from a prefix of the first
`n - 1` blocks, the last block at the total length with the final flag gives the answered hash of
the cells (`final_iff`'s forward direction). -/
theorem final_model {cs : List E} {n : ℕ} (hlen : cs.length = 4 * n) (hn : 1 ≤ n) {st : E × E}
    (hp : M.Prefix (prefixBlocks cs (n - 1)) st) {d0 d1 : E}
    (hc : M.sem.check (blocksOf cs (n - 1)) st.1 st.2 d0 d1 (metadataCell (64 * n) true)) :
    ∃ d, M.H (cs.flatMap cellBytes) = some d ∧ (d0, d1) = digestScalars d := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hp hc
  have := HashModel.final_block hp (by rw [length_prefixBlocks]; exact hc)
  rwa [prefixBlocks, ← List.flatMap_def, ← List.flatMap_singleton (f := fun j =>
      blockBytes (blocksOf cs j)) m, ← List.flatMap_append, ← List.range_succ,
    ← flatMap_cellBytes_blocks cs (m + 1) hlen] at this

/-- At the deployed model the prefix of the first `k` blocks is the chaining value after them. -/
theorem deployedPrefix_prefixBlocks (cs : List E) (k : ℕ) :
    HashModel.deployed.Prefix (prefixBlocks cs k) (digestScalars (prefixDigest cs k)) :=
  ⟨fun b hb => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hb
    exact length_blockBytes _, rfl⟩

end Final

/-! ## `claims_tail__L{k}` -/

/-- **`claims_tail__L{k}` under `S`**: `k` claims at `ptr`, the rows chained from the state under
`baseMd base`; the pointer past them. -/
def Meaning_claims_tailB (S : BlakeSem) (k : ℕ) (rd : Reader) (args rets : List E) : Prop :=
  ∃ s0 s1 base ptr o0 o1 p', args = [s0, s1, base, ptr] ∧ rets = [o0, o1, p'] ∧
    p' = ptr * gen ^ (4 * k) ∧ ∃ cs : List E, cs.length = 4 * k ∧ CellsAt rd ptr cs ∧
      ChainSteps S (s0, s1) (blocksOf cs) (baseMd base) k (o0, o1)

section Tail

variable {S : BlakeSem}

/-- `claims_tail__L{k}`'s body under `S`, `k ≥ 1`, gives its meaning. -/
theorem claims_tail_succB (k : ℕ) (hk : k < 32) (rd : Reader) (name : String)
    (args rets : List E)
    (h : Fn.SemB S (coreProgram.RelB S rd) rd ⟨name, [.n 0, .n 1, .n 2, .n 3], ctBody k⟩ args rets) :
    Meaning_claims_tailB S k rd args rets := by
  simp only [Fn.SemB, ctBody, holdsListB_atoms, holdsListB_ret, List.forall_mem_append,
    forall_mem_flatMap_range, ctBlk, List.forall_mem_cons, Atom.HoldsB, forall_mem_nil_iff,
    and_true, true_and, List.map_cons, List.map_nil] at h
  obtain ⟨σ, hp, ⟨⟨⟨h4, h5⟩, hblk⟩, h6, h7, h8, h9⟩, hr⟩ := h
  set cs := (List.range (4 * k)).map (fun i => σ (.n (6 + 8 * (i / 4) + i % 4))) with hcsdef
  have hcs : ∀ j r, j < k → r < 4 → cs.getD (4 * j + r) 0 = σ (.n (6 + 8 * j + r)) :=
    cs_getD k (fun i => σ (.n i))
  have hch := chainSteps_of_steps (S := S) (n := k)
    (blocks := fun j => ![σ (.n (6 + 8 * j)), σ (.n (7 + 8 * j)), σ (.n (8 + 8 * j)),
      σ (.n (9 + 8 * j))]) (md := fun j => σ (.n (11 + 8 * j)))
    (st := fun j => (σ (.n (4 + 8 * j)), σ (.n (5 + 8 * j)))) (fun j hj => (hblk j hj).2.2.2.2.2.2)
  refine ⟨σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n (6 + 8 * k)), σ (.n (7 + 8 * k)),
    σ (.n (9 + 8 * k)), hp.symm, hr.symm, by rw [h9, h8, tailC_eq k hk], cs, by simp [cs], ?_, ?_⟩
  · intro i hi
    have hi' : i < 4 * k := by simpa [cs] using hi
    obtain ⟨j, r, hr4, rfl⟩ : ∃ j r, r < 4 ∧ i = 4 * j + r := ⟨i / 4, i % 4, by omega, by omega⟩
    rw [← List.getD_eq_getElem _ 0 hi, hcs j r (by omega) hr4]
    obtain ⟨l0, l1, l2, l3, -⟩ := hblk j (by omega)
    interval_cases r
    · simpa using l0
    · rw [show 6 + 8 * j + 1 = 7 + 8 * j by omega]; exact l1
    · rw [show 6 + 8 * j + 2 = 8 + 8 * j by omega]; exact l2
    · rw [show 6 + 8 * j + 3 = 9 + 8 * j by omega]; exact l3
  · rw [chainSteps_congr (b' := fun j => ![σ (.n (6 + 8 * j)), σ (.n (7 + 8 * j)),
        σ (.n (8 + 8 * j)), σ (.n (9 + 8 * j))]) (md' := fun j => σ (.n (11 + 8 * j)))
        (fun j hj => ?_) (fun j hj => ?_)]
    · simp only [Nat.mul_zero, Nat.add_zero] at hch
      rw [← h4, ← h5, h6, h7]
      exact hch
    · have e0 := hcs j 0 hj (by omega)
      have e1 := hcs j 1 hj (by omega)
      have e2 := hcs j 2 hj (by omega)
      have e3 := hcs j 3 hj (by omega)
      rw [Nat.add_zero, Nat.add_zero] at e0
      rw [show 6 + 8 * j + 1 = 7 + 8 * j by omega] at e1
      rw [show 6 + 8 * j + 2 = 8 + 8 * j by omega] at e2
      rw [show 6 + 8 * j + 3 = 9 + 8 * j by omega] at e3
      simp only [blocksOf, e0, e1, e2, e3]
    · rw [baseMd, (hblk j hj).2.2.2.2.2.1, (hblk j hj).2.2.2.2.1, word_md]

/-- `claims_tail__L0`'s body under `S` gives its meaning. -/
theorem claims_tail_zeroB (rd : Reader) (name : String) (args rets : List E)
    (h : Fn.SemB S (coreProgram.RelB S rd) rd ⟨name, [.n 0, .n 1, .n 2, .n 3], ctBody0⟩ args rets) :
    Meaning_claims_tailB S 0 rd args rets := by
  simp only [Fn.SemB, ctBody0, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB] at h
  obtain ⟨σ, hp, h4, h5, h6, h7, h8, hr⟩ := h
  refine ⟨σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 6), σ (.n 7), σ (.n 8), hp.symm, hr.symm,
    by rw [h8, Nat.mul_zero, pow_zero, mul_one], [], rfl, cellsAt_nil _ _,
    ⟨fun _ => (σ (.n 0), σ (.n 1)), rfl, ?_, fun j hj => absurd hj (by omega)⟩⟩
  rw [h6, h7, h4, h5]

/-- **`claims_tail__L{k}` is sound under any semantics**, `k < 32`. -/
theorem claims_tail_B (k : ℕ) (hk : k < 32) (rd : Reader) (args rets : List E)
    (h : coreProgram.RelB S rd (ctNames.getD k "") args rets) :
    Meaning_claims_tailB S k rd args rets := by
  rw [relB_of_find (find_claims_tail k hk)] at h
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exact claims_tail_zeroB rd _ args rets h
  · simp only [show k ≠ 0 by omega, ↓reduceIte] at h
    exact claims_tail_succB k hk rd _ args rets h

end Tail

/-! ## `claims_window` -/

/-- **`claims_window` under `S`**: `x_q·g = g^N`, `N < 2^16`, `nxt = E(2^11·N)`, and the rows of
the 32 claims at `ptr` chained from the state under `windowMd base nxt`. -/
def Meaning_claims_windowB (S : BlakeSem) (rd : Reader) (args rets : List E) : Prop :=
  ∃ s0 s1 base ptr xq gsq o0 o1 nxt, args = [s0, s1, base, ptr, xq, gsq] ∧ rets = [o0, o1, nxt] ∧
    ∃ N < 2 ^ 16, xq * gen = gen ^ N ∧ nxt = eOfNat (2 ^ 11 * N) ∧ ∃ cs : List E,
      cs.length = 128 ∧ CellsAt rd ptr cs ∧
        ChainSteps S (s0, s1) (blocksOf cs) (windowMd base nxt) 32 (o0, o1)

/-- **`claims_window` is sound under any semantics.** -/
theorem claims_window_B {S : BlakeSem} {rd : Reader} {gsq : E} (hT : SquaresAt rd gsq)
    (s0 s1 base ptr xq : E) (rets : List E)
    (h : coreProgram.RelB S rd "claims_window" [s0, s1, base, ptr, xq, gsq] rets) :
    Meaning_claims_windowB S rd [s0, s1, base, ptr, xq, gsq] rets := by
  rw [relB_of_find find_claims_window] at h
  simp only [Fn.SemB, cwBody, holdsListB_atoms, List.cons_append, List.nil_append,
    Stmt.HoldsListB, Stmt.HoldsB, List.forall_mem_append, forall_mem_flatMap_range,
    cwBlk, List.forall_mem_cons, Atom.HoldsB, forall_mem_nil_iff, and_true, true_and, List.map_cons,
    List.map_nil] at h
  obtain ⟨σ, hp, c6, m7, hcall, c9, c10, ⟨hblk, l0, l1, l2, l3, hc, h265, h266, h267⟩, hr⟩ := h
  simp only [List.cons.injEq, and_true] at hp
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hp
  obtain ⟨v, hv, N, hN, h7, h8⟩ := (scaled_log_11_iffB hT _ _).mp hcall
  simp only [List.cons.injEq, and_true] at hv
  set cs := (List.range (4 * 32)).map (fun i => σ (.n (11 + 8 * (i / 4) + i % 4))) with hcsdef
  have hcs : ∀ j r, j < 32 → r < 4 → cs.getD (4 * j + r) 0 = σ (.n (11 + 8 * j + r)) :=
    cs_getD' 11 32 (fun i => σ (.n i))
  have hch := chainSteps_of_steps (S := S) (n := 32)
    (blocks := fun j => ![σ (.n (11 + 8 * j)), σ (.n (12 + 8 * j)), σ (.n (13 + 8 * j)),
      σ (.n (14 + 8 * j))]) (md := fun j => if j < 31 then σ (.n (16 + 8 * j)) else σ (.n 8))
    (st := fun j => if j = 32 then (σ (.n 263), σ (.n 264))
      else (σ (.n (9 + 8 * j)), σ (.n (10 + 8 * j))))
    (fun j hj => by
      rcases (show j < 31 ∨ j = 31 by omega) with h | rfl
      · simp only [show j ≠ 32 by omega, show j + 1 ≠ 32 by omega, h, ↓reduceIte]
        exact (hblk j h).2.2.2.2.2.2
      · exact hc)
  simp only [show (0 : ℕ) ≠ 32 by omega, ↓reduceIte, Nat.mul_zero, Nat.add_zero] at hch
  refine ⟨σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 265), σ (.n 266),
    σ (.n 267), rfl, hr.symm, N, hN, by rw [← h7, m7, c6, word_eq_eOfNat]; rfl,
    by rw [h267, hv, h8], cs, by simp [cs], ?_, ?_⟩
  · intro i hi
    have hi' : i < 128 := by simpa [cs] using hi
    obtain ⟨j, r, hr4, rfl⟩ : ∃ j r, r < 4 ∧ i = 4 * j + r := ⟨i / 4, i % 4, by omega, by omega⟩
    rw [← List.getD_eq_getElem _ 0 hi, hcs j r (by omega) hr4]
    rcases (show j < 31 ∨ j = 31 by omega) with hj | rfl
    · obtain ⟨m0, m1, m2, m3, -⟩ := hblk j hj
      interval_cases r
      · simpa using m0
      · rw [show 11 + 8 * j + 1 = 12 + 8 * j by omega]; exact m1
      · rw [show 11 + 8 * j + 2 = 13 + 8 * j by omega]; exact m2
      · rw [show 11 + 8 * j + 3 = 14 + 8 * j by omega]; exact m3
    · interval_cases r
      exacts [l0, l1, l2, l3]
  · rw [← c9, ← c10, h265, h266, h267]
    rw [chainSteps_congr (b' := fun j => ![σ (.n (11 + 8 * j)), σ (.n (12 + 8 * j)),
        σ (.n (13 + 8 * j)), σ (.n (14 + 8 * j))])
        (md' := fun j => if j < 31 then σ (.n (16 + 8 * j)) else σ (.n 8)) (fun j hj => ?_)
        (fun j hj => ?_)]
    · exact hch
    · have e0 := hcs j 0 hj (by omega)
      have e1 := hcs j 1 hj (by omega)
      have e2 := hcs j 2 hj (by omega)
      have e3 := hcs j 3 hj (by omega)
      rw [Nat.add_zero, Nat.add_zero] at e0
      rw [show 11 + 8 * j + 1 = 12 + 8 * j by omega] at e1
      rw [show 11 + 8 * j + 2 = 13 + 8 * j by omega] at e2
      rw [show 11 + 8 * j + 3 = 14 + 8 * j by omega] at e3
      simp only [blocksOf, e0, e1, e2, e3]
    · unfold windowMd
      split_ifs with h
      · rw [baseMd, (hblk j h).2.2.2.2.2.1, (hblk j h).2.2.2.2.1, word_md]
      · rfl

/-! ## `__loop86` -/

theorem l86_stepB {S : BlakeSem} (rd : Reader) (W c gsq : E) (C : CallRel) (x : E)
    (h : ∃ fn, coreProgram.find? "__loop86" = some fn ∧ fn.SemB S C rd (x :: [W, c, gsq]) []) :
    L86Step rd c gsq C x ∧ IsInK (x * gen + W) ∧
      (x * gen + W ≠ 0 → C "__loop86" (x * gen :: [W, c, gsq]) []) := by
  obtain ⟨fn, hfn, h⟩ := h
  rw [find_loop86, Option.some.injEq] at hfn
  subst hfn
  simp only [Fn.SemB, l86Body, List.cons_append, List.nil_append, Stmt.HoldsListB,
    Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, L86Step, cellsAt_four,
    ← word_gen] at h ⊢
  obtain ⟨σ, hp, m4, m5, m6, l7, l8, l9, l10, hcall, c14, m15, m16, m17, m18, l11, l12, l13,
    l19, c20, m21, l21, c22, m23, a24, c25, m26, hk, hnext, -⟩ := h
  simp only [List.cons.injEq, and_true] at hp
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hp
  rw [m6, m5, m4] at l7 l8 l9 l10 l19
  rw [m18, m17, m16, m15, c14] at l11 l12 l13 l21
  rw [loadHolds_unique l19 l10, c20] at m21
  rw [m21] at l21
  rw [a24, m23, c22] at hk hnext
  rw [m26, c25] at hnext
  exact ⟨⟨_, _, _, _, _, _, _, ⟨l7, l8, l9, l10⟩, hcall, ⟨l11, l12, l13, l21⟩⟩, hk, hnext⟩

/-- The loop's iterations under `S`, from the entry `callIf`: `w` of them, at `g^j`, `j < w`. -/
theorem loop86_itersB {S : BlakeSem} {rd : Reader} {W c gsq : E} {w : ℕ} (hW : W = gen ^ w)
    (hw : w < 2 ^ 33) (h : coreProgram.RelB S rd "__loop86" [gen ^ 0, W, c, gsq] []) :
    ∀ j < w, L86Step rd c gsq (coreProgram.RelB S rd) (gen ^ j) := by
  intro j hj
  obtain ⟨m, hm0, hmN, hfirst, hall⟩ :=
    loopB_fwd (l86Step_mono rd c gsq) (l86_stepB rd W c gsq) 0 h
  have hmw : m = w := by
    rcases Nat.lt_or_ge w m with hlt | hge
    · exact absurd hW.symm (hfirst w (by omega) hlt)
    · exact gen_pow_inj' (by omega) hw (hmN.symm.trans hW)
  exact hall j (by omega) (by omega)

/-! ## `claim_list_digest` -/

/-- What a window establishes of the scratch table under a model: window `q`'s slot holds a
prefix of the first `32q` blocks. -/
def WinInvM (M : HashModel) (rd : Reader) (p c : E) (len q : ℕ) : Prop :=
  (∃ st : E × E, M.Prefix (prefixBlocks (cellsFrom rd p len) (32 * q)) st ∧
    CellsAt rd (c * gen ^ (4 * q)) [st.1, st.2, eOfNat (2 ^ 11 * q), p * gen ^ (128 * q)]) ∧
  (∀ j < 32 * q, ∀ r, IsCanonical128 (blocksOf (cellsFrom rd p len) j r)) ∧
  (∀ i < 128 * q, LoadHolds rd p i (cellAt rd p i))

/-- **The windows, forward, under a model**: from the initial slot (the IV), `w` loop iterations
establish a prefix in each slot, the canonicity and the reads of the first `32w` blocks. -/
theorem windows_fwdM {M : HashModel} {rd : Reader} {gsq p c : E} (hT : SquaresAt rd gsq)
    {len w : ℕ} (hw : 128 * w ≤ len) (hw' : w < 2 ^ 11)
    (h0 : CellsAt rd c [(digestScalars paramIv).1, (digestScalars paramIv).2, 0, p])
    (hstep : ∀ j < w, L86Step rd c gsq (coreProgram.RelB M.sem rd) (gen ^ j)) :
    ∀ q ≤ w, WinInvM M rd p c len q := by
  intro q hq
  induction q with
  | zero =>
    refine ⟨⟨ivCells, M.prefix_nil, ?_⟩, fun j hj => absurd hj (by omega),
      fun i hi => absurd hi (by omega)⟩
    show CellsAt rd (c * gen ^ (4 * 0)) [(digestScalars paramIv).1, (digestScalars paramIv).2,
      eOfNat (2 ^ 11 * 0), p * gen ^ (128 * 0)]
    simpa [eOfNat_zero] using h0
  | succ q ih =>
    obtain ⟨⟨st, hpre, hI⟩, hcan, hld⟩ := ih (by omega)
    obtain ⟨s0, s1, base, ptr, o0, o1, nxt, hslot, hwin, hstore⟩ := hstep q (by omega)
    rw [pow4_eq _ q rfl] at hslot
    rw [cellsAt_four] at hslot hI
    have e0 := loadHolds_unique hslot.1 hI.1
    have e1 := loadHolds_unique hslot.2.1 hI.2.1
    have e2 := loadHolds_unique hslot.2.2.1 hI.2.2.1
    have e3 := loadHolds_unique hslot.2.2.2 hI.2.2.2
    subst e2 e3
    obtain ⟨_, _, _, _, _, _, o0', o1', nxt', hargs, hrets, N, hN, hxq, hnxt, csq, hlen, hcells,
      hch⟩ := claims_window_B hT _ _ _ _ _ _ hwin
    simp only [List.cons.injEq, and_true] at hargs hrets
    obtain ⟨rfl, rfl, rfl, rfl, rfl, -⟩ := hargs
    obtain ⟨rfl, rfl, rfl⟩ := hrets
    rw [← pow_succ] at hxq
    have hNq : N = q + 1 := (gen_pow_inj' (by omega) (lt_trans hN (by norm_num)) hxq).symm
    subst hNq
    have hb := blocksOf_slice (len := len) (b := 32 * q) 32
      (by rw [show 4 * (32 * q) = 128 * q by ring]; exact hcells) hlen (by omega)
    have hst : (s0, s1) = st := by rw [e0, e1]
    rw [hst] at hch
    obtain ⟨hcan', hpre'⟩ := chainSteps_prefix (k := 32 * q) hpre hb
      (fun j hj => by rw [hnxt]; exact windowMd_eq q j hj) hch
    refine ⟨⟨(o0, o1), by rw [show 32 * (q + 1) = 32 * q + 32 by ring]; exact hpre', ?_⟩,
      fun j hj => ?_, fun i hi => ?_⟩
    · rw [show c * (gen ^ q * gen * (gen ^ q * gen) * (gen ^ q * gen * (gen ^ q * gen))) =
        c * gen ^ (4 * (q + 1)) by rw [← pow_succ, pow4_eq _ (q + 1) rfl]] at hstore
      rw [cellsAt_four] at hstore ⊢
      rw [← hnxt, show p * gen ^ (128 * (q + 1)) = p * gen ^ (128 * q) * word 325 0 0 by
          rw [word_g128, mul_assoc, ← pow_add, show 128 * (q + 1) = 128 * q + 128 by ring]]
      exact hstore
    · rcases Nat.lt_or_ge j (32 * q) with h | h
      · exact hcan j h
      · have := hcan' (j - 32 * q) (by omega)
        rwa [show 32 * q + (j - 32 * q) = j by omega] at this
    · rcases Nat.lt_or_ge i (128 * q) with h | h
      · exact hld i h
      · have := loads_slice hcells (i - 128 * q) (by omega)
        rwa [show 128 * q + (i - 128 * q) = i by omega] at this

/-- **`claim_list_digest(ptr, n_g, g_squares)` over a hash model**: `n_g = g^n`, `n < 2^16`, and
the digest is the answered hash of the `4n` canonical cells at `ptr`. -/
def Meaning_claim_list_digestWith (M : HashModel) (rd : Reader) (args rets : List E) : Prop :=
  ∃ ptr n_g gsq d0 d1, args = [ptr, n_g, gsq] ∧ rets = [d0, d1] ∧ ∃ n < 2 ^ 16, n_g = gen ^ n ∧
    ∃ cs : List E, cs.length = 4 * n ∧ CellsAt rd ptr cs ∧ (∀ c ∈ cs, IsCanonical128 c) ∧
      ∃ d, M.H (cs.flatMap cellBytes) = some d ∧ (d0, d1) = digestScalars d

/-- The deployed meaning, its scratch table dropped, is the meaning at the deployed model. -/
theorem meaning_claim_list_digestWith_of_deployed {rd : Reader} {args rets : List E}
    (h : Meaning_claim_list_digest rd args rets) :
    Meaning_claim_list_digestWith HashModel.deployed rd args rets := by
  obtain ⟨ptr, n_g, gsq, d0, d1, ha, hr, n, hn, hng, cs, hlen, hcs, hcan, hd, -⟩ := h
  exact ⟨ptr, n_g, gsq, d0, d1, ha, hr, n, hn, hng, cs, hlen, hcs, hcan, _, rfl, hd⟩

/-- **`claim_list_digest` is sound under a hash model** (G:2762-2799): its relation under the
model's semantics gives the answered hash of the claim list. -/
theorem claim_list_digest_model {M : HashModel} {rd : Reader} (hm : MemOk rd) {gsq : E}
    (hT : SquaresAt rd gsq) (p n_g : E) (rets : List E)
    (h : coreProgram.RelB M.sem rd "claim_list_digest" [p, n_g, gsq] rets) :
    Meaning_claim_list_digestWith M rd [p, n_g, gsq] rets := by
  rw [relB_of_find find_claim_list_digest] at h
  simp only [Fn.SemB, cldBody, List.cons_append, List.nil_append, Stmt.HoldsListB,
    Stmt.HoldsB, Atom.HoldsB, true_and, List.map_cons, List.map_nil] at h
  obtain ⟨σ, hp, c3, a4, hk4, hz, hnz⟩ := h
  simp only [List.cons.injEq, and_true] at hp
  obtain ⟨rfl, rfl, rfl⟩ := hp
  by_cases h4 : σ (.n 4) = 0
  · obtain ⟨c5, c6, c7, c8, c9, c10, c11, hc, h60, h61, hr⟩ := hz h4
    have h1 : σ (.n 1) = 1 := by
      rw [a4, c3, word_one] at h4; exact e_add_eq_zero_iff.mp h4
    rw [c5, c6, c7, c8, c9, c10, c11, word_zero, iv0_word, iv1_word, md_final_word] at hc
    obtain ⟨d, hd, hout⟩ := HashModel.empty (M := M) hc
    refine ⟨σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 60), σ (.n 61), rfl, hr.symm, 0, by norm_num,
      by rw [h1, pow_zero], [], rfl, cellsAt_nil _ _, by simp, d, by simpa using hd, ?_⟩
    rw [h60, h61]
    exact hout
  obtain ⟨c16, rc15, c20, rc14, m24, m25, m26, m27, m28, m29, c30, m31, ae, c32, m33, m34, m35,
    c37, l37, c38, l38, c39, l39, l0, c40, a41, c42, hk41, hloop, m43, m44, m45, l46, l47, l48,
    l49, ⟨t, ht, h15, htail⟩, hsl, c54, a55, l56, l57, l58, l59, hfin, h60, h61, hr⟩ := hnz h4
  -- the counts
  obtain ⟨w, e', hw32, he', h14, h21, h20⟩ := rangeCheck_sound hm rc14
  rw [c20, word_g2047] at h20
  have hw : w < 2048 := by have := gen_pow_inj' (by norm_num) (by omega) h20; omega
  have ht32 : t < 32 := by simpa [ctNames] using ht
  have h15' : σ (.n 15) = gen ^ t := by rw [h15, gen_pow_eq_ofK]
  have h28 : σ (.n 28) = gen ^ (32 * w) := by
    rw [m28, m27, m26, m25, m24, h14]; ring
  set n := 32 * w + t + 1 with hn
  have hng : σ (.n 1) = gen ^ n := by
    have e1 := e_add_eq_zero_iff.mp ae
    rw [m29, m31, c30, h28, h15'] at e1
    have : σ (.n 1) = σ (.n 1) * (word 9223372036854775821 0 0 * gen) := by
      rw [ginv_mul_gen, mul_one]
    rw [this, ← mul_assoc, ← e1, ← pow_add, ← pow_succ]
  obtain ⟨v, hv, N, hN, hN1, hN53⟩ := (scaled_log_6_iffB hT _ _).mp hsl
  simp only [List.cons.injEq, and_true] at hv
  have hNn : N = n := gen_pow_inj' (lt_trans hN (by norm_num)) (by omega) (hN1.symm.trans hng)
  subst hNn
  -- the windows
  have h0c : CellsAt rd (σ (.n 36)) [(digestScalars paramIv).1, (digestScalars paramIv).2, 0,
      σ (.n 0)] := by
    rw [cellsAt_four, ← iv0_word, ← iv1_word, ← word_zero, ← c37, ← c38, ← c39]
    exact ⟨l37, l38, l39, l0⟩
  have hsteps : ∀ j < w, L86Step rd (σ (.n 36)) (σ (.n 2)) (coreProgram.RelB M.sem rd)
      (gen ^ j) := by
    intro j hj
    have hne : σ (.n 41) ≠ 0 := by
      rw [a41, c40, word_one, h14]
      intro h
      have := (gen_pow_eq_one_iff (by omega)).mp (e_add_eq_zero_iff.mp h).symm
      omega
    have hl := hloop hne
    rw [c42, word_one, ← pow_zero gen] at hl
    exact loop86_itersB h14 (by omega) hl j hj
  have hwin := windows_fwdM (M := M) (len := 4 * n) hT (by omega) (by omega) h0c hsteps
  obtain ⟨⟨st, hpre, hIw⟩, hcanw, hldw⟩ := hwin w le_rfl
  have h45 : σ (.n 45) = σ (.n 36) * gen ^ (4 * w) := by rw [m45, m44, m43, pow4_eq _ w h14]
  rw [h45] at l46 l47 l48 l49
  rw [cellsAt_four] at hIw
  have e46 := loadHolds_unique l46 hIw.1
  have e47 := loadHolds_unique l47 hIw.2.1
  have e48 := loadHolds_unique l48 hIw.2.2.1
  have e49 := loadHolds_unique l49 hIw.2.2.2
  -- the tail
  rw [← List.getD_eq_getElem _ "" ht] at htail
  have htail := claims_tail_B t ht32 rd _ _ htail
  obtain ⟨_, _, _, _, _, _, _, hargs, hrets, hp', cst, hlent, hcellst, hcht⟩ := htail
  simp only [List.cons.injEq, and_true] at hargs hrets
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hargs
  obtain ⟨rfl, rfl, rfl⟩ := hrets
  rw [e49, show 128 * w = 4 * (32 * w) by ring] at hcellst
  have hbt := blocksOf_slice (len := 4 * n) (b := 32 * w) t hcellst hlent (by omega)
  rw [e46, e47, e48] at hcht
  obtain ⟨hcant, hpret⟩ := chainSteps_prefix (k := 32 * w) hpre hbt
    (fun j hj => baseMd_eq w j (by omega)) hcht
  -- the last block
  have h52 : σ (.n 52) = σ (.n 0) * gen ^ (4 * (n - 1)) := by
    rw [hp', e49, mul_assoc, ← pow_add]; congr 2; omega
  rw [h52] at l56 l57 l58 l59
  rw [loadHolds_mul_gen_pow] at l56 l57 l58 l59
  rw [Nat.add_zero] at l56
  set cs := cellsFrom rd (σ (.n 0)) (4 * n) with hcs
  have hlast : blocksOf cs (n - 1) = ![σ (.n 56), σ (.n 57), σ (.n 58), σ (.n 59)] := by
    have hr : ∀ r < 4, cs.getD (4 * (n - 1) + r) 0 = cellAt rd (σ (.n 0)) (4 * (n - 1) + r) :=
      fun r hr => cellsFrom_getD (by omega)
    have r0 := hr 0 (by omega)
    rw [Nat.add_zero] at r0
    simp only [blocksOf, r0, hr 1 (by omega), hr 2 (by omega), hr 3 (by omega),
      cellAt_of_load l56, cellAt_of_load l57, cellAt_of_load l58, cellAt_of_load l59]
  have h55 : σ (.n 55) = metadataCell (64 * n) true := by
    rw [a55, c54, hv, hN53, md_final_word, eOfNat_add_metadataCell, Nat.xor_zero]; rfl
  rw [← hlast, h55] at hfin
  rw [show 32 * w + t = n - 1 by omega] at hpret
  have hcanl := (M.canonical hfin).1
  have hcan : ∀ j < n, ∀ r, IsCanonical128 (blocksOf cs j r) := by
    intro j hj
    rcases (show j < 32 * w ∨ 32 * w ≤ j ∧ j < 32 * w + t ∨ j = n - 1 by omega) with
      h | ⟨h1, h2⟩ | rfl
    · exact hcanw j h
    · have := hcant (j - 32 * w) (by omega)
      rwa [show 32 * w + (j - 32 * w) = j by omega] at this
    · exact hcanl
  have hlen : cs.length = 4 * n := length_cellsFrom _ _ _
  obtain ⟨d, hd, hout⟩ := final_model (st := (σ (.n 50), σ (.n 51))) hlen (by omega) hpret hfin
  refine ⟨σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 60), σ (.n 61), rfl, hr.symm, n, hN, hng, cs, hlen,
    ?_, canonical_of_blocks hlen hcan, d, hd, by rw [h60, h61]; exact hout⟩
  intro i hi
  rw [hlen] at hi
  simp only [hcs, cellsFrom, List.getElem_map, List.getElem_range]
  rcases (show i < 128 * w ∨ 128 * w ≤ i ∧ i < 128 * w + 4 * t ∨ 4 * (n - 1) ≤ i by omega)
    with h | ⟨h1, h2⟩ | h
  · exact hldw i h
  · have := loads_slice hcellst (i - 4 * (32 * w)) (by omega)
    rwa [show 4 * (32 * w) + (i - 4 * (32 * w)) = i by omega] at this
  · obtain ⟨r, hr4, rfl⟩ : ∃ r, r < 4 ∧ i = 4 * (n - 1) + r :=
      ⟨i - 4 * (n - 1), by omega, by omega⟩
    interval_cases r
    · rw [Nat.add_zero]; exact load_cellAt l56
    · exact load_cellAt l57
    · exact load_cellAt l58
    · exact load_cellAt l59

end
end LeanVM.Guest.B1.Digest
