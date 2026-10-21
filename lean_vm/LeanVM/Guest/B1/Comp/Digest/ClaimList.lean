/-
  LeanVM.Guest.B1.Comp.Digest.ClaimList

  `__loop86` and `claim_list_digest` over a completeness model: the windows and the tail run the
  model's chain of the claims' bytes, the last block reaches the answer.
-/

module

public import LeanVM.Guest.B1.Comp.Digest.ClaimWindow
public import LeanVM.Guest.B1.Comp.Digest.Common

/-!
# Claim lists over a completeness model

`claim_list_digest` hashes the `4n` claims' cells `x = cs.flatMap cellBytes` as `n` blocks: the
windows (`__loop86`, 32 blocks each, their states through the scratch table), the tail, the last
block. Over a `CompModel` answering `x` by `d`, the chain's cells after `k` blocks are
`CM.st (prefixAt x k)` (the deployed `prefixDigest`'s): each window's and the tail's rows are the
model's (`CompModel.step` through `step_cells`), the last one reaches `d` (`final_cells`).

* `ClScratchC CM`: the scratch table holding the model's states (`ClScratch` at the deployed
  model, `clScratchC_deployed`);
* `l86_step_bwdB` (any semantics), `windows_bwdC`: every loop iteration holds;
* `cld_holds_zeroC`, `cld_holds_posC`: the body holds at the honest values (`cld_holds_pos`);
* `claim_list_digest_comp` from `Meaning_claim_list_digestComp CM`, and
  `claim_list_digest_completeC` (`claim_list_digest_complete`'s shape); at `CompModel.deployed`
  the deployed backward direction (`claim_list_digest_of_comp`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.E2E.Complete

@[expose] public section

/-! ## The chain of the claims' bytes -/

/-- Block `j` of the claims' bytes. -/
theorem blockAt_cells {cs : List E} {n : ℕ} (hlen : cs.length = 4 * n) {j : ℕ} (hj : j < n) :
    LeanVM.E2E.Complete.blockAt (cs.flatMap cellBytes) j = blockBytes (blocksOf cs j) := by
  rw [flatMap_cellBytes_blocks cs n hlen]
  exact CompModel.blockAt_blocks _ hj

/-- The first `k ≤ n` blocks of the claims' bytes. -/
theorem prefixAt_cells {cs : List E} {n : ℕ} (hlen : cs.length = 4 * n) {k : ℕ} (hk : k ≤ n) :
    prefixAt (cs.flatMap cellBytes) k = prefixBlocks cs k := by
  simp only [prefixAt, prefixBlocks]
  exact List.map_congr_left fun j hj => blockAt_cells hlen (by have := List.mem_range.mp hj; omega)

/-- **A whole non-final block of the claims' bytes over a completeness model.** -/
theorem step_cells (CM : CompModel) {cs : List E} {n : ℕ} (hlen : cs.length = 4 * n) {d : Digest}
    (hd : CM.H (cs.flatMap cellBytes) = some d) {j : ℕ} (hj : j + 1 < n)
    (hm : ∀ r, IsCanonical128 (blocksOf cs j r)) :
    CM.sem.check (blocksOf cs j) (CM.st (prefixAt (cs.flatMap cellBytes) j)).1
      (CM.st (prefixAt (cs.flatMap cellBytes) j)).2
      (CM.st (prefixAt (cs.flatMap cellBytes) (j + 1))).1
      (CM.st (prefixAt (cs.flatMap cellBytes) (j + 1))).2 (metadataCell (64 * (j + 1)) false) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [flatMap_cellBytes_blocks cs (m + 1) hlen] at hd ⊢
  exact CM.step_blocks hd (by omega) hm

/-- **The last block of the claims' bytes over a completeness model.** -/
theorem final_cells (CM : CompModel) {cs : List E} {n : ℕ} (hlen : cs.length = 4 * n) (hn : 1 ≤ n)
    {d : Digest} (hd : CM.H (cs.flatMap cellBytes) = some d)
    (hm : ∀ r, IsCanonical128 (blocksOf cs (n - 1) r)) :
    CM.sem.check (blocksOf cs (n - 1)) (CM.st (prefixAt (cs.flatMap cellBytes) (n - 1))).1
      (CM.st (prefixAt (cs.flatMap cellBytes) (n - 1))).2 (digestScalars d).1
      (digestScalars d).2 (metadataCell (64 * n) true) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  rw [flatMap_cellBytes_blocks cs (m + 1) hlen] at hd ⊢
  exact CM.final_blocks hd hm

/-- **`m` blocks from block `k` over a completeness model** (a window, the tail): the rows of the
model's chain of the claims' bytes, from the cells after `k` blocks to the cells after `k + m`. -/
theorem chainSteps_cells (CM : CompModel) {cs : List E} {n : ℕ} (hlen : cs.length = 4 * n)
    {d : Digest} (hd : CM.H (cs.flatMap cellBytes) = some d) (hcan : ∀ c ∈ cs, IsCanonical128 c)
    {k m : ℕ} (hkm : k + m < n) {b : ℕ → Fin 4 → E} {md : ℕ → E}
    (hb : ∀ j < m, b j = blocksOf cs (k + j))
    (hmd : ∀ j < m, md j = metadataCell (64 * k + 64 * (j + 1)) false) :
    ChainSteps CM.sem (CM.st (prefixAt (cs.flatMap cellBytes) k)) b md m
      (CM.st (prefixAt (cs.flatMap cellBytes) (k + m))) := by
  refine ⟨fun j => CM.st (prefixAt (cs.flatMap cellBytes) (k + j)), rfl, rfl, fun j hj => ?_⟩
  dsimp only
  rw [hb j hj, hmd j hj, show 64 * k + 64 * (j + 1) = 64 * (k + j + 1) by ring,
    show k + (j + 1) = k + j + 1 by ring]
  exact step_cells CM hlen hd (by omega) (blocks_canonical hlen hcan _ (by omega))

/-! ## `__loop86` -/

/-- One iteration of `__loop86` under any semantics, backward (`l86_step`'s backward half). -/
theorem l86_step_bwdB {S : BlakeSem} (rd : Reader) (W c gsq x : E)
    (h : L86Step rd c gsq (coreProgram.RelB S rd) x) (hk : IsInK (x * gen + W))
    (hnext : x * gen + W ≠ 0 → coreProgram.RelB S rd "__loop86" (x * gen :: [W, c, gsq]) []) :
    ∃ fn, coreProgram.find? "__loop86" = some fn ∧
      fn.SemB S (coreProgram.RelB S rd) rd (x :: [W, c, gsq]) [] := by
  refine ⟨_, find_loop86, ?_⟩
  simp only [Fn.SemB, l86Body, List.cons_append, List.nil_append, Stmt.HoldsListB,
    Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil]
  obtain ⟨s0, s1, base, ptr, o0, o1, nxt, hin, hcall, hout⟩ := h
  rw [cellsAt_four] at hin hout
  obtain ⟨l7, l8, l9, l10⟩ := hin
  obtain ⟨l11, l12, l13, l21⟩ := hout
  rw [← word_gen] at l11 l12 l13 l21 hk hnext
  refine ⟨listVal [x, W, c, gsq, x * x, x * x * (x * x), c * (x * x * (x * x)), s0, s1, base, ptr,
    o0, o1, nxt, word 2 0 0, x * word 2 0 0, x * word 2 0 0 * (x * word 2 0 0),
    x * word 2 0 0 * (x * word 2 0 0) * (x * word 2 0 0 * (x * word 2 0 0)),
    c * (x * word 2 0 0 * (x * word 2 0 0) * (x * word 2 0 0 * (x * word 2 0 0))), ptr,
    word 325 0 0, ptr * word 325 0 0, word 2 0 0, x * word 2 0 0, x * word 2 0 0 + W,
    word 2 0 0, x * word 2 0 0], rfl, ?_⟩
  simp only [listVal, List.getD_cons_succ, List.getD_cons_zero, true_and]
  exact ⟨l7, l8, l9, l10, hcall, l11, l12, l13, l10, l21, hk, hnext, trivial⟩

/-- **The scratch table over a completeness model**: window `q ≤ w` at `chain·g^(4q)`, the model's
cells after `32q` blocks of the claims' bytes, its base `E(2^11·q)` and its first entry
`ptr·g^(128q)` (`ClScratch`). -/
def ClScratchC (CM : CompModel) (rd : Reader) (ptr chain : E) (cs : List E) (w : ℕ) : Prop :=
  ∀ q ≤ w, CellsAt rd (chain * gen ^ (4 * q)) [(CM.st (prefixAt (cs.flatMap cellBytes) (32 * q))).1,
    (CM.st (prefixAt (cs.flatMap cellBytes) (32 * q))).2, eOfNat (2 ^ 11 * q),
    ptr * gen ^ (128 * q)]

/-- **The windows, backward, over a completeness model** (`windows_bwd`): canonical cells whose
bytes the model answers and a scratch table holding the model's states make every loop iteration
hold. -/
theorem windows_bwdC {CM : CompModel} {rd : Reader} {gsq p c : E} (hT : SquaresAt rd gsq)
    {cs : List E} {n w : ℕ} (hlen : cs.length = 4 * n) (hw : 32 * w < n) (hn : n < 2 ^ 16)
    {d : Digest}
    (hd : CM.H (cs.flatMap cellBytes) = some d) (hcells : CellsAt rd p cs)
    (hcan : ∀ x ∈ cs, IsCanonical128 x) (hscr : ClScratchC CM rd p c cs w) :
    ∀ j < w, L86Step rd c gsq (coreProgram.RelB CM.sem rd) (gen ^ j) := by
  intro j hj
  have h0 := hscr j (by omega)
  have h1 := hscr (j + 1) (by omega)
  rw [show 32 * (j + 1) = 32 * j + 32 by ring] at h1
  refine ⟨_, _, _, _, (CM.st (prefixAt (cs.flatMap cellBytes) (32 * j + 32))).1,
    (CM.st (prefixAt (cs.flatMap cellBytes) (32 * j + 32))).2, eOfNat (2 ^ 11 * (j + 1)),
    by rw [pow4_eq _ j rfl]; exact h0, ?_, ?_⟩
  · refine claims_window_compB hT _ _ _ _ _ _ ⟨_, _, _, _, _, _, _, _, _, rfl, rfl, j + 1,
      by omega, (pow_succ gen j).symm, rfl, sliceOf cs (32 * j) 32, length_sliceOf _ _ _, ?_, ?_⟩
    · rw [show 128 * j = 4 * (32 * j) by ring]
      exact cellsAt_sliceOf hcells (by omega)
    · exact chainSteps_cells CM hlen hd hcan (k := 32 * j) (m := 32) (by omega)
        (blocksOf_sliceOf cs (32 * j) 32) (fun i hi => windowMd_eq j i hi)
  · rw [← pow_succ, pow4_eq _ (j + 1) rfl,
      show p * gen ^ (128 * j) * word 325 0 0 = p * gen ^ (128 * (j + 1)) by
        rw [word_g128, mul_assoc, ← pow_add, show 128 * (j + 1) = 128 * j + 128 by ring]]
    exact h1

/-! ## `claim_list_digest` -/

/-- The honest values of `claim_list_digest`, `n = 0` (`ClaimListAt`'s `cldZeroList`). -/
def cldZeroListS (p gsq d0 d1 : E) : List E :=
  [p, 1, gsq, word 1 0 0, 1 + word 1 0 0, word 0 0 0, word 0 0 0, word 0 0 0,
    word 0 0 0, word 13503953895743350343 11912009169889063794 0,
    word 11170449402626986623 6620516960021240235 0, word 0 4294967295 0, d0, d1] ++
    List.replicate 46 0 ++ [d0, d1]

/-- **`claim_list_digest`'s body holds over a completeness model**, `n = 0`: the empty string's
row. -/
theorem cld_holds_zeroC {CM : CompModel} (rd : Reader) (p gsq : E) {d0 d1 : E} {d : Digest}
    (hH : CM.H (([] : List E).flatMap cellBytes) = some d) (hd : (d0, d1) = digestScalars d) :
    Stmt.HoldsListB CM.sem (coreProgram.RelB CM.sem rd) rd (listVal (cldZeroListS p gsq d0 d1))
      cldBody False (fun rs => rs = [d0, d1]) := by
  simp only [cldBody, List.cons_append, List.nil_append, Stmt.HoldsListB,
    Stmt.HoldsB, Atom.HoldsB, true_and, List.map_cons, List.map_nil]
  have h11 : (1 : E) + word 1 0 0 = 0 := by rw [word_one, e_add_self]
  refine ⟨rfl, rfl, ?_, fun _ => ?_, fun h => ?_⟩
  · show IsInK ((1 : E) + word 1 0 0)
    rw [h11, ← ofK_zero]; exact ofK_isInK _
  · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl⟩
    show CM.sem.check ![word 0 0 0, word 0 0 0, word 0 0 0, word 0 0 0]
      (word 13503953895743350343 11912009169889063794 0)
      (word 11170449402626986623 6620516960021240235 0) d0 d1 (word 0 4294967295 0)
    rw [word_zero, iv0_word, iv1_word, md_final_word, show d0 = (d0, d1).1 from rfl,
      show d1 = (d0, d1).2 from rfl, hd]
    exact CM.check_empty hH
  · exfalso; apply h; show (1 : E) + word 1 0 0 = 0; exact h11

/-- The honest values of `claim_list_digest`, `n ≥ 1`, the window `w`'s state `sw` and the state
before the last block `sl` given (`cldList` at the deployed chain). -/
noncomputable def cldListS (p gsq c d0 d1 : E) (cs : List E) (n w t : ℕ) (t1 t2 t3 t4 : E)
    (sw sl : E × E) : List E :=
  [p, gen ^ n, gsq, word 1 0 0, gen ^ n + word 1 0 0, 0, 0, 0, 0, 0, 0, 0, d0,
  d1, gen ^ w, gen ^ t, word 2147483648 0 0, gen ^ (31 - t), t1, t2, word 55834575010 0 0,
  gen ^ (2047 - w), t3, t4, gen ^ w * gen ^ w, gen ^ w * gen ^ w * (gen ^ w * gen ^ w),
  gen ^ w * gen ^ w * (gen ^ w * gen ^ w) * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w)),
  gen ^ w * gen ^ w * (gen ^ w * gen ^ w) * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w)) *
    (gen ^ w * gen ^ w * (gen ^ w * gen ^ w) * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w))),
  gen ^ w * gen ^ w * (gen ^ w * gen ^ w) * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w)) *
    (gen ^ w * gen ^ w * (gen ^ w * gen ^ w) * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w))) *
    (gen ^ w * gen ^ w * (gen ^ w * gen ^ w) * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w)) *
    (gen ^ w * gen ^ w * (gen ^ w * gen ^ w) * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w)))),
  gen ^ w * gen ^ w * (gen ^ w * gen ^ w) * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w)) *
    (gen ^ w * gen ^ w * (gen ^ w * gen ^ w) * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w))) *
    (gen ^ w * gen ^ w * (gen ^ w * gen ^ w) * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w)) *
    (gen ^ w * gen ^ w * (gen ^ w * gen ^ w) * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w)))) *
    gen ^ t,
  word 9223372036854775821 0 0, gen ^ n * word 9223372036854775821 0 0, word 2 0 0,
  gen ^ w * word 2 0 0, gen ^ w * word 2 0 0 * (gen ^ w * word 2 0 0),
  gen ^ w * word 2 0 0 * (gen ^ w * word 2 0 0) * (gen ^ w * word 2 0 0 * (gen ^ w * word 2 0 0)),
  c, word 13503953895743350343 11912009169889063794 0,
  word 11170449402626986623 6620516960021240235 0, word 0 0 0, word 1 0 0,
  word 1 0 0 + gen ^ w, word 1 0 0, gen ^ w * gen ^ w, gen ^ w * gen ^ w * (gen ^ w * gen ^ w),
  c * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w)),
  sw.1, sw.2, eOfNat (2 ^ 11 * w), p * gen ^ (128 * w), sl.1, sl.2,
  p * gen ^ (128 * w) * gen ^ (4 * t),
  eOfNat (2 ^ 6 * n), word 0 4294967295 0, eOfNat (2 ^ 6 * n) + word 0 4294967295 0,
  cs.getD (4 * (n - 1) + 0) 0, cs.getD (4 * (n - 1) + 1) 0, cs.getD (4 * (n - 1) + 2) 0,
  cs.getD (4 * (n - 1) + 3) 0, d0, d1]

/-- The deployed honest values are `cldListS` at the deployed chain's states. -/
theorem cldList_eq_S (p gsq c d0 d1 : E) (cs : List E) (n w t : ℕ) (t1 t2 t3 t4 : E) :
    cldList p gsq c d0 d1 cs n w t t1 t2 t3 t4 = cldListS p gsq c d0 d1 cs n w t t1 t2 t3 t4
      (digestScalars (prefixDigest cs (32 * w))) (digestScalars (prefixDigest cs (n - 1))) := rfl

/-- **`claim_list_digest`'s body holds over a completeness model**, `n ≥ 1`, at its honest values,
on a memory defined below `2^16` holding the squares table, the cells and the windows' scratch
table at `c` (`cld_holds_pos`), when the model answers the claims' bytes. -/
theorem cld_holds_posC {CM : CompModel} {rd : Reader} (hl : Low16 rd) {gsq : E}
    (hT : SquaresAt rd gsq) {p c : E} {n : ℕ} (hn : n < 2 ^ 16) (hn1 : 0 < n) {cs : List E}
    (hlen : cs.length = 4 * n) (hcells : CellsAt rd p cs) (hcan : ∀ x ∈ cs, IsCanonical128 x)
    (hscr : ClScratchC CM rd p c cs ((n - 1) / 32)) {d0 d1 : E} {d : Digest}
    (hH : CM.H (cs.flatMap cellBytes) = some d) (hd : (d0, d1) = digestScalars d) :
    ∃ t1 t2 t3 t4, Stmt.HoldsListB CM.sem (coreProgram.RelB CM.sem rd) rd
      (listVal (cldListS p gsq c d0 d1 cs n ((n - 1) / 32) ((n - 1) % 32) t1 t2 t3 t4
        (CM.st (prefixAt (cs.flatMap cellBytes) (32 * ((n - 1) / 32))))
        (CM.st (prefixAt (cs.flatMap cellBytes) (n - 1))))) cldBody False
      (fun rs => rs = [d0, d1]) := by
  set w := (n - 1) / 32 with hw
  set t := (n - 1) % 32 with ht
  set X := cs.flatMap cellBytes with hX
  have hwt : n = 32 * w + t + 1 := by omega
  have ht32 : t < 32 := by omega
  have hw2 : w < 2048 := by omega
  obtain ⟨t1, t2, l18, -, l19⟩ := rangeCheck_complete_low hl (e := t) (e' := 31 - t) (by omega) (by omega)
  obtain ⟨t3, t4, l22, -, l23⟩ := rangeCheck_complete_low hl (e := w) (e' := 2047 - w) (by omega) (by omega)
  have hsteps := windows_bwdC hT hlen (by omega) hn hH hcells hcan hscr
  have hS := fun q (hq : q ≤ w) => cellsAt_four.mp (hscr q hq)
  obtain ⟨s00, s01, s02, s03⟩ := hS 0 (by omega)
  obtain ⟨sw0, sw1, sw2, sw3⟩ := hS w le_rfl
  simp only [Nat.mul_zero, pow_zero, mul_one, eOfNat_zero, prefixAt_zero, CM.st_nil] at s00 s01 s02 s03
  rw [← pow4_eq _ w rfl] at sw0 sw1 sw2 sw3
  have hb := blocks_canonical hlen hcan
  have hl : ∀ r < 4, LoadHolds rd (p * gen ^ (128 * w) * gen ^ (4 * t)) r
      (cs.getD (4 * (n - 1) + r) 0) := fun r hr => by
    rw [mul_assoc, ← pow_add, loadHolds_mul_gen_pow,
      List.getD_eq_getElem _ _ (by omega), show 128 * w + 4 * t + r = 4 * (n - 1) + r by omega]
    exact hcells _ (by omega)
  have hlast : ![cs.getD (4 * (n - 1) + 0) 0, cs.getD (4 * (n - 1) + 1) 0,
      cs.getD (4 * (n - 1) + 2) 0, cs.getD (4 * (n - 1) + 3) 0] = blocksOf cs (n - 1) := by
    simp [blocksOf]
  have hmd : eOfNat (2 ^ 6 * n) + word 0 4294967295 0 = metadataCell (64 * n) true := by
    rw [md_final_word, eOfNat_add_metadataCell, Nat.xor_zero]; rfl
  refine ⟨t1, t2, t3, t4, ?_⟩
  simp only [cldBody, List.cons_append, List.nil_append, Stmt.HoldsListB,
    Stmt.HoldsB, Atom.HoldsB, true_and, List.map_cons, List.map_nil]
  refine ⟨rfl, rfl, ?_, fun h => ?_, fun _ => ?_⟩
  · show IsInK (gen ^ n + word 1 0 0)
    rw [word_one, gen_pow_eq_ofK, ← ofK_one, ← ofK_add]; exact ofK_isInK _
  · exfalso
    have h' : gen ^ n + word 1 0 0 = 0 := h
    rw [word_one] at h'
    have := (gen_pow_eq_one_iff (by omega)).mp (e_add_eq_zero_iff.mp h')
    omega
  refine ⟨rfl, ⟨l18, ?_, l19⟩, rfl, ⟨l22, ?_, l23⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_,
    rfl, rfl, rfl, rfl, rfl, ?_, rfl, ?_, rfl, ?_, ?_, rfl, rfl, rfl, ?_, ?_, rfl, rfl, rfl, ?_, ?_,
    ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_⟩
  · show word 2147483648 0 0 = gen ^ t * gen ^ (31 - t)
    rw [word_g31, ← pow_add]; congr 1; omega
  · show word 55834575010 0 0 = gen ^ w * gen ^ (2047 - w)
    rw [word_g2047, ← pow_add]; congr 1; omega
  all_goals simp only [listVal, cldListS, List.getD_cons_succ, List.getD_cons_zero]
  · rw [show gen ^ n * word 9223372036854775821 0 0 = gen ^ (32 * w + t) by
      rw [show gen ^ n = gen ^ (32 * w + t) * gen by rw [← pow_succ, hwt], mul_assoc,
        mul_comm gen, ginv_mul_gen, mul_one], e_add_eq_zero_iff]
    ring
  · rw [iv0_word]; exact s00
  · rw [iv1_word]; exact s01
  · rw [word_zero]; exact s02
  · exact s03
  · rw [word_one, gen_pow_eq_ofK, ← ofK_one, ← ofK_add]; exact ofK_isInK _
  · intro h
    rw [word_one, ← pow_zero gen]
    have hw0 : 0 < w := by
      rcases Nat.eq_zero_or_pos w with h0 | h0
      · exfalso; apply h; rw [h0, word_one, pow_zero, e_add_self]
      · exact h0
    exact loopB_bwd (B := L86Step rd c gsq (coreProgram.RelB CM.sem rd))
      (fun x hB hK hnext => l86_step_bwdB rd (gen ^ w) c gsq x hB hK hnext) hw0 rfl
      (fun j _ h2 => hsteps j h2)
  · exact sw0
  · exact sw1
  · exact sw2
  · exact sw3
  · refine ⟨t, by simp [ctNames]; omega, (gen_pow_eq_ofK t), ?_⟩
    rw [← List.getD_eq_getElem _ "" (by simp [ctNames]; omega)]
    refine claims_tail_compB t ht32 rd _ _ ⟨_, _, _, _, _, _, _, rfl, rfl, rfl,
      sliceOf cs (32 * w) t, length_sliceOf _ _ _, ?_, ?_⟩
    · rw [show 128 * w = 4 * (32 * w) by ring]
      exact cellsAt_sliceOf hcells (by omega)
    · have := chainSteps_cells CM hlen hH hcan (k := 32 * w) (m := t) (by omega)
        (blocksOf_sliceOf cs (32 * w) t) (fun j hj => baseMd_eq w j (by omega))
      rwa [show 32 * w + t = n - 1 by omega] at this
  · exact (scaled_log_6_iffB hT _ _).mpr ⟨_, rfl, n, hn, rfl, rfl⟩
  · exact hl 0 (by omega)
  · exact hl 1 (by omega)
  · exact hl 2 (by omega)
  · exact hl 3 (by omega)
  · rw [hlast, hmd, show d0 = (d0, d1).1 from rfl, show d1 = (d0, d1).2 from rfl, hd]
    exact final_cells CM hlen (by omega) hH (hb (n - 1) (by omega))

/-- **`claim_list_digest` over a completeness model**: `n_g = g^n`, `n < 2^16`, the digest is the
model's answer for the `4n` canonical cells at `ptr`, and the windows' scratch table holds the
model's states (`Meaning_claim_list_digest`). -/
def Meaning_claim_list_digestComp (CM : CompModel) (rd : Reader) (args rets : List E) : Prop :=
  ∃ ptr n_g gsq d0 d1, args = [ptr, n_g, gsq] ∧ rets = [d0, d1] ∧ ∃ n < 2 ^ 16, n_g = gen ^ n ∧
    ∃ cs : List E, cs.length = 4 * n ∧ CellsAt rd ptr cs ∧ (∀ c ∈ cs, IsCanonical128 c) ∧
      ∃ d, CM.H (cs.flatMap cellBytes) = some d ∧ (d0, d1) = digestScalars d ∧
        (n = 0 ∨ ∃ chain, ClScratchC CM rd ptr chain cs ((n - 1) / 32))

/-- **`claim_list_digest` is complete over a completeness model** (G:2762-2799). -/
theorem claim_list_digest_comp {CM : CompModel} {rd : Reader} (hm : MemOk rd) {gsq : E}
    (hT : SquaresAt rd gsq) (p n_g : E) (rets : List E)
    (h : Meaning_claim_list_digestComp CM rd [p, n_g, gsq] rets) :
    coreProgram.RelB CM.sem rd "claim_list_digest" [p, n_g, gsq] rets := by
  rw [relB_of_find find_claim_list_digest]
  obtain ⟨p', n_g', gsq', d0, d1, hargs, rfl, n, hn, rfl, cs, hlen, hcells, hcan, d, hH, hd,
    hscr⟩ := h
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl⟩ := hargs
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · obtain rfl : cs = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
    exact ⟨listVal (cldZeroListS p gsq d0 d1), by simp [listVal, cldZeroListS], by
      simpa only [pow_zero] using cld_holds_zeroC (CM := CM) rd p gsq hH hd⟩
  · obtain ⟨c, hc⟩ := hscr.resolve_left (by omega)
    obtain ⟨t1, t2, t3, t4, h⟩ := cld_holds_posC hm.low16 hT hn hn1 hlen hcells hcan hc hH hd
    exact ⟨_, rfl, h⟩

/-- **Completeness over a completeness model** (`claim_list_digest_complete`), for every pointer
`chain` of the windows' `HeapBuf` holding the model's states. -/
theorem claim_list_digest_completeC {CM : CompModel} {rd : Reader} (hm : MemOk rd) {gsq : E}
    (hT : SquaresAt rd gsq) (chain ptr : E) {n : ℕ} (hn : n < 2 ^ 16) {cs : List E}
    (hlen : cs.length = 4 * n) (hcs : CellsAt rd ptr cs) (hcan : ∀ c ∈ cs, IsCanonical128 c)
    {d : Digest} (hH : CM.H (cs.flatMap cellBytes) = some d)
    (hS : 0 < n → ClScratchC CM rd ptr chain cs ((n - 1) / 32)) :
    coreProgram.RelB CM.sem rd "claim_list_digest" [ptr, gen ^ n, gsq]
      [(digestScalars d).1, (digestScalars d).2] :=
  claim_list_digest_comp hm hT _ _ _ ⟨ptr, _, gsq, _, _, rfl, rfl, n, hn, rfl, cs, hlen, hcs,
    hcan, d, hH, rfl, (Nat.eq_zero_or_pos n).imp id fun h => ⟨chain, hS h⟩⟩

/-! ## At the deployed model -/

/-- At the deployed model the scratch table is the deployed one. -/
theorem clScratchC_deployed {rd : Reader} {ptr chain : E} {cs : List E} {n w : ℕ}
    (hlen : cs.length = 4 * n) (hw : 32 * w ≤ n) :
    ClScratchC CompModel.deployed rd ptr chain cs w ↔ ClScratch rd ptr chain cs w := by
  have e : ∀ q ≤ w, CompModel.deployed.st (prefixAt (cs.flatMap cellBytes) (32 * q)) =
      digestScalars (prefixDigest cs (32 * q)) := fun q hq => by
    show digestScalars (absorbBlocks paramIv 0 _) = _
    rw [prefixAt_cells hlen (by omega)]
    rfl
  constructor
  · intro h q hq
    rw [← e q hq]; exact h q hq
  · intro h q hq
    rw [e q hq]; exact h q hq

theorem claim_list_digest_of_comp {rd : Reader} (hm : MemOk rd) {gsq : E} (hT : SquaresAt rd gsq)
    (p n_g : E) (rets : List E) (h : Meaning_claim_list_digest rd [p, n_g, gsq] rets) :
    coreProgram.Rel rd "claim_list_digest" [p, n_g, gsq] rets := by
  rw [← relB_deployed]
  obtain ⟨p', n_g', gsq', d0, d1, ha, hr, n, hn, hng, cs, hlen, hcells, hcan, hd, hscr⟩ := h
  refine claim_list_digest_comp (CM := CompModel.deployed) hm hT p n_g rets
    ⟨p', n_g', gsq', d0, d1, ha, hr, n, hn, hng, cs, hlen, hcells, hcan, _, rfl, hd, ?_⟩
  rcases hscr with h0 | ⟨chain, hc⟩
  · exact Or.inl h0
  · rcases Nat.eq_zero_or_pos n with h0 | hn1
    · exact Or.inl h0
    · exact Or.inr ⟨chain, (clScratchC_deployed hlen (by omega)).mpr hc⟩

end
end LeanVM.Guest.B1.Digest
