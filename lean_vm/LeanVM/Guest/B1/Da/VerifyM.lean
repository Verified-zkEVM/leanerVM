/-
  LeanVM.Guest.B1.Da.VerifyM

  `da_verify` under a hash model: a LeanDA witness opens the returned root and vector digest with
  every hash answered by the model and the guest's padding digests (`Da.Witness.OpensWith`).
-/

module

public import LeanVM.Guest.B1.Da.Verify
public import LeanVM.Guest.B1.Da.ColumnM
public import LeanVM.Guest.B1.Da.OpensSome

/-!
# `da_verify` over a hash model

The deployed proof (`Verify.lean`, from `DaFacts`) computes every digest with BLAKE2s. Over a
`HashModel`:

* the hash-free helpers (`da_row_shape`, `__loop88`, `__loop89`, `__loop92`, `__loop94`) carry
  over by transfer (`freeOn_dv`); the row hashes (`__loop93`, `L93StepM`), the columns
  (`Meaning_da_verify_columnWith`) and the trees (`Meaning_da_levelsWith`) are the model's, and
  the last compression is a row of `M.sem`: `da_verify_factsM` gives `DaFactsM`;
* the vector hash is one run of `12288` rows from the IV through the `128` columns' parts
  (`vector_chainM`), whose last block reads the answered vector digest;
* the commitment is the answered hash of the row tree's root and the column tree's, both
  answered trees over the answered cell and row digests and the guest's padding digests
  (`commitCodewordsWith_eqM`);

so `da_verify_model` concludes `w.OpensWith M.H (toBytes padCellD) (toBytes padRowD) root vd`:
the padding digests are the guest's baked constants (`padCellD`, `padRowD`, `Pad.lean`), which at
BLAKE2s are LeanDA's (`paddingCell_eq`, `paddingRow_eq`), so that at the deployed model it is
`Witness.Opens` (`da_verify_model_deployed`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Node

@[expose] public section

/-! ## The hash-free helpers, by transfer -/

/-- `da_verify`'s hash-free helpers are free of `BLAKE2S` and call only among themselves. -/
theorem freeOn_dv :
    coreProgram.FreeOn ["da_row_shape", "__loop88", "__loop89", "__loop92", "__loop94"] = true := by
  decide +kernel

/-- `da_verify`'s hash-free helpers have their deployed relation under any semantics. -/
theorem relB_dv {S : BlakeSem} {rd : Reader} {f : String}
    (hf : f ∈ ["da_row_shape", "__loop88", "__loop89", "__loop92", "__loop94"]) {args rets : List E}
    (h : coreProgram.RelB S rd f args rets) : coreProgram.Rel rd f args rets :=
  (relB_iff_rel_of_freeOn freeOn_dv hf args rets).mp h

/-! ## `__loop93`: the row digests -/

/-- Row `x`'s digest under a model: the 128 cells at `prefix_bases[x]`, the answered hash of
their bytes stored at `rowtree·x²`. -/
def L93StepM (M : HashModel) (rd : Reader) (pb rt x : E) : Prop :=
  ∃ P cs, LoadHolds rd (pb * x) 0 P ∧ cs.length = 128 ∧ CellsAt rd P cs ∧
    (∀ c ∈ cs, IsCanonical128 c) ∧ ∃ c0 c1, CellsAt rd (rt * (x * x)) [c0, c1] ∧
      Ans M (cs.flatMap cellBytes) (c0, c1)

/-- Block `b ≥ 1` of a row digest's chain under `S`. -/
theorem rhBlkB_iff {S : BlakeSem} {rd : Reader} {σ : Val} {b : ℕ} :
    (∀ a ∈ rhBlk b, a.HoldsB S rd σ) ↔
      LoadHolds rd (σ (.n 5)) (4 * b) (σ (.n (7 * b + 8 + 0))) ∧
      LoadHolds rd (σ (.n 5)) (4 * b + 1) (σ (.n (7 * b + 8 + 1))) ∧
      LoadHolds rd (σ (.n 5)) (4 * b + 2) (σ (.n (7 * b + 8 + 2))) ∧
      LoadHolds rd (σ (.n 5)) (4 * b + 3) (σ (.n (7 * b + 8 + 3))) ∧
      σ (.n (7 * b + 12)) = word (64 * (b + 1)) (if b + 1 = 32 then 4294967295 else 0) 0 ∧
      S.check ![σ (.n (7 * b + 8 + 0)), σ (.n (7 * b + 8 + 1)), σ (.n (7 * b + 8 + 2)),
        σ (.n (7 * b + 8 + 3))] (σ (.n (7 * b + 6))) (σ (.n (7 * b + 6 + 1)))
        (σ (.n (7 * (b + 1) + 6))) (σ (.n (7 * (b + 1) + 6 + 1))) (σ (.n (7 * b + 12))) := by
  simp only [rhBlk, List.forall_mem_cons, Atom.HoldsB, forall_mem_nil_iff, and_true]

/-- `__loop93`'s atoms under a model: its row's digest, its test and next row. -/
theorem rh_fwdM {M : HashModel} {rd : Reader} {σ : Val} (hA : ∀ a ∈ rhAtoms, a.HoldsB M.sem rd σ) :
    L93StepM M rd (σ (.n 2)) (σ (.n 3)) (σ (.n 0)) ∧ σ (.n 236) = σ (.n 0) * gen + σ (.n 1) ∧
      σ (.n 238) = σ (.n 0) * gen := by
  simp only [rhAtoms, List.forall_mem_append, forall_mem_flatMap_range, List.forall_mem_cons,
    Atom.HoldsB, forall_mem_nil_iff, and_true] at hA
  obtain ⟨⟨⟨m4, l5, l6, l7, l8, l9, c10, c11, c12, b0⟩, hblk⟩, m232, m233, l230, l231, c234, m235,
    a236, c237, m238⟩ := hA
  set P := σ (.n 5)
  -- every block, uniformly
  have hB : ∀ b < 32, (∀ r < 4, LoadHolds rd P (4 * b + r) (σ (.n (rhLd b r)))) ∧
      σ (.n (7 * b + 12)) = rhMd b ∧
      M.sem.check ![σ (.n (rhLd b 0)), σ (.n (rhLd b 1)), σ (.n (rhLd b 2)), σ (.n (rhLd b 3))]
        (σ (.n (rhSt b))) (σ (.n (rhSt b + 1))) (σ (.n (rhSt (b + 1))))
        (σ (.n (rhSt (b + 1) + 1))) (σ (.n (7 * b + 12))) := by
    intro b hb
    rcases Nat.eq_zero_or_pos b with rfl | hpos
    · refine ⟨fun r hr => ?_, by rw [c12]; rfl, b0⟩
      interval_cases r
      exacts [l6, l7, l8, l9]
    · obtain ⟨i, rfl⟩ : ∃ i, b = i + 1 := ⟨b - 1, by omega⟩
      obtain ⟨a0, a1, a2, a3, am, ac⟩ := rhBlkB_iff.mp (hblk i (by omega))
      have e : ∀ r, rhLd (i + 1) r = 7 * (i + 1) + 8 + r := fun r => by
        unfold rhLd; rw [ite_neg' (by omega)]
      have s1 : rhSt (i + 1) = 7 * (i + 1) + 6 := by unfold rhSt; rw [ite_neg' (by omega)]
      have s2 : rhSt (i + 1 + 1) = 7 * (i + 1 + 1) + 6 := by unfold rhSt; rw [ite_neg' (by omega)]
      refine ⟨fun r hr => ?_, by rw [am, rhMd_word], ?_⟩
      · rw [e]
        interval_cases r
        exacts [a0, a1, a2, a3]
      · rw [e, e, e, e, s1, s2]
        exact ac
  let cs : List E := (List.range 128).map (cellAt rd P)
  have hcs : ∀ k < 128, cs.getD k 0 = cellAt rd P k ∧ LoadHolds rd P k (cellAt rd P k) := by
    intro k hk
    refine ⟨by simp [cs, List.getD_eq_getElem?_getD, hk], ?_⟩
    obtain ⟨b, r, hr, rfl⟩ : ∃ b r, r < 4 ∧ k = 4 * b + r := ⟨k / 4, k % 4, by omega, by omega⟩
    exact load_cellAt ((hB b (by omega)).1 r hr)
  have hblkv : ∀ b < 32, ![σ (.n (rhLd b 0)), σ (.n (rhLd b 1)), σ (.n (rhLd b 2)),
      σ (.n (rhLd b 3))] = blocksOf cs b := by
    intro b hb
    have e : ∀ r < 4, σ (.n (rhLd b r)) = cs.getD (4 * b + r) 0 := fun r hr => by
      rw [(hcs _ (by omega)).1, cellAt_of_load ((hB b hb).1 r hr)]
    simp only [blocksOf]
    rw [e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega), Nat.add_zero]
  obtain ⟨d, hd, hch⟩ := HashModel.chain_blocks (M := M) (n := 31) (blocks := blocksOf cs)
    (st := fun b => (σ (.n (rhSt b)), σ (.n (rhSt b + 1)))) (md := fun b => σ (.n (7 * b + 12)))
    (by show (σ (.n 10), σ (.n 11)) = _; rw [c10, c11, iv0_word, iv1_word]; rfl)
    (fun j hj => by
      rw [(hB j (by omega)).2.1]; unfold rhMd; congr 1
      simp only [decide_eq_false_iff_not]; omega)
    (by rw [(hB 31 (by omega)).2.1]; rfl)
    (fun j hj => by rw [← hblkv j (by omega)]; exact (hB j (by omega)).2.2)
  rw [blocksOf_bytes cs 32 (by simp [cs])] at hd
  have hst : rhSt (31 + 1) = 230 := rfl
  simp only [hst] at hch
  refine ⟨⟨P, cs, by rw [m4] at l5; exact l5, by simp [cs], fun k hk => ?_, fun c hc => ?_,
    σ (.n 230), σ (.n 231), ?_, d, hd, hch⟩,
    by rw [a236, m235, c234, word_gen], by rw [m238, c237, word_gen]⟩
  · have hk' : k < 128 := by simpa [cs] using hk
    have := (hcs k hk').2
    rwa [← (hcs k hk').1, List.getD_eq_getElem _ _ hk] at this
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
    have hk' : k < 128 := by simpa [cs] using hk
    obtain ⟨b, r, hr, e⟩ : ∃ b r, r < 4 ∧ k = 4 * b + r := ⟨k / 4, k % 4, by omega, by omega⟩
    have hc' := (M.canonical (hB b (by omega)).2.2).1
    rw [hblkv b (by omega)] at hc'
    have := hc' ⟨r, hr⟩
    have hg : IsCanonical128 (cs.getD (4 * b + r) 0) := by
      interval_cases r <;> simpa [blocksOf] using this
    rw [← e, List.getD_eq_getElem _ _ hk] at hg
    exact hg
  · rw [m233, m232] at l230 l231
    exact cellsAt_two.mpr ⟨l230, l231⟩

/-- One frame of `__loop93` under a model. -/
theorem l93_stepB {M : HashModel} (rd : Reader) (W pb rt : E) (C : CallRel) (x : E)
    (h : ∃ fn, coreProgram.find? "__loop93" = some fn ∧
      fn.SemB M.sem C rd (x :: [W, pb, rt]) []) :
    L93StepM M rd pb rt x ∧ IsInK (x * gen + W) ∧
      (x * gen + W ≠ 0 → C "__loop93" (x * gen :: [W, pb, rt]) []) := by
  obtain ⟨fn, hfn, h⟩ := h
  rw [find_l93, Option.some.injEq] at hfn
  subst hfn
  simp only [Fn.SemB, rhBody, holdsListB_atoms, Stmt.HoldsListB, Stmt.HoldsB, List.map_cons,
    List.map_nil] at h
  obtain ⟨σ, hp, hA, hk, hnext, -⟩ := h
  simp only [List.cons.injEq, and_true] at hp
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hp
  obtain ⟨hS, e236, e238⟩ := rh_fwdM hA
  rw [e236] at hk hnext
  rw [e238] at hnext
  exact ⟨hS, hk, hnext⟩

/-! ## `__loop90`, `__loop91`: the columns -/

theorem colLoop_stepB {S : BlakeSem} (store : Bool) (rd : Reader) (ps : List E)
    (hps : ps.length = 9) (C : CallRel) (x : E)
    (h : ∃ fn, coreProgram.find? (colLoopName store) = some fn ∧ fn.SemB S C rd (x :: ps) []) :
    C (colName store) (x :: ps) [] ∧ IsInK (x * gen + colLoopEnd store) ∧
      (x * gen + colLoopEnd store ≠ 0 → C (colLoopName store) (x * gen :: ps) []) := by
  match ps, hps with
  | [nb, np, gap, glp, pb, ct, rb, hs, ctr], _ =>
  simp only [find_colLoop, Option.some.injEq, exists_eq_left', Fn.SemB, colLoopBody,
    Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, word_gen] at h
  obtain ⟨σ, hp, hcall, c10, m11, c12, a13, c14, m15, hk, hnext, -⟩ := h
  simp only [List.cons.injEq, and_true] at hp
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hp
  rw [a13, m11, c10, c12] at hk hnext
  rw [m15, c14] at hnext
  exact ⟨hcall, hk, hnext⟩

/-- The prefix columns under a model. -/
theorem colLoop_prefixM {M : HashModel} {rd : Reader} {ps : List E} (hps : ps.length = 9)
    (h : coreProgram.RelB M.sem rd "__loop90" (1 :: ps) []) :
    ∀ b < 64, Meaning_da_verify_columnWith M true rd (gen ^ b :: ps) [] := by
  rw [← pow_zero gen] at h
  obtain ⟨m, hkm, hN, hfirst, hall⟩ :=
    loopB_fwd (B := fun C x => C (colName true) (x :: ps) []) (fun _ _ _ hC h => hC _ _ _ h)
      (colLoop_stepB true rd ps hps) 0 h
  rw [colLoopEnd_eq, ite_pos' rfl] at hN hfirst
  have := loop_end_exact (by norm_num) (by norm_num) hN hfirst
  subst this
  exact fun b hb => da_verify_column_model true rd _ _ (hall b (Nat.zero_le _) hb)

/-- The other columns under a model. -/
theorem colLoop_restM {M : HashModel} {rd : Reader} {ps : List E} (hps : ps.length = 9)
    (h : coreProgram.RelB M.sem rd "__loop91" (word 27 0 0 :: ps) []) :
    ∀ b, 64 ≤ b → b < 128 → Meaning_da_verify_columnWith M false rd (gen ^ b :: ps) [] := by
  rw [word_g64] at h
  obtain ⟨m, hkm, hN, hfirst, hall⟩ :=
    loopB_fwd (B := fun C x => C (colName false) (x :: ps) []) (fun _ _ _ hC h => hC _ _ _ h)
      (colLoop_stepB false rd ps hps) 64 h
  rw [colLoopEnd_eq, ite_neg' (by decide)] at hN hfirst
  have := loop_end_exact (by norm_num) (by norm_num) hN hfirst
  subst this
  exact fun b hb hb' => da_verify_column_model false rd _ _ (hall b hb hb')

/-! ## What the body says -/

/-- **`DaFacts` but the columns', under a model** (`DaRest`): the row digests' and the trees'
facts over the model, and the last row of `M.sem`. -/
def DaRestM (M : HashModel) (rd : Reader) (r : ℕ) (pb pd hs ctr acc rb ct rt rc0 rc1 rr0 rr1 r0 r1 v0 v1 : E) :
    Prop :=
  1 ≤ r ∧ r ≤ LeanDa.maxRows ∧
    (∀ i < r, L88Step rd pb pd (gen ^ i)) ∧
    LoadHolds rd hs 0 (digestScalars paramIv).1 ∧ LoadHolds rd hs 1 (digestScalars paramIv).2 ∧
    IsInK ctr ∧
    (∀ k < 385, ∀ w, rd (ctr.limb 0 * Parameters.gpow k) = some w → w = word (k * 2048) 0 0) ∧
    (∀ i < r, L89Step rd acc rb (gen ^ i)) ∧
    (∀ i < r, L92Step rd rb (gen ^ i)) ∧
    Meaning_da_levelsWith M 7 rd [ct] [rc0, rc1] ∧
    (∀ i < r, L93StepM M rd pb rt (gen ^ i)) ∧
    (∀ d < LeanDa.nPad r - r, L94Step rd rt (gen ^ r) (gen ^ d)) ∧
    Meaning_da_levelsWith M (LeanDa.logPad r) rd [rt] [rr0, rr1] ∧
    M.sem.check ![rr0, rr1, rc0, rc1] (digestScalars paramIv).1 (digestScalars paramIv).2 r0 r1
      (metadataCell 64 true) ∧
    LoadHolds rd hs 256 v0 ∧ LoadHolds rd hs 257 v1

/-- **What `da_verify`'s relation says of memory, under a model** (`DaFacts`): `DaRestM` and the
columns' facts over the model. -/
def DaFactsM (M : HashModel) (rd : Reader) (r0 r1 v0 v1 : E) : Prop :=
  ∃ (r : ℕ) (pb pd hs ctr acc rb ct rt rc0 rc1 rr0 rr1 : E),
    DaRestM M rd r pb pd hs ctr acc rb ct rt rc0 rc1 rr0 rr1 r0 r1 v0 v1 ∧
    ∀ b < 128, Meaning_da_verify_columnWith M (decide (b < 64)) rd
      [gen ^ b, gen ^ r, gen ^ LeanDa.nPad r, gen ^ (LeanDa.nPad r - r), gen ^ LeanDa.logPad r,
        pb, ct, rb, hs, ctr] []

/-- A block of atoms under `S`, then `next`. -/
theorem holdsListB_atoms' {S : BlakeSem} {C : CallRel} {rd : Reader} {σ : Val} (as : List Atom)
    (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsListB S C rd σ (as.map .atom) next kret ↔ (∀ a ∈ as, a.HoldsB S rd σ) ∧ next := by
  have := holdsListB_atoms (S := S) (C := C) (rd := rd) (σ := σ) as [] next kret
  rw [List.append_nil] at this
  rw [this]; rfl

/-- **`da_verify`'s body, on a valuation, under a model** (`da_verify_rest`), under any call
relation below the program's: the row count `r`, the facts other than the columns' at the
valuation's pointers, and the two column loops' calls. -/
theorem da_verify_restM {M : HashModel} {C : CallRel} {rd : Reader}
    (hC : CallRel.Le C (coreProgram.RelB M.sem rd)) (hm : MemOk rd) {gsq : E}
    (hT : SquaresAt rd gsq) {σ : Val} {r0 r1 v0 v1 : E} (hp : ([.n 0] : List V).map σ = [gsq])
    (hb : Stmt.HoldsListB M.sem C rd σ dvBody False (fun rs => rs = [r0, r1, v0, v1])) :
    ∃ r, σ (.n 420) = 1 ∧ σ (.n 421) = gen ^ 64 ∧ σ (.n 1) = gen ^ r ∧
      σ (.n 3) = gen ^ LeanDa.nPad r ∧ σ (.n 4) = gen ^ (LeanDa.nPad r - r) ∧
      σ (.n 2) = gen ^ LeanDa.logPad r ∧
      DaRestM M rd r (σ (.n 13)) (σ (.n 12)) (σ (.n 17)) (σ (.n 405)) (σ (.n 414)) (σ (.n 415))
        (σ (.n 419)) (σ (.n 429)) (σ (.n 425)) (σ (.n 426)) (σ (.n 436)) (σ (.n 437)) r0 r1 v0 v1 ∧
      C "__loop90" (dvColArgs σ (.n 420)) [] ∧ C "__loop91" (dvColArgs σ (.n 421)) [] := by
  rw [dvBody, holdsListB_append, holdsListB_append, holdsListB_atoms'] at hb
  simp only [dvA, dvB, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil,
    true_and, word_one, word_g64] at hb hp
  obtain ⟨hshape, m5, m6, m7, m8, m9, m10, m11, c14, a15, c16, hk15, h88, c18, l18, c19, l19, hK,
    ⟨hk405, hfr⟩, m406, m407, m408, m409, m410, m411, m412, m413, c416, a417, c418, hk417, h89,
    c420, h90, c421, h91, c422, a423, c424, hk423, h92, hlv7, m427, m428, c430, a431, c432, hk431,
    h93, c433, a434, c435, hk434, h94, hdl, c438, c439, c440, hfin, c443, c444, l445, l446,
    hret⟩ := hb
  simp only [List.cons.injEq, and_true] at hp hret
  subst hp
  obtain ⟨_, _, _, np, gap, he, hr, r, hr1, hr2, hnb, hglp, hnp, hgap⟩ :=
    (da_row_shape_iff hm hT _ _ _).mp (relB_dv (f := "da_row_shape") (by simp) (hC _ _ _ hshape))
  simp only [List.cons.injEq, and_true] at he hr
  obtain ⟨e1, e2, -⟩ := he
  obtain ⟨e3, e4⟩ := hr
  rw [← e1] at hnb
  rw [← e2] at hglp
  rw [← e3] at hnp
  rw [← e4] at hgap
  have hr33 : r < 2 ^ 33 := by unfold LeanDa.maxRows at hr2; omega
  have hlp := logPad_le hr2
  have hN := nPad_le hr2
  -- the counter words
  have hK' : ∀ k < 385, σ (.n (20 + k)) = word (k * 2048) 0 0 := by
    intro k hk
    exact hK _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hret
  have h88' := relB_dv (f := "__loop88") (by simp)
    (hC _ _ _ (callIf_loop hr1 hr33 (by rwa [a15, c14, hnb] at h88)))
  have h89' := relB_dv (f := "__loop89") (by simp)
    (hC _ _ _ (callIf_loop hr1 hr33 (by rwa [a417, c416, hnb] at h89)))
  have h92' := relB_dv (f := "__loop92") (by simp)
    (hC _ _ _ (callIf_loop hr1 hr33 (by rwa [a423, c422, hnb] at h92)))
  have h93' := hC _ _ _ (callIf_loop hr1 hr33 (by rwa [a431, c430, hnb] at h93))
  rw [c16, ← pow_zero gen] at h88'
  rw [c418, ← pow_zero gen] at h89'
  rw [c424, ← pow_zero gen] at h92'
  rw [c432, ← pow_zero gen] at h93'
  obtain ⟨k, hk, hk2, hlvk⟩ := dl_dispatchM (let ⟨j, hj, hx, hc⟩ := hdl; ⟨j, hj, hx, hC _ _ _ hc⟩)
  rw [hglp] at hk2
  have hkl : k = LeanDa.logPad r := gen_pow_inj' (by omega) (by omega) hk2.symm
  subst hkl
  rw [c438, c439, c440, iv0_word, iv1_word, md64_word] at hfin
  -- the row digests
  obtain ⟨m93, -, hN93, hfirst93, hall93⟩ :=
    loopB_fwd (B := fun _ x => L93StepM M rd (σ (.n 13)) (σ (.n 429)) x) (fun _ _ _ _ h => h)
      (l93_stepB rd _ _ _) 0 h93'
  have h93all : ∀ i < r, L93StepM M rd (σ (.n 13)) (σ (.n 429)) (gen ^ i) := by
    have := loop_end_exact hr33 (by omega) hN93 hfirst93
    subst this
    exact fun i hi => hall93 i (Nat.zero_le _) hi
  refine ⟨r, c420, c421, hnb, hnp, hgap, hglp, ⟨hr1, hr2,
    loop_all (B := fun j => L88Step rd (σ (.n 13)) (σ (.n 12)) (gen ^ j)) hr33 rfl
      ((l88_iff rd _ _ _ 0).mp h88'),
    by rw [← iv0_word, ← c18]; exact l18, by rw [← iv1_word, ← c19]; exact l19, hk405,
    fun k hk w hw => ?_,
    loop_all (B := fun j => L89Step rd (σ (.n 414)) (σ (.n 415)) (gen ^ j)) hr33 rfl
      ((l89_iff rd _ _ _ 0).mp h89'),
    loop_all (B := fun j => L92Step rd (σ (.n 415)) (gen ^ j)) hr33 rfl
      ((l92_iff rd _ _ 0).mp h92'),
    da_levels_model 7 (by norm_num) _ _ (hC _ _ _ hlv7), h93all, fun d hd => ?_, hlvk,
    by rw [c443, c444]; exact hfin, l445, l446⟩, h90, h91⟩
  · have := hfr k (by simpa using hk) w hw
    simp only [List.getElem_map, List.getElem_range] at this
    rw [this, hK' k hk]
  · have hpos : 0 < LeanDa.nPad r - r := by omega
    have h94' := relB_dv (f := "__loop94") (by simp)
      (hC _ _ _ (callIf_loop hpos (by omega) (by rwa [a434, c433, hgap] at h94)))
    rw [c435, hnb, ← pow_zero gen] at h94'
    exact loop_all (B := fun j => L94Step rd (σ (.n 429)) (gen ^ r) (gen ^ j)) (by omega) rfl
      ((l94_iff rd _ _ _ 0).mp h94') d hd

/-- **`da_verify`'s relation under a model gives its facts.** -/
theorem da_verify_factsM {M : HashModel} {rd : Reader} (hm : MemOk rd) {gsq : E}
    (hT : SquaresAt rd gsq) {r0 r1 v0 v1 : E}
    (h : coreProgram.RelB M.sem rd "da_verify" [gsq] [r0, r1, v0, v1]) :
    DaFactsM M rd r0 r1 v0 v1 := by
  rw [relB_of_find find_dv] at h
  obtain ⟨σ, hp, hb⟩ := h
  obtain ⟨r, c420, c421, hnb, hnp, hgap, hglp, hrest, h90, h91⟩ :=
    da_verify_restM (fun _ _ _ h => h) hm hT hp hb
  unfold dvColArgs at h90 h91
  rw [c420, hnb, hglp, hnp, hgap] at h90
  rw [c421, hnb, hglp, hnp, hgap, ← word_g64] at h91
  refine ⟨r, _, _, _, _, _, _, _, _, _, _, _, _, hrest, fun b hb => ?_⟩
  by_cases h64 : b < 64
  · rw [decide_eq_true h64]
    exact colLoop_prefixM rfl h90 b h64
  · rw [decide_eq_false h64]
    exact colLoop_restM rfl h91 b (by omega) hb

/-! ## Columns and cells -/

/-- Column `b`'s facts under a model, under the honest counter words (`ColOk`). -/
def ColOkM (M : HashModel) (rd : Reader) (r : ℕ) (pb ct rb hs : E) (b : ℕ) (c : ColW) : Prop :=
  c.ws.length = 256 ∧ CellsAt rd (hs * gen ^ (2 * b)) [c.h0, c.h1] ∧
    CellsAt rd (hs * gen ^ (2 * b + 2)) [c.o0, c.o1] ∧
    ChainSteps M.sem (c.h0, c.h1) (vxBlocks (c.ws.getD · 0)) (vxMd (decide (b = 127)) (cvOf b)) 96
      (c.o0, c.o1) ∧
    FrameRun rd c.lv c.ws ∧
    (∀ i < r, RowCellM M (decide (b < 64)) rd c.lv rb (gen ^ b) c.node pb (gen ^ i)) ∧
    (∀ d < LeanDa.nPad r - r, GapStep rd c.node (gen ^ r) (gen ^ d)) ∧
    Meaning_da_levelsWith M (LeanDa.logPad r) rd [c.node] [c.c0, c.c1] ∧
    CellsAt rd (ct * gen ^ (2 * b)) [c.c0, c.c1]

/-- A column's facts under a model, from its meaning (`col_facts`). -/
theorem col_factsM {M : HashModel} {rd : Reader} {r : ℕ} (hr1 : 1 ≤ r) (hr2 : r ≤ LeanDa.maxRows)
    {pb ct rb hs ctr : E}
    (hctr : ∀ k < 385, ∀ w, rd (ctr.limb 0 * Parameters.gpow k) = some w → w = word (k * 2048) 0 0)
    {b : ℕ} (hb : b < 128)
    (h : Meaning_da_verify_columnWith M (decide (b < 64)) rd [gen ^ b, gen ^ r, gen ^ LeanDa.nPad r,
      gen ^ (LeanDa.nPad r - r), gen ^ LeanDa.logPad r, pb, ct, rb, hs, ctr] []) :
    ∃ c : ColW, ColOkM M rd r pb ct rb hs b c := by
  have hr33 : r < 2 ^ 33 := by unfold LeanDa.maxRows at hr2; omega
  have hlp := logPad_le hr2
  have hN := nPad_le hr2
  obtain ⟨xb, nb, np, gap, glp, pb', ct', rb', hs', ctr', ha, -, h0, h1, o0, o1, lv, node, c0, c1,
    hh, hdisp, ho, -, hrow, -, hgap, ⟨k, hk, hglp, hlv⟩, hc⟩ := h
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := ha
  obtain ⟨xb, rest, hxa, -, hvc⟩ := hdisp
  simp only [List.cons.injEq] at hxa
  obtain ⟨rfl, rfl⟩ := hxa
  obtain ⟨_, _, _, _, _, _, wp, ha, hr, ws, cv, hwl, hcl, hcv, hch, hfr⟩ := hvc
  simp only [List.cons.injEq, and_true] at ha hr
  obtain ⟨rfl, rfl, rfl, rfl⟩ := ha
  obtain ⟨rfl, rfl, rfl⟩ := hr
  have hkl : k = LeanDa.logPad r := gen_pow_inj' (by omega) (by omega) hglp.symm
  subst hkl
  have hfinal : decide (gen ^ b = gen ^ 127) = decide (b = 127) := by
    by_cases h127 : b = 127
    · rw [decide_eq_true h127, decide_eq_true (by rw [h127])]
    · rw [decide_eq_false h127, decide_eq_false fun he => h127 (gen_pow_inj' (by omega) (by omega) he)]
  have hcv' : ∀ k < 4, cv.getD k 0 = cvOf b k := by
    intro k hk
    have hl := hcv k (by omega)
    rw [show gen ^ b * gen ^ b * gen ^ b = gen ^ (3 * b) by rw [← pow_add, ← pow_add]; congr 1; ring,
      loadHolds_mul_gen_pow] at hl
    rw [List.getD_eq_getElem _ _ (by omega), hctr (3 * b + k) (by omega) _ hl.2, cvOf, Nat.add_mul]
  rw [hfinal, chainSteps_congr (b' := vxBlocks (ws.getD · 0))
    (md' := vxMd (decide (b = 127)) (cvOf b)) (fun _ _ => rfl) (fun j hj => vxMd_congr hcv' hj)]
    at hch
  refine ⟨⟨h0, h1, o0, o1, lv, node, c0, c1, ws⟩, hwl, ?_, ?_, hch, hfr,
    loopTo_all hr33 (hrow (gen_pow_ne_one' hr1 hr33)), fun d hd => ?_, hlv, ?_⟩
  · have e : gen ^ b * gen ^ b = gen ^ (2 * b) := by rw [← pow_add, two_mul]
    rw [e] at hh; exact hh
  · have e : gen ^ b * gen * (gen ^ b * gen) = gen ^ (2 * b + 2) := by
      rw [← pow_succ, ← pow_add]; congr 1; ring
    rw [e] at ho; exact ho
  · exact loopTo_all (by omega) (hgap (gen_pow_ne_one' (by omega) (by omega))) d hd
  · have e : gen ^ b * gen ^ b = gen ^ (2 * b) := by rw [← pow_add, two_mul]
    rw [e] at hc; exact hc

/-- A row's cell in a column under a model (`CellOk`): its digest the answered hash of its
symbols. -/
def CellOkM (M : HashModel) (rd : Reader) (store : Bool) (lv rb xb node pb x : E) (c : CellW) :
    Prop :=
  c.syms.length = 256 ∧ c.wsc.length = 256 ∧ CellsAt rd lv c.wsc ∧
    Ans M (c.syms.flatMap kBytes) (c.d0, c.d1) ∧
    c.s = ∑ k ∈ Finset.range 256, c.wsc.getD k 0 * ofK (c.syms.getD k 0) ∧
    LoadHolds rd (rb * x) 0 c.R ∧ LoadHolds rd (c.R * xb) 0 c.a ∧
    LoadHolds rd (c.R * xb) 1 (c.a + c.s) ∧
    CellsAt rd (node * (x * x)) [c.d0, c.d1] ∧
    (store = true → ∃ P, LoadHolds rd (pb * x) 0 P ∧ CellsAt rd (P * (xb * xb)) [c.d0, c.d1])

/-- A row's cell's facts under a model, from its meaning (`cell_facts`). -/
theorem cell_factsM {M : HashModel} {rd : Reader} {store : Bool} {lv rb xb node pb x : E}
    (h : RowCellM M store rd lv rb xb node pb x) :
    ∃ c : CellW, CellOkM M rd store lv rb xb node pb x c := by
  obtain ⟨d0, d1, s, R, a, hm, hR, ha, has, hn, hst⟩ := h
  obtain ⟨_, _, _, _, hargs, hrets, syms, wsc, hsl, hwl, hws, hd, hs⟩ := hm
  simp only [List.cons.injEq, and_true] at hargs hrets
  obtain ⟨rfl⟩ := hargs
  obtain ⟨rfl, rfl, rfl⟩ := hrets
  exact ⟨⟨_, _, _, R, a, syms, wsc⟩, hsl, hwl, hws, hd, hs, hR, ha, has, hn, hst⟩

/-! ## The vector hash -/

/-- **The vector digest under a model**: the `128` columns' rows, from the IV at `hashes`, are one
run whose last block reads the answered hash of the weights' bytes, which `hashes·g^256` holds. -/
theorem vector_chainM {M : HashModel} {rd : Reader} {r : ℕ} {pb ct rb hs v0 v1 : E}
    {F : ℕ → ColW} (hok : ∀ b < 128, ColOkM M rd r pb ct rb hs b (F b))
    (hiv0 : LoadHolds rd hs 0 (digestScalars paramIv).1)
    (hiv1 : LoadHolds rd hs 1 (digestScalars paramIv).2)
    (hv0 : LoadHolds rd hs 256 v0) (hv1 : LoadHolds rd hs 257 v1) :
    Ans M (((List.range 128).flatMap fun b => (F b).ws).flatMap eBytes) (v0, v1) := by
  let all : ℕ → Fin 4 → E := fun i => vxBlocks ((F (i / 96)).ws.getD · 0) (i % 96)
  let mdA : ℕ → E := fun i => metadataCell (64 * (i + 1)) (decide (i + 1 = 12288))
  have hcell : ∀ {p : E} {k : ℕ} {a b a' b' : E}, CellsAt rd (p * gen ^ k) [a, b] →
      CellsAt rd (p * gen ^ k) [a', b'] → (a, b) = (a', b') := fun h h' => by
    obtain ⟨x0, x1⟩ := cellsAt_two.mp h
    obtain ⟨y0, y1⟩ := cellsAt_two.mp h'
    rw [loadHolds_unique x0 y0, loadHolds_unique x1 y1]
  have hcol : ∀ b < 128, ChainSteps M.sem ((F b).h0, (F b).h1) (fun i => all (96 * b + i))
      (fun i => mdA (96 * b + i)) 96 ((F b).o0, (F b).o1) := by
    intro b hb
    obtain ⟨-, -, -, hch, -⟩ := hok b hb
    have hb1 : ∀ i < 96, vxBlocks ((F b).ws.getD · 0) i = all (96 * b + i) := fun i hi => by
      show vxBlocks _ i = vxBlocks ((F ((96 * b + i) / 96)).ws.getD · 0) ((96 * b + i) % 96)
      rw [show (96 * b + i) / 96 = b by omega, show (96 * b + i) % 96 = i by omega]
    have hm1 : ∀ i < 96, vxMd (decide (b = 127)) (cvOf b) i = mdA (96 * b + i) := fun i hi => by
      rw [vxMd_counters hb hi]
      show _ = metadataCell (64 * (96 * b + i + 1)) (decide (96 * b + i + 1 = 12288))
      rw [decide_eq_decide.mpr (show (b = 127 ∧ i = 95) ↔ 96 * b + i + 1 = 12288 by omega)]
    exact (chainSteps_congr hb1 hm1).mp hch
  have hS : ∀ b < 128, ChainSteps M.sem ivCells all mdA (96 * b) ((F b).h0, (F b).h1) := by
    intro b hb
    induction b with
    | zero =>
      obtain ⟨-, hh, -⟩ := hok 0 hb
      rw [Nat.mul_zero, pow_zero, mul_one] at hh
      obtain ⟨x0, x1⟩ := cellsAt_two.mp hh
      refine ⟨fun _ => ivCells, rfl, ?_, fun j hj => absurd hj (by omega)⟩
      rw [loadHolds_unique x0 hiv0, loadHolds_unique x1 hiv1]
      rfl
    | succ b ih =>
      obtain ⟨-, -, ho, -⟩ := hok b (by omega)
      obtain ⟨-, hh, -⟩ := hok (b + 1) hb
      rw [show 2 * b + 2 = 2 * (b + 1) by ring] at ho
      rw [hcell hh ho, show 96 * (b + 1) = 96 * b + 96 by ring]
      exact (ih (by omega)).append (hcol b (by omega))
  have hall := (hS 127 (by omega)).append (hcol 127 (by omega))
  obtain ⟨d, hd, hout⟩ := ChainSteps.blocks (n := 12287) hall
    (fun j hj => by simp only [mdA]; congr 1; simp only [decide_eq_false_iff_not]; omega) rfl
  have hbytes : (List.range (12287 + 1)).flatMap (fun j => blockBytes (all j)) =
      ((List.range 128).flatMap fun b => (F b).ws).flatMap eBytes := by
    rw [show 12287 + 1 = 96 * 128 by rfl, flatMap_range_mul 96, List.flatMap_assoc]
    refine List.flatMap_congr fun b hb => ?_
    have hb' := List.mem_range.mp hb
    rw [← vx_bytes _ (hok b hb').1]
    refine List.flatMap_congr fun j hj => ?_
    have hj' := List.mem_range.mp hj
    show blockBytes (vxBlocks ((F ((96 * b + j) / 96)).ws.getD · 0) ((96 * b + j) % 96)) = _
    rw [show (96 * b + j) / 96 = b by omega, show (96 * b + j) % 96 = j by omega]
  rw [hbytes] at hd
  refine ⟨d, hd, ?_⟩
  obtain ⟨-, -, ho, -⟩ := hok 127 (by omega)
  obtain ⟨x0, x1⟩ := cellsAt_two.mp ho
  rw [loadHolds_mul_gen_pow] at x0 x1
  rw [loadHolds_unique hv0 x0, loadHolds_unique hv1 x1]
  exact hout

/-! ## The commitment -/

/-- Leaf `i` of column `b`'s tree: the cell's digest, then the zero cell's (the guest's baked
`padCellD`). -/
def colLeafM (r : ℕ) (cD : ℕ → ℕ → Digest) (b i : ℕ) : Digest := if i < r then cD b i else padCellD

/-- Leaf `i` of the row tree: the row's digest, then the zero row's (the guest's baked
`padRowD`). -/
def rowLeafM (r : ℕ) (rD : ℕ → Digest) (i : ℕ) : Digest := if i < r then rD i else padRowD

/-- A `mapM` over the images of indices, every step answered by index. -/
theorem mapM_option_map_range {α β : Type} (f : α → Option β) (rowL : ℕ → α) (g : ℕ → β) (n : ℕ)
    (h : ∀ i < n, f (rowL i) = some (g i)) :
    ∀ is : List ℕ, (∀ i ∈ is, i < n) → (is.map rowL).mapM f = some (is.map g)
  | [], _ => rfl
  | i :: is, hi => by
    rw [List.map_cons, List.mapM_cons, h i (hi i (by simp)),
      mapM_option_map_range f rowL g n h is fun j hj => hi j (by simp [hj])]
    rfl

/-- LeanDA's bytes of a vector are its entries' `eBytes`. -/
theorem vector_bytes (v : List E) :
    (v.flatMap fun e => [LeanDa.limb e 0, LeanDa.limb e 1, LeanDa.limb e 2]).flatMap LeanDa.kBytes =
      v.flatMap eBytes := by
  rw [List.flatMap_assoc]
  refine List.flatMap_congr fun e _ => ?_
  simp [leanDa_kBytes, eBytes, LeanDa.limb, E.limb]

/-- **LeanDA's commitment over the answered hash** of rows whose cells are `sym`, every cell's,
row's and tree node's hash answered, the padding digests the guest's. -/
theorem commitCodewordsWith_eqM {M : HashModel} {r : ℕ} (hr : 1 ≤ r) {rowL : ℕ → List K}
    {sym : ℕ → ℕ → List K} (hcell : ∀ i < r, ∀ b < 128, LeanDa.listCell (rowL i) b = sym b i)
    {cD : ℕ → ℕ → Digest}
    (hcD : ∀ b < 128, ∀ i < r, M.H ((sym b i).flatMap kBytes) = some (cD b i))
    {rD : ℕ → Digest}
    (hrD : ∀ i < r, M.H ((List.range 64).flatMap fun b => digestBytes (cD b i)) = some (rD i))
    (hRT : TreeAns M (rowLeafM r rD) (LeanDa.logPad r))
    (hCT : ∀ b < 128, TreeAns M (colLeafM r cD b) (LeanDa.logPad r))
    (hTop : TreeAns M (fun b => nodeM M (colLeafM r cD b) (LeanDa.logPad r) 0) 7) {root : Digest}
    (hroot : M.H (digestBytes (nodeM M (rowLeafM r rD) (LeanDa.logPad r) 0) ++
      digestBytes (nodeM M (fun b => nodeM M (colLeafM r cD b) (LeanDa.logPad r) 0) 7 0)) =
        some root) :
    Da.commitCodewordsWith (Da.daHash M.H) (Da.toBytes padCellD) (Da.toBytes padRowD)
      ((List.range r).map rowL) = some (Da.toBytes root) := by
  obtain ⟨hrN, -⟩ := (logPad_iff (lp := LeanDa.logPad r) hr).mp rfl
  have hNdef : LeanDa.nPad r = 2 ^ LeanDa.logPad r := rfl
  have hcd : ∀ i < r, ∀ j < 128, Da.listCellDigestWith (Da.daHash M.H) (rowL i) j =
      some (Da.toBytes (cD j i)) := by
    intro i hi j hj
    rw [Da.listCellDigestWith, hcell i hi j hj,
      show (sym j i).flatMap LeanDa.kBytes = (sym j i).flatMap kBytes from
        List.flatMap_congr fun a _ => leanDa_kBytes a, Da.daHash, hcD j hj i hi]
    rfl
  have hrd : ∀ i < r, Da.rowDigestWith (Da.daHash M.H) (rowL i) = some (Da.toBytes (rD i)) := by
    intro i hi
    have hm : (List.range LeanDa.payloadCells).mapM
        (fun j => Da.listCellDigestWith (Da.daHash M.H) (rowL i) j) =
        some ((List.range 64).map fun j => Da.toBytes (cD j i)) :=
      mapM_option_some_mem _ _ _ fun j hj =>
        hcd i hi j (lt_trans (List.mem_range.mp hj) (by decide : LeanDa.payloadCells < 128))
    rw [Da.rowDigestWith, hm]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [List.flatMap_map, Da.daHash]
    simp only [toBytes_toList]
    rw [hrD i hi]
    rfl
  have hl : ((List.range r).map rowL).length = r := by simp
  have hrows : ((List.range r).map rowL).mapM (Da.rowDigestWith (Da.daHash M.H)) =
      some ((List.range r).map fun i => Da.toBytes (rD i)) :=
    mapM_option_map_range _ rowL _ r hrd _ fun i hi => List.mem_range.mp hi
  have hrowList : (List.range r).map (fun i => Da.toBytes (rD i)) ++
      List.replicate (LeanDa.nPad ((List.range r).map rowL).length - ((List.range r).map rowL).length)
        (Da.toBytes padRowD) =
      (List.range (2 ^ LeanDa.logPad r)).map fun i => Da.toBytes (rowLeafM r rD i) := by
    rw [hl]
    apply List.ext_getElem (by simp; rw [← hNdef]; omega)
    intro i h1 h2
    simp only [List.length_map, List.length_range] at h2
    by_cases hir : i < r
    · rw [List.getElem_append_left (by simp; omega)]
      simp only [List.getElem_map, List.getElem_range, rowLeafM, hir, ↓reduceIte]
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.getElem_replicate, List.getElem_map, List.getElem_range, rowLeafM, hir,
        ↓reduceIte]
  have hcols : ((List.range LeanDa.cellsPerRow).flatMap fun j =>
      (List.range (LeanDa.nPad ((List.range r).map rowL).length)).map fun i => (i, j)).mapM
      (fun ij => if h : ij.1 < ((List.range r).map rowL).length then
        Da.listCellDigestWith (Da.daHash M.H) ((List.range r).map rowL)[ij.1] ij.2
        else pure (Da.toBytes padCellD)) =
      some ((List.range (2 ^ 7)).flatMap fun j =>
        (List.range (2 ^ LeanDa.logPad r)).map fun i => Da.toBytes (colLeafM r cD j i)) := by
    rw [mapM_option_some_mem _ (fun ij => Da.toBytes (colLeafM r cD ij.2 ij.1)) _ (fun ij hij => ?_)]
    · rw [List.map_flatMap, hl, show LeanDa.cellsPerRow = 2 ^ 7 from rfl, hNdef]
      congr 1
      refine List.flatMap_congr fun j _ => ?_
      rw [List.map_map]
      rfl
    · obtain ⟨j, hj, hij⟩ := List.mem_flatMap.mp hij
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hij
      have hj' : j < 128 := List.mem_range.mp hj
      by_cases hir : i < r
      · simp only [show i < ((List.range r).map rowL).length by rw [hl]; exact hir, ↓reduceDIte,
          List.getElem_map, List.getElem_range, colLeafM, hir, ↓reduceIte]
        exact hcd i hir j hj'
      · simp only [show ¬i < ((List.range r).map rowL).length by rw [hl]; exact hir, ↓reduceDIte,
          colLeafM, hir, ↓reduceIte]
        rfl
  simp only [Da.commitCodewordsWith]
  rw [hrows]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [hrowList, treeRootWith_nodeM hRT]
  simp only [Option.bind_some]
  rw [hcols]
  simp only [Option.bind_some]
  rw [treeRootWith_blocks (a := LeanDa.logPad r) (c := 7) (L := fun j i => colLeafM r cD j i)
    hCT hTop]
  simp only [Option.bind_some]
  rw [pairBytes_toBytes, Da.daHash, hroot]
  rfl

/-! ## `da_verify` -/

/-- **`da_verify`, soundly under a model, its witness given** (`opens_of`): the facts other than
the columns', each column's facts `F b` and each of its cells' `G b i` give the witness of the
cells' symbols and the columns' weights (`daWitOf`), which opens the returned root and vector
digest with every hash answered by the model and the guest's padding digests. -/
theorem opens_ofM {M : HashModel} {rd : Reader} {r0 r1 v0 v1 : E} {r : ℕ}
    {pb pd hs ctr acc rb ct rt rc0 rc1 rr0 rr1 : E}
    (h : DaRestM M rd r pb pd hs ctr acc rb ct rt rc0 rc1 rr0 rr1 r0 r1 v0 v1) (F : ℕ → ColW)
    (G : ℕ → ℕ → CellW) (hF : ∀ b < 128, ColOkM M rd r pb ct rb hs b (F b))
    (hG : ∀ b < 128, ∀ i < r,
      CellOkM M rd (decide (b < 64)) (F b).lv rb (gen ^ b) (F b).node pb (gen ^ i) (G b i)) :
    ∃ root vd : Digest, (r0, r1) = digestScalars root ∧ (v0, v1) = digestScalars vd ∧
      (daWitOf r (fun b i => (G b i).syms) (fun b => (F b).ws)).OpensWith M.H
        (Da.toBytes padCellD) (Da.toBytes padRowD) root vd := by
  obtain ⟨hr1, hr2, -, hiv0, hiv1, -, -, h89, h92, hlv7, h93, h94, hlvr, hfin, hv0, hv1⟩ := h
  have hr33 : r < 2 ^ 33 := by unfold LeanDa.maxRows at hr2; omega
  obtain ⟨hrN, hNr⟩ := (logPad_iff (lp := LeanDa.logPad r) hr1).mp rfl
  have hNdef : LeanDa.nPad r = 2 ^ LeanDa.logPad r := rfl
  obtain ⟨Rw, hRw⟩ := choose_lt (α := E × List E) (n := r) (P := fun i x =>
      LoadHolds rd (pb * gen ^ i) 0 x.1 ∧ x.2.length = 128 ∧ CellsAt rd x.1 x.2 ∧
        (∀ c ∈ x.2, IsCanonical128 c) ∧ ∃ c0 c1, CellsAt rd (rt * (gen ^ i * gen ^ i)) [c0, c1] ∧
          Ans M (x.2.flatMap cellBytes) (c0, c1))
    (fun i hi => by obtain ⟨P, cs, h⟩ := h93 i hi; exact ⟨(P, cs), h⟩)
  -- the witness
  let sy : ℕ → ℕ → List K := fun b i => (G b i).syms
  let rowL : ℕ → List K := fun i => (List.range 128).flatMap fun b => sy b i
  let vector : List E := (List.range 128).flatMap fun b => (F b).ws
  have hsyl : ∀ b < 128, ∀ i < r, (sy b i).length = 256 := fun b hb i hi => (hG b hb i hi).1
  have hrowL : ∀ i < r, (rowL i).length = 2 ^ LeanDa.logM := fun i hi => by
    rw [length_flatMap_range _ 128 (fun b hb => hsyl b hb i hi)]; rfl
  -- the cell digests
  let cD : ℕ → ℕ → Digest := fun b i => ansD M ((sy b i).flatMap kBytes)
  have hcD : ∀ b < 128, ∀ i < r, M.H ((sy b i).flatMap kBytes) = some (cD b i) ∧
      ((G b i).d0, (G b i).d1) = digestScalars (cD b i) := fun b hb i hi =>
    (hG b hb i hi).2.2.2.1.eq
  -- the column roots
  have hcolroot : ∀ b < 128, ((F b).c0, (F b).c1) =
      digestScalars (nodeM M (colLeafM r cD b) (LeanDa.logPad r) 0) ∧
      TreeAns M (colLeafM r cD b) (LeanDa.logPad r) := by
    intro b hb
    obtain ⟨-, -, -, -, -, -, hgap, hlv, -⟩ := hF b hb
    refine levels_rootM hlv fun i hi => ?_
    rw [← hNdef] at hi
    by_cases hir : i < r
    · obtain ⟨-, -, -, -, -, -, -, -, hn, -⟩ := hG b hb i hir
      simp only [colLeafM, hir, ↓reduceIte]
      rw [gen_sq] at hn
      rw [← (hcD b hb i hir).2]; exact hn
    · have := hgap (i - r) (by omega)
      simp only [colLeafM, hir, ↓reduceIte, padCell_cells]
      unfold GapStep at this
      rwa [pad_ptr, show r + (i - r) = i by omega] at this
  obtain ⟨hRC, hTop⟩ := levels_rootM (L := fun b => nodeM M (colLeafM r cD b) (LeanDa.logPad r) 0)
    hlv7 fun b hb => by
      rw [← (hcolroot b (by simpa using hb)).1]
      exact (hF b (by simpa using hb)).2.2.2.2.2.2.2.2
  -- the row digests
  have hcs : ∀ i < r, (Rw i).2.flatMap cellBytes =
      (List.range 64).flatMap fun b => digestBytes (cD b i) := by
    intro i hi
    obtain ⟨hP, hlen, hcells, -, -⟩ := hRw i hi
    have hc2 : ∀ b < 64, (Rw i).2.getD (2 * b) 0 = (G b i).d0 ∧
        (Rw i).2.getD (2 * b + 1) 0 = (G b i).d1 := by
      intro b hb
      obtain ⟨-, -, -, -, -, -, -, -, -, hst⟩ := hG b (by omega) i hi
      obtain ⟨P', hP', hc⟩ := hst (decide_eq_true hb)
      rw [loadHolds_unique hP' hP, gen_sq] at hc
      obtain ⟨x0, x1⟩ := cellsAt_two.mp hc
      rw [loadHolds_mul_gen_pow] at x0 x1
      rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
      exact ⟨loadHolds_unique (hcells _ (by omega)) x0, loadHolds_unique (hcells _ (by omega)) x1⟩
    rw [← flatMap_range_getD (Rw i).2 0 cellBytes, hlen, show 128 = 2 * 64 by rfl,
      flatMap_range_mul 2]
    refine List.flatMap_congr fun b hb => ?_
    have hb' := List.mem_range.mp hb
    rw [show List.range 2 = [0, 1] from rfl]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Nat.add_zero]
    rw [(hc2 b hb').1, (hc2 b hb').2, digestBytes_eq, ← (hcD b (by omega) i hi).2]
  let rD : ℕ → Digest := fun i => ansD M ((List.range 64).flatMap fun b => digestBytes (cD b i))
  have hrD : ∀ i < r, M.H ((List.range 64).flatMap fun b => digestBytes (cD b i)) = some (rD i) ∧
      ∃ c0 c1, CellsAt rd (rt * (gen ^ i * gen ^ i)) [c0, c1] ∧ (c0, c1) = digestScalars (rD i) := by
    intro i hi
    obtain ⟨-, -, -, -, c0, c1, hc, hA⟩ := hRw i hi
    rw [hcs i hi] at hA
    exact ⟨hA.eq.1, c0, c1, hc, hA.eq.2⟩
  obtain ⟨hRR, hRT⟩ := levels_rootM (L := rowLeafM r rD) hlvr fun i hi => by
    rw [← hNdef] at hi
    by_cases hir : i < r
    · obtain ⟨-, c0, c1, hc, he⟩ := hrD i hir
      simp only [rowLeafM, hir, ↓reduceIte]
      rw [gen_sq] at hc
      rw [← he]; exact hc
    · have := h94 (i - r) (by omega)
      simp only [rowLeafM, hir, ↓reduceIte, padRow_cells]
      unfold L94Step at this
      rwa [pad_ptr, show r + (i - r) = i by omega] at this
  -- the commitment's hash
  obtain ⟨e1, e2⟩ := Prod.mk.inj hRR
  obtain ⟨e3, e4⟩ := Prod.mk.inj hRC
  rw [e1, e2, e3, e4] at hfin
  obtain ⟨hroot, hout⟩ := pair_model hfin
  -- the vector digest
  obtain ⟨vd, hvd, hvout⟩ := vector_chainM (fun b hb => hF b hb) hiv0 hiv1 hv0 hv1
  let rows : List (List K) := (List.range r).map rowL
  have hlen : rows.length = r := by simp [rows]
  change ∃ root vd, _ ∧ _ ∧ (⟨rows, vector⟩ : Da.Witness).OpensWith _ _ _ root vd
  refine ⟨_, vd, hout, hvout, by simp only [hlen]; exact hr1,
    by simp only [hlen]; exact hr2, fun row hrow => ?_, ?_, ?_, ?_, fun row hrow => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hrow
    exact hrowL i (List.mem_range.mp hi)
  · exact commitCodewordsWith_eqM hr1 (sym := sy)
      (fun i hi b hb => listCell_flatMap (fun b => sy b i) (fun b hb => hsyl b hb i hi) hb)
      (fun b hb i hi => (hcD b hb i hi).1) (fun i hi => (hrD i hi).1) hRT
      (fun b hb => (hcolroot b hb).2) hTop hroot
  · show vector.length = _
    rw [length_flatMap_range _ 128 (fun b hb => (hF b hb).1)]; rfl
  · show Da.vectorDigestWith (Da.daHash M.H) vector = _
    rw [Da.vectorDigestWith, vector_bytes, Da.daHash, hvd]
    rfl
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hrow
    have hi' := List.mem_range.mp hi
    have hws : ∀ b < 128, ∀ k < 256, (G b i).wsc.getD k 0 = (F b).ws.getD k 0 := by
      intro b hb k hk
      obtain ⟨-, hwl, hcells, -⟩ := hG b hb i hi'
      obtain ⟨-, -, -, -, hfr, -⟩ := hF b hb
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact hfr.2 k (by rw [(hF b hb).1]; exact hk) _ (hcells k (by omega)).2
    let Ri : E := acc * (gen ^ i) ^ 129
    have hR : ∀ b < 128, (G b i).R = Ri := fun b hb =>
      loadHolds_unique (hG b hb i hi').2.2.2.2.2.1 (h89 i hi').1
    have hA : ∀ b < 128, (G b i).s = cellAt rd Ri (b + 1) - cellAt rd Ri b := by
      intro b hb
      obtain ⟨-, -, -, -, -, -, ha, has, -⟩ := hG b hb i hi'
      rw [hR b hb, loadHolds_mul_gen_pow] at ha has
      have e0 : cellAt rd Ri b = (G b i).a := cellAt_of_load ha
      have e1 : cellAt rd Ri (b + 1) = (G b i).a + (G b i).s := cellAt_of_load has
      rw [e0, e1]
      ring
    have h0 : cellAt rd Ri 0 = 0 := cellAt_of_load (h89 i hi').2
    have h128 : cellAt rd Ri 128 = 0 := by
      obtain ⟨R', hR', h1⟩ := h92 i hi'
      rw [loadHolds_unique hR' (h89 i hi').1] at h1
      exact cellAt_of_load h1
    rw [dot_eq rfl rfl (fun b hb => (hF b hb).1) (fun b hb => hsyl b hb i hi')]
    rw [Finset.sum_congr rfl (g := fun b => (G b i).s) fun b hb => by
        have hb' := Finset.mem_range.mp hb
        rw [(hG b hb' i hi').2.2.2.2.1]
        exact Finset.sum_congr rfl fun k hk => by rw [hws b hb' k (Finset.mem_range.mp hk)],
      Finset.sum_congr rfl (fun b hb => hA b (Finset.mem_range.mp hb)), Finset.sum_range_sub,
      h128, h0, sub_zero]

/-- **`da_verify`'s facts under a model give a witness** that opens the returned root and vector
digest with every hash answered by the model and the guest's padding digests. -/
theorem daFactsM_opens {M : HashModel} {rd : Reader} {r0 r1 v0 v1 : E}
    (h : DaFactsM M rd r0 r1 v0 v1) :
    ∃ (root vd : Digest) (w : Da.Witness), (r0, r1) = digestScalars root ∧
      (v0, v1) = digestScalars vd ∧
      w.OpensWith M.H (Da.toBytes padCellD) (Da.toBytes padRowD) root vd := by
  obtain ⟨r, pb, pd, hs, ctr, acc, rb, ct, rt, rc0, rc1, rr0, rr1, hrest, hcol⟩ := h
  obtain ⟨hr1, hr2, -, -, -, -, hctr, -⟩ := id hrest
  obtain ⟨F, hF⟩ := choose_lt (fun b hb => col_factsM hr1 hr2 hctr hb (hcol b hb))
  obtain ⟨G, hG⟩ := choose_lt₂ (n := 128) (m := r) (P := fun b i c =>
      CellOkM M rd (decide (b < 64)) (F b).lv rb (gen ^ b) (F b).node pb (gen ^ i) c)
    (fun b hb i hi => cell_factsM ((hF b hb).2.2.2.2.2.1 i hi))
  obtain ⟨root, vd, e1, e2, ho⟩ := opens_ofM hrest F G hF hG
  exact ⟨root, vd, _, e1, e2, ho⟩

/-- **`da_verify` is sound under a hash model** (G:2888-2956): on a valid execution's memory and
the squares table, the returned cells are a root and a vector digest that some LeanDA witness
opens, every hash answered by the model and the padding digests the guest's baked ones. -/
theorem da_verify_model {M : HashModel} {rd : Reader} (hm : MemOk rd) {gsq : E}
    (hT : SquaresAt rd gsq) {r0 r1 v0 v1 : E}
    (h : coreProgram.RelB M.sem rd "da_verify" [gsq] [r0, r1, v0, v1]) :
    ∃ (root vd : Digest) (w : Da.Witness), (r0, r1) = digestScalars root ∧
      (v0, v1) = digestScalars vd ∧
      w.OpensWith M.H (Da.toBytes padCellD) (Da.toBytes padRowD) root vd :=
  daFactsM_opens (da_verify_factsM hm hT h)

/-- **The guest's padding digests are LeanDA's at BLAKE2s** (`paddingCell_eq`, `paddingRow_eq`,
checked by `decide`): at the deployed model the generic opening is `Witness.Opens`. -/
theorem opensWith_deployed_iff (root vd : Digest) (w : Da.Witness) :
    w.OpensWith HashModel.deployed.H (Da.toBytes padCellD) (Da.toBytes padRowD) root vd ↔
      w.Opens root vd := by
  rw [← paddingCell_eq, ← paddingRow_eq]
  exact Da.opensWith_some_iff root vd w

/-- `da_verify`'s deployed soundness, from the generic one at the deployed model. -/
theorem da_verify_model_deployed {rd : Reader} (hm : MemOk rd) {gsq : E} (hT : SquaresAt rd gsq)
    {r0 r1 v0 v1 : E} (h : coreProgram.Rel rd "da_verify" [gsq] [r0, r1, v0, v1]) :
    ∃ (root vd : Digest) (w : Da.Witness), (r0, r1) = digestScalars root ∧
      (v0, v1) = digestScalars vd ∧ w.Opens root vd := by
  obtain ⟨root, vd, w, e1, e2, ho⟩ := da_verify_model (M := HashModel.deployed) hm hT (by
    show coreProgram.RelB blakeDeployed rd _ _ _
    rw [relB_deployed]; exact h)
  exact ⟨root, vd, w, e1, e2, (opensWith_deployed_iff root vd w).mp ho⟩

end
end LeanVM.Guest.B1.Digest
