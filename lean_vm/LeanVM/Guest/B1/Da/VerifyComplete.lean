/-
  LeanVM.Guest.B1.Da.VerifyComplete

  `da_verify`, completely: the rows' symbols, the columns' weights and the memory an honest run
  leaves at its buffers give its core IR relation, its returns the root's and the vector digest's
  cells (TRIAGE G #90).
-/

module

public import LeanVM.Guest.B1.Da.VerifyColComplete
public import LeanVM.Guest.B1.Da.VerifyLoopsComplete
public import LeanVM.Guest.B1.Da.VerifyL23Complete
public import LeanVM.Guest.B1.Da.VerifyCChk
public import LeanVM.Guest.B1.Da.RowShapeComplete
public import LeanVM.Guest.B1.Da.Verify

/-!
# `da_verify`, completely

The honest valuation is the body evaluated (`Fwd.ev`) on the exponent table, the hints and the
calls' returns its honest ones (`dvOrc`: the shape `g^r`, `g^L`, the buffers `P`, the trees'
roots). Its atoms hold (their side conditions its loads of the columns' digests); its calls hold
by their completeness: the shape (`da_row_shape_complete`), the prefix bases and running sums'
loops, the column loops (`colLoop_complete`, `dv_col`), the sums' check (`l22_block`, the rows'
inner products zero), the trees (`da_levels_complete`), the rows' digests (`l23_block`) and the
padding rows (`l24_block`). The returns are the root's and the vector digest's cells, as in
`da_verify_holds`.

`da_verify_complete_mem` is pointer-parametric (any `DaPtrs` holding `DaMem`): the placed form
instantiates `P` at the allocator's buffers.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main LeanVM.Guest.B1.Fwd

@[expose] public section

variable {rd : Reader}

/-- The oracle of `da_verify`'s hints and calls' returns. -/
def dvOrc (r L : ℕ) (P : DaPtrs) (cr rr : E × E) (j : ℕ) : E :=
  if j = 1 then gen ^ r else if j = 2 then gen ^ L else if j = 3 then gen ^ 2 ^ L
  else if j = 4 then gen ^ (2 ^ L - r) else if j = 12 then P.pd else if j = 13 then P.pb
  else if j = 17 then P.cd else if j = 26 then P.acc else if j = 27 then P.rb
  else if j = 31 then P.ct else if j = 37 then cr.1 else if j = 38 then cr.2
  else if j = 41 then P.rt else if j = 48 then rr.1 else if j = 49 then rr.2 else 0

/-- A guard's words: `1 + N` and the counter's `1`. -/
theorem guard_vals {σ : Val} {P : List Stmt} {gc : V} {f : String} {one N : V} {rest : List V}
    (h : guardOk P gc f one N rest = true) (hat : ∀ a ∈ atomsIn P, a.Holds rd σ) :
    σ gc = 1 + σ N ∧ σ one = 1 := by
  simp only [guardOk, Bool.and_eq_true] at h
  obtain ⟨⟨-, ha⟩, h1⟩ := h
  split at ha
  · rename_i p q hpq
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ha
    obtain ⟨hp1, rfl⟩ := ha
    exact ⟨by rw [addOf_sound hpq hat, const_sound hp1 hat, word_one],
      by rw [const_sound h1 hat, word_one]⟩
  · exact absurd ha (by simp)

theorem colLeaves_root (r L : ℕ) (syms : ℕ → ℕ → List K) :
    cellRoot 7 (colLeaves r L syms) = digestScalars (mRoot 7 fun j => mRoot L (cellLeaf r syms j)) := by
  rw [colLeaves, show (128 : ℕ) = 2 ^ 7 from rfl]
  exact cellRoot_mRoot 7 _

theorem rowLeaves_root (r L : ℕ) (syms : ℕ → ℕ → List K) :
    cellRoot L (rowLeaves r L syms) = digestScalars (mRoot L (rowLeaf r syms)) := by
  rw [rowLeaves]; exact cellRoot_mRoot L _

theorem prefixCells_bytes (syms : ℕ → ℕ → List K) (i : ℕ) :
    cellsBytes (prefixCells syms i) = (List.range 64).flatMap fun j => digestBytes (cellD syms i j) := by
  rw [prefixCells, cellsBytes, List.flatMap_assoc]
  refine List.flatMap_congr fun j _ => ?_
  rw [digestBytes_eq_cells, cellsBytes]; rfl

theorem canon_digestCells_flat {α : Type} (l : List α) (f : α → Digest) :
    AllCanonical (l.flatMap fun a => digestCells (f a)) := by
  intro c hc
  obtain ⟨a, -, hc⟩ := List.mem_flatMap.mp hc
  simp only [digestCells, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact (digestScalars_canonical _).1
  · exact (digestScalars_canonical _).2

/-- `da_verify`'s honest valuation: its body evaluated on the exponent table, the hints and the
calls' returns `dvOrc`'s. -/
noncomputable def dvσ (rd : Reader) (gsq : E) (r L : ℕ) (P : DaPtrs) (cr rr : E × E) : Val :=
  B1.Val.ofArgs (ev rd (dvOrc r L P cr rr) [gsq] (Fn.body Data.core25))

/-- **What `da_verify`'s honest valuation is**: its atoms hold, and its words. -/
structure DvVals (rd : Reader) (σ : Val) (gsq : E) (r L : ℕ) (P : DaPtrs) (cr rr : E × E)
    (root vd : Digest) : Prop where
  atoms : ∀ a ∈ atomsIn dvP, a.Holds rd σ
  v0 : σ (.n 0) = gsq
  v1 : σ (.n 1) = gen ^ r
  v2 : σ (.n 2) = gen ^ L
  v3 : σ (.n 3) = gen ^ 2 ^ L
  v4 : σ (.n 4) = gen ^ (2 ^ L - r)
  v11 : σ (.n 11) = gen ^ (128 * 2 ^ L)
  v12 : σ (.n 12) = P.pd
  v13 : σ (.n 13) = P.pb
  v17 : σ (.n 17) = P.cd
  v25 : σ (.n 25) = gen ^ (129 * r)
  v26 : σ (.n 26) = P.acc
  v27 : σ (.n 27) = P.rb
  v31 : σ (.n 31) = P.ct
  v32 : σ (.n 32) = 1
  v33 : σ (.n 33) = gen ^ 64
  v37 : σ (.n 37) = cr.1
  v38 : σ (.n 38) = cr.2
  v40 : σ (.n 40) = gen ^ (4 * 2 ^ L)
  v41 : σ (.n 41) = P.rt
  v48 : σ (.n 48) = rr.1
  v49 : σ (.n 49) = rr.2
  g15 : σ (.n 15) = 1 + gen ^ r
  g16 : σ (.n 16) = 1
  g29 : σ (.n 29) = 1 + gen ^ r
  g30 : σ (.n 30) = 1
  g35 : σ (.n 35) = 1 + gen ^ r
  g36 : σ (.n 36) = 1
  g43 : σ (.n 43) = 1 + gen ^ r
  g44 : σ (.n 44) = 1
  g46 : σ (.n 46) = 1 + gen ^ (2 ^ L - r)
  g47 : σ (.n 47) = 1
  rets : [σ (.n 993), σ (.n 994), σ (.n 995), σ (.n 996)] = digestCells root ++ digestCells vd

set_option maxRecDepth 20000 in
/-- **`da_verify`'s honest valuation**, on a memory holding the column digests at `P.cd`. -/
theorem dv_core {gsq : E} {r L : ℕ}
    {syms : ℕ → ℕ → List K} {ws : ℕ → List E} {P : DaPtrs} (hcd : ReadsAt rd P.cd (cdCells ws)) :
    DvVals rd (dvσ rd gsq r L P (cellRoot 7 (colLeaves r L syms)) (cellRoot L (rowLeaves r L syms)))
      gsq r L P (cellRoot 7 (colLeaves r L syms)) (cellRoot L (rowLeaves r L syms))
      (daRoot r L syms) (daVd ws) := by
  have hok := dv_ok
  unfold dvOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hparams, hbody⟩, -⟩, -⟩, hm11⟩, hg18⟩, hm25⟩, hg19⟩,
    hc32⟩, -⟩, hc33⟩, -⟩, hg22⟩, -⟩, hm40⟩, hg23⟩, hg24⟩, -⟩, hroot⟩, hcp993⟩,
    hcp994⟩, hld17⟩, hvshape⟩, hvnb⟩, hcp995⟩, hcp996⟩ := hok
  have hcok := dvc_ok
  unfold dvCOk at hcok
  simp only [Bool.and_eq_true, Option.isSome_iff_exists, List.isEmpty_iff, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true'] at hcok
  obtain ⟨⟨⟨⟨⟨⟨⟨c', hchk⟩, hst⟩, hcanA⟩, hneeds⟩, hcallsAll⟩, hhints⟩, -⟩ := hcok
  have hbody' := stmtsEqb_sound hbody
  -- the valuation
  set cr := cellRoot 7 (colLeaves r L syms) with hcrd
  set rr := cellRoot L (rowLeaves r L syms) with hrrd
  let w : ℕ → E := dvOrc r L P cr rr
  set σ := dvσ rd gsq r L P cr rr with hσ
  have hidx : ∀ v, σ v = σ (.n v.idx) := fun v => by rw [hσ]; rfl
  obtain ⟨-, -, hgs⟩ := ev_spec rd w (Fn.body Data.core25) [gsq] hchk
  rw [show [gsq].length = 1 from rfl, hst] at hgs
  have hmemP : ∀ s ∈ dvP, s ∈ Fn.body Data.core25 := fun s hs => by
    rw [hbody']; exact List.mem_append_left _ hs
  have hg : ∀ a ∈ atomsIn dvP, Good rd [] w σ a := fun a ha =>
    hgs (.atom a) (hmemP _ (atom_mem_of_atomsIn ha))
  have e0 : σ (.n 0) = gsq := by rw [hσ]; exact ev_params rd _ (l := [gsq]) hchk (by simp)
  -- the hints and the calls' returns
  have hint : ∀ a ∈ dvHints, Good rd [] w σ a := fun a ha => hg a (by simpa using hhints a ha)
  simp only [dvHints, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Good] at hint
  obtain ⟨hsh, h12, h13, h17, h26, h27, h31, h41⟩ := hint
  have v1 : σ (.n 1) = gen ^ r := by rw [hsh.1]; rfl
  have v2 : σ (.n 2) = gen ^ L := by rw [hsh.2]; rfl
  have v12 : σ (.n 12) = P.pd := by rw [h12]; rfl
  have v13 : σ (.n 13) = P.pb := by rw [h13]; rfl
  have v17 : σ (.n 17) = P.cd := by rw [h17]; rfl
  have v26 : σ (.n 26) = P.acc := by rw [h26]; rfl
  have v27 : σ (.n 27) = P.rb := by rw [h27]; rfl
  have v31 : σ (.n 31) = P.ct := by rw [h31]; rfl
  have v41 : σ (.n 41) = P.rt := by rw [h41]; rfl
  have hcallIn : ∀ c ∈ dvCalls, GoodS rd [] w σ c := by
    intro c hc
    have := List.all_eq_true.mp (show dvCalls.all (fun c => dvP.any (stmtEqb · c)) = true by
      have h := dvc_ok
      unfold dvCOk at h
      simp only [Bool.and_eq_true] at h
      exact h.2) c hc
    obtain ⟨s, hs, he⟩ := List.any_eq_true.mp this
    rw [← stmtEqb_sound he]
    exact hgs s (hmemP s hs)
  have hcalls := hcallIn
  simp only [dvCalls, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    GoodS] at hcalls
  obtain ⟨hcs, -, -, -, -, -, hc7, -, -, hdisp⟩ := hcalls
  have v3 : σ (.n 3) = gen ^ 2 ^ L := by rw [hcs.1]; rfl
  have v4 : σ (.n 4) = gen ^ (2 ^ L - r) := by rw [hcs.2]; rfl
  have v37 : σ (.n 37) = cr.1 := by rw [hc7.1]; rfl
  have v38 : σ (.n 38) = cr.2 := by rw [hc7.2]; rfl
  have v48 : σ (.n 48) = rr.1 := by rw [hdisp.1]; rfl
  have v49 : σ (.n 49) = rr.2 := by rw [hdisp.2]; rfl
  -- the atoms
  have hcd' : ∀ i < 256, σ (.n (69 + i)) = (cdCells ws).getD i 0 := by
    intro i hi
    obtain ⟨a, ha, hp⟩ : ∃ a ∈ atomsIn dvP, isLoadAt (.n (69 + i)) (.n 17) i a = true := by
      simp only [loadsOk, List.all_eq_true, List.mem_range] at hld17
      have := hld17 i (by simpa using hi)
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range (show i < 256 by omega), Option.map_some, Option.getD_some] at this
      exact List.any_eq_true.mp this
    rw [good_load_of_any rfl hg (List.any_eq_true.mpr ⟨a, ha, hp⟩), v17,
      rdAt_of_load (hcd i (by rw [cdCells_length]; exact hi)),
      List.getD_eq_getElem _ _ (by rw [cdCells_length]; exact hi)]
  have hcr : cr = digestScalars (mRoot 7 fun j => mRoot L (cellLeaf r syms j)) :=
    colLeaves_root r L syms
  have hrr : rr = digestScalars (mRoot L (rowLeaf r syms)) := rowLeaves_root r L syms
  have hA : ∀ i ∈ [37, 38, 48, 49] ++ (List.range 256).map (69 + ·), IsCanonical128 (σ (.n i)) := by
    intro i hi
    simp only [List.cons_append, List.mem_cons, List.nil_append, List.mem_map,
      List.mem_range] at hi
    rcases hi with rfl | rfl | rfl | rfl | ⟨k, hk, rfl⟩
    · rw [v37, hcr]; exact (digestScalars_canonical _).1
    · rw [v38, hcr]; exact (digestScalars_canonical _).2
    · rw [v48, hrr]; exact (digestScalars_canonical _).1
    · rw [v49, hrr]; exact (digestScalars_canonical _).2
    · rw [hcd' k hk, List.getD_eq_getElem _ _ (by rw [cdCells_length]; exact hk)]
      exact canon_digestCells_flat _ _ _ (List.getElem_mem _)
  have hat : ∀ a ∈ atomsIn dvP, a.Holds rd σ := by
    refine atoms_holds hidx hcanA hg hA fun a ha hns => Or.inl ?_
    rcases hneeds a ha with h | h
    · rw [hns] at h; exact absurd h (by simp)
    · cases a <;> simp only [isCdLoad, Bool.false_eq_true, Bool.and_eq_true,
        decide_eq_true_eq] at h
      rename_i d p o
      obtain ⟨⟨rfl, rfl⟩, ho⟩ := h
      show LoadHolds rd (σ (.n 17)) o (σ (.n (69 + o)))
      rw [v17, hcd' o ho, List.getD_eq_getElem _ _ (by rw [cdCells_length]; exact ho)]
      exact hcd o (by rw [cdCells_length]; exact ho)
  -- the returns
  have hrootd : [σ (.n 993), σ (.n 994)] = digestCells (daRoot r L syms) := by
    obtain ⟨hd, -⟩ := chain_final hroot rfl hat (pre := []) (n := 0) rfl
      (fun c => (cellsOfState_zero false c).symm)
    have hv : ((rootSpec (atomsIn dvP)).vals σ).take ((rootSpec (atomsIn dvP)).len / 16) =
        [σ (.n 48), σ (.n 49), σ (.n 37), σ (.n 38)] := by
      simp [rootSpec, ChainSpec.vals, srcVal]
    rw [hv, List.nil_append, v48, v49, v37, v38, hrr, hcr] at hd
    have hb : cellsBytes [(digestScalars (mRoot L (rowLeaf r syms))).1,
        (digestScalars (mRoot L (rowLeaf r syms))).2,
        (digestScalars (mRoot 7 fun j => mRoot L (cellLeaf r syms j))).1,
        (digestScalars (mRoot 7 fun j => mRoot L (cellLeaf r syms j))).2] =
        digestBytes (mRoot L (rowLeaf r syms)) ++
          digestBytes (mRoot 7 fun j => mRoot L (cellLeaf r syms j)) := by
      rw [digestBytes_eq_cells, digestBytes_eq_cells]
      simp [cellsBytes]
    rw [hb, ← daRoot] at hd
    rw [copy_sound hcp993 hat, copy_sound hcp994 hat, digestCells]
    simp only [Prod.ext_iff] at hd
    rw [← hd.1, ← hd.2]
  have hvd : [σ (.n 995), σ (.n 996)] = digestCells (daVd ws) := by
    have hchkV : (vdSpec (atomsIn dvP)).check (atomsIn dvP) = true :=
      ChainSpec.check_of_parts hvshape fun k hk => by
        rcases Nat.lt_or_ge k 8 with a | a
        · exact ChainSpec.partOk_sound vd_chain0_ok k (by omega) a
        rcases Nat.lt_or_ge k 16 with b | b
        · exact ChainSpec.partOk_sound vd_chain1_ok k a b
        rcases Nat.lt_or_ge k 24 with c | c
        · exact ChainSpec.partOk_sound vd_chain2_ok k b c
        · exact ChainSpec.partOk_sound vd_chain3_ok k c (by omega)
    obtain ⟨hd, -⟩ := chain_final hchkV rfl hat (pre := []) (n := 0) rfl
      (fun c => (cellsOfState_zero false c).symm)
    have hr := loads_sound hld17 hat
    have hv0 : (((List.range 256).map fun i => some (V.n (69 + i))).map (srcVal σ)) =
        memRun rd (σ (.n 17)) 256 := by
      have := readsAt_memRun hr
      simpa using this
    have hv : ((vdSpec (atomsIn dvP)).vals σ).take ((vdSpec (atomsIn dvP)).len / 16) =
        memRun rd (σ (.n 17)) 256 := by
      rw [← hv0, show (vdSpec (atomsIn dvP)).len / 16 = 256 by simp [vdSpec]]
      simp [vdSpec, ChainSpec.vals]
    have hmem' : memRun rd (σ (.n 17)) 256 = cdCells ws := by
      rw [v17, readsAt_memRun hcd, cdCells_length]
    have hbytes : cellsBytes (cdCells ws) =
        (List.range 128).flatMap fun j => digestBytes (colD ws j) := by
      rw [cdCells, cellsBytes, List.flatMap_assoc]
      refine List.flatMap_congr fun j _ => ?_
      rw [digestBytes_eq_cells, cellsBytes]; rfl
    rw [hv, hmem', hbytes, List.nil_append, ← daVd] at hd
    rw [copy_sound hcp995 hat, copy_sound hcp996 hat, digestCells]
    simp only [Prod.ext_iff] at hd
    rw [← hd.1, ← hd.2]
  obtain ⟨g15, g16⟩ := guard_vals hg18 hat
  obtain ⟨g29, g30⟩ := guard_vals hg19 hat
  obtain ⟨g35, g36⟩ := guard_vals hg22 hat
  obtain ⟨g43, g44⟩ := guard_vals hg23 hat
  obtain ⟨g46, g47⟩ := guard_vals hg24 hat
  refine ⟨hat, e0, v1, v2, v3, v4, ?_, v12, v13, v17, ?_, v26, v27, v31,
    by rw [const_sound hc32 hat, word_one], by rw [const_sound hc33 hat, word_g64], v37, v38, ?_,
    v41, v48, v49, by rw [g15, v1], g16, by rw [g29, v1], g30, by rw [g35, v1], g36,
    by rw [g43, v1], g44, by rw [g46, v4], g47, by
      rw [show [σ (.n 993), σ (.n 994), σ (.n 995), σ (.n 996)] =
        [σ (.n 993), σ (.n 994)] ++ [σ (.n 995), σ (.n 996)] from rfl, hrootd, hvd]⟩
  · rw [monoIs_sound hm11 hat, v3, ← pow_succ', ← pow_mul,
      show 2 ^ L * (127 + 1) = 128 * 2 ^ L by ring]
  · rw [monoIs_sound hm25 hat, v1, ← pow_succ', ← pow_mul, show r * (128 + 1) = 129 * r by ring]
  · rw [monoIs_sound hm40 hat, v3, ← pow_succ', ← pow_mul,
      show 2 ^ L * (3 + 1) = 4 * 2 ^ L by ring]

set_option maxRecDepth 20000 in
/-- **`da_verify` is complete** on the honest memory of `r` rows of symbols `syms` and the columns'
weights `ws`, the rows orthogonal to the vector, at any choice of its buffers `P`. -/
theorem da_verify_complete_mem (hm : MemOk rd) {gsq : E} (hsq : SquaresAt rd gsq) {r L : ℕ}
    (hr1 : 1 ≤ r) (hr : r ≤ LeanDa.maxRows) (hL : 2 ^ L = LeanDa.nPad r)
    {syms : ℕ → ℕ → List K} {ws : ℕ → List E} (hsl : ∀ i j, (syms i j).length = 256)
    (hwl : ∀ j, (ws j).length = 256) (hdot : ∀ i < r, accSum syms ws i 128 = 0) {P : DaPtrs}
    (hmem : DaMem r L syms ws rd P) :
    coreProgram.Rel rd "da_verify" [gsq] (digestCells (daRoot r L syms) ++ digestCells (daVd ws)) := by
  -- the shape
  have hr' := hr
  unfold LeanDa.maxRows at hr'
  obtain ⟨hlo, hhi⟩ := nPad_bounds hr1
  have hrL : r ≤ 2 ^ L := hL ▸ hlo
  have hlt : 2 ^ L < 2 ^ 11 := by
    calc 2 ^ L < 2 * r := hL ▸ hhi
      _ ≤ 2 ^ 11 := by norm_num; omega
  have hL10 : L ≤ 10 := by
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hlt
    omega
  have hok := dv_ok
  unfold dvOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hparams, hbody⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩,
    -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hok
  have hcok := dvc_ok
  unfold dvCOk at hcok
  simp only [Bool.and_eq_true, Option.isSome_iff_exists, List.isEmpty_iff, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true'] at hcok
  obtain ⟨⟨⟨⟨⟨⟨⟨c', -⟩, -⟩, -⟩, -⟩, hcallsAll⟩, -⟩, -⟩ := hcok
  have hbody' := stmtsEqb_sound hbody
  have hV := dv_core (gsq := gsq) (syms := syms) (r := r) (L := L) hmem.cd
  set cr := cellRoot 7 (colLeaves r L syms)
  set rr := cellRoot L (rowLeaves r L syms)
  set σ := dvσ rd gsq r L P cr rr
  have hat := hV.atoms
  -- the calls
  have find359 := find_of_idx (by
    have h := l18_ok; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2)
    (show 356 < coreProgram.length by rw [coreProgram_length]; omega)
  have find360 := find_of_idx (by
    have h := l19_ok; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2)
    (show 357 < coreProgram.length by rw [coreProgram_length]; omega)
  have find363 := find_of_idx (by
    have h := l22_ok; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2)
    (show 360 < coreProgram.length by rw [coreProgram_length]; omega)
  have find365 := find_of_idx (by
    have h := l23_ok; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2)
    (show 362 < coreProgram.length by rw [coreProgram_length]; omega)
  have find366 := find_of_idx (by
    have h := l24_ok; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2)
    (show 363 < coreProgram.length by rw [coreProgram_length]; omega)
  obtain ⟨⟨s18, -⟩, ⟨s19, -⟩, ⟨s22, -⟩, ⟨s24, -⟩⟩ := dvloops_shape
  have s23 : loopShapeF (coreProgram.getD 362 default) "__loop22" = true := by
    have h := l23_ok
    simp only [l23Ok, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1.1.1.1.1.1.1.1.1
  have hacc0 : ∀ i < r, ∀ b ≤ 128, LoadHolds rd (P.acc * (gen ^ i) ^ 129) b (accSum syms ws i b) := by
    intro i hi b hb
    have := hmem.acc i hi b (by simp; omega)
    simpa using this
  have hcolR : ∀ k < 128, coreProgram.Rel rd (if k < 64 then "da_verify_column__L1" else
      "da_verify_column__L0") [gen ^ k, gen ^ r, gen ^ 2 ^ L, gen ^ (2 ^ L - r), gen ^ L, P.pb, P.ct,
        P.rb, P.cd] [] := fun k hk => dv_col hmem hL10 hrL hsl hwl hk
  have hall : ∀ s ∈ dvP, SHolds (coreProgram.Rel rd) rd σ s := by
    intro s hs
    by_cases hsa : ∃ a, s = .atom a
    · obtain ⟨a, rfl⟩ := hsa
      exact hat a (mem_atomsIn hs)
    have hsk : dvCalls.any (stmtEqb s) = true := by
      have := hcallsAll s hs
      cases s with
      | atom a => exact absurd ⟨a, rfl⟩ hsa
      | _ => exact this
    obtain ⟨c, hc, he⟩ := List.any_eq_true.mp hsk
    rw [stmtEqb_sound he]
    simp only [dvCalls, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · show coreProgram.Rel rd "da_row_shape" [σ (.n 1), σ (.n 2), σ (.n 0)] [σ (.n 3), σ (.n 4)]
      rw [hV.v1, hV.v2, hV.v0, hV.v3, hV.v4]
      exact da_row_shape_complete rd hm gsq hsq r L hr1 hr hL
    · show IsInK (σ (.n 15)) ∧ (σ (.n 15) ≠ 0 →
        coreProgram.Rel rd "__loop17" [σ (.n 16), σ (.n 1), σ (.n 13), σ (.n 12)] [])
      rw [hV.g15, hV.g16, hV.v1, hV.v13, hV.v12]
      exact guard_complete find359 s18 (rest := [P.pb, P.pd]) (m := r)
        fun i hi => l18_block (hmem.pbase i hi)
    · show IsInK (σ (.n 29)) ∧ (σ (.n 29) ≠ 0 →
        coreProgram.Rel rd "__loop18" [σ (.n 30), σ (.n 1), σ (.n 26), σ (.n 27)] [])
      rw [hV.g29, hV.g30, hV.v1, hV.v26, hV.v27]
      exact guard_complete find360 s19 (rest := [P.acc, P.rb]) (m := r)
        fun i hi => l19_block (hmem.rbase i hi) (by
          have := hacc0 i hi 0 (by omega); simpa [accSum] using this)
    · show coreProgram.Rel rd "__loop19" [σ (.n 32), σ (.n 1), σ (.n 3), σ (.n 4), σ (.n 2),
        σ (.n 13), σ (.n 31), σ (.n 27), σ (.n 17)] []
      rw [hV.v32, ← pow_zero gen, hV.v1, hV.v3, hV.v4, hV.v2, hV.v13, hV.v31, hV.v27, hV.v17]
      exact colLoop_complete (by rw [coreProgram_length]; omega) l20_ok word_g64 (a := 0)
        (fun k _ hk => by have := hcolR k (by omega); rwa [ite_pos' hk] at this) 0 le_rfl (by norm_num)
    · show coreProgram.Rel rd "__loop20" [σ (.n 33), σ (.n 1), σ (.n 3), σ (.n 4), σ (.n 2),
        σ (.n 13), σ (.n 31), σ (.n 27), σ (.n 17)] []
      rw [hV.v33, hV.v1, hV.v3, hV.v4, hV.v2, hV.v13, hV.v31, hV.v27, hV.v17]
      exact colLoop_complete (by rw [coreProgram_length]; omega) l21_ok word_g128 (a := 64)
        (fun k hk hk' => by have := hcolR k hk'; rwa [ite_neg' (by omega)] at this) 64 le_rfl
        (by norm_num)
    · show IsInK (σ (.n 35)) ∧ (σ (.n 35) ≠ 0 →
        coreProgram.Rel rd "__loop21" [σ (.n 36), σ (.n 1), σ (.n 27)] [])
      rw [hV.g35, hV.g36, hV.v1, hV.v27]
      exact guard_complete find363 s22 (rest := [P.rb]) (m := r)
        fun i hi => l22_block (hmem.rbase i hi) (by
          have := hacc0 i hi 128 le_rfl; rwa [hdot i hi] at this)
    · show coreProgram.Rel rd "da_levels__L128_L7" [σ (.n 31)] [σ (.n 37), σ (.n 38)]
      rw [hV.v31, hV.v37, hV.v38]
      exact da_levels_complete 7 (by norm_num) rd P.ct (colLeaves r L syms)
        (by simp [colLeaves]) (fun _ => by rw [colLeaves]; exact canon_scalars_map _ _) hmem.ct
    · show IsInK (σ (.n 43)) ∧ (σ (.n 43) ≠ 0 →
        coreProgram.Rel rd "__loop22" [σ (.n 44), σ (.n 1), σ (.n 13), σ (.n 41)] [])
      rw [hV.g43, hV.g44, hV.v1, hV.v13, hV.v41]
      refine guard_complete find365 s23 (rest := [P.pb, P.rt]) (m := r) fun i hi => ?_
      have hi2 : i < 2 ^ L := by omega
      obtain ⟨t0, t1⟩ := treeMem_leaf hmem.rt (by simp [rowLeaves]) hi2
      have hrl : (rowLeaves r L syms).getD i 0 = digestScalars (rowD syms i) := by
        simp [rowLeaves, List.getD_eq_getElem?_getD, hi2, rowLeaf, hi]
      rw [hrl, rowD, ← prefixCells_bytes, ← gen_sq] at t0 t1
      exact l23_block (hmem.pbase i hi) (hmem.pcells i hi)
        (by rw [prefixCells, length_flatMap_range _ 2 _ (fun j => rfl)])
        (canon_digestCells_flat _ _) t0 t1
    · show IsInK (σ (.n 46)) ∧ (σ (.n 46) ≠ 0 →
        coreProgram.Rel rd "__loop23" [σ (.n 47), σ (.n 4), σ (.n 41), σ (.n 1)] [])
      rw [hV.g46, hV.g47, hV.v4, hV.v41, hV.v1]
      refine guard_complete find366 s24 (rest := [P.rt, gen ^ r]) (m := 2 ^ L - r) fun d hd => ?_
      have hrd : r + d < 2 ^ L := by omega
      obtain ⟨t0, t1⟩ := treeMem_leaf hmem.rt (by simp [rowLeaves]) hrd
      have hrl : (rowLeaves r L syms).getD (r + d) 0 = digestScalars daPadRowDigest := by
        simp [rowLeaves, List.getD_eq_getElem?_getD, hrd, rowLeaf]
      rw [hrl] at t0 t1
      have e : P.rt * (gen ^ r * gen ^ r) * (gen ^ d * gen ^ d) = P.rt * gen ^ (2 * (r + d)) := by
        rw [gen_sq, gen_sq, mul_assoc, ← pow_add]; congr 2; ring
      exact l24_block (by rw [e]; exact t0) (by rw [e]; exact t1)
    · show (∃ (j : ℕ) (h : j < dlNames.length), σ (.n 2) = ofK (Parameters.gpow j) ∧
        coreProgram.Rel rd dlNames[j] [σ (.n 41)] [σ (.n 48), σ (.n 49)])
      have hlt : L < dlNames.length := by simp [dlNames]; omega
      refine ⟨L, hlt, by rw [hV.v2, gen_pow_eq_ofK], ?_⟩
      rw [show dlNames[L] = daLevelsName L by simp [dlNames], hV.v41, hV.v48, hV.v49]
      exact da_levels_complete L hL10 rd P.rt (rowLeaves r L syms) (by simp [rowLeaves])
        (fun _ => by rw [rowLeaves]; exact canon_scalars_map _ _) hmem.rt
  refine (rel_iff_sem find_da_verify _ _).mpr ⟨σ, by rw [hparams]; simp [hV.v0], ?_⟩
  rw [hbody']
  exact holdsList_straight dvP _ _ _ hall hV.rets

end
end LeanVM.Guest.B1.Da
