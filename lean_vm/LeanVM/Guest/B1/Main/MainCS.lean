/-
  LeanVM.Guest.B1.Main.MainCS

  `MainC.lean` under any semantics of `BLAKE2S` (`S : BlakeSem`).
-/

module

public import LeanVM.Guest.B1.Main.MainC
public import LeanVM.Guest.B1.Main.LoopsCS
public import LeanVM.Guest.B1.UniformS
public import LeanVM.Guest.B1.BasicS
public import LeanVM.Guest.B1.Main.CalleesWM

/-!
# `MainC.lean` under any `BLAKE2S` semantics

Each definition and lemma of `MainC.lean` that mentions the semantics, with `S : BlakeSem` a
parameter and a `S` in its name.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

variable {S : BlakeSem}

variable {rd : Reader} {C : CallRel}

variable (S) in
/-- **What `main`'s body needs**: the counts' bounds, its callees' relations, the compression of
the signer set, and the words of its `HeapBuf`s and of the public input. -/
structure MainOkS (C : CallRel) (rd : Reader) (R : MainRun) : Prop where
  low : LeanVM.Guest.B1.LowDef 16 rd
  total : R.total ≤ 65535
  nc : R.nc ≤ 16
  rd1 : R.rd ≤ 1
  da : R.da ≤ 16
  ud : R.ud ≤ 257
  dau : R.da + R.ud ≤ 257
  rx : R.rx ≤ 65535
  rs : R.rs ≤ 65535
  decl : 0 < R.dx + R.ds + R.da
  tables : C "exponent_tables" [] [R.glp, R.gsq]
  loop0 : R.da + R.ud ≠ 0 → C "__loop0" [1, gen ^ R.da * gen ^ R.ud, R.daT] []
  daList : C "da_list_digest" [R.daT, gen ^ R.da]
    [(digestScalars R.daDig).1, (digestScalars R.daDig).2]
  xList : C "claim_list_digest" [R.xT, gen ^ R.dx, R.gsq]
    [(digestScalars R.xDig).1, (digestScalars R.xDig).2]
  sList : C "claim_list_digest" [R.sT, gen ^ R.ds, R.gsq]
    [(digestScalars R.sDig).1, (digestScalars R.sDig).2]
  loop1 : R.ux ≠ 0 → C "__loop1" [1, gen ^ R.ux, R.xT, gen ^ R.dx] []
  loop2 : R.us ≠ 0 → C "__loop2" [1, gen ^ R.us, R.sT, gen ^ R.ds] []
  sig : S.check ![(digestScalars R.xDig).1, (digestScalars R.xDig).2, (digestScalars R.sDig).1,
    (digestScalars R.sDig).2] Value.ivCells.1 Value.ivCells.2 (digestScalars R.sigDig).1
    (digestScalars R.sigDig).2 (metadataCell 64 true)
  sigp : ReadsAt rd R.sigp [(digestScalars R.sigDig).1, (digestScalars R.sigDig).2]
  loop3 : R.rx ≠ 0 → C "__loop3"
    [1, gen ^ R.rx, gen ^ R.dx * gen ^ R.ux, R.cover, R.xT] []
  loop4 : R.rs ≠ 0 → C "__loop4"
    [1, gen ^ R.rs, gen ^ R.ds * gen ^ R.us, R.cover, gen ^ R.dx * gen ^ R.ux, gen ^ R.rx, R.sT] []
  daVerify : R.rd = 1 → C "da_verify" [R.gsq] [R.dr0, R.dr1, R.dr2, R.dr3]
  daCover : R.rd = 1 → C "cover_da_root"
    [R.daT, R.cover * (gen ^ R.dx * gen ^ R.ux * (gen ^ R.ds * gen ^ R.us)),
      gen ^ R.da * gen ^ R.ud, gen ^ R.rx * gen ^ R.rs] [R.dr0, R.dr1, R.dr2, R.dr3]
  written0 : LoadHolds rd R.written 0 (gen ^ R.rx * gen ^ R.rs * gen ^ R.rd)
  loop5 : R.nc ≠ 0 → C "__loop5"
    [1, gen ^ R.nc, R.written, R.xT, R.cover, gen ^ R.dx * gen ^ R.ux, R.gsq, R.sT,
      gen ^ R.ds * gen ^ R.us, R.carried, R.daT,
      R.cover * (gen ^ R.dx * gen ^ R.ux * (gen ^ R.ds * gen ^ R.us)), gen ^ R.da * gen ^ R.ud,
      (digestScalars R.seed).1, (digestScalars R.seed).2, R.cpi, R.glp, R.cfresh] []
  writtenN : LoadHolds rd R.written R.nc
    (gen ^ R.dx * gen ^ R.ux * (gen ^ R.ds * gen ^ R.us) * (gen ^ R.da * gen ^ R.ud))
  leaf : R.nc = 0 → ReadsAt rd R.dstmt
    (List.replicate 22 0 ++ [R.lbv] ++ List.replicate 28 0 ++ [R.lmA, R.lmB])
  agg : R.nc ≠ 0 → C "aggregate_claims"
    [gen ^ R.nc, R.cpi, R.cfresh, R.carried, R.dstmt] []
  stmt : C "statement_digest"
    [(digestScalars R.seed).1, (digestScalars R.seed).2, R.sigp, (digestScalars R.daDig).1,
      (digestScalars R.daDig).2, R.dstmt] [(digestScalars R.stDig).1, (digestScalars R.stDig).2]
  pub0 : rd 1 = some (digestScalars R.stDig).1
  pub1 : rd g = some (digestScalars R.stDig).2

set_option maxRecDepth 100000 in
theorem mainS_pre_holds {R : MainRun} (h : MainOkS S C rd R) :
    Stmt.HoldsListB S C rd (mainVal rd R) mainPre True (fun rs => rs = []) := by
  simp only [mainPre, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil,
    word_gmax, word_g16, word_g257, word_gen, word_one, word_iv0, word_iv1, word_md64]
  simp only [mainVal]
  b1_look
  simp only [true_and, and_true]
  have hm := h.low
  have ht := h.total
  have hda := h.dau
  simp only [MainRun.total] at ht
  have e50 : gen ^ R.da * gen ^ R.ud = gen ^ (R.da + R.ud) := (pow_add _ _ _).symm
  have e58 : gen ^ R.dx * gen ^ R.ux * (gen ^ R.ds * gen ^ R.us) * (gen ^ R.da * gen ^ R.ud) =
      gen ^ R.total := by rw [MainRun.total]; simp only [← pow_add]
  have hT : R.total ≤ 65535 := h.total
  have rc : ∀ e b, e ≤ b → b < 2 ^ 16 → LoadHolds rd (gen ^ e) 0 (cellAt rd (gen ^ e) 0) ∧
      gen ^ b = gen ^ e * gen ^ (b - e) ∧
      LoadHolds rd (gen ^ (b - e)) 0 (cellAt rd (gen ^ (b - e)) 0) := fun e b h1 h2 =>
    ⟨loadHolds_cellAt_gen hm (by omega), by rw [← pow_add]; congr 1; omega,
      loadHolds_cellAt_gen hm (by omega)⟩
  have h0 : 0 < R.dx + R.ds + R.da := h.decl
  refine ⟨rc _ _ (by omega) (by norm_num), rc _ _ (by omega) (by norm_num),
    rc _ _ h.rx (by norm_num), rc _ _ (by omega) (by norm_num), rc _ _ (by omega) (by norm_num),
    rc _ _ h.rs (by norm_num), rc _ _ h.nc (by norm_num), pow_one gen, rc _ _ h.rd1 (by norm_num),
    rc _ _ h.da (by norm_num), rc _ _ h.ud (by norm_num), ?_, ?_, h.tables, one_add_isInK' _ _,
    fun hne => h.loop0 (by intro hz; apply hne; rw [e50, hz, pow_zero]; exact e_add_eq_zero_iff.mpr rfl),
    h.daList, h.xList, h.sList, one_add_isInK _, fun hne => h.loop1 (ne_zero_of_one_add hne),
    one_add_isInK _, fun hne => h.loop2 (ne_zero_of_one_add hne), ?_, h.sig,
    by simpa using h.sigp 0 (by simp), by simpa using h.sigp 1 (by simp), one_add_isInK _,
    fun hne => h.loop3 (ne_zero_of_one_add hne), one_add_isInK _,
    fun hne => h.loop4 (ne_zero_of_one_add hne)⟩
  · rw [e50]; exact rc _ _ hda (by norm_num)
  · rw [e58]; exact rc _ _ hT (by norm_num)
  · apply mul_inv_cancel₀
    rw [← pow_add, ← pow_add, add_comm]
    exact one_add_gen_pow_ne_zero h0 (by unfold ordG; omega)

set_option maxRecDepth 100000 in
theorem mainS_da_holds {R : MainRun} (h : MainOkS S C rd R) (h0 : mainVal rd R (.n 112) = 0) :
    Stmt.HoldsListB S C rd (mainVal rd R) daBranch True (fun rs => rs = []) := by
  have e : mainVal rd R (.n 112) = gen ^ R.rd + gen := by simp only [mainVal]; b1_look
  have h1 := gen_pow_add_gen_eq_zero h.rd1 (e ▸ h0)
  simp only [daBranch, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil]
  simp only [mainVal]
  b1_look
  simp only [true_and, and_true]
  exact ⟨h.daVerify h1, h.daCover h1, e_add_eq_zero_iff.mpr rfl, e_add_eq_zero_iff.mpr rfl,
    e_add_eq_zero_iff.mpr rfl, e_add_eq_zero_iff.mpr rfl⟩

set_option maxRecDepth 100000 in
theorem mainS_mid_holds {R : MainRun} (h : MainOkS S C rd R) :
    Stmt.HoldsListB S C rd (mainVal rd R) mainMid True (fun rs => rs = []) := by
  simp only [mainMid, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, word_gen,
    word_one]
  simp only [mainVal]
  b1_look
  simp only [true_and, and_true]
  refine ⟨by ring, by ring, by ring, by ring, by ring, by ring, by ring, by ring, by ring, by ring,
    by ring, by ring, by ring, by ring, by ring, by ring, by ring, h.written0, one_add_isInK _,
    fun hne => h.loop5 (ne_zero_of_one_add hne), loadHolds_of_mul0 rfl h.writtenN,
    e_add_eq_zero_iff.mpr rfl⟩

set_option maxRecDepth 100000 in
theorem mainS_leaf_holds {R : MainRun} (h : MainOkS S C rd R) (h0 : mainVal rd R (.n 155) = 0) :
    Stmt.HoldsListB S C rd (mainVal rd R) leafT True (fun rs => rs = []) := by
  have e : mainVal rd R (.n 155) = gen ^ R.nc + 1 := by simp only [mainVal]; b1_look
  have h1 := gen_pow_add_one_eq_zero h.nc (e ▸ h0)
  have hl := h.leaf h1
  rw [leafT, Stmt.HoldsListB, Stmt.HoldsB]
  simp only [holdsListB_append]
  rw [holdsListB_flatten_range 22 (zeroStores 159 0) (fun _ => rfl),
    holdsListB_flatten_range 28 (zeroStores 181 23) (fun _ => rfl)]
  simp only [zeroStores, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, word_zero, and_true, true_and]
  have hs : ∀ k < 53, LoadHolds rd R.dstmt k
      ((List.replicate 22 (0 : E) ++ [R.lbv] ++ List.replicate 28 0 ++ [R.lmA, R.lmB]).getD k 0) :=
    fun k hk => readsAt_getD' hl (by simp; omega)
  have z1 : ∀ k < 22,
      (List.replicate 22 (0 : E) ++ [R.lbv] ++ List.replicate 28 0 ++ [R.lmA, R.lmB]).getD k 0 = 0 := by
    intro k hk
    interval_cases k <;> rfl
  have z2 : ∀ k < 28,
      (List.replicate 22 (0 : E) ++ [R.lbv] ++ List.replicate 28 0 ++ [R.lmA, R.lmB]).getD (23 + k) 0 =
        0 := by
    intro k hk
    interval_cases k <;> rfl
  simp only [mainVal]
  refine ⟨fun k hk => ⟨by b1_look, ?_⟩, ?_, fun k hk => ⟨by b1_look, ?_⟩, ?_, ?_⟩
  · b1_look; rw [← z1 k hk]; exact hs k (by omega)
  · b1_look; exact hs 22 (by omega)
  · b1_look; rw [← z2 k hk]; exact hs _ (by omega)
  · b1_look; exact hs 51 (by omega)
  · b1_look; exact hs 52 (by omega)

set_option maxRecDepth 100000 in
theorem mainS_agg_holds {R : MainRun} (h : MainOkS S C rd R) (h0 : mainVal rd R (.n 155) ≠ 0) :
    Stmt.HoldsListB S C rd (mainVal rd R) aggT True (fun rs => rs = []) := by
  have e : mainVal rd R (.n 155) = gen ^ R.nc + 1 := by simp only [mainVal]; b1_look
  have h1 : R.nc ≠ 0 := fun hz => h0 (by rw [e, hz, pow_zero]; exact e_add_eq_zero_iff.mpr rfl)
  simp only [aggT, Stmt.HoldsListB, Stmt.HoldsB, List.map_cons, List.map_nil, and_true]
  simp only [mainVal]
  b1_look
  exact h.agg h1

set_option maxRecDepth 100000 in
theorem mainS_post_holds {R : MainRun} (h : MainOkS S C rd R) :
    Stmt.HoldsListB S C rd (mainVal rd R) mainPost False (fun rs => rs = []) := by
  simp only [mainPost, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, word_gen,
    word_one]
  simp only [mainVal]
  b1_look
  simp only [true_and, and_true]
  have l1 : LoadHolds rd 1 0 (digestScalars R.stDig).1 := by
    refine ⟨by simpa using gen_pow_isInK 0, ?_⟩
    rw [show (1 : E).limb 0 * Parameters.gpow 0 = 1 by
      rw [← ofK_one, limb_ofK]; simp [Parameters.gpow]]
    exact h.pub0
  have l2 : LoadHolds rd gen 0 (digestScalars R.stDig).2 := by
    refine ⟨by simpa using gen_pow_isInK 1, ?_⟩
    rw [show gen.limb 0 * Parameters.gpow 0 = g by simp [Parameters.gpow, gen_eq_ofK]]
    exact h.pub1
  exact ⟨h.stmt, l1, e_add_eq_zero_iff.mpr rfl, by rw [one_mul]; exact l2, e_add_eq_zero_iff.mpr rfl⟩

set_option maxRecDepth 100000 in
/-- **`main`'s body on its honest valuation.** -/
theorem mainS_body_holds {R : MainRun} (h : MainOkS S C rd R) :
    Stmt.HoldsListB S C rd (mainVal rd R) mainBody False (fun rs => rs = []) := by
  rw [mainBody, holdsListB_append, holdsListB_noRet mainPre rfl, Stmt.HoldsListB,
    holdsS_ite_noRet (.n 112) daBranch [] rfl rfl, holdsListB_append, holdsListB_noRet mainMid rfl,
    show Stmt.HoldsListB S C rd (mainVal rd R) (Stmt.ite (.n 155) leafT aggT :: mainPost)
      False (fun rs => rs = []) = Stmt.HoldsB S C rd (mainVal rd R)
        (Stmt.ite (.n 155) leafT aggT)
        (Stmt.HoldsListB S C rd (mainVal rd R) mainPost False (fun rs => rs = []))
        (fun rs => rs = []) from rfl,
    holdsS_ite_noRet (.n 155) leafT aggT rfl rfl]
  refine ⟨mainS_pre_holds h, ⟨?_, mainS_da_holds h, fun _ => trivial⟩, mainS_mid_holds h,
    ⟨?_, mainS_leaf_holds h, mainS_agg_holds h⟩, mainS_post_holds h⟩
  · have e : mainVal rd R (.n 112) = gen ^ R.rd + gen := by simp only [mainVal]; b1_look
    rw [e]; exact isInK_add (gen_pow_isInK _) (by simpa using gen_pow_isInK 1)
  · have e : mainVal rd R (.n 155) = gen ^ R.nc + 1 := by simp only [mainVal]; b1_look
    rw [e]; exact isInK_add (gen_pow_isInK _) (by simpa using gen_pow_isInK 0)

/-- **`main` holds** once its body's needs hold (`MainOkS`). -/
theorem mainS_rel_of_ok {R : MainRun} (h : MainOkS S (coreProgram.RelB S rd) rd R) :
    coreProgram.RelB S rd "main" [] [] := by
  rw [relS_iff_sem find_main]
  exact ⟨mainVal rd R, rfl, by rw [core0_body]; exact mainS_body_holds h⟩

end
end LeanVM.Guest.B1.Main
