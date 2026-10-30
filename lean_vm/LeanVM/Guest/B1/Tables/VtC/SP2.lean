/-
  LeanVM.Guest.B1.Tables.VtC.SP2

  `verify_tables`' statements `2189 ..< 2404` hold on the honest valuation: `bytecode_val`, the
  six tables' heights and padding weights, `idxc_tab`, `zeta1` and the shared selector tables.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.SPads
public import LeanVM.Guest.B1.Tables.VtC.SShared
public import LeanVM.Guest.B1.Tables.VtC.SSort

/-!
# Statements `2189 ..< 2404` (G:1993-2035)

`forall_slice_blocks`: `k` consecutive blocks of `L` statements. `vtS_p2`: for the bus point
(`|point| = μ < 33`), the tables' heights `τ t = max (log2Ceil (n t)) floor < 29`, `τ t ≤ μ`, on a
memory holding `dims_g`, `table_rows`, the squares, `idxc_tab`, `zeta1` and the shared tables,
the oracle returning `padding_weight`'s outcomes and `plus_one_run`'s `0`, every statement holds;
the padding weights and `shared_len` are the honest ones.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- **`k` blocks of `L` statements from `a`.** -/
theorem forall_slice_blocks {P : Stmt → Prop} (a L : ℕ) (blk : ℕ → List Stmt) :
    ∀ k : ℕ, (∀ i < k, (blk i).length = L) →
      (∀ i < k, tbStmtsEqb (blk i) ((vtPre.drop (a + L * i)).take (blk i).length) = true) →
      (∀ i < k, ∀ s ∈ blk i, P s) → ∀ s ∈ (vtPre.drop a).take (L * k), P s
  | 0, _, _, _ => by simp
  | k + 1, hl, hc, hp => by
    rw [Nat.mul_succ]
    refine forall_slice_split a (L * k) L
      (forall_slice_blocks a L blk k (fun i hi => hl i (by omega)) (fun i hi => hc i (by omega))
        (fun i hi => hp i (by omega))) ?_
    have := forall_slice_of (hc k (by omega)) (hp k (by omega))
    rwa [hl k (by omega)] at this

theorem vtS_p2_checks :
    tbStmtsEqb [.atom (.hint (.witness "bytecode_val" (.stack [.n 2639])))]
      ((vtPre.drop 2189).take 1) = true ∧
    tbStmtsEqb [.atom (.hint (.alloc (.n 2732) 34))] ((vtPre.drop 2257).take 1) = true ∧
    tbStmtsEqb [.atom (.hint (.allocDyn (.n 2767) (.n 9))),
      .dispatch (.n 9) plusOneRunNames [.n 2767, .n 8] [.n 2768],
      .atom (.hint (.alloc (.n 2769) 1728)), .atom (.hint (.alloc (.n 2770) 864))]
      ((vtPre.drop 2326).take 4) = true := by
  decide +kernel

theorem vtPad_reads : ∀ t < 5, ∀ a ∈ [Atom.load (.n (2640 + 14 * t)) (.n 10) (t + 1),
    .load (.n (2640 + 14 * t + 5)) (.n 11) t], a ∉ vtSL := by decide +kernel

theorem vtPad5_reads : ∀ a ∈ [Atom.load (.n 2710) (.n 10) 6, .load (.n (2710 + 5)) (.n 11) 5],
    a ∉ vtSL := by decide +kernel

theorem vtSh_reads : (Atom.load (.n 2771) (.n 10) 1 ∉ vtSL) ∧
    ∀ i < 5, Atom.load (.n (2781 + 14 * i)) (.n 10) (i + 1 + 1) ∉ vtSL := by decide +kernel

theorem vtSh_check' : ∀ i < 5, tbStmtsEqb (vtShT (2781 + 14 * i) (i + 1))
    ((vtPre.drop (2339 + 13 * i)).take (vtShT (2781 + 14 * i) (i + 1)).length) = true := by
  intro i hi
  have := vtSh_check (i + 1) (by omega) (by omega)
  simpa using this

theorem vtPad5T_length : (vtPad5T 2710).length = 12 := rfl

section
variable {rd : Reader} {w : ℕ → E} {args : List E}

theorem vt_hint1 (hl : args.length = 22) (n : ℕ) {d : ℕ} {h : Hint}
    (heq : tbStmtsEqb [.atom (.hint h)] ((vtPre.drop n).take 1) = true)
    (hh : GoodS rd vtSL w (vtσ rd w args) (fixNe (.atom (.hint h))) → vtσ rd w args (.n d) = w d) :
    vtσ rd w args (.n d) = w d :=
  hh (vt_goodS hl (vt_mem_slice (blk := [_]) heq List.mem_cons_self))

set_option maxHeartbeats 4000000 in
/-- **Statements `2189 ..< 2404`.** -/
theorem vtS_p2 (hl : args.length = 22) (hlow : LowDefB 8 rd) (point : List E)
    (hμ33 : point.length < 33) (τ n : ℕ → ℕ)
    (hτ : ∀ t < 6, τ t = max (log2Ceil (n t)) (tableLogFloors.getD t 0))
    (hτ29 : ∀ t < 6, τ t < 29) (hτμ : ∀ t < 6, τ t ≤ point.length)
    (hz : TbReadsAt rd (args.getD 8 0) point) (h9 : args.getD 9 0 = gen ^ point.length)
    (hdims : ∀ t < 6, LoadHolds rd (args.getD 10 0) (t + 1) (gen ^ τ t))
    (hrows : ∀ t < 6, LoadHolds rd (args.getD 11 0) t (eOfNat (n t)))
    (hsq : TbReadsAt rd (args.getD 13 0) gSquaresList)
    (hwp : ∀ t < 6, w (vtPadV t) = paddingWeight (point.take (τ t)) (n t) ∧
      w (vtPadV t + 1) = PadLead (τ t) (n t) ∧ w (vtPadV t + 2) = PadRest (τ t) (n t))
    (hidxc : TbReadsAt rd (w 2732) vtIdxcW) (hz1 : TbReadsAt rd (w 2767) (point.map (1 + ·)))
    (hw2768 : w 2768 = 0)
    (hrun : ∀ t < 6, RunTables rd (w 2769 * gen ^ (288 * t)) (w 2770 * gen ^ (144 * t))
      (point.length - τ t) (point.drop (τ t)) ((point.map (1 + ·)).drop (τ t))
      ((gSquaresList.drop (τ t)).take (point.length - τ t))) :
    (∀ s ∈ (vtPre.drop 2189).take 215, VSH (coreProgram.Rel rd) rd (vtσ rd w args) s) ∧
      (∀ t < 6, vtσ rd w args (.n (vtPadV t)) = paddingWeight (point.take (τ t)) (n t)) ∧
      (∀ t < 6, vtσ rd w args (.n (vtShLen t)) = gen ^ (point.length - τ t)) ∧
      vtσ rd w args (.n 2639) = w 2639 ∧ vtσ rd w args (.n 2732) = w 2732 ∧
      vtσ rd w args (.n 2767) = w 2767 ∧ vtσ rd w args (.n 2769) = w 2769 ∧
      vtσ rd w args (.n 2770) = w 2770 := by
  obtain ⟨c1, c2, c3⟩ := vtS_p2_checks
  have e8 : vtσ rd w args (.n 8) = args.getD 8 0 := vt_param hl (by norm_num)
  have e9 : vtσ rd w args (.n 9) = gen ^ point.length := by rw [vt_param hl (by norm_num), h9]
  have e10 : vtσ rd w args (.n 10) = args.getD 10 0 := vt_param hl (by norm_num)
  have e11 : vtσ rd w args (.n 11) = args.getD 11 0 := vt_param hl (by norm_num)
  have e13 : vtσ rd w args (.n 13) = args.getD 13 0 := vt_param hl (by norm_num)
  have e2639 : vtσ rd w args (.n 2639) = w 2639 := vt_hint1 hl 2189 c1 (fun h => by
    simpa [fixNe, GoodS, Good] using h)
  have e2732 : vtσ rd w args (.n 2732) = w 2732 := vt_alloc hl 2257 c2
  have g3 := vt_goodL (rd := rd) (w := w) hl 2326 _ c3
  simp only [GoodL, GoodS, fixNe, Good, and_true] at g3
  obtain ⟨e2767, -, e2769, e2770⟩ := g3
  have hz' : TbReadsAt rd (vtσ rd w args (.n 8)) point := by rw [e8]; exact hz
  have hsq' : TbReadsAt rd (vtσ rd w args (.n 13)) gSquaresList := by rw [e13]; exact hsq
  have hz1' : TbReadsAt rd (vtσ rd w args (.n 2767)) (point.map (1 + ·)) := by rw [e2767]; exact hz1
  -- the pads
  have hpad : ∀ t < 5, (∀ st ∈ vtPadT (2640 + 14 * t) t,
      VSH (coreProgram.Rel rd) rd (vtσ rd w args) st) ∧
      vtσ rd w args (.n (2640 + 14 * t + 6)) = paddingWeight (point.take (τ t)) (n t) := by
    intro t ht
    have hf : tableLogFloors.getD t 0 = 0 := by interval_cases t <;> rfl
    have hτt := hτ t (by omega)
    rw [hf] at hτt
    obtain ⟨w6, w7, w8⟩ := hwp t (by omega)
    rw [show vtPadV t = 2640 + 14 * t + 6 by unfold vtPadV; ring] at w6 w7 w8
    exact pad_ok hlow (vt_goodL hl _ _ (vtPad_check t ht)) (vtPad_reads t ht)
      (by rw [e10]; exact hdims t (by omega)) (by rw [e11]; exact hrows t (by omega))
      (tbReadsAt_take hz' (τ t)) (by simp; exact hτμ t (by omega)) (hτ29 t (by omega))
      (by omega) w6 w7 (by rw [show 2640 + 14 * t + 8 = 2640 + 14 * t + 6 + 2 by ring]; exact w8)
  have hpad5 : (∀ st ∈ vtPad5T 2710, VSH (coreProgram.Rel rd) rd (vtσ rd w args) st) ∧
      vtσ rd w args (.n (2710 + 6)) = paddingWeight (point.take (τ 5)) (n 5) := by
    obtain ⟨w6, w7, w8⟩ := hwp 5 (by norm_num)
    have hm : Stmt.ite (.n (2710 + 16)) [] [.atom (.const (.n (2710 + 17)) (word 1 0 0)),
      .atom (.assertEq (.n (2710 + 7)) (.n (2710 + 17))),
      .atom (.const (.n (2710 + 18)) (word 0 0 0)),
      .atom (.add (.n (2710 + 19)) (.n (2710 + 8)) (.n (2710 + 18))),
      .atom (.hint (.inverse (.n (2710 + 19)) (.n (2710 + 20)))),
      .atom (.assertNe (.n (2710 + 19)) (.n (2710 + 20)) (.n (2710 + 21)))] ∈ vtPre :=
      vt_mem_slice vtPad5_check (by simp [vtPad5T])
    have hgb := vt_goodIte' (rd := rd) (w := w) hl hm
    rw [List.nil_append] at hgb
    exact pad5_ok hlow (vt_goodL hl _ _ vtPad5_check) hgb vtPad5_reads
      (by rw [e10]; exact hdims 5 (by norm_num)) (by rw [e11]; exact hrows 5 (by norm_num))
      (tbReadsAt_take hz' (τ 5)) (by simp; exact hτμ 5 (by norm_num)) (hτ29 5 (by norm_num))
      (hτ 5 (by norm_num)) w6 w7 w8
  -- the shared tables
  have hsh0 := sh0_ok (rd := rd) (w := w) hlow (μ := point.length) (τ := τ 0) (point := point)
    (vt_goodL hl _ _ vtSh0_check) vtSh_reads.1 (by rw [e10]; exact hdims 0 (by norm_num)) e9 rfl
    hμ33 (hτμ 0 (by norm_num)) hz' hz1' hsq'
    (by rw [e2769, e2770]; simpa using hrun 0 (by norm_num))
  have hsh : ∀ i < 5, (∀ st ∈ vtShT (2781 + 14 * i) (i + 1),
      VSH (coreProgram.Rel rd) rd (vtσ rd w args) st) ∧
      vtσ rd w args (.n (2781 + 14 * i + 2)) = gen ^ (point.length - τ (i + 1)) := fun i hi =>
    sh_ok hlow (by omega) (by omega) (vt_goodL hl _ _ (vtSh_check' i hi)) (vtSh_reads.2 i hi)
      (by rw [e10]; exact hdims (i + 1) (by omega)) e9 rfl hμ33 (hτμ (i + 1) (by omega)) hz' hz1'
      hsq' (by rw [e2769, e2770]; exact hrun (i + 1) (by omega))
  refine ⟨?_, ?_, ?_, e2639, e2732, e2767, e2769, e2770⟩
  · refine forall_slice_split 2189 1 214 ?_ ?_
    · rw [show (1 : ℕ) = [Stmt.atom (.hint (.witness "bytecode_val" (.stack [.n 2639])))].length
        from rfl]
      refine forall_slice_of c1 ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]
      trivial
    refine forall_slice_split 2190 55 159
      (forall_slice_blocks (P := VSH (coreProgram.Rel rd) rd (vtσ rd w args)) 2190 11
        (fun t => vtPadT (2640 + 14 * t) t) 5 (fun _ _ => rfl) (fun t ht => vtPad_check t ht)
        (fun t ht => (hpad t ht).1)) ?_
    refine forall_slice_split 2245 12 147 ?_ ?_
    · rw [← vtPad5T_length]; exact forall_slice_of vtPad5_check hpad5.1
    refine forall_slice_split 2257 1 146 ?_ ?_
    · rw [show (1 : ℕ) = [Stmt.atom (.hint (.alloc (.n 2732) 34))].length from rfl]
      refine forall_slice_of c2 ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]
      trivial
    refine forall_slice_split 2258 68 78 ?_ ?_
    · rw [← vtIdxcT_length]
      exact forall_slice_of vtIdxc_check (idxc_ok hl (by rw [e2732]; exact hidxc))
    refine forall_slice_split 2326 4 74 ?_ ?_
    · rw [show (4 : ℕ) = [Stmt.atom (.hint (.allocDyn (.n 2767) (.n 9))),
        .dispatch (.n 9) plusOneRunNames [.n 2767, .n 8] [.n 2768],
        .atom (.hint (.alloc (.n 2769) 1728)), .atom (.hint (.alloc (.n 2770) 864))].length
        from rfl]
      refine forall_slice_of c3 ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨trivial, zeta1_ok hl e9 (by omega) hz' hz1' hw2768, trivial, trivial⟩
    refine forall_slice_split 2330 9 65 ?_ ?_
    · rw [show (9 : ℕ) = vtSh0T.length from rfl]; exact forall_slice_of vtSh0_check hsh0.1
    · exact forall_slice_blocks 2339 13 (fun i => vtShT (2781 + 14 * i) (i + 1)) 5
        (fun _ _ => rfl) (fun i hi => vtSh_check' i hi) (fun i hi => (hsh i hi).1)
  · intro t ht
    rcases Nat.lt_or_ge t 5 with h5 | h5
    · rw [show vtPadV t = 2640 + 14 * t + 6 by unfold vtPadV; ring]; exact (hpad t h5).2
    · obtain rfl : t = 5 := by omega
      exact hpad5.2
  · intro t ht
    rcases Nat.eq_zero_or_pos t with rfl | ht0
    · exact hsh0.2
    · obtain ⟨i, rfl⟩ : ∃ i, t = i + 1 := ⟨t - 1, by omega⟩
      have := (hsh i (by omega)).2
      simpa [vtShLen] using this

end

end
end LeanVM.Guest.B1.Tables
