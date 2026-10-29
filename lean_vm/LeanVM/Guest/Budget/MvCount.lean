/-
  LeanVM.Guest.Budget.MvCount

  `main`'s `da_verify` and `claim_list_digest`, their instructions per opcode by their trees'
  shapes (B1's `Da.dvNH`, `Main.clHonest`): each callee by its static count from the `V` count
  certificates (`Count/MvCountData`), each loop by its iterations.
-/

module

public import LeanVM.Guest.Count.MvCountChkX
public import LeanVM.Guest.Count.MvCountChkM
public import LeanVM.Guest.Count.MvCountChkS
public import LeanVM.Guest.Count.MvCountChkD
public import LeanVM.Guest.Count.MvCountChkJ
public import LeanVM.Guest.Count.MvCountChkK
public import LeanVM.Guest.Budget.VsCount
public import LeanVM.Guest.Budget.MainCount
public import LeanVM.Guest.Count.Static
public import LeanVM.Guest.B1.Da.VerifyAtT
public import LeanVM.Guest.B1.Main.MainGoalsClT

/-!
# `da_verify`'s and the claim lists' instructions

`colW op i r L`: a column's instructions of `op` on `r` rows padded to `2^L` (`i = 0` for
`da_verify_column__L1`, `1` for `__L0`): its frame's weight, the vector cell's, its row loop's `r`
iterations, its padding loop's `2^L - r`, the DA levels at `L` (`col_weight_le`, on a tree of
`Da.colNH`). `colFrom_weight_le`: a column loop's `n` iterations, each its frame and a column.
`dvW op r L`: `da_verify`'s, its frame, its static callees, its row loops' `r` iterations, its two
column loops' 64 columns each, `__loop23`'s `2^L - r` and the levels at `L` (`dv_weight_le`, on a
tree of `Da.dvNH r L`); `dvW_le`: within `kcDvA op + kcDvR op · r + kcDvP op · 2^L`.
`clW op n`: `claim_list_digest`'s on `n` claims, its frame's, `list_split`'s, `n / 17` iterations
of `__loop15` and the last group's `claim_list_last__L{n % 17}` (`cl_weight_le`, on a tree of
`Main.clHonest n`); `clW_le`: within `kcClA op + kcClS op · n`. `Count.mainCounts op`: `main`'s callees' weights at
`op`'s instructions, the static ones' certificates and these two by their shapes.
-/

namespace LeanVM.Guest.Budget

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest
open LeanVM.Guest.Count
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

theorem mvTab_ok (op : Opcode) : mvTabOk op = true := by
  cases op
  · exact mvTab_ok_x
  · exact mvTab_ok_m
  · exact mvTab_ok_s
  · exact mvTab_ok_d
  · exact mvTab_ok_j
  · exact mvTab_ok_k

theorem mvTab_parts (op : Opcode) :
    (∀ i < 3, (kvOkB op (dvStJ.getD i 0) (dvStNames.getD i "") &&
      kvSBJ op (dvStJ.getD i 0) == (kcDvStT op).getD i 0) = true) ∧
    (∀ i < 9, (kvOkK op (dvLpJ.getD i 0) (dvLpNames.getD i "") &&
      kvSKJ op (dvLpJ.getD i 0) == (kcDvLpT op).getD i 0) = true) ∧
    (∀ L < 11, (kvOkB op (dlJ.getD L 0) (B1.Da.dlNames.getD L "") &&
      kvSBJ op (dlJ.getD L 0) == (kcDlT op).getD L 0) = true) ∧
    (∀ k < 17, (kvOkB op (clJ.getD k 0) (B1.Digest.clNames.getD k "") &&
      kvSBJ op (clJ.getD k 0) == (kcClT op).getD k 0) = true) ∧
    (kvOkK op l16J "__loop15" && kvSKJ op l16J == kcL16 op) = true ∧
    (∀ i < 6, decide ((coreProgram[mvOmJ.getD i 0]?).map Fn.name = some (mvOmNames.getD i "")) = true ∧
      (B2C.plumbOf (mvOmJ.getD i 0 + 1)).pmax.getD (B2C.opIdx op) 0 = (mvOmT op).getD i 0) := by
  have h := mvTab_ok op
  simp only [mvTabOk, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5a⟩, h5b⟩, h6⟩ := h
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun L hL => ?_, fun k hk => ?_, ?_, fun i hi => h6 i hi⟩
  · have := h1 i hi; simp only [Bool.and_eq_true, beq_iff_eq]; exact this
  · have := h2 i hi; simp only [Bool.and_eq_true, beq_iff_eq]; exact this
  · have := h3 L hL; simp only [Bool.and_eq_true, beq_iff_eq]; exact this
  · have := h4 k hk; simp only [Bool.and_eq_true, beq_iff_eq]; exact this
  · simp only [Bool.and_eq_true, beq_iff_eq]; exact ⟨h5a, h5b⟩

variable (op : Opcode)

/-- **`da_verify`'s static callees** but the levels by `L`. -/
theorem dvSt_weightLe {i : ℕ} (hi : i < 3) :
    WeightLe coreProgram (B2C.ωArm B2C.xmssArmC op) (dvStNames.getD i "")
      fun _ => (kcDvStT op).getD i 0 :=
  weightLe_tab ((mvTab_parts op).1 i hi)

/-- **`da_verify`'s and its columns' loops, per iteration.** -/
theorem dvLp_loop {i : ℕ} (hi : i < 9) :
    LoopWeightLe (B2C.ωArm B2C.xmssArmC op) (dvLpNames.getD i "") ((kcDvLpT op).getD i 0) :=
  loopWeightLe_tab ((mvTab_parts op).2.1 i hi)

/-- **The DA levels at `L`.** -/
theorem dl_weightLe {L : ℕ} (hL : L < 11) :
    WeightLe coreProgram (B2C.ωArm B2C.xmssArmC op) (B1.Da.dlNames.getD L "")
      fun _ => (kcDlT op).getD L 0 :=
  weightLe_tab ((mvTab_parts op).2.2.1 L hL)

/-- **`claim_list_last__L{k}`.** -/
theorem cl_weightLe {k : ℕ} (hk : k < 17) :
    WeightLe coreProgram (B2C.ωArm B2C.xmssArmC op) (B1.Digest.clNames.getD k "")
      fun _ => (kcClT op).getD k 0 :=
  weightLe_tab ((mvTab_parts op).2.2.2.1 k hk)

/-- **`__loop15`, per iteration.** -/
theorem l16_loop : LoopWeightLe (B2C.ωArm B2C.xmssArmC op) "__loop15" (kcL16 op) :=
  loopWeightLe_tab (mvTab_parts op).2.2.2.2.1

/-- **The frame weights** of `mvOmNames`. -/
theorem mvOm_eq {i : ℕ} (hi : i < 6) :
    B2C.ωArm B2C.xmssArmC op (mvOmNames.getD i "") = (mvOmT op).getD i 0 := by
  obtain ⟨hn, hv⟩ := (mvTab_parts op).2.2.2.2.2 i hi
  rw [ωArm_idx (decide_eq_true_eq.mp hn) (by interval_cases i <;> decide), hv]

theorem dlNames_bang {L : ℕ} (hL : L < 11) : B1.Da.dlNames[L]! = B1.Da.dlNames.getD L "" := by
  interval_cases L <;> decide

theorem clNames_bang {k : ℕ} (hk : k < 17) :
    B1.Digest.clNames[k]! = B1.Digest.clNames.getD k "" := by
  interval_cases k <;> decide

theorem clNames_ne {k : ℕ} (hk : k < 17) :
    B1.Digest.clNames[k]! ≠ "list_split" ∧ B1.Digest.clNames[k]! ≠ "__loop15" := by
  interval_cases k <;> decide

/-- A loop of `r` iterations from the counter `1`, at most `r` per-iteration counts. -/
theorem loop_at {ω : String → ℕ} {f : String} {K : ℕ} (hL : LoopWeightLe ω f K) {rd : Reader}
    {t : Tree} {args rets : List E} {r : ℕ} (hn : t.name = f) (hv : t.Valid coreProgram rd args rets)
    (hb : t.BufsOk coreProgram) (h0 : args.getD 0 0 = 1) (h1 : args.getD 1 0 = gen ^ r)
    (hr : 0 < r) (hr64 : r < 2 ^ 64 - 1) : t.weight ω ≤ r * K := by
  have := hL rd t args rets 0 r hn hv hb (by rw [h0, one_eq_ofK])
    (by rw [h1, Value.gen_pow_eq_ofK]) hr hr64
  simpa using this

/-! ## A column and a column loop -/

/-- **A column's instructions** on `r` rows padded to `2^L`, its frame `ωc`, its row loop's and
padding loop's `Kr`, `Kg` per iteration. -/
def colW (ωc Kr Kg r L : ℕ) : ℕ :=
  ωc + (kcDvStT op).getD 1 0 + r * Kr + (2 ^ L - r) * Kg + (kcDlT op).getD L 0

set_option maxHeartbeats 1000000 in
/-- **A column's instructions** on a tree of its honest shape. -/
theorem col_weight_le {fname rl gl : String} {Kr Kg r L : ℕ}
    (hlr : LoopWeightLe (B2C.ωArm B2C.xmssArmC op) rl Kr)
    (hlg : LoopWeightLe (B2C.ωArm B2C.xmssArmC op) gl Kg) (hr : 0 < r) (hrL : r ≤ 2 ^ L)
    (hL : L < 11) {rd : Reader} {t : Tree} {args rets : List E}
    (h : B1.Da.colNH fname rl gl r L t) (hv : t.Valid coreProgram rd args rets)
    (hb : t.BufsOk coreProgram) :
    t.weight (B2C.ωArm B2C.xmssArmC op) ≤
      colW op (B2C.ωArm B2C.xmssArmC op fname) Kr Kg r L := by
  obtain ⟨σ, ks, rfl, ⟨h1, h3, -, h17, h20⟩, hc, hl, hT⟩ := h
  obtain ⟨hk, hbk⟩ := node_kids hv hb hc
  have h2L : 2 ^ L < 2 ^ 11 := Nat.pow_lt_pow_right (by norm_num) hL
  have hk' := kids_weight_leL (B2C.ωArm B2C.xmssArmC op) (B1.Da.colCalls rl gl r L)
    (List.replicate 4 fun _ => True)
    [(kcDvStT op).getD 1 0, r * Kr, (2 ^ L - r) * Kg, (kcDlT op).getD L 0] ks hk hbk hT
    (by simp [B1.Da.colCalls]) (by simp [B1.Da.colCalls])
    (fun i hi _ _ ht t' rets' hn hv' hb' _ => by
      have hi4 : i < 4 := by simpa [B1.Da.colCalls] using hi
      interval_cases i <;>
        simp only [B1.Da.colCalls, List.getElem_cons_zero, List.getElem_cons_succ,
          List.getElem_cons_zero] at ht hn hv' ⊢
      · exact dvSt_weightLe op (i := 1) (by norm_num) rd t' _ rets' hn hv' hb'
      · exact loop_at hlr hn hv' hb' (by simp [h17]) (by simp [h1]) hr (by omega)
      · have hg : 2 ^ L - r ≠ 0 := by simpa using ht
        exact loop_at hlg hn hv' hb' (by simp [h20]) (by simp [h3]) (by omega) (by omega)
      · rw [dlNames_bang hL] at hn
        exact dl_weightLe op hL rd t' _ rets' hn hv' hb')
  rw [Tree.weight]
  simp only [List.sum_cons, List.sum_nil] at hk'
  unfold colW
  omega

/-- **A column loop's `n` iterations** weigh at most `n` times its frame and a column's bound. -/
theorem colFrom_weight_le {f col : String} {m : ℕ} {Tc : Tree → Prop} {Kc : ℕ}
    (hc : ∀ (rd : Reader) (t : Tree) (args rets : List E), Tc t → t.Valid coreProgram rd args rets →
      t.BufsOk coreProgram → t.weight (B2C.ωArm B2C.xmssArmC op) ≤ Kc) :
    ∀ (n k : ℕ) (rd : Reader) (t : Tree) (args rets : List E), B1.Da.colFrom f col m Tc n k t →
      t.Valid coreProgram rd args rets → t.BufsOk coreProgram →
        t.weight (B2C.ωArm B2C.xmssArmC op) ≤ n * (B2C.ωArm B2C.xmssArmC op f + Kc)
  | 0, _, _, _, _, _, h, _, _ => h.elim
  | n + 1, k, rd, t, args, rets, h, hv, hb => by
    obtain ⟨σ, ks, rfl, -, hcl, hl, hT⟩ := h
    obtain ⟨hk, hbk⟩ := node_kids hv hb hcl
    have hk' := kids_weight_leL (B2C.ωArm B2C.xmssArmC op) (B1.Da.colLoopCalls col f k m)
      [Tc, B1.Da.colFrom f col m Tc n (k + 1)] [Kc, n * (B2C.ωArm B2C.xmssArmC op f + Kc)] ks hk
      hbk hT (by simp [B1.Da.colLoopCalls]) (by simp [B1.Da.colLoopCalls])
      (fun i hi _ _ _ t' rets' _ hv' hb' hT' => by
        have hi2 : i < 2 := by simpa [B1.Da.colLoopCalls] using hi
        interval_cases i <;>
          simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hT' ⊢
        · exact hc rd t' _ rets' hT' hv' hb'
        · exact colFrom_weight_le hc n (k + 1) rd t' _ rets' hT' hv' hb')
    rw [Tree.weight]
    simp only [List.sum_cons, List.sum_nil] at hk'
    rw [Nat.succ_mul]
    omega

/-! ## `da_verify` -/

/-- **`da_verify`'s instructions of `op`** on `r` rows padded to `2^L`. -/
def dvW (r L : ℕ) : ℕ :=
  (mvOmT op).getD 0 0 + (kcDvStT op).getD 0 0 + r * (kcDvLpT op).getD 0 0 +
    r * (kcDvLpT op).getD 1 0 +
    64 * ((mvOmT op).getD 1 0 +
      colW op ((mvOmT op).getD 3 0) ((kcDvLpT op).getD 5 0) ((kcDvLpT op).getD 6 0) r L) +
    64 * ((mvOmT op).getD 2 0 +
      colW op ((mvOmT op).getD 4 0) ((kcDvLpT op).getD 7 0) ((kcDvLpT op).getD 8 0) r L) +
    r * (kcDvLpT op).getD 2 0 + (kcDvStT op).getD 2 0 + r * (kcDvLpT op).getD 3 0 +
    (2 ^ L - r) * (kcDvLpT op).getD 4 0 + (kcDlT op).getD L 0

/-- A column loop of `da_verify`, its 64 columns. -/
theorem dvCol_weight_le {f col rl gl : String} {jf jc jr jg : ℕ} {r L m k : ℕ}
    (hf : mvOmNames.getD jf "" = f) (hjf : jf < 6) (hc : mvOmNames.getD jc "" = col) (hjc : jc < 6)
    (hrl : dvLpNames.getD jr "" = rl) (hjr : jr < 9) (hgl : dvLpNames.getD jg "" = gl)
    (hjg : jg < 9) (hr : 0 < r) (hrL : r ≤ 2 ^ L) (hL : L < 11) {rd : Reader} {t : Tree}
    {args rets : List E} (h : B1.Da.colFrom f col m (B1.Da.colNH col rl gl r L) 64 k t)
    (hv : t.Valid coreProgram rd args rets) (hb : t.BufsOk coreProgram) :
    t.weight (B2C.ωArm B2C.xmssArmC op) ≤ 64 * ((mvOmT op).getD jf 0 +
      colW op ((mvOmT op).getD jc 0) ((kcDvLpT op).getD jr 0) ((kcDvLpT op).getD jg 0) r L) := by
  have hcw := fun (rd : Reader) (t : Tree) (args rets : List E) (hT : B1.Da.colNH col rl gl r L t)
      (hv : t.Valid coreProgram rd args rets) (hb : t.BufsOk coreProgram) =>
    col_weight_le op (hrl ▸ dvLp_loop op hjr) (hgl ▸ dvLp_loop op hjg) hr hrL hL hT hv hb
  have := colFrom_weight_le op hcw 64 k rd t args rets h hv hb
  rw [← hf, ← hc, mvOm_eq op hjf, mvOm_eq op hjc] at this
  exact this

set_option maxHeartbeats 4000000 in
/-- **`da_verify`'s instructions of `op`** on a tree of its honest shape `Da.dvNH r L`. -/
theorem dv_weight_le {r L : ℕ} (hr : 0 < r) (hrL : r ≤ 2 ^ L) (hL : L < 11) {rd : Reader}
    {t : Tree} {args rets : List E} (h : B1.Da.dvNH r L t) (hv : t.Valid coreProgram rd args rets)
    (hb : t.BufsOk coreProgram) : t.weight (B2C.ωArm B2C.xmssArmC op) ≤ dvW op r L := by
  obtain ⟨σ, ks, rfl, ⟨h1, -, -, h4, -, -, -, h16, h30, h36, h44, h47⟩, hc, hl, hT⟩ := h
  obtain ⟨hk, hbk⟩ := node_kids hv hb hc
  have h2L : 2 ^ L < 2 ^ 11 := Nat.pow_lt_pow_right (by norm_num) hL
  have hk' := kids_weight_leL (B2C.ωArm B2C.xmssArmC op) (B1.Da.dvCallList r L) (B1.Da.dvTs r L)
    [(kcDvStT op).getD 0 0, r * (kcDvLpT op).getD 0 0, r * (kcDvLpT op).getD 1 0,
      64 * ((mvOmT op).getD 1 0 +
        colW op ((mvOmT op).getD 3 0) ((kcDvLpT op).getD 5 0) ((kcDvLpT op).getD 6 0) r L),
      64 * ((mvOmT op).getD 2 0 +
        colW op ((mvOmT op).getD 4 0) ((kcDvLpT op).getD 7 0) ((kcDvLpT op).getD 8 0) r L),
      r * (kcDvLpT op).getD 2 0, (kcDvStT op).getD 2 0, r * (kcDvLpT op).getD 3 0,
      (2 ^ L - r) * (kcDvLpT op).getD 4 0, (kcDlT op).getD L 0] ks hk hbk hT
    (by simp [B1.Da.dvCallList, B1.Da.dvTs]) (by simp [B1.Da.dvCallList])
    (fun i hi _ _ ht t' rets' hn hv' hb' hT' => by
      have hi10 : i < 10 := by simpa [B1.Da.dvCallList] using hi
      interval_cases i <;>
        simp only [B1.Da.dvCallList, B1.Da.dvTs, List.getElem_cons_zero,
          List.getElem_cons_succ] at ht hn hv' hT' ⊢
      · exact dvSt_weightLe op (i := 0) (by norm_num) rd t' _ rets' hn hv' hb'
      · exact loop_at (dvLp_loop op (i := 0) (by norm_num)) hn hv' hb' (by simp [h16])
          (by simp [h1]) hr (by omega)
      · exact loop_at (dvLp_loop op (i := 1) (by norm_num)) hn hv' hb' (by simp [h30])
          (by simp [h1]) hr (by omega)
      · exact dvCol_weight_le op (jf := 1) (jc := 3) (jr := 5) (jg := 6) rfl (by norm_num) rfl
          (by norm_num) rfl (by norm_num) rfl (by norm_num) hr hrL hL hT' hv' hb'
      · exact dvCol_weight_le op (jf := 2) (jc := 4) (jr := 7) (jg := 8) rfl (by norm_num) rfl
          (by norm_num) rfl (by norm_num) rfl (by norm_num) hr hrL hL hT' hv' hb'
      · exact loop_at (dvLp_loop op (i := 2) (by norm_num)) hn hv' hb' (by simp [h36])
          (by simp [h1]) hr (by omega)
      · exact dvSt_weightLe op (i := 2) (by norm_num) rd t' _ rets' hn hv' hb'
      · exact loop_at (dvLp_loop op (i := 3) (by norm_num)) hn hv' hb' (by simp [h44])
          (by simp [h1]) hr (by omega)
      · have hg : 2 ^ L - r ≠ 0 := by simpa using ht
        exact loop_at (dvLp_loop op (i := 4) (by norm_num)) hn hv' hb' (by simp [h47])
          (by simp [h4]) (by omega) (by omega)
      · rw [dlNames_bang hL] at hn
        exact dl_weightLe op hL rd t' _ rets' hn hv' hb')
  have hom := mvOm_eq op (i := 0) (by norm_num)
  rw [Tree.weight]
  simp only [List.sum_cons, List.sum_nil] at hk'
  rw [show B2C.ωArm B2C.xmssArmC op "da_verify" = (mvOmT op).getD 0 0 from hom]
  unfold dvW
  omega

set_option maxHeartbeats 4000000 in
/-- **`da_verify`'s instructions on `r` rows padded to `2^L`** within
`kcDvA op + kcDvR op · r + kcDvP op · 2^L`. -/
theorem dvW_le {r L : ℕ} (hlo : r ≤ 2 ^ L) (hL : L < 11) :
    dvW op r L ≤ kcDvA op + kcDvR op * r + kcDvP op * 2 ^ L := by
  unfold dvW colW
  cases op <;> interval_cases L <;>
    simp only [mvOmT, kcDvStT, kcDvLpT, kcDlT, kcDvA, kcDvR, kcDvP, List.getD_cons_zero,
      List.getD_cons_succ, Nat.reducePow] at hlo ⊢ <;> omega

/-! ## The claim lists -/

/-- **`claim_list_digest`'s instructions of `op` on `n` claims.** -/
def clW (n : ℕ) : ℕ :=
  (mvOmT op).getD 5 0 + (if n = 0 then 0 else kcLs op + n / 17 * kcL16 op + (kcClT op).getD (n % 17) 0)

set_option maxHeartbeats 1000000 in
/-- **`claim_list_digest`'s instructions** on a tree of honest shape. -/
theorem cl_weight_le {n : ℕ} (hn : n / 17 < 2 ^ 64 - 1) {rd : Reader} {t : Tree}
    {args rets : List E} (h : B1.Main.clHonest n t) (hv : t.Valid coreProgram rd args rets)
    (hb : t.BufsOk coreProgram) : t.weight (B2C.ωArm B2C.xmssArmC op) ≤ clW op n := by
  let W : Call → ℕ := fun c =>
    if c.f = "list_split" then kcLs op
    else if c.f = "__loop15" then n / 17 * kcL16 op else (kcClT op).getD (n % 17) 0
  obtain ⟨σ, hQ, hle⟩ := NodeHonest.weight_le (B2C.ωArm B2C.xmssArmC op) (fun _ => W) h hv hb
    (by
      intro σ hQ c T hmem ht t' rets' hn' hv' hb' _
      by_cases h0 : n = 0
      · simp [B1.Digest.clCalls, h0] at hmem
      obtain ⟨-, h23, -, -, h48⟩ := And.intro hQ.1 (hQ.2 h0)
      simp only [B1.Digest.clCalls, h0, ↓reduceIte, B1.Digest.clTs, List.zip_cons_cons,
        List.zip_nil_right, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp only [W, ↓reduceIte]
        exact ls_weightLe op rd t' _ rets' hn' hv' hb'
      · simp only [W, String.reduceEq, ↓reduceIte]
        have hq : n / 17 ≠ 0 := by simpa using ht
        exact loop_at (l16_loop op) hn' hv' hb' (by simp [h48]) (by simp [h23]) (by omega) hn
      · have hk : n % 17 < 17 := Nat.mod_lt _ (by norm_num)
        obtain ⟨e1, e2⟩ := clNames_ne hk
        simp only [W, e1, e2, ↓reduceIte]
        rw [clNames_bang hk] at hn'
        exact cl_weightLe op hk rd t' _ rets' hn' hv' hb')
  have hom := mvOm_eq op (i := 5) (by norm_num)
  simp only [mvOmNames, List.getD_cons_succ, List.getD_cons_zero] at hom
  rw [hom] at hle
  unfold clW
  by_cases h0 : n = 0
  · have hc : callsW W (B1.Digest.clCalls n σ) = 0 := by simp [callsW, B1.Digest.clCalls, h0]
    simp only [h0, ↓reduceIte]
    omega
  · have hc : callsW W (B1.Digest.clCalls n σ) ≤
        kcLs op + n / 17 * kcL16 op + (kcClT op).getD (n % 17) 0 := by
      have hk := Nat.mod_lt n (show 0 < 17 by norm_num)
      obtain ⟨e1, e2⟩ := clNames_ne hk
      simp only [callsW, B1.Digest.clCalls, h0, ↓reduceIte, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, W, String.reduceEq, e1, e2]
      clear hle
      generalize n / 17 * kcL16 op = P
      split <;> omega
    simp only [h0, ↓reduceIte]
    omega

theorem kcClA_eq : kcClA op = (mvOmT op).getD 5 0 + kcLs op + (kcClT op).foldl max 0 := by
  cases op <;> decide

theorem kcClS_eq : kcClS op = (kcL16 op + 16) / 17 := by
  cases op <;> decide

/-- **`claim_list_digest`'s instructions** within `kcClA op + kcClS op · n`. -/
theorem clW_le (n : ℕ) : clW op n ≤ kcClA op + kcClS op * n := by
  rw [kcClA_eq, kcClS_eq]
  unfold clW
  split
  · omega
  · have hk : (kcClT op).getD (n % 17) 0 ≤ (kcClT op).foldl max 0 := by
      cases op <;> (have : n % 17 < 17 := Nat.mod_lt _ (by norm_num); interval_cases (n % 17) <;> decide)
    have hq : n / 17 * kcL16 op ≤ (kcL16 op + 16) / 17 * n := by
      have h1 : kcL16 op ≤ 17 * ((kcL16 op + 16) / 17) := by omega
      have h2 : 17 * (n / 17) ≤ n := Nat.mul_div_le n 17
      calc n / 17 * kcL16 op ≤ n / 17 * (17 * ((kcL16 op + 16) / 17)) := Nat.mul_le_mul_left _ h1
        _ = 17 * (n / 17) * ((kcL16 op + 16) / 17) := by ring
        _ ≤ n * ((kcL16 op + 16) / 17) := Nat.mul_le_mul_right _ h2
        _ = (kcL16 op + 16) / 17 * n := Nat.mul_comm _ _
    omega

end
end LeanVM.Guest.Budget

namespace LeanVM.Guest.Count

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest

@[expose] public section

/-- **The weights of `main`'s callees at `op`'s instructions**: the static ones' certificates,
the claim lists and `da_verify` by their trees' shapes (`Budget.clW_le`, `Budget.dvW_le`). -/
noncomputable def mainCounts (op : Opcode) :
    Budget.MainCounts (B2C.ωArm B2C.xmssArmC op) B2C.fs where
  kExp := kcExp op
  exp := kcExp_weightLe op
  kSd := kcSd op
  sd := kcSd_weightLe op
  kL1 := kcL1 op
  l1 := kcL1_loop op
  kL2 := kcL2 op
  l2 := kcL2_loop op
  kL3 := kcL3 op
  l3 := kcL3_loop op
  kL4 := kcL4 op
  l4 := kcL4_loop op
  aggC := kcAggC op
  aggD := kcAggD op
  agg := kcAgg_le op
  clA := kcClA op
  clS := kcClS op
  cl := fun _ _ _ _ n _ hv hb hT hn =>
    (Budget.cl_weight_le op hn hT hv hb).trans (Budget.clW_le op n)
  dvA := kcDvA op
  dvR := kcDvR op
  dvP := kcDvP op
  dv := fun _ _ _ _ r L _ hv hb hT h1 hr hL => by
    obtain ⟨hlo, hhi⟩ := B1.Da.nPad_bounds h1
    rw [← hL] at hlo hhi
    have hm : r ≤ 1024 := hr
    have hL11 : L < 11 :=
      (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp (by omega : 2 ^ L < 2 ^ 11)
    exact (Budget.dv_weight_le op (by omega) hlo hL11 hT hv hb).trans
      (Budget.dvW_le op hlo hL11)

end
end LeanVM.Guest.Count
