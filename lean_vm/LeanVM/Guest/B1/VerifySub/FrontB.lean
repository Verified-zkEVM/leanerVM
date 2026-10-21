/-
  LeanVM.Guest.B1.VerifySub.FrontB

  `verify_sub`'s first phases as facts of its valuation under any semantics of `BLAKE2S`, the
  seed's hash over a hash model.
-/

module

public import LeanVM.Guest.B1.VerifySub.ExtractB
public import LeanVM.Guest.B1.VerifySub.Front
public import LeanVM.Guest.Value.ModelChain

/-!
# The seed, the sizes and the kappas, under any semantics (G:2091-2123)

`Front.lean` over `S : BlakeSem` (`VsHoldsToB`):

* `vs_seedM`: over a hash model `M`, `compress(seed, pi)` is the model's answer for
  `seed ‖ pi` (`HashModel.one_block`, the cells canonical by `M.canonical`);
* `vs_logMemB`, `vs_kappasB`: the memory's log and `dims_g`, `kappa_base`, `block_kappa`, read
  off runs free of `BLAKE2S` (`VsHoldsToB.sliceF'`), their proofs `Front.lean`'s.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {S : BlakeSem} {rd : Reader} {σ : Val}

/-! ## The seed -/

/-- **The seed over a hash model** (G:2092-2093): the cells `seed`, `pi` are digests and
`compress(seed, pi)` is the model's answer `d` for `seed ‖ pi`. -/
theorem vs_seedM {M : HashModel} {N : ℕ} (h : VsHoldsToB M.sem N rd σ) (hN : 6 ≤ N) :
    ∃ seed pi d : Digest, (σ (.n 2), σ (.n 3)) = digestScalars seed ∧
      (σ (.n 0), σ (.n 1)) = digestScalars pi ∧
      M.H (digestBytes seed ++ digestBytes pi) = some d ∧
      (σ (.n 12), σ (.n 13)) = digestScalars d := by
  replace h := h.mono hN
  have hs := h.slice' 2 [.atom (.const (.n 9) (word 13503953895743350343 11912009169889063794 0)),
    .atom (.const (.n 10) (word 11170449402626986623 6620516960021240235 0)),
    .atom (.const (.n 11) (word 64 4294967295 0)),
    .atom (.blake2s (.n 2) (.n 3) (.n 0) (.n 1) (.n 9) (.n 10) (.n 12) (.n 13) (.n 11))]
    (by decide +kernel)
  simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, word_iv0, word_iv1, word_md64,
    and_true] at hs
  obtain ⟨h9, h10, h11, hc⟩ := hs
  rw [h9, h10, h11] at hc
  obtain ⟨seed, hseed⟩ := exists_digest ((M.canonical hc).1 0) ((M.canonical hc).1 1)
  obtain ⟨pi, hpi⟩ := exists_digest ((M.canonical hc).1 2) ((M.canonical hc).1 3)
  obtain ⟨d, hd, hout⟩ := HashModel.one_block hc
  refine ⟨seed, pi, d, hseed, hpi, ?_, hout⟩
  rw [← hd, blockBytes, digestBytes_eq, digestBytes_eq, ← hseed, ← hpi]
  simp only [List.append_assoc]

/-! ## The memory's log -/

/-- **The memory's log under `S`** (`vs_logMem`). -/
theorem vs_logMemB {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (Lm : MemImage κ) {N : ℕ}
    (h : VsHoldsToB S N Lm.read σ) (hN : 132 ≤ N) (ht : ExpTables Lm.read (σ (.n 4)) (σ (.n 5))) :
    ∃ m, 16 ≤ m ∧ m ≤ 32 ∧ σ (.n 15) = eOfNat m ∧ σ (.n 144) = gen ^ m := by
  replace h := h.mono hN
  obtain ⟨N, hN, hv, hr⟩ := gpw6_pow ht (h.callF' 125 "g_power_of_word__L6" [.n 15, .n 5] [.n 144]
    (by decide +kernel))
  have hs := h.sliceF' 126 [.atom (.const (.n 145) (word 4294967296 0 0)),
    .atom (.rangeCheck (.n 144) (.n 146) (.n 147) (.n 148) (.n 145)),
    .atom (.const (.n 149) (word 4294967296 0 0)), .atom (.const (.n 150) (word 65536 0 0)),
    .atom (.mul (.n 144) (.n 151) (.n 150)),
    .atom (.rangeCheck (.n 151) (.n 152) (.n 153) (.n 154) (.n 149))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hs
  obtain ⟨h145, ⟨r1, r2, r3⟩, h149, h150, h144, ⟨s1, s2, s3⟩⟩ := hs
  obtain ⟨e, he, hx⟩ := rc_gen hκ hκ6 Lm (K := 33) (by decide) (by decide)
    (by rw [h145]; exact word_two_pow (a := 32) (by decide)) r1 r2 r3
  obtain ⟨e', he', hx'⟩ := rc_gen hκ hκ6 Lm (K := 33) (by decide) (by decide)
    (by rw [h149]; exact word_two_pow (a := 32) (by decide)) s1 s2 s3
  have w16 : word 65536 0 0 = gen ^ 16 := word_two_pow (a := 16) (by decide)
  rw [h150, w16, hx', ← pow_add] at h144
  rw [hr] at hx h144
  have h1 := gen_pow_inj (by omega) (by omega) hx
  have h2 := gen_pow_inj (by omega) (by omega) h144
  exact ⟨N, by omega, by omega, hv, hr⟩

/-! ## The kappas -/

theorem vs_kb_blocksF : ∀ b < 102, b ≠ 2 → b ≠ 39 →
    (decide (bkStmt b + 2 ≤ 359) && stmtsEqb [.atom (.load (.n (bkV b)) (.n 155) (blockKappaSrc.getD b 0)),
      .atom (.load (.n (bkV b)) (.n 163) b)] ((vsPre.drop (bkStmt b)).take 2) &&
      Stmt.freeInList vsFree [.atom (.load (.n (bkV b)) (.n 155) (blockKappaSrc.getD b 0)),
        .atom (.load (.n (bkV b)) (.n 163) b)]) = true := by
  decide +kernel

theorem vs_kb_adjF : ∀ b ∈ [2, 39],
    (decide (bkStmt b + 4 ≤ 359) && stmtsEqb [.atom (.load (.n (bkV b)) (.n 155) 0),
      .atom (.const (.n (bkV b + 1)) (word 262144 0 0)),
      .atom (.mul (.n (bkV b + 2)) (.n (bkV b)) (.n (bkV b + 1))),
      .atom (.load (.n (bkV b + 2)) (.n 163) b)] ((vsPre.drop (bkStmt b)).take 4) &&
      Stmt.freeInList vsFree [.atom (.load (.n (bkV b)) (.n 155) 0),
        .atom (.const (.n (bkV b + 1)) (word 262144 0 0)),
        .atom (.mul (.n (bkV b + 2)) (.n (bkV b)) (.n (bkV b + 1))),
        .atom (.load (.n (bkV b + 2)) (.n 163) b)]) = true := by
  decide +kernel

theorem vs_kbase_blocksF : ∀ t < 6,
    (decide (138 + 2 * t + 2 ≤ 359) && stmtsEqb [.atom (.load (.n (157 + t)) (.n 143) (1 + t)),
      .atom (.load (.n (157 + t)) (.n 155) (2 + t))] ((vsPre.drop (138 + 2 * t)).take 2) &&
      Stmt.freeInList vsFree [.atom (.load (.n (157 + t)) (.n 143) (1 + t)),
        .atom (.load (.n (157 + t)) (.n 155) (2 + t))]) = true := by
  decide +kernel

/-- **`dims_g` and `block_kappa` under `S`** (`vs_kappas`). -/
theorem vs_kappasB {N : ℕ} (h : VsHoldsToB S N rd σ) (hN : 359 ≤ N) :
    ReadsAt rd (σ (.n 143)) (σ (.n 144) :: dimsWords σ) ∧
      ReadsAt rd (σ (.n 155)) (kappaBase (σ (.n 144)) (dimsWords σ)) ∧
      ReadsAt rd (σ (.n 163)) (blockKappas (σ (.n 144)) (dimsWords σ)) := by
  replace h := h.mono hN
  have h132 := h.atomF' 132 (.load (.n 144) (.n 143) 0) (by decide +kernel)
  have hb3 := h.sliceF' 135 [.atom (.const (.n 156) (word 1 0 0)), .atom (.load (.n 156) (.n 155) 0),
    .atom (.load (.n 144) (.n 155) 1)] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, word_one] at hb3
  obtain ⟨h156, l0, l1⟩ := hb3
  rw [h156] at l0
  have hk := fun t (ht : t < 6) => by
    have := h.sliceF' _ _ (vs_kbase_blocksF t ht)
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at this
    exact this
  have hdims : ReadsAt rd (σ (.n 143)) (σ (.n 144) :: dimsWords σ) := by
    intro k hk'
    cases k with
    | zero => exact h132
    | succ t =>
      simp only [dimsWords, List.length_cons, List.length_map, List.length_range] at hk'
      simpa [dimsWords, Nat.add_comm 1 t] using (hk t (by omega)).1
  have hbase : ReadsAt rd (σ (.n 155)) (kappaBase (σ (.n 144)) (dimsWords σ)) := by
    intro k hk'
    simp only [kappaBase, dimsWords, List.length_cons, List.length_map, List.length_range] at hk'
    match k, hk' with
    | 0, _ => simpa [kappaBase] using l0
    | 1, _ => simpa [kappaBase] using l1
    | t + 2, _ => simpa [kappaBase, dimsWords, Nat.add_comm 2 t] using (hk t (by omega)).2
  have hbase' : ∀ j < 8, LoadHolds rd (σ (.n 155)) j ((kappaBase (σ (.n 144)) (dimsWords σ)).getD j 0) :=
    fun j hj => by
      have hl : j < (kappaBase (σ (.n 144)) (dimsWords σ)).length := by
        simp [kappaBase, dimsWords]; omega
      rw [List.getD_eq_getElem _ _ hl]
      exact hbase j hl
  have hblk : ∀ b < 102, LoadHolds rd (σ (.n 163)) b
      ((kappaBase (σ (.n 144)) (dimsWords σ)).getD (blockKappaSrc.getD b 0) 0 *
        gen ^ blockKappaAdj.getD b 0) := fun b hb => by
    rw [blockKappaAdj_eq b hb]
    by_cases hadj : b = 2 ∨ b = 39
    · have hs := h.sliceF' _ _ (vs_kb_adjF b (by rcases hadj with rfl | rfl <;> simp))
      simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hs
      obtain ⟨la, hc, hm, lb⟩ := hs
      have hsrc0 : blockKappaSrc.getD b 0 = 0 := by rcases hadj with rfl | rfl <;> rfl
      have w18 : word 262144 0 0 = gen ^ 18 := word_two_pow (a := 18) (by decide)
      rw [hm, hc, loadHolds_unique la (hbase' 0 (by decide)), w18] at lb
      rw [hsrc0]
      simp only [hadj, ↓reduceIte]
      exact lb
    · have hs := h.sliceF' _ _ (vs_kb_blocksF b hb (fun e => hadj (Or.inl e))
        (fun e => hadj (Or.inr e)))
      simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hs
      obtain ⟨la, lb⟩ := hs
      rw [← loadHolds_unique la (hbase' _ (blockKappaSrc_lt b hb))]
      simp only [hadj, ↓reduceIte, pow_zero, mul_one]
      exact lb
  refine ⟨hdims, hbase, fun b hb => ?_⟩
  simp only [blockKappas, List.length_map, List.length_range] at hb
  simpa [blockKappas] using hblk b hb

/-! ## Blocks that hash -/

/-- **An `fs_next` block of the body over a hash model**: the word at the cursor's offset `j`,
absorbed into the state, the new state the model's answer. -/
theorem VsHoldsB.fsNextM {M : HashModel} (h : VsHoldsB M.sem rd σ) (n : ℕ) (s0 s1 cur : V)
    (j b : ℕ) (heq : stmtsEqb (fsNextT s0 s1 cur j b) ((vsPre.drop n).take 13) = true) :
    LoadHolds rd (σ cur) j (σ (.n b)) ∧ ∃ cv d, (σ s0, σ s1) = digestScalars cv ∧
      obsCvM M cv (σ (.n b)) = some d ∧ (σ (.n (b + 13)), σ (.n (b + 14))) = digestScalars d := by
  obtain ⟨⟨hl, cv, d, hcv, hd, hv⟩, -⟩ := holdsB_fsNextT s0 s1 cur j b
    (h.slice n _ (by rw [show (fsNextT s0 s1 cur j b).length = 13 by simp [fsNextT, fsCompressT]]; exact heq))
  refine ⟨hl, cv, d, hcv, hd, ?_⟩
  have h12 := hv 12 (by omega) (by omega)
  have h13 := hv 13 (by omega) (by omega)
  rw [show b + 1 + 12 = b + 13 by omega] at h12
  rw [show b + 1 + 13 = b + 14 by omega] at h13
  rw [h12, h13, fsValsD, fsValsD]

/-- **A `squeeze` block of the body over a hash model**: the new state the model's answer and
the challenge its. -/
theorem VsHoldsB.squeezeM {M : HashModel} (h : VsHoldsB M.sem rd σ) (n : ℕ) (s0 s1 : V) (b : ℕ)
    (heq : stmtsEqb (squeezeT s0 s1 b) ((vsPre.drop n).take 14) = true) :
    ∃ cv d, (σ s0, σ s1) = digestScalars cv ∧ sqCvM M cv = some d ∧
      (σ (.n (b + 5)), σ (.n (b + 6))) = digestScalars d ∧ σ (.n (b + 13)) = challengeOf d := by
  obtain ⟨⟨cv, d, hcv, hd, hv⟩, -⟩ := holdsB_squeezeT s0 s1 b
    (h.slice n _ (by rw [show (squeezeT s0 s1 b).length = 14 by simp [squeezeT, squeezeStateT, challengeT]]; exact heq))
  refine ⟨cv, d, hcv, hd, ?_, hv 13 (by omega)⟩
  rw [hv 5 (by omega), hv 6 (by omega)]
  simp only [sqValsD, sqStateValsD]

/-! ## The announced sizes and the root -/

theorem obsAllM_append_one (M : HashModel) (cv : Digest) (xs : List E) (x : E) :
    obsAllM M cv (xs ++ [x]) = (obsAllM M cv xs).bind fun c ↦ obsCvM M c x := by
  induction xs generalizing cv with
  | nil => simp [obsAllM]
  | cons y xs ih =>
    simp only [List.cons_append, obsAllM, ih, Option.bind_assoc]

/-- **The eight announced words over a hash model** (`vs_reads`): each at the stream's offset
`k`, absorbed in order, every state the model's answer; the six row counts at `table_rows`. -/
theorem vs_readsM {M : HashModel} (h : VsHoldsB M.sem rd σ) {cv0 : Digest}
    (h0 : (σ (.n 12), σ (.n 13)) = digestScalars cv0) :
    (∀ k < 8, LoadHolds rd (σ (.n 14)) k (σ (.n (rdB k)))) ∧
      (∀ k ≤ 8, ∃ cv, obsAllM M cv0 (readWords σ k) = some cv ∧
        (σ (.n (rdS k)), σ (.n (rdS k + 1))) = digestScalars cv) ∧
      ∀ t < 6, LoadHolds rd (σ (.n 30)) t (σ (.n (rdB (t + 1)))) := by
  have hb := fun k hk => h.fsNextM (rdN k) _ _ _ k (rdB k) (vs_reads_blocks k hk)
  refine ⟨fun k hk => (hb k hk).1, ?_, fun t ht => ?_⟩
  · intro k hk
    induction k with
    | zero => exact ⟨cv0, rfl, h0⟩
    | succ k ih =>
      obtain ⟨c, hc, hs⟩ := ih (by omega)
      obtain ⟨-, cv, d, hcv, hd, hout⟩ := hb k (by omega)
      rw [hs] at hcv
      obtain rfl := digestScalars_injective hcv
      refine ⟨d, ?_, hout⟩
      rw [readWords_succ, obsAllM_append_one, hc, Option.bind_some, hd]
  · exact h.atomF (rdN (t + 1) + 13) (.load (.n (rdB (t + 1))) (.n 30) t)
      (by rw [vs_rows_blocks t ht]; rfl)

/-- **The stack's root over a hash model** (`vs_root`): the two words at offsets `8`, `9`,
absorbed, both canonical; the root's digest. -/
theorem vs_rootM {M : HashModel} (h : VsHoldsB M.sem rd σ) {cv : Digest}
    (h0 : (σ (.n 134), σ (.n 135)) = digestScalars cv) :
    LoadHolds rd (σ (.n 14)) 8 (σ (.n 419)) ∧ LoadHolds rd (σ (.n 14)) 9 (σ (.n 434)) ∧
      (∃ cv', obsAllM M cv [σ (.n 419), σ (.n 434)] = some cv' ∧
        (σ (.n 447), σ (.n 448)) = digestScalars cv') ∧
      ∃ root : Digest, (σ (.n 419), σ (.n 434)) = digestScalars root := by
  obtain ⟨l8, cv8, d8, h8, e8, o8⟩ := h.fsNextM 508 (.n 134) (.n 135) (.n 14) 8 419 (by decide +kernel)
  obtain ⟨l9, cv9, d9, h9, e9, o9⟩ := h.fsNextM 521 (.n 432) (.n 433) (.n 14) 9 434 (by decide +kernel)
  rw [h0] at h8
  obtain rfl := digestScalars_injective h8
  rw [o8] at h9
  obtain rfl := digestScalars_injective h9
  have c1 := (assert_canonical_iff rd _ _).mp (h.callF 534 "assert_canonical" [.n 419] [.n 449]
    (by decide +kernel))
  have c2 := (assert_canonical_iff rd _ _).mp (h.callF 535 "assert_canonical" [.n 434] [.n 450]
    (by decide +kernel))
  refine ⟨l8, l9, ⟨d9, ?_, o9⟩, exists_digest c1.1 c2.1⟩
  simp only [obsAllM, e8, e9, Option.bind_some]

/-! ## The rate -/

/-- **The rate under `S`** (`vs_rate`). -/
theorem vs_rateB {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (Lm : MemImage κ) (h : VsHoldsB S Lm.read σ)
    (ht : ExpTables Lm.read (σ (.n 4)) (σ (.n 5))) :
    ∃ r, 1 ≤ r ∧ r ≤ 4 ∧ σ (.n 121) = eOfNat r ∧ σ (.n 138) = gen ^ (r - 1) := by
  obtain ⟨N, hN, hv, hr⟩ := gpw6_pow ht (h.callF 119 "g_power_of_word__L6" [.n 121, .n 5] [.n 136]
    (by decide +kernel))
  have hs := h.sliceF 120 [.atom (.const (.n 137) (word 2 0 0)),
    .atom (.mul (.n 136) (.n 138) (.n 137)), .atom (.const (.n 139) (word 8 0 0)),
    .atom (.rangeCheck (.n 138) (.n 140) (.n 141) (.n 142) (.n 139))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hs
  obtain ⟨h137, h136, h139, ⟨r1, r2, r3⟩⟩ := hs
  obtain ⟨e, he, hx⟩ := rc_gen hκ hκ6 Lm (K := 4) (by decide) (by decide)
    (by rw [h139]; exact word_two_pow (a := 3) (by decide)) r1 r2 r3
  rw [h137, word_gen, hx, gen_pow_mul_gen] at h136
  rw [h136] at hr
  have := gen_pow_inj (by omega) (by omega) hr
  exact ⟨N, by omega, by omega, hv, by rw [hx, show N - 1 = e by omega]⟩

/-! ## The push side's total and the bus depth -/

theorem vs_push_blocksF : ∀ b < 36,
    (stmtsEqb [.atom (.load (.n (pushK (b + 1))) (.n 163) (b + 1)),
      .atom (.mul (.n (pushK (b + 1) + 1)) (.n 5) (.n (pushK (b + 1)))),
      .atom (.load (.n (pushK (b + 1) + 2)) (.n (pushK (b + 1) + 1)) 0),
      .atom (.mul (.n (pushP (b + 1))) (.n (pushP b)) (.n (pushK (b + 1) + 2)))]
      ((vsPre.drop (pushStmt (b + 1))).take 4) &&
      Stmt.freeInList vsFree [.atom (.load (.n (pushK (b + 1))) (.n 163) (b + 1)),
      .atom (.mul (.n (pushK (b + 1) + 1)) (.n 5) (.n (pushK (b + 1)))),
      .atom (.load (.n (pushK (b + 1) + 2)) (.n (pushK (b + 1) + 1)) 0),
      .atom (.mul (.n (pushP (b + 1))) (.n (pushP b)) (.n (pushK (b + 1) + 2)))]) = true := by
  decide +kernel

/-- **The push side's total under `S`** (`vs_push`). -/
theorem vs_pushB (h : VsHoldsB S rd σ) :
    (∀ b < 37, LoadHolds rd (σ (.n 163)) b (σ (.n (pushK b))) ∧
      LoadHolds rd (σ (.n 5) * σ (.n (pushK b))) 0 (σ (.n (pushK b + 2)))) ∧
      σ (.n 416) = ((List.range 37).map fun b ↦ σ (.n (pushK b + 2))).prod := by
  have h0 := h.sliceF 359 [.atom (.load (.n 270) (.n 163) 0), .atom (.mul (.n 271) (.n 5) (.n 270)),
    .atom (.load (.n 272) (.n 271) 0)] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h0
  obtain ⟨a0, m0, b0⟩ := h0
  have hs := fun b (hb : b < 36) => by
    have := h.sliceF _ _ (vs_push_blocksF b hb)
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at this
    exact this
  refine ⟨fun b hb => ?_, ?_⟩
  · cases b with
    | zero =>
      refine ⟨a0, ?_⟩
      show LoadHolds rd (σ (.n 5) * σ (.n 270)) 0 (σ (.n 272))
      rw [← m0]; exact b0
    | succ b =>
      obtain ⟨a, m, l, -⟩ := hs b (by omega)
      exact ⟨a, by rw [← m]; exact l⟩
  · have hp : ∀ b < 37, σ (.n (pushP b)) = ((List.range (b + 1)).map fun b ↦ σ (.n (pushK b + 2))).prod := by
      intro b hb
      induction b with
      | zero => simp [pushP, pushK]
      | succ b ih =>
        obtain ⟨-, -, -, hm⟩ := hs b (by omega)
        rw [hm, ih (by omega), List.range_succ (n := b + 1), List.map_append, List.prod_append]
        simp
    simpa [pushP, pushK] using hp 36 (by omega)

/-- **The bus depth under `S`** (`vs_busMu`). -/
theorem vs_busMuB {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (Lm : MemImage κ) (h : VsHoldsB S Lm.read σ)
    (ht : ExpTables Lm.read (σ (.n 4)) (σ (.n 5))) :
    ∃ N < 2 ^ 34, σ (.n 416) = gen ^ N ∧ log2Ceil N < 34 ∧ σ (.n 417) = gen ^ log2Ceil N := by
  have hc := h.callF 506 "log2_ceil_in_the_exponent__L0_L34" [.n 416, .n 4, .n 5] [.n 417]
    (by decide +kernel)
  obtain ⟨N, hN, hg, hl, -, -, hr⟩ :=
    (log2_ceil_in_the_exponent_L0_L34_iff hκ hκ6 Lm ht _).mp hc
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true, Nat.zero_max] at hr hl
  exact ⟨N, hN, hg, hl, hr⟩

end
end LeanVM.Guest.B1.VerifySub
