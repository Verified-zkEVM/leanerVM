/-
  LeanVM.Guest.B1.Comp.Tables.VtPlacedB

  `verify_tables`' placed form's conditions on a valuation of its body under any semantics of
  `BLAKE2S` (`VtPlacedOkB`).
-/

module

public import LeanVM.Guest.B1.Tables.VtPlaced
public import LeanVM.Guest.B1.Tables.VerifyTablesBaseM

/-!
# `verify_tables`, placed, under any semantics

`Tables/VtPlLoads.lean`, `Tables/VtPlVals.lean` and `Tables/VtPlaced.lean` with the body holding
under `S : BlakeSem` (`VtHoldsB S`) for `VtHolds`: each fact read off the body is read off a run
of it under `S` (`VtHoldsB.sliceB`, `VtHoldsB.atom`), none of them at a `BLAKE2S` atom, and the
padding's dispatches, to functions free of `BLAKE2S`, are their deployed relations
(`relB_iff_rel_of_freeOn`). `vt_placed_okB`: `VtPlacedOkB S`, `VtPlacedOk` under `S`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Sig
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

variable {S : BlakeSem}

/-- The padding's callees are free of `BLAKE2S`. -/
theorem pw_mem_vtFree : ∀ (j : ℕ) (hj : j < pwNames.length), pwNames[j]'hj ∈ vtFree := by
  decide

section
variable {rd : Reader} {σ : Val}

/-- A selector's pointer facts. -/
theorem vt_sel_factsB (h : VtHoldsB S rd σ) {i : ℕ} (hi : i < 65) :
    LoadHolds rd (σ (.n 9)) (selBlk.getD i 0) (σ (.n (selVal.getD i 0))) ∧
      σ (.n 6) = σ (.n (selVal.getD i 0 + 5)) * σ (.n (selVal.getD i 0)) ∧
      σ (.n (selVal.getD i 0 + 22)) = σ (.n (selVal.getD i 0 + 15)) * σ (.n (selVal.getD i 0 + 5)) ∧
      σ (.n (selVal.getD i 0 + 24)) = σ (.n (selVal.getD i 0 + 16)) * σ (.n (selVal.getD i 0 + 5)) := by
  obtain ⟨kr, hb⟩ := h.sliceB _ _ (sel_blocks i hi)
  simp only [selT, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, and_true, true_and, word_one,
    List.map_cons, List.map_nil] at hb
  obtain ⟨l0, -, -, m6, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, m22, -, m24, -, -, -⟩ := hb
  exact ⟨l0, m6, m22, m24⟩

/-- A side's rank `0`'s pointer facts. -/
theorem vt_rank0_factsB (h : VtHoldsB S rd σ) {k v so sd : ℕ}
    (heq : stmtsEqb (vtRank0 v so sd) ((vtPre.drop k).take 14) = true) :
    LoadHolds rd (σ (.n 24)) so (σ (.n v)) ∧ σ (.n (v + 5)) = σ (.n 25) * σ (.n v) ∧
      σ (.n (v + 8)) = σ (.n 9) * σ (.n v) ∧ LoadHolds rd (σ (.n (v + 8))) 0 (σ (.n (v + 9))) ∧
      σ (.n (v + 11)) = σ (.n 128) * σ (.n v) ∧ σ (.n (v + 12)) = σ (.n 10) * σ (.n (v + 9)) := by
  obtain ⟨kr, hb⟩ := h.sliceB _ _ heq
  simp only [vtRank0, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, and_true, word_one] at hb
  obtain ⟨l0, -, -, m5, -, -, -, m8, l9, -, m11, -, m12, -⟩ := hb
  exact ⟨l0, m5, m8, l9, m11, m12⟩

/-- A side's rank `≥ 1`'s pointer facts. -/
theorem vt_rankN_factsB (h : VtHoldsB S rd σ) {k v pk pg pgo so sd : ℕ}
    (heq : stmtsEqb (vtRankN v pk pg pgo so sd) ((vtPre.drop k).take 19) = true) :
    LoadHolds rd (σ (.n 24)) so (σ (.n v)) ∧ σ (.n (v + 5)) = σ (.n 25) * σ (.n v) ∧
      σ (.n (v + 8)) = σ (.n 9) * σ (.n v) ∧ LoadHolds rd (σ (.n (v + 8))) 0 (σ (.n (v + 9))) ∧
      σ (.n (v + 21)) = σ (.n 128) * σ (.n v) ∧ σ (.n (v + 22)) = σ (.n 10) * σ (.n (v + 9)) := by
  obtain ⟨kr, hb⟩ := h.sliceB _ _ heq
  simp only [vtRankN] at hb
  rw [Stmt.HoldsListB, Stmt.HoldsListB, Stmt.HoldsListB, Stmt.HoldsListB, Stmt.HoldsListB,
    Stmt.HoldsListB, Stmt.HoldsListB, Stmt.HoldsListB, Stmt.HoldsListB, Stmt.HoldsListB,
    Stmt.HoldsListB, Stmt.HoldsListB, Stmt.HoldsListB, Stmt.HoldsListB, holdsB_ite_noRet _ _ _ rfl rfl] at hb
  simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, and_true, implies_true] at hb
  obtain ⟨l0, -, -, m5, -, -, -, m8, l9, -, -, -, -, -, m21, -, m22, -, -⟩ := hb
  exact ⟨l0, m5, m8, l9, m21, m22⟩

/-- A table's pointer facts. -/
theorem vt_tab_factsB (h : VtHoldsB S rd σ) {dS g mS q pcS pc ppS pp t : ℕ}
    (e1 : stmtsEqb [.atom (.load (.n g) (.n 7) (t + 1))] ((vtPre.drop dS).take 1) = true)
    (e2 : stmtsEqb [.atom (.mul (.n 4554) (.n q) (.n g))] ((vtPre.drop mS).take 1) = true)
    (e3 : stmtsEqb [.atom (.mul (.n pc) (.n 4639) (.n q))] ((vtPre.drop pcS).take 1) = true)
    (e4 : stmtsEqb [.atom (.mul (.n pp) (.n 4655) (.n g))] ((vtPre.drop ppS).take 1) = true) :
    LoadHolds rd (σ (.n 7)) (t + 1) (σ (.n g)) ∧ σ (.n 4554) = σ (.n q) * σ (.n g) ∧
      σ (.n pc) = σ (.n 4639) * σ (.n q) ∧ σ (.n pp) = σ (.n 4655) * σ (.n g) :=
  ⟨h.atom' _ _ e1 rfl, h.atom' _ _ e2 rfl, h.atom' _ _ e3 rfl, h.atom' _ _ e4 rfl⟩

/-- A selector's frame's words. -/
theorem vt_sel_facts2B (h : VtHoldsB S rd σ) {i : ℕ} (hi : i < 65) :
    σ (.n (selVal.getD i 0 + 10)) = σ (.n 5) * σ (.n (selVal.getD i 0)) ∧
      σ (.n (selVal.getD i 0 + 11)) = word 17179869184 0 0 ∧
      σ (.n (selVal.getD i 0 + 14)) = σ (.n (selVal.getD i 0 + 12)) * σ (.n (selVal.getD i 0)) ∧
      σ (.n (selVal.getD i 0 + 20)) = 1 + σ (.n (selVal.getD i 0 + 5)) ∧
      σ (.n (selVal.getD i 0 + 21)) = 1 := by
  obtain ⟨kr, hb⟩ := h.sliceB _ _ (sel_blocks i hi)
  simp only [selT, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, and_true, true_and, word_one,
    List.map_cons, List.map_nil] at hb
  obtain ⟨-, -, -, -, -, -, m10, c11, -, m14, -, -, -, -, c19, a20, c21, -, -, -, -, -, -, -, -⟩ := hb
  exact ⟨m10, c11, m14, by rw [a20, c19], c21⟩

/-- **The padding weights**: table `t`'s selector `g^τ`, row count and results. -/
theorem vt_pad_valsB (h : VtHoldsB S rd σ) {rowsN : List ℕ} {point : List E} {logMem dims rows z : ℕ}
    (hrl : rowsN.length = 6) (hτ29 : ∀ m ∈ rowsN, log2Ceil m < 29)
    (hτμ : ∀ t < 6, log2Ceil (rowsN.getD t 0) ≤ point.length)
    (h7 : σ (.n 7) = ofK (Parameters.gpow dims)) (h8 : σ (.n 8) = ofK (Parameters.gpow rows))
    (h5 : σ (.n 5) = ofK (Parameters.gpow z))
    (hd : ReadsAt rd (ofK (Parameters.gpow dims)) (gen ^ logMem :: rowsN.map fun m ↦ gen ^ log2Ceil m))
    (hr : ReadsAt rd (ofK (Parameters.gpow rows)) (rowsN.map eOfNat))
    (hz : ReadsAt rd (ofK (Parameters.gpow z)) point) {t : ℕ} (ht : t < 6) :
    σ (.n (1733 + 14 * t)) = gen ^ log2Ceil (rowsN.getD t 0) ∧
      σ (.n (1733 + 14 * t + 5)) = eOfNat (rowsN.getD t 0) ∧
      [σ (.n (1733 + 14 * t + 6)), σ (.n (1733 + 14 * t + 7)), σ (.n (1733 + 14 * t + 8))] =
        [paddingWeight (point.take (log2Ceil (rowsN.getD t 0))) (rowsN.getD t 0),
          pwLead (log2Ceil (rowsN.getD t 0)) (rowsN.getD t 0),
          pwRest (log2Ceil (rowsN.getD t 0)) (rowsN.getD t 0)] := by
  obtain ⟨k, hb⟩ := h.sliceB _ _ (vt_pad_blocks t ht)
  simp only [vtPad, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, and_true, true_and, word_one,
    word_zero, List.map_cons, List.map_nil] at hb
  obtain ⟨l0, -, -, l5, ⟨j, hj, hjx, hrel⟩, -⟩ := hb
  have hτ := hτ29 (rowsN.getD t 0) (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
  have hdt : LoadHolds rd (ofK (Parameters.gpow dims)) (t + 1) (gen ^ log2Ceil (rowsN.getD t 0)) := by
    have := hd (t + 1) (by simp; omega)
    simp only [List.getElem_cons_succ, List.getElem_map] at this
    rwa [List.getD_eq_getElem _ _ (by omega)]
  have hrt : LoadHolds rd (ofK (Parameters.gpow rows)) t (eOfNat (rowsN.getD t 0)) := by
    have := hr t (by simp; omega)
    simp only [List.getElem_map] at this
    rwa [List.getD_eq_getElem _ _ (by omega)]
  rw [h7] at l0
  rw [h8] at l5
  have ev := loadHolds_unique l0 hdt
  have e5 := loadHolds_unique l5 hrt
  have hj29 : j < 29 := by simpa [pwNames] using hj
  have hjτ : j = log2Ceil (rowsN.getD t 0) := by
    rw [ev, gen_pow_eq_ofK] at hjx
    exact (gpow_injOn (by simp only [Set.mem_Iio]; omega)
      (by simp only [Set.mem_Iio]; omega) (ofK_injective hjx)).symm
  subst hjτ
  obtain ⟨n', zs, hn', hrows, hzl, hzs, hret⟩ := pw_dispatch _ hj
    ((relB_iff_rel_of_freeOn freeOn_vtFree (pw_mem_vtFree _ hj) _ _).mp hrel)
  rw [e5] at hrows
  have hle := le_two_pow_log2Ceil (rowsN.getD t 0)
  have hpow : 2 ^ log2Ceil (rowsN.getD t 0) < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hn := eOfNat_inj (by omega) (by omega) hrows
  rw [h5] at hzs
  have hzs' : zs = point.take (log2Ceil (rowsN.getD t 0)) := by
    apply List.ext_getElem (by simpa [hzl] using hτμ t ht)
    intro k h1 h2
    have hk : k < point.length := by simp at h2; omega
    rw [List.getElem_take]
    exact loadHolds_unique (hzs k h1) (hz k hk)
  refine ⟨ev, e5, ?_⟩
  rw [hret, hzs', ← hn]

set_option maxHeartbeats 4000000 in
/-- A selector's frame matches its callee. -/
theorem vt_sel_okB (h : VtHoldsB S rd σ) {i : ℕ} (hi : i < 65) (L : Main.Layout) {b n μ bk : ℕ}
    {ks : ℕ → ℕ} {zeta sq : E} (h5 : σ (.n 5) = zeta) (h6 : σ (.n 6) = gen ^ μ)
    (h9 : σ (.n 9) = ofK (Parameters.gpow bk)) (h10 : σ (.n 10) = sq)
    (hptr : ∀ i < 205, σ (.n (vtAllocVar.getD i 0)) = vtPtr b n i)
    (hbkR : ∀ b' < 102, LoadHolds rd (ofK (Parameters.gpow bk)) b' (gen ^ ks b'))
    (hks : ∀ b' < 102, ks b' ≤ μ) (hμ : μ < 33) (o : List E × Main.Layout)
    (hout : (vtSelKid L b n μ ks zeta sq i).taken = true → (vtSelKid L b n μ ks zeta sq i).Out o.1 o.2) :
    CallOk σ (Main.mkCall σ (vtSelCall i)) (vtSelKid L b n μ ks zeta sq i) o := by
  obtain ⟨sb2, -, -, av0, av1, av2, hblk⟩ := vt_selBuf i hi
  obtain ⟨l0, m6, -, -⟩ := vt_sel_factsB h hi
  obtain ⟨m10, -, m14, a20, c21⟩ := vt_sel_facts2B h hi
  rw [h9] at l0
  have ev := loadHolds_unique l0 (hbkR _ hblk)
  have hkμ := hks _ hblk
  have e5 : σ (.n (selVal.getD i 0 + 5)) = gen ^ (μ - ks (selBlk.getD i 0)) := by
    rw [h6, ev] at m6
    refine mul_right_cancel₀ (b := gen ^ ks (selBlk.getD i 0)) (pow_ne_zero _ vt_gen_ne_zero) ?_
    rw [← m6, ← pow_add, Nat.sub_add_cancel hkμ]
  have p12 : σ (.n (selVal.getD i 0 + 12)) = vtPtr b n (selBuf i) := by rw [← av0, hptr _ (by omega)]
  have p15 : σ (.n (selVal.getD i 0 + 15)) = vtPtr b n (selBuf i + 1) := by rw [← av1, hptr _ (by omega)]
  have p16 : σ (.n (selVal.getD i 0 + 16)) = vtPtr b n (selBuf i + 2) := by rw [← av2, hptr _ (by omega)]
  simp only [CallOk, vtSelCall, vtSelKid, Main.mkCall, List.map_cons, List.map_nil]
  refine ⟨trivial, ?_, fun ht => ⟨?_, (hout ht).1.symm⟩⟩
  · rw [a20, e5]; exact one_add_gen_pow_dec' (by omega)
  · rw [c21, e5, m14, p12, p15, m10, h5, p16, h10, ev]

end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **Every load reads the caller's words or a buffer.** -/
theorem vt_placed_loadsB {κ : ℕ} {rd : Reader} {σ : Val} {Lin : Main.Layout} {b : ℕ}
    {logMem n : ℕ} {rowsN : List ℕ} {point xs chis claims cpw : List E} {alphas : List E}
    {c sq dims rows bk fpw pool cplen : ℕ} {τ ks : ℕ → ℕ} {own : List (List E)}
    {cvr : ℕ → Digest} {cl ch : ℕ → E}
    (hτd : τ = fun t => log2Ceil (rowsN.getD t 0)) (hksd : ks = vtKs logMem τ)
    (hownd : own = vtOwnW ks point logMem n cvr (ofK (Parameters.gpow c)) cl ch chis)
    (h : VtHoldsB S rd σ) (hlow : LowDef κ rd) (hLin : MemL rd Lin) (hlm32 : logMem ≤ 32)
    (hrl : rowsN.length = 6) (hτ29 : ∀ t < 6, τ t < 29) (hal : alphas.length = 4)
    (hτn : ∀ t < 6, τ t ≤ n) (hnμ : n ≤ point.length) (hxl : xs.length = 5 + 3 * n + 104)
    (hcl : claims.length = nClaims) (hcpl : cpw.length = nPooled) (hlmμ : logMem ≤ point.length)
    (h18 : 18 ≤ point.length) (hμ33 : point.length < 33)
    (h2 : σ (.n 2) = ofK (Parameters.gpow c)) (h6 : σ (.n 6) = gen ^ point.length)
    (h7 : σ (.n 7) = ofK (Parameters.gpow dims)) (h8 : σ (.n 8) = ofK (Parameters.gpow rows))
    (h9 : σ (.n 9) = ofK (Parameters.gpow bk)) (h10 : σ (.n 10) = ofK (Parameters.gpow sq))
    (h11 : σ (.n 11) = ofK (Parameters.gpow fpw)) (h13 : σ (.n 13) = ofK (Parameters.gpow pool))
    (h14 : σ (.n 14) = ofK (Parameters.gpow cplen))
    (hptr : ∀ i < 205, σ (.n (vtAllocVar.getD i 0)) = vtPtr b n i) (h4554 : σ (.n 4554) = gen ^ n)
    (hallX : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd (ofK (Parameters.gpow c)) xs)
    (hallD : ∀ rd, LowDef κ rd → MemL rd Lin →
      ReadsAt rd (ofK (Parameters.gpow dims)) (gen ^ logMem :: rowsN.map fun m ↦ gen ^ log2Ceil m))
    (hallR : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd (ofK (Parameters.gpow rows)) (rowsN.map eOfNat))
    (hallK : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd (ofK (Parameters.gpow bk))
      (blockKappas (gen ^ logMem) (rowsN.map fun m ↦ gen ^ log2Ceil m)))
    (hallF : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd (ofK (Parameters.gpow fpw)) (eqKernel alphas))
    (hallP : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd (ofK (Parameters.gpow pool)) claims)
    (hallC : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd (ofK (Parameters.gpow cplen)) cpw)
    (hallS : ∀ rd, LowDef κ rd → MemL rd Lin →
      ReadsAt rd (ofK (Parameters.gpow sq)) ((List.range 34).map fun j => gen ^ 2 ^ j))
    (hB : MemL rd (bufL b (vtSizes n) own)) :
    ∀ q ∈ vtPre.filterMap Stmt.loadS, VtLoadOk Lin (bufL b (vtSizes n) own) σ q := by
  subst hksd
  have hks : ∀ b' < 102, vtKs logMem τ b' ≤ point.length := fun b' hb' => vtKs_le hlmμ h18 hnμ hτn hb'
  have hks34 : ∀ b' < 102, vtKs logMem τ b' < 34 := vtKs_lt hlm32 hτ29
  have hbkR : ∀ b' < 102, LoadHolds rd (ofK (Parameters.gpow bk)) b' (gen ^ vtKs logMem τ b') := by
    intro b' hb'
    have := readsAt_getD0 (hallK rd hlow hLin) (k := b') (by simp [blockKappas]; exact hb')
    rwa [vt_bk_get hrl hb', ← hτd] at this
  have hdR : ∀ t < 6, LoadHolds rd (ofK (Parameters.gpow dims)) (t + 1) (gen ^ τ t) := fun t ht => by
    have := (hallD rd hlow hLin) (t + 1) (by simp; omega)
    simp only [List.getElem_cons_succ, List.getElem_map] at this
    rw [hτd]; dsimp only; rw [List.getD_eq_getElem _ _ (by omega)]; exact this
  rw [hownd] at hB
  have hbuf0 := vt_own_reads (i := 0) hB (by omega)
  have hbuf202 := vt_own_reads (i := 202) hB (by omega)
  rw [vtOwnW_0] at hbuf0
  rw [vtOwnW_202] at hbuf202
  obtain ⟨a0, a1, a2, a11, a15, a202, a203, a204, z0, z1, z2, z11, z15⟩ := vt_allocVar_fixed
  have p25 : σ (.n 25) = vtPtr b n 1 := by rw [← hptr 1 (by omega), a1]
  have p24 : σ (.n 24) = vtPtr b n 0 := by rw [← hptr 0 (by omega), a0]
  have p128 : σ (.n 128) = vtPtr b n 2 := by rw [← hptr 2 (by omega), a2]
  have p4636 : σ (.n 4636) = vtPtr b n 202 := by rw [← hptr 202 (by omega), a202]
  have p4639 : σ (.n 4639) = vtPtr b n 203 := by rw [← hptr 203 (by omega), a203]
  have p4655 : σ (.n 4655) = vtPtr b n 204 := by rw [← hptr 204 (by omega), a204]
  -- regions
  have linA : ∀ {a : ℕ} {ws : List E}, (∀ rd, LowDef κ rd → MemL rd Lin →
      ReadsAt rd (ofK (Parameters.gpow a)) ws) → ∀ {k : ℕ} {e : ℕ} (off : ℕ),
      σ (.n k) = ofK (Parameters.gpow a) * gen ^ e → e + off < ws.length →
      VtLoadOk Lin (bufL b (vtSizes n) own) σ (.n k, off) := by
    intro a ws hall k e off hk he
    obtain ⟨i, hi, hr⟩ := addr_in_region hall hlow hLin (j := e + off) he
    refine ⟨i, ?_, Or.inl hr⟩
    show (σ (.n k)).limb 0 * Parameters.gpow off = Parameters.gpow i
    rw [hk, addr_gen, Nat.add_assoc, ← addr_k]; exact hi
  have ownA : ∀ {k : ℕ} (j e off : ℕ), σ (.n k) = vtPtr b n j * gen ^ e → j < 205 →
      e + off < (vtSizes n).getD j 0 → VtLoadOk Lin (bufL b (vtSizes n) own) σ (.n k, off) :=
    by
      intro k j e off hk hj he
      refine ⟨(bases b (vtSizes n)).getD j 0 + (e + off), ?_, Or.inr ?_⟩
      · show (σ (.n k)).limb 0 * _ = _
        rw [hk]; exact vtPtr_addr b n j e off
      · rw [hownd]; exact vt_own_region hj he
  have g0 : ∀ {x : E}, x = x * gen ^ 0 := fun {x} => by simp
  -- a rank
  have rankOK : ∀ {v blk P5 P8 P11 P12 : ℕ}, σ (.n v) = gen ^ blk → blk < 102 →
      σ (.n P5) = σ (.n 25) * σ (.n v) → σ (.n P8) = σ (.n 9) * σ (.n v) →
      LoadHolds rd (σ (.n P8)) 0 (σ (.n (v + 9))) → σ (.n P11) = σ (.n 128) * σ (.n v) →
      σ (.n P12) = σ (.n 10) * σ (.n (v + 9)) →
      VtLoadOk Lin (bufL b (vtSizes n) own) σ (.n P5, 0) ∧ VtLoadOk Lin (bufL b (vtSizes n) own) σ (.n P8, 0) ∧
        VtLoadOk Lin (bufL b (vtSizes n) own) σ (.n P11, 0) ∧
        VtLoadOk Lin (bufL b (vtSizes n) own) σ (.n P12, 0) := by
    intro v blk P5 P8 P11 P12 hv hblk m5 m8 l9 m11 m12
    have e9 : σ (.n (v + 9)) = gen ^ vtKs logMem τ blk := by
      rw [m8, h9, hv, loadHolds_mul_gen_pow, Nat.add_zero] at l9
      exact loadHolds_unique l9 (hbkR blk hblk)
    refine ⟨ownA 1 blk 0 (by rw [m5, p25, hv]) (by omega) (by rw [vtSizes_lo n (by omega), z1]; omega),
      linA hallK 0 (by rw [m8, h9, hv]) (by simp [blockKappas]; omega),
      ownA 2 blk 0 (by rw [m11, p128, hv]) (by omega) (by rw [vtSizes_lo n (by omega), z2]; omega),
      linA hallS 0 (by rw [m12, h10, e9]) (by simp; exact hks34 blk hblk)⟩
  -- a table
  have tabOK : ∀ {dS g mS q pcS pc ppS pp t : ℕ}, t < 6 →
      stmtsEqb [.atom (.load (.n g) (.n 7) (t + 1))] ((vtPre.drop dS).take 1) = true →
      stmtsEqb [.atom (.mul (.n 4554) (.n q) (.n g))] ((vtPre.drop mS).take 1) = true →
      stmtsEqb [.atom (.mul (.n pc) (.n 4639) (.n q))] ((vtPre.drop pcS).take 1) = true →
      stmtsEqb [.atom (.mul (.n pp) (.n 4655) (.n g))] ((vtPre.drop ppS).take 1) = true →
      VtLoadOk Lin (bufL b (vtSizes n) own) σ (.n pc, 0) ∧ VtLoadOk Lin (bufL b (vtSizes n) own) σ (.n pp, 0) := by
    intro dS g mS q pcS pc ppS pp t ht e1 e2 e3 e4
    obtain ⟨ld, mq, mpc, mpp⟩ := vt_tab_factsB h e1 e2 e3 e4
    rw [h7] at ld
    have eg : σ (.n g) = gen ^ τ t := loadHolds_unique ld (hdR t ht)
    have eq : σ (.n q) = gen ^ (n - τ t) := by
      rw [h4554, eg] at mq
      have hτt := hτn t ht
      refine mul_right_cancel₀ (pow_ne_zero (τ t) vt_gen_ne_zero) ?_
      rw [← mq, ← pow_add, Nat.sub_add_cancel hτt]
    refine ⟨ownA 203 (n - τ t) 0 (by rw [mpc, p4639, eq]) (by omega) (by rw [vtSizes_203]; omega),
      ownA 204 (τ t) 0 (by rw [mpp, p4655, eg]) (by omega)
        (by rw [vtSizes_204]; have := hτn t ht; omega)⟩
  intro q hq
  have hb := List.all_eq_true.mp vt_loads q hq
  obtain ⟨⟨path, tag, k⟩, off⟩ := q
  match path, tag, hb with
  | _ :: _, _, hb => simp [vtLoadB] at hb
  | [], _ + 1, hb => simp [vtLoadB] at hb
  | [], 0, hb =>
    show VtLoadOk Lin (bufL b (vtSizes n) own) σ (.n k, off)
    rcases vtLoadN_cases (k := k) (off := off) hb with ⟨t, ht, rfl, hoff⟩ | ⟨rfl, hk⟩ |
      ⟨rfl, hoff⟩ | ⟨rfl, hoff⟩ | ⟨t, ht, rfl, hoff⟩
    · simp only [vtArgPairs, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only at hoff ⊢
      · exact linA hallX off (h2.trans g0) (by rw [hxl]; omega)
      · exact linA hallD off (h7.trans g0) (by simp [hrl]; omega)
      · exact linA hallR off (h8.trans g0) (by simp [hrl]; omega)
      · exact linA hallK off (h9.trans g0) (by simp [blockKappas]; omega)
      · exact linA hallF off (h11.trans g0) (by rw [length_eqKernel, hal]; omega)
      · exact linA hallP off (h13.trans g0) (by rw [hcl]; show 0 + off < 112; omega)
      · exact linA hallC off (h14.trans g0) (by rw [hcpl]; show 0 + off < 109; omega)
    · rcases hk with hk | rfl | rfl | hk | hk
      · simp only [vtTabPtrs, List.mem_cons, List.not_mem_nil, or_false] at hk
        have T0 := tabOK (t := 0) (dS := 4374) (g := 4660) (mS := 4855) (q := 5141) (pcS := 4856) (pc := 5142)
          (ppS := 4858) (pp := 5144) (by omega) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          (by decide +kernel)
        have T1 := tabOK (t := 1) (dS := 4862) (g := 5148) (mS := 5383) (q := 5669) (pcS := 5384) (pc := 5670)
          (ppS := 5386) (pp := 5672) (by omega) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          (by decide +kernel)
        have T2 := tabOK (t := 2) (dS := 5391) (g := 5677) (mS := 5660) (q := 5946) (pcS := 5661) (pc := 5947)
          (ppS := 5663) (pp := 5949) (by omega) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          (by decide +kernel)
        have T3 := tabOK (t := 3) (dS := 5668) (g := 5954) (mS := 6183) (q := 6469) (pcS := 6184) (pc := 6470)
          (ppS := 6186) (pp := 6472) (by omega) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          (by decide +kernel)
        have T4 := tabOK (t := 4) (dS := 6191) (g := 6477) (mS := 6685) (q := 6971) (pcS := 6686) (pc := 6972)
          (ppS := 6688) (pp := 6974) (by omega) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          (by decide +kernel)
        have T5 := tabOK (t := 5) (dS := 6693) (g := 6979) (mS := 7846) (q := 8132) (pcS := 7847) (pc := 8133)
          (ppS := 7849) (pp := 8135) (by omega) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          (by decide +kernel)
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact T0.1
        · exact T0.2
        · exact T1.1
        · exact T1.2
        · exact T2.1
        · exact T2.2
        · exact T3.1
        · exact T3.2
        · exact T4.1
        · exact T4.2
        · exact T5.1
        · exact T5.2
      · -- the memory's index chain
        have m30 : σ (.n 1930) = σ (.n 1925) * σ (.n 1893) :=
          h.atom 1656 (.mul (.n 1930) (.n 1925) (.n 1893)) (by decide +kernel)
        have l93 := (vt_sel_factsB h (i := 1) (by omega)).1
        rw [h9] at l93
        have k1 : vtKs logMem τ 1 = logMem := by unfold vtKs; rfl
        have e93 : σ (.n 1893) = gen ^ logMem := by
          rw [← k1]; exact loadHolds_unique l93 (hbkR 1 (by omega))
        refine ownA 11 logMem 0 (by rw [m30, ← a11, hptr 11 (by omega), e93]) (by omega)
          (by rw [vtSizes_lo n (by omega), z11]; omega)
      · -- the bytecode's index chain
        have m34 : σ (.n 2034) = σ (.n 2029) * σ (.n 1997) :=
          h.atom 1764 (.mul (.n 2034) (.n 2029) (.n 1997)) (by decide +kernel)
        have l97 := (vt_sel_factsB h (i := 2) (by omega)).1
        rw [h9] at l97
        have k2 : vtKs logMem τ 2 = 18 := by unfold vtKs; rfl
        have e97 : σ (.n 1997) = gen ^ 18 := by
          rw [← k2]; exact loadHolds_unique l97 (hbkR 2 (by omega))
        refine ownA 15 18 0 (by rw [m34, ← a15, hptr 15 (by omega), e97]) (by omega)
          (by rw [vtSizes_lo n (by omega), z15]; omega)
      · -- a selector
        rw [vtSelPtrs_eq] at hk
        obtain ⟨i, hi, hk⟩ := List.mem_flatMap.mp hk
        have hi65 := List.mem_range.mp hi
        obtain ⟨sb2, sz1, sz2, -, av1, av2, hblk⟩ := vt_selBuf i hi65
        obtain ⟨l0, m6, m22, m24⟩ := vt_sel_factsB h hi65
        rw [h9] at l0
        have ev := loadHolds_unique l0 (hbkR _ hblk)
        have hkμ := hks _ hblk
        have e5 : σ (.n (selVal.getD i 0 + 5)) = gen ^ (point.length - vtKs logMem τ (selBlk.getD i 0)) := by
          rw [h6, ev] at m6
          refine mul_right_cancel₀ (b := gen ^ vtKs logMem τ (selBlk.getD i 0))
            (pow_ne_zero _ vt_gen_ne_zero) ?_
          rw [← m6, ← pow_add, Nat.sub_add_cancel hkμ]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl
        · refine ownA (selBuf i + 1) _ 0 (by rw [m22, ← av1, hptr _ (by omega), e5]) (by omega)
            (by rw [vtSizes_lo n (by omega), sz1]; omega)
        · refine ownA (selBuf i + 2) _ 0 (by rw [m24, ← av2, hptr _ (by omega), e5]) (by omega)
            (by rw [vtSizes_lo n (by omega), sz2]; omega)
      · -- a sort rank
        rw [vtRankPtrs_eq] at hk
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_flatMap,
          List.mem_range] at hk
        have pushV : ∀ r < 37, ∀ {v : ℕ}, LoadHolds rd (σ (.n 24)) r (σ (.n v)) →
            σ (.n v) = gen ^ (pushOrd (vtKs logMem τ)).getD r 0 := fun r hr v hl => by
          rw [p24] at hl
          have := readsAt_getD0 hbuf0 (k := r) (by simp [sortW]; omega)
          rw [sortW_get _ (by omega), ite_pos' hr] at this
          exact loadHolds_unique hl this
        have countV : ∀ r < 28, ∀ {v so : ℕ}, so = 74 + r → LoadHolds rd (σ (.n 24)) so (σ (.n v)) →
            σ (.n v) = gen ^ (74 + (countOrd (vtKs logMem τ)).getD r 0) := fun r hr v so hso hl => by
          subst hso
          rw [p24] at hl
          have := readsAt_getD0 hbuf0 (k := 74 + r) (by simp [sortW]; omega)
          rw [sortW_get _ (by omega), ite_neg' (by omega), ite_pos' (by omega),
            show 74 + r - 74 = r by omega] at this
          exact loadHolds_unique hl this
        obtain ⟨pl0, pm5, pm8, pl9, pm11, pm12⟩ := vt_rank0_factsB h vt_push_rank0
        obtain ⟨cl0, cm5, cm8, cl9, cm11, cm12⟩ := vt_rank0_factsB h vt_count_rank0
        have RP0 := rankOK (pushV 0 (by omega) pl0) (by have := pushOrd_lt (vtKs logMem τ) (r := 0) (by omega); omega)
          pm5 pm8 pl9 pm11 pm12
        have RC0 := rankOK (countV 0 (by omega) rfl cl0)
          (by have := countOrd_lt (vtKs logMem τ) (r := 0) (by omega); omega) cm5 cm8 cl9 cm11 cm12
        rcases hk with (hk | ⟨q, hq, hk⟩) | ⟨q, hq, hk⟩
        · rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact RP0.1
          · exact RP0.2.1
          · exact RP0.2.2.1
          · exact RP0.2.2.2
          · exact RC0.1
          · exact RC0.2.1
          · exact RC0.2.2.1
          · exact RC0.2.2.2
        · obtain ⟨l0, m5, m8, l9, m21, m22⟩ := vt_rankN_factsB h (vt_push_ranks q hq)
          have R := rankOK (pushV (q + 1) (by omega) l0)
            (by have := pushOrd_lt (vtKs logMem τ) (r := q + 1) (by omega); omega) m5 m8 l9 m21 m22
          rcases hk with rfl | rfl | rfl | rfl
          · exact R.1
          · exact R.2.1
          · exact R.2.2.1
          · exact R.2.2.2
        · obtain ⟨l0, m5, m8, l9, m21, m22⟩ := vt_rankN_factsB h (vt_count_ranks q hq)
          have R := rankOK (countV (q + 1) (by omega) (by omega) l0)
            (by have := countOrd_lt (vtKs logMem τ) (r := q + 1) (by omega); omega) m5 m8 l9 m21 m22
          rcases hk with rfl | rfl | rfl | rfl
          · exact R.1
          · exact R.2.1
          · exact R.2.2.1
          · exact R.2.2.2
    · -- the slots
      have m46 : σ (.n 4646) = σ (.n 4554) * σ (.n 4554) := h.atom 4358 (.mul (.n 4646) (.n 4554) (.n 4554)) (by decide +kernel)
      have m47 : σ (.n 4647) = σ (.n 4646) * σ (.n 4646) := h.atom 4359 (.mul (.n 4647) (.n 4646) (.n 4646)) (by decide +kernel)
      have m48 : σ (.n 4648) = σ (.n 4636) * σ (.n 4647) := h.atom 4360 (.mul (.n 4648) (.n 4636) (.n 4647)) (by decide +kernel)
      refine ownA 202 (4 * n) off ?_ (by omega) (by rw [vtSizes_202]; omega)
      rw [m48, m47, m46, h4554, p4636, ← pow_add, ← pow_add]; congr 2; ring
    · have m46 : σ (.n 4646) = σ (.n 4554) * σ (.n 4554) := h.atom 4358 (.mul (.n 4646) (.n 4554) (.n 4554)) (by decide +kernel)
      have m47 : σ (.n 4647) = σ (.n 4646) * σ (.n 4646) := h.atom 4359 (.mul (.n 4647) (.n 4646) (.n 4646)) (by decide +kernel)
      have m48 : σ (.n 4648) = σ (.n 4636) * σ (.n 4647) := h.atom 4360 (.mul (.n 4648) (.n 4636) (.n 4647)) (by decide +kernel)
      have l51 : LoadHolds rd (σ (.n 4648)) 2 (σ (.n 4651)) := h.atom 4363 (.load (.n 4651) (.n 4648) 2) (by decide +kernel)
      rw [m48, m47, m46, h4554, p4636, ← pow_add, ← pow_add, loadHolds_mul_gen_pow,
        show n + n + (n + n) + 2 = 4 * n + 2 by ring] at l51
      have e51 := loadHolds_unique l51 (zcRoundsW_get hbuf202 (r := n) le_rfl).2.2.1
      exact linA hallX off e51 (by rw [hxl]; omega)
    · rw [vtAllocPairs_eq] at ht
      obtain ⟨i, hi, hti⟩ := List.mem_iff_getElem.mp ht
      simp only [List.length_zip, List.length_append, vtSzPre_length] at hi
      have hi205 : i < 205 := by
        have : vtAllocVar.length = 205 := by decide
        omega
      rw [← hti, List.getElem_zip] at hoff ⊢
      dsimp only at hoff ⊢
      rw [← List.getD_eq_getElem _ 0]
      have hoff' : off < (vtSizes 0).getD i 0 := by
        rw [vtSizes_split, List.getD_eq_getElem _ _ (by simp [vtSzPre_length]; omega)]; exact hoff
      exact ownA i 0 off ((hptr i hi205).trans g0) hi205
        (by have := vtSizes_mono n hi205; simp only [Nat.zero_add]; omega)

variable (S) in
/-- **The placed form's conditions on a valuation of the body** (g5b): on a valuation under which
all of `vtPre` holds (`VtHolds`), with the arguments, the 205 hinted pointers from the base `b` and
`g^n`, on a memory defined below `2^κ` holding the caller's words `Lin` (`CompleteTablesAt`'s reads)
and the honest buffers, the hints' sizes are `vtSizes n`, their pointers the allocator's, the
dispatches' selectors powers of `g`, the frames `vtKids`', and every load reads the caller's words
or the buffers. The run's facts: `rowsN` the row counts (log-heights `τs`), `ks` the blocks'
log-heights `vtKs logMem τs`, `n` the largest `τs`, the stream `xs` of `5 + 3n + 104` words. -/
def VtPlacedOkB : Prop :=
  ∀ (κ : ℕ), 7 ≤ κ → ∀ (rd : Reader) (σ : Val) (Lin : Main.Layout) (b : ℕ)
    (logMem n : ℕ) (rowsN : List ℕ) (point xs chis : List E) (claims cpw : List E)
    (cvr : ℕ → Digest) (cl ch : ℕ → E) (alphas : List E)
    (c z lp sq dims rows bk fpw pool cplen chi : ℕ) (outs : List (List E × Main.Layout)),
    VtHoldsB S rd σ → LowDef κ rd → MemL rd Lin →
    point.length < 33 → 16 ≤ logMem → logMem ≤ 32 → rowsN.length = 6 → (∀ m ∈ rowsN, log2Ceil m < 29) →
    alphas.length = 4 → n = ((List.range 6).map fun t => log2Ceil (rowsN.getD t 0)).foldl max 0 →
    n ≤ point.length → logMem ≤ point.length → 18 ≤ point.length → xs.length = 5 + 3 * n + 104 →
    claims.length = nClaims → chis.length = n →
    cpw.length = nPooled →
    σ (.n 2) = ofK (Parameters.gpow c) → σ (.n 5) = ofK (Parameters.gpow z) →
    σ (.n 6) = gen ^ point.length → σ (.n 7) = ofK (Parameters.gpow dims) →
    σ (.n 8) = ofK (Parameters.gpow rows) → σ (.n 9) = ofK (Parameters.gpow bk) →
    σ (.n 10) = ofK (Parameters.gpow sq) → σ (.n 11) = ofK (Parameters.gpow fpw) →
    σ (.n 13) = ofK (Parameters.gpow pool) → σ (.n 14) = ofK (Parameters.gpow cplen) →
    σ (.n 15) = ofK (Parameters.gpow chi) →
    (∀ i < 205, σ (.n (vtAllocVar.getD i 0)) = vtPtr b n i) → σ (.n 4554) = gen ^ n →
    (∀ rd, LowDef κ rd → MemL rd Lin →
      ReadsAt rd (ofK (Parameters.gpow c)) xs ∧ ReadsAt rd (ofK (Parameters.gpow z)) point ∧
      ExpTables rd (ofK (Parameters.gpow lp)) (ofK (Parameters.gpow sq)) ∧
      ReadsAt rd (ofK (Parameters.gpow rows)) (rowsN.map eOfNat) ∧
      ReadsAt rd (ofK (Parameters.gpow dims)) (gen ^ logMem :: rowsN.map fun m ↦ gen ^ log2Ceil m) ∧
      ReadsAt rd (ofK (Parameters.gpow bk))
        (blockKappas (gen ^ logMem) (rowsN.map fun m ↦ gen ^ log2Ceil m)) ∧
      ReadsAt rd (ofK (Parameters.gpow fpw)) (eqKernel alphas) ∧
      ReadsAt rd (ofK (Parameters.gpow pool)) claims ∧
      ReadsAt rd (ofK (Parameters.gpow chi)) chis ∧
      ReadsAt rd (ofK (Parameters.gpow cplen)) cpw) →
    MemL rd (bufL b (vtSizes n) (vtOwnW (vtKs logMem fun t => log2Ceil (rowsN.getD t 0)) point logMem n
      cvr (ofK (Parameters.gpow c)) cl ch chis)) →
    OutsOk (vtKids Lin b n point.length logMem (vtKs logMem fun t => log2Ceil (rowsN.getD t 0))
      (fun t => log2Ceil (rowsN.getD t 0)) (fun t => rowsN.getD t 0) point (ofK (Parameters.gpow z))
      (ofK (Parameters.gpow sq)) (ofK (Parameters.gpow chi))
      (vtOwnW (vtKs logMem fun t => log2Ceil (rowsN.getD t 0)) point logMem n cvr
        (ofK (Parameters.gpow c)) cl ch chis)) outs →
    (∀ s ∈ vtPre, DispOk σ s) ∧
      (vtPre.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) = vtSizes n ∧
      ((vtPre.filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
        (bases b (vtSizes n)).map (fun b => ofK (Parameters.gpow b)) ∧
      CallsMatch σ ((vtPre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ))
        (vtKids Lin b n point.length logMem (vtKs logMem fun t => log2Ceil (rowsN.getD t 0))
          (fun t => log2Ceil (rowsN.getD t 0)) (fun t => rowsN.getD t 0) point (ofK (Parameters.gpow z))
          (ofK (Parameters.gpow sq)) (ofK (Parameters.gpow chi))
          (vtOwnW (vtKs logMem fun t => log2Ceil (rowsN.getD t 0)) point logMem n cvr
            (ofK (Parameters.gpow c)) cl ch chis)) outs ∧
      ∀ q ∈ vtPre.filterMap Stmt.loadS, ∃ i, (σ q.1).limb 0 * Parameters.gpow q.2 = Parameters.gpow i ∧
        (RegionL Lin i ∨ RegionL (bufL b (vtSizes n) (vtOwnW (vtKs logMem fun t => log2Ceil (rowsN.getD t 0))
          point logMem n cvr (ofK (Parameters.gpow c)) cl ch chis)) i)


variable (S) in
/-- **`VtPlacedOkB`, with the blocks' log-heights at most `|point|`.** -/
def VtPlacedOkB' : Prop :=
  ∀ (κ : ℕ), 7 ≤ κ → ∀ (rd : Reader) (σ : Val) (Lin : Main.Layout) (b : ℕ)
    (logMem n : ℕ) (rowsN : List ℕ) (point xs chis : List E) (claims cpw : List E)
    (cvr : ℕ → Digest) (cl ch : ℕ → E) (alphas : List E)
    (c z lp sq dims rows bk fpw pool cplen chi : ℕ) (outs : List (List E × Main.Layout)),
    VtHoldsB S rd σ → LowDef κ rd → MemL rd Lin →
    point.length < 33 → 16 ≤ logMem → logMem ≤ 32 → rowsN.length = 6 → (∀ m ∈ rowsN, log2Ceil m < 29) →
    alphas.length = 4 → n = ((List.range 6).map fun t => log2Ceil (rowsN.getD t 0)).foldl max 0 →
    n ≤ point.length → logMem ≤ point.length → 18 ≤ point.length →
    xs.length = 5 + 3 * n + 104 → claims.length = nClaims → chis.length = n →
    cpw.length = nPooled →
    σ (.n 2) = ofK (Parameters.gpow c) → σ (.n 5) = ofK (Parameters.gpow z) →
    σ (.n 6) = gen ^ point.length → σ (.n 7) = ofK (Parameters.gpow dims) →
    σ (.n 8) = ofK (Parameters.gpow rows) → σ (.n 9) = ofK (Parameters.gpow bk) →
    σ (.n 10) = ofK (Parameters.gpow sq) → σ (.n 11) = ofK (Parameters.gpow fpw) →
    σ (.n 13) = ofK (Parameters.gpow pool) → σ (.n 14) = ofK (Parameters.gpow cplen) →
    σ (.n 15) = ofK (Parameters.gpow chi) →
    (∀ i < 205, σ (.n (vtAllocVar.getD i 0)) = vtPtr b n i) → σ (.n 4554) = gen ^ n →
    (∀ rd, LowDef κ rd → MemL rd Lin →
      ReadsAt rd (ofK (Parameters.gpow c)) xs ∧ ReadsAt rd (ofK (Parameters.gpow z)) point ∧
      ExpTables rd (ofK (Parameters.gpow lp)) (ofK (Parameters.gpow sq)) ∧
      ReadsAt rd (ofK (Parameters.gpow rows)) (rowsN.map eOfNat) ∧
      ReadsAt rd (ofK (Parameters.gpow dims)) (gen ^ logMem :: rowsN.map fun m ↦ gen ^ log2Ceil m) ∧
      ReadsAt rd (ofK (Parameters.gpow bk))
        (blockKappas (gen ^ logMem) (rowsN.map fun m ↦ gen ^ log2Ceil m)) ∧
      ReadsAt rd (ofK (Parameters.gpow fpw)) (eqKernel alphas) ∧
      ReadsAt rd (ofK (Parameters.gpow pool)) claims ∧
      ReadsAt rd (ofK (Parameters.gpow chi)) chis ∧
      ReadsAt rd (ofK (Parameters.gpow cplen)) cpw) →
    MemL rd (bufL b (vtSizes n) (vtOwnW (vtKs logMem fun t => log2Ceil (rowsN.getD t 0)) point logMem n
      cvr (ofK (Parameters.gpow c)) cl ch chis)) →
    OutsOk (vtKids Lin b n point.length logMem (vtKs logMem fun t => log2Ceil (rowsN.getD t 0))
      (fun t => log2Ceil (rowsN.getD t 0)) (fun t => rowsN.getD t 0) point (ofK (Parameters.gpow z))
      (ofK (Parameters.gpow sq)) (ofK (Parameters.gpow chi))
      (vtOwnW (vtKs logMem fun t => log2Ceil (rowsN.getD t 0)) point logMem n cvr
        (ofK (Parameters.gpow c)) cl ch chis)) outs →
    (∀ s ∈ vtPre, DispOk σ s) ∧
      (vtPre.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) = vtSizes n ∧
      ((vtPre.filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
        (bases b (vtSizes n)).map (fun b => ofK (Parameters.gpow b)) ∧
      CallsMatch σ ((vtPre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ))
        (vtKids Lin b n point.length logMem (vtKs logMem fun t => log2Ceil (rowsN.getD t 0))
          (fun t => log2Ceil (rowsN.getD t 0)) (fun t => rowsN.getD t 0) point (ofK (Parameters.gpow z))
          (ofK (Parameters.gpow sq)) (ofK (Parameters.gpow chi))
          (vtOwnW (vtKs logMem fun t => log2Ceil (rowsN.getD t 0)) point logMem n cvr
            (ofK (Parameters.gpow c)) cl ch chis)) outs ∧
      ∀ q ∈ vtPre.filterMap Stmt.loadS, ∃ i, (σ q.1).limb 0 * Parameters.gpow q.2 = Parameters.gpow i ∧
        (RegionL Lin i ∨ RegionL (bufL b (vtSizes n) (vtOwnW (vtKs logMem fun t => log2Ceil (rowsN.getD t 0))
          point logMem n cvr (ofK (Parameters.gpow c)) cl ch chis)) i)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`verify_tables`' frames match its callees.** -/
theorem vt_calls_matchB {rd : Reader} {σ : Val} (h : VtHoldsB S rd σ) {Lin : Main.Layout} {b n logMem bk : ℕ}
    {point : List E} {ks τs nr : ℕ → ℕ} {zeta sq chiP : E} {own : List (List E)}
    {outs : List (List E × Main.Layout)} (hk1 : ks 1 = logMem) (hk2 : ks 2 = 18)
    (hpad : ∀ t < 6, σ (.n (1733 + 14 * t)) = gen ^ τs t ∧ τs t < 29 ∧
      σ (.n (1733 + 14 * t + 5)) = eOfNat (nr t) ∧
      [σ (.n (1733 + 14 * t + 6)), σ (.n (1733 + 14 * t + 7)), σ (.n (1733 + 14 * t + 8))] =
        [paddingWeight (point.take (τs t)) (nr t), pwLead (τs t) (nr t), pwRest (τs t) (nr t)])
    (hbkR : ∀ b' < 102, LoadHolds rd (ofK (Parameters.gpow bk)) b' (gen ^ ks b'))
    (hks : ∀ b' < 102, ks b' ≤ point.length) (hμ : point.length < 33) (hlm32 : logMem ≤ 32)
    (hnμ : n ≤ point.length) (h5 : σ (.n 5) = zeta) (h6 : σ (.n 6) = gen ^ point.length)
    (h9 : σ (.n 9) = ofK (Parameters.gpow bk)) (h10 : σ (.n 10) = sq) (h15 : σ (.n 15) = chiP)
    (hptr : ∀ i < 205, σ (.n (vtAllocVar.getD i 0)) = vtPtr b n i) (h4554 : σ (.n 4554) = gen ^ n)
    (ho : OutsOk (vtKids Lin b n point.length logMem ks τs nr point zeta sq chiP own) outs) :
    CallsMatch σ ((vtPre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ))
      (vtKids Lin b n point.length logMem ks τs nr point zeta sq chiP own) outs := by
  rw [vt_calls σ, vtRestCalls_eq, vtKids_eq]
  rw [vtKids_eq] at ho
  obtain ⟨o1, o2, rfl, ho1, ho2⟩ := vt_outsOk_append _ _ _ ho
  obtain ⟨o3, o4, rfl, ho3, ho4⟩ := vt_outsOk_append _ _ _ ho2
  obtain ⟨o5, o6, rfl, ho5, ho6⟩ := vt_outsOk_append _ _ _ ho4
  simp only [List.map_append, List.map_map]
  have selOK := fun i (hi : i < 65) o hout => vt_sel_okB h hi (Lin ++ bufL b (vtSizes n) own) h5 h6 h9 h10
    hptr hbkR hks hμ o hout
  refine vt_callsMatch_append _ _ _ _ _ _ (vt_callsMatch_map _ _ _ _ ho1 ?_)
    (vt_callsMatch_append _ _ _ _ _ _ ?_ (vt_callsMatch_append _ _ _ _ _ _
      (vt_callsMatch_map _ _ _ _ ho5 fun i hi o hout => selOK (i + 3) (by simp at hi; omega) o hout) ?_))
  · intro t ht o hout
    obtain ⟨e0, h29, e5', e6⟩ := hpad t (List.mem_range.mp ht)
    simp only [CallOk, Function.comp, vtPadCall, Main.mkCall, List.map_cons, List.map_nil]
    refine ⟨by rw [e0, logG_g _ (by omega)], trivial, fun _ => ⟨by rw [e5', h5], ?_⟩⟩
    rw [e6, (hout rfl).1]
  · -- the first five
    have e93 : σ (.n 1893) = gen ^ logMem := by
      have l93 := (vt_sel_factsB h (i := 1) (by omega)).1
      rw [h9] at l93
      rw [← hk1]; exact loadHolds_unique l93 (hbkR 1 (by omega))
    have e97 : σ (.n 1997) = gen ^ 18 := by
      have l97 := (vt_sel_factsB h (i := 2) (by omega)).1
      rw [h9] at l97
      rw [← hk2]; exact loadHolds_unique l97 (hbkR 2 (by omega))
    have a28 : σ (.n 1928) = σ (.n 1927) + σ (.n 1893) :=
      h.atom 1653 (.add (.n 1928) (.n 1927) (.n 1893)) (by decide +kernel)
    have c27 : σ (.n 1927) = word 1 0 0 := h.atom 1652 (.const (.n 1927) (word 1 0 0)) (by decide +kernel)
    have c29 : σ (.n 1929) = word 1 0 0 := h.atom 1654 (.const (.n 1929) (word 1 0 0)) (by decide +kernel)
    have a32 : σ (.n 2032) = σ (.n 2031) + σ (.n 1997) :=
      h.atom 1761 (.add (.n 2032) (.n 2031) (.n 1997)) (by decide +kernel)
    have c31 : σ (.n 2031) = word 1 0 0 := h.atom 1760 (.const (.n 2031) (word 1 0 0)) (by decide +kernel)
    have c33 : σ (.n 2033) = word 1 0 0 := h.atom 1762 (.const (.n 2033) (word 1 0 0)) (by decide +kernel)
    have av3 : vtAllocVar.getD 3 0 = 1817 := by decide
    obtain ⟨-, -, -, a11, a15, -, -, -, -, -, -, -, -⟩ := vt_allocVar_fixed
    have p1817 : σ (.n 1817) = vtPtr b n 3 := by rw [← av3, hptr 3 (by omega)]
    have p1925 : σ (.n 1925) = vtPtr b n 11 := by rw [← a11, hptr 11 (by omega)]
    have p2029 : σ (.n 2029) = vtPtr b n 15 := by rw [← a15, hptr 15 (by omega)]
    match o3, ho3 with
    | [q1, q2, q3, q4, q5], ⟨r1, r2, r3, r4, r5, _⟩ =>
      refine vt_cm_cons (selOK 0 (by omega) q1 r1) (vt_cm_cons (selOK 1 (by omega) q2 r2)
        (vt_cm_cons ?_ (vt_cm_cons (selOK 2 (by omega) q4 r4) (vt_cm_cons ?_ trivial))))
      · simp only [CallOk, Main.mkCall, List.map_cons, List.map_nil]
        refine ⟨trivial, ?_, fun ht => ⟨?_, (r3 ht).1.symm⟩⟩
        · rw [a28, c27, word_one, e93]; exact one_add_gen_pow_dec' (by omega)
        · rw [c29, word_one, e93, p1925, h5, p1817]
      · simp only [CallOk, Main.mkCall, List.map_cons, List.map_nil]
        refine ⟨trivial, ?_, fun _ => ⟨?_, (r5 rfl).1.symm⟩⟩
        · rw [a32, c31, word_one, e97]; exact one_add_gen_pow_dec' (by omega)
        · rw [c33, word_one, e97, p2029, h5, p1817]
  · -- the two sum-check loops
    have a44 : σ (.n 4644) = σ (.n 4643) + σ (.n 4554) :=
      h.atom 4355 (.add (.n 4644) (.n 4643) (.n 4554)) (by decide +kernel)
    have c43 : σ (.n 4643) = word 1 0 0 := h.atom 4354 (.const (.n 4643) (word 1 0 0)) (by decide +kernel)
    have c45 : σ (.n 4645) = word 1 0 0 := h.atom 4356 (.const (.n 4645) (word 1 0 0)) (by decide +kernel)
    have a58 : σ (.n 4658) = σ (.n 4657) + σ (.n 4554) :=
      h.atom 4371 (.add (.n 4658) (.n 4657) (.n 4554)) (by decide +kernel)
    have c57 : σ (.n 4657) = word 1 0 0 := h.atom 4370 (.const (.n 4657) (word 1 0 0)) (by decide +kernel)
    have c59 : σ (.n 4659) = word 1 0 0 := h.atom 4372 (.const (.n 4659) (word 1 0 0)) (by decide +kernel)
    obtain ⟨-, -, -, -, -, a202, a203, a204, -⟩ := vt_allocVar_fixed
    have p4636 : σ (.n 4636) = vtPtr b n 202 := by rw [← a202, hptr 202 (by omega)]
    have p4639 : σ (.n 4639) = vtPtr b n 203 := by rw [← a203, hptr 203 (by omega)]
    have p4655 : σ (.n 4655) = vtPtr b n 204 := by rw [← a204, hptr 204 (by omega)]
    match o6, ho6 with
    | [q1, q2], ⟨r1, r2, _⟩ =>
      refine vt_cm_cons ?_ (vt_cm_cons ?_ trivial)
      · simp only [CallOk, Main.mkCall, List.map_cons, List.map_nil]
        refine ⟨trivial, ?_, fun ht => ⟨?_, (r1 ht).1.symm⟩⟩
        · rw [a44, c43, word_one, h4554]; exact one_add_gen_pow_dec' (by omega)
        · rw [c45, word_one, h4554, p4636, h15, p4639]
      · simp only [CallOk, Main.mkCall, List.map_cons, List.map_nil]
        refine ⟨trivial, ?_, fun ht => ⟨?_, (r2 ht).1.symm⟩⟩
        · rw [a58, c57, word_one, h4554]; exact one_add_gen_pow_dec' (by omega)
        · rw [c59, word_one, h4554, p4655, h5, h15]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem vt_placed_okB' : VtPlacedOkB' S := by
  intro κ hκ rd σ Lin b logMem n rowsN point xs chis claims cpw cvr cl ch alphas c z lp sq dims rows bk fpw
    pool cplen chi outs h hlow hLin hμ33 h16 hlm32 hrl hτ29 hal hn hnμ hlmμ h18 hxl hcl hchl hcpl h2 h5 h6
    h7 h8 h9 h10 h11 h13 h14 h15 hptr h4554 hpre hB ho
  obtain ⟨hxs, hz, hexp, hrows, hdims, hbk, hfpw, hpool, hchi, hcp⟩ := hpre rd hlow hLin
  have hτn : ∀ t < 6, log2Ceil (rowsN.getD t 0) ≤ n := fun t ht => by
    rw [hn]; exact le_foldl_max _ 0 _ (List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩)
  have hτ29' : ∀ t < 6, log2Ceil (rowsN.getD t 0) < 29 := fun t ht =>
    hτ29 (rowsN.getD t 0) (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
  have hτμ : ∀ t < 6, log2Ceil (rowsN.getD t 0) ≤ point.length := fun t ht => le_trans (hτn t ht) hnμ
  have pad := fun t (ht : t < 6) => vt_pad_valsB h hrl hτ29 hτμ h7 h8 h5 hdims hrows hz ht
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine dispOk_of fun p hp => ?_
    rw [vt_disps] at hp
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hp
    have ht6 := List.mem_range.mp ht
    exact ⟨log2Ceil (rowsN.getD t 0), by show _ < 29; exact hτ29' t ht6, by have := hτ29' t ht6; omega,
      by rw [(pad t ht6).1, gen_pow_eq_ofK]⟩
  · rw [show (vtPre.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) =
        ((vtPre.filterMap Main.Stmt.allocSz).map Prod.snd).map (fun y => y.elim id fun s => logG (σ s)) by
        rw [List.map_map]; rfl, vt_allocs, List.map_append, vtSizes_split]
    congr 1
    · rw [← vtSzSrcA_sizes]
      refine List.map_congr_left fun x hx => ?_
      have hc := List.all_eq_true.mp vtSzSrcA_cells x hx
      match x, hc with
      | .inl _, _ => rfl
      | .inr v, hc =>
        simp only [List.any_eq_true, beq_iff_eq, List.mem_range] at hc
        obtain ⟨i, hi, rfl⟩ := hc
        show logG (σ (.n (selVal.getD i 0 + 11))) = 34
        rw [(vt_sel_facts2B h hi).2.1, word_g34, logG_g _ (by norm_num)]
    · have c32 : σ (.n 4632) = word 2 0 0 := h.atom 4338 (.const (.n 4632) (word 2 0 0)) (by decide +kernel)
      have m33 : σ (.n 4633) = σ (.n 4554) * σ (.n 4632) :=
        h.atom 4339 (.mul (.n 4633) (.n 4554) (.n 4632)) (by decide +kernel)
      have m34 : σ (.n 4634) = σ (.n 4633) * σ (.n 4633) :=
        h.atom 4340 (.mul (.n 4634) (.n 4633) (.n 4633)) (by decide +kernel)
      have m35 : σ (.n 4635) = σ (.n 4634) * σ (.n 4634) :=
        h.atom 4341 (.mul (.n 4635) (.n 4634) (.n 4634)) (by decide +kernel)
      have c37 : σ (.n 4637) = word 2 0 0 := h.atom 4343 (.const (.n 4637) (word 2 0 0)) (by decide +kernel)
      have m38 : σ (.n 4638) = σ (.n 4554) * σ (.n 4637) :=
        h.atom 4344 (.mul (.n 4638) (.n 4554) (.n 4637)) (by decide +kernel)
      have c53 : σ (.n 4653) = word 2 0 0 := h.atom 4365 (.const (.n 4653) (word 2 0 0)) (by decide +kernel)
      have m54 : σ (.n 4654) = σ (.n 4554) * σ (.n 4653) :=
        h.atom 4366 (.mul (.n 4654) (.n 4554) (.n 4653)) (by decide +kernel)
      show [logG (σ (.n 4635)), logG (σ (.n 4638)), logG (σ (.n 4654))] = [4 * (n + 1), n + 1, n + 1]
      rw [m35, m34, m33, m38, m54, c32, c37, c53, word_gen, h4554, ← pow_succ, ← pow_add, ← pow_add,
        logG_g _ (by omega), logG_g _ (by omega)]
      simp only [List.cons.injEq, and_true]
      omega
  · rw [vt_allocs_fst, List.map_map]
    have hl : vtAllocVar.length = 205 := by decide
    apply List.ext_getElem (by simp [vt_length_bases, vtSizes_length, hl])
    intro i h1 h2
    have hi : i < 205 := by simpa [hl] using h1
    simp only [List.getElem_map, Function.comp]
    have := hptr i hi
    rw [List.getD_eq_getElem _ _ (by omega)] at this
    rw [this, vtPtr, List.getD_eq_getElem _ _ (by simpa [vt_length_bases, vtSizes_length] using hi)]
  · exact vt_calls_matchB h (zeta := ofK (Parameters.gpow z)) (sq := ofK (Parameters.gpow sq))
      (chiP := ofK (Parameters.gpow chi)) (bk := bk) (by unfold vtKs; rfl) (by unfold vtKs; rfl)
      (fun t ht => ⟨(pad t ht).1, hτ29' t ht, (pad t ht).2.1, (pad t ht).2.2⟩)
      (fun b' hb' => by
        have := readsAt_getD0 hbk (k := b') (by simp [blockKappas]; exact hb')
        rwa [vt_bk_get hrl hb'] at this)
      (fun b' hb' => vtKs_le hlmμ h18 hnμ hτn hb') hμ33 hlm32 hnμ h5 h6 h9 h10 h15 hptr h4554 ho
  · exact vt_placed_loadsB (τ := fun t => log2Ceil (rowsN.getD t 0)) rfl rfl rfl h hlow hLin hlm32 hrl hτ29' hal
      hτn hnμ hxl hcl hcpl hlmμ h18 hμ33 h2 h6 h7 h8 h9 h10 h11 h13 h14 hptr h4554
      (fun rd a e => (hpre rd a e).1) (fun rd a e => (hpre rd a e).2.2.2.2.1)
      (fun rd a e => (hpre rd a e).2.2.2.1) (fun rd a e => (hpre rd a e).2.2.2.2.2.1)
      (fun rd a e => (hpre rd a e).2.2.2.2.2.2.1) (fun rd a e => (hpre rd a e).2.2.2.2.2.2.2.1)
      (fun rd a e => (hpre rd a e).2.2.2.2.2.2.2.2.2)
      (fun rd a e j hj => by
        simp only [List.length_map, List.length_range] at hj
        simp only [List.getElem_map, List.getElem_range]
        exact ((hpre rd a e).2.2.1 j hj).2) hB

/-- **`verify_tables`' placed conditions under any semantics** (`vt_placed_ok`). -/
theorem vt_placed_okB : VtPlacedOkB S := vt_placed_okB'

end
end LeanVM.Guest.B1.VerifySub
