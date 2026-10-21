/-
  LeanVM.Guest.B1.Comp.Tables.VtKidsC

  `verify_tables`' 75 callees complete in the placed form over a completeness model.
-/

module

public import LeanVM.Guest.B1.Comp.Tables.VtPlacedB
public import LeanVM.Guest.B1.Comp.Tables.VtLoopsC
public import LeanVM.Guest.B1.Comp.Tables.VtTraceC
public import LeanVM.Guest.B1.Comp.Tables.ShapesWS
public import LeanVM.Guest.B1.Comp.FreeTree
public import LeanVM.Guest.B1.Tables.VtKidsB
public import LeanVM.Guest.B1.Tables.VtCSizeS

/-!
# `verify_tables`' callees over a completeness model

`Tables/VtKidsB.lean` over a `CompModel`: the 74 callees free of `BLAKE2S` (the padding weights,
the selectors, the index chains `__loop14`, `__loop16`, the equality product `__loop80`) are
complete under the model's semantics as deployed (`completeAtWS_of_freeOn`); the table sumcheck's
rounds `__loop79` are complete from their answered runs (`loop79_completeAtWC`, from
`loop79_completeC` and `vtc_zcRound_honestM`), its trees under any semantics bounded as deployed
(`vtcS_l79_total`). `vt_kids_completeWC`: `VtKidsCompleteWC CM`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Sig LeanVM.E2E.Complete
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-- The selectors are free of `BLAKE2S`. -/
theorem sel_mem_vtFree : ∀ i < 65, selNames.getD i "" ∈ vtFree := by
  decide

section
variable {S : BlakeSem} {fs : String → ℕ} {cert : String → V → ℕ} {Θ : Type} {w : Θ → String → ℕ}

private theorem vtclS_mem {l : List Stmt} {s : Stmt} (i : ℕ) (h : l[i]? = some s) : s ∈ l :=
  List.mem_of_getElem? h

/-- A loop's step: `x·g + N` and `x·g` from the five statements at `i`. -/
theorem vtclS_tail {rd : Reader} {σ : Val} {pre : List Stmt}
    (hes : ∀ e ∈ pre.flatMap (Main.slEvs σ), e.HoldsB S rd σ) (v i : ℕ)
    (h0 : pre[i]? = some (.atom (.const (.n v) (word 2 0 0))))
    (h1 : pre[i + 1]? = some (.atom (.mul (.n (v + 1)) (.n 0) (.n v))))
    (h2 : pre[i + 2]? = some (.atom (.add (.n (v + 2)) (.n (v + 1)) (.n 1))))
    (h3 : pre[i + 3]? = some (.atom (.const (.n (v + 3)) (word 2 0 0))))
    (h4 : pre[i + 4]? = some (.atom (.mul (.n (v + 4)) (.n 0) (.n (v + 3))))) :
    σ (.n (v + 2)) = σ (.n 0) * gen + σ (.n 1) ∧ σ (.n (v + 4)) = σ (.n 0) * gen := by
  have a0 := vtcS_atom hes (vtclS_mem _ h0)
  have a1 := vtcS_atom hes (vtclS_mem _ h1)
  have a2 := vtcS_atom hes (vtclS_mem _ h2)
  have a3 := vtcS_atom hes (vtclS_mem _ h3)
  have a4 := vtcS_atom hes (vtclS_mem _ h4)
  simp only [Atom.HoldsB, word_gen] at a0 a1 a2 a3 a4
  exact ⟨by rw [a2, a1, a0], by rw [a4, a3]⟩


/-- **A leaf's valid trees are its frame.** -/
theorem vtcS_leaf_total_of_ok {fs : String → ℕ} {g : String} (hok : vtcLeafOk g = true) {rd : Reader}
    {t : Tree} {args rets : List E} (hn : t.name = g) (hv : t.ValidB S coreProgram rd args rets)
    (hbo : t.BufsOk coreProgram) : t.total fs = fs g := by
  unfold vtcLeafOk at hok
  split at hok
  · next fn hf =>
    split at hok
    · next vs hl =>
      simp only [Bool.and_eq_true, List.isEmpty_iff] at hok
      obtain ⟨⟨hst, hna⟩, hnc⟩ := hok
      have hb : fn.body = fn.body.dropLast ++ [.ret vs] := by
        rw [← List.dropLast_append_getLast?  _ hl]
        simp
      exact vtcS_leaf_total (S := S) hf hb hst hna hnc hn hv hbo
    · exact absurd hok (by simp)
  · exact absurd hok (by simp)

/-- **`__loop79`'s trees** over `m` rounds, each with its `sumcheck_round4`. -/
theorem vtcS_l79_total {rd : Reader} {m : ℕ} {rest : List E} {t : Tree} {rets : List E} (hm : 0 < m)
    (hn : t.name = "__loop79") (hv : t.ValidB S coreProgram rd (1 :: gen ^ m :: rest) rets)
    (hbo : t.BufsOk coreProgram) :
    t.total fs ≤ m * (fs "__loop79" + fs "sumcheck_round4") + fs "__loop79" := by
  refine vtcS_loop_total (S := S) (fs := fs) find_loop79 vtc_core138 vtc_p79_ok.1 vtc_p79_ok.2.1 rd m rest _ ?_ m 0 t
    rets (by omega) hm hn (by rwa [pow_zero]) hbo
  intro σ j _ hp hes
  simp only [show Fn.params Data.core138 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5] from rfl,
    List.map_cons, List.map_nil, List.cons.injEq] at hp
  obtain ⟨h0, h1, hr⟩ := hp
  subst hr
  obtain ⟨e1, e2⟩ := vtclS_tail hes 26 22 rfl rfl rfl rfl rfl
  refine ⟨by rw [e1, h0, h1], by simp [e2, h0, h1], fun kids hk hbk => ?_⟩
  rw [vtc_p79_ok.2.2] at hk
  simp only [List.map_cons, List.map_nil, Main.mkCall] at hk
  match kids, hk, hbk with
  | [k], ⟨hnk, hvk, _⟩, ⟨hbk, _⟩ =>
    simp only [↓reduceIte] at hvk
    simp [Tree.totalKids, vtcS_leaf_total_of_ok vtc_sr4_leaf hnk hvk hbk]

/-- **`__loop79` is complete, placed, by a bounded tree.** -/
theorem loop79_completeAtBC (CM : CompModel) {rounds chi gn cprod : E} {m : ℕ} (hm0 : 0 < m) (k : ℕ) {Lin : Main.Layout}
    (hB : ∀ rd, LowDef k rd → MemL rd Lin → ∀ rd' : Reader,
      (∀ i, RegionL Lin i → rd' (gpow i) = rd (gpow i)) → ∀ j < m, ZcRoundM CM.hm rd' rounds chi gn cprod (gen ^ j)) :
    CompleteAtBS CM.sem fs cert k "__loop79" Lin [1, gen ^ m, rounds, chi, gn, cprod] (Returns [])
      (m * (fs "__loop79" + fs "sumcheck_round4") + fs "__loop79") :=
  completeAtS_of_rel_lowB pure79 (by simp) k
    (fun rd hl hL rd' hag => loop79_completeC hm0 (hB rd hl hL rd' hag))
    fun _ _ hn hv hbo => vtcS_l79_total hm0 hn hv hbo

/-- `loop79_completeAtB` within weights. -/
theorem loop79_completeAtWC (CM : CompModel) {rounds chi gn cprod : E} {m : ℕ} (hm0 : 0 < m) (k : ℕ) {Lin : Main.Layout}
    (hB : ∀ rd, LowDef k rd → MemL rd Lin → ∀ rd' : Reader,
      (∀ i, RegionL Lin i → rd' (gpow i) = rd (gpow i)) → ∀ j < m, ZcRoundM CM.hm rd' rounds chi gn cprod (gen ^ j)) :
    Main.CompleteAtWS CM.sem fs cert w k "__loop79" Lin [1, gen ^ m, rounds, chi, gn, cprod] (Returns [])
      (m * (fs "__loop79" + fs "sumcheck_round4") + fs "__loop79")
      fun θ => m * (w θ "__loop79" + w θ "sumcheck_round4") + w θ "__loop79" :=
  Main.CompleteAtB.toWS_total (loop79_completeAtBC CM hm0 k hB) fun _ _ _ _ hn hv hbo => vtcS_l79_total hm0 hn hv hbo

end

/-- **A table sumcheck round** on the honest round states, challenges and their products. -/
theorem vtc_zcRound_honestM {M : HashModel} {rd : Reader} {pR chi pC cur : E} {n j : ℕ} {cvr : ℕ → Digest}
    {cl ch : ℕ → E} {wsr : ℕ → List E} {chis : List E}
    (hR : ReadsAt rd pR (zcRoundsW cvr cur cl n)) (hC : ReadsAt rd pC (zcCprodW ch n))
    (hchi : ReadsAt rd chi chis) (hchis : chis = ((List.range n).map ch).reverse)
    (hws : ReadsAt rd (cur * gen ^ 5) ((List.range n).flatMap wsr))
    (hrun : ∀ r < n, RunsToM M (roundPoly 4 (cl r) none) (cvr r) (wsr r) (cl (r + 1), ch r) (cvr (r + 1)))
    (hj : j < n) : ZcRoundM M rd pR chi (gen ^ n) pC (gen ^ j) := by
  have hl3 : ∀ r < n, (wsr r).length = 3 := fun r hr => RunsToM.roundPoly4_len (hrun r hr)
  have hblk := readsAt_flatMap_block hws hj
  rw [vtc_flatMap3_length hl3 j hj.le, mul_assoc, ← pow_add] at hblk
  obtain ⟨c0, c2, c3, hw⟩ : ∃ a b c, wsr j = [a, b, c] := by
    match h : wsr j, hl3 j hj with
    | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
  rw [hw] at hblk
  have hrn := hrun j hj
  rw [hw] at hrn
  have B : ∀ r ≤ n, ReadsAt rd (pR * gen ^ (4 * r)) [(digestScalars (cvr r)).1, (digestScalars (cvr r)).2,
      cur * gen ^ (5 + 3 * r), cl r] := fun r hr => by
    have hR' : ReadsAt rd pR ((List.range (n + 1)).flatMap fun r => [(digestScalars (cvr r)).1,
        (digestScalars (cvr r)).2, cur * gen ^ (5 + 3 * r), cl r]) := hR
    have := readsAt_flatMap_block hR' (i := r) (by omega)
    rw [length_flatMap_range_const (w := 4) (fun _ => rfl)] at this
    exact this
  have Bj := B j hj.le
  have Bj1 := B (j + 1) hj
  have hx4 : pR * (gen ^ j) ^ 4 = pR * gen ^ (4 * j) := by rw [← pow_mul, Nat.mul_comm]
  have g0 : ∀ {k : ℕ} {w : E}, LoadHolds rd (pR * gen ^ (4 * (j + 1))) k w →
      LoadHolds rd (pR * gen ^ (4 * j)) (4 + k) w := fun h => vtc_shift h (by ring)
  have hq : gen ^ n * wInvG = gen ^ (n - 1 - j) * gen ^ j := by
    have e : gen ^ n = gen ^ (n - 1 - j) * gen ^ j * gen := by
      rw [← pow_add, ← pow_succ]; congr 1; omega
    rw [e, mul_assoc, show gen * wInvG = 1 by rw [mul_comm]; exact wInvG_mul_gen, mul_one]
  have hchj : LoadHolds rd (chi * gen ^ (n - 1 - j)) 0 (ch j) := by
    refine loadHolds_gen_pow_mul.mpr ?_
    have := hchi (n - 1 - j) (by rw [hchis]; simp; omega)
    rw [Nat.add_zero]
    convert this using 1
    subst hchis
    rw [List.getElem_reverse]
    simp only [List.getElem_map, List.getElem_range, List.length_map, List.length_range]
    congr 1; omega
  have Cj : LoadHolds rd (pC * gen ^ j) 0 (∏ r ∈ Finset.range j, ch r) := by
    refine loadHolds_gen_pow_mul.mpr ?_
    have := hC j (by simp [zcCprodW]; omega)
    simpa [zcCprodW] using this
  have Cj1 : LoadHolds rd (pC * gen ^ j) 1 ((∏ r ∈ Finset.range j, ch r) * ch j) := by
    refine loadHolds_gen_pow_mul.mpr ?_
    have := hC (j + 1) (by simp [zcCprodW]; omega)
    simpa [zcCprodW, Finset.prod_range_succ] using this
  refine ⟨cvr j, cur * gen ^ (5 + 3 * j), cl j, c0, c2, c3, cl (j + 1), ch j, cvr (j + 1),
    gen ^ (n - 1 - j), ∏ r ∈ Finset.range j, ch r, ?_, ?_, ?_, ?_, hblk, hrn, hq, hchj, ?_, ?_, ?_, ?_, Cj, Cj1⟩
  · rw [hx4]; exact Bj 0 (by simp)
  · rw [hx4]; exact Bj 1 (by simp)
  · rw [hx4]; exact Bj 2 (by simp)
  · rw [hx4]; exact Bj 3 (by simp)
  · rw [hx4]; exact g0 (k := 0) (Bj1 0 (by simp))
  · rw [hx4]; exact g0 (k := 1) (Bj1 1 (by simp))
  · rw [hx4]
    have := g0 (k := 2) (Bj1 2 (by simp))
    rwa [show cur * gen ^ (5 + 3 * (j + 1)) = cur * gen ^ (5 + 3 * j) * gen ^ 3 by
      rw [mul_assoc, ← pow_add]; ring_nf] at this
  · rw [hx4]; exact g0 (k := 3) (Bj1 3 (by simp))

/-- **`verify_tables`' callees are complete, placed, each by a tree within its name's bound and
weight, over a completeness model** (`VtKidsCompleteW`). -/
def VtKidsCompleteWC (CM : CompModel) : Prop :=
  ∀ (fs : String → ℕ) (cert : String → V → ℕ) (Θ : Type) (w : Θ → String → ℕ) (κ : ℕ), 7 ≤ κ → ∀ (Lin : Main.Layout) (b n logMem : ℕ)
    (ks τs nr : ℕ → ℕ) (point chis : List E) (cvr : ℕ → Digest) (cur : E) (cl ch : ℕ → E)
    (wsr : ℕ → List E) (zeta sq chiP : E),
    point.length < 33 → logMem ≤ point.length → 18 ≤ point.length → n ≤ point.length →
    (∀ i < 65, ks (selBlk.getD i 0) ≤ point.length) →
    (∀ t < 6, τs t < 29 ∧ τs t ≤ point.length ∧ nr t ≤ 2 ^ τs t) →
    chis = ((List.range n).map ch).reverse →
    (∀ r < n, RunsToM CM.hm (roundPoly 4 (cl r) none) (cvr r) (wsr r) (cl (r + 1), ch r) (cvr (r + 1))) →
    (∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd zeta point ∧ (∀ j < 34, LoadHolds rd sq j (gen ^ 2 ^ j)) ∧
      ReadsAt rd chiP chis ∧ ReadsAt rd (cur * gen ^ 5) ((List.range n).flatMap wsr)) →
    ∀ k ∈ vtKids Lin b n point.length logMem ks τs nr point zeta sq chiP
      (vtOwnW ks point logMem n cvr cur cl ch chis), k.taken = true →
      Main.CompleteAtWS CM.sem fs cert w κ k.f k.Lin k.args k.Out (vtNameBd fs k.f) fun θ => vtNameBd (w θ) k.f

section
variable (CM : CompModel)

set_option maxHeartbeats 4000000 in
/-- **`verify_tables`' callees are complete, placed, by bounded trees within weights**, on its honest buffers. -/
theorem vt_kids_completeWC : VtKidsCompleteWC CM := by
  intro fs cert Θ w κ hκ Lin b n logMem ks τs nr point chis cvr cur cl ch wsr zeta sq chiP hμ hlm h18 hn hks hτ
    hchis hrun hLin k hk ht
  have hown := (vtc_own_length ks point logMem n cvr cur cl ch chis).trans (vtc_sizes_length n)
  have hzs : ∀ rd, LowDef κ rd → MemL rd Lin →
      ReadsAt rd zeta point ∧ ReadsAt rd sq ((List.range 34).map fun j => gen ^ 2 ^ j) := fun rd h1 h2 =>
    ⟨(hLin rd h1 h2).1, fun t ht => by simpa using (hLin rd h1 h2).2.1 t (by simpa using ht)⟩
  obtain ⟨o3, o11, o15⟩ := vtc_own_idx ks point logMem n cvr cur cl ch chis
  have hidxR : ∀ {rd rd' : Reader}, LowDef κ rd →
      MemL rd (Lin ++ bufL b (vtSizes n) (vtOwnW ks point logMem n cvr cur cl ch chis)) →
      (∀ i, RegionL (Lin ++ bufL b (vtSizes n) (vtOwnW ks point logMem n cvr cur cl ch chis)) i →
        rd' (gpow i) = rd (gpow i)) →
      ReadsAt rd' zeta point ∧ (∀ t < 34, LoadHolds rd' (vtPtr b n 3) t (1 + gen ^ 2 ^ t)) := by
    intro rd rd' hlow hL hag
    obtain ⟨hL1, -⟩ := Main.memL_append.mp hL
    refine ⟨readsAt_transfer (fun rd h1 h2 => (hLin rd h1 h2).1) hlow hL1
      fun t ht => hag t (regionL_append.mpr (Or.inl ht)), fun t ht => ?_⟩
    have R := vtc_own_reads hown hL hag (i := 3) (by omega)
    rw [o3] at R
    exact vtcs_get (f := fun t => 1 + gen ^ 2 ^ t) R ht
  simp only [vtKids, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hk
  rcases hk with ((⟨t, ht6, rfl⟩ | rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩) | rfl | rfl
  · obtain ⟨h29, hτp, hnr⟩ := hτ t ht6
    have hj : τs t < pwNames.length := by simpa [pwNames] using h29
    show Main.CompleteAtWS CM.sem fs cert w κ (pwNames.getD (τs t) "") Lin _ _
      (vtNameBd fs (pwNames.getD (τs t) ""))
      fun θ => vtNameBd (w θ) (pwNames.getD (τs t) "")
    rw [List.getD_eq_getElem _ _ hj]
    refine completeAtWS_of_freeOn freeOn_vtFree (pw_mem_vtFree _ hj) ?_
    exact ((pw_completeAtW (τs t) hj hnr hτp (fun rd h1 h2 => (hLin rd h1 h2).1)).bmono
      (fs_le_vtNameBd fs _)).wmono fun θ => fs_le_vtNameBd (w θ) _
  · refine completeAtWS_of_freeOn freeOn_vtFree (sel_mem_vtFree 0 (by norm_num)) ?_
    exact (vtc_sel_kidW (i := 0) (by norm_num) hown
      (fun r hr => vtc_own_sel ks point logMem n cvr cur cl ch chis (by norm_num) hr) hzs hμ
      (Nat.pos_of_ne_zero (by simpa using ht))).bmono (le_of_eq (sel_nameBd fs (by norm_num)).symm)
      |>.wmono fun θ => le_of_eq (sel_nameBd (w θ) (by norm_num)).symm
  · refine completeAtWS_of_freeOn freeOn_vtFree (sel_mem_vtFree 1 (by norm_num)) ?_
    exact (vtc_sel_kidW (i := 1) (by norm_num) hown
      (fun r hr => vtc_own_sel ks point logMem n cvr cur cl ch chis (by norm_num) hr) hzs hμ
      (Nat.pos_of_ne_zero (by simpa using ht))).bmono (le_of_eq (sel_nameBd fs (by norm_num)).symm)
      |>.wmono fun θ => le_of_eq (sel_nameBd (w θ) (by norm_num)).symm
  · refine completeAtWS_of_freeOn freeOn_vtFree (show "__loop14" ∈ vtFree by decide) ?_
    refine ((idx_completeAtW idx_ok.1 (by simp) (Nat.pos_of_ne_zero (by simpa using ht)) κ
      fun rd hlow hL rd' hag j hj => ?_).bmono (idx14_le fs (by omega))).wmono fun θ => idx14_le (w θ) (by omega)
    obtain ⟨hz, hidx⟩ := hidxR hlow hL hag
    have R := vtc_own_reads hown hL hag (i := 11) (by omega)
    rw [o11] at R
    exact vtc_idxBody_honest hz hidx R hj (by omega) (by omega)
  · refine completeAtWS_of_freeOn freeOn_vtFree (sel_mem_vtFree 2 (by norm_num)) ?_
    exact (vtc_sel_kidW (i := 2) (by norm_num) hown
      (fun r hr => vtc_own_sel ks point logMem n cvr cur cl ch chis (by norm_num) hr) hzs hμ
      (Nat.pos_of_ne_zero (by simpa using ht))).bmono (le_of_eq (sel_nameBd fs (by norm_num)).symm)
      |>.wmono fun θ => le_of_eq (sel_nameBd (w θ) (by norm_num)).symm
  · refine completeAtWS_of_freeOn freeOn_vtFree (show "__loop16" ∈ vtFree by decide) ?_
    refine ((idx_completeAtW idx_ok.2 (by simp) (by norm_num) κ fun rd hlow hL rd' hag j hj => ?_).bmono
      (idx16_le fs)).wmono fun θ => idx16_le (w θ)
    obtain ⟨hz, hidx⟩ := hidxR hlow hL hag
    have R := vtc_own_reads hown hL hag (i := 15) (by omega)
    rw [o15] at R
    exact vtc_idxBody_honest hz hidx R hj (by omega) (by omega)
  · refine completeAtWS_of_freeOn freeOn_vtFree (sel_mem_vtFree (i + 3) (by omega)) ?_
    exact (vtc_sel_kidW (i := i + 3) (by omega) hown
      (fun r hr => vtc_own_sel ks point logMem n cvr cur cl ch chis (by omega) hr) hzs hμ
      (Nat.pos_of_ne_zero (by simpa using ht))).bmono (le_of_eq (sel_nameBd fs (by omega)).symm)
      |>.wmono fun θ => le_of_eq (sel_nameBd (w θ) (by omega)).symm
  · refine ((loop79_completeAtWC CM (Nat.pos_of_ne_zero (by simpa using ht)) κ
      fun rd hlow hL rd' hag j hj => ?_).bmono (l79_le fs (by omega))).wmono fun θ => l79_le (w θ) (by omega)
    obtain ⟨hL1, -⟩ := Main.memL_append.mp hL
    have hagL : ∀ t, RegionL Lin t → rd' (gpow t) = rd (gpow t) := fun t ht =>
      hag t (regionL_append.mpr (Or.inl ht))
    have hchi := readsAt_transfer (fun rd h1 h2 => (hLin rd h1 h2).2.2.1) hlow hL1 hagL
    have hws := readsAt_transfer (fun rd h1 h2 => (hLin rd h1 h2).2.2.2) hlow hL1 hagL
    have R := vtc_own_reads hown hL hag (i := 202 + 0) (by omega)
    have C := vtc_own_reads hown hL hag (i := 202 + 1) (by omega)
    rw [vtc_own_tail ks point logMem n cvr cur cl ch chis (by omega)] at R C
    exact vtc_zcRound_honestM R C hchi hchis hws hrun hj
  · refine completeAtWS_of_freeOn freeOn_vtFree (show "__loop80" ∈ vtFree by decide) ?_
    refine ((loop80_completeAtW (Nat.pos_of_ne_zero (by simpa using ht)) κ
      fun rd hlow hL rd' hag j hj => ?_).bmono (l80_le fs (by omega))).wmono fun θ => l80_le (w θ) (by omega)
    obtain ⟨hL1, -⟩ := Main.memL_append.mp hL
    have hagL : ∀ t, RegionL Lin t → rd' (gpow t) = rd (gpow t) := fun t ht =>
      hag t (regionL_append.mpr (Or.inl ht))
    have hz := readsAt_transfer (fun rd h1 h2 => (hLin rd h1 h2).1) hlow hL1 hagL
    have hchi := readsAt_transfer (fun rd h1 h2 => (hLin rd h1 h2).2.2.1) hlow hL1 hagL
    have P := vtc_own_reads hown hL hag (i := 202 + 2) (by omega)
    rw [vtc_own_tail ks point logMem n cvr cur cl ch chis (by omega)] at P
    exact vtc_peqBody_honest P hz hchi hj hn (by rw [hchis]; simp)

end

end
end LeanVM.Guest.B1.VerifySub
