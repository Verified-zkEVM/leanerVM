/-
  LeanVM.Guest.B1.Comp.VerifySub.Front

  `verify_sub`'s first blocks complete over a completeness model: the seed, the announced sizes,
  the rate and the memory's log, `kappa_base`, `block_kappa`, the push side's total and the root.
-/

module

public import LeanVM.Guest.B1.Comp.VerifySub.Blocks

/-!
# The first blocks over a completeness model (G:2091-2135)

`VerifySub/CFront.lean` over a `CompModel`. The blocks with a `BLAKE2S` row (the seed, the
announced words, the root) complete under `CM.sem` from the model's answers: the seed's state
`cv0` (`CM.H (digestBytes seed ++ digestBytes pi) = some cv0`), the state `cvA` after the eight
announced words (`obsAllM CM.hm cv0 D.ann = some cvA`), the state `cv10` after the root's two
words (`obsAllM CM.hm cvA [D.x0, D.x1] = some cv10`); their values are `seedOutC`, `readsOutC`,
`rootOutC`, the deployed `seedOut`, `readsOut`, `rootOut` at `D.cv0`, `obsAll D.cv0 D.ann`,
`D.cv10` (`c_seed_of_comp`, `c_reads_of_comp`, `c_root_of_comp`).

The blocks with none (`bSizes`, `bKBase`, `bBlockKappa`, `bPush`) complete under every semantics
as under the deployed one (`CompletesB.of_free`); `c_sizesB` and `c_pushB` take the calls they
make (`g_power_of_word`, `log2_ceil_in_the_exponent`) by themselves rather than through
`VsCallsOk`, whose other fields name the deployed run's states.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig LeanVM.E2E.Complete

@[expose] public section

variable {S : BlakeSem} {C : CallRel} {rd : Reader} {D : VsData} {P : VsPtrs}

/-! ## The seed -/

/-- The values the seed block leaves, its state `cv0` (`seedOut`). -/
def seedOutC (P : VsPtrs) (cv0 : Digest) : List (ℕ × E) :=
  [(7, P.pool), (8, P.cplen), (12, (digestScalars cv0).1), (13, (digestScalars cv0).2),
    (14, P.stream)]

theorem seedOutC_deployed : seedOutC P D.cv0 = seedOut D P := rfl

/-- **The seed over a completeness model** (G:2092-2094, `c_seed`). -/
theorem c_seed_comp {CM : CompModel} (σ : Val) (h2 : σ (.n 2) = (digestScalars D.seed).1)
    (h3 : σ (.n 3) = (digestScalars D.seed).2) (h0 : σ (.n 0) = (digestScalars D.pi).1)
    (h1 : σ (.n 1) = (digestScalars D.pi).2) {cv0 : Digest}
    (hcv0 : CM.H (digestBytes D.seed ++ digestBytes D.pi) = some cv0) :
    CompletesB CM.sem C rd 7 15 bSeed σ (fun σ' => Fixes σ' (seedOutC P cv0)) := by
  refine completesB_upds [(7, P.pool), (8, P.cplen), (9, word 13503953895743350343 11912009169889063794 0),
    (10, word 11170449402626986623 6620516960021240235 0), (11, word 64 4294967295 0),
    (12, (digestScalars cv0).1), (13, (digestScalars cv0).2), (14, P.stream)]
    (by simp) (fun next kret hn => ?_) ?_
  · simp only [bSeed, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, upds_n, upds_nil]
    simp only [Nat.reduceEqDiff, ↓reduceIte, true_and, word_iv0, word_iv1, word_md64,
      h0, h1, h2, h3]
    exact ⟨compress_seed_comp CM hcv0, hn⟩
  · intro p hp
    simp only [seedOutC, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp [upds_n]

/-- The deployed `c_seed`, from the model's at `CompModel.deployed`. -/
theorem c_seed_of_comp (σ : Val) (h2 : σ (.n 2) = (digestScalars D.seed).1)
    (h3 : σ (.n 3) = (digestScalars D.seed).2) (h0 : σ (.n 0) = (digestScalars D.pi).1)
    (h1 : σ (.n 1) = (digestScalars D.pi).2) :
    Completes C rd 7 15 bSeed σ (fun σ' => Fixes σ' (seedOut D P)) :=
  (c_seed_comp (CM := CompModel.deployed) σ h2 h3 h0 h1 rfl).of_deployed

/-! ## The announced sizes -/

/-- **One announced word over a completeness model** (G:2103-2107, `c_read`): read at offset `k`,
absorbed from the state `c` into the model's answer `c'`. -/
theorem c_read_comp {CM : CompModel} {k : ℕ} (hk : k < 8) (σ : Val) (h14 : σ (.n 14) = P.stream)
    (hx : LoadHolds rd P.stream k (D.ann.getD k 0)) {c c' : Digest}
    (hs : (σ (.n (rdS k)), σ (.n (rdS k + 1))) = digestScalars c)
    (hd : obsCvM CM.hm c (D.ann.getD k 0) = some c') :
    CompletesB CM.sem C rd (rdB k) (rdB k + 15) (bRead k) σ (fun σ' =>
      σ' (.n (rdB k)) = D.ann.getD k 0 ∧ (σ' (.n (rdS (k + 1))), σ' (.n (rdS (k + 1) + 1))) =
        digestScalars c') := by
  have h1 := rdS_lt k hk
  have h2 : 14 < rdB k := (show ∀ k < 8, 14 < rdB k by decide) k hk
  exact completesB_fsNextT_comp ⟨_, by omega, rfl⟩ ⟨_, h1, rfl⟩ ⟨14, h2, rfl⟩ hs
    (by rw [h14]; exact hx) hd fun σ' _ hb ho => ⟨hb, by rw [rdS_succ]; exact ho⟩

/-- The deployed `c_read`, from the model's at `CompModel.deployed`. -/
theorem c_read_of_comp {k : ℕ} (hk : k < 8) (hl : D.rows.length = 6) (σ : Val)
    (h14 : σ (.n 14) = P.stream) (hx : LoadHolds rd P.stream k (D.ann.getD k 0))
    (hs : (σ (.n (rdS k)), σ (.n (rdS k + 1))) = digestScalars (obsAll D.cv0 (D.ann.take k))) :
    Completes C rd (rdB k) (rdB k + 15) (bRead k) σ (fun σ' =>
      σ' (.n (rdB k)) = D.ann.getD k 0 ∧ (σ' (.n (rdS (k + 1))), σ' (.n (rdS (k + 1) + 1))) =
        digestScalars (obsAll D.cv0 (D.ann.take (k + 1)))) := by
  refine (c_read_comp (CM := CompModel.deployed) hk σ h14 hx hs ?_).of_deployed
  rw [ann_take_succ hl hk, obsAll_append_one]
  rfl

/-- The values the announced sizes leave, the state after them `cvA` (`readsOut`). -/
def readsOutC (D : VsData) (P : VsPtrs) (cvA : Digest) : List (ℕ × E) :=
  [(15, eOfNat D.logMem), (30, P.rows), (121, eOfNat D.rate),
    (134, (digestScalars cvA).1), (135, (digestScalars cvA).2)]

theorem readsOutC_deployed : readsOutC D P (obsAll D.cv0 D.ann) = readsOut D P := rfl

/-- **The eight announced words over a completeness model** (G:2103-2107, `c_reads`), the row
counts stored at `table_rows`: the model answers the chain of the eight words from `cv0`. -/
theorem c_reads_comp {CM : CompModel} (hl : D.rows.length = 6) (σ : Val) {cv0 cvA : Digest}
    (hσ : Fixes σ (seedOutC P cv0)) (hA : obsAllM CM.hm cv0 D.ann = some cvA)
    (hst : ∀ k < 8, LoadHolds rd P.stream k (D.ann.getD k 0))
    (hrows : ∀ t < 6, LoadHolds rd P.rows t (eOfNat (D.rows.getD t 0))) :
    CompletesB CM.sem C rd 15 136 bReads σ (fun σ' => Fixes σ' (readsOutC D P cvA)) := by
  have hlen := ann_length (D := D) hl
  have h14 : σ (.n 14) = P.stream := hσ.get (by simp [seedOutC])
  have hs0 : (σ (.n (rdS 0)), σ (.n (rdS 0 + 1))) = digestScalars cv0 := by
    show (σ (.n 12), σ (.n 13)) = _
    rw [hσ.get (k := 12) (e := (digestScalars cv0).1) (by simp [seedOutC]),
      hσ.get (k := 13) (e := (digestScalars cv0).2) (by simp [seedOutC])]
  -- the chain's states after each prefix
  have hpre : ∀ k, ∃ c, obsAllM CM.hm cv0 (D.ann.take k) = some c := fun k => obsAllM_take hA k
  have hnext : ∀ k < 8, ∀ c, obsAllM CM.hm cv0 (D.ann.take k) = some c →
      ∃ c', obsAllM CM.hm cv0 (D.ann.take (k + 1)) = some c' ∧
        obsCvM CM.hm c (D.ann.getD k 0) = some c' := fun k hk c hc => by
    obtain ⟨c', hc'⟩ := hpre (k + 1)
    exact ⟨c', hc', obsAllM_take_succ (by omega) hc' hc⟩
  obtain ⟨c1, hc1, hd1⟩ := hnext 0 (by omega) cv0 rfl
  obtain ⟨nb0, nb1, nb2, nbf⟩ := numBelow_reads
  rw [bReads_eq]
  have c0 := (c_read_comp (C := C) (P := P) (rd := rd) (D := D) (k := 0) (by omega) σ h14
    (hst 0 (by omega)) hs0 hd1).keep
    (l := [(14, P.stream)]) (by intro p hp; simp at hp; subst hp; exact h14) (by simp [rdB])
  refine CompletesB.append (m := 121) (P := fun σ' ↦ (σ' (.n 14) = P.stream ∧ σ' (.n 30) = P.rows ∧
      ∃ c, obsAllM CM.hm cv0 (D.ann.take (6 + 1)) = some c ∧
        (σ' (.n (rdS (6 + 1))), σ' (.n (rdS (6 + 1) + 1))) = digestScalars c) ∧
      Fixes σ' [(15, eOfNat D.logMem)])
    (by omega) (by omega) nb2 ?_ fun σ1 e1 h1 => ?_
  · refine CompletesB.append (m := 31) (P := fun σ' => σ' (.n 15) = eOfNat D.logMem ∧
        σ' (.n 14) = P.stream ∧ σ' (.n 30) = P.rows ∧ (σ' (.n 28), σ' (.n 29)) =
          digestScalars c1) (by omega) (by omega) nb1 ?_
      fun σ1 e1 h1 => ?_
    · refine CompletesB.append (m := 30) (by omega) (by omega) nb0 c0 fun σ1 e1 h1 => ?_
      exact completesB_hint (k := 30) P.rows (Post := fun σ' => σ' (.n 15) = eOfNat D.logMem ∧
        σ' (.n 14) = P.stream ∧ σ' (.n 30) = P.rows ∧ (σ' (.n 28), σ' (.n 29)) =
          digestScalars c1) (by
        obtain ⟨⟨hb, hs⟩, hf⟩ := h1
        vs_ev
        exact ⟨hb, hf.get (by simp), by first | rfl | trivial, hs⟩)
    · -- the six row counts
      obtain ⟨h15, h14', h30, hs⟩ := h1
      have := CompletesB.flatten (S := CM.sem) (C := C) (rd := rd) (blk := bReadRow)
        (st := fun t ↦ rdB (t + 1)) (Inv := fun t σ' ↦ σ' (.n 14) = P.stream ∧
          σ' (.n 30) = P.rows ∧ ∃ c, obsAllM CM.hm cv0 (D.ann.take (t + 1)) = some c ∧
            (σ' (.n (rdS (t + 1))), σ' (.n (rdS (t + 1) + 1))) = digestScalars c)
        6 (fun t _ => by simp [rdB]) (fun t ht => nbf t ht) (fun t ht σ' ⟨i14, i30, c, ic, is⟩ => ?_)
        σ1 ⟨h14', h30, c1, hc1, hs⟩
      · exact (this.keep (l := [(15, eOfNat D.logMem)])
          (by intro p hp; simp at hp; subst hp; exact h15) (by simp [rdB])).post fun _ _ h => h
      · obtain ⟨c', hc', hd'⟩ := hnext (t + 1) (by omega) c ic
        have c := (c_read_comp (C := C) (P := P) (rd := rd) (D := D) (k := t + 1) (by omega) σ' i14
          (hst (t + 1) (by omega)) is hd').keep (l := [(14, P.stream), (30, P.rows)])
          (by intro p hp; simp at hp; rcases hp with rfl | rfl <;> assumption)
          (by intro p hp; simp at hp; rcases hp with rfl | rfl <;> simp [rdB] <;> omega)
        refine (c.append_atom fun σ'' ⟨⟨hb, hs'⟩, hf⟩ => ⟨?_, hf.get (e := P.stream) (by simp),
          hf.get (e := P.rows) (by simp), c', hc', hs'⟩)
        show LoadHolds rd (σ'' (.n 30)) t (σ'' (.n (rdB (t + 1))))
        rw [hf.get (k := 30) (e := P.rows) (by simp), hb, ann_getD_row hl ht]
        exact hrows t ht
  · -- the rate
    obtain ⟨⟨h14', h30, c7, hc7, hs⟩, h15⟩ := h1
    obtain ⟨c8, hc8, hd8⟩ := hnext 7 (by omega) c7 hc7
    rw [List.take_of_length_le (by rw [hlen]), hA, Option.some.injEq] at hc8
    subst hc8
    have c := (c_read_comp (C := C) (P := P) (rd := rd) (D := D) (k := 7) (by omega) σ1 h14'
      (hst 7 (by omega)) hs hd8).keep
      (l := [(15, eOfNat D.logMem), (30, P.rows)])
      (by intro p hp; simp at hp; rcases hp with rfl | rfl
          · exact h15.get (by simp)
          · exact h30) (by intro p hp; simp at hp; rcases hp with rfl | rfl <;> simp [rdB])
    refine c.post fun σ' _ ⟨⟨hb, hs'⟩, hf⟩ => ?_
    rw [ann_getD_seven hl] at hb
    intro p hp
    simp only [readsOutC, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact hf.get (by simp)
    · exact hf.get (by simp)
    · exact hb
    · exact congrArg Prod.fst hs'
    · exact congrArg Prod.snd hs'

/-- The deployed `c_reads`, from the model's at `CompModel.deployed`. -/
theorem c_reads_of_comp (hl : D.rows.length = 6) (σ : Val) (hσ : Fixes σ (seedOut D P))
    (hst : ∀ k < 8, LoadHolds rd P.stream k (D.ann.getD k 0))
    (hrows : ∀ t < 6, LoadHolds rd P.rows t (eOfNat (D.rows.getD t 0))) :
    Completes C rd 15 136 bReads σ (fun σ' => Fixes σ' (readsOut D P)) :=
  (c_reads_comp (CM := CompModel.deployed) hl σ hσ (obsAllM_hm_deployed _ _) hst hrows).of_deployed

/-! ## The rate and the memory's log -/

/-- **The rate, `dims_g[0]` and the memory's log** (G:2108-2115, `c_sizes`), the two calls of
`g_power_of_word` given. -/
theorem c_sizesE (hlow : LowDef 6 rd) {sq : E} (hm1 : 16 ≤ D.logMem) (hm2 : D.logMem ≤ 32)
    (hr1 : 1 ≤ D.rate) (hr2 : D.rate ≤ 4)
    (hgR : C "g_power_of_word__L6" [eOfNat D.rate, sq] [gen ^ D.rate])
    (hgM : C "g_power_of_word__L6" [eOfNat D.logMem, sq] [gen ^ D.logMem])
    (hd0 : LoadHolds rd P.dims 0 (gen ^ D.logMem)) (σ : Val)
    (hσ : Fixes σ [(5, sq), (15, eOfNat D.logMem), (121, eOfNat D.rate)]) :
    Completes C rd 136 155 bSizes σ (fun σ' => Fixes σ' (sizesOut D P)) := by
  have h5 : σ (.n 5) = sq := hσ.get (by simp)
  have h15 : σ (.n 15) = eOfNat D.logMem := hσ.get (by simp)
  have h121 : σ (.n 121) = eOfNat D.rate := hσ.get (by simp)
  set r := D.rate
  set m := D.logMem
  refine completes_upds [(136, gen ^ r), (137, word 2 0 0), (138, gen ^ (r - 1)), (139, word 8 0 0),
    (140, (rcLow rd (r - 1) 4).1), (141, (rcLow rd (r - 1) 4).2.1),
    (142, (rcLow rd (r - 1) 4).2.2), (143, P.dims), (144, gen ^ m),
    (145, word 4294967296 0 0), (146, (rcLow rd m 33).1), (147, (rcLow rd m 33).2.1),
    (148, (rcLow rd m 33).2.2), (149, word 4294967296 0 0), (150, word 65536 0 0),
    (151, gen ^ (m - 16)), (152, (rcLow rd (m - 16) 33).1),
    (153, (rcLow rd (m - 16) 33).2.1), (154, (rcLow rd (m - 16) 33).2.2)]
    (by simp) (fun next kret hn => ?_) ?_
  · simp only [bSizes, Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil]
    refine ⟨?_, ?_, ?_, ?_, ?_, trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial, hn⟩
    · vs_ev
      rw [h121, h5]
      exact hgR
    · simp [Atom.Holds, upds_n]
    · simp only [Atom.Holds]
      vs_ev
      rw [word_gen]
      rw [← pow_succ, show r - 1 + 1 = r by omega]
    · simp [Atom.Holds, upds_n]
    · exact rc_holds_low hlow (K := 4) (e := r - 1) (by omega) (by omega) (by simp [upds_n])
        (by simp [upds_n]) (by simp [upds_n]) (by simp [upds_n])
        (by vs_ev
            exact word_two_pow (a := 3) (by decide))
    · vs_ev
      rw [h15, h5]
      exact hgM
    · simp [Atom.Holds, upds_n]
    · exact rc_holds_low hlow (K := 33) (e := m) (by omega) (by omega) (by simp [upds_n])
        (by simp [upds_n]) (by simp [upds_n]) (by simp [upds_n])
        (by vs_ev
            exact word_two_pow (a := 32) (by decide))
    · simp [Atom.Holds, upds_n]
    · simp [Atom.Holds, upds_n]
    · simp only [Atom.Holds]
      vs_ev
      have w16 : word 65536 0 0 = gen ^ 16 := word_two_pow (a := 16) (by decide)
      rw [w16, ← pow_add, show m - 16 + 16 = m by omega]
    · exact rc_holds_low hlow (K := 33) (e := m - 16) (by omega) (by omega) (by simp [upds_n])
        (by simp [upds_n]) (by simp [upds_n]) (by simp [upds_n])
        (by vs_ev
            exact word_two_pow (a := 32) (by decide))
    · simp only [Atom.Holds]
      vs_ev
      exact hd0
  · intro p hp
    simp only [sizesOut, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp [upds_n, r, m]

theorem bSizes_free : Stmt.freeInList ["g_power_of_word__L6"] bSizes = true := by decide

/-- **The sizes under any semantics** (`c_sizes`): `bSizes` has no `BLAKE2S` row. -/
theorem c_sizesB (hlow : LowDef 6 rd) {sq : E} (hm1 : 16 ≤ D.logMem) (hm2 : D.logMem ≤ 32)
    (hr1 : 1 ≤ D.rate) (hr2 : D.rate ≤ 4)
    (hgR : C "g_power_of_word__L6" [eOfNat D.rate, sq] [gen ^ D.rate])
    (hgM : C "g_power_of_word__L6" [eOfNat D.logMem, sq] [gen ^ D.logMem])
    (hd0 : LoadHolds rd P.dims 0 (gen ^ D.logMem)) (σ : Val)
    (hσ : Fixes σ [(5, sq), (15, eOfNat D.logMem), (121, eOfNat D.rate)]) :
    CompletesB S C rd 136 155 bSizes σ (fun σ' => Fixes σ' (sizesOut D P)) :=
  CompletesB.of_free bSizes_free (c_sizesE hlow hm1 hm2 hr1 hr2 hgR hgM hd0 σ hσ)

/-- The deployed `c_sizes`, from the block's under any semantics at `blakeDeployed`. -/
theorem c_sizes_of_comp (hlow : LowDef 6 rd) {lp sq : E} (hm1 : 16 ≤ D.logMem) (hm2 : D.logMem ≤ 32)
    (hr1 : 1 ≤ D.rate) (hr2 : D.rate ≤ 4) {bytecode : List K} (hC : VsCallsOk C bytecode D P lp sq)
    (hd0 : LoadHolds rd P.dims 0 (gen ^ D.logMem)) (σ : Val)
    (hσ : Fixes σ [(5, sq), (15, eOfNat D.logMem), (121, eOfNat D.rate)]) :
    Completes C rd 136 155 bSizes σ (fun σ' => Fixes σ' (sizesOut D P)) :=
  (c_sizesB (S := blakeDeployed) hlow hm1 hm2 hr1 hr2 hC.gpwRate hC.gpwMem hd0 σ hσ).of_deployed

/-! ## `kappa_base` and `block_kappa` -/

theorem bKBase_free : Stmt.freeInList [] bKBase = true := by decide

/-- **`kappa_base` under any semantics** (`c_kbase`). -/
theorem c_kbaseB (σ : Val) (hσ : Fixes σ [(143, P.dims), (144, gen ^ D.logMem)])
    (hd : ∀ t < 6, LoadHolds rd P.dims (1 + t) (gen ^ D.hs.getD t 0))
    (hk0 : LoadHolds rd P.kbase 0 1) (hk1 : LoadHolds rd P.kbase 1 (gen ^ D.logMem))
    (hk : ∀ t < 6, LoadHolds rd P.kbase (2 + t) (gen ^ D.hs.getD t 0)) :
    CompletesB S C rd 155 163 bKBase σ (fun σ' => Fixes σ' [(155, P.kbase)]) :=
  CompletesB.of_free bKBase_free (c_kbase σ hσ hd hk0 hk1 hk)

theorem bkBlk_free : ∀ b < 102, Stmt.freeInList [] (bkBlk b) = true := by decide

/-- **Block `b` of `block_kappa` under any semantics** (`c_bkBlk`). -/
theorem c_bkBlkB {b : ℕ} (hb : b < 102) (σ : Val) (h155 : σ (.n 155) = P.kbase)
    (h163 : σ (.n 163) = P.bk) (hsrc : LoadHolds rd P.kbase (blockKappaSrc.getD b 0) (bkSrc D b))
    (hbk : LoadHolds rd P.bk b ((blockKappas (gen ^ D.logMem) (D.hs.map (gen ^ ·))).getD b 0)) :
    CompletesB S C rd (bkV b) (bkV (b + 1)) (bkBlk b) σ
      (fun σ' => σ' (.n 155) = P.kbase ∧ σ' (.n 163) = P.bk) :=
  CompletesB.of_free (bkBlk_free b hb) (c_bkBlk hb σ h155 h163 hsrc hbk)

theorem bBlockKappa_free : Stmt.freeInList [] bBlockKappa = true := by decide +kernel

/-- **`block_kappa` under any semantics** (`c_blockKappa`). -/
theorem c_blockKappaB (σ : Val) (h155 : σ (.n 155) = P.kbase)
    (hsrc : ∀ b < 102, LoadHolds rd P.kbase (blockKappaSrc.getD b 0) (bkSrc D b))
    (hbk : ∀ b < 102, LoadHolds rd P.bk b
      ((blockKappas (gen ^ D.logMem) (D.hs.map (gen ^ ·))).getD b 0)) :
    CompletesB S C rd 163 270 bBlockKappa σ
      (fun σ' => Fixes σ' [(155, P.kbase), (163, P.bk)]) :=
  CompletesB.of_free bBlockKappa_free (c_blockKappa σ h155 hsrc hbk)

/-! ## The push side's total -/

theorem pushBlk_free (b : ℕ) : Stmt.freeInList [] (pushBlk b) = true := rfl

/-- **Push block `b + 1` under any semantics** (`c_pushBlk0`). -/
theorem c_pushBlk0B {lp sq : E} (ht : ExpTables rd lp sq) {b : ℕ} (hb : b < 36)
    (hk : pkap D (b + 1) < 34) (hbk : LoadHolds rd P.bk (b + 1) (gen ^ pkap D (b + 1))) (σ : Val)
    (h5 : σ (.n 5) = sq) (h163 : σ (.n 163) = P.bk) (hP : σ (.n (pushP b)) = gen ^ pS D b) :
    CompletesB S C rd (273 + 4 * b) (273 + 4 * (b + 1)) (pushBlk b) σ
      (fun σ' => σ' (.n 5) = sq ∧ σ' (.n 163) = P.bk ∧ σ' (.n (pushP (b + 1))) = gen ^ pS D (b + 1) ∧
        σ' (.n (274 + 4 * b)) = sq * gen ^ pkap D (b + 1)) :=
  CompletesB.of_free (pushBlk_free b) (c_pushBlk0 ht hb hk hbk σ h5 h163 hP)

/-- **Push block `b + 1` under any semantics** (`c_pushBlk`). -/
theorem c_pushBlkB {lp sq : E} (ht : ExpTables rd lp sq) {b : ℕ} (hb : b < 36)
    (hk : pkap D (b + 1) < 34) (hbk : LoadHolds rd P.bk (b + 1) (gen ^ pkap D (b + 1))) (σ : Val)
    (h5 : σ (.n 5) = sq) (h163 : σ (.n 163) = P.bk) (hP : σ (.n (pushP b)) = gen ^ pS D b)
    (hF : Fixes σ (pushPtrs D sq b)) :
    CompletesB S C rd (273 + 4 * b) (273 + 4 * (b + 1)) (pushBlk b) σ
      (fun σ' => σ' (.n 5) = sq ∧ σ' (.n 163) = P.bk ∧ σ' (.n (pushP (b + 1))) = gen ^ pS D (b + 1) ∧
        Fixes σ' (pushPtrs D sq (b + 1))) :=
  CompletesB.of_free (pushBlk_free b) (c_pushBlk ht hb hk hbk σ h5 h163 hP hF)

/-- **The push side's total and `g_bus_mu`** (G:2124-2128, `c_push`), the call of
`log2_ceil_in_the_exponent` given. -/
theorem c_pushE {lp sq : E}
    (ht : ExpTables rd lp sq) (hl : D.rows.length = 6) (hm : D.logMem ≤ 32)
    (hh : ∀ h ∈ D.hs, h < 29)
    (hbk : ∀ b < 37, LoadHolds rd P.bk b (gen ^ pkap D b))
    (hlog : C "log2_ceil_in_the_exponent__L0_L34" [gen ^ D.pushTotal, lp, sq]
      [gen ^ log2Ceil D.pushTotal]) (σ : Val)
    (hσ : Fixes σ [(4, lp), (5, sq), (163, P.bk)]) :
    Completes C rd 270 419 bPush σ (fun σ' => Fixes σ' (pushOut D P sq)) := by
  have h4 : σ (.n 4) = lp := hσ.get (by simp)
  have h5 : σ (.n 5) = sq := hσ.get (by simp)
  have h163 : σ (.n 163) = P.bk := hσ.get (by simp)
  have hhl : D.hs.length = 6 := by simp [VsData.hs, hl]
  have hk : ∀ b < 37, pkap D b < 34 := fun b hb => by
    have := pushKappas_le D.logMem D.hs hhl hm hh b hb; unfold pkap; omega
  rw [bPush]
  refine Completes.append (m := 417) (P := fun σ' => (σ' (.n 5) = sq ∧ σ' (.n 163) = P.bk ∧
      σ' (.n (pushP 36)) = gen ^ pS D 36 ∧ Fixes σ' (pushPtrs D sq 36)) ∧ Fixes σ' [(4, lp)])
    (by omega) (by omega)
    (numBelow_of_B (by decide +kernel)) ?_ fun σ2 e2 h2 => ?_
  · refine Completes.append (m := 273) (P := fun σ' => σ' (.n 4) = lp ∧ σ' (.n 5) = sq ∧
        σ' (.n 163) = P.bk ∧ σ' (.n 272) = gen ^ pS D 0 ∧ Fixes σ' (pushPtrs D sq 0)) (by omega)
      (by omega)
      (numBelow_of_B (by decide +kernel)) ?_ fun σ1 e1 h1 => ?_
    · refine completes_upds [(270, gen ^ pkap D 0), (271, sq * gen ^ pkap D 0),
        (272, gen ^ 2 ^ pkap D 0)] (by simp) (fun next kret hn => ?_) ?_
      · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds]
        vs_ev
        rw [h5, h163]
        refine ⟨hbk 0 (by omega), rfl, ?_, hn⟩
        rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact (ht _ (hk 0 (by omega))).2
      · vs_ev
        rw [h4, h5, h163]
        refine ⟨rfl, rfl, rfl, by simp [pS], fun p hp => ?_⟩
        simp [pushPtrs] at hp
        subst hp
        simp only [pushK, ↓reduceIte, Nat.reduceAdd]
        vs_ev
    · obtain ⟨i4, i5, i163, i272, iF⟩ := h1
      have := Completes.flatten (C := C) (rd := rd) (blk := pushBlk)
        (st := fun b ↦ 273 + 4 * b) (Inv := fun b σ' ↦ σ' (.n 5) = sq ∧ σ' (.n 163) = P.bk ∧
          σ' (.n (pushP b)) = gen ^ pS D b ∧ Fixes σ' (pushPtrs D sq b)) 36 (fun b _ => by omega)
        numBelow_push
        (fun b hb σ' ⟨j5, j163, jP, jF⟩ => c_pushBlk ht hb (hk (b + 1) (by omega))
          (hbk (b + 1) (by omega)) σ' j5 j163 jP jF) σ1 ⟨i5, i163, i272, iF⟩
      exact this.keep (l := [(4, lp)]) (by intro p hp; simp at hp; subst hp; exact i4) (by simp)
  · obtain ⟨⟨j5, -, jP, jF⟩, j4⟩ := h2
    have j4' : σ2 (.n 4) = lp := j4.get (by simp)
    rw [pushP_eq, pS_total hl] at jP
    refine completes_upds [(417, gen ^ log2Ceil D.pushTotal), (418, P.zeta)] (by simp)
      (fun next kret hn => ?_) ?_
    · simp only [Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil]
      vs_ev
      rw [jP, j4', j5]
      exact ⟨hlog, trivial, hn⟩
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
        rcases hp with rfl | rfl <;> simp [upds_n]
      · rw [upds_of_not_mem]
        · exact jF p hp
        · intro q hq
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
          simp only [pushPtrs, List.mem_map, List.mem_range] at hp
          obtain ⟨j, hj, rfl⟩ := hp
          have := pushK_lt j
          rcases hq with rfl | rfl <;> simp <;> omega

theorem bPush_free : Stmt.freeInList ["log2_ceil_in_the_exponent__L0_L34"] bPush = true := by
  decide +kernel

/-- **The push side under any semantics** (`c_push`). -/
theorem c_pushB {lp sq : E}
    (ht : ExpTables rd lp sq) (hl : D.rows.length = 6) (hm : D.logMem ≤ 32)
    (hh : ∀ h ∈ D.hs, h < 29)
    (hbk : ∀ b < 37, LoadHolds rd P.bk b (gen ^ pkap D b))
    (hlog : C "log2_ceil_in_the_exponent__L0_L34" [gen ^ D.pushTotal, lp, sq]
      [gen ^ log2Ceil D.pushTotal]) (σ : Val)
    (hσ : Fixes σ [(4, lp), (5, sq), (163, P.bk)]) :
    CompletesB S C rd 270 419 bPush σ (fun σ' => Fixes σ' (pushOut D P sq)) :=
  CompletesB.of_free bPush_free (c_pushE ht hl hm hh hbk hlog σ hσ)

/-- The deployed `c_push`, from the block's under any semantics at `blakeDeployed`. -/
theorem c_push_of_comp {lp sq : E}
    (ht : ExpTables rd lp sq) (hl : D.rows.length = 6) (hm : D.logMem ≤ 32)
    (hh : ∀ h ∈ D.hs, h < 29) (hbk : ∀ b < 37, LoadHolds rd P.bk b (gen ^ pkap D b))
    {bytecode : List K} (hC : VsCallsOk C bytecode D P lp sq) (σ : Val)
    (hσ : Fixes σ [(4, lp), (5, sq), (163, P.bk)]) :
    Completes C rd 270 419 bPush σ (fun σ' => Fixes σ' (pushOut D P sq)) :=
  (c_pushB (S := blakeDeployed) ht hl hm hh hbk hC.log2Push σ hσ).of_deployed

/-! ## The root -/

/-- The values the root leaves, the state after it `cv10` (`rootOut`). -/
def rootOutC (D : VsData) (cv10 : Digest) : List (ℕ × E) :=
  [(419, D.x0), (434, D.x1), (447, (digestScalars cv10).1), (448, (digestScalars cv10).2)]

theorem rootOutC_deployed : rootOutC D D.cv10 = rootOut D := rfl

/-- **The stack's root over a completeness model** (G:2131-2135, `c_root`): its two words read
at offsets `8`, `9`, absorbed from `cvA` into the model's `cv10`, both canonical. -/
theorem c_root_comp {CM : CompModel} (σ : Val) (h14 : σ (.n 14) = P.stream) {cvA cv10 : Digest}
    (hs : (σ (.n 134), σ (.n 135)) = digestScalars cvA)
    (hA : obsAllM CM.hm cvA [D.x0, D.x1] = some cv10)
    (h8 : LoadHolds rd P.stream 8 D.x0) (h9 : LoadHolds rd P.stream 9 D.x1)
    (hc0 : C "assert_canonical" [D.x0] [0]) (hc1 : C "assert_canonical" [D.x1] [0]) :
    CompletesB CM.sem C rd 419 451 bRoot σ (fun σ' => Fixes σ' (rootOutC D cv10)) := by
  rw [show [D.x0, D.x1] = [D.x0] ++ [D.x1] from rfl, obsAllM_append, obsAllM_singleton,
    Option.bind_eq_some_iff] at hA
  obtain ⟨cvx, hx, hx'⟩ := hA
  rw [obsAllM_singleton] at hx'
  rw [bRoot]
  refine CompletesB.append (m := 449) (P := fun σ' => Fixes σ' (rootOutC D cv10))
    (by omega) (by omega) (numBelow_of_B (by decide +kernel)) ?_ fun σ2 _ h2 => ?_
  · refine CompletesB.append (m := 434) (P := fun σ' => σ' (.n 419) = D.x0 ∧ σ' (.n 14) = P.stream ∧
        (σ' (.n 432), σ' (.n 433)) = digestScalars cvx) (by omega)
      (by omega) (numBelow_of_B (by decide +kernel)) ?_ fun σ1 e1 h1 => ?_
    · exact completesB_fsNextT_comp (b := 419) ⟨134, by omega, rfl⟩ ⟨135, by omega, rfl⟩
        ⟨14, by omega, rfl⟩ hs (by rw [h14]; exact h8) hx fun σ' e hb ho =>
          ⟨hb, by rw [e.apply (by omega)]; exact h14, ho⟩
    · obtain ⟨h419, h14', h432⟩ := h1
      exact completesB_fsNextT_comp (b := 434) ⟨432, by omega, rfl⟩ ⟨433, by omega, rfl⟩
        ⟨14, by omega, rfl⟩ h432 (by rw [h14']; exact h9) hx' fun σ' e hb ho => by
          intro p hp
          simp only [rootOutC, List.mem_cons, List.mem_nil_iff, or_false] at hp
          rcases hp with rfl | rfl | rfl | rfl
          · rw [e.apply (by omega)]; exact h419
          · exact hb
          · exact congrArg Prod.fst ho
          · exact congrArg Prod.snd ho
  · refine completesB_upds [(449, 0), (450, 0)] (by simp) (fun next kret hn => ?_) ?_
    · simp only [Stmt.HoldsListB, Stmt.HoldsB, List.map_cons, List.map_nil]
      vs_ev
      rw [h2.get (k := 419) (e := D.x0) (by simp [rootOutC]),
        h2.get (k := 434) (e := D.x1) (by simp [rootOutC])]
      exact ⟨hc0, hc1, hn⟩
    · intro p hp
      rw [upds_of_not_mem]
      · exact h2 p hp
      · intro q hq
        simp only [rootOutC, List.mem_cons, List.mem_nil_iff, or_false] at hp
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl <;> simp

/-- The deployed `c_root`, from the model's at `CompModel.deployed`. -/
theorem c_root_of_comp (σ : Val) (h14 : σ (.n 14) = P.stream)
    (hs : (σ (.n 134), σ (.n 135)) = digestScalars (obsAll D.cv0 D.ann))
    (h8 : LoadHolds rd P.stream 8 D.x0) (h9 : LoadHolds rd P.stream 9 D.x1) {bytecode : List K}
    {lp sq : E} (hC : VsCallsOk C bytecode D P lp sq) :
    Completes C rd 419 451 bRoot σ (fun σ' => Fixes σ' (rootOut D)) :=
  (c_root_comp (CM := CompModel.deployed) σ h14 hs (obsAllM_hm_deployed _ _) h8 h9 hC.canon0
    hC.canon1).of_deployed

end
end LeanVM.Guest.B1.VerifySub
