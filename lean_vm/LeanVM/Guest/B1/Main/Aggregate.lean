/-
  LeanVM.Guest.B1.Main.Aggregate

  `aggregate_claims`' soundness: its core IR writes the batching (`Node.batch`) of the children
  whose words the memory holds.
-/

module

public import LeanVM.Guest.B1.Main.AggBody
public import LeanVM.Guest.B1.Sumcheck.Batch
public import LeanVM.Guest.Batch.Def

/-!
# `aggregate_claims` (TRIAGE G #97)

`aggregate_claims_holds : aggregate_claims_sound_Spec`. For `n_children_g = g^m`, the hints are
the rounds at `bc_sumcheck_msgs` (`batch_sumcheck`'s statement, B1-a) and `bc_star_hint`, and the
claim written at `defer_stmt` is the sumcheck's point and the hint. For `m` children whose words
the memory holds (`ChildWordsAt`), `batch_fs` reads `Node.batch` on the carried sponge:

* the absorbing rows (`__loop24`, `l25_step`) carry the sponge after the count and the first `c`
  children's words (`absorb_rows`);
* the squeezing rows (`__loop25`, `l26_step`) carry the sponge after `c` children's lambdas
  (`sq2F`), and their running claim is the lambdas' combination of the children's values
  (`squeeze_rows`); the last one feeds `batch_sumcheck__L23`;
* the weights (`__loop26`, `l27_step`) are the lambdas' combination of the claims' equality
  weights at the sumcheck's point (`weight_rows`), and the body checks that the final claim is
  the hint times the last.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

variable {rd : Reader}

/-! ## Bookkeeping -/

theorem pend_absorbAll : ∀ (xs : List E) (s : Fs) (t : ℕ), 1 ≤ s.pend.length →
    s.pend.length ≤ 4 → (s.absorbAll xs t).pend.length = (s.pend.length - 1 + xs.length) % 4 + 1
  | [], s, t, h1, h4 => by
    show s.pend.length = _
    simp only [List.length_nil]
    omega
  | x :: xs, s, t, h1, h4 => by
    show ((s.absorb x t).absorbAll xs t).pend.length = _
    by_cases hf : s.pend.length = 4
    · have e : s.absorb x t = ⟨capOf s.perm, [(x, t)]⟩ := by simp [Fs.absorb, hf, rateScalars]
      rw [e, pend_absorbAll xs _ t (by simp) (by simp)]
      simp only [List.length_cons, List.length_nil]
      omega
    · have e : s.absorb x t = ⟨s.cap, s.pend ++ [(x, t)]⟩ := by
        simp [Fs.absorb, hf, rateScalars]
      rw [e, pend_absorbAll xs _ t (by simp) (by simp; omega)]
      simp only [List.length_append, List.length_cons, List.length_nil, List.length_cons]
      omega

theorem sq2F_snoc : ∀ (n : ℕ) (s : Fs), sq2F (n + 1) s =
    ((sq2F n s).1 ++ [((sq2F n s).2.squeeze.1, (sq2F n s).2.squeeze.2.squeeze.1)],
      (sq2F n s).2.squeeze.2.squeeze.2)
  | 0, _ => rfl
  | n + 1, s => by
    have h1 : sq2F (n + 1 + 1) s = ((s.squeeze.1, s.squeeze.2.squeeze.1) ::
        (sq2F (n + 1) s.squeeze.2.squeeze.2).1, (sq2F (n + 1) s.squeeze.2.squeeze.2).2) := rfl
    have h2 : sq2F (n + 1) s = ((s.squeeze.1, s.squeeze.2.squeeze.1) ::
        (sq2F n s.squeeze.2.squeeze.2).1, (sq2F n s.squeeze.2.squeeze.2).2) := rfl
    rw [h1, h2, sq2F_snoc n]
    rfl

/-- The `c`-th pair of lambdas. -/
def lamOf (s : Fs) (c : ℕ) : E × E := ((sq2F c s).2.squeeze.1, (sq2F c s).2.squeeze.2.squeeze.1)

theorem sq2F_fst : ∀ (n : ℕ) (s : Fs), (sq2F n s).1 = (List.range n).map (lamOf s)
  | 0, _ => rfl
  | n + 1, s => by
    rw [sq2F_snoc, sq2F_fst n, List.range_succ, List.map_append]
    rfl

theorem sumE_snoc (xs : List E) (y : E) : sumE (xs ++ [y]) = sumE xs + y := by
  simp [sumE, List.foldl_append]

/-- A running sum over the first `c + 1` children. -/
theorem zip_prefix {α : Type} (F : α → E × E → E) (cs : List α) (L : ℕ → E × E) {c : ℕ}
    (hc : c < cs.length) :
    sumE (List.zipWith F (cs.take (c + 1)) ((List.range (c + 1)).map L)) =
      sumE (List.zipWith F (cs.take c) ((List.range c).map L)) + F cs[c] (L c) := by
  rw [List.take_succ_eq_append_getElem hc, List.range_succ, List.map_append,
    List.zipWith_append (by simp; omega)]
  simp [sumE, List.foldl_append]

theorem bsRun_len : ∀ (rounds : List (E × E)) (claim : E) (s : Fs),
    (bsRun rounds claim s).1.1.length = rounds.length
  | [], _, _ => rfl
  | (_, _) :: rest, _, _ => by simp [bsRun, bsRun_len rest]

/-- A row read at other words. -/
theorem rowRel_congr {p p' : E} {s : Fs} (h : RowRel rd p s)
    (he : ∀ k < 13, memAt rd p' k = memAt rd p k) : RowRel rd p' s := by
  obtain ⟨hc, hl, hk⟩ := h
  refine ⟨?_, hl, fun k hk4 => ?_⟩
  · rw [hc, rowCap, rowCap]
    exact List.map_congr_left fun i hi => (he i (by simp at hi; omega)).symm
  · rw [he (5 + 2 * k) (by omega), he (6 + 2 * k) (by omega)]
    exact hk k hk4

theorem memAt_of_reads {p : E} {xs : List E} (h : ReadsAt rd p xs) {k : ℕ} (hk : k < xs.length) :
    memAt rd p k = xs.getD k 0 := by
  rw [memAt_of_load (h k hk), List.getD_eq_getElem _ _ hk]

/-! ## A child's words -/

theorem childCells_eq (cc : ChildClaims) (h1 : cc.fresh.bytecodePoint.length = 23)
    (h2 : cc.carried.bytecodePoint.length = 23) :
    Batch.childCells cc = cc.words ++ [0, 0] := by
  have hl : cc.words.length = 50 := by
    simp [ChildClaims.words, DeferredClaim.cells, h1, h2]
  rw [Batch.childCells, padRate, hl]
  rfl

/-- **A child's words, as the absorbing loop reads them.** -/
theorem kid_words {cpi cfresh ccarried : E} {c : ℕ} {cc : ChildClaims}
    (h : ChildWordsAt rd cpi cfresh ccarried c cc) :
    memAt rd (cfresh * (gen ^ c) ^ 24) 23 = cc.fresh.bytecodeValue ∧
    memAt rd (ccarried * (gen ^ c) ^ 24) 23 = cc.carried.bytecodeValue ∧
    memRun rd (cfresh * (gen ^ c) ^ 24) 23 = cc.fresh.bytecodePoint ∧
    memRun rd (ccarried * (gen ^ c) ^ 24) 23 = cc.carried.bytecodePoint ∧
    l25Words rd cpi cfresh ccarried (gen ^ c) = Batch.childCells cc := by
  obtain ⟨h1, h2, hp0, hp1, hf, hc⟩ := h
  have e24 : (gen ^ c) ^ 24 = gen ^ (24 * c) := by rw [← pow_mul, mul_comm]
  have e2 : (gen ^ c) ^ 2 = gen ^ (2 * c) := by rw [← pow_mul, mul_comm]
  have b23 : bytecodeVars = 23 := rfl
  rw [b23] at h1 h2
  rw [e24]
  have hfl : (DeferredClaim.cells cc.fresh).length = 24 := by simp [DeferredClaim.cells, h1]
  have hcl : cc.carried.cells.length = 24 := by simp [DeferredClaim.cells, h2]
  have pf := (readsAt_append.mp (show ReadsAt rd _ (cc.fresh.bytecodePoint ++
    [cc.fresh.bytecodeValue]) from hf)).1
  have pc := (readsAt_append.mp (show ReadsAt rd _ (cc.carried.bytecodePoint ++
    [cc.carried.bytecodeValue]) from hc)).1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [memAt_of_reads hf (by omega)]
    simp [DeferredClaim.cells, List.getD_eq_getElem?_getD, h1]
  · rw [memAt_of_reads hc (by omega)]
    simp [DeferredClaim.cells, List.getD_eq_getElem?_getD, h2]
  · rw [readsAt_memRun pf, h1]
  · rw [readsAt_memRun pc, h2]
  · rw [childCells_eq cc h1 h2]
    have hwl : (cc.words ++ [0, 0]).length = 52 := by
      simp [ChildClaims.words, DeferredClaim.cells, h1, h2]
    refine list_eq_of_getD (n := 52) (by simp [l25Words]) hwl fun w hw => ?_
    have lhs : (l25Words rd cpi cfresh ccarried (gen ^ c)).getD w 0 =
        l25Word rd cpi cfresh ccarried (gen ^ c) w := by
      simp [l25Words, List.getD_eq_getElem?_getD, hw]
    rw [lhs, l25Word, ChildClaims.words, e2, e24]
    generalize hA2 : ([(digestScalars cc.publicInput).1, (digestScalars cc.publicInput).2] :
      List E) = A2
    have hA : A2.length = 2 := by rw [← hA2]; rfl
    have hAF : (A2 ++ DeferredClaim.cells cc.fresh).length = 26 := by simp [hA, hfl]
    have hAFC : (A2 ++ DeferredClaim.cells cc.fresh ++ cc.carried.cells).length = 50 := by
      simp [hA, hfl, hcl]
    by_cases ha : w < 50
    · rw [List.getD_append (A2 ++ DeferredClaim.cells cc.fresh ++ cc.carried.cells) [0, 0] 0 w
        (by rw [hAFC]; exact ha)]
      by_cases hb : w < 26
      · rw [List.getD_append (A2 ++ DeferredClaim.cells cc.fresh) cc.carried.cells 0 w
          (by rw [hAF]; exact hb)]
        by_cases hc2 : w < 2
        · rw [ite_pos' hc2, List.getD_append A2 (DeferredClaim.cells cc.fresh) 0 w (by rw [hA]; exact hc2),
            ← hA2]
          rcases (show w = 0 ∨ w = 1 by omega) with rfl | rfl
          · exact memAt_of_load ((loadHolds_mul_gen_pow rd _ _ _ _).mpr hp0)
          · exact memAt_of_load ((loadHolds_mul_gen_pow rd _ _ _ _).mpr hp1)
        · rw [ite_neg' hc2, ite_pos' hb,
            List.getD_append_right A2 (DeferredClaim.cells cc.fresh) 0 w (by rw [hA]; omega), hA,
            memAt_of_reads hf (by omega)]
      · rw [ite_neg' (show ¬ w < 2 by omega), ite_neg' hb, ite_pos' ha,
          List.getD_append_right (A2 ++ DeferredClaim.cells cc.fresh) cc.carried.cells 0 w
            (by rw [hAF]; omega), hAF, memAt_of_reads hc (by omega)]
    · rw [ite_neg' (show ¬ w < 2 by omega), ite_neg' (show ¬ w < 26 by omega), ite_neg' ha,
        List.getD_append_right (A2 ++ DeferredClaim.cells cc.fresh ++ cc.carried.cells) [0, 0] 0 w
          (by rw [hAFC]; omega), hAFC]
      rcases (show w = 50 ∨ w = 51 by omega) with rfl | rfl <;> rfl

/-! ## The rows -/

/-- **The absorbing rows**: row `c` carries the sponge after the count and the first `c`
children's words. -/
theorem absorb_rows {absorb cpi cfresh lfT ccarried lcT : E} {m : ℕ} {cs : List ChildClaims}
    (hcl : cs.length = m)
    (hcw : ∀ c (hc : c < cs.length), ChildWordsAt rd cpi cfresh ccarried c cs[c])
    (L25 : ∀ c < m, L25Step rd absorb cfresh lfT ccarried lcT cpi (gen ^ c))
    (h0 : RowRel rd absorb (aggS0.absorbAll (Batch.headCells m) dsObserve))
    (hp0 : (aggS0.absorbAll (Batch.headCells m) dsObserve).pend.length = 4) :
    ∀ c ≤ m, RowRel rd (absorb * (gen ^ c) ^ 13)
      (aggS0.absorbAll (Batch.headCells m ++ (cs.take c).flatMap Batch.childCells) dsObserve) ∧
      (aggS0.absorbAll (Batch.headCells m ++ (cs.take c).flatMap Batch.childCells)
        dsObserve).pend.length = 4 := by
  intro c
  induction c with
  | zero => intro _; simpa using ⟨h0, hp0⟩
  | succ c ih =>
    intro hc
    obtain ⟨hr, hp⟩ := ih (by omega)
    have hcc : c < cs.length := by omega
    obtain ⟨-, -, -, -, hw⟩ := kid_words (hcw c hcc)
    obtain ⟨-, -, hstep⟩ := L25 c (by omega)
    rw [List.take_succ_eq_append_getElem hcc, List.flatMap_append, List.flatMap_singleton,
      ← List.append_assoc, absorbAll_append, ← hw]
    refine ⟨?_, ?_⟩
    · have := hstep _ hp hr
      rwa [show absorb * (gen ^ c) ^ 13 * gen ^ 13 = absorb * (gen ^ (c + 1)) ^ 13 by ring]
        at this
    · rw [pend_absorbAll, hp]
      · simp [l25Words]
      · omega
      · omega

/-- **The squeezing rows**: row `c` carries the sponge after `c` children's lambdas, and its
running claim is their combination of the first `c` children's values. -/
theorem squeeze_rows {absorb cpi cfresh lfT ccarried lcT sqT lamT : E} {m : ℕ}
    {cs : List ChildClaims} (hcl : cs.length = m)
    (hcw : ∀ c (hc : c < cs.length), ChildWordsAt rd cpi cfresh ccarried c cs[c])
    (L25 : ∀ c < m, L25Step rd absorb cfresh lfT ccarried lcT cpi (gen ^ c))
    (L26 : ∀ c < m, L26Step rd sqT lamT lfT lcT (gen ^ c))
    (h0 : RowRel rd sqT (aggAbs cs)) (hz : memAt rd sqT 13 = 0) :
    ∀ c ≤ m, RowRel rd (sqT * (gen ^ c) ^ 14) (sq2F c (aggAbs cs)).2 ∧
      memAt rd (sqT * (gen ^ c) ^ 14) 13 = sumE (List.zipWith (fun c l ↦
        l.1 * c.fresh.bytecodeValue + l.2 * c.carried.bytecodeValue) (cs.take c)
        ((List.range c).map (lamOf (aggAbs cs)))) := by
  intro c
  induction c with
  | zero => intro _; simpa using ⟨h0, hz⟩
  | succ c ih =>
    intro hc
    obtain ⟨hr, hacc⟩ := ih (by omega)
    have hcc : c < cs.length := by omega
    obtain ⟨-, -, hr', hst⟩ := L26 c (by omega) _ hr
    obtain ⟨hp1, hp2, -⟩ := L25 c (by omega)
    obtain ⟨fv, cv, -, -, -⟩ := kid_words (hcw c hcc)
    have e14 : sqT * (gen ^ (c + 1)) ^ 14 = sqT * (gen ^ c) ^ 14 * gen ^ 14 := by ring
    refine ⟨?_, ?_⟩
    · rw [sq2F_snoc, e14]; exact hr'
    · rw [e14, memAt_of_load ((loadHolds_mul_gen_pow rd _ 14 13 _).mpr hst),
        zip_prefix _ _ _ hcc, ← hacc, memAt_of_load hp1, memAt_of_load hp2, fv, cv]
      simp only [lamOf]
      ring

/-- **The weights**: `w[c]` is the lambdas' combination of the first `c` children's equality
weights at `r`. -/
theorem weight_rows {absorb cpi cfresh lfT ccarried lcT wT lamT pt : E} {r : List E} {m : ℕ}
    {cs : List ChildClaims} {s : Fs} (hcl : cs.length = m)
    (hcw : ∀ c (hc : c < cs.length), ChildWordsAt rd cpi cfresh ccarried c cs[c])
    (L25 : ∀ c < m, L25Step rd absorb cfresh lfT ccarried lcT cpi (gen ^ c))
    (L27 : ∀ c < m, L27Step rd lfT lcT pt wT lamT (gen ^ c))
    (hlam : ∀ c < m, memAt rd (lamT * (gen ^ c) ^ 2) 0 = (lamOf s c).1 ∧
      memAt rd (lamT * (gen ^ c) ^ 2) 1 = (lamOf s c).2)
    (hpt : memRun rd pt 23 = r) (hz : memAt rd wT 0 = 0) :
    ∀ c ≤ m, memAt rd (wT * gen ^ c) 0 = sumE (List.zipWith (fun c l ↦
      l.1 * eqEval c.fresh.bytecodePoint r + l.2 * eqEval c.carried.bytecodePoint r) (cs.take c)
      ((List.range c).map (lamOf s))) := by
  intro c
  induction c with
  | zero => intro _; simpa [sumE] using hz
  | succ c ih =>
    intro hc
    have hcc : c < cs.length := by omega
    have hst := L27 c (by omega)
    obtain ⟨hp1, hp2, -⟩ := L25 c (by omega)
    obtain ⟨-, -, fp, cp, -⟩ := kid_words (hcw c hcc)
    obtain ⟨l1, l2⟩ := hlam c (by omega)
    rw [show wT * gen ^ (c + 1) = wT * gen ^ c * gen ^ 1 by ring,
      memAt_of_load ((loadHolds_mul_gen_pow rd _ 1 0 _).mpr hst), zip_prefix _ _ _ hcc,
      ih (by omega), memAt_of_load hp1, memAt_of_load hp2, fp, cp, hpt, l1, l2]
    ring

/-! ## `aggregate_claims` -/

theorem headCells_eq (m : ℕ) : Batch.headCells m = [gen ^ m, 0, 0, 0] := rfl

theorem absorb_head (m : ℕ) : aggS0.absorbAll (Batch.headCells m) dsObserve =
    ⟨capOf batchSeed, [gen ^ m, 0, 0, 0].map (·, dsObserve)⟩ := by
  rw [headCells_eq, absorbAll_short aggS0 _ dsObserve (by simp [aggS0])]
  rfl

/-- The sumcheck's rounds `aggregate_claims` hints, read off the memory at `bc_sumcheck_msgs`. -/
noncomputable def aggRounds (rd : Reader) (σ : Val) : List (E × E) :=
  (List.range 23).map fun k => (memAt rd (σ (.n 5)) (2 * k), memAt rd (σ (.n 5)) (2 * k + 1))

/-- **`aggregate_claims`' hints**, read off its valuation and the memory: the rounds at
`bc_sumcheck_msgs`, the bytecode's value `bc_star_hint`. -/
noncomputable def aggHints (rd : Reader) (σ : Val) : BatchHints := ⟨aggRounds rd σ, σ (.n 6)⟩

theorem pairs_getD : ∀ (l : List (E × E)) (i : ℕ),
    (l.flatMap fun g => [g.1, g.2]).getD (2 * i) 0 = (l.getD i 0).1 ∧
      (l.flatMap fun g => [g.1, g.2]).getD (2 * i + 1) 0 = (l.getD i 0).2
  | [], _ => by simp
  | p :: l, 0 => by simp
  | p :: l, i + 1 => by
    have ih := pairs_getD l i
    simp only [List.flatMap_cons, List.cons_append, List.nil_append] at ih ⊢
    rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring, List.getD_cons_succ, List.getD_cons_succ,
      List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ]
    exact ih

/-- Rounds read from memory are the memory's. -/
theorem rounds_of_reads {rd : Reader} {p : E} {rounds : List (E × E)} {n : ℕ}
    (hl : rounds.length = n) (h : ReadsAt rd p (rounds.flatMap fun g => [g.1, g.2])) :
    rounds = (List.range n).map fun k => (memAt rd p (2 * k), memAt rd p (2 * k + 1)) := by
  have hlen : (rounds.flatMap fun g => [g.1, g.2]).length = 2 * n := by
    simp [List.length_flatMap, hl, mul_comm]
  refine List.ext_getElem (by simp [hl]) fun k h1 h2 => ?_
  have hk : k < n := by omega
  obtain ⟨e0, e1⟩ := pairs_getD rounds k
  have l0 := h (2 * k) (by omega)
  have l1 := h (2 * k + 1) (by omega)
  rw [← List.getD_eq_getElem _ 0, e0] at l0
  rw [← List.getD_eq_getElem _ 0, e1] at l1
  simp only [List.getElem_map, List.getElem_range]
  rw [memAt_of_load l0, memAt_of_load l1, List.getD_eq_getElem _ _ h1]

/-- **`aggregate_claims`, its hints named**: on a valuation of its body (its calls under a
relation below `coreProgram.Rel`), the meaning holds with the hints `aggHints rd σ`. -/
def MeaningAggregateClaimsW (rd : Reader) (h : BatchHints) : List E → List E → Prop
  | [ncg, cpi, cfresh, ccarried, dst], rets => ∀ m, 1 ≤ m → m ≤ 16 → ncg = gen ^ m →
      rets = [] ∧ ∃ out : DeferredClaim,
        out.bytecodePoint.length = bytecodeVars ∧ ReadsAt rd dst out.cells ∧
        ∀ cs : List ChildClaims, cs.length = m →
          (∀ c (hc : c < cs.length), ChildWordsAt rd cpi cfresh ccarried c cs[c]) →
          batch cs h = some out
  | _, _ => False

set_option maxHeartbeats 1000000 in
/-- **`aggregate_claims` at a valuation** writes the batching, with the hints `aggHints rd σ`, of
the children whose words the memory holds. -/
theorem aggregate_claims_val {C : CallRel} {rd : Reader} (hle : CallRel.Le C (coreProgram.Rel rd))
    {σ : Val} {args rets : List E} (hpar : Data.core29.params.map σ = args)
    (hbC : Stmt.HoldsList C rd σ (Fn.body Data.core29) False (fun rs => rs = rets)) :
    MeaningAggregateClaimsW rd (aggHints rd σ) args rets := by
  have hb := holdsList_mono hle _ id (fun _ h => h) hbC
  have hok := agg_ok
  simp only [aggOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hflat, hparams⟩, hseed⟩, hp0⟩, hc23⟩, hp23⟩, hc33⟩,
    hp33⟩, hc43⟩, hp43⟩, hrate⟩, hg25⟩, hm69⟩, hcopy⟩, hc93⟩, hl93⟩, hg26⟩, hm102⟩, hl103⟩,
    hl105⟩, hbs⟩, hc119⟩, hl119⟩, hg27⟩, hm123⟩, hl124⟩, hm125⟩, hae⟩, hout⟩, hl6⟩ := hok
  rw [hparams] at hpar
  subst hpar
  rw [agg_shape, holdsList_append] at hb
  obtain ⟨hall, hret⟩ := holdsList_flat aggP hflat _ _ hb
  have hr : rets = [] := by
    simp only [Stmt.HoldsList, Stmt.Holds, List.map_nil] at hret
    exact hret.symm
  subst hr
  have hat := atoms_of_flat hall
  simp only [List.map_cons, List.map_nil, MeaningAggregateClaimsW]
  intro m hm1 hm16 hN
  refine ⟨trivial, ?_⟩
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true] at hseed hrate hcopy hl105 hout
  -- the loops
  have L25 : ∀ c < m, L25Step rd (σ (.n 60)) (σ (.n 2)) (σ (.n 7)) (σ (.n 3)) (σ (.n 8))
      (σ (.n 1)) (gen ^ c) :=
    loop_sound (f := "__loop24")
      (ps := [σ (.n 0), σ (.n 60), σ (.n 2), σ (.n 7), σ (.n 3), σ (.n 8), σ (.n 1)])
      (by unfold ordG; omega) hN
      (fun y hy => by
        obtain ⟨h1, h2⟩ := l25_step hy
        exact ⟨h1 _ _ _ _ _ _ _ rfl, h2⟩)
      (fun hne => by simpa using guard_sound hg25 hall hne)
  have L26 : ∀ c < m, L26Step rd (σ (.n 79)) (σ (.n 71)) (σ (.n 7)) (σ (.n 8)) (gen ^ c) :=
    loop_sound (f := "__loop25") (ps := [σ (.n 0), σ (.n 79), σ (.n 71), σ (.n 7), σ (.n 8)])
      (by unfold ordG; omega) hN
      (fun y hy => by
        obtain ⟨h1, h2⟩ := l26_step hy
        exact ⟨h1 _ _ _ _ _ rfl, h2⟩)
      (fun hne => by simpa using guard_sound hg26 hall hne)
  have L27 : ∀ c < m, L27Step rd (σ (.n 7)) (σ (.n 8)) (σ (.n 104)) (σ (.n 118)) (σ (.n 71))
      (gen ^ c) :=
    loop_sound (f := "__loop26")
      (ps := [σ (.n 0), σ (.n 7), σ (.n 8), σ (.n 104), σ (.n 118), σ (.n 71)])
      (by unfold ordG; omega) hN
      (fun y hy => by
        obtain ⟨h1, h2⟩ := l27_step hy
        exact ⟨h1 _ _ _ _ _ _ rfl, h2⟩)
      (fun hne => by simpa using guard_sound hg27 hall hne)
  -- the sumcheck
  have hbsm := (batch_sumcheck_holds rd _ _).mp (call_of_flat hall hbs)
  simp only [List.map_cons, List.map_nil] at hbsm
  obtain ⟨-, rounds, hrl, hrd, hpt, hrets⟩ := hbsm
  have hrnd : rounds = aggRounds rd σ := rounds_of_reads hrl hrd
  have h115 : σ (.n 115) = (bsRun rounds (σ (.n 103)) ⟨[σ (.n 105), σ (.n 106), σ (.n 107),
      σ (.n 108), σ (.n 109)], []⟩).1.2 := by
    have := congrArg List.getLast? hrets
    simpa using this
  have hptl : (bsRun rounds (σ (.n 103)) ⟨[σ (.n 105), σ (.n 106), σ (.n 107), σ (.n 108),
      σ (.n 109)], []⟩).1.1.length = 23 := by rw [bsRun_len, hrl]
  refine ⟨⟨(bsRun rounds (σ (.n 103)) ⟨[σ (.n 105), σ (.n 106), σ (.n 107),
    σ (.n 108), σ (.n 109)], []⟩).1.1, σ (.n 6)⟩, hptl, ?_, ?_⟩
  · -- the claim written
    intro k hk
    simp only [DeferredClaim.cells, List.length_append, List.length_cons, List.length_nil,
      hptl] at hk
    by_cases hk23 : k < 23
    · rw [show (DeferredClaim.cells ⟨(bsRun rounds (σ (.n 103)) ⟨[σ (.n 105), σ (.n 106),
        σ (.n 107), σ (.n 108), σ (.n 109)], []⟩).1.1, σ (.n 6)⟩)[k] = _ from
        List.getElem_append_left (by rw [hptl]; exact hk23)]
      obtain ⟨h1, h2⟩ := hout k hk23
      have e := loadHolds_unique (load_sound h1 hat) (hpt k (by rw [hptl]; exact hk23))
      rw [← e]
      exact load_sound h2 hat
    · have hk' : k = 23 := by omega
      subst hk'
      rw [show (DeferredClaim.cells ⟨(bsRun rounds (σ (.n 103)) ⟨[σ (.n 105), σ (.n 106),
        σ (.n 107), σ (.n 108), σ (.n 109)], []⟩).1.1, σ (.n 6)⟩)[23] = σ (.n 6) by
          simp [DeferredClaim.cells, List.getElem_append_right, hptl]]
      exact load_sound hl6 hat
  -- the batching
  intro cs hcl hcw
  have hp60 := hp0
  -- row 0
  have hcap0 : rowCap rd (σ (.n 60)) = capOf batchSeed := by
    refine list_eq_of_getD (n := 5) (by simp [rowCap]) (by simp [capOf]) fun i hi => ?_
    obtain ⟨hcst, hld⟩ := hseed i hi
    rw [← seed_cells i hi, ← const_sound hcst hat, ← memAt_of_load (load_sound hld hat)]
    simp [rowCap, List.getD_eq_getElem?_getD, hi]
  have hrow0 : RowRel rd (σ (.n 60)) (aggS0.absorbAll (Batch.headCells m) dsObserve) := by
    rw [absorb_head, ← hcap0]
    refine rowRel_full (by simp) fun j hj => ?_
    obtain ⟨r1, r2⟩ := hrate j hj
    rw [memAt_of_load (load_sound r1 hat), memAt_of_load (load_sound r2 hat)]
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
    · have := packOf_of (packIn_sound hp60 hat)
      rw [hN] at this
      exact this
    · have := packOf_of (packIn_sound hp23 hat)
      rw [const_sound hc23 hat, word_zero] at this
      exact this
    · have := packOf_of (packIn_sound hp33 hat)
      rw [const_sound hc33 hat, word_zero] at this
      exact this
    · have := packOf_of (packIn_sound hp43 hat)
      rw [const_sound hc43 hat, word_zero] at this
      exact this
  have hpend0 : (aggS0.absorbAll (Batch.headCells m) dsObserve).pend.length = 4 := by
    rw [absorb_head]; rfl
  -- the absorbing rows
  obtain ⟨hrowm, -⟩ := absorb_rows hcl hcw L25 hrow0 hpend0 m le_rfl
  rw [List.take_of_length_le (by omega), show Batch.headCells m ++ cs.flatMap Batch.childCells =
    Batch.batchWords cs by rw [Batch.batchWords, hcl]] at hrowm
  have hrow69 : RowRel rd (σ (.n 69)) (aggAbs cs) := by
    rw [monoIs_sound hm69 hat, hN]
    exact hrowm
  -- the first squeezing row
  have hrow79 : RowRel rd (σ (.n 79)) (aggAbs cs) := rowRel_congr hrow69 fun k hk => by
    obtain ⟨h1, h2⟩ := hcopy k hk
    rw [memAt_of_load (load_sound h1 hat), memAt_of_load (load_sound h2 hat)]
  have hz79 : memAt rd (σ (.n 79)) 13 = 0 := by
    rw [memAt_of_load (load_sound hl93 hat), const_sound hc93 hat, word_zero]
  have SQ := squeeze_rows hcl hcw L25 L26 hrow79 hz79
  obtain ⟨hrowM, haccM⟩ := SQ m le_rfl
  rw [List.take_of_length_le (by omega)] at haccM
  have p102 : σ (.n 102) = σ (.n 79) * (gen ^ m) ^ 14 := by
    rw [monoIs_sound hm102 hat, hN]
  -- the sumcheck's sponge and claim
  have hlam : aggLam cs = ((List.range m).map (lamOf (aggAbs cs)),
      ⟨[σ (.n 105), σ (.n 106), σ (.n 107), σ (.n 108), σ (.n 109)], []⟩) := by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [aggLam, hcl, ← sq2F_fst]
    refine Prod.ext rfl ?_
    have hcap := hrowM.1
    have hpend : (sq2F (m' + 1) (aggAbs cs)).2.pend = [] := by rw [sq2F_snoc]; rfl
    rw [← p102] at hcap
    have e : rowCap rd (σ (.n 102)) =
        [σ (.n 105), σ (.n 106), σ (.n 107), σ (.n 108), σ (.n 109)] := by
      have e : ∀ i < 5, memAt rd (σ (.n 102)) i = σ (.n (105 + i)) := fun i hi =>
        memAt_of_load (load_sound (hl105 i hi) hat)
      simp only [rowCap, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
        List.map_nil, List.cons_append]
      rw [e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega)]
    generalize (sq2F (m' + 1) (aggAbs cs)).2 = S at hcap hpend ⊢
    obtain ⟨cap, pend⟩ := S
    simp only at hcap hpend
    rw [hcap, hpend, e]
  have hclaim : Batch.claimBOf cs (aggLam cs).1 = σ (.n 103) := by
    rw [hlam, ← memAt_of_load (load_sound hl103 hat), p102, haccM]
    rfl
  have hrun : aggRun cs ⟨rounds, σ (.n 6)⟩ = bsRun rounds (σ (.n 103))
      ⟨[σ (.n 105), σ (.n 106), σ (.n 107), σ (.n 108), σ (.n 109)], []⟩ := by
    rw [aggRun, hclaim, hlam]
  -- the weight
  have hlamc : ∀ c < m, memAt rd (σ (.n 71) * (gen ^ c) ^ 2) 0 = (lamOf (aggAbs cs) c).1 ∧
      memAt rd (σ (.n 71) * (gen ^ c) ^ 2) 1 = (lamOf (aggAbs cs) c).2 := fun c hc => by
    obtain ⟨l1, l2, -, -⟩ := L26 c hc _ (SQ c hc.le).1
    exact ⟨memAt_of_load l1, memAt_of_load l2⟩
  have hptr : memRun rd (σ (.n 104)) 23 = (bsRun rounds (σ (.n 103)) ⟨[σ (.n 105), σ (.n 106),
      σ (.n 107), σ (.n 108), σ (.n 109)], []⟩).1.1 := by
    rw [readsAt_memRun hpt, hptl]
  have hz118 : memAt rd (σ (.n 118)) 0 = 0 := by
    rw [memAt_of_load (load_sound hl119 hat), const_sound hc119 hat, word_zero]
  have W := weight_rows hcl hcw L25 L27 hlamc hptr hz118 m le_rfl
  rw [List.take_of_length_le (by omega)] at W
  have hw : Batch.bytecodeWeight cs (aggLam cs).1 (bsRun rounds (σ (.n 103))
      ⟨[σ (.n 105), σ (.n 106), σ (.n 107), σ (.n 108), σ (.n 109)], []⟩).1.1 =
      σ (.n 124) := by
    rw [hlam, ← memAt_of_load (load_sound hl124 hat), isMul_sound hm123 hat, hN, W]
    rfl
  -- the check
  rw [show aggHints rd σ = ⟨rounds, σ (.n 6)⟩ by rw [hrnd]; rfl, batch_fs, hrun, hw, ← h115, assertEq_sound hae hat, isMul_sound hm125 hat]
  exact ite_pos' rfl

/-- **`aggregate_claims`' core IR writes the batching of the children whose words the memory
holds.** -/
theorem aggregate_claims_holds : aggregate_claims_sound_Spec := by
  intro rd args rets hrel
  obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem find_aggregate_claims _ _).mp hrel
  have h := aggregate_claims_val (fun _ _ _ h => h) hpar hb
  match args, h with
  | [ncg, cpi, cfresh, ccarried, dst], h =>
    intro m hm1 hm16 hN
    obtain ⟨hr, out, hl, hrd, hb⟩ := h m hm1 hm16 hN
    exact ⟨hr, aggHints rd σ, out, hl, hrd, hb⟩
  | [], h | [_], h | [_, _], h | [_, _, _], h | [_, _, _, _], h => exact h.elim
  | _ :: _ :: _ :: _ :: _ :: _ :: _, h => exact h.elim

end
end LeanVM.Guest.B1.Main
