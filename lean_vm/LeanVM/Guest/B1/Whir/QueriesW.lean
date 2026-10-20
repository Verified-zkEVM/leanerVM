/-
  LeanVM.Guest.B1.Whir.QueriesW

  `opening_queries` and its loop with their openings named: each query's opening an explicit
  function of the loop's frame, the queries' openings what the loop's witness function gives.
-/

module

public import LeanVM.Guest.B1.Whir.Queries
public import LeanVM.Guest.B1.Whir.Cap
public import LeanVM.Guest.B1.Loops

/-!
# `opening_queries`, its openings named (TRIAGE #28, #35)

* `oqOpeningOf … σ`: the opening a frame `σ` of the loop helper reads: the leaf of its hinted row
  (`merkle_leaf_rows`, `rowv σ`), the siblings its hinted children give at the position its bit
  run spells (`merkle_children`, `pathSibs`), then the cap's siblings (`capSibs`, read off the
  hinted `merkle_caps`).
* `QueryOkO … i q o`: query `i` at the position `q` is `QueryOk` with the opening `o`: its leaf is
  the row whose weighted sum the query sum adds, its path the siblings below the cap that climb
  from the leaf's digest to the cap leaf, then the cap's siblings.
* `OqLoopOut … args os` (the loop helper's outcome, its witness `os` the openings of the
  remaining iterations) and `oqLoop_frame_w`: a frame of the loop, given the outcome of its
  recursive call at the openings `wl`, has the outcome at `oqOpeningOf σ :: wl …`.
* `MeaningOpeningQueriesW` and `opening_queries_frame_w`: a frame of `opening_queries`, given the
  loop's outcome at `wl`, has the meaning at the openings `oqQueriesOs wl σ`.

The frame lemmas are stated for any call relation `C`, the loop's recursion a callee.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## The opening of a frame -/

/-- The position a bit run at `dbp` spells, `depth` bits, least significant first. -/
def bitsPos (rd : Reader) (dbp : E) (depth : ℕ) : ℕ :=
  bitsVal (fun l => decide (memAt rd dbp l = 1)) depth

theorem decide_bitE_eq_one (b : Bool) : decide (bitE b = 1) = b := by
  cases b
  · simp only [bitE, Bool.false_eq_true, ↓reduceIte, decide_eq_false_iff_not]
    exact fun h => one_ne_zero h.symm
  · simp [bitE]

theorem bitsPos_eq {dbp : E} {depth q : ℕ} (hq : q < 2 ^ depth)
    (h : ∀ l < depth, LoadHolds rd dbp l (bitE (q.testBit l))) : bitsPos rd dbp depth = q := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [bitsPos, testBit_bitsVal]
  by_cases hi : i < depth
  · simp only [hi, decide_true, Bool.true_and]
    rw [memAt_of_load (h i hi), decide_bitE_eq_one]
  · simp only [hi, decide_false, Bool.false_and]
    exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le hq (Nat.pow_le_pow_right (by decide) (by omega)))).symm

/-- **The opening a frame of the loop helper reads**: the leaf of the hinted row, the siblings
the hinted children give at the position of the bit run `σ (oqK2 + 8)`, then the cap's siblings
from the cap leaf of that position. -/
def oqOpeningOf (base I blocks pd cd : ℕ) (rd : Reader) (σ : Val) : Opening :=
  let q := bitsPos rd (σ (.n (oqK2 base I blocks + 8))) (pd + cd)
  ⟨leafWords base I (rowv σ), pathSibs (fun k => σ (.n (oqP base I blocks + k))) q pd ++
    capSibs rd (σ (.n 7)) cd (2 ^ cd + q / 2 ^ pd)⟩

/-- **Query `i` at the position `q` with the opening `o`**: `QueryOk` with the leaf `o.leaf` and
the siblings below the cap that start `o.path`, the rest of `o.path` the cap's siblings from the
cap leaf of `q`. -/
def QueryOkO (base I depth cd : ℕ) (rd : Reader) (rew qsc qw qbp flags cap : E) (i q : ℕ)
    (o : Opening) : Prop :=
  ∃ sibs, o.path = sibs ++ capSibs rd cap cd (2 ^ cd + q / 2 ^ (depth - cd)) ∧
    QueryOkW base I depth cd rd rew qsc qw qbp flags cap i q o.leaf sibs

theorem QueryOkO.queryOk {base I depth cd : ℕ} {rew qsc qw qbp flags cap : E} {i q : ℕ}
    {o : Opening} (h : QueryOkO base I depth cd rd rew qsc qw qbp flags cap i q o) :
    QueryOk base I depth cd rd rew qsc qw qbp flags cap i q :=
  h.choose_spec.2.queryOk

theorem QueryOk.exists_o {base I depth cd : ℕ} {rew qsc qw qbp flags cap : E} {i q : ℕ}
    (h : QueryOk base I depth cd rd rew qsc qw qbp flags cap i q) :
    ∃ o, QueryOkO base I depth cd rd rew qsc qw qbp flags cap i q o := by
  obtain ⟨leaf, sibs, hw⟩ := h.exists_w
  exact ⟨⟨leaf, sibs ++ capSibs rd cap cd (2 ^ cd + q / 2 ^ (depth - cd))⟩, sibs, rfl, hw⟩

/-- A frame's query at `g^i`, at a position whose bits are at `qbp[i]`, opens with
`oqOpeningOf`. -/
theorem oqOpeningOf_ok {base I blocks pd cd i q : ℕ} (hs : OqShape base I blocks pd cd)
    (hq : q < 2 ^ (pd + cd)) (hx : σ (.n 0) = gen ^ i)
    (hbits : ∀ dbp, LoadHolds rd (σ (.n 5)) i dbp → BitsAt rd dbp q (pd + cd))
    (h : OqSemX base I pd cd rd (σ (.n 2)) (σ (.n 3)) (σ (.n 4)) (σ (.n 5)) (σ (.n 6)) (σ (.n 7))
      (σ (.n 0)) (rowv σ) (σ (.n (oqK2 base I blocks + 8))) (σ (.n (oqP base I blocks + 4 * pd)))
      (fun k => σ (.n (oqP base I blocks + k))) (oqNd base I blocks σ)) :
    QueryOkO base I (pd + cd) cd rd (σ (.n 2)) (σ (.n 3)) (σ (.n 4)) (σ (.n 5)) (σ (.n 6)) (σ (.n 7))
      i q (oqOpeningOf base I blocks pd cd rd σ) := by
  have ldbp := h.2.2.2.1
  rw [hx] at h ldbp
  rw [loadHolds_gen_pow] at ldbp
  have hw := oqSemX_query hs hq hbits h
  obtain ⟨dbp, l1, l2, -⟩ := id hw
  have edbp := loadHolds_unique ldbp l1
  rw [← edbp] at l2
  have hpos := bitsPos_eq hq l2
  refine ⟨pathSibs (fun k => σ (.n (oqP base I blocks + k))) q pd, ?_, ?_⟩
  · simp only [oqOpeningOf, hpos, show pd + cd - cd = pd by omega]
  · exact hw

/-! ## The loop helper -/

/-- **The loop helper's outcome**, the openings `os` of the remaining iterations: from
`x = g^k` to the first `N = g^m`, `os` has an opening per iteration, query `j`'s opening at
every position whose bits are at `qbp[j]`. -/
def OqLoopOut (base I pd cd : ℕ) (rd : Reader) : List E → List Opening → Prop
  | [x, N, rew, qsc, qw, qbp, flags, cap], os =>
      ∀ k, x = gen ^ k → ∃ m, k < m ∧ N = gen ^ m ∧ (∀ j, k < j → j < m → gen ^ j ≠ N) ∧
        os.length = m - k ∧ ∀ j, k ≤ j → j < m → ∀ q, q < 2 ^ (pd + cd) →
          (∀ dbp, LoadHolds rd qbp j dbp → BitsAt rd dbp q (pd + cd)) →
          QueryOkO base I (pd + cd) cd rd rew qsc qw qbp flags cap j q (os.getD (j - k) ⟨[], []⟩)
  | _, _ => False

/-- The loop helper's arguments in its frame. -/
def oqArgs (σ : Val) : List E :=
  [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7)]

/-- The arguments of the frame's recursive call. -/
def oqNextArgs (σ : Val) : List E :=
  [σ (.n 0) * gen, σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7)]

/-- **The openings of a frame of the loop helper and its iterations after**: its own, then what
the witness function `wl` gives of the recursive call, if any. -/
def oqLoopOs (base I blocks pd cd : ℕ) (rd : Reader) (wl : List E → List E → List Opening)
    (σ : Val) : List Opening :=
  oqOpeningOf base I blocks pd cd rd σ ::
    if σ (.n 0) * gen + σ (.n 1) ≠ 0 then wl (oqNextArgs σ) [] else []

/-- **The loop helper's frame, its openings named**: given the outcome of its recursive call at
the openings `wl`, a frame of the loop helper has the outcome at `oqLoopOs`. -/
theorem oqLoop_frame_w {base I blocks pd cd : ℕ} (hs : OqShape base I blocks pd cd) {loop : String}
    {wl : List E → List E → List Opening}
    (hrec : ∀ a, C loop a [] → OqLoopOut base I pd cd rd a (wl a []))
    (h : Stmt.HoldsList C rd σ (oqLoopBody base I blocks pd cd loop) False fun rs => rs = []) :
    OqLoopOut base I pd cd rd (oqArgs σ) (oqLoopOs base I blocks pd cd rd wl σ) := by
  obtain ⟨hx, -, hcall, -⟩ := oqFrame_sound hs h
  intro k hk
  by_cases h0 : σ (.n 0) * gen + σ (.n 1) = 0
  · have hN : σ (.n 1) = gen ^ (k + 1) := by rw [hk] at h0; exact (gen_pow_add_eq_zero_iff k).mp h0
    refine ⟨k + 1, by omega, hN, fun j h1 h2 => by omega, by simp [oqLoopOs, h0], fun j h1 h2 q hq hb => ?_⟩
    obtain rfl : j = k := by omega
    simp only [oqLoopOs, h0, ne_eq, not_true_eq_false, ↓reduceIte, Nat.sub_self, List.getD_cons_zero]
    exact oqOpeningOf_ok hs hq hk hb hx
  · have hc : C loop (oqNextArgs σ) [] := hcall h0
    obtain ⟨m, hkm, hN, hfirst, hlen, hall⟩ := hrec _ hc (k + 1) (by rw [hk, pow_succ])
    refine ⟨m, by omega, hN, fun j h1 h2 => ?_, ?_, fun j h1 h2 q hq hb => ?_⟩
    · rcases Nat.lt_or_ge (k + 1) j with h | h
      · exact hfirst j h h2
      · rw [show j = k + 1 by omega]
        intro he
        exact h0 (by rw [hk]; exact (gen_pow_add_eq_zero_iff k).mpr he.symm)
    · simp only [oqLoopOs, h0, ne_eq, not_false_eq_true, ↓reduceIte, List.length_cons, hlen]
      omega
    · rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
      · simp only [oqLoopOs, Nat.sub_self, List.getD_cons_zero]
        exact oqOpeningOf_ok hs hq hk hb hx
      · simp only [oqLoopOs, h0, ne_eq, not_false_eq_true, ↓reduceIte]
        rw [show j - k = (j - (k + 1)) + 1 by omega, List.getD_cons_succ]
        exact hall j hlt h2 q hq hb

/-! ## `opening_queries` -/

/-- **`opening_queries` with its openings named**: `MeaningOpeningQueries` at the openings `os`,
one per query. -/
def MeaningOpeningQueriesW (base I depth cd n : ℕ) (pos : ℕ → ℕ) (rd : Reader) (qsc : E) :
    List E → List E → List Opening → Prop
  | [cap, flags, qw, qbp, rew, nq], rets, os =>
      nq = gen ^ n ∧ LoadHolds rd qsc 0 0 ∧ os.length = n ∧
        (∀ i < n, QueryOkO base I depth cd rd rew qsc qw qbp flags cap i (pos i) (os.getD i ⟨[], []⟩)) ∧
        ∃ s, LoadHolds rd qsc n s ∧ rets = [s]
  | _, _, _ => False

theorem MeaningOpeningQueriesW.meaning {base I depth cd n : ℕ} {pos : ℕ → ℕ} {qsc : E}
    {args rets : List E} {os : List Opening}
    (h : MeaningOpeningQueriesW base I depth cd n pos rd qsc args rets os) :
    MeaningOpeningQueries base I depth cd n pos rd qsc args rets := by
  match args, h with
  | [_, _, _, _, _, _], ⟨h1, h2, _, h4, h5⟩ => exact ⟨h1, h2, fun i hi => (h4 i hi).queryOk, h5⟩

theorem MeaningOpeningQueries.exists_w {base I depth cd n : ℕ} {pos : ℕ → ℕ} {qsc : E}
    {args rets : List E} (h : MeaningOpeningQueries base I depth cd n pos rd qsc args rets) :
    ∃ os, MeaningOpeningQueriesW base I depth cd n pos rd qsc args rets os := by
  match args, h with
  | [_, _, _, _, _, _], ⟨h1, h2, h4, h5⟩ =>
    have ho := fun i (hi : i < n) => (h4 i hi).exists_o
    have : Nonempty Opening := ⟨⟨[], []⟩⟩
    choose! o ho using ho
    refine ⟨(List.range n).map o, h1, h2, by simp, fun i hi => ?_, h5⟩
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
    exact ho i hi

/-- **The openings of a frame of `opening_queries`**: what the loop's witness function `wl` gives
of the loop's call, if any. -/
def oqQueriesOs (wl : List E → List E → List Opening) (σ : Val) : List Opening :=
  if σ (.n 11) ≠ 0 then
    wl [σ (.n 12), σ (.n 5), σ (.n 4), σ (.n 8), σ (.n 2), σ (.n 3), σ (.n 1), σ (.n 0)] []
  else []

/-- **`opening_queries`' frame, its openings named**: at `n` queries below the order of `g`
whose positions' bits are at `qbp`, given the loop's outcome at the openings `wl`, a frame of
`opening_queries` (its parameters `cap, flags, qw, qbp, rew, g^n` at `σ 0 .. σ 5`) has the
meaning at the openings `oqQueriesOs wl σ` and its chain `σ 8`. -/
theorem opening_queries_frame_w {base I pd cd : ℕ} {loop : String} {wl : List E → List E → List Opening}
    (hrec : ∀ a, C loop a [] → OqLoopOut base I pd cd rd a (wl a [])) {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} (h5 : σ (.n 5) = gen ^ n) (hpre : QueryBits rd (σ (.n 3)) n (pd + cd) pos)
    {rets : List E} (h : Stmt.HoldsList C rd σ (oqBody loop) False fun rs => rs = rets) :
    MeaningOpeningQueriesW base I (pd + cd) cd n pos rd (σ (.n 8))
      [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5)] rets (oqQueriesOs wl σ) := by
  rw [oqBody] at h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, word_gen, word_zero, word_one, List.map_cons,
    List.map_nil] at h
  obtain ⟨h6, h7, -, h9, l9, h10, h11, h12, hK, hrun, h13, l14, hret⟩ := h
  rw [h9] at l9
  rw [h13, h5, loadHolds_gen_pow] at l14
  have hn' : n < 2 ^ 64 - 1 := hn
  by_cases hz : σ (.n 11) = 0
  · -- no query
    have h1 : σ (.n 5) = 1 := by
      rw [h11, h10] at hz; exact (e_add_eq_zero_iff.mp hz).symm
    have hn0 : n = 0 := gen_pow_inj hn' (by decide) (by rw [← h5, h1, pow_zero])
    refine ⟨h5, l9, by simp [oqQueriesOs, hz, hn0], fun i hi => by omega, _, l14, hret.symm⟩
  · obtain ⟨m, -, hN, hfirst, hlen, hall⟩ := hrec _ (hrun hz) 0 (by rw [h12, pow_zero])
    have hmn : m = n := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · exact absurd (gen_pow_inj (by omega) hn' (hN.symm.trans h5)) (by omega)
      · rcases Nat.eq_zero_or_pos n with h0 | hpos
        · apply hz
          rw [h11, h10, h5, h0, pow_zero]; exact e_add_self 1
        · exact hfirst n hpos hgt h5.symm
    refine ⟨h5, l9, ?_, fun i hi => ?_, _, l14, hret.symm⟩
    · simp only [oqQueriesOs, hz, ne_eq, not_false_eq_true, ↓reduceIte, hlen, hmn, Nat.sub_zero]
    · have := hall i (Nat.zero_le i) (by omega) (pos i) (hpre i hi).1 (hpre i hi).2
      simpa only [oqQueriesOs, hz, ne_eq, not_false_eq_true, ↓reduceIte, Nat.sub_zero] using this

/-! ## `opening_queries` as a callee -/

/-- **`opening_queries` named `name` is sound with the openings `w`**: for `n` queries below the
order of `g` whose positions' bits are at `qbp`, its relation on the arguments `args` and the
returns `rets` gives the meaning at the openings `w args rets`. -/
def SoundQueriesW (rd : Reader) (name : String) (base I depth cd : ℕ)
    (w : List E → List E → List Opening) : Prop :=
  ∀ (n : ℕ) (pos : ℕ → ℕ) (cap flags qw qbp rew : E) (rets : List E), n < ordG →
    QueryBits rd qbp n depth pos → coreProgram.Rel rd name [cap, flags, qw, qbp, rew, gen ^ n] rets →
    ∃ qsc, MeaningOpeningQueriesW base I depth cd n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets
      (w [cap, flags, qw, qbp, rew, gen ^ n] rets)

/-- The position of a query is the one its bits at `qbp[i]` spell. -/
theorem queryOk_pos_unique {base I depth cd : ℕ} {rew qsc qw qbp flags cap : E} {i q q' : ℕ}
    (h : QueryOk base I depth cd rd rew qsc qw qbp flags cap i q) (hq : q < 2 ^ depth)
    (hq' : q' < 2 ^ depth) (hb : ∀ dbp, LoadHolds rd qbp i dbp → BitsAt rd dbp q' depth) : q = q' := by
  obtain ⟨dbp, ld, hl, -⟩ := h
  have hB := hb dbp ld
  apply Nat.eq_of_testBit_eq
  intro l
  by_cases hlt : l < depth
  · have e := hB.2 l hlt _ (hl l hlt).2
    have := congrArg (fun x : E => decide (x = 1)) e
    simpa only [decide_bitE_eq_one] using this
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hq (Nat.pow_le_pow_right (by decide) (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hq' (Nat.pow_le_pow_right (by decide) (by omega)))]

/-- The meaning at `pos` is the meaning at every positions whose bits are at `qbp`. -/
theorem MeaningOpeningQueriesW.of_pos {base I depth cd n : ℕ} {pos pos' : ℕ → ℕ} {qsc : E}
    {cap flags qw qbp rew : E} {rets : List E} {os : List Opening}
    (h : MeaningOpeningQueriesW base I depth cd n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets os)
    (hp : QueryBits rd qbp n depth pos) (hp' : QueryBits rd qbp n depth pos') :
    MeaningOpeningQueriesW base I depth cd n pos' rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets os := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, h3, fun i hi => ?_, h5⟩
  have e := queryOk_pos_unique (h4 i hi).queryOk (hp i hi).1 (hp' i hi).1 (hp' i hi).2
  rw [← e]
  exact h4 i hi

/-- `opening_queries`' soundness gives a witness function. -/
theorem exists_soundQueriesW {name : String} {base I depth cd : ℕ}
    (h : ∀ (n : ℕ) (pos : ℕ → ℕ) (cap flags qw qbp rew : E) (rets : List E), n < ordG →
      QueryBits rd qbp n depth pos → coreProgram.Rel rd name [cap, flags, qw, qbp, rew, gen ^ n] rets →
      ∃ qsc, MeaningOpeningQueries base I depth cd n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ w, SoundQueriesW rd name base I depth cd w := by
  classical
  have hex : ∀ args rets : List E, ∃ os : List Opening, ∀ (n : ℕ) (pos : ℕ → ℕ) (cap flags qw qbp rew : E),
      args = [cap, flags, qw, qbp, rew, gen ^ n] → n < ordG → QueryBits rd qbp n depth pos →
      coreProgram.Rel rd name args rets →
      ∃ qsc, MeaningOpeningQueriesW base I depth cd n pos rd qsc args rets os := by
    intro args rets
    by_cases hx : ∃ (n : ℕ) (pos : ℕ → ℕ) (cap flags qw qbp rew : E),
        args = [cap, flags, qw, qbp, rew, gen ^ n] ∧ n < ordG ∧ QueryBits rd qbp n depth pos ∧
          coreProgram.Rel rd name args rets
    · obtain ⟨n, pos, cap, flags, qw, qbp, rew, rfl, hn, hp, hr⟩ := hx
      obtain ⟨qsc, hm⟩ := h n pos cap flags qw qbp rew rets hn hp hr
      obtain ⟨os, hw⟩ := hm.exists_w
      refine ⟨os, fun n' pos' cap' flags' qw' qbp' rew' ha hn' hp' _ => ?_⟩
      simp only [List.cons.injEq, and_true] at ha
      obtain ⟨rfl, rfl, rfl, rfl, rfl, hg⟩ := ha
      obtain rfl := gen_pow_inj hn' hn hg.symm
      exact ⟨qsc, hw.of_pos hp hp'⟩
    · exact ⟨[], fun n pos cap flags qw qbp rew ha hn hp hr =>
        absurd ⟨n, pos, cap, flags, qw, qbp, rew, ha, hn, hp, hr⟩ hx⟩
  choose w hw using hex
  exact ⟨w, fun n pos cap flags qw qbp rew rets hn hp hr => hw _ _ n pos cap flags qw qbp rew rfl hn hp hr⟩

end
end LeanVM.Guest.B1
