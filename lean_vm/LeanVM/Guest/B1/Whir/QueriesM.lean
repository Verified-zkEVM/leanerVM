/-
  LeanVM.Guest.B1.Whir.QueriesM

  `opening_queries` under a hash model: per query, the leaf hash and the Merkle path below the
  cap are the model's answered hashes, the path's top stored at the cap leaf.
-/

module

public import LeanVM.Guest.B1.Whir.QueriesW
public import LeanVM.Guest.B1.Whir.CapM
public import LeanVM.Guest.B1.Whir.QueriesSpec

/-!
# `opening_queries` under a hash model (TRIAGE #28, #35)

`Whir/Queries.lean` over a `HashModel`. The blocks without a `BLAKE2S` row (the row, the query
sum, the cap leaf, the body of `opening_queries`) carry their deployed lemmas over unchanged
(`holdsListB_iff_of_noBlake`); the leaf hash is a chain of whole blocks from the IV
(`HashModel.chain_blocks`: the model answers the leaf's bytes), and every path level one block
under the IV (`HashModel.one_block`: the model answers the two children's bytes). In the
specification's terms (`QueryOkM`): query `i` at `q` has an opening whose leaf the model hashes
and whose siblings below the cap `climb` (V:526, at `Option` over `M.H`) to the digest stored at
the cap leaf; `opening_queries_model` is `opening_queries_sound` over the model.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {M : HashModel} {C : CallRel} {rd : Reader} {σ : Val}

/-! ## Blocks -/

theorem oqRows_noBlake (base I : ℕ) : Stmt.noBlakeList (oqRows base I) = true := by
  unfold oqRows
  split
  · rw [oqRows1, noBlakeList_append, noBlakeList_append,
      noBlakeList_flatten_range _ (fun j => oq1Blk I (j + 1)) (fun _ => rfl)]
    rfl
  · rw [oqRows0, noBlakeList_append, noBlakeList_append, noBlakeList_append, noBlakeList_append,
      noBlakeList_flatten_range _ (oq0Pack (3 * I)) (fun _ => rfl),
      noBlakeList_flatten_range _ (fun j => oq0Blk I (j + 1)) (fun _ => by
        unfold oq0Blk oq0WordT; split <;> rfl)]
    unfold oq0WordT
    split <;> rfl

theorem oqCapT_noBlake (P pd cd : ℕ) (loop : String) : Stmt.noBlakeList (oqCapT P pd cd loop) = true := by
  rw [oqCapT, noBlakeList_append, noBlakeList_append,
    noBlakeList_flatten_range _ (oqCapBit P pd) (fun _ => rfl)]
  rfl

/-! ## The leaf hash and the path -/

/-- **The leaf hash under a hash model** (G:1019-1023): the chain's last state is the model's
answered hash of the row's words' bytes, when the row fills its `blocks ≥ 1` whole blocks. -/
theorem oqLeaf_soundM {base I blocks : ℕ} (hbl : 1 ≤ blocks) (hR : oqR base I = 8 * blocks)
    (hrow : RowFacts base I rd σ) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsListB M.sem C rd σ (oqLeafT base I blocks) next kret) :
    (∃ ld, M.H ((leafWords base I (rowv σ)).flatMap kBytes) = some ld ∧
      (σ (.n (oqK1 base I + 3 * blocks)), σ (.n (oqK1 base I + 3 * blocks + 1))) = digestScalars ld) ∧
      next := by
  set K1 := oqK1 base I
  rw [oqLeafT, holdsListB_append] at h
  simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, word_iv0, word_iv1] at h
  obtain ⟨h0, h1, h2, hc0, h⟩ := h
  rw [holdsListB_flatten_range _ _ (fun _ => rfl)] at h
  obtain ⟨hb, hn⟩ := h
  refine ⟨?_, hn⟩
  let st : ℕ → E × E := fun j => if j = 0 then Value.ivCells else (σ (.n (K1 + 3 * j)), σ (.n (K1 + 3 * j + 1)))
  let bl : ℕ → Fin 4 → E := fun j =>
    ![σ (.n (oqPk base I (4 * j))), σ (.n (oqPk base I (4 * j + 1))), σ (.n (oqPk base I (4 * j + 2))),
      σ (.n (oqPk base I (4 * j + 3)))]
  have hst : st blocks = (σ (.n (K1 + 3 * blocks)), σ (.n (K1 + 3 * blocks + 1))) := by
    simp only [st, show blocks ≠ 0 by omega, ↓reduceIte]
  have hc : ∀ j ≤ blocks - 1, M.sem.check (bl j) (st j).1 (st j).2 (st (j + 1)).1 (st (j + 1)).2
      (oqMd blocks j) := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · simp only [st, ↓reduceIte, Nat.one_ne_zero, Nat.mul_one, bl, Nat.mul_zero, Nat.zero_add]
      rw [← h0, ← h1, ← h2]
      exact hc0
    · have := hb (j - 1) (by omega)
      rw [show j - 1 + 1 = j by omega] at this
      simp only [oqLeafBlk, leafBlkT, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, and_true] at this
      obtain ⟨hm, hc⟩ := this
      simp only [st, show j ≠ 0 by omega, show j + 1 ≠ 0 by omega, ↓reduceIte, bl]
      rw [← hm, show K1 + 3 * (j + 1) = K1 + 3 * j + 2 + 1 by ring,
        show K1 + 3 * j + 2 + 1 + 1 = K1 + 3 * j + 2 + 2 by ring]
      exact hc
  obtain ⟨ld, hld, hchain⟩ := HashModel.chain_blocks (M := M) (n := blocks - 1) (blocks := bl)
    (st := st) (md := oqMd blocks) (by simp [st])
    (fun j hj => by rw [oqMd_eq]; congr 1; simp; omega)
    (by rw [oqMd_eq, show blocks - 1 + 1 = blocks by omega]; simp)
    hc
  rw [show blocks - 1 + 1 = blocks by omega, hst] at hchain
  rw [show blocks - 1 + 1 = blocks by omega] at hld
  have hbytes : ((List.range blocks).flatMap fun j ↦ blockBytes (bl j)) =
      (leafWords base I (rowv σ)).flatMap kBytes := by
    obtain ⟨-, hpk, -, -⟩ := hrow
    rw [leafWords, hR, List.flatMap_map, show 8 * blocks = 2 * (4 * blocks) by ring,
      ← flatMap_range_mul 2 (4 * blocks), ← flatMap_range_mul 4 blocks]
    refine List.flatMap_congr fun jb hjb => ?_
    rw [List.mem_range] at hjb
    rw [blockBytes_eq_flatMap]
    refine List.flatMap_congr fun t ht => ?_
    rw [List.mem_range] at ht
    have hfin : ((Fin.ofNat 4 t : Fin 4) : ℕ) = t := by simp [Fin.ofNat, Nat.mod_eq_of_lt ht]
    have hbl : bl jb (Fin.ofNat 4 t) = σ (.n (oqPk base I (4 * jb + t))) := by
      interval_cases t <;> rfl
    rw [hbl, hpk _ (by omega), cellBytes]
    simp [List.range_succ, rowv]
  exact ⟨ld, hbytes ▸ hld, hchain⟩

/-- What one path level asks under a hash model: `PathLevel` with the model's row. -/
def PathLevelM (M : HashModel) (rd : Reader) (σ : Val) (P pd K l : ℕ) : Prop :=
  ∃ d, LoadHolds rd (σ (.n (P - 1))) l d ∧
    LoadHolds rd (σ (.n (P + 4 * pd)) * gen ^ (4 * l) * (1 + d * eOfNat 5)) 0 (σ (.n (oqNode P K l))) ∧
    LoadHolds rd (σ (.n (P + 4 * pd)) * gen ^ (4 * l) * (1 + d * eOfNat 5)) 1 (σ (.n (oqNode P K l + 1))) ∧
    M.sem.check ![σ (.n (P + 4 * l)), σ (.n (P + 4 * l + 1)), σ (.n (P + 4 * l + 2)),
        σ (.n (P + 4 * l + 3))] Value.ivCells.1 Value.ivCells.2 (σ (.n (oqNode P K (l + 1))))
      (σ (.n (oqNode P K (l + 1) + 1))) (metadataCell 64 true)

/-- `verify_merkle_path` (`oqPathT`) under a hash model, from its relation: the frame run of the
hinted children, and every level. -/
theorem oqPath_soundM {base I blocks pd : ℕ} (hpd : 1 ≤ pd) (hpd20 : pd ≤ 20) {next : Prop}
    {kret : List E → Prop} (h : Stmt.HoldsListB M.sem C rd σ (oqPathT base I blocks pd) next kret) :
    (IsInK (σ (.n (oqP base I blocks + 4 * pd))) ∧ ∀ k < 4 * pd, ∀ w,
        rd ((σ (.n (oqP base I blocks + 4 * pd))).limb 0 * Parameters.gpow k) = some w →
          w = σ (.n (oqP base I blocks + k))) ∧
      (∀ l < pd, PathLevelM M rd σ (oqP base I blocks) pd (oqK1 base I + 3 * blocks) l) ∧ next := by
  rw [oqPathT, holdsListB_append] at h
  generalize oqP base I blocks = P at h ⊢
  simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, true_and, word_iv0, word_iv1,
    word_md64, word_eOfNat, eOfNat_one] at h
  obtain ⟨⟨hp, hfr⟩, l81, h82, h83, h84, h85, h86, ln0, ln1, h87, h88, h89, hc0, h⟩ := h
  rw [holdsListB_flatten_range _ _ (fun _ => rfl)] at h
  obtain ⟨hb, hn⟩ := h
  refine ⟨⟨hp, fun k hk w hw => ?_⟩, fun l hl => ?_, hn⟩
  · have := hfr k (by simp; omega) w hw
    rwa [getElem_frameRun hk] at this
  · rcases Nat.eq_zero_or_pos l with rfl | hpos
    · refine ⟨σ (.n (P + 81)), l81, ?_, ?_, ?_⟩
      · rw [h86, h85, h84, h83, h82] at ln0
        simpa [oqNode] using ln0
      · rw [h86, h85, h84, h83, h82] at ln1
        simpa [oqNode] using ln1
      · rw [h87, h88, h89] at hc0
        simpa [oqNode, show P + 77 + 13 = P + 90 by ring] using hc0
    · have := hb (l - 1) (by omega)
      rw [show l - 1 + 1 = l by omega] at this
      simp only [oqLevel, levelT, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, and_true,
        word_iv0, word_iv1, word_md64, word_eOfNat, eOfNat_one] at this
      obtain ⟨lL, h1, h2, h3, h4, h5, h6, h7, n0, n1, h8, h9, h10, hc⟩ := this
      have hg : kw (gpowK (4 * l)) = gen ^ (4 * l) := kw_gpowK (by
        have : 4 * l < 2 ^ 7 := by omega
        exact lt_trans this (by decide))
      refine ⟨_, lL, ?_, ?_, ?_⟩
      · rw [h7, h6, h5, h4, h3, h2, h1, hg] at n0
        simpa [oqNode, show l ≠ 0 by omega] using n0
      · rw [h7, h6, h5, h4, h3, h2, h1, hg] at n1
        simpa [oqNode, show l ≠ 0 by omega, show P + 78 + 13 * l = P + 77 + 13 * l + 1 by ring] using n1
      · rw [h8, h9, h10] at hc
        simpa [oqNode, show l ≠ 0 by omega, show P + 79 + 13 * l + 11 = P + 77 + 13 * (l + 1) by ring,
          show P + 79 + 13 * l + 12 = P + 77 + 13 * (l + 1) + 1 by ring] using hc

/-! ## One query -/

/-- **One query under a hash model, its witnesses named**: `OqSemX` with the leaf hash and every
path level answered by the model. -/
def OqSemXM (M : HashModel) (base I pd cd : ℕ) (rd : Reader) (rew qsc qw qbp flags cap x : E)
    (r : ℕ → E) (dbp ptr : E) (cs : ℕ → E) (nd : ℕ → E × E) : Prop :=
  (∀ j < oqR base I, IsInK (r j)) ∧ (∀ jw < I, LoadHolds rd rew jw (memAt rd rew jw)) ∧
    (∃ s w, LoadHolds rd (qsc * x) 0 s ∧ LoadHolds rd (qw * x) 0 w ∧
      LoadHolds rd (qsc * x) 1 (s + w * ∑ jw ∈ Finset.range I, oqRowWord base r jw * memAt rd rew jw)) ∧
    LoadHolds rd (qbp * x) 0 dbp ∧
    (∃ ld, M.H ((leafWords base I r).flatMap kBytes) = some ld ∧ nd 0 = digestScalars ld) ∧
      IsInK ptr ∧ (∀ k < 4 * pd, ∀ w, rd (ptr.limb 0 * Parameters.gpow k) = some w → w = cs k) ∧
      (∀ l < pd, ∃ d, LoadHolds rd dbp l d ∧
        LoadHolds rd (ptr * gen ^ (4 * l) * (1 + d * eOfNat 5)) 0 (nd l).1 ∧
        LoadHolds rd (ptr * gen ^ (4 * l) * (1 + d * eOfNat 5)) 1 (nd l).2 ∧
        M.sem.check ![cs (4 * l), cs (4 * l + 1), cs (4 * l + 2), cs (4 * l + 3)] Value.ivCells.1
          Value.ivCells.2 (nd (l + 1)).1 (nd (l + 1)).2 (metadataCell 64 true)) ∧
      CapLeaf rd flags cap dbp pd cd (nd pd)

/-- **The loop helper's frame under a hash model**: the query at `x` with the frame's witnesses
(`OqSemXM`), then the call at `x·g` unless `x·g + N = 0`. -/
theorem oqFrame_soundM {base I blocks pd cd : ℕ} (hs : OqShape base I blocks pd cd) {loop : String}
    {kret : List E → Prop}
    (h : Stmt.HoldsListB M.sem C rd σ (oqLoopBody base I blocks pd cd loop) False kret) :
    OqSemXM M base I pd cd rd (σ (.n 2)) (σ (.n 3)) (σ (.n 4)) (σ (.n 5)) (σ (.n 6)) (σ (.n 7))
        (σ (.n 0)) (rowv σ) (σ (.n (oqK2 base I blocks + 8))) (σ (.n (oqP base I blocks + 4 * pd)))
        (fun k => σ (.n (oqP base I blocks + k))) (oqNd base I blocks σ) ∧
      IsInK (σ (.n 0) * gen + σ (.n 1)) ∧
      (σ (.n 0) * gen + σ (.n 1) ≠ 0 → C loop [σ (.n 0) * gen, σ (.n 1), σ (.n 2), σ (.n 3),
        σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7)] []) ∧ kret [] := by
  rw [oqLoopBody] at h
  simp only [holdsListB_append] at h
  obtain ⟨hrows, h⟩ := holdsListB_split_free (oqRows_noBlake _ _) (oqRows_noRet _ _) h
  have hrf := oqRows_sound hs.hbase hs.i4 hs.imod hrows
  obtain ⟨hleaf, h⟩ := holdsListB_true_of (oqLeafT_noRet _ _ _) h
  obtain ⟨ld, hld, hl⟩ := (oqLeaf_soundM hs.hblocks hs.fill hrf hleaf).1
  obtain ⟨hsum, h⟩ := holdsListB_split_free rfl rfl h
  obtain ⟨s1, s3, s7, s9, -⟩ := oqSum_sound hsum
  obtain ⟨hpath, h⟩ := holdsListB_true_of (oqPathT_noRet _ _ _ _) h
  obtain ⟨⟨hptr, hfr⟩, hlev, -⟩ := oqPath_soundM hs.pd1 hs.pd20 hpath
  rw [holdsListB_iff_of_noBlake (oqCapT_noBlake _ _ _ _)] at h
  obtain ⟨hcap, hK, hcall, hk⟩ := oqCap_sound hs.cd1 hs.cd8 h
  refine ⟨⟨hrf.1, hrf.2.2.1, ⟨_, _, s1, s3, by rw [← hrf.2.2.2]; exact s7⟩, s9,
    ⟨ld, hld, by simpa [oqNode, oqNd] using hl⟩, hptr, hfr, fun l hl => ?_, ?_⟩, hK, hcall, hk⟩
  · obtain ⟨dv, ld, n0, n1, hc⟩ := hlev l hl
    exact ⟨dv, by simpa [oqP] using ld, n0, n1, by simpa [add_assoc, oqNd] using hc⟩
  · simpa [oqNode, oqNd, show pd ≠ 0 by have := hs.pd1; omega, oqP] using hcap

/-- The loop helper's step under a hash model, from its relation: one query, then the call at
`x·g`. -/
theorem oqLoop_stepM {base I blocks pd cd : ℕ} (hs : OqShape base I blocks pd cd) {loop : String}
    {fn : Fn} (hfind : coreProgram.find? loop = some fn)
    (hp : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7])
    (hb : fn.body = oqLoopBody base I blocks pd cd loop) {rd : Reader} {N rew qsc qw qbp flags cap : E}
    {d : ℕ} {x : E}
    (h : coreProgram.relNB M.sem rd (d + 1) loop (x :: [N, rew, qsc, qw, qbp, flags, cap]) []) :
    (∃ r dbp ptr cs nd, OqSemXM M base I pd cd rd rew qsc qw qbp flags cap x r dbp ptr cs nd) ∧
      IsInK (x * gen + N) ∧
      (x * gen + N ≠ 0 →
        coreProgram.relNB M.sem rd d loop (x * gen :: [N, rew, qsc, qw, qbp, flags, cap]) []) := by
  rw [relNB_succ_iff hfind, hp, hb] at h
  obtain ⟨σ, hpar, h⟩ := h
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hpar
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := hpar
  obtain ⟨hx, hK, hcall, -⟩ := oqFrame_soundM hs h
  exact ⟨⟨_, _, _, _, _, hx⟩, hK, hcall⟩

/-! ## A query in the specification's terms -/

/-- `climb` (V:526) over a hash model, through a concatenation of sibling lists. -/
theorem climbM_append_list (D : Digest) (q : ℕ) : ∀ ss ts : List Digest,
    climb (m := Option) M.H D q (ss ++ ts) =
      (climb (m := Option) M.H D q ss).bind fun n ↦ climb (m := Option) M.H n (q / 2 ^ ss.length) ts
  | [], ts => by simp; rfl
  | s :: ss, ts => by
    rw [List.cons_append, climbM_cons, climbM_cons, Option.bind_assoc]
    congr 1
    funext p
    rw [climbM_append_list p (q / 2) ss ts, List.length_cons, Nat.div_div_eq_div_mul, pow_succ']

/-- `climb` over a hash model, one sibling. -/
theorem climbM_single (D s : Digest) (q : ℕ) :
    climb (m := Option) M.H D q [s] =
      if q % 2 = 0 then M.H (digestBytes D ++ digestBytes s) else M.H (digestBytes s ++ digestBytes D) := by
  rw [climbM_cons]
  split <;> cases M.H _ <;> rfl

/-- **Query `i` at the position `q` under a hash model, with the opening `o`**: its bits readable
at `qbp[i]`, its leaf of `oqR base I` words with the query sum `qsc[i + 1] = qsc[i] + qw[i]·⟨row,
weights⟩`, its path the siblings below the cap then the cap's siblings (`capSibs`), the model
hashing the leaf to `ld` and the siblings below the cap climbing from it (V:526, at `Option` over
`M.H`) to the digest `top` stored at the cap leaf, whose parent's flag is `1`. -/
def QueryOkM (M : HashModel) (base I depth cd : ℕ) (rd : Reader) (rew qsc qw qbp flags cap : E)
    (i q : ℕ) (o : Opening) : Prop :=
  ∃ dbp, LoadHolds rd qbp i dbp ∧ (∀ l < depth, LoadHolds rd dbp l (bitE (q.testBit l))) ∧
    o.leaf.length = oqR base I ∧ (∀ jw < I, LoadHolds rd rew jw (memAt rd rew jw)) ∧
    (∃ s w, LoadHolds rd qsc i s ∧ LoadHolds rd qw i w ∧ LoadHolds rd qsc (i + 1)
      (s + w * ∑ jw ∈ Finset.range I, leafRowWord base o.leaf jw * memAt rd rew jw)) ∧
    ∃ sibs, o.path = sibs ++ capSibs rd cap cd (2 ^ cd + q / 2 ^ (depth - cd)) ∧
      sibs.length = depth - cd ∧ ∃ ld top, M.H (o.leaf.flatMap kBytes) = some ld ∧
      climb (m := Option) M.H ld q sibs = some top ∧
      CapCell rd cap (2 ^ cd + q / 2 ^ (depth - cd)) top ∧
      LoadHolds rd flags (2 ^ (cd - 1) + q / 2 ^ (depth - cd + 1)) 1

/-- One level of the path at the position's bit under a hash model: with the running node the
cells of `N` and the climb so far at `N`, the next node is the model's answered hash, the climb
one level further. -/
theorem path_levelM {ptr : E} {cs : ℕ → E} {nd : ℕ → E × E} {ld N : Digest} {q pd l : ℕ}
    (sibs : List Digest) (hsl : sibs.length = pd)
    (hsib : sibs.getD l default = if q.testBit l then pairDigest (cs (4 * l)) (cs (4 * l + 1))
      else pairDigest (cs (4 * l + 2)) (cs (4 * l + 3)))
    (hl : l < pd)
    (hfr : ∀ k < 4 * pd, ∀ w, rd (ptr.limb 0 * Parameters.gpow k) = some w → w = cs k)
    (hd : ∃ d, LoadHolds rd (ptr * gen ^ (4 * l) * (1 + d * eOfNat 5)) 0 (nd l).1 ∧
      LoadHolds rd (ptr * gen ^ (4 * l) * (1 + d * eOfNat 5)) 1 (nd l).2 ∧ d = bitE (q.testBit l))
    (hc : M.sem.check ![cs (4 * l), cs (4 * l + 1), cs (4 * l + 2), cs (4 * l + 3)] Value.ivCells.1
      Value.ivCells.2 (nd (l + 1)).1 (nd (l + 1)).2 (metadataCell 64 true))
    (hnd : nd l = digestScalars N) (hclimb : climb (m := Option) M.H ld q (sibs.take l) = some N) :
    ∃ N', nd (l + 1) = digestScalars N' ∧ climb (m := Option) M.H ld q (sibs.take (l + 1)) = some N' := by
  obtain ⟨d, n0, n1, rfl⟩ := hd
  rw [one_add_bitE_five, mul_assoc, ← pow_add, loadHolds_mul_gen_pow, Nat.add_zero] at n0
  rw [one_add_bitE_five, mul_assoc, ← pow_add, loadHolds_mul_gen_pow] at n1
  rw [hnd] at n0 n1
  obtain ⟨L, R, D', hL, hR, hD', ho⟩ := check_hashPairM hc
  change (cs (4 * l), cs (4 * l + 1)) = _ at hL
  change (cs (4 * l + 2), cs (4 * l + 3)) = _ at hR
  have e0 := hfr _ (by cases q.testBit l <;> simp <;> omega) _ n0.2
  have e1 := hfr _ (by cases q.testBit l <;> simp <;> omega) _ n1.2
  have ho' : nd (l + 1) = digestScalars D' := Prod.mk.eta.symm.trans ho
  refine ⟨D', ho', ?_⟩
  have hl' : l < sibs.length := by omega
  rw [List.take_add_one, List.getElem?_eq_getElem hl', Option.toList_some, climbM_append_list, hclimb,
    Option.bind_some, List.length_take, Nat.min_eq_left hl'.le, climbM_single]
  have hbit : (q / 2 ^ l % 2 = 0) ↔ q.testBit l = false := by
    rw [← Nat.toNat_testBit]; cases q.testBit l <;> simp
  have hgs : sibs[l] = sibs.getD l default := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl', Option.getD_some]
  rw [hgs, hsib]
  cases hb : q.testBit l
  · simp only [hb, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at e0 e1
    have hn : N = L := digestScalars_injective (by rw [← hL, ← e0, ← e1])
    rw [ite_pos' (hbit.mpr hb), hn]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show pairDigest (cs (4 * l + 2)) (cs (4 * l + 3)) = R by
      rw [show cs (4 * l + 2) = (digestScalars R).1 from congrArg Prod.fst hR,
        show cs (4 * l + 3) = (digestScalars R).2 from congrArg Prod.snd hR, pairDigest_digestScalars]]
    exact hD'
  · simp only [hb, Bool.toNat_true, Nat.mul_one, show 4 * l + 2 + 1 = 4 * l + 3 by ring] at e0 e1
    have hn : N = R := digestScalars_injective (by rw [← hR, ← e0, ← e1])
    rw [ite_neg' (fun h => absurd (hbit.mp h) (by simp [hb])), hn]
    simp only [↓reduceIte]
    rw [show pairDigest (cs (4 * l)) (cs (4 * l + 1)) = L by
      rw [show cs (4 * l) = (digestScalars L).1 from congrArg Prod.fst hL,
        show cs (4 * l + 1) = (digestScalars L).2 from congrArg Prod.snd hL, pairDigest_digestScalars]]
    exact hD'

/-- **A query under a hash model, in the specification's terms**: the loop body at `g^i`, with
the position's bits at `qbp[i]`, is `QueryOkM` at the opening of its row's leaf, the siblings the
hinted children give at the position (`pathSibs`), then the cap's. -/
theorem oqSemX_queryM {base I blocks pd cd i q : ℕ} (hs : OqShape base I blocks pd cd)
    (hq : q < 2 ^ (pd + cd)) {rew qsc qw qbp flags cap : E}
    (hbits : ∀ dbp, LoadHolds rd qbp i dbp → BitsAt rd dbp q (pd + cd)) {r : ℕ → E} {dbp ptr : E}
    {cs : ℕ → E} {nd : ℕ → E × E}
    (h : OqSemXM M base I pd cd rd rew qsc qw qbp flags cap (gen ^ i) r dbp ptr cs nd) :
    QueryOkM M base I (pd + cd) cd rd rew qsc qw qbp flags cap i q
      ⟨leafWords base I r, pathSibs cs q pd ++ capSibs rd cap cd (2 ^ cd + q / 2 ^ pd)⟩ := by
  obtain ⟨hrK, hw, ⟨s, w, ls, lw, ls1⟩, ldbp, ⟨ld, hld, hnd0⟩, -, hfr, hlev, hcap⟩ := h
  rw [loadHolds_gen_pow] at ls lw ldbp
  rw [loadHolds_mul_gen_pow] at ls1
  have hB := hbits dbp ldbp
  have bit : ∀ l < pd + cd, ∀ d, LoadHolds rd dbp l d → d = bitE (q.testBit l) :=
    fun l hl d hd => hB.2 l hl d hd.2
  set sibs : List Digest := pathSibs cs q pd
  have hsl : sibs.length = pd := by simp [sibs, pathSibs]
  have hsib : ∀ l < pd, sibs.getD l default = if q.testBit l then pairDigest (cs (4 * l)) (cs (4 * l + 1))
      else pairDigest (cs (4 * l + 2)) (cs (4 * l + 3)) := fun l hl => by
    simp [sibs, pathSibs, List.getD_eq_getElem?_getD, hl]
  have hnd : ∀ l ≤ pd, ∃ N, nd l = digestScalars N ∧
      climb (m := Option) M.H ld q (sibs.take l) = some N := by
    intro l hl
    induction l with
    | zero => exact ⟨ld, hnd0, by simp; rfl⟩
    | succ l ih =>
      obtain ⟨N, hN, hcl⟩ := ih (by omega)
      obtain ⟨dv, ldv, n0, n1, hc⟩ := hlev l (by omega)
      exact path_levelM sibs hsl (hsib l (by omega)) (by omega) hfr
        ⟨dv, n0, n1, bit l (by omega) dv ldv⟩ hc hN hcl
  obtain ⟨top, htop, hclimb⟩ := hnd pd le_rfl
  rw [← hsl, List.take_length] at hclimb
  obtain ⟨hcl, hcf, hci0, hci1⟩ := hcap
  have hcb : ∀ t < cd, memAt rd dbp (pd + t) = bitE (q.testBit (pd + t)) := fun t ht =>
    bit (pd + t) (by omega) _ (hcl t ht)
  have hpar : capPar rd dbp pd cd (cd - 1) = gen ^ (2 ^ (cd - 1) + q / 2 ^ (pd + 1)) := by
    rw [capPar]
    rw [Finset.prod_congr rfl fun t ht => by
      rw [show pd + 1 + t = pd + (t + 1) by ring, hcb (t + 1) (by simp at ht; have := hs.cd1; omega)]]
    rw [prod_bitE_gen_pow' (fun t => q.testBit (pd + (t + 1))) (cd - 1), ← pow_add]
    congr 2
    rw [show (fun t => q.testBit (pd + (t + 1))) = (fun t => q.testBit ((pd + 1) + t)) from
      funext fun t => by rw [show pd + (t + 1) = pd + 1 + t by ring], bitsVal_shift,
      (capLeaf_index hs.cd1 hq).1]
  have hidx : capIdx rd dbp pd cd = gen ^ (2 ^ cd + q / 2 ^ pd) := by
    rw [capIdx, hpar, show memAt rd dbp pd = bitE (q.testBit pd) by simpa using hcb 0 hs.cd1,
      one_add_bitE_three, ← pow_add, ← pow_add, ← (capLeaf_index hs.cd1 hq).2]
    congr 1; ring
  rw [hpar, loadHolds_gen_pow] at hcf
  rw [hidx, ← pow_add, loadHolds_gen_pow] at hci0
  rw [hidx, mul_assoc, ← pow_add, ← pow_succ', loadHolds_gen_pow] at hci1
  rw [htop] at hci0 hci1
  refine ⟨dbp, ldbp, fun l hl => ?_, length_leafWords _ _ _, hw, ⟨s, w, ls, lw, ?_⟩, sibs,
    by simp only [show pd + cd - cd = pd by omega], by rw [hsl]; omega, ld, top, hld, hclimb,
    ⟨?_, ?_⟩, ?_⟩
  · rcases Nat.lt_or_ge l pd with hlp | hlp
    · obtain ⟨dv, ldv, -⟩ := hlev l hlp
      rw [← bit l hl dv ldv]; exact ldv
    · have := hcl (l - pd) (by omega)
      rw [show pd + (l - pd) = l by omega] at this
      rw [← bit l hl _ this]; exact this
  · rw [Finset.sum_congr rfl fun jw hjw => by rw [oqRowWord_leaf hrK (Finset.mem_range.mp hjw)]] at ls1
    exact ls1
  · rw [show pd + cd - cd = pd by omega, two_mul]; exact hci0
  · rw [show pd + cd - cd = pd by omega, two_mul]; exact hci1
  · rwa [show pd + cd - cd + 1 = pd + 1 by omega]

/-! ## `opening_queries` -/

/-- **`opening_queries` under a hash model** (the meaning of `MeaningOpeningQueries`, each query
`QueryOkM` at some opening). -/
def MeaningOpeningQueriesWith (M : HashModel) (base I depth cd n : ℕ) (pos : ℕ → ℕ) (rd : Reader)
    (qsc : E) : List E → List E → Prop
  | [cap, flags, qw, qbp, rew, nq], rets =>
      nq = gen ^ n ∧ LoadHolds rd qsc 0 0 ∧
        (∀ i < n, ∃ o, QueryOkM M base I depth cd rd rew qsc qw qbp flags cap i (pos i) o) ∧
        ∃ s, LoadHolds rd qsc n s ∧ rets = [s]
  | _, _ => False

theorem oqBody_noBlake (loop : String) : Stmt.noBlakeList (oqBody loop) = true := rfl

/-- **`opening_queries` is sound under a hash model**: at a shape `OqShape` and `n` queries below
the order of `g` whose positions' bits are at `qbp`, the relation gives the meaning at some chain
`qsc`. -/
theorem opening_queries_model {base I blocks pd cd : ℕ} (hs : OqShape base I blocks pd cd)
    {name loop : String} {f lf : Fn} (hfind : coreProgram.find? name = some f)
    (hp : f.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5]) (hb : f.body = oqBody loop)
    (hlf : coreProgram.find? loop = some lf)
    (hlp : lf.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7])
    (hlb : lf.body = oqLoopBody base I blocks pd cd loop) {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n (pd + cd) pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd name [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M base I (pd + cd) cd n pos rd qsc
      [cap, flags, qw, qbp, rew, gen ^ n] rets := by
  rw [relB_iff_sem hfind, hb, hp] at h
  obtain ⟨σ, hpar, h⟩ := h
  rw [holdsListB_iff_of_noBlake (oqBody_noBlake loop), oqBody] at h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_gen,
    word_zero, word_one, List.cons.injEq] at hpar h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, h5, -⟩ := hpar
  obtain ⟨h6, h7, -, h9, l9, h10, h11, h12, hK, hrun, h13, l14, hret⟩ := h
  have hloop := guarded_loopB_sound (B := fun x => ∃ r dbp ptr cs nd, OqSemXM M base I pd cd rd
      (σ (.n 4)) (σ (.n 8)) (σ (.n 2)) (σ (.n 3)) (σ (.n 1)) (σ (.n 0)) x r dbp ptr cs nd)
    (fun d x hx => oqLoop_stepM hs hlf hlp hlb hx) (fun hne => by
      have := hrun (by rw [h11, h10]; exact hne)
      rwa [h12] at this)
  obtain ⟨m, hm, hN, hB⟩ := hloop
  have hmn : m = n := gen_pow_inj (by simp only [ordG] at hm; omega) (by simp only [ordG] at hn; omega)
    (hN.symm.trans h5)
  subst hmn
  rw [h9] at l9
  rw [h13, h5, loadHolds_gen_pow] at l14
  refine ⟨σ (.n 8), rfl, l9, fun i hi => ?_, _, l14, hret.symm⟩
  obtain ⟨r, dbp, ptr, cs, nd, hx⟩ := hB i hi
  exact ⟨_, oqSemX_queryM hs (hpre i hi).1 (hpre i hi).2 hx⟩

/-! ## The openings named (`Whir/QueriesW.lean` under a hash model) -/

/-- A frame's query at `g^i` under a hash model, at a position whose bits are at `qbp[i]`, opens
with `oqOpeningOf` (`oqOpeningOf_ok`). -/
theorem oqOpeningOf_okM {base I blocks pd cd i q : ℕ} (hs : OqShape base I blocks pd cd)
    (hq : q < 2 ^ (pd + cd)) (hx : σ (.n 0) = gen ^ i)
    (hbits : ∀ dbp, LoadHolds rd (σ (.n 5)) i dbp → BitsAt rd dbp q (pd + cd))
    (h : OqSemXM M base I pd cd rd (σ (.n 2)) (σ (.n 3)) (σ (.n 4)) (σ (.n 5)) (σ (.n 6)) (σ (.n 7))
      (σ (.n 0)) (rowv σ) (σ (.n (oqK2 base I blocks + 8))) (σ (.n (oqP base I blocks + 4 * pd)))
      (fun k => σ (.n (oqP base I blocks + k))) (oqNd base I blocks σ)) :
    QueryOkM M base I (pd + cd) cd rd (σ (.n 2)) (σ (.n 3)) (σ (.n 4)) (σ (.n 5)) (σ (.n 6))
      (σ (.n 7)) i q (oqOpeningOf base I blocks pd cd rd σ) := by
  have ldbp := h.2.2.2.1
  rw [hx] at h ldbp
  rw [loadHolds_gen_pow] at ldbp
  have hw := oqSemX_queryM hs hq hbits h
  obtain ⟨dbp, l1, l2, -⟩ := id hw
  have edbp := loadHolds_unique ldbp l1
  rw [← edbp] at l2
  have hpos := bitsPos_eq hq l2
  have ho : oqOpeningOf base I blocks pd cd rd σ = ⟨leafWords base I (rowv σ),
      pathSibs (fun k => σ (.n (oqP base I blocks + k))) q pd ++
        capSibs rd (σ (.n 7)) cd (2 ^ cd + q / 2 ^ pd)⟩ := by
    simp only [oqOpeningOf, hpos]
  rw [ho]
  exact hw

/-- **The loop helper's outcome under a hash model** (`OqLoopOut`), the openings `os` of the
remaining iterations: query `j`'s `QueryOkM` at its opening. -/
def OqLoopOutM (M : HashModel) (base I pd cd : ℕ) (rd : Reader) : List E → List Opening → Prop
  | [x, N, rew, qsc, qw, qbp, flags, cap], os =>
      ∀ k, x = gen ^ k → ∃ m, k < m ∧ N = gen ^ m ∧ (∀ j, k < j → j < m → gen ^ j ≠ N) ∧
        os.length = m - k ∧ ∀ j, k ≤ j → j < m → ∀ q, q < 2 ^ (pd + cd) →
          (∀ dbp, LoadHolds rd qbp j dbp → BitsAt rd dbp q (pd + cd)) →
          QueryOkM M base I (pd + cd) cd rd rew qsc qw qbp flags cap j q (os.getD (j - k) ⟨[], []⟩)
  | _, _ => False

/-- **The loop helper's frame under a hash model, its openings named** (`oqLoop_frame_w`). -/
theorem oqLoop_frame_wM {base I blocks pd cd : ℕ} (hs : OqShape base I blocks pd cd) {loop : String}
    {wl : List E → List E → List Opening}
    (hrec : ∀ a, C loop a [] → OqLoopOutM M base I pd cd rd a (wl a []))
    (h : Stmt.HoldsListB M.sem C rd σ (oqLoopBody base I blocks pd cd loop) False fun rs => rs = []) :
    OqLoopOutM M base I pd cd rd (oqArgs σ) (oqLoopOs base I blocks pd cd rd wl σ) := by
  obtain ⟨hx, -, hcall, -⟩ := oqFrame_soundM hs h
  intro k hk
  by_cases h0 : σ (.n 0) * gen + σ (.n 1) = 0
  · have hN : σ (.n 1) = gen ^ (k + 1) := by rw [hk] at h0; exact (gen_pow_add_eq_zero_iff k).mp h0
    refine ⟨k + 1, by omega, hN, fun j h1 h2 => by omega, by simp [oqLoopOs, h0], fun j h1 h2 q hq hb => ?_⟩
    obtain rfl : j = k := by omega
    simp only [oqLoopOs, h0, ne_eq, not_true_eq_false, ↓reduceIte, Nat.sub_self, List.getD_cons_zero]
    exact oqOpeningOf_okM hs hq hk hb hx
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
        exact oqOpeningOf_okM hs hq hk hb hx
      · simp only [oqLoopOs, h0, ne_eq, not_false_eq_true, ↓reduceIte]
        rw [show j - k = (j - (k + 1)) + 1 by omega, List.getD_cons_succ]
        exact hall j hlt h2 q hq hb

/-- **`opening_queries` with its openings named under a hash model** (`MeaningOpeningQueriesW`). -/
def MeaningOpeningQueriesWM (M : HashModel) (base I depth cd n : ℕ) (pos : ℕ → ℕ) (rd : Reader)
    (qsc : E) : List E → List E → List Opening → Prop
  | [cap, flags, qw, qbp, rew, nq], rets, os =>
      nq = gen ^ n ∧ LoadHolds rd qsc 0 0 ∧ os.length = n ∧
        (∀ i < n, QueryOkM M base I depth cd rd rew qsc qw qbp flags cap i (pos i) (os.getD i ⟨[], []⟩)) ∧
        ∃ s, LoadHolds rd qsc n s ∧ rets = [s]
  | _, _, _ => False

theorem MeaningOpeningQueriesWM.meaning {base I depth cd n : ℕ} {pos : ℕ → ℕ} {qsc : E}
    {args rets : List E} {os : List Opening}
    (h : MeaningOpeningQueriesWM M base I depth cd n pos rd qsc args rets os) :
    MeaningOpeningQueriesWith M base I depth cd n pos rd qsc args rets := by
  match args, h with
  | [_, _, _, _, _, _], ⟨h1, h2, _, h4, h5⟩ => exact ⟨h1, h2, fun i hi => ⟨_, h4 i hi⟩, h5⟩

theorem MeaningOpeningQueriesWith.exists_w {base I depth cd n : ℕ} {pos : ℕ → ℕ} {qsc : E}
    {args rets : List E} (h : MeaningOpeningQueriesWith M base I depth cd n pos rd qsc args rets) :
    ∃ os, MeaningOpeningQueriesWM M base I depth cd n pos rd qsc args rets os := by
  match args, h with
  | [_, _, _, _, _, _], ⟨h1, h2, h4, h5⟩ =>
    have : Nonempty Opening := ⟨⟨[], []⟩⟩
    choose! o ho using h4
    refine ⟨(List.range n).map o, h1, h2, by simp, fun i hi => ?_, h5⟩
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
    exact ho i hi

/-- **`opening_queries`' frame under a hash model, its openings named**
(`opening_queries_frame_w`). -/
theorem opening_queries_frame_wM {base I pd cd : ℕ} {loop : String}
    {wl : List E → List E → List Opening}
    (hrec : ∀ a, C loop a [] → OqLoopOutM M base I pd cd rd a (wl a [])) {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} (h5 : σ (.n 5) = gen ^ n) (hpre : QueryBits rd (σ (.n 3)) n (pd + cd) pos)
    {rets : List E} (h : Stmt.HoldsListB M.sem C rd σ (oqBody loop) False fun rs => rs = rets) :
    MeaningOpeningQueriesWM M base I (pd + cd) cd n pos rd (σ (.n 8))
      [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5)] rets (oqQueriesOs wl σ) := by
  rw [holdsListB_iff_of_noBlake (oqBody_noBlake loop), oqBody] at h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, word_gen, word_zero, word_one, List.map_cons,
    List.map_nil] at h
  obtain ⟨h6, h7, -, h9, l9, h10, h11, h12, hK, hrun, h13, l14, hret⟩ := h
  rw [h9] at l9
  rw [h13, h5, loadHolds_gen_pow] at l14
  have hn' : n < 2 ^ 64 - 1 := hn
  by_cases hz : σ (.n 11) = 0
  · have h1 : σ (.n 5) = 1 := by
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

/-- **`opening_queries` named `name` is sound under a hash model with the openings `w`**, over the
call relation `C` (`SoundQueriesWC`). -/
def SoundQueriesWCM (M : HashModel) (C : CallRel) (rd : Reader) (name : String) (base I depth cd : ℕ)
    (w : List E → List E → List Opening) : Prop :=
  ∀ (n : ℕ) (pos : ℕ → ℕ) (cap flags qw qbp rew : E) (rets : List E), n < ordG →
    QueryBits rd qbp n depth pos → C name [cap, flags, qw, qbp, rew, gen ^ n] rets →
    ∃ qsc, MeaningOpeningQueriesWM M base I depth cd n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n]
      rets (w [cap, flags, qw, qbp, rew, gen ^ n] rets)

/-- The position of a query is the one its bits at `qbp[i]` spell. -/
theorem queryOkM_pos_unique {base I depth cd : ℕ} {rew qsc qw qbp flags cap : E} {i q q' : ℕ}
    {o : Opening} (h : QueryOkM M base I depth cd rd rew qsc qw qbp flags cap i q o) (hq : q < 2 ^ depth)
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
theorem MeaningOpeningQueriesWM.of_pos {base I depth cd n : ℕ} {pos pos' : ℕ → ℕ} {qsc : E}
    {cap flags qw qbp rew : E} {rets : List E} {os : List Opening}
    (h : MeaningOpeningQueriesWM M base I depth cd n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets os)
    (hp : QueryBits rd qbp n depth pos) (hp' : QueryBits rd qbp n depth pos') :
    MeaningOpeningQueriesWM M base I depth cd n pos' rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets os := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, h3, fun i hi => ?_, h5⟩
  have e := queryOkM_pos_unique (h4 i hi) (hp i hi).1 (hp' i hi).1 (hp' i hi).2
  rw [← e]
  exact h4 i hi

/-- `opening_queries`' soundness under a hash model gives a witness function. -/
theorem exists_soundQueriesWM {name : String} {base I depth cd : ℕ}
    (h : ∀ (n : ℕ) (pos : ℕ → ℕ) (cap flags qw qbp rew : E) (rets : List E), n < ordG →
      QueryBits rd qbp n depth pos →
      coreProgram.RelB M.sem rd name [cap, flags, qw, qbp, rew, gen ^ n] rets →
      ∃ qsc, MeaningOpeningQueriesWith M base I depth cd n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ w, SoundQueriesWCM M (coreProgram.RelB M.sem rd) rd name base I depth cd w := by
  classical
  have hex : ∀ args rets : List E, ∃ os : List Opening, ∀ (n : ℕ) (pos : ℕ → ℕ) (cap flags qw qbp rew : E),
      args = [cap, flags, qw, qbp, rew, gen ^ n] → n < ordG → QueryBits rd qbp n depth pos →
      coreProgram.RelB M.sem rd name args rets →
      ∃ qsc, MeaningOpeningQueriesWM M base I depth cd n pos rd qsc args rets os := by
    intro args rets
    by_cases hx : ∃ (n : ℕ) (pos : ℕ → ℕ) (cap flags qw qbp rew : E),
        args = [cap, flags, qw, qbp, rew, gen ^ n] ∧ n < ordG ∧ QueryBits rd qbp n depth pos ∧
          coreProgram.RelB M.sem rd name args rets
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

/-- `opening_queries_model` at a specialization. -/
theorem opening_queries_model_of_spec {name loop : String} {base I blocks pd cd : ℕ}
    (hs : OqSpec name loop base I blocks pd cd) {rd : Reader} {n : ℕ} (hn : n < ordG)
    {pos : ℕ → ℕ} {cap flags qw qbp rew : E} (hpre : QueryBits rd qbp n (pd + cd) pos) {rets : List E}
    (h : coreProgram.RelB M.sem rd name [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueriesWith M base I (pd + cd) cd n pos rd qsc
      [cap, flags, qw, qbp, rew, gen ^ n] rets := by
  obtain ⟨f, hf, hfp, hfb⟩ := hs.fn
  obtain ⟨lf, hlf, hlp, hlb⟩ := hs.loopFn
  exact opening_queries_model hs.shape hf hfp hfb hlf hlp hlb hn hpre h

end
end LeanVM.Guest.B1
