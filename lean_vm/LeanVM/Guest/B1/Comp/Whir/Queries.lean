/-
  LeanVM.Guest.B1.Comp.Whir.Queries

  The blocks of `opening_queries`' loop over a completeness model: the leaf hash and the Merkle
  path through the model's rows, the blocks without a `BLAKE2S` row carried over.
-/

module

public import LeanVM.Guest.B1.Comp.Whir.Cap
public import LeanVM.Guest.B1.Whir.QueriesM
public import LeanVM.Guest.B1.Whir.QueriesIter

/-!
# `opening_queries`' blocks over a completeness model (TRIAGE #28, #35)

`Whir/QueriesComplete.lean` over a `CompModel`. The honest digests are a total hash `Ht`'s
(`climbAtW`, `climbCellsW`, `hashWordsW`; at `blake2sBytes` the deployed `climbAt`, `climbCells`,
`hashWords`) which the model answers where the guest hashes:

* the leaf hash (`oqLeaf_completeC`): the blocks of an answered string check through the model's
  chain of it (`CompModel.chain_checks_blocks`), its cells `chainSt` after each block;
* the Merkle path (`oqPathT_completeC`): each level's block of two digests checks from the IV to
  the model's answer for their bytes (`compress_of_hashPairC`), the answers those of a climb the
  model answers (`climb_answered`);
* the row, the query sum and the cap leaf have no `BLAKE2S` row and carry their deployed lemmas
  over (`oqRows_completeB`, `oqSumT_completeB`, `oqCapT_completeB`).

At `CompModel.deployed` and `blake2sBytes` the two hash blocks are the deployed lemmas
(`oqLeaf_complete_of_comp`, `oqPathT_complete_of_comp`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.E2E.Complete LeanVM.Guest.B1.Digest

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## The climb over a total hash -/

/-- The digest of a node over the hash `Ht` (`hashPair`). -/
def hashPairW (Ht : Bytes → Digest) (l r : Digest) : Digest := Ht (digestBytes l ++ digestBytes r)

/-- A leaf's digest over the hash `Ht` (`hashWords`). -/
def hashWordsW (Ht : Bytes → Digest) (words : List K) : Digest := Ht (words.flatMap kBytes)

/-- The running node after `l` levels of `climb` over the hash `Ht` (`climbAt`). -/
def climbAtW (Ht : Bytes → Digest) (D : Digest) (q : ℕ) (sibs : List Digest) (l : ℕ) : Digest :=
  climb (m := Id) Ht D q (sibs.take l)

/-- The cells `verify_merkle_path` hints for the climb over the hash `Ht` (`climbCells`). -/
def climbCellsW (Ht : Bytes → Digest) (D : Digest) (q : ℕ) (sibs : List Digest) : List E :=
  (List.range sibs.length).flatMap fun l =>
    lvlCells (climbAtW Ht D q sibs l) (sibs.getD l default) (q.testBit l)

/-- The string level `l` of the climb hashes: the running node and its sibling, in order. -/
def climbLvlBytes (Ht : Bytes → Digest) (D : Digest) (q : ℕ) (sibs : List Digest) (l : ℕ) : Bytes :=
  if q.testBit l then digestBytes (sibs.getD l default) ++ digestBytes (climbAtW Ht D q sibs l)
  else digestBytes (climbAtW Ht D q sibs l) ++ digestBytes (sibs.getD l default)

theorem hashPairW_blake : hashPairW blake2sBytes = hashPair := rfl

theorem hashWordsW_blake : hashWordsW blake2sBytes = hashWords := rfl

theorem climbAtW_blake : climbAtW blake2sBytes = climbAt := rfl

theorem climbCellsW_blake : climbCellsW blake2sBytes = climbCells := rfl

theorem climbW_cons (Ht : Bytes → Digest) (node s : Digest) (q : ℕ) (ss : List Digest) :
    climb (m := Id) Ht node q (s :: ss) =
      climb (m := Id) Ht (if q % 2 = 0 then hashPairW Ht node s else hashPairW Ht s node) (q / 2) ss := by
  simp only [climb]
  split <;> rfl

theorem climbW_append (Ht : Bytes → Digest) (D : Digest) (q : ℕ) (ss : List Digest) (s : Digest) :
    climb (m := Id) Ht D q (ss ++ [s]) =
      if q / 2 ^ ss.length % 2 = 0 then hashPairW Ht (climb (m := Id) Ht D q ss) s
      else hashPairW Ht s (climb (m := Id) Ht D q ss) := by
  induction ss generalizing D q with
  | nil => simp only [List.nil_append, climbW_cons, List.length_nil, pow_zero, Nat.div_one]; rfl
  | cons x ss ih =>
    rw [List.cons_append, climbW_cons, ih, climbW_cons, List.length_cons, Nat.div_div_eq_div_mul,
      pow_succ']

theorem climbAtW_succ (Ht : Bytes → Digest) (D : Digest) (q : ℕ) (sibs : List Digest) {l : ℕ}
    (hl : l < sibs.length) :
    climbAtW Ht D q sibs (l + 1) =
      if q.testBit l then hashPairW Ht (sibs.getD l default) (climbAtW Ht D q sibs l)
      else hashPairW Ht (climbAtW Ht D q sibs l) (sibs.getD l default) := by
  rw [climbAtW, List.take_add_one, List.getElem?_eq_getElem hl, Option.toList_some, climbW_append,
    List.length_take, Nat.min_eq_left hl.le, ← Nat.toNat_testBit, climbAtW,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
  cases q.testBit l <;> rfl

theorem climbAtW_length (Ht : Bytes → Digest) (D : Digest) (q : ℕ) (sibs : List Digest) :
    climbAtW Ht D q sibs sibs.length = climb (m := Id) Ht D q sibs := by
  rw [climbAtW, List.take_length]

/-- The climb one level up: its nodes those of the climb from the parent. -/
theorem climbAtW_cons (Ht : Bytes → Digest) (D s : Digest) (q : ℕ) (ss : List Digest) (l : ℕ) :
    climbAtW Ht D q (s :: ss) (l + 1) =
      climbAtW Ht (if q % 2 = 0 then hashPairW Ht D s else hashPairW Ht s D) (q / 2) ss l := by
  rw [climbAtW, List.take_succ_cons, climbW_cons, climbAtW]

theorem climbLvlBytes_cons (Ht : Bytes → Digest) (D s : Digest) (q : ℕ) (ss : List Digest) (l : ℕ) :
    climbLvlBytes Ht D q (s :: ss) (l + 1) =
      climbLvlBytes Ht (if q % 2 = 0 then hashPairW Ht D s else hashPairW Ht s D) (q / 2) ss l := by
  rw [climbLvlBytes, climbLvlBytes, Nat.testBit_succ, climbAtW_cons, List.getD_cons_succ]

/-- **A climb the model answers**: with a total hash `Ht` the model agrees with where it answers,
its top is the climb over `Ht`, and the model answers each level's string by the next node. -/
theorem climb_answered {H : Bytes → Option Digest} {Ht : Bytes → Digest}
    (hHt : ∀ x d, H x = some d → d = Ht x) :
    ∀ {sibs : List Digest} {D : Digest} {q : ℕ} {t : Digest},
      climb (m := Option) H D q sibs = some t →
      t = climb (m := Id) Ht D q sibs ∧
        ∀ l < sibs.length, H (climbLvlBytes Ht D q sibs l) = some (climbAtW Ht D q sibs (l + 1))
  | [], D, q, t, h => by
    simp only [climb] at h
    exact ⟨(Option.some.inj h).symm, fun l hl => absurd hl (by simp)⟩
  | s :: ss, D, q, t, h => by
    have hb0 : q.testBit 0 = !decide (q % 2 = 0) := by
      rw [Nat.testBit_zero]; rcases Nat.mod_two_eq_zero_or_one q with h' | h' <;> simp [h']
    by_cases h0 : q % 2 = 0
    · simp only [climb, h0, ↓reduceIte, bind, Option.bind_eq_some_iff] at h
      obtain ⟨p, hp1, hp2⟩ := h
      obtain rfl := hHt _ _ hp1
      obtain ⟨ht, hl⟩ := climb_answered hHt hp2
      refine ⟨by rw [ht, climbW_cons, ite_pos' h0]; rfl, fun l hl' => ?_⟩
      rcases l with _ | l
      · have e1 : climbAtW Ht D q (s :: ss) (0 + 1) = Ht (digestBytes D ++ digestBytes s) := by
          rw [Nat.zero_add, climbAtW, List.take_succ_cons, List.take_zero, climbW_cons, ite_pos' h0]; rfl
        have e2 : climbLvlBytes Ht D q (s :: ss) 0 = digestBytes D ++ digestBytes s := by
          simp only [climbLvlBytes, hb0, h0, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          rfl
        rw [e1, e2]; exact hp1
      · rw [climbLvlBytes_cons, climbAtW_cons, ite_pos' h0]
        exact hl l (by simp at hl'; omega)
    · simp only [climb, h0, ↓reduceIte, bind, Option.bind_eq_some_iff] at h
      obtain ⟨p, hp1, hp2⟩ := h
      obtain rfl := hHt _ _ hp1
      obtain ⟨ht, hl⟩ := climb_answered hHt hp2
      refine ⟨by rw [ht, climbW_cons, ite_neg' h0]; rfl, fun l hl' => ?_⟩
      rcases l with _ | l
      · have e1 : climbAtW Ht D q (s :: ss) (0 + 1) = Ht (digestBytes s ++ digestBytes D) := by
          rw [Nat.zero_add, climbAtW, List.take_succ_cons, List.take_zero, climbW_cons, ite_neg' h0]; rfl
        have e2 : climbLvlBytes Ht D q (s :: ss) 0 = digestBytes s ++ digestBytes D := by
          simp only [climbLvlBytes, hb0, h0, decide_false, Bool.not_false, ↓reduceIte]
          rfl
        rw [e1, e2]; exact hp1
      · rw [climbLvlBytes_cons, climbAtW_cons, ite_neg' h0]
        exact hl l (by simp at hl'; omega)

/-- At the deployed hash, a climb is answered. -/
theorem climb_some_blake (D : Digest) (q : ℕ) (sibs : List Digest) :
    climb (m := Option) (fun x => some (blake2sBytes x)) D q sibs =
      some (climb (m := Id) blake2sBytes D q sibs) := by
  induction sibs generalizing D q with
  | nil => rfl
  | cons s ss ih =>
    simp only [climb]
    split <;> exact ih _ _

/-! ## The leaf hash -/

/-- The bytes of the leaf's blocks as the guest packs them. -/
def oqLeafBytes (σ : Val) (base I blocks : ℕ) : Bytes :=
  (List.range blocks).flatMap fun j => blockBytes (oqLeafBl σ base I j)

/-- **The leaf hash over a completeness model**: the IV, then each block's metadata and the
model's chain of the leaf's bytes, the model answering them (`oqLeaf_complete`). -/
theorem oqLeaf_completeC {CM : CompModel} {base I blocks : ℕ} (hbl : 1 ≤ blocks) {next : Prop}
    {kret : List E → Prop}
    (hcan : ∀ j < blocks, ∀ t, IsCanonical128 (oqLeafBl σ base I j t)) {d : Digest}
    (hd : CM.H (oqLeafBytes σ base I blocks) = some d)
    (hiv0 : σ (.n (oqK1 base I)) = (digestScalars paramIv).1)
    (hiv1 : σ (.n (oqK1 base I + 1)) = (digestScalars paramIv).2)
    (hmd : ∀ j < blocks, σ (.n (oqK1 base I + 3 * j + 2)) = oqMd blocks j)
    (hst : ∀ j < blocks, (σ (.n (oqK1 base I + 3 * j + 3)), σ (.n (oqK1 base I + 3 * j + 4))) =
      CM.chainSt (oqLeafBytes σ base I blocks) d (j + 1)) (hn : next) :
    Stmt.HoldsListB CM.sem C rd σ (oqLeafT base I blocks) next kret := by
  set K1 := oqK1 base I
  set X := oqLeafBytes σ base I blocks with hX
  obtain ⟨n, rfl⟩ : ∃ n, blocks = n + 1 := ⟨blocks - 1, by omega⟩
  have hchk : ∀ j ≤ n, CM.sem.check (oqLeafBl σ base I j) (CM.chainSt X d j).1 (CM.chainSt X d j).2
      (CM.chainSt X d (j + 1)).1 (CM.chainSt X d (j + 1)).2 (oqMd (n + 1) j) :=
    CM.chain_checks_blocks (n := n) (blocks := oqLeafBl σ base I) (md := oqMd (n + 1))
    hd (fun j hj r => hcan j (by omega) r)
    (fun j hj => by rw [oqMd_eq]; congr 1; simp only [decide_eq_false_iff_not]; omega)
    (by rw [oqMd_eq]; simp)
  have hchain : ∀ j ≤ n + 1, (if j = 0 then (σ (.n K1), σ (.n (K1 + 1)))
      else (σ (.n (K1 + 3 * j)), σ (.n (K1 + 3 * j + 1)))) = CM.chainSt X d j := by
    intro j hj
    rcases j with _ | j
    · simp only [↓reduceIte, hiv0, hiv1, CompModel.chainSt_zero]; rfl
    · simp only [Nat.add_one_ne_zero, ↓reduceIte]
      rw [show K1 + 3 * (j + 1) = K1 + 3 * j + 3 by ring,
        show K1 + 3 * j + 3 + 1 = K1 + 3 * j + 4 by ring]
      exact hst j (by omega)
  rw [oqLeafT, holdsListB_append]
  simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, word_iv0, word_iv1]
  have c0 := hchain 0 (by omega)
  simp only [↓reduceIte] at c0
  refine ⟨by rw [hiv0]; rfl, by rw [hiv1]; rfl, by simpa using hmd 0 (by omega), ?_, ?_⟩
  · have := hchk 0 (by omega)
    have c1 := hchain 1 (by omega)
    simp only [Nat.one_ne_zero, ↓reduceIte, Nat.mul_one] at c1
    rw [← c0, ← c1] at this
    rw [show σ (.n (oqK1 base I + 2)) = oqMd (n + 1) 0 by simpa using hmd 0 (by omega)]
    exact this
  · rw [holdsListB_flatten_range _ _ (fun _ => rfl)]
    refine ⟨fun j hj => ?_, hn⟩
    simp only [oqLeafBlk, leafBlkT, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, and_true]
    refine ⟨hmd (j + 1) (by omega), ?_⟩
    have := hchk (j + 1) (by omega)
    have ca := hchain (j + 1) (by omega)
    have cb := hchain (j + 1 + 1) (by omega)
    simp only [Nat.add_one_ne_zero, ↓reduceIte] at ca cb
    rw [← ca, ← cb, ← hmd (j + 1) (by omega)] at this
    rw [show oqK1 base I + 3 * (j + 1) + 2 + 1 = K1 + 3 * (j + 1 + 1) by ring,
      show oqK1 base I + 3 * (j + 1) + 2 + 2 = K1 + 3 * (j + 1 + 1) + 1 by ring]
    exact this

/-- The leaf's bytes are its row's words' bytes, when the row fills its whole blocks (from
`oqLeaf_soundM`). -/
theorem oqLeafBytes_eq {base I blocks : ℕ} (hR : oqR base I = 8 * blocks) (hrow : RowFacts base I rd σ) :
    oqLeafBytes σ base I blocks = (leafWords base I (rowv σ)).flatMap kBytes := by
  obtain ⟨-, hpk, -, -⟩ := hrow
  rw [oqLeafBytes, leafWords, hR, List.flatMap_map, show 8 * blocks = 2 * (4 * blocks) by ring,
    ← flatMap_range_mul 2 (4 * blocks), ← flatMap_range_mul 4 blocks]
  refine List.flatMap_congr fun jb hjb => ?_
  rw [List.mem_range] at hjb
  rw [blockBytes_eq_flatMap]
  refine List.flatMap_congr fun t ht => ?_
  rw [List.mem_range] at ht
  have hbl : oqLeafBl σ base I jb (Fin.ofNat 4 t) = σ (.n (oqPk base I (4 * jb + t))) := by
    interval_cases t <;> rfl
  rw [hbl, hpk _ (by omega), cellBytes]
  simp [List.range_succ, rowv]

/-! ## The Merkle path -/

theorem oq_climbCellsW_getD {Ht : Bytes → Digest} {D : Digest} {q : ℕ} {sibs : List Digest} {l t : ℕ}
    (hl : l < sibs.length) (ht : t < 4) : (climbCellsW Ht D q sibs).getD (4 * l + t) 0 =
      (lvlCells (climbAtW Ht D q sibs l) (sibs.getD l default) (q.testBit l)).getD t 0 :=
  oq_getD_flatten_uniform (fun l => lvlCells (climbAtW Ht D q sibs l) (sibs.getD l default) (q.testBit l)) 4
    (fun _ => length_lvlCells _ _ _) _ _ _ hl ht

theorem oq_length_climbCellsW (Ht : Bytes → Digest) (D : Digest) (q : ℕ) (sibs : List Digest) :
    (climbCellsW Ht D q sibs).length = 4 * sibs.length := by
  rw [climbCellsW, List.flatMap]
  exact (oq_length_flatten_uniform _ 4 (fun _ => length_lvlCells _ _ _) _).trans (by ring)

/-- The honest values of path level `0` from `P + 81`, over `Ht` (`oqPath0Vals`). -/
def oqPath0ValsW (Ht : Bytes → Digest) (ptr : E) (D : Digest) (q : ℕ) (sibs : List Digest) : List E :=
  [bitE (q.testBit 0), 1, eOfNat 5, bitE (q.testBit 0) * eOfNat 5, 1 + bitE (q.testBit 0) * eOfNat 5,
    ptr * (1 + bitE (q.testBit 0) * eOfNat 5), Value.ivCells.1, Value.ivCells.2, metadataCell 64 true,
    (digestScalars (climbAtW Ht D q sibs 1)).1, (digestScalars (climbAtW Ht D q sibs 1)).2]

/-- The honest values of path level `l ≥ 1` from `P + 79 + 13·l`, over `Ht` (`oqPathLVals`). -/
def oqPathLValsW (Ht : Bytes → Digest) (ptr : E) (D : Digest) (q : ℕ) (sibs : List Digest) (l : ℕ) :
    List E :=
  [bitE (q.testBit l), gen ^ (4 * l), ptr * gen ^ (4 * l), 1, eOfNat 5, bitE (q.testBit l) * eOfNat 5,
    1 + bitE (q.testBit l) * eOfNat 5, ptr * gen ^ (4 * l) * (1 + bitE (q.testBit l) * eOfNat 5),
    Value.ivCells.1, Value.ivCells.2, metadataCell 64 true, (digestScalars (climbAtW Ht D q sibs (l + 1))).1,
    (digestScalars (climbAtW Ht D q sibs (l + 1))).2]

theorem oqPath0ValsW_blake : oqPath0ValsW blake2sBytes = oqPath0Vals := rfl

theorem oqPathLValsW_blake : oqPathLValsW blake2sBytes = oqPathLVals := rfl

/-- **One level's row over a completeness model**: the level's four cells check from the IV to
the next node, the model answering the level's string by it (`oq_compress_level`). -/
theorem oq_compress_levelC (CM : CompModel) {Ht : Bytes → Digest} {D : Digest} {q : ℕ}
    {sibs : List Digest} {l : ℕ} (hl : l < sibs.length)
    (hA : CM.H (climbLvlBytes Ht D q sibs l) = some (climbAtW Ht D q sibs (l + 1))) :
    CM.sem.check ![(climbCellsW Ht D q sibs).getD (4 * l) 0, (climbCellsW Ht D q sibs).getD (4 * l + 1) 0,
      (climbCellsW Ht D q sibs).getD (4 * l + 2) 0, (climbCellsW Ht D q sibs).getD (4 * l + 3) 0]
      Value.ivCells.1 Value.ivCells.2 (digestScalars (climbAtW Ht D q sibs (l + 1))).1
      (digestScalars (climbAtW Ht D q sibs (l + 1))).2 (metadataCell 64 true) := by
  have e := fun t (ht : t < 4) => oq_climbCellsW_getD (Ht := Ht) (D := D) (q := q) (l := l) hl ht
  rw [show 4 * l = 4 * l + 0 from rfl, e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega)]
  unfold climbLvlBytes at hA
  cases hb : q.testBit l
  · rw [hb] at hA
    exact compress_of_hashPairC CM _ _ hA
  · rw [hb] at hA
    exact compress_of_hashPairC CM _ _ hA

/-- The selected child: the running node at offset `4l + 2b` of the level's cells
(`oq_node_load`). -/
theorem oq_node_loadW {Ht : Bytes → Digest} {D : Digest} {q : ℕ} {sibs : List Digest} {l : ℕ}
    (hl : l < sibs.length) {ptr : E}
    (hcell : ∀ j < 4 * sibs.length, LoadHolds rd ptr j ((climbCellsW Ht D q sibs).getD j 0)) :
    LoadHolds rd (ptr * gen ^ (4 * l) * (1 + bitE (q.testBit l) * eOfNat 5)) 0
        (digestScalars (climbAtW Ht D q sibs l)).1 ∧
      LoadHolds rd (ptr * gen ^ (4 * l) * (1 + bitE (q.testBit l) * eOfNat 5)) 1
        (digestScalars (climbAtW Ht D q sibs l)).2 := by
  rw [one_add_bitE_five, mul_assoc, ← pow_add, LeanVM.Guest.B1.loadHolds_mul_gen_pow,
    LeanVM.Guest.B1.loadHolds_mul_gen_pow]
  have e := fun t (ht : t < 4) => oq_climbCellsW_getD (Ht := Ht) (D := D) (q := q) (l := l) hl ht
  have c0 := hcell (4 * l + 2 * (q.testBit l).toNat) (by cases q.testBit l <;> simp <;> omega)
  have c1 := hcell (4 * l + 2 * (q.testBit l).toNat + 1) (by cases q.testBit l <;> simp <;> omega)
  rw [e _ (by cases q.testBit l <;> simp)] at c0
  rw [show 4 * l + 2 * (q.testBit l).toNat + 1 = 4 * l + (2 * (q.testBit l).toNat + 1) by ring,
    e _ (by cases q.testBit l <;> simp)] at c1
  rw [Nat.add_zero]
  rcases hb : q.testBit l with _ | _
  · rw [hb] at c0 c1
    simp only [lvlCells, Bool.false_eq_true, ↓reduceIte, Bool.toNat_false, Nat.mul_zero, Nat.zero_add,
      Nat.add_zero, List.getD_cons_zero, List.getD_cons_succ] at c0 c1 ⊢
    exact ⟨c0, c1⟩
  · rw [hb] at c0 c1
    simp only [lvlCells, ↓reduceIte, Bool.toNat_true, Nat.mul_one, List.getD_cons_zero,
      List.getD_cons_succ] at c0 c1 ⊢
    exact ⟨c0, by simpa [Nat.add_assoc] using c1⟩

/-- **`verify_merkle_path` (`oqPathT`) over a completeness model**: the hinted children the
climb's cells over `Ht`, the model answering each level's string by the next node
(`oqPathT_complete`). -/
theorem oqPathT_completeC {CM : CompModel} {Ht : Bytes → Digest} {base I blocks pd : ℕ} (hpd : 1 ≤ pd)
    (hpd20 : pd ≤ 20) {D : Digest} {q : ℕ} {sibs : List Digest} (hsl : sibs.length = pd) {ptr : E}
    {next : Prop} {kret : List E → Prop}
    (hA : ∀ l < pd, CM.H (climbLvlBytes Ht D q sibs l) = some (climbAtW Ht D q sibs (l + 1)))
    (hK : (σ (.n (oqK1 base I + 3 * blocks)), σ (.n (oqK1 base I + 3 * blocks + 1))) = digestScalars D)
    (hcs : ∀ j < 4 * pd, σ (.n (oqP base I blocks + j)) = (climbCellsW Ht D q sibs).getD j 0)
    (hptr : σ (.n (oqP base I blocks + 4 * pd)) = ptr) (hptrK : IsInK ptr)
    (hcell : ∀ j < 4 * pd, LoadHolds rd ptr j ((climbCellsW Ht D q sibs).getD j 0))
    (hfr2 : ∀ j < 80 - 4 * pd, ∀ w, rd (ptr.limb 0 * Parameters.gpow (4 * pd + j)) = some w →
      w = σ (.n (oqP base I blocks + 4 * pd + 1 + j)))
    (hbits : ∀ l < pd, LoadHolds rd (σ (.n (oqP base I blocks - 1))) l (bitE (q.testBit l)))
    (hv0 : ∀ t < 11, σ (.n (oqP base I blocks + 81 + t)) = (oqPath0ValsW Ht ptr D q sibs).getD t 0)
    (hvl : ∀ l < pd - 1, ∀ t < 13, σ (.n (oqP base I blocks + 79 + 13 * (l + 1) + t)) =
      (oqPathLValsW Ht ptr D q sibs (l + 1)).getD t 0) (hn : next) :
    Stmt.HoldsListB CM.sem C rd σ (oqPathT base I blocks pd) next kret := by
  rw [oqPathT, holdsListB_append]
  subst hsl
  have hcell' : ∀ j < 4 * sibs.length, LoadHolds rd ptr j ((climbCellsW Ht D q sibs).getD j 0) := hcell
  generalize oqP base I blocks = P at *
  generalize oqK1 base I + 3 * blocks = K at *
  have e0 := hv0 0 (by omega); have e1 := hv0 1 (by omega); have e2 := hv0 2 (by omega)
  have e3 := hv0 3 (by omega); have e4 := hv0 4 (by omega); have e5 := hv0 5 (by omega)
  have e6 := hv0 6 (by omega); have e7 := hv0 7 (by omega); have e8 := hv0 8 (by omega)
  have e9 := hv0 9 (by omega); have e10 := hv0 10 (by omega)
  simp only [oqPath0ValsW, List.getD_cons_zero, List.getD_cons_succ,
    show ∀ t, P + 81 + t = t + P + 81 from fun t => by ring] at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
  simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, true_and, word_iv0, word_iv1, word_md64,
    word_eOfNat, eOfNat_one]
  obtain ⟨n0, n1⟩ := oq_node_loadW (l := 0) (by omega) hcell'
  have k0 : (σ (.n K), σ (.n (K + 1))) = digestScalars (climbAtW Ht D q sibs 0) := hK
  refine ⟨⟨by rw [hptr]; exact hptrK, fun k hk w hw => ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left
  · rw [show P + 81 = 0 + P + 81 by ring, e0]; simpa using hbits 0 (by omega)
  · rw [show P + 82 = 1 + P + 81 by ring, e1]
  · rw [show P + 83 = 2 + P + 81 by ring, e2]
  · rw [show P + 84 = 3 + P + 81 by ring, e3, show P + 81 = 0 + P + 81 by ring, e0,
      show P + 83 = 2 + P + 81 by ring, e2]
  · rw [show P + 85 = 4 + P + 81 by ring, e4, show P + 82 = 1 + P + 81 by ring, e1,
      show P + 84 = 3 + P + 81 by ring, e3]
  · rw [show P + 86 = 5 + P + 81 by ring, e5, hptr, show P + 85 = 4 + P + 81 by ring, e4]
  · rw [show P + 86 = 5 + P + 81 by ring, e5, show σ (.n K) = _ from congrArg Prod.fst k0]
    simpa using n0
  · rw [show P + 86 = 5 + P + 81 by ring, e5, show σ (.n (K + 1)) = _ from congrArg Prod.snd k0]
    simpa using n1
  · rw [show P + 87 = 6 + P + 81 by ring, e6]
  · rw [show P + 88 = 7 + P + 81 by ring, e7]
  · rw [show P + 89 = 8 + P + 81 by ring, e8]
  rotate_left 2
  · rw [hptr] at hw
    rcases Nat.lt_or_ge k (4 * sibs.length) with hk4 | hk4
    · rw [getElem_frameRun hk4, hcs k hk4]
      exact Option.some.inj (hw.symm.trans (hcell' k hk4).2)
    · have hk80 : k < 80 := by simp at hk; omega
      rw [List.getElem_append_right (by simpa using hk4)]
      simp only [List.length_map, List.length_range, List.getElem_map, List.getElem_range]
      have := hfr2 (k - 4 * sibs.length) (by omega) w (by
        rw [show 4 * sibs.length + (k - 4 * sibs.length) = k by omega]; exact hw)
      exact this
  · rw [show P + 87 = 6 + P + 81 by ring, e6, show P + 88 = 7 + P + 81 by ring, e7,
      show P + 89 = 8 + P + 81 by ring, e8, show P + 90 = 9 + P + 81 by ring, e9,
      show P + 91 = 10 + P + 81 by ring, e10]
    have hc := oq_compress_levelC CM (Ht := Ht) (D := D) (q := q) (sibs := sibs) (l := 0) (by omega)
      (hA 0 (by omega))
    rw [Nat.mul_zero, Nat.zero_add, Nat.zero_add, Nat.zero_add] at hc
    have h0' : σ (.n P) = (climbCellsW Ht D q sibs).getD 0 0 := by simpa using hcs 0 (by omega)
    rw [h0', hcs 1 (by omega), hcs 2 (by omega), hcs 3 (by omega)]
    exact hc
  · rw [holdsListB_flatten_range _ _ (fun _ => rfl)]
    refine ⟨fun j hj => ?_, hn⟩
    have hv := hvl j hj
    set l := j + 1 with hl
    have f := fun t (ht : t < 13) => hv t ht
    have f0 := f 0 (by omega); have f1 := f 1 (by omega); have f2 := f 2 (by omega)
    have f3 := f 3 (by omega); have f4 := f 4 (by omega); have f5 := f 5 (by omega)
    have f6 := f 6 (by omega); have f7 := f 7 (by omega); have f8 := f 8 (by omega)
    have f9 := f 9 (by omega); have f10 := f 10 (by omega); have f11 := f 11 (by omega)
    have f12 := f 12 (by omega)
    simp only [oqPathLValsW, List.getD_cons_zero, List.getD_cons_succ, Nat.zero_add,
      show ∀ t, P + 79 + 13 * l + t = t + (P + 79 + 13 * l) from fun t => by ring]
      at f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12
    simp only [oqLevel, levelT, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, and_true, word_iv0, word_iv1,
      word_md64, word_eOfNat, eOfNat_one, show ∀ t, P + 79 + 13 * l + t = t + (P + 79 + 13 * l) from
        fun t => by ring]
    have hg : kw (gpowK (4 * l)) = gen ^ (4 * l) :=
      kw_gpowK (lt_trans (show 4 * l < 2 ^ 7 by omega) (by decide))
    obtain ⟨m0, m1⟩ := oq_node_loadW (l := l) (by omega) hcell'
    have hprev : σ (.n (P + 77 + 13 * l)) = (digestScalars (climbAtW Ht D q sibs l)).1 ∧
        σ (.n (P + 77 + 13 * l + 1)) = (digestScalars (climbAtW Ht D q sibs l)).2 := by
      rcases j with _ | j
      · rw [show P + 77 + 13 * l + 1 = 10 + P + 81 by omega, show P + 77 + 13 * l = 9 + P + 81 by omega,
          e9, e10]
        exact ⟨rfl, rfl⟩
      · have g := hvl j (by omega)
        have g11 := g 11 (by omega); have g12 := g 12 (by omega)
        simp only [oqPathLValsW, List.getD_cons_zero, List.getD_cons_succ] at g11 g12
        rw [show P + 77 + 13 * l + 1 = P + 79 + 13 * (j + 1) + 12 by omega,
          show P + 77 + 13 * l = P + 79 + 13 * (j + 1) + 11 by omega, g11, g12]
        exact ⟨rfl, rfl⟩
    have hc := oq_compress_levelC CM (Ht := Ht) (D := D) (q := q) (sibs := sibs) (l := l) (by omega)
      (hA l (by omega))
    rw [← hcs (4 * l) (by omega), ← hcs (4 * l + 1) (by omega), ← hcs (4 * l + 2) (by omega),
      ← hcs (4 * l + 3) (by omega)] at hc
    refine ⟨by rw [f0]; exact hbits l (by omega), by rw [f1, hg], by rw [f2, hptr, f1], by rw [f3],
      by rw [f4], by rw [f5, f0, f4], by rw [f6, f3, f5], by rw [f7, f2, f6], ?_, ?_, by rw [f8],
      by rw [f9], by rw [f10], ?_⟩
    · rw [f7, hprev.1]; exact m0
    · rw [f7, show P + 78 + 13 * l = P + 77 + 13 * l + 1 by ring, hprev.2]; exact m1
    · rw [f8, f9, f10, f11, f12]
      simpa [Nat.add_assoc] using hc

/-! ## The blocks without a `BLAKE2S` row -/

theorem oqSumT_noBlake (base I blocks : ℕ) : Stmt.noBlakeList (oqSumT base I blocks) = true := rfl

/-- The row under any semantics, from its deployed relation. -/
theorem oqRows_completeB {S : BlakeSem} {base I : ℕ} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (oqRows base I) next kret) :
    Stmt.HoldsListB S C rd σ (oqRows base I) next kret :=
  (holdsListB_iff_of_noBlake (oqRows_noBlake base I) _ _).mpr h

/-- The query sum under any semantics, from its deployed relation. -/
theorem oqSumT_completeB {S : BlakeSem} {base I blocks : ℕ} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (oqSumT base I blocks) next kret) :
    Stmt.HoldsListB S C rd σ (oqSumT base I blocks) next kret :=
  (holdsListB_iff_of_noBlake (oqSumT_noBlake base I blocks) _ _).mpr h

/-- The cap leaf under any semantics, from its deployed relation. -/
theorem oqCapT_completeB {S : BlakeSem} {P pd cd : ℕ} {loop : String} {next : Prop}
    {kret : List E → Prop} (h : Stmt.HoldsList C rd σ (oqCapT P pd cd loop) next kret) :
    Stmt.HoldsListB S C rd σ (oqCapT P pd cd loop) next kret :=
  (holdsListB_iff_of_noBlake (oqCapT_noBlake P pd cd loop) _ _).mpr h

/-! ## At the deployed model -/

/-- The deployed model's chain of a string of whole blocks is `chainRun`'s. -/
theorem chainSt_deployed_blocks {n : ℕ} (bl : ℕ → Fin 4 → E) {md : ℕ → E}
    (hmd : ∀ j < n, md j = metadataCell (64 * (j + 1)) false) (hfin : md n = metadataCell (64 * (n + 1)) true)
    (hcan : ∀ j ≤ n, ∀ t, IsCanonical128 (bl j t)) :
    ∀ j ≤ n + 1, CompModel.deployed.chainSt ((List.range (n + 1)).flatMap fun j => blockBytes (bl j))
      (blake2sBytes ((List.range (n + 1)).flatMap fun j => blockBytes (bl j))) j =
      digestScalars (chainRun paramIv bl md j) := by
  intro j hj
  induction j with
  | zero => rw [CompModel.chainSt_zero]; rfl
  | succ j ih =>
    have hchk := CompModel.deployed.chain_checks_blocks (n := n) (blocks := bl) (md := md) rfl hcan hmd hfin
      j (by omega)
    rw [ih (by omega)] at hchk
    have hmdc : IsCanonical128 (md j) := by
      rcases Nat.lt_or_ge j n with h | h
      · rw [hmd j h]; exact isCanonical128_metadataCell _ _
      · rw [show j = n by omega, hfin]; exact isCanonical128_metadataCell _ _
    exact Prod.mk.eta.symm.trans ((compressCells_chainRun (h := paramIv) (blocks := bl) (md := md) (i := j)
      (hcan j (by omega)) hmdc).mp hchk)

/-- The deployed `oqLeaf_complete`, from the generic one. -/
theorem oqLeaf_complete_of_comp {base I blocks : ℕ} (hbl : 1 ≤ blocks) {next : Prop} {kret : List E → Prop}
    (hcan : ∀ j < blocks, ∀ t, IsCanonical128 (oqLeafBl σ base I j t))
    (hiv0 : σ (.n (oqK1 base I)) = (digestScalars paramIv).1)
    (hiv1 : σ (.n (oqK1 base I + 1)) = (digestScalars paramIv).2)
    (hmd : ∀ j < blocks, σ (.n (oqK1 base I + 3 * j + 2)) = oqMd blocks j)
    (hst : ∀ j < blocks, (σ (.n (oqK1 base I + 3 * j + 3)), σ (.n (oqK1 base I + 3 * j + 4))) =
      digestScalars (chainRun paramIv (oqLeafBl σ base I) (oqMd blocks) (j + 1))) (hn : next) :
    Stmt.HoldsList C rd σ (oqLeafT base I blocks) next kret := by
  rw [← holdsListB_deployed]
  obtain ⟨n, rfl⟩ : ∃ n, blocks = n + 1 := ⟨blocks - 1, by omega⟩
  have e := chainSt_deployed_blocks (n := n) (oqLeafBl σ base I) (md := oqMd (n + 1))
    (fun j hj => by rw [oqMd_eq]; congr 1; simp only [decide_eq_false_iff_not]; omega)
    (by rw [oqMd_eq]; simp) (fun j hj t => hcan j (by omega) t)
  exact oqLeaf_completeC (CM := CompModel.deployed) hbl hcan rfl hiv0 hiv1 hmd
    (fun j hj => by rw [hst j hj, oqLeafBytes, e (j + 1) (by omega)]) hn

/-- The deployed `oqPathT_complete`, from the generic one. -/
theorem oqPathT_complete_of_comp {base I blocks pd : ℕ} (hpd : 1 ≤ pd) (hpd20 : pd ≤ 20) {D : Digest}
    {q : ℕ} {sibs : List Digest} (hsl : sibs.length = pd) {ptr : E} {next : Prop} {kret : List E → Prop}
    (hK : (σ (.n (oqK1 base I + 3 * blocks)), σ (.n (oqK1 base I + 3 * blocks + 1))) = digestScalars D)
    (hcs : ∀ j < 4 * pd, σ (.n (oqP base I blocks + j)) = (climbCells D q sibs).getD j 0)
    (hptr : σ (.n (oqP base I blocks + 4 * pd)) = ptr) (hptrK : IsInK ptr)
    (hcell : ∀ j < 4 * pd, LoadHolds rd ptr j ((climbCells D q sibs).getD j 0))
    (hfr2 : ∀ j < 80 - 4 * pd, ∀ w, rd (ptr.limb 0 * Parameters.gpow (4 * pd + j)) = some w →
      w = σ (.n (oqP base I blocks + 4 * pd + 1 + j)))
    (hbits : ∀ l < pd, LoadHolds rd (σ (.n (oqP base I blocks - 1))) l (bitE (q.testBit l)))
    (hv0 : ∀ t < 11, σ (.n (oqP base I blocks + 81 + t)) = (oqPath0Vals ptr D q sibs).getD t 0)
    (hvl : ∀ l < pd - 1, ∀ t < 13, σ (.n (oqP base I blocks + 79 + 13 * (l + 1) + t)) =
      (oqPathLVals ptr D q sibs (l + 1)).getD t 0) (hn : next) :
    Stmt.HoldsList C rd σ (oqPathT base I blocks pd) next kret := by
  rw [← holdsListB_deployed]
  have hA : ∀ l < pd, CompModel.deployed.H (climbLvlBytes blake2sBytes D q sibs l) =
      some (climbAtW blake2sBytes D q sibs (l + 1)) := fun l hl =>
    (climb_answered (H := CompModel.deployed.H) (Ht := blake2sBytes)
      (fun x d h => (Option.some.inj h).symm) (climb_some_blake D q sibs)).2 l (by omega)
  exact oqPathT_completeC (CM := CompModel.deployed) (Ht := blake2sBytes) hpd hpd20 hsl hA hK hcs hptr hptrK
    hcell hfr2 hbits hv0 hvl hn

end
end LeanVM.Guest.B1
