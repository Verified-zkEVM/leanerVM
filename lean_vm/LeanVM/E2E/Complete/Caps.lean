/-
  LeanVM.E2E.Complete.Caps

  The honest prover's openings agree in the guest's Merkle caps: one tree's openings at positions
  below its leaf count give every heap node the tree's label, and the compiled verifier's query
  steps on an honest proof are such openings, when the program queries every tree below its leaf
  count.
-/

module

public import LeanVM.E2E.Complete.Interfaces
public import LeanVM.E2E.Complete.FsRun

/-!
# The honest openings agree

The guest keeps one Merkle cap per committed tree, written once per heap node; its completeness
asks that the openings of one query step agree wherever they meet (`CapsAgreeWith`,
`BatchAgreesWith`, `NodeIsWith`). The honest prover's openings are one tree's:

* `heapLabel`: the heap labelling of the tree over a level (the root at `1`, the children of `v`
  at `2v`, `2v + 1`); `climb_take_label`, `getD_path_label`: an honest path's climb, at every
  level, and its siblings are the labels of their heap nodes (`heapNode`, `sibNode`);
* `batchAgreesWith_openingAt`: honest openings at positions below `2^height` agree: what each
  gives a node is its label;
* `QRange hts p`: every query of `p` opens its tree at positions below the tree's leaf count, the
  heights `hts` of the trees committed so far extended by `p`'s commitments;
* `queriesOfWith_proveFrom`: along the Fiat–Shamir run (`FsRun.lean`), every query step of the
  compiled verifier on the honest proof of a program of queries in range is a step of honest
  openings, so they agree.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Guest.B1

@[expose] public section

/-! ## The heap labelling of a tree -/

section Label

variable (hp : Digest → Digest → Digest)

/-- **The heap labelling** of the tree over a level of `2^k` digests: the level at the heap
indices `[2^k, 2^(k+1))`, its parents' tree above. -/
def heapLabel : (k : ℕ) → Vector Digest (2 ^ k) → ℕ → Digest
  | 0, level, _ => level[0]
  | k + 1, level, v =>
    if 2 ^ (k + 1) ≤ v then level.toList.getD (v - 2 ^ (k + 1)) default
    else heapLabel k (MerkleTree.parents hp level) v

theorem heapLabel_level {k : ℕ} (level : Vector Digest (2 ^ (k + 1))) {i : ℕ}
    (hi : i < 2 ^ (k + 1)) : heapLabel hp (k + 1) level (2 ^ (k + 1) + i) = level[i] := by
  simp only [heapLabel, Nat.le_add_right, ↓reduceIte, Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

theorem heapLabel_up {k : ℕ} (level : Vector Digest (2 ^ (k + 1))) {v : ℕ}
    (hv : v < 2 ^ (k + 1)) :
    heapLabel hp (k + 1) level v = heapLabel hp k (MerkleTree.parents hp level) v := by
  simp only [heapLabel, show ¬ 2 ^ (k + 1) ≤ v by omega, ↓reduceIte]

/-- The heap node at level `l ≤ k` above leaf `i < 2^k` is below `2^(k - l + 1)`. -/
theorem heapNode_lt {k i l : ℕ} (hi : i < 2 ^ k) (hl : l ≤ k) :
    heapNode k i l < 2 ^ (k - l + 1) := by
  unfold heapNode
  have h1 : i / 2 ^ l < 2 ^ (k - l) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show k - l + l = k by omega]
    exact hi
  rw [pow_succ]
  omega

/-- One level up: the heap node above leaf `i` at level `l + 1` is the one above `i / 2` at `l`. -/
theorem heapNode_succ_div {k i l : ℕ} : heapNode (k + 1) i (l + 1) = heapNode k (i / 2) l := by
  unfold heapNode
  rw [Nat.div_div_eq_div_mul, ← pow_succ', Nat.add_sub_add_right]

/-- **An honest path's climb is the label of its heap node**, at every level. -/
theorem climb_take_label : ∀ (k : ℕ) (level : Vector Digest (2 ^ k)) (i : ℕ) (hi : i < 2 ^ k)
    (l : ℕ), l ≤ k →
      MerkleTree.climb hp level[i] i ((MerkleTree.pathOfLevel hp k level ⟨i, hi⟩).take l) =
        heapLabel hp k level (heapNode k i l)
  | 0, level, i, hi, l, hl => by
    obtain rfl : l = 0 := by omega
    obtain rfl : i = 0 := by simpa using hi
    simp [MerkleTree.climb, heapLabel]
  | k + 1, level, i, hi, 0, _ => by
    simp only [List.take_zero, MerkleTree.climb, heapNode, Nat.sub_zero, pow_zero, Nat.div_one]
    exact (heapLabel_level hp level hi).symm
  | k + 1, level, i, hi, l + 1, hl => by
    rw [MerkleTree.pathOfLevel, List.take_succ_cons, MerkleTree.climb]
    have hpar : (if i % 2 = 0 then hp level[i] (level[MerkleTree.sibling i]'
        (MerkleTree.sibling_lt hi)) else hp (level[MerkleTree.sibling i]'
        (MerkleTree.sibling_lt hi)) level[i]) =
        (MerkleTree.parents hp level)[i / 2]'(MerkleTree.div_two_lt hi) := by
      rw [MerkleTree.getElem_parents]
      unfold MerkleTree.sibling
      split
      · simp only [show 2 * (i / 2) = i by omega]
      · simp only [show 2 * (i / 2) = i - 1 by omega, show i - 1 + 1 = i by omega]
    rw [hpar, climb_take_label k _ (i / 2) (MerkleTree.div_two_lt hi) l (by omega),
      heapNode_succ_div, heapLabel_up hp level]
    have := heapNode_lt (MerkleTree.div_two_lt hi) (show l ≤ k by omega)
    have h2 : 2 ^ (k - l + 1) ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-- **An honest path's siblings are the labels of their heap nodes.** -/
theorem getD_path_label : ∀ (k : ℕ) (level : Vector Digest (2 ^ k)) (i : ℕ) (hi : i < 2 ^ k)
    (l : ℕ), l < k →
      (MerkleTree.pathOfLevel hp k level ⟨i, hi⟩).getD l default =
        heapLabel hp k level (sibNode k i l)
  | 0, _, _, _, l, hl => absurd hl (Nat.not_lt_zero l)
  | k + 1, level, i, hi, 0, _ => by
    rw [MerkleTree.pathOfLevel, List.getD_cons_zero]
    have hs : sibNode (k + 1) i 0 = 2 ^ (k + 1) + MerkleTree.sibling i := by
      unfold sibNode heapNode MerkleTree.sibling
      rw [show k + 1 - (0 + 1) = k by omega, Nat.testBit_zero, pow_succ, pow_zero, one_mul]
      rcases Nat.mod_two_eq_zero_or_one i with h | h <;> simp [h] <;> omega
    rw [hs, heapLabel_level hp level (MerkleTree.sibling_lt hi)]
  | k + 1, level, i, hi, l + 1, hl => by
    rw [MerkleTree.pathOfLevel, List.getD_cons_succ,
      getD_path_label k _ (i / 2) (MerkleTree.div_two_lt hi) l (by omega)]
    have hs : sibNode (k + 1) i (l + 1) = sibNode k (i / 2) l := by
      unfold sibNode
      rw [heapNode_succ_div, Nat.testBit_succ]
    rw [hs, heapLabel_up hp level]
    have h1 := heapNode_lt (MerkleTree.div_two_lt hi) (show l + 1 ≤ k by omega)
    have h2 : 2 ^ (k - (l + 1) + 1) * 2 ≤ 2 ^ (k + 1) := by
      rw [← pow_succ]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    unfold sibNode
    have := Bool.toNat_le (!(i / 2).testBit l)
    omega

end Label

/-! ## Honest openings agree -/

/-- A pair of a list zipped with its image is a member and its image. -/
theorem mem_zip_map_self {α β : Type} (f : α → β) :
    ∀ {l : List α} {a : α} {b : β}, (a, b) ∈ l.zip (l.map f) → a ∈ l ∧ b = f a
  | [], _, _, h => by simp at h
  | x :: l, a, b, h => by
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · exact ⟨List.mem_cons_self, rfl⟩
    · obtain ⟨h1, h2⟩ := mem_zip_map_self f h
      exact ⟨List.mem_cons_of_mem _ h1, h2⟩

/-- Zipping a list with its image followed by more drops the more. -/
theorem zip_map_append {α β : Type} (f : α → β) (r : List β) :
    ∀ l : List α, l.zip (l.map f ++ r) = l.zip (l.map f)
  | [] => rfl
  | x :: l => by simp only [List.map_cons, List.cons_append, List.zip_cons_cons, zip_map_append f r l]

variable (H : Bytes → Digest)

/-- **What an honest opening gives a node is the node's label**, at a position below the leaf
count. -/
theorem nodeIsWith_openingAt {ht : ℕ} {word : Word} {q : ℕ} (hq : q < 2 ^ ht) {v : ℕ}
    {d : Digest} (h : NodeIsWith H ht (q, openingAt H ht word q) v d) :
    d = heapLabel (nodeHash H) ht ((leavesOf ht word).map (leafHash H)) v := by
  have hmod : q % 2 ^ ht = q := Nat.mod_eq_of_lt hq
  have hfin : (⟨q % 2 ^ ht, Nat.mod_lt _ (Nat.two_pow_pos ht)⟩ : Fin (2 ^ ht)) = ⟨q, hq⟩ :=
    Fin.ext hmod
  have hpath : (openingAt H ht word q).path =
      MerkleTree.pathOfLevel (nodeHash H) ht ((leavesOf ht word).map (leafHash H)) ⟨q, hq⟩ := by
    simp only [openingAt, MerkleTree.path, hfin]
  have hleaf : H ((openingAt H ht word q).leaf.flatMap kBytes) =
      ((leavesOf ht word).map (leafHash H))[q] := by
    simp [openingAt, hmod, leavesOf, leafHash]
  rcases h with ⟨l, hl, rfl, rfl⟩ | ⟨l, hl, rfl, rfl⟩
  · simp only
    rw [climb_eq_merkleClimb, hleaf, hpath]
    exact climb_take_label _ ht _ q hq l hl
  · simp only
    rw [hpath]
    exact getD_path_label _ ht _ q hq l hl

/-- **Honest openings agree** wherever they meet, at positions below the leaf count. -/
theorem batchAgreesWith_openingAt {ht : ℕ} {word : Word} {ps : List ℕ}
    (hps : ∀ q ∈ ps, q < 2 ^ ht) :
    BatchAgreesWith H ht (ps.zip (ps.map (openingAt H ht word))) := by
  rintro ⟨q, o⟩ ha ⟨q', o'⟩ hb v d d' hd hd'
  obtain ⟨hq, rfl⟩ := mem_zip_map_self _ ha
  obtain ⟨hq', rfl⟩ := mem_zip_map_self _ hb
  rw [nodeIsWith_openingAt H (hps q hq) hd, nodeIsWith_openingAt H (hps q' hq') hd']

/-! ## Queries in range -/

/-- **Every query of `p` is in range**: it opens its tree at positions below the tree's leaf
count, the trees' heights being `hts` extended by `p`'s commitments in order. -/
def QRange {α : Type} (hts : List ℕ) : Prog α → Prop
  | .ret _ => True
  | .fail => True
  | .read k => ∀ x, QRange hts (k x)
  | .sample k => ∀ x, QRange hts (k x)
  | .grind _ k => QRange hts k
  | .commit ht _ k => QRange (hts ++ [ht]) k
  | .query i ps k => (∀ q ∈ ps, ∀ ht, hts[i]? = some ht → q < 2 ^ ht) ∧ ∀ rows, QRange hts (k rows)

variable (S : Strategy) (fuel : ℕ)

/-- **The query steps on an honest proof are honest openings**: along the Fiat–Shamir run of a
program of queries in range, with well-shaped commitments so far, every query step of the
compiled verifier on the honest proof (and anything after it) agrees. -/
theorem queriesOfWith_proveFrom {α : Type} :
    ∀ (p : Prog α) (h : List Ev) (cv : Digest) (xs : List E) (os : List Opening)
      (restS : List E) (restO : List Opening) (r : α × Digest × List Ev),
      fsRun H S fuel p cv h = some r → (∀ c ∈ commits h, WellShaped c.2.1 c.2.2) →
      QRange ((commits h).map (·.1)) p → proveFrom H S fuel p cv h = some (xs, os) →
      ∀ b ∈ queriesOfWith H p ⟨cv, xs ++ restS, os ++ restO, rootsOf H (commits h)⟩,
        BatchAgreesWith H b.1 b.2 := by
  intro p
  induction p with
  | ret a => intros; simp_all [queriesOfWith]
  | fail => intros; simp_all [queriesOfWith]
  | read k ih =>
    intro h cv xs os restS restO r hacc hws hq hp b hb
    simp only [proveFrom] at hp
    obtain ⟨t, ht, he⟩ := Option.map_eq_some_iff.mp hp
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have hws' : ∀ c ∈ commits (h ++ [Ev.read (S.msg h)]), WellShaped c.2.1 c.2.2 := by
      simpa [commits_append, commits] using hws
    have hc : commits (h ++ [Ev.read (S.msg h)]) = commits h := by simp [commits_append, commits]
    simp only [queriesOfWith, List.cons_append] at hb
    refine ih (S.msg h) _ _ t.1 t.2 restS restO r hacc hws' (by rw [hc]; exact hq _) ht b ?_
    rw [hc]
    exact hb
  | sample k ih =>
    intro h cv xs os restS restO r hacc hws hq hp b hb
    simp only [proveFrom] at hp
    have hc : commits (h ++ [Ev.sample (challengeOf (H (digestBytes cv ++ blockOf 0 2)))]) =
        commits h := by simp [commits_append, commits]
    have hws' : ∀ c ∈ commits (h ++ [Ev.sample (challengeOf (H (digestBytes cv ++ blockOf 0 2)))]),
        WellShaped c.2.1 c.2.2 := by rw [hc]; exact hws
    simp only [queriesOfWith] at hb
    refine ih _ _ _ xs os restS restO r hacc hws' (by rw [hc]; exact hq _) hp b ?_
    rw [hc]
    exact hb
  | grind bits k ih =>
    intro h cv xs os restS restO r hacc hws hq hp b hb
    simp only [proveFrom] at hp
    split at hp
    · exact absurd hp (by simp)
    · rename_i n hn
      simp only [fsRun, hn] at hacc
      obtain ⟨t, ht, he⟩ := Option.map_eq_some_iff.mp hp
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hc : commits (h ++ [Ev.grind bits]) = commits h := by simp [commits_append, commits]
      have hws' : ∀ c ∈ commits (h ++ [Ev.grind bits]), WellShaped c.2.1 c.2.2 := by
        rw [hc]; exact hws
      have hpow := powOk_of_findNonce H hn
      simp only [queriesOfWith, List.cons_append] at hb
      have hpow' : powOk bits n (absorbBlock (m := Id) H (absorbBlock (m := Id) H cv
          (blockOf 0 3)) (blockOf n 4)) = true := hpow
      simp only [hpow', ↓reduceIte] at hb
      refine ih _ _ t.1 t.2 restS restO r hacc hws' (by rw [hc]; exact hq) ht b ?_
      rw [hc]
      exact hb
  | commit ht w k ih =>
    intro h cv xs os restS restO r hacc hws hq hp b hb
    simp only [fsRun] at hacc
    split at hacc
    · rename_i hw
      simp only [proveFrom] at hp
      obtain ⟨t, htt, he⟩ := Option.map_eq_some_iff.mp hp
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hws' : ∀ c ∈ commits (h ++ [Ev.commit ht w (S.word h)]), WellShaped c.2.1 c.2.2 := by
        simp only [commits_append, commits, List.mem_append, List.mem_singleton]
        rintro c (hc | rfl)
        · exact hws c hc
        · exact hw
      have hdec : digestOfScalars ((digestScalars (treeRoot H ht (S.word h))).1,
          (digestScalars (treeRoot H ht (S.word h))).2) = some (treeRoot H ht (S.word h)) :=
        digestOfScalars_digestScalars _
      have hroots : rootsOf H (commits (h ++ [Ev.commit ht w (S.word h)])) =
          rootsOf H (commits h) ++ [(treeRoot H ht (S.word h), ht, w)] := by
        simp [rootsOf, commits_append, commits]
      have hhts : (commits (h ++ [Ev.commit ht w (S.word h)])).map (·.1) =
          (commits h).map (·.1) ++ [ht] := by simp [commits_append, commits]
      simp only [queriesOfWith, List.cons_append, hdec] at hb
      refine ih _ _ t.1 t.2 restS restO r hacc hws' (by rw [hhts]; exact hq) htt b ?_
      rw [hroots]
      exact hb
    · exact absurd hacc (by simp)
  | query i ps k ih =>
    intro h cv xs os restS restO r hacc hws hq hp b hb
    simp only [fsRun] at hacc
    simp only [proveFrom] at hp
    split at hp
    · rename_i hc
      simp [hc] at hacc
    · rename_i ht w word hc
      simp only [hc] at hacc
      obtain ⟨t, htt, he⟩ := Option.map_eq_some_iff.mp hp
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hc' : commits (h ++ [Ev.query (ps.map fun q ↦ word (q % 2 ^ ht))]) = commits h := by
        simp [commits_append, commits]
      have hws' : ∀ c ∈ commits (h ++ [Ev.query (ps.map fun q ↦ word (q % 2 ^ ht))]),
          WellShaped c.2.1 c.2.2 := by rw [hc']; exact hws
      have hw : WellShaped w word := hws _ (List.mem_of_getElem? hc)
      have hroot : (rootsOf H (commits h))[i]? = some (treeRoot H ht word, ht, w) := by
        simp [rootsOf, hc]
      have hopen := openAll_openingAt H hw (height := ht) ps (t.2 ++ restO)
      have hht : ((commits h).map (·.1))[i]? = some ht := by simp [hc]
      simp only [queriesOfWith, hroot, List.append_assoc] at hb
      rw [hopen] at hb
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · simp only
        rw [zip_map_append]
        exact batchAgreesWith_openingAt H fun q hq' ↦ hq.1 q hq' ht hht
      · refine ih _ _ _ t.1 t.2 restS restO r hacc hws' (by rw [hc']; exact hq.2 _) htt b ?_
        rw [hc']
        exact hb

end
end LeanVM.E2E.Complete
