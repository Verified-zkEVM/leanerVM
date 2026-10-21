/-
  LeanVM.Guest.B1.Comp.Da.Witness

  LeanDA's algorithms over an answered hash, taken apart: an answered commitment, tree and vector
  digest give every hash they make answered.
-/

module

public import LeanVM.Guest.B1.Comp.Basic
public import LeanVM.Guest.B1.Da.VerifyM

/-!
# An answered witness, taken apart

The converses of W2's `treeRootWith_nodeM`, `treeRootWith_blocks`, `commitCodewordsWith_eqM`
(`Da/TreeM.lean`, `Da/VerifyM.lean`): a commitment, a tree root or a vector digest that LeanDA's
algorithm over a hash model's answers returns (`some`) is the one of the answered trees and
digests (`nodeM`, `ansD`), every hash it makes answered:

* `mapM_option_inv`: an answered `mapM` is answered at every element;
* `treeRootFuel_inv`, `treeRootWith_inv`: an answered tree (`TreeAns`) and its root;
* `treeAns_blocks_inv`: a tree over blocks, answered, has answered blocks under an answered tree
  of their roots (`treeAns_blocks`' converse);
* `commitCodewordsWith_inv`: the cells', rows', trees' and commitment's hashes all answered;
* `vectorDigestWith_inv`: the vector's bytes answered.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- **An answered `mapM` over `Option`** is answered at every element. -/
theorem mapM_option_inv {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (l' : List β), l.mapM f = some l' →
      ∃ h : l'.length = l.length, ∀ i (hi : i < l.length), f l[i] = some (l'[i]'(by omega))
  | [], l', h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun i hi => absurd hi (by simp)⟩
  | a :: l, l', h => by
    rw [List.mapM_cons] at h
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    obtain ⟨hl, hall⟩ := mapM_option_inv f l bs hbs
    refine ⟨by simp [hl], fun i hi => ?_⟩
    rcases i with _ | i
    · simpa using hb
    · simpa using hall i (by simpa using hi)

/-- The answered hash of a byte string, as LeanDA's digest. -/
theorem daHash_some {M : HashModel} {x : List UInt8} {d : LeanDa.Digest}
    (h : Da.daHash M.H x = some d) : M.H x = some (ansD M x) ∧ d = Da.toBytes (ansD M x) := by
  simp only [Da.daHash, Functor.map, Option.map_eq_some_iff] at h
  obtain ⟨a, ha, rfl⟩ := h
  rw [ansD_of ha]
  exact ⟨ha, rfl⟩

/-- **An answered tree, taken apart** (`treeRootFuel_nodeM`'s converse): LeanDA's tree over the
answers of `2^k` leaves, answered, is an answered tree, its root the answered root. -/
theorem treeRootFuel_inv {M : HashModel} : ∀ (k : ℕ) (leaf : ℕ → Digest) (fuel : ℕ),
    k ≤ fuel → ∀ {r : LeanDa.Digest},
    Da.treeRootFuel (Da.daHash M.H) fuel ((List.range (2 ^ k)).map fun i => Da.toBytes (leaf i)) =
      some r → TreeAns M leaf k ∧ r = Da.toBytes (nodeM M leaf k 0)
  | 0, leaf, fuel, _, r, h => by
    cases fuel <;> simp [Da.treeRootFuel, nodeM, nodeH] at h ⊢ <;>
      exact ⟨fun l hl => absurd hl (by omega), h.symm⟩
  | k + 1, leaf, fuel, hf, r, h => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hlen : ((List.range (2 ^ (k + 1))).map fun i => Da.toBytes (leaf i)).length =
        2 * 2 ^ k := by simp [pow_succ, mul_comm]
    rw [Da.treeRootFuel, ite_neg' (by rw [hlen]; have := Nat.one_le_two_pow (n := k); omega)] at h
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨next, hnext, h⟩ := h
    rw [Da.treeLevelWith, hlen, show 2 * 2 ^ k / 2 = 2 ^ k by omega] at hnext
    obtain ⟨hl, hall⟩ := mapM_option_inv _ _ _ hnext
    have hl2 : next.length = 2 ^ k := by rw [hl]; simp
    -- each pair answered
    have hpair : ∀ i (hi : i < 2 ^ k), M.H (digestBytes (leaf (2 * i)) ++ digestBytes (leaf (2 * i + 1))) =
        some (pairM M (leaf (2 * i)) (leaf (2 * i + 1))) ∧
        next[i]'(by rw [hl2]; exact hi) = Da.toBytes (pairM M (leaf (2 * i)) (leaf (2 * i + 1))) := by
      intro i hi
      have := hall i (by simpa using hi)
      simp only [List.getElem_range] at this
      rw [List.getD_eq_getElem _ _ (by rw [hlen]; omega),
        List.getD_eq_getElem _ _ (by rw [hlen]; omega)] at this
      simp only [List.getElem_map, List.getElem_range] at this
      rw [pairBytes_toBytes] at this
      exact daHash_some this
    have hnext' : next = (List.range (2 ^ k)).map fun i =>
        Da.toBytes (pairM M (leaf (2 * i)) (leaf (2 * i + 1))) := by
      apply List.ext_getElem (by simp [hl2])
      intro i h1 h2
      simp only [List.getElem_map, List.getElem_range]
      exact (hpair i (by simpa using h2)).2
    rw [hnext'] at h
    obtain ⟨hA, hr⟩ := treeRootFuel_inv k (fun i => pairM M (leaf (2 * i)) (leaf (2 * i + 1))) f
      (by omega) h
    refine ⟨fun l hl i hi => ?_, ?_⟩
    · rcases l with _ | l
      · simp only [nodeM, nodeH]
        exact (hpair i (by simpa using hi)).1
      · have := hA l (by omega) i (by rwa [show k + 1 - (l + 1) - 1 = k - l - 1 by omega] at hi)
        simp only [nodeM] at this ⊢
        rw [nodeH_succ, nodeH_succ, nodeH_succ]
        exact this
    · rw [hr]
      simp only [nodeM]
      rw [nodeH_succ]

/-- **An answered tree, taken apart** (`treeRootWith_nodeM`'s converse). -/
theorem treeRootWith_inv {M : HashModel} {k : ℕ} {leaf : ℕ → Digest} {r : LeanDa.Digest}
    (h : Da.treeRootWith (Da.daHash M.H) ((List.range (2 ^ k)).map fun i => Da.toBytes (leaf i)) =
      some r) : TreeAns M leaf k ∧ r = Da.toBytes (nodeM M leaf k 0) :=
  treeRootFuel_inv k leaf _ (by simpa using (Nat.lt_two_pow_self (n := k)).le) h

/-- **An answered tree over blocks, taken apart** (`treeAns_blocks`' converse): every block is an
answered tree, under an answered tree of their roots. -/
theorem treeAns_blocks_inv {M : HashModel} {a c : ℕ} {L : ℕ → ℕ → Digest}
    (h : TreeAns M (blkLeaf a L) (a + c)) :
    (∀ j < 2 ^ c, TreeAns M (L j) a) ∧ TreeAns M (fun j => nodeM M (L j) a 0) c := by
  refine ⟨fun j hj l hl t ht => ?_, fun c' hc' i hi => ?_⟩
  · -- inside block `j`
    set P := 2 ^ (a - l - 1) with hP
    have hP0 : 0 < P := by positivity
    have hpow : 2 ^ (a - l) = 2 * P := by rw [hP, ← pow_succ']; congr 1; omega
    have hpow1 : 2 ^ (a - (l + 1)) = P := by rw [hP]; congr 1
    have hi : P * j + t < 2 ^ (a + c - l - 1) := by
      have : 2 ^ (a + c - l - 1) = P * 2 ^ c := by
        rw [hP, ← pow_add]; congr 1; omega
      rw [this]
      have : P * j + t < P * (j + 1) := by rw [Nat.mul_succ]; omega
      exact lt_of_lt_of_le this (Nat.mul_le_mul_left _ hj)
    have := h l (by omega) (P * j + t) hi
    simp only [nodeM] at this ⊢
    have e0 : 2 * (P * j + t) = 2 ^ (a - l) * j + 2 * t := by rw [hpow]; ring
    have e1 : 2 * (P * j + t) + 1 = 2 ^ (a - l) * j + (2 * t + 1) := by rw [hpow]; ring
    rw [e1, e0, nodeH_blk _ a L l hl.le j (2 * t) (by omega),
      nodeH_blk _ a L l hl.le j (2 * t + 1) (by omega),
      show P * j + t = 2 ^ (a - (l + 1)) * j + t by rw [hpow1],
      nodeH_blk _ a L (l + 1) hl j t (by omega)] at this
    exact this
  · -- the top tree
    have := h (a + c') (by omega) i (by rwa [show a + c - (a + c') - 1 = c - c' - 1 by omega])
    simp only [nodeM] at this ⊢
    rw [nodeH_top, nodeH_top, show a + c' + 1 = a + (c' + 1) by ring, nodeH_top] at this
    exact this

/-- **An answered vector digest, taken apart**: the vector's bytes answered. -/
theorem vectorDigestWith_inv {M : HashModel} {v : List E} {vd : Digest}
    (h : Da.vectorDigestWith (Da.daHash M.H) v = some (Da.toBytes vd)) :
    M.H (v.flatMap LeanVM.Node.eBytes) = some vd := by
  rw [Da.vectorDigestWith, vector_bytes] at h
  obtain ⟨ha, hd⟩ := daHash_some h
  rw [ha, toBytes_injective hd]

/-- An answered `mapM` over `Option` answers every member. -/
theorem mapM_option_inv_mem {α β : Type} {f : α → Option β} {l : List α} {l' : List β}
    (h : l.mapM f = some l') : ∀ a ∈ l, ∃ b, f a = some b := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  obtain ⟨hl, hall⟩ := mapM_option_inv f l l' h
  exact ⟨_, hall i hi⟩

/-- An answered cell digest, LeanDA's (`listCellDigestWith`). -/
theorem listCellDigestWith_inv {M : HashModel} {row : List K} {j : ℕ} {d : LeanDa.Digest}
    (h : Da.listCellDigestWith (Da.daHash M.H) row j = some d) :
    M.H ((LeanDa.listCell row j).flatMap kBytes) =
        some (ansD M ((LeanDa.listCell row j).flatMap kBytes)) ∧
      d = Da.toBytes (ansD M ((LeanDa.listCell row j).flatMap kBytes)) := by
  rw [Da.listCellDigestWith, show (LeanDa.listCell row j).flatMap LeanDa.kBytes =
    (LeanDa.listCell row j).flatMap kBytes from List.flatMap_congr fun a _ => leanDa_kBytes a] at h
  exact daHash_some h

/-- **An answered row digest, LeanDA's, taken apart** (`rowDigestWith`): its 64 payload cells'
digests and its own hash answered. -/
theorem rowDigestWith_inv {M : HashModel} {row : List K} {d : LeanDa.Digest}
    (h : Da.rowDigestWith (Da.daHash M.H) row = some d) :
    (∀ j < 64, M.H ((LeanDa.listCell row j).flatMap kBytes) =
        some (ansD M ((LeanDa.listCell row j).flatMap kBytes))) ∧
      M.H ((List.range 64).flatMap fun j => digestBytes (ansD M ((LeanDa.listCell row j).flatMap kBytes))) =
        some (ansD M ((List.range 64).flatMap fun j =>
          digestBytes (ansD M ((LeanDa.listCell row j).flatMap kBytes)))) ∧
      d = Da.toBytes (ansD M ((List.range 64).flatMap fun j =>
          digestBytes (ansD M ((LeanDa.listCell row j).flatMap kBytes)))) := by
  rw [Da.rowDigestWith] at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨ds, hds, h⟩ := h
  have hcd : ∀ j < 64, M.H ((LeanDa.listCell row j).flatMap kBytes) =
      some (ansD M ((LeanDa.listCell row j).flatMap kBytes)) ∧
      Da.listCellDigestWith (Da.daHash M.H) row j =
        some (Da.toBytes (ansD M ((LeanDa.listCell row j).flatMap kBytes))) := by
    intro j hj
    obtain ⟨b, hb⟩ := mapM_option_inv_mem hds j (List.mem_range.mpr hj)
    obtain ⟨e1, e2⟩ := listCellDigestWith_inv hb
    exact ⟨e1, by rw [hb, e2]⟩
  have hds' : ds = (List.range 64).map fun j =>
      Da.toBytes (ansD M ((LeanDa.listCell row j).flatMap kBytes)) := by
    have := mapM_option_some_mem (fun j => Da.listCellDigestWith (Da.daHash M.H) row j)
      (fun j => Da.toBytes (ansD M ((LeanDa.listCell row j).flatMap kBytes)))
      (List.range LeanDa.payloadCells) fun j hj => (hcd j (List.mem_range.mp hj)).2
    rw [hds] at this
    exact Option.some.inj this
  subst hds'
  rw [List.flatMap_map] at h
  simp only [toBytes_toList] at h
  obtain ⟨e1, e2⟩ := daHash_some h
  exact ⟨fun j hj => (hcd j hj).1, e1, e2⟩

/-- **An answered commitment, LeanDA's, taken apart** (`commitCodewordsWith_eqM`'s converse): with
the guest's padding digests, every cell's, row's and tree node's hash is answered, and the
commitment is the answer for the two roots. -/
theorem commitCodewordsWith_inv {M : HashModel} {rows : List (List K)} (hr : 1 ≤ rows.length)
    {root : Digest}
    (h : Da.commitCodewordsWith (Da.daHash M.H) (Da.toBytes padCellD) (Da.toBytes padRowD) rows =
      some (Da.toBytes root)) :
    let r := rows.length
    let cD : ℕ → ℕ → Digest := fun b i => ansD M ((LeanDa.listCell (rows.getD i []) b).flatMap kBytes)
    let rD : ℕ → Digest := fun i => ansD M ((List.range 64).flatMap fun b => digestBytes (cD b i))
    (∀ b < 128, ∀ i < r, M.H ((LeanDa.listCell (rows.getD i []) b).flatMap kBytes) = some (cD b i)) ∧
    (∀ i < r, M.H ((List.range 64).flatMap fun b => digestBytes (cD b i)) = some (rD i)) ∧
    TreeAns M (rowLeafM r rD) (LeanDa.logPad r) ∧
    (∀ b < 128, TreeAns M (colLeafM r cD b) (LeanDa.logPad r)) ∧
    TreeAns M (fun b => nodeM M (colLeafM r cD b) (LeanDa.logPad r) 0) 7 ∧
    M.H (digestBytes (nodeM M (rowLeafM r rD) (LeanDa.logPad r) 0) ++
      digestBytes (nodeM M (fun b => nodeM M (colLeafM r cD b) (LeanDa.logPad r) 0) 7 0)) =
        some root := by
  intro r cD rD
  obtain ⟨hrN, -⟩ := (logPad_iff (lp := LeanDa.logPad rows.length) hr).mp rfl
  have hNdef : LeanDa.nPad rows.length = 2 ^ LeanDa.logPad rows.length := rfl
  have hget : ∀ i (hi : i < rows.length), rows[i] = rows.getD i [] := fun i hi =>
    (List.getD_eq_getElem _ _ hi).symm
  simp only [Da.commitCodewordsWith, bind, Option.bind_eq_some_iff] at h
  obtain ⟨rds, hrds, rowTree, hrt, cols, hcols, colTree, hct, hfin⟩ := h
  -- the rows
  obtain ⟨hrl, hrall⟩ := mapM_option_inv _ _ _ hrds
  have hrow : ∀ i (hi : i < rows.length), (∀ j < 64,
      M.H ((LeanDa.listCell (rows.getD i []) j).flatMap kBytes) = some (cD j i)) ∧
      M.H ((List.range 64).flatMap fun b => digestBytes (cD b i)) = some (rD i) ∧
      rds[i]'(by rw [hrl]; exact hi) = Da.toBytes (rD i) := by
    intro i hi
    have := hrall i hi
    rw [hget i hi] at this
    exact rowDigestWith_inv this
  have hrds' : rds = (List.range rows.length).map fun i => Da.toBytes (rD i) := by
    apply List.ext_getElem (by simp [hrl])
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    exact (hrow i (by simpa using h2)).2.2
  have hrowList : rds ++ List.replicate (LeanDa.nPad rows.length - rows.length)
      (Da.toBytes padRowD) =
      (List.range (2 ^ LeanDa.logPad rows.length)).map fun i => Da.toBytes (rowLeafM rows.length rD i) := by
    rw [hrds']
    apply List.ext_getElem (by simp; rw [← hNdef]; omega)
    intro i h1 h2
    simp only [List.length_map, List.length_range] at h2
    by_cases hir : i < rows.length
    · rw [List.getElem_append_left (by simp; omega)]
      simp only [List.getElem_map, List.getElem_range, rowLeafM, hir, ↓reduceIte]
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.getElem_replicate, List.getElem_map, List.getElem_range, rowLeafM, hir,
        ↓reduceIte]
  rw [hrowList] at hrt
  obtain ⟨hRT, hrt'⟩ := treeRootWith_inv hrt
  -- the columns
  have hcell : ∀ ij ∈ ((List.range LeanDa.cellsPerRow).flatMap fun j =>
      (List.range (LeanDa.nPad rows.length)).map fun i => (i, j)),
      (fun ij => if h : ij.1 < rows.length then
        Da.listCellDigestWith (Da.daHash M.H) rows[ij.1] ij.2 else pure (Da.toBytes padCellD)) ij =
        some (Da.toBytes (colLeafM rows.length cD ij.2 ij.1)) ∧
      (ij.1 < rows.length → M.H ((LeanDa.listCell (rows.getD ij.1 []) ij.2).flatMap kBytes) =
        some (cD ij.2 ij.1)) := by
    intro ij hij
    obtain ⟨b, hb⟩ := mapM_option_inv_mem hcols ij hij
    by_cases hir : ij.1 < rows.length
    · simp only [hir, ↓reduceDIte] at hb ⊢
      rw [hget _ hir] at hb ⊢
      obtain ⟨e1, e2⟩ := listCellDigestWith_inv hb
      refine ⟨by rw [hb, e2]; simp only [colLeafM, hir, ↓reduceIte, cD], fun _ => e1⟩
    · simp only [hir, ↓reduceDIte, colLeafM, ↓reduceIte, false_implies, and_true]
      rfl
  have hcols' : cols = (List.range (2 ^ 7)).flatMap fun j =>
      (List.range (2 ^ LeanDa.logPad rows.length)).map fun i => Da.toBytes (colLeafM rows.length cD j i) := by
    have := mapM_option_some_mem _ (fun ij => Da.toBytes (colLeafM rows.length cD ij.2 ij.1)) _
      (fun ij hij => (hcell ij hij).1)
    rw [hcols, List.map_flatMap, show LeanDa.cellsPerRow = 2 ^ 7 from rfl, hNdef] at this
    rw [Option.some.inj this]
    refine List.flatMap_congr fun j _ => ?_
    rw [List.map_map]
    rfl
  rw [hcols'] at hct
  have e : (List.range (2 ^ 7)).flatMap (fun j => (List.range (2 ^ LeanDa.logPad rows.length)).map fun i =>
      Da.toBytes (colLeafM rows.length cD j i)) = (List.range (2 ^ (LeanDa.logPad rows.length + 7))).map fun m =>
        Da.toBytes (blkLeaf (LeanDa.logPad rows.length) (fun j i => colLeafM rows.length cD j i) m) := by
    rw [pow_add, map_range_mul_blocks]
    refine List.flatMap_congr fun j _ => List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    have hp : 0 < 2 ^ LeanDa.logPad rows.length := by positivity
    simp only [blkLeaf]
    rw [show (2 ^ LeanDa.logPad rows.length * j + i) / 2 ^ LeanDa.logPad rows.length = j by
        rw [Nat.add_comm, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hi', Nat.zero_add],
      show (2 ^ LeanDa.logPad rows.length * j + i) % 2 ^ LeanDa.logPad rows.length = i by
        rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi']]
  rw [e] at hct
  obtain ⟨hBT, hct'⟩ := treeRootWith_inv hct
  obtain ⟨hCT, hTop⟩ := treeAns_blocks_inv hBT
  -- the commitment
  rw [hrt', hct', pairBytes_toBytes] at hfin
  obtain ⟨hH, hroot⟩ := daHash_some hfin
  have hroot' := toBytes_injective hroot
  refine ⟨fun b hb i hi => ?_, fun i hi => (hrow i hi).2.1, hRT, fun b hb => hCT b (by simpa using hb),
    hTop, ?_⟩
  · refine (hcell (i, b) ?_).2 hi
    refine List.mem_flatMap.mpr ⟨b, List.mem_range.mpr (by simpa [LeanDa.cellsPerRow] using hb), ?_⟩
    exact List.mem_map.mpr ⟨i, List.mem_range.mpr (by rw [hNdef]; omega), rfl⟩
  · rw [hroot']
    simp only [nodeM] at hH ⊢
    rw [nodeH_top] at hH ⊢
    exact hH

end
end LeanVM.Guest.B1.Digest
