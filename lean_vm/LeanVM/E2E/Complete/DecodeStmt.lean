/-
  LeanVM.E2E.Complete.DecodeStmt

  The decoder's statement of an honest child: on a memory whose coverage table reads the honest
  marks (or nothing) and whose tables hold the honest claims at the slots the child's loads name,
  `kidStmt` is the child's statement.
-/

module

public import LeanVM.Guest.B1.Main.ChildSlots
public import LeanVM.Guest.B1.Main.WritersW
public import LeanVM.Guest.B1.Main.Sound
public import LeanVM.Guest.B1.Sig.Callees

/-!
# The children's statements, decoded

`B1.Main.kidStmt rd F T cnt c` reads child `c`'s statement off `main`'s frame: the claims of the
coverage table's slots marked with the child's writers' numbers `cnt c ≤ e < cnt (c + 1)`
(`slotOf`, the first slot holding `g^e`), by region (`entryX`, `entryS`, `daOf`), and its deferred
cells (`decDefer`). `kidStmt_honest`: on a memory whose coverage table holds, below `T`, the honest
table's marks or `0`, at the honest counts, where each of the child's claims is marked at a slot
of its region whose table cells are the honest table's, the decoded statement is the child's.

The honest coverage table repeats no mark (`B1.Main.honestCov_nodup`), so the mark `g^e` of a
child's writer is found at one slot only, the honest one (`B1.Main.honest_child_slots`), whose
region's table holds the claim (`take4_flatMap`: a table's four cells at `4·s` are its `s`-th
claim's); `B1.Main.kidStmt_eq` assembles them.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1.Main (cellAt honestWordsC hbase planX planS planD kidStmt xCellsOf sCellsOf
  daCellsOf entryX entryS DaAt)

@[expose] public section

/-- **A table's four cells at `4·s` are its `s`-th entry's**, every entry four cells. -/
theorem take4_flatMap {α : Type} (f : α → List E) (hf : ∀ a, (f a).length = 4) :
    ∀ (l : List α) {i : ℕ} (hi : i < l.length), ((l.flatMap f).drop (4 * i)).take 4 = f l[i]
  | [], _, hi => absurd hi (Nat.not_lt_zero _)
  | a :: l, 0, _ => by
    rw [List.flatMap_cons, Nat.mul_zero, List.drop_zero, List.take_append_of_le_length (by rw [hf]),
      List.take_of_length_le (by rw [hf])]
    rfl
  | a :: l, i + 1, hi => by
    rw [List.flatMap_cons, show 4 * (i + 1) = (f a).length + 4 * i by rw [hf]; ring,
      ← List.drop_drop, List.drop_left, take4_flatMap f hf l (by simpa using hi)]
    rfl

theorem xCellsOf_eq (c : XmssClaim) : xCellsOf c =
    [B1.claimCells c.1.root c.1.parameter c.2 0, B1.claimCells c.1.root c.1.parameter c.2 1,
      B1.claimCells c.1.root c.1.parameter c.2 2, B1.claimCells c.1.root c.1.parameter c.2 3] := rfl

theorem sCellsOf_eq (c : SphincsClaim) : sCellsOf c =
    [B1.claimCells c.1.root c.1.parameter c.2 0, B1.claimCells c.1.root c.1.parameter c.2 1,
      B1.claimCells c.1.root c.1.parameter c.2 2, B1.claimCells c.1.root c.1.parameter c.2 3] := rfl

/-- The entry a leanXMSS claim's cells make is the claim. -/
theorem entryX_of_cells {rd : Reader} {T : E} {s : ℕ} {c : XmssClaim}
    (h : B1.ReadsAt rd (T * gen ^ (4 * s)) (xCellsOf c)) : entryX rd T s = c := by
  rw [xCellsOf_eq] at h
  rw [B1.Main.entryX_of_reads h, B1.Sig.xmssOf_claim]

/-- The entry a leanSPHINCS claim's cells make is the claim. -/
theorem entryS_of_cells {rd : Reader} {T : E} {s : ℕ} {c : SphincsClaim}
    (h : B1.ReadsAt rd (T * gen ^ (4 * s)) (sCellsOf c)) : entryS rd T s = c := by
  rw [sCellsOf_eq] at h
  rw [B1.Main.entryS_of_reads h, B1.Sig.sphincsOf_claim]

/-- Two positions of a list without repeats holding one value are one. -/
theorem nodup_getElem?_inj {α : Type} {l : List α} (hl : l.Nodup) {i j : ℕ} {x : α}
    (hi : l[i]? = some x) (hj : l[j]? = some x) : i = j := by
  obtain ⟨hi', rfl⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hj', e⟩ := List.getElem?_eq_some_iff.mp hj
  exact (hl.getElem_inj_iff (hi := hi') (hj := hj')).mp e.symm

theorem gen_pow_ne_zero' (e : ℕ) : gen ^ e ≠ (0 : E) := pow_ne_zero _ B1.VerifySub.vt_gen_ne_zero

/-- **The decoder reads an honest child's statement.** On a memory whose coverage table holds,
below `T`, the honest table's marks or `0`, the counts giving child `c` the honest writers'
numbers, each of the child's claims marked (with its writer's number in the honest table) at a
slot of its region whose table cells there are the honest table's, and its deferred cells at the
carried claims' slot: `kidStmt` is the child's statement. -/
theorem kidStmt_honest {Ha : List UInt8 → Option Digest} (Ht : List UInt8 → Digest) (seed : Digest)
    {s : NodeStatement} {w : NodeWitness}
    (hrel : NodeRelWith Ha B1.Main.aggSeedD B1.Main.daPadCell B1.Main.daPadRow End.bytecode seed s w)
    (hlim : End.Limits s w) {c : ℕ} (hc : c < w.children.length)
    {rd : Reader} {F : B1.Main.Frame} {T : ℕ} {cnt : ℕ → ℕ}
    (hLx : F.Lx = s.claims.xmss.length + (planX s w).2.length)
    (hLs : F.Ls = s.claims.sphincs.length + (planS s w).2.length)
    (hMd : F.Md = s.claims.da.length + (planD s w).2.length)
    (hT : T = s.claims.xmss.length + (planX s w).2.length +
      (s.claims.sphincs.length + (planS s w).2.length) + (s.claims.da.length + (planD s w).2.length))
    (hdaC : F.daC = F.cover * gen ^ (s.claims.xmss.length + (planX s w).2.length +
      (s.claims.sphincs.length + (planS s w).2.length)))
    (hb0 : cnt c = hbase s w c) (hb1 : cnt (c + 1) = hbase s w (c + 1))
    (hcov : ∀ s' < T, cellAt rd F.cover s' = 0 ∨
      (honestWordsC Ht seed s w).cov[s']? = some (cellAt rd F.cover s'))
    (hX : ∀ j < w.children[c].statement.claims.xmss.length,
      ∃ s' < s.claims.xmss.length + (planX s w).2.length,
        (honestWordsC Ht seed s w).cov[s']? = some (gen ^ (hbase s w c + j)) ∧
        LoadHolds rd F.cover s' (gen ^ (hbase s w c + j)) ∧
        B1.ReadsAt rd (F.lxT * gen ^ (4 * s')) (((honestWordsC Ht seed s w).xTab.drop (4 * s')).take 4))
    (hS : ∀ j < w.children[c].statement.claims.sphincs.length,
      ∃ s' < s.claims.sphincs.length + (planS s w).2.length,
        (honestWordsC Ht seed s w).cov[s.claims.xmss.length + (planX s w).2.length + s']? =
          some (gen ^ (hbase s w c + (w.children[c].statement.claims.xmss.length + j))) ∧
        LoadHolds rd F.cover (s.claims.xmss.length + (planX s w).2.length + s')
          (gen ^ (hbase s w c + (w.children[c].statement.claims.xmss.length + j))) ∧
        B1.ReadsAt rd (F.spT * gen ^ (4 * s')) (((honestWordsC Ht seed s w).sTab.drop (4 * s')).take 4))
    (hD : ∀ j < w.children[c].statement.claims.da.length,
      ∃ i < s.claims.da.length + (planD s w).2.length,
        (honestWordsC Ht seed s w).cov[s.claims.xmss.length + (planX s w).2.length +
          (s.claims.sphincs.length + (planS s w).2.length) + i]? =
          some (gen ^ (hbase s w c + (w.children[c].statement.claims.xmss.length +
            w.children[c].statement.claims.sphincs.length + j))) ∧
        LoadHolds rd F.daC i (gen ^ (hbase s w c + (w.children[c].statement.claims.xmss.length +
          w.children[c].statement.claims.sphincs.length + j))) ∧
        B1.ReadsAt rd (F.daR * gen ^ (4 * i)) (((honestWordsC Ht seed s w).daTab.drop (4 * i)).take 4))
    (hdef : B1.ReadsAt rd (F.carried * gen ^ (53 * c)) w.children[c].statement.defer.cells) :
    kidStmt rd F T cnt c = w.children[c].statement := by
  set W := honestWordsC Ht seed s w with hW
  set st := w.children[c].statement with hst
  set b := hbase s w c with hb
  have hnd : W.cov.Nodup := by rw [hW, B1.Main.honestWordsC_cov]; exact B1.Main.honestCov_nodup hlim
  obtain ⟨hbs, slX, slS, slD⟩ := B1.Main.honest_child_slots (s := s) (w := w) Ht seed hc
  -- the child's deferred claim is shaped
  have hshp := (B1.Main.deferredShaped_iff End.bytecode_length _).mp
    (hrel.2.1 _ (List.getElem_mem hc)).1
  -- a mark found below `T` is the honest table's
  have hmark : ∀ s' < T, ∀ e, cellAt rd F.cover s' = gen ^ e → W.cov[s']? = some (gen ^ e) := by
    intro s' hs' e he
    rcases hcov s' hs' with h0 | h1
    · exact absurd (he.symm.trans h0) (gen_pow_ne_zero' e)
    · rw [h1, he]
  refine B1.Main.kidStmt_eq (F := F) (T := T) (cnt := cnt) (b := b) (st := st)
    (by rw [hdaC, hLx, hLs]) (by rw [hLx, hLs, hMd, hT]) hb0 (by rw [hb1, hbs]) ?_ ?_ ?_ ?_
    hshp.1 hshp.2 hdef
  · -- the slots of the child's marks
    intro j hj s' hs' hl
    refine B1.Main.slotOf_eq hs' (B1.Main.cellAt_of_load hl) fun s'' hs'' he => ?_
    exact nodup_getElem?_inj hnd (hmark s'' hs'' _ he) (hmark s' hs' _ (B1.Main.cellAt_of_load hl))
  · -- leanXMSS
    intro j hj
    obtain ⟨s', hs', hcv, hl, hrd⟩ := hX j hj
    obtain ⟨sl, hsl, hcv', he⟩ := slX j hj
    obtain rfl : sl = s' := nodup_getElem?_inj hnd hcv' hcv
    have hlen : sl < (s.claims.xmss ++ (planX s w).2).length := (List.getElem?_eq_some_iff.mp he).1
    rw [hW, show (honestWordsC Ht seed s w).xTab = (s.claims.xmss ++ (planX s w).2).flatMap xCellsOf
      from rfl, take4_flatMap xCellsOf (fun _ => rfl) _ hlen] at hrd
    refine ⟨sl, by rw [hLx]; exact hs', by rw [← pow_add]; exact hl, ?_⟩
    rw [entryX_of_cells hrd, ← List.getElem?_eq_getElem hlen, he, List.getElem?_eq_getElem hj]
  · -- leanSPHINCS
    intro j hj
    obtain ⟨s', hs', hcv, hl, hrd⟩ := hS j hj
    obtain ⟨sl, hsl, hcv', he⟩ := slS j hj
    obtain rfl : sl = s' := by
      have := nodup_getElem?_inj hnd hcv' hcv
      omega
    have hlen : sl < (s.claims.sphincs ++ (planS s w).2).length :=
      (List.getElem?_eq_some_iff.mp he).1
    rw [hW, show (honestWordsC Ht seed s w).sTab =
      (s.claims.sphincs ++ (planS s w).2).flatMap sCellsOf from rfl,
      take4_flatMap sCellsOf (fun _ => rfl) _ hlen] at hrd
    refine ⟨sl, by rw [hLs]; exact hs', by rw [hLx, ← pow_add]; exact hl, ?_⟩
    rw [entryS_of_cells hrd, ← List.getElem?_eq_getElem hlen, he, List.getElem?_eq_getElem hj]
  · -- DA
    intro j hj
    obtain ⟨i, hi, hcv, hl, hrd⟩ := hD j hj
    obtain ⟨il, hil, hcv', he⟩ := slD j hj
    obtain rfl : il = i := by
      have := nodup_getElem?_inj hnd hcv' hcv
      omega
    have hlen : il < (s.claims.da ++ (planD s w).2).length := (List.getElem?_eq_some_iff.mp he).1
    rw [hW, show (honestWordsC Ht seed s w).daTab =
      (s.claims.da ++ (planD s w).2).flatMap daCellsOf from rfl,
      take4_flatMap daCellsOf (fun _ => rfl) _ hlen] at hrd
    refine ⟨il, by rw [hMd]; exact hi, by rw [← pow_add]; exact hl, fun cl hcl => ?_⟩
    have e1 : (s.claims.da ++ (planD s w).2)[il] = cl := by
      rw [← Option.some_inj, ← List.getElem?_eq_getElem hlen, he, ← hcl, List.getElem?_eq_getElem hj]
    rw [← e1]
    exact hrd

end
end LeanVM.E2E.Complete
