/-
  LeanVM.Guest.B1.Main.HonestChildC

  A child's iteration on `main`'s honest words over a hash (`HonestChild.lean` over `Ht`, the
  digests answered by `Ha`): its claim lists, its DA roots, its deferred cells, its public input
  and its proof's run (`ChildWordsOkC`).
-/

module

public import LeanVM.Guest.B1.Main.HonestMainC
public import LeanVM.Guest.B1.Main.HonestChild

/-!
# A child, honestly, over a hash

`HonestChild.lean`'s lemmas at `honestWordsC Ht` (`honC_ccx`, `honC_ccs`, `honC_childCov`,
`honC_child`): the child's list digests, signer set's, DA list's and statement's digests over `Ht`
answered by `Ha` (`StmtAns`), its proof's run in `VsGood` at its digest over `Ht`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.Hints (direct)
open LeanVM.Guest.End (Limits coverage)
open LeanVM.Guest.B1 (LowDef)
open LeanVM.Guest.B1.Digest (SquaresAt CellsAt SdPreAtC DaListPreAtC ClPreAtC CclPreAtC)

@[expose] public section

variable (fs : String → ℕ) (Ht : List UInt8 → Digest) {Ha : List UInt8 → Option Digest} {fp : ℕ} {seed : Digest}
  {s : NodeStatement} {w : NodeWitness} {rd : Reader}

theorem honC_child_eq {c : ℕ} (hc : c < w.children.length) :
    (honestWordsC Ht seed s w).child c = childWordsOfC Ht seed w.children[c] (hbase s w c) := by
  simp [honestWordsC, hc]


/-! ## The claim lists -/

theorem honC_ccx (hlim : Limits s w) {c : ℕ} (hc : c < w.children.length)
    (hx : xmssListDigestWith Ha w.children[c].statement.claims.xmss =
      some (xmssListDigestH Ht w.children[c].statement.claims.xmss))
    (hL : MemL rd (mainIn fs fp (honestWordsC Ht seed s w))) :
    CclPreAtC Ha (fun j => (planX s w).1.getD (hrx s w + ((w.children.take c).map cnx).sum + j) 0)
      (w.children[c].statement.claims.xmss.flatMap xCellsOf) rd
      [mainPtr fs fp (honestWordsC Ht seed s w) 1, mainPtr fs fp (honestWordsC Ht seed s w) 4,
        gen ^ hbase s w c, 1, gen ^ s.claims.xmss.length * gen ^ (planX s w).2.length,
        gen ^ cnx w.children[c], ofK (gpow (mainExpBase fs fp (honestWordsC Ht seed s w) + 34))]
      [(digestScalars (xmssListDigestH Ht w.children[c].statement.claims.xmss)).1,
        (digestScalars (xmssListDigestH Ht w.children[c].statement.claims.xmss)).2] := by
  have ht : (honestWordsC Ht seed s w).total < 2 ^ 16 := by
    have h0 := honest_total (seed := seed) hlim
    simp only [MainWords.total, honestWords] at h0
    simp only [MainWords.total, honestWordsC]; omega
  simp only [MainWords.total, honestWordsC] at ht
  have hl := (hlim.lists _ (List.getElem_mem hc)).1
  have hlen := writersX_length hlim
  rw [writersX_len] at hlen
  have hsum := sum_take_lt cnx w.children hc
  refine ⟨squaresAt_of_mainIn fs hL, ⟨_, by omega, (pow_add _ _ _).symm⟩, cnx w.children[c], hl, rfl,
    length_flatMap_const _ 4 _ fun x _ => xCellsOf_length x, fun j hj => ?_, xCellsOf_canonical _, _, ?_,
    rfl⟩
  · have hr : hrx s w + ((w.children.take c).map cnx).sum + j < (writersX s w).length := by
      rw [writersX_len]; omega
    obtain ⟨hs, hm⟩ := honC_markX fs Ht (seed := seed) (fp := fp) hr
    rw [gX_child hc hj] at hm
    refine ⟨⟨s.claims.xmss.length + (planX s w).2.length, by omega, (pow_add _ _ _).symm, hs⟩, ?_, ?_⟩
    · rw [one_mul, loadHolds_mul_gen_pow, Nat.add_zero, ← pow_add]
      exact hm.load hL
    · have he := honC_xEntry fs Ht hL hr ((writersX_child (s := s) hc hj).trans (List.getElem?_eq_getElem hj))
      have g : ∀ k < 4, (w.children[c].statement.claims.xmss.flatMap xCellsOf).getD (4 * j + k) 0 =
          (xCellsOf (w.children[c].statement.claims.xmss[j]'hj)).getD k 0 := fun k hk =>
        getD_flatMap_four _ xCellsOf_length 0 _ j k hj hk
      have g0 : (w.children[c].statement.claims.xmss.flatMap xCellsOf).getD (4 * j) 0 =
          (xCellsOf (w.children[c].statement.claims.xmss[j]'hj)).getD 0 0 := by simpa using g 0 (by omega)
      rw [g0, g 1 (by omega), g 2 (by omega), g 3 (by omega), ← list4 (xCellsOf_length _)]
      exact he
  · rw [xCellsOf_bytes]; exact hx

theorem honC_ccs (hlim : Limits s w) {c : ℕ} (hc : c < w.children.length)
    (hs : sphincsListDigestWith Ha w.children[c].statement.claims.sphincs =
      some (sphincsListDigestH Ht w.children[c].statement.claims.sphincs))
    (hL : MemL rd (mainIn fs fp (honestWordsC Ht seed s w))) :
    CclPreAtC Ha (fun j => (planS s w).1.getD (hrs s w + ((w.children.take c).map cns).sum + j) 0)
      (w.children[c].statement.claims.sphincs.flatMap sCellsOf) rd
      [mainPtr fs fp (honestWordsC Ht seed s w) 2, mainPtr fs fp (honestWordsC Ht seed s w) 4,
        gen ^ hbase s w c * gen ^ cnx w.children[c],
        gen ^ s.claims.xmss.length * gen ^ (planX s w).2.length,
        gen ^ s.claims.sphincs.length * gen ^ (planS s w).2.length,
        gen ^ cns w.children[c], ofK (gpow (mainExpBase fs fp (honestWordsC Ht seed s w) + 34))]
      [(digestScalars (sphincsListDigestH Ht w.children[c].statement.claims.sphincs)).1,
        (digestScalars (sphincsListDigestH Ht w.children[c].statement.claims.sphincs)).2] := by
  have ht : (honestWordsC Ht seed s w).total < 2 ^ 16 := by
    have h0 := honest_total (seed := seed) hlim
    simp only [MainWords.total, honestWords] at h0
    simp only [MainWords.total, honestWordsC]; omega
  simp only [MainWords.total, honestWordsC] at ht
  have hl := (hlim.lists _ (List.getElem_mem hc)).2
  have hlen := writersS_length hlim
  rw [writersS_len] at hlen
  have hsum := sum_take_lt cns w.children hc
  refine ⟨squaresAt_of_mainIn fs hL, ⟨_, by omega, (pow_add _ _ _).symm⟩, cns w.children[c], hl, rfl,
    length_flatMap_const _ 4 _ fun x _ => sCellsOf_length x, fun j hj => ?_, sCellsOf_canonical _, _, ?_,
    rfl⟩
  · have hr : hrs s w + ((w.children.take c).map cns).sum + j < (writersS s w).length := by
      rw [writersS_len]; omega
    obtain ⟨hs, hm⟩ := honC_markS fs Ht (seed := seed) (fp := fp) hr
    rw [gS_child hc hj] at hm
    refine ⟨⟨s.claims.sphincs.length + (planS s w).2.length, by omega, (pow_add _ _ _).symm, hs⟩, ?_, ?_⟩
    · rw [← pow_add, ← pow_add, loadHolds_mul_gen_pow, Nat.add_zero, ← pow_add, ← pow_add]
      exact hm.load hL
    · have he := honC_sEntry fs Ht hL hr ((writersS_child (s := s) hc hj).trans (List.getElem?_eq_getElem hj))
      have g : ∀ k < 4, (w.children[c].statement.claims.sphincs.flatMap sCellsOf).getD (4 * j + k) 0 =
          (sCellsOf (w.children[c].statement.claims.sphincs[j]'hj)).getD k 0 := fun k hk =>
        getD_flatMap_four _ sCellsOf_length 0 _ j k hj hk
      have g0 : (w.children[c].statement.claims.sphincs.flatMap sCellsOf).getD (4 * j) 0 =
          (sCellsOf (w.children[c].statement.claims.sphincs[j]'hj)).getD 0 0 := by simpa using g 0 (by omega)
      rw [g0, g 1 (by omega), g 2 (by omega), g 3 (by omega), ← list4 (sCellsOf_length _)]
      exact he
  · rw [sCellsOf_bytes]; exact hs

/-! ## The DA roots -/

theorem honC_childCov (hlim : Limits s w) {c : ℕ} (hc : c < w.children.length)
    (hL : MemL rd (mainIn fs fp (honestWordsC Ht seed s w))) {k : ℕ}
    (hk : k < w.children[c].statement.claims.da.length) :
    CoverPreAt ((planD s w).1.getD (hrd s w + ((w.children.take c).map cnda).sum + k) 0) rd
      [mainPtr fs fp (honestWordsC Ht seed s w) 0,
      mainPtr fs fp (honestWordsC Ht seed s w) 4 * (gen ^ s.claims.xmss.length * gen ^ (planX s w).2.length *
        (gen ^ s.claims.sphincs.length * gen ^ (planS s w).2.length)),
      gen ^ s.claims.da.length * gen ^ (planD s w).2.length,
      gen ^ hbase s w c * (gen ^ cnx w.children[c] * gen ^ cns w.children[c]) * gen ^ k]
      (daCellsOf (w.children[c].statement.claims.da[k]'hk)) := by
  have hsum := sum_take_lt cnda w.children hc
  have hr : hrd s w + ((w.children.take c).map cnda).sum + k < (writersD s w).length := by
    have : cnda w.children[c] = w.children[c].statement.claims.da.length := rfl
    rw [writersD_len]; omega
  obtain ⟨hs, hm⟩ := honC_markD fs Ht (seed := seed) (fp := fp) hr
  rw [gD_child hc hk] at hm
  have hdau := honest_dau hlim
  have he := honC_dEntry fs Ht hL hr ((writersD_child (s := s) hc hk).trans (List.getElem?_eq_getElem hk))
  refine ⟨s.claims.da.length + (planD s w).2.length, by omega, hs, (pow_add _ _ _).symm, ?_, he⟩
  have hv : gen ^ (hbase s w c + (cnx w.children[c] + cns w.children[c]) + k) =
      gen ^ hbase s w c * (gen ^ cnx w.children[c] * gen ^ cns w.children[c]) * gen ^ k := by ring
  rw [hv] at hm
  exact loadHolds_cover (hm.load hL)

/-! ## The whole iteration -/



theorem honC_child {S : BlakeSem} (hF : FsRowsC S Ha) {κ : ℕ} {VsGood : VerifySub.VsData → VerifySub.VsRunC → Prop}
    {bytecode : List K} (hb : bytecode.length = 2 ^ 22) (hlim : Limits s w)
    (hshp : ∀ c ∈ w.children, c.statement.defer.Shaped bytecode)
    (hfr : ∀ c ∈ w.children, FreshShaped c.fresh)
    (hvs : ∀ c ∈ w.children, ∃ (D : VerifySub.VsData) (R : VerifySub.VsRunC), VsGood D R ∧ D.pi = statementDigestH Ht seed c.statement ∧
      D.seed = seed ∧ R.fresh D = c.fresh)
    (hans : ∀ c ∈ w.children, StmtAns Ha Ht seed c.statement)
    {c : ℕ} (hc : c < w.children.length) :
    ChildWordsOkC S Ha κ VsGood (mainIn fs fp (honestWordsC Ht seed s w))
      (mainBase fs fp (honestWordsC Ht seed s w) 8) (mainBase fs fp (honestWordsC Ht seed s w) 5)
      (mainPtr fs fp (honestWordsC Ht seed s w) 1) (mainPtr fs fp (honestWordsC Ht seed s w) 4)
      (gen ^ (honestWordsC Ht seed s w).dx * gen ^ (honestWordsC Ht seed s w).ux)
      (ofK (gpow (mainExpBase fs fp (honestWordsC Ht seed s w) + 34))) (mainPtr fs fp (honestWordsC Ht seed s w) 2)
      (gen ^ (honestWordsC Ht seed s w).ds * gen ^ (honestWordsC Ht seed s w).us)
      (mainPtr fs fp (honestWordsC Ht seed s w) 7) (mainPtr fs fp (honestWordsC Ht seed s w) 0)
      (mainPtr fs fp (honestWordsC Ht seed s w) 4 * (gen ^ (honestWordsC Ht seed s w).dx *
        gen ^ (honestWordsC Ht seed s w).ux * (gen ^ (honestWordsC Ht seed s w).ds * gen ^ (honestWordsC Ht seed s w).us)))
      (gen ^ (honestWordsC Ht seed s w).da * gen ^ (honestWordsC Ht seed s w).ud)
      (digestScalars (honestWordsC Ht seed s w).seed).1 (digestScalars (honestWordsC Ht seed s w).seed).2
      (ofK (gpow (mainExpBase fs fp (honestWordsC Ht seed s w)))) (mainPtr fs fp (honestWordsC Ht seed s w) 6)
      (honestWordsC Ht seed s w).seed c ((honestWordsC Ht seed s w).child c) := by
  rw [honC_child_eq (Ht := Ht) hc]
  have hmem := List.getElem_mem hc
  obtain ⟨D, R, hg, hpi, hseed, hfresh⟩ := hvs _ hmem
  have ha := hans _ hmem
  have hnc := hlim.children
  have hfl : (fixedCells w.children[c].fresh).length = 106 := fixedCells_length (hfr _ hmem)
  have hfrl : (w.children.flatMap fun c => fixedCells c.fresh).length = 106 * w.children.length :=
    length_flatMap_const _ 106 _ fun x hx => fixedCells_length (hfr x hx)
  refine
    { base := honC_written fs Ht (seed := seed) (s := s) (w := w) c (by omega)
      next := ?_
      nx := (hlim.lists _ hmem).1
      ns := (hlim.lists _ hmem).2
      nda := hlim.daRoots.2 _ hmem
      ccx := ⟨_, _, length_flatMap_const _ 4 _ fun c _ => xCellsOf_length c, fun rd _ hL => honC_ccx fs Ht hlim hc ha.xl hL⟩
      ccs := ⟨_, _, length_flatMap_const _ 4 _ fun c _ => sCellsOf_length c, fun rd _ hL => honC_ccs fs Ht hlim hc ha.sl hL⟩
      sig := honC_sig hF ha.sg
      cov := ⟨_, fun k hk rd _ hL => honC_childCov fs Ht hlim hc hL hk⟩
      defer := fun rd hL => ?_
      dlen := defer_cells_length hb (hshp _ hmem)
      seed := rfl
      pd := ⟨_, ha.dl, ha.st⟩
      pi0 := ?_
      pi1 := ?_
      vs := ⟨D, R, mainExpBase fs fp (honestWordsC Ht seed s w), mainExpBase fs fp (honestWordsC Ht seed s w) + 34,
        mainBase fs fp (honestWordsC Ht seed s w) 6 + 106 * c, hg, hpi, hseed, rfl, rfl,
        ofK_gpow_mul_gen _ _, ?_⟩ }
  · have := honC_written fs Ht (fp := fp) (seed := seed) (s := s) (w := w) (c + 1) (by omega)
    have hv : gen ^ hbase s w (c + 1) = gen ^ hbase s w c *
        (gen ^ cnx w.children[c] * gen ^ cns w.children[c]) * gen ^ cnda w.children[c] := by
      rw [hbase_succ hc, cnw]; ring
    rw [hv] at this
    exact this
  · have h7 : ReadsAt rd (mainPtr fs fp (honestWordsC Ht seed s w) 7)
        (w.children.flatMap fun c => c.statement.defer.cells) := mainIn_reads hL 7 (by omega)
    exact readsAt_flatMap_of (w := 53) w.children
      (fun x hx => defer_cells_length hb (hshp x hx)) h7 c hc
  · refine cellL_of_getD (mainIn_mem 5 (by omega)) (2 * c) ?_ ?_
    · simp only [MainWords.bufs, honestWordsC, List.getD_cons_succ, List.getD_cons_zero]
      rw [length_flatMap_const _ 2 _ fun _ _ => rfl]; omega
    · simp only [MainWords.bufs, honestWordsC, List.getD_cons_succ, List.getD_cons_zero]
      rw [show 2 * c = 2 * c + 0 from rfl, getD_flatMap_const _ 2 (fun _ => rfl) 0 _ c 0 hc (by omega)]
      rfl
  · refine cellL_of_getD (mainIn_mem 5 (by omega)) (2 * c + 1) ?_ ?_
    · simp only [MainWords.bufs, honestWordsC, List.getD_cons_succ, List.getD_cons_zero]
      rw [length_flatMap_const _ 2 _ fun _ _ => rfl]; omega
    · simp only [MainWords.bufs, honestWordsC, List.getD_cons_succ, List.getD_cons_zero]
      rw [getD_flatMap_const _ 2 (fun _ => rfl) 0 _ c 1 hc (by omega)]
      rfl
  · refine SubL.append (SubL.of_mem fun q hq => List.mem_append_right _ ?_) ?_
    · simp only [VerifySub.expL, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ List.mem_cons_self
    · rw [hfresh]
      have hlen : 106 * c + (fixedCells w.children[c].fresh).length ≤
          (w.children.flatMap fun c => fixedCells c.fresh).length := by rw [hfl, hfrl]; nlinarith
      refine SubL.run (ys := w.children.flatMap fun c => fixedCells c.fresh)
        (mainIn_mem 6 (by omega)) hlen fun k hk => ?_
      have hk' : k < 106 := by rw [hfl] at hk; exact hk
      have := getElem?_flatMap_mem (fun c : Child => fixedCells c.fresh) 106 w.children
        (fun x hx => fixedCells_length (hfr x hx)) c k _ (List.getElem?_eq_getElem hc) hk'
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem hk] at this
      exact (Option.some.inj this).symm

end
end LeanVM.Guest.B1.Main
