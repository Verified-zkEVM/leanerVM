/-
  LeanVM.Guest.B1.Main.HonestAllC

  `main`'s honest words over a hash satisfy `MainWordsOkC` (from a witness of `NodeRelWith` within
  the deployed limits), and `main` is complete, placed, under a semantics `S` over the answered
  hash.
-/

module

public import LeanVM.Guest.B1.Main.HonestChildC
public import LeanVM.Guest.B1.Main.HonestAll

/-!
# `main` is complete over an answered hash

`HonestAll.lean` under `S : BlakeSem` over the answered hash `Ha`, the honest words over a total
hash `Ht` agreeing with `Ha` where it answers (`hag`): `honestC_wordsOk`, from a witness of
`NodeRelWith Ha` from the guest's baked start and padding, its statement's digest answered;
`mainC_completeW`: `main_completeW` at `honestWordsC Ht`, the callees `CalleesAtC Ha S`, the
weights `MainWeightHypsS S`, the inline rows `FsRowsC S Ha` and the batching sumchecks
`BsRowsC S Ha`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.Hints (direct)
open LeanVM.Guest.End (Limits coverage)
open LeanVM.Guest.B1 (LowDef Within)

@[expose] public section

variable (fs : String → ℕ) (Ht : List UInt8 → Digest) {Ha : List UInt8 → Option Digest} {fp : ℕ}
  {seed : Digest} {s : NodeStatement} {w : NodeWitness}

/-- The children's claims over an answered hash are their statements' digests over `Ht`. -/
theorem childClaimsWith_ans (hag : ∀ x d, Ha x = some d → d = Ht x) {seed : Digest} :
    ∀ (children : List Child) {cs : List ChildClaims}, childClaimsWith Ha seed children = some cs →
      cs = children.map fun c ↦ ⟨statementDigestH Ht seed c.statement, c.fresh, c.statement.defer⟩
  | [], cs, h => by simp only [childClaimsWith, List.mapM_nil] at h; exact (Option.some.inj h).symm
  | c :: cl, cs, h => by
    simp only [childClaimsWith, List.mapM_cons, Option.bind_eq_bind, Option.map_eq_map,
      Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨q, ⟨pi, hpi, rfl⟩, rest, hrest, hcs⟩ := h
    cases hcs
    obtain ⟨-, rfl⟩ := stmtAns_of hag hpi
    rw [childClaimsWith_ans hag cl hrest]
    rfl

theorem honestC_lens {bytecode : List K} (hb : bytecode.length = 2 ^ 22)
    (hsh : s.defer.Shaped bytecode) (hch : ∀ c ∈ w.children, c.statement.defer.Shaped bytecode)
    (hfr : ∀ c ∈ w.children, FreshShaped c.fresh) :
    (honestWordsC Ht seed s w).bufs.map List.length = (honestWordsC Ht seed s w).sizes := by
  simp only [MainWords.bufs, MainWords.sizes, List.map_cons, List.map_nil, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, defer_cells_length hb hsh⟩
  · simp only [honestWordsC]
    rw [length_flatMap_const _ 4 _ fun c _ => daCellsOf_length c, List.length_append]
  · simp only [honestWordsC]
    rw [length_flatMap_const _ 4 _ fun c _ => xCellsOf_length c, List.length_append]
  · simp only [honestWordsC]
    rw [length_flatMap_const _ 4 _ fun c _ => sCellsOf_length c, List.length_append]
  · exact (honC_cov_length (seed := seed) (s := s) (w := w) Ht).trans rfl
  · simp only [honestWordsC]
    rw [length_flatMap_const _ 2 _ fun c _ => rfl]
  · simp only [honestWordsC]
    rw [length_flatMap_const _ 106 _ fun c hc => fixedCells_length (hfr c hc)]
  · simp only [honestWordsC]
    rw [length_flatMap_const _ 53 _ fun c hc => defer_cells_length hb (hch c hc)]
  · simp [honestWordsC]

/-- **`main`'s honest words over a hash are what its callees need** (`honest_wordsOk`). -/
theorem honestC_wordsOk {S : BlakeSem} (hag : ∀ x d, Ha x = some d → d = Ht x) (hF : FsRowsC S Ha)
    {κ : ℕ} {VsGood : VerifySub.VsData → VerifySub.VsRunC → Prop} {bytecode : List K}
    (hb : bytecode.length = 2 ^ 22)
    (hN : NodeRelWith Ha aggSeedD daPadCell daPadRow bytecode seed s w) {pi : Digest}
    (hpi : statementDigestWith Ha seed s = some pi) (hlim : Limits s w)
    (hfr : ∀ c ∈ w.children, FreshShaped c.fresh)
    (hvs : ∀ c ∈ w.children, ∃ (D : VerifySub.VsData) (R : VerifySub.VsRunC), VsGood D R ∧
      D.pi = statementDigestH Ht seed c.statement ∧ D.seed = seed ∧ R.fresh D = c.fresh) :
    MainWordsOkC S fs Ha κ VsGood fp (honestWordsC Ht seed s w) := by
  obtain ⟨hsh, hch, hX, hS, hD, hfin⟩ := hN
  obtain ⟨ha, -⟩ := stmtAns_of hag hpi
  have hans : ∀ c ∈ w.children, StmtAns Ha Ht seed c.statement := fun c hc => by
    obtain ⟨-, pic, hpic, -⟩ := hch c hc
    exact (stmtAns_of hag hpic).1
  have ht : (honestWordsC Ht seed s w).total < 2 ^ 16 := by
    have h0 := honest_total (seed := seed) hlim
    simp only [MainWords.total, honestWords] at h0
    simp only [MainWords.total, honestWordsC]; omega
  have hrxl := honest_rx_le hlim
  have hrsl := honest_rs_le hlim
  have hdau := honest_dau hlim
  have hrdl : hrd s w ≤ 1 := hlim.directDa
  simp only [MainWords.total, honestWordsC] at ht
  refine
    { total := by simp only [MainWords.total, honestWordsC]; omega
      nc := hlim.children
      rd1 := hrdl
      da := hlim.daRoots.1
      ud := by simp only [honestWordsC]; omega
      dau := hdau
      rx := by simp only [honestWordsC]; omega
      rs := by simp only [honestWordsC]; omega
      decl := hlim.nonempty
      lens := honestC_lens Ht hb hsh (fun x hx => (hch x hx).1) hfr
      daList := ⟨_, rfl, fun rd _ hL => honC_daList fs Ht hlim ha.dl hL⟩
      xList := ⟨_, length_flatMap_const _ 4 _ fun c _ => xCellsOf_length c,
        fun rd _ hL => honC_xList fs Ht hlim ha.xl hL⟩
      sList := ⟨_, length_flatMap_const _ 4 _ fun c _ => sCellsOf_length c,
        fun rd _ hL => honC_sList fs Ht hlim ha.sl hL⟩
      sig := honC_sig hF ha.sg
      xSlot := fun c hc => (honC_markX fs Ht (seed := seed) (fp := fp)
        (show c < (writersX s w).length by rw [writersX_len]; simp only [honestWordsC] at hc; omega)).1
      xMark := fun c hc => by
        have := (honC_markX fs Ht (seed := seed) (fp := fp)
          (show c < (writersX s w).length by rw [writersX_len]; simp only [honestWordsC] at hc; omega)).2
        rw [gX_raw hc] at this
        exact this
      xSig := fun c hc rd _ hL => honC_xSig fs Ht hX hL hc
      sSlot := fun c hc => (honC_markS fs Ht (seed := seed) (fp := fp)
        (show c < (writersS s w).length by rw [writersS_len]; simp only [honestWordsC] at hc; omega)).1
      sMark := fun c hc => by
        have := (honC_markS fs Ht (seed := seed) (fp := fp)
          (show c < (writersS s w).length by rw [writersS_len]; simp only [honestWordsC] at hc; omega)).2
        rw [gS_raw hc, pow_add] at this
        exact this
      sSig := fun c hc rd _ hL => honC_sSig fs Ht hS hL hc
      daVerify := fun h1 => by
        obtain ⟨wt, root, vd, ho, hr, h⟩ := honC_daVerify fs Ht (fp := fp) (seed := seed) hD h1
        exact ⟨wt, root, vd, ho, hr, fun rd _ hL => h rd hL⟩
      daCover := fun h1 => ⟨_, fun rd _ hL => honC_daCover fs Ht hlim h1 hL⟩
      written0 := by
        have := honC_written fs Ht (fp := fp) (seed := seed) (s := s) (w := w) 0 (by omega)
        rw [show hbase s w 0 = hrx s w + hrs s w + hrd s w by simp [hbase], pow_add, pow_add] at this
        exact this
      writtenN := by
        have := honC_written fs Ht (fp := fp) (seed := seed) (s := s) (w := w) w.children.length le_rfl
        rw [hbase_children (seed := seed) hlim] at this
        simp only [MainWords.total, honestWordsC, pow_add] at this
        exact this
      children := fun c hc => honC_child fs Ht hF hb hlim (fun x hx => (hch x hx).1) hfr hvs hans hc
      leaf := fun h0 => by
        have he : w.children = [] := List.length_eq_zero_iff.mp h0
        simp only [he, ↓reduceIte] at hfin
        obtain ⟨h1, h2⟩ := hfin
        rw [hb, Nat.log2_two_pow] at h1
        simp [honestWordsC, DeferredClaim.cells, h1, h2, blake2sR1csLogSize]
      agg := fun h0 => by
        have he : w.children ≠ [] := fun h => h0 (by simp [honestWordsC, h])
        simp only [he, ↓reduceIte] at hfin
        obtain ⟨cs, hcs, hfin⟩ := hfin
        rw [childClaimsWith_ans Ht hag w.children hcs] at hfin
        have hfin' := hfin
        obtain ⟨-, hfinH⟩ := aggAns_of (Ht := Ht) hag hfin
        obtain ⟨l1, l2⟩ := batchH_lengths Ht hfinH
        obtain ⟨b1, b2⟩ := hsh
        rw [hb, Nat.log2_two_pow] at b1
        refine ⟨_, w.hints, s.defer, by simp [honestWordsC], hfin', by omega,
          by rw [← l2, b2]; rfl, fun c hc => ?_,
          by simp [honestWordsC, List.flatMap_map], by simp [honestWordsC, List.flatMap_map],
          by simp [honestWordsC, List.flatMap_map], rfl⟩
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
        obtain ⟨c1, c2⟩ := (hch x hx).1
        rw [hb, Nat.log2_two_pow] at c1
        exact ⟨hfr x hx, c1, by rw [c2]; rfl⟩
      stmt := ⟨_, _, fun rd _ hL => honC_stmt fs Ht hb hsh ha.st hL⟩ }

/-- **`main` is complete, placed, under `S` over the answered hash `Ha`** (`main_completeW`): for a
witness of `NodeRelWith Ha` within the deployed limits, its statement's digest `pi` answered, every
child's proof run by a run in `VsGood` and of the guest's fresh shape, `main`'s callees complete
under `S` over `Ha` within `Bd`, at every `fp` one size, within `mainBound`, and one layout serve
every memory holding them, defined below `2^κ`, with `pi` at words `0` and `1`: `main` holds under
`S` by a tree placed at `fp`, within `mainWeightS` at the honest words over `Ht`. -/
theorem mainC_completeW {S : BlakeSem} {cert : String → V → ℕ} {κ : ℕ}
    {VsGood : VerifySub.VsData → VerifySub.VsRunC → Prop} {Bd : CalleeBounds} (H : CalleesAtC Ha S fs cert κ VsGood Bd)
    (hF : FsRowsC S Ha) (hBs : BsRowsC S Ha) (hag : ∀ x d, Ha x = some d → d = Ht x)
    {Θ : Type} {ωs : Θ → String → ℕ} (Wt : ∀ θ, MainWeightHypsS S fs (ωs θ)) (hκ : 16 ≤ κ)
    {bytecode : List K} (hb : bytecode.length = 2 ^ 22)
    (hN : NodeRelWith Ha aggSeedD daPadCell daPadRow bytecode seed s w) {pi : Digest}
    (hpi : statementDigestWith Ha seed s = some pi) (hlim : Limits s w)
    (hfr : ∀ c ∈ w.children, FreshShaped c.fresh)
    (hvs : ∀ c ∈ w.children, ∃ (D : VerifySub.VsData) (R : VerifySub.VsRunC), VsGood D R ∧
      D.pi = statementDigestH Ht seed c.statement ∧ D.seed = seed ∧ R.fresh D = c.fresh) (fp : ℕ) :
    ∃ (m : ℕ) (L : Layout), Within L (fp + fs "main") m ∧ LeanVM.Guest.B1.DisjL L ∧
      fs "main" + m ≤ mainBound fs Bd (honestWordsC Ht seed s w) ∧
      ∀ rd, LowDef κ rd → MemL rd L →
        rd 1 = some (digestScalars pi).1 → rd g = some (digestScalars pi).2 →
        RelAtInWS S fs cert ωs rd (fun i => i < 2) (fun _ => False) fp (fs "main" + m)
          "main" [] [] fun θ => mainWeightS S (ωs θ) Bd (Wt θ) (honestWordsC Ht seed s w) := by
  obtain ⟨-, rfl⟩ := stmtAns_of hag hpi
  obtain ⟨m, _, hW, hD, hB, h⟩ := mainS_relAtInW Wt H hF hBs hκ
    (honestC_wordsOk fs Ht (fp := fp) hag hF hb hN hpi hlim hfr hvs)
  exact ⟨m, _, hW, hD, by unfold mainBound; omega, h⟩

end
end LeanVM.Guest.B1.Main
