/-
  LeanVM.Guest.B1.Main.MainCompleteT

  `main` complete at the honest words over a hash, its tree keeping each child's `verify_sub`
  tree at the run chosen for it (`HonestAllC.lean`'s `mainC_completeW` with tree predicates).
-/

module

public import LeanVM.Guest.B1.Main.HonestAllC
public import LeanVM.Guest.B1.Main.MainAtCT

/-!
# `main` at the honest words, its tree kept

* `honC_vsSub`: child `c`'s `verify_sub` call reads the exponent tables and its fixed claims'
  cells of `main`'s words at a run record whose fixed claims are the child's;
* `honC_vr`: per-child runs `vr` give `mainS_relAtInWT`'s `hvr` at the honest words;
* `mainC_completeWT`: `mainC_completeW` with `verify_sub`'s trees satisfying `VsQ`, `main`'s tree
  satisfying `MainQ` at the runs `vr`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.Hints (direct)
open LeanVM.Guest.End (Limits coverage)
open LeanVM.Guest.B1 (LowDef RelAtInWST CompleteAtWST)

@[expose] public section

variable (fs : String → ℕ) (Ht : List UInt8 → Digest) {Ha : List UInt8 → Option Digest} {fp : ℕ}
  {seed : Digest} {s : NodeStatement} {w : NodeWitness}

/-- **Child `c`'s `verify_sub` reads `main`'s honest words**: the exponent tables and, at
`child_fresh·g^(106c)`, the fixed claims of a run record whose fixed claims are the child's. -/
theorem honC_vsSub (hlim : Limits s w) (hfr : ∀ c ∈ w.children, FreshShaped c.fresh) {c : ℕ}
    (hc : c < w.children.length) {D : VerifySub.VsData} {R : VerifySub.VsRunC}
    (hfresh : R.fresh D = w.children[c].fresh) :
    SubL (vsExtLR (mainExpBase fs fp (honestWordsC Ht seed s w))
      (mainExpBase fs fp (honestWordsC Ht seed s w) + 34)
      (mainBase fs fp (honestWordsC Ht seed s w) 6 + 106 * c) D R)
      (mainIn fs fp (honestWordsC Ht seed s w)) := by
  have hmem := List.getElem_mem hc
  have hnc := hlim.children
  have hfl : (fixedCells w.children[c].fresh).length = 106 := fixedCells_length (hfr _ hmem)
  have hfrl : (w.children.flatMap fun c => fixedCells c.fresh).length = 106 * w.children.length :=
    length_flatMap_const _ 106 _ fun x hx => fixedCells_length (hfr x hx)
  refine SubL.append (SubL.of_mem fun q hq => List.mem_append_right _ ?_) ?_
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

/-- **Per-child runs at the honest words** (`mainS_relAtInWT`'s `hvr`). -/
theorem honC_vr (hlim : Limits s w) (hfr : ∀ c ∈ w.children, FreshShaped c.fresh)
    {VsGood : VerifySub.VsData → VerifySub.VsRunC → Prop} (vr : ℕ → VerifySub.VsData × VerifySub.VsRunC)
    (hvr : ∀ c (hc : c < w.children.length), VsGood (vr c).1 (vr c).2 ∧
      (vr c).1.pi = statementDigestH Ht seed w.children[c].statement ∧ (vr c).1.seed = seed ∧
      (vr c).2.fresh (vr c).1 = w.children[c].fresh) :
    ∀ c < (honestWordsC Ht seed s w).nc, ∃ lpA sqA outA : ℕ, VsGood (vr c).1 (vr c).2 ∧
      (vr c).1.pi = ((honestWordsC Ht seed s w).child c).pd ∧
      (vr c).1.seed = (honestWordsC Ht seed s w).seed ∧
      ofK (gpow (mainExpBase fs fp (honestWordsC Ht seed s w))) = ofK (gpow lpA) ∧
      ofK (gpow (mainExpBase fs fp (honestWordsC Ht seed s w) + 34)) = ofK (gpow sqA) ∧
      mainPtr fs fp (honestWordsC Ht seed s w) 6 * gen ^ (106 * c) = ofK (gpow outA) ∧
      SubL (vsExtLR lpA sqA outA (vr c).1 (vr c).2) (mainIn fs fp (honestWordsC Ht seed s w)) := by
  intro c hc
  have hc' : c < w.children.length := hc
  obtain ⟨hg, hpi, hseed, hfresh⟩ := hvr c hc'
  refine ⟨mainExpBase fs fp (honestWordsC Ht seed s w), mainExpBase fs fp (honestWordsC Ht seed s w) + 34,
    mainBase fs fp (honestWordsC Ht seed s w) 6 + 106 * c, hg, ?_, hseed, rfl, rfl,
    ofK_gpow_mul_gen _ _, honC_vsSub fs Ht hlim hfr hc' hfresh⟩
  rw [honC_child_eq (Ht := Ht) hc', hpi]
  rfl

/-- **`main` is complete, placed, its tree kept** (`mainC_completeW`): `verify_sub` complete by
trees satisfying `VsQ` at every good run, child `c` run by `vr c`: `main`'s tree satisfies
`MainQ` at `vr`. -/
theorem mainC_completeWT {S : BlakeSem} {cert : String → V → ℕ} {κ : ℕ}
    {VsGood : VerifySub.VsData → VerifySub.VsRunC → Prop} {Bd : CalleeBounds}
    (H : CalleesAtC Ha S fs cert κ VsGood Bd)
    (hF : FsRowsC S Ha) (hBs : BsRowsC S Ha) (hag : ∀ x d, Ha x = some d → d = Ht x)
    {Θ : Type} {ωs : Θ → String → ℕ} (Wt : ∀ θ, MainWeightHypsS S fs (ωs θ)) (hκ : 16 ≤ κ)
    {bytecode : List K} (hb : bytecode.length = 2 ^ 22)
    (hN : NodeRelWith Ha aggSeedD daPadCell daPadRow bytecode seed s w) {pi : Digest}
    (hpi : statementDigestWith Ha seed s = some pi) (hlim : Limits s w)
    (hfr : ∀ c ∈ w.children, FreshShaped c.fresh)
    (VsQ : VerifySub.VsData → VerifySub.VsRunC → ℕ → Reader → Memory.Tree → Prop)
    (HV : ∀ D R, VsGood D R → ∀ lpA sqA outA : ℕ, ∀ (c : Θ → VerifySub.VsStat),
      (∀ θ, VerifySub.VsStatOkS S (ωs θ) (c θ)) →
      CompleteAtWST S fs cert ωs κ "verify_sub" (vsExtLR lpA sqA outA D R)
        [(digestScalars D.pi).1, (digestScalars D.pi).2, (digestScalars D.seed).1,
          (digestScalars D.seed).2, ofK (gpow lpA), ofK (gpow sqA), ofK (gpow outA)] (Returns []) Bd.vs
        (fun θ => Bd.vsW (ωs θ) (c θ)) (VsQ D R))
    (vr : ℕ → VerifySub.VsData × VerifySub.VsRunC)
    (hvr : ∀ c (hc : c < w.children.length), VsGood (vr c).1 (vr c).2 ∧
      (vr c).1.pi = statementDigestH Ht seed w.children[c].statement ∧ (vr c).1.seed = seed ∧
      (vr c).2.fresh (vr c).1 = w.children[c].fresh) (fp : ℕ) :
    ∃ (m : ℕ) (L : Layout), Within L (fp + fs "main") m ∧ LeanVM.Guest.B1.DisjL L ∧
      fs "main" + m ≤ mainBound fs Bd (honestWordsC Ht seed s w) ∧
      ∀ rd, LowDef κ rd → MemL rd L →
        rd 1 = some (digestScalars pi).1 → rd g = some (digestScalars pi).2 →
        RelAtInWST S fs cert ωs rd (fun i => i < 2) (fun _ => False) fp (fs "main" + m)
          "main" [] [] (fun θ => mainWeightS S (ωs θ) Bd (Wt θ) (honestWordsC Ht seed s w))
          (MainQ VsQ vr fs w.children.length fp
            (mainVal rd (mainRunAt fs fp (honestWordsC Ht seed s w))) rd) := by
  obtain ⟨-, rfl⟩ := stmtAns_of hag hpi
  have hvs : ∀ c ∈ w.children, ∃ (D : VerifySub.VsData) (R : VerifySub.VsRunC), VsGood D R ∧
      D.pi = statementDigestH Ht seed c.statement ∧ D.seed = seed ∧ R.fresh D = c.fresh := by
    intro c hc
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    exact ⟨(vr i).1, (vr i).2, hvr i hi⟩
  obtain ⟨m, _, hW, hD, hB, h⟩ := mainS_relAtInWT Wt H hF hBs hκ
    (honestC_wordsOk fs Ht (fp := fp) hag hF hb hN hpi hlim hfr hvs) VsQ
    (fun D R hD lpA sqA outA c hc => HV D R hD lpA sqA outA c hc) vr
    (honC_vr fs Ht (fp := fp) hlim hfr vr hvr)
  exact ⟨m, _, hW, hD, by unfold mainBound; omega, h⟩

end
end LeanVM.Guest.B1.Main
