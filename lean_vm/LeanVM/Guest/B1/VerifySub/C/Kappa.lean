/-
  LeanVM.Guest.B1.VerifySub.C.Kappa

  `verify_sub`'s `block_kappa` (G:3194-3198), honestly.
-/

module

public import LeanVM.Guest.B1.VerifySub.C.Sizes
public import LeanVM.Guest.B1.VerifySub.Mid

/-!
# `block_kappa`, honestly

`vsKappaT_complete`: with `kappa_base` holding `1, g, ds…` and `block_kappa` its honest words
`blockKappaWords g ds` (the stores), every step reads its source and stores its block's word
(`g^19` times it for the bytecode blocks), and `vsKappaT` holds.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Tables LeanVM.Protocol.Verifier

@[expose] public section

/-- A read of a word the memory holds, on an evaluated valuation. -/
theorem good_read {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {d p : V} {off : ℕ} {v : E}
    (hg : Good rd S w σ (.load d p off)) (hS : Atom.load d p off ∉ S)
    (hm : LoadHolds rd (σ p) off v) : σ d = v ∧ (Atom.load d p off).Holds rd σ := by
  simp only [Good] at hg
  have e : σ d = v := by rw [hg.resolve_left hS, rdAt, hm.2]; rfl
  exact ⟨e, by show LoadHolds rd _ _ _; rw [e]; exact hm⟩

theorem vsKappaT_noNe : vsKappaT.all noNeB = true := by decide +kernel

theorem vsKappa_notS : ∀ b < Tables.nBlocks,
    Atom.load (.n (vsKV b)) (.n 141) (Tables.blockKappaSrc.getD b 0) ∉ vsSL := by decide +kernel

variable {rd : Reader} {w : ℕ → E} {args : List E}

theorem vsKappaT_good (hl : args.length = 7) :
    ∀ s ∈ vsKappaT, GoodS rd vsSL w (vsσ rd w args) s := by
  intro s hs
  have h := vs_goodS (rd := rd) (w := w) hl (vs_mem_slice (n := 121) (blk := vsKappaT)
    (by decide +kernel) hs)
  rwa [fixNe_of_noNe (List.all_eq_true.mp vsKappaT_noNe s hs)] at h

theorem vsKappaStep_mem {b : ℕ} (hb : b < Tables.nBlocks) {s : Stmt} (hs : s ∈ vsKappaStep b) :
    s ∈ vsKappaT := List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨b, List.mem_range.2 hb, hs⟩)

/-- One block, honestly. -/
theorem vsKappaStep_complete (hl : args.length = 7) {g : E} {ds : List E} (hds : ds.length = 6)
    (hkb : ReadsAt rd (vsσ rd w args (.n 141)) (1 :: g :: ds))
    (hbk : ReadsAt rd (vsσ rd w args (.n 149)) (Tables.blockKappaWords g ds))
    {b : ℕ} (hb : b < Tables.nBlocks) {C : CallRel} {next : Prop} {kret : List E → Prop}
    (hn : next) : Stmt.HoldsList C rd (vsσ rd w args) (vsKappaStep b) next kret := by
  have hG := vsKappaT_good (rd := rd) (w := w) hl
  have hsrc := blockKappaSrc_lt b hb
  have hsrcL : LoadHolds rd (vsσ rd w args (.n 141)) (Tables.blockKappaSrc.getD b 0)
      ((1 :: g :: ds).getD (Tables.blockKappaSrc.getD b 0) 0) := by
    rw [List.getD_eq_getElem (1 :: g :: ds) _ (by simp only [List.length_cons, hds]; omega)]
    exact hkb _ _
  have hbkL : LoadHolds rd (vsσ rd w args (.n 149)) b ((Tables.blockKappaWords g ds).getD b 0) := by
    rw [List.getD_eq_getElem _ _ (by simp [Tables.blockKappaWords]; exact hb)]
    exact hbk _ _
  have hbw : (Tables.blockKappaWords g ds).getD b 0 =
      (1 :: g :: ds).getD (Tables.blockKappaSrc.getD b 0) 0 * gen ^ Tables.blockKappaAdj b := by
    rw [Tables.blockKappaWords, List.getD_eq_getElem _ _ (by simpa using hb), List.getElem_map,
      List.getElem_range]
  have hr0 : Good rd vsSL w (vsσ rd w args)
      (.load (.n (vsKV b)) (.n 141) (Tables.blockKappaSrc.getD b 0)) :=
    hG _ (vsKappaStep_mem hb (s := vsLd (vsKV b) 141 _) (by unfold vsKappaStep; split <;> simp))
  have hr := good_read hr0 (vsKappa_notS b hb) hsrcL
  unfold vsKappaStep
  split
  · rename_i h0
    simp only [Stmt.HoldsList, Stmt.Holds, vsLd]
    refine ⟨hr.2, ?_, hn⟩
    show LoadHolds rd _ _ _
    have e : (Tables.blockKappaWords g ds).getD b 0 =
        (1 :: g :: ds).getD (Tables.blockKappaSrc.getD b 0) 0 := by
      rw [hbw, h0, pow_zero, mul_one]
    rw [hr.1, ← e]
    exact hbkL
  · rename_i h0
    have hadj : Tables.blockKappaAdj b = 19 := by
      unfold Tables.blockKappaAdj at h0 ⊢; split <;> simp_all
    have hc := hG _ (vsKappaStep_mem hb (s := vsConst (vsKV b + 1) (word (2 ^ 19) 0 0))
      (by unfold vsKappaStep; simp [h0]))
    have hm := hG _ (vsKappaStep_mem hb (s := vsMul (vsKV b + 2) (vsKV b) (vsKV b + 1))
      (by unfold vsKappaStep; simp [h0]))
    simp only [vsConst, vsMul, GoodS, Good] at hc hm
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by simp))] at hm
    simp only [Stmt.HoldsList, Stmt.Holds, vsLd, vsConst, vsMul]
    refine ⟨hr.2, hc, hm, ?_, hn⟩
    show LoadHolds rd _ _ _
    rw [hm, hr.1, hc, word_two_pow (by norm_num), ← hadj, ← hbw]
    exact hbkL

/-- **`block_kappa`, honestly.** -/
theorem vsKappaT_complete (hl : args.length = 7) {g : E} {ds : List E} (hds : ds.length = 6)
    (hkb : ReadsAt rd (vsσ rd w args (.n 141)) (1 :: g :: ds))
    (hbk : ReadsAt rd (vsσ rd w args (.n 149)) (Tables.blockKappaWords g ds))
    {C : CallRel} {next : Prop} {kret : List E → Prop} (hn : next) :
    Stmt.HoldsList C rd (vsσ rd w args) vsKappaT next kret := by
  unfold vsKappaT
  simp only [Stmt.HoldsList, Stmt.Holds, vsAlloc]
  refine ⟨trivial, ?_⟩
  have key : ∀ (l : List ℕ), (∀ b ∈ l, b < Tables.nBlocks) → ∀ {nx : Prop}, nx →
      Stmt.HoldsList C rd (vsσ rd w args) (l.flatMap vsKappaStep) nx kret := by
    intro l
    induction l with
    | nil => intro _ nx h; exact h
    | cons b l ih =>
      intro hl' nx h
      rw [List.flatMap_cons, holdsList_append]
      exact vsKappaStep_complete hl hds hkb hbk (hl' b List.mem_cons_self)
        (ih (fun x hx ↦ hl' x (List.mem_cons_of_mem _ hx)) h)
  exact key _ (fun b hb ↦ List.mem_range.1 hb) hn

end
end LeanVM.Guest.B1.VerifySub
