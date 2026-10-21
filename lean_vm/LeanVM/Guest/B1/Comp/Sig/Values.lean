/-
  LeanVM.Guest.B1.Comp.Sig.Values

  The signature verifiers' honest values over a completeness model: the model's answers as total
  cells, the chains, tips and Merkle folds they compute, which strings they hash, and their
  bridges to the answered (`Option`) values of the soundness side.
-/

module

public import LeanVM.Guest.B1.Comp.Sig.Hashing
public import LeanVM.Guest.B1.Sig.Model.XmssScheme

/-!
# Honest values over a completeness model

The deployed completeness proofs of the signature verifiers preset the cells of every hash to
`hb`, BLAKE2s of their bytes (`hcell`, `chainFrom`, `tipPair`, `mFold`). Over a completeness model
the honest value of a hash is the model's answer, which exists only for the strings the model
answers. The values here are total, the answer where there is one (`hbC`, `hcellC`, `chainFromC`,
`tipPairC`, `mFoldC`), with the predicates that the model answers every string they hash
(`Ans`, `AnsCells`, `chainAns`, `tipAns`, `mFoldAns`). At the deployed model every string is
answered and the values are the deployed ones (`hbC_deployed`, `chainFromC_deployed`, …); against
the soundness side's answered values (`hcellWith`, `chainFromWith`, `tipPairWith`, `mFoldWith`),
an answered value is `some` of the total one exactly when its strings are answered
(`hcellWith_eq_some_iff`, `chainFromWith_eq_some_iff`, …).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.E2E.Complete

@[expose] public section

variable (CM : CompModel)

/-! ## Answers -/

/-- The model answers the bytes. -/
def Ans (bs : List UInt8) : Prop := ∃ d, CM.H bs = some d

/-- The model answers the bytes of the cells. -/
def AnsCells (cs : List E) : Prop := Ans CM (cs.flatMap cellBytes)

/-- The cells of the model's answer for the bytes (of BLAKE2s where it does not answer). -/
def hbC (bs : List UInt8) : E × E := digestScalars ((CM.H bs).getD (blake2sBytes bs))

/-- The cells of the model's answer for the bytes of cells. -/
def hcellC (cs : List E) : E × E := hbC CM (cs.flatMap cellBytes)

variable {CM}

theorem hbWith_of_ans {bs : List UInt8} (h : Ans CM bs) : hbWith CM.H bs = some (hbC CM bs) := by
  obtain ⟨d, hd⟩ := h
  rw [hbC, hd]
  exact hbWith_of hd rfl

theorem hcellWith_of_ans {cs : List E} (h : AnsCells CM cs) :
    hcellWith CM.H cs = some (hcellC CM cs) :=
  hbWith_of_ans h

theorem hbWith_eq_some_iff {bs : List UInt8} {o : E × E} :
    hbWith CM.H bs = some o ↔ Ans CM bs ∧ hbC CM bs = o := by
  constructor
  · intro h
    obtain ⟨d, hd, rfl⟩ := hbWith_some.mp h
    exact ⟨⟨d, hd⟩, by rw [hbC, hd]; rfl⟩
  · rintro ⟨ha, rfl⟩
    exact hbWith_of_ans ha

theorem hcellWith_eq_some_iff {cs : List E} {o : E × E} :
    hcellWith CM.H cs = some o ↔ AnsCells CM cs ∧ hcellC CM cs = o :=
  hbWith_eq_some_iff

theorem isCanonical128_hbC (bs : List UInt8) : IsCanonical128 (hbC CM bs).1 ∧ IsCanonical128 (hbC CM bs).2 :=
  isCanonical128_digestScalars _

theorem isCanonical128_hcellC (cs : List E) :
    IsCanonical128 (hcellC CM cs).1 ∧ IsCanonical128 (hcellC CM cs).2 :=
  isCanonical128_hbC _

theorem ans_deployed (bs : List UInt8) : Ans CompModel.deployed bs := ⟨_, rfl⟩

theorem ansCells_deployed (cs : List E) : AnsCells CompModel.deployed cs := ans_deployed _

theorem hbC_deployed (bs : List UInt8) : hbC CompModel.deployed bs = hb bs := rfl

theorem hcellC_deployed (cs : List E) : hcellC CompModel.deployed cs = hcell cs := rfl

/-! ## Rows -/

/-- One final block of four cells under the IV, its cells answered (`compress4_iff.mpr`). -/
theorem compress4_C {a b c d : E}
    (hc : IsCanonical128 a ∧ IsCanonical128 b ∧ IsCanonical128 c ∧ IsCanonical128 d)
    (h : AnsCells CM [a, b, c, d]) :
    CM.sem.check ![a, b, c, d] iv0 iv1 (hcellC CM [a, b, c, d]).1 (hcellC CM [a, b, c, d]).2
      (mdw 64 true) :=
  compress4_comp CM hc (hcellWith_of_ans h)

/-- One final block of three cells and a zero under the IV, its cells answered
(`compress3_iff.mpr`). -/
theorem compress3_C {a b c : E} (hc : IsCanonical128 a ∧ IsCanonical128 b ∧ IsCanonical128 c)
    (h : AnsCells CM [a, b, c]) :
    CM.sem.check ![a, b, c, 0] iv0 iv1 (hcellC CM [a, b, c]).1 (hcellC CM [a, b, c]).2
      (mdw 48 true) :=
  compress3_comp CM hc (hcellWith_of_ans h)

/-- A non-final block under the IV, then a final one, all the bytes answered
(`compress_two_iff.mpr`). -/
theorem compress_two_C {b0 b1 : Fin 4 → E} {r : List UInt8}
    (hr : blockBytes b1 = r ++ List.replicate (64 - r.length) 0) (hlen : r.length ≤ 64)
    (hpos : 1 ≤ r.length) (hc0 : ∀ i, IsCanonical128 (b0 i)) (hc1 : ∀ i, IsCanonical128 (b1 i))
    (h : Ans CM (blockBytes b0 ++ r)) :
    CM.sem.check b0 iv0 iv1 (hmidC CM b0).1 (hmidC CM b0).2 (mdw 64 false) ∧
      CM.sem.check b1 (hmidC CM b0).1 (hmidC CM b0).2 (hbC CM (blockBytes b0 ++ r)).1
        (hbC CM (blockBytes b0 ++ r)).2 (mdw (64 + r.length) true) :=
  compress_two_comp CM hr hlen hpos hc0 hc1 (hbWith_of_ans h)

/-! ## Chains -/

variable (CM)

/-- `m + 1` steps of chain `i` from position `s`, over the model (`chainFrom`). -/
def chainFromC (lx : Bool) (pp : E) (adr : Nat → E) (idx : E) (i : Nat) : Nat → Nat → E → E × E
  | 0, s, v => hcellC CM (stepCells lx pp adr idx i s v)
  | m + 1, s, v => chainFromC lx pp adr idx i m (s + 1) (hcellC CM (stepCells lx pp adr idx i s v)).1

/-- The model answers every step of `chainFromC`. -/
def chainAns (lx : Bool) (pp : E) (adr : Nat → E) (idx : E) (i : Nat) : Nat → Nat → E → Prop
  | 0, s, v => AnsCells CM (stepCells lx pp adr idx i s v)
  | m + 1, s, v => AnsCells CM (stepCells lx pp adr idx i s v) ∧
      chainAns lx pp adr idx i m (s + 1) (hcellC CM (stepCells lx pp adr idx i s v)).1

/-- The end of chain `i` revealed at digit `d` with the value `x`, over the model (`tipPair`). -/
def tipPairC (lx : Bool) (pp : E) (adr : Nat → E) (idx : E) (i d : Nat) (x : E) : E × E :=
  if d = 3 then (x, 0) else chainFromC CM lx pp adr idx i (2 - d) d x

/-- The model answers the steps of `tipPairC`. -/
def tipAns (lx : Bool) (pp : E) (adr : Nat → E) (idx : E) (i d : Nat) (x : E) : Prop :=
  d ≠ 3 → chainAns CM lx pp adr idx i (2 - d) d x

variable {CM}

theorem chainFromC_succ (lx : Bool) (pp : E) (adr : Nat → E) (idx : E) (i m s : Nat) (v : E) :
    chainFromC CM lx pp adr idx i (m + 1) s v =
      chainFromC CM lx pp adr idx i m (s + 1) (hcellC CM (stepCells lx pp adr idx i s v)).1 := rfl

theorem canonical_chainFromC (lx : Bool) (pp : E) (adr : Nat → E) (idx : E) (i : Nat) :
    ∀ m s v, IsCanonical128 (chainFromC CM lx pp adr idx i m s v).1 ∧
      IsCanonical128 (chainFromC CM lx pp adr idx i m s v).2
  | 0, _, _ => isCanonical128_hcellC _
  | m + 1, s, _ => canonical_chainFromC lx pp adr idx i m (s + 1) _

theorem canonical_tipPairC (lx : Bool) (pp : E) (adr : Nat → E) (idx : E) (i d : Nat) {x : E}
    (hx : IsCanonical128 x) : IsCanonical128 (tipPairC CM lx pp adr idx i d x).1 := by
  unfold tipPairC
  split
  · exact hx
  · exact (canonical_chainFromC lx pp adr idx i _ _ _).1

theorem chainFromWith_eq_some_iff (lx : Bool) (pp : E) (adr : Nat → E) (idx : E) (i : Nat) :
    ∀ (m s : Nat) (v : E) {p : E × E}, chainFromWith CM.H lx pp adr idx i m s v = some p ↔
      chainAns CM lx pp adr idx i m s v ∧ chainFromC CM lx pp adr idx i m s v = p
  | 0, s, v, p => hcellWith_eq_some_iff
  | m + 1, s, v, p => by
      simp only [chainFromWith, chainAns, chainFromC, Option.bind_eq_some_iff]
      constructor
      · rintro ⟨h, hh, hp⟩
        obtain ⟨ha, rfl⟩ := hcellWith_eq_some_iff.mp hh
        obtain ⟨ha', hp'⟩ := (chainFromWith_eq_some_iff lx pp adr idx i m (s + 1) _).mp hp
        exact ⟨⟨ha, ha'⟩, hp'⟩
      · rintro ⟨⟨ha, ha'⟩, hp⟩
        exact ⟨_, hcellWith_of_ans ha, (chainFromWith_eq_some_iff lx pp adr idx i m (s + 1) _).mpr ⟨ha', hp⟩⟩

theorem tipPairWith_eq_some_iff (lx : Bool) (pp : E) (adr : Nat → E) (idx : E) (i d : Nat) (x : E)
    {p : E × E} : tipPairWith CM.H lx pp adr idx i d x = some p ↔
      tipAns CM lx pp adr idx i d x ∧ tipPairC CM lx pp adr idx i d x = p := by
  unfold tipPairWith tipAns tipPairC
  by_cases hd : d = 3
  · simp only [hd, ↓reduceIte, Option.some.injEq, ne_eq, not_true_eq_false, IsEmpty.forall_iff,
      true_and]
  · simp only [hd, ↓reduceIte, ne_eq, not_false_eq_true, forall_const]
    exact chainFromWith_eq_some_iff lx pp adr idx i _ _ _

theorem chainFromC_deployed (lx : Bool) (pp : E) (adr : Nat → E) (idx : E) (i : Nat) :
    ∀ m s v, chainFromC CompModel.deployed lx pp adr idx i m s v = chainFrom lx pp adr idx i m s v
  | 0, _, _ => rfl
  | m + 1, s, _ => chainFromC_deployed lx pp adr idx i m (s + 1) _

theorem chainAns_deployed (lx : Bool) (pp : E) (adr : Nat → E) (idx : E) (i : Nat) :
    ∀ m s v, chainAns CompModel.deployed lx pp adr idx i m s v
  | 0, _, _ => ansCells_deployed _
  | m + 1, s, _ => ⟨ansCells_deployed _, chainAns_deployed lx pp adr idx i m (s + 1) _⟩

theorem tipPairC_deployed (lx : Bool) (pp : E) (adr : Nat → E) (idx : E) (i d : Nat) (x : E) :
    tipPairC CompModel.deployed lx pp adr idx i d x = tipPair lx pp adr idx i d x := by
  unfold tipPairC tipPair
  split
  · rfl
  · exact chainFromC_deployed lx pp adr idx i _ _ _

theorem tipAns_deployed (lx : Bool) (pp : E) (adr : Nat → E) (idx : E) (i d : Nat) (x : E) :
    tipAns CompModel.deployed lx pp adr idx i d x := fun _ => chainAns_deployed lx pp adr idx i _ _ _

/-! ## A chain's tips in a valuation -/

variable (CM)

/-- The tips `t` hold chain `i`'s end at digit `d` from the value `x`, over the model (`TipSet`). -/
def TipSetC (w : Wots) (σ : Val) (i d : Nat) (x : E) (t : V × V) : Prop :=
  σ t.1 = (tipPairC CM w.lx (w.pp' σ) (w.adr' σ) (w.idx' σ) i d x).1 ∧
    (d ≠ 3 → σ t.2 = (tipPairC CM w.lx (w.pp' σ) (w.adr' σ) (w.idx' σ) i d x).2)

/-- The model answers the steps of chain `i` at digit `d` from the value `x`, the chain's inputs
those of the valuation. -/
def TipAnsC (w : Wots) (σ : Val) (i d : Nat) (x : E) : Prop :=
  tipAns CM w.lx (w.pp' σ) (w.adr' σ) (w.idx' σ) i d x

variable {CM}

theorem TipSetC.congr {w : Wots} {σ σ' : Val} {i d : Nat} {x : E} {t : V × V}
    (h : TipSetC CM w σ i d x t)
    (hk : w.pp' σ' = w.pp' σ ∧ w.adr' σ' = w.adr' σ ∧ w.idx' σ' = w.idx' σ ∧ σ' w.md = σ w.md)
    (h1 : σ' t.1 = σ t.1) (h2 : σ' t.2 = σ t.2) : TipSetC CM w σ' i d x t := by
  rw [TipSetC, hk.1, hk.2.1, hk.2.2.1, h1, h2]; exact h

theorem TipAnsC.congr {w : Wots} {σ σ' : Val} {i d : Nat} {x : E} (h : TipAnsC CM w σ i d x)
    (hk : w.pp' σ' = w.pp' σ ∧ w.adr' σ' = w.adr' σ ∧ w.idx' σ' = w.idx' σ ∧ σ' w.md = σ w.md) :
    TipAnsC CM w σ' i d x := by
  rw [TipAnsC, hk.1, hk.2.1, hk.2.2.1]; exact h

theorem tipSetC_deployed {w : Wots} {σ : Val} {i d : Nat} {x : E} {t : V × V} :
    TipSetC CompModel.deployed w σ i d x t ↔ TipSet w σ i d x t := by
  rw [TipSetC, TipSet, tipPairC_deployed]

/-- The model's tips, as the soundness side's answered ones (`TipSetWith`). -/
theorem tipSetWith_of_C {w : Wots} {σ : Val} {i d : Nat} {x : E} {t : V × V}
    (ha : TipAnsC CM w σ i d x) (h : TipSetC CM w σ i d x t) : TipSetWith CM.H w σ i d x t :=
  ⟨_, (tipPairWith_eq_some_iff _ _ _ _ _ _ _).mpr ⟨ha, rfl⟩, h.1, h.2⟩

/-! ## Merkle paths -/

variable (CM)

/-- `m` levels of a path from `x` at level `l`, over the model (`mFold`). -/
def mFoldC (pp : E) (A : Nat → E) (bits : Nat → Bool) (sibs : Nat → E) : Nat → Nat → E → E
  | 0, _, x => x
  | m + 1, l, x => mFoldC pp A bits sibs m (l + 1)
      (hcellC CM [pp, A l, if bits l then sibs l else x, if bits l then x else sibs l]).1

/-- The model answers every node of `mFoldC`. -/
def mFoldAns (pp : E) (A : Nat → E) (bits : Nat → Bool) (sibs : Nat → E) : Nat → Nat → E → Prop
  | 0, _, _ => True
  | m + 1, l, x => AnsCells CM [pp, A l, if bits l then sibs l else x, if bits l then x else sibs l] ∧
      mFoldAns pp A bits sibs m (l + 1)
        (hcellC CM [pp, A l, if bits l then sibs l else x, if bits l then x else sibs l]).1

variable {CM}

theorem mFoldWith_eq_some_iff (pp : E) (A : Nat → E) (bits : Nat → Bool) (sibs : Nat → E) :
    ∀ (m l : Nat) (x : E) {r : E}, mFoldWith CM.H pp A bits sibs m l x = some r ↔
      mFoldAns CM pp A bits sibs m l x ∧ mFoldC CM pp A bits sibs m l x = r
  | 0, l, x, r => by simp [mFoldWith, mFoldAns, mFoldC]
  | m + 1, l, x, r => by
      simp only [mFoldWith, mFoldAns, mFoldC, Option.bind_eq_some_iff]
      constructor
      · rintro ⟨h, hh, hp⟩
        obtain ⟨ha, rfl⟩ := hcellWith_eq_some_iff.mp hh
        obtain ⟨ha', hp'⟩ := (mFoldWith_eq_some_iff pp A bits sibs m (l + 1) _).mp hp
        exact ⟨⟨ha, ha'⟩, hp'⟩
      · rintro ⟨⟨ha, ha'⟩, hp⟩
        exact ⟨_, hcellWith_of_ans ha, (mFoldWith_eq_some_iff pp A bits sibs m (l + 1) _).mpr ⟨ha', hp⟩⟩

theorem mFoldC_deployed (pp : E) (A : Nat → E) (bits : Nat → Bool) (sibs : Nat → E) :
    ∀ m l x, mFoldC CompModel.deployed pp A bits sibs m l x = mFold pp A bits sibs m l x
  | 0, _, _ => rfl
  | m + 1, l, _ => mFoldC_deployed pp A bits sibs m (l + 1) _

theorem mFoldAns_deployed (pp : E) (A : Nat → E) (bits : Nat → Bool) (sibs : Nat → E) :
    ∀ m l x, mFoldAns CompModel.deployed pp A bits sibs m l x
  | 0, _, _ => trivial
  | m + 1, l, _ => ⟨ansCells_deployed _, mFoldAns_deployed pp A bits sibs m (l + 1) _⟩

theorem mFoldC_congr2 (pp : E) (bits : Nat → Bool) {A A' : Nat → E} {sibs sibs' : Nat → E} :
    ∀ (m l : Nat), (∀ l', l ≤ l' → l' < l + m → A l' = A' l' ∧ sibs l' = sibs' l') → ∀ x,
      mFoldC CM pp A bits sibs m l x = mFoldC CM pp A' bits sibs' m l x ∧
        (mFoldAns CM pp A bits sibs m l x ↔ mFoldAns CM pp A' bits sibs' m l x)
  | 0, _, _, _ => ⟨rfl, Iff.rfl⟩
  | m + 1, l, h, x => by
      simp only [mFoldC, mFoldAns]
      rw [(h l le_rfl (by omega)).1, (h l le_rfl (by omega)).2]
      have := mFoldC_congr2 pp bits m (l + 1) (fun l' h1 h2 => h l' (by omega) (by omega))
      exact ⟨(this _).1, and_congr Iff.rfl (this _).2⟩

theorem mFoldC_canonical (pp : E) (A : Nat → E) (bits : Nat → Bool) (sibs : Nat → E) :
    ∀ (m l : Nat) (x : E), (0 < m ∨ IsCanonical128 x) → IsCanonical128 (mFoldC CM pp A bits sibs m l x)
  | 0, _, _, h => h.resolve_left (by omega)
  | m + 1, l, _, _ => mFoldC_canonical pp A bits sibs m (l + 1) _ (Or.inr (isCanonical128_hcellC _).1)

end
end LeanVM.Guest.B1.Sig
