/-
  LeanVM.Guest.B1.Sig.Model.SphincsFold

  `sp_fold` and its arms under a hash model (`SphincsFold` over `M.sem`): a forest tree's leaf
  folded up its hinted path, every node an answered hash.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsFold
public import LeanVM.Guest.B1.Sig.Model.XmssScheme

/-!
# Forest folds under a hash model

`spLevel_model`, `spLevels_model` (`spLevels_sound_w`), `spArm_model` (`spArm_sound_w`),
`spMatch_model` (`spMatch_sound_w`): the node a fold reaches is `mFoldWith M.H` of its leaf along
the siblings its frame hints (`lvSibs`, `armSibs`).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {M : HashModel} {C : CallRel} {rd : Reader}

/-- **A level under a model** (`spLevel_sound`): the node is the answered hash of the pair in the
order of the bit. -/
theorem spLevel_model {σ : Val} {pp md adr cur o0 o1 : V} {addr b : Nat} {bit : Bool}
    (hmd : σ md = mdw 64 true) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsListB M.sem C rd σ (spLevel pp md adr addr bit cur b o0 o1) next kret) :
    hcellWith M.H [σ pp, σ adr + word addr 0 0, if bit then σ (.n b) else σ cur,
      if bit then σ cur else σ (.n b)] = some (σ o0, σ o1) ∧ next := by
  simp only [spLevel, hintW, cst, ivs, addS, List.cons_append, List.nil_append, holdsListB_cons_atom,
    Atom.HoldsB, true_and] at h
  obtain ⟨h1, h2, h3, h4, h⟩ := h
  cases bit <;> simp only [b2s, Bool.false_eq_true, ↓reduceIte, holdsListB_cons_atom, holdsListB_nil,
    Atom.HoldsB] at h ⊢ <;> obtain ⟨hc, hn⟩ := h <;> rw [h2, h1, h3, h4, hmd] at hc <;>
    exact ⟨(compress4_model hc).2, hn⟩

/-- **Levels of a fold under a model**, along the siblings they hint (`spLevels_sound_w`). -/
theorem spLevels_model {σ : Val} {pp md adr : V} (F : Fold) (index : Nat) (hmd : σ md = mdw 64 true) :
    ∀ (m l : Nat) (cur : V) (b : Nat) {next : Prop} {kret : List E → Prop},
      Stmt.HoldsListB M.sem C rd σ (spLevels pp md adr F index m l cur b).1 next kret →
      mFoldWith M.H (σ pp) (foldAddr σ adr F index) (fun l => index.testBit l) (lvSibs σ m l b) m l (σ cur) =
        some (σ (spLevels pp md adr F index m l cur b).2) ∧ next
  | 0, _, _, _, _, _, h => ⟨rfl, h⟩
  | m + 1, l, cur, b, next, kret, h => by
      simp only [spLevels, holdsListB_append] at h ⊢
      obtain ⟨hl, h⟩ := spLevel_model hmd h
      obtain ⟨hs, hn⟩ := spLevels_model F index hmd m (l + 1) _ _ h
      refine ⟨?_, hn⟩
      rw [mFoldWith]
      have e : [σ pp, foldAddr σ adr F index l, if index.testBit l then lvSibs σ (m + 1) l b l else σ cur,
          if index.testBit l then σ cur else lvSibs σ (m + 1) l b l] =
          [σ pp, σ adr + word (F.addr index l) 0 0, if index.testBit l then σ (.n b) else σ cur,
            if index.testBit l then σ cur else σ (.n b)] := by
        simp [foldAddr, lvSibs]
      rw [e, hl, Option.bind_some, ← hs]
      exact mFoldWith_congr _ _ _ _ m (l + 1) (fun l' h1 _ => by simp [lvSibs, show l' ≠ l by omega]) _

theorem mFoldWith_last (H : List UInt8 → Option Protocol.Digest) (pp : E) (A : Nat → E) (bits : Nat → Bool)
    (sibs : Nat → E) (m : Nat) (x s : E) :
    mFoldWith H pp A bits (fun l => if l = m then s else sibs l) (m + 1) 0 x =
      (mFoldWith H pp A bits sibs m 0 x).bind fun y =>
        (hcellWith H [pp, A m, if bits m then s else y, if bits m then y else s]).map Prod.fst := by
  rw [mFoldWith_succ, Nat.zero_add, mFoldWith_congr _ _ _ _ m 0 (sibs := fun l => if l = m then s else sibs l)
    (sibs' := sibs) (fun l' _ h2 => by simp [show l' ≠ m by omega])]
  simp

/-- **An arm of a fold under a model**, along the siblings it hints (`spArm_sound_w`). -/
theorem spArm_model {σ : Val} {pp md adr node ret1 ret2 : V} {F : Fold} {out : Nat → V} {r1 r2 : E}
    {index b : Nat} (hmd : σ md = mdw 64 true) (hF : 2 ≤ F.height) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsListB M.sem C rd σ (spArm pp md adr node F out ret1 ret2 r1 r2 index b) next kret) :
    mFoldWith M.H (σ pp) (foldAddr σ adr F index) (fun l => index.testBit l) (armSibs σ F b) (F.height - 1) 0
        (σ node) = some (σ (out (2 * (index / 2 ^ (F.height - 1))))) ∧
      σ ret1 = r1 ∧ σ ret2 = r2 ∧ next := by
  simp only [spArm, holdsListB_append] at h
  obtain ⟨hs, h⟩ := spLevels_model F index hmd _ 0 node b h
  obtain ⟨hl, h⟩ := spLevel_model hmd h
  simp only [hintW, holdsListB_cons_atom, holdsListB_nil, Atom.HoldsB, true_and] at h
  obtain ⟨h1, h2, hn⟩ := h
  refine ⟨?_, h1, h2, hn⟩
  rw [show F.height - 1 = F.height - 2 + 1 by omega, show armSibs σ F b = fun l => if l = F.height - 2 then
      σ (.n (b + 7 * (F.height - 2))) else lvSibs σ (F.height - 2) 0 b l from rfl, mFoldWith_last, hs,
    Option.bind_some]
  have e : [σ pp, foldAddr σ adr F index (F.height - 2),
      if index.testBit (F.height - 2) then σ (.n (b + 7 * (F.height - 2)))
        else σ (spLevels pp md adr F index (F.height - 2) 0 node b).2,
      if index.testBit (F.height - 2) then σ (spLevels pp md adr F index (F.height - 2) 0 node b).2
        else σ (.n (b + 7 * (F.height - 2)))] =
      [σ pp, σ adr + word (F.addr index (F.height - 2)) 0 0,
        if index.testBit (F.height - 2) then σ (.n (b + 7 * (F.height - 2)))
          else σ (spLevels pp md adr F index (F.height - 2) 0 node b).2,
        if index.testBit (F.height - 2) then σ (spLevels pp md adr F index (F.height - 2) 0 node b).2
          else σ (.n (b + 7 * (F.height - 2)))] := rfl
  rw [e, hl, Option.map_some]
  rw [show F.height - 2 + 1 = F.height - 1 by omega]

/-- **A fold's dispatch under a model**, at the arm `selIdx` names (`spMatch_sound_w`). -/
theorem spMatch_model {σ : Val} {pp md adr node ret1 ret2 x : V} {F : Fold} {out : Nat → V} {r1 r2 : Nat → E}
    {m b : Nat} (hmd : σ md = mdw 64 true) (hF : 2 ≤ F.height) (hm : m < 2 ^ 64 - 1) {ss : List Stmt}
    {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsListB M.sem C rd σ (.match_ x (spArms pp md adr node F out ret1 ret2 r1 r2 m 0 b).1 :: ss)
      next kret) :
    ∃ a < m, selIdx (σ x) 0 m = a ∧ σ x = ofK (gpow a) ∧
      mFoldWith M.H (σ pp) (foldAddr σ adr F a) (fun l => a.testBit l) (armSibs σ F (spArmsBase F 0 b a))
        (F.height - 1) 0 (σ node) = some (σ (out (2 * (a / 2 ^ (F.height - 1))))) ∧
      σ ret1 = r1 a ∧ σ ret2 = r2 a ∧ Stmt.HoldsListB M.sem C rd σ ss next kret := by
  obtain ⟨j, hj, hx, ha⟩ := (holdsB_match_iff x _ _ _).mp h
  rw [spArms_length] at hj
  have hget := spArms_get_w pp md adr node F out ret1 ret2 r1 r2 m 0 b j hj
  rw [List.getElem?_eq_getElem (by rw [spArms_length]; exact hj), Option.some.injEq, Nat.zero_add] at hget
  rw [hget] at ha
  obtain ⟨hs, h1, h2, hn⟩ := spArm_model hmd hF ha
  exact ⟨j, hj, selIdx_of hx (by omega) m 0 (by omega) (by omega), hx, hs, h1, h2, hn⟩

end
end LeanVM.Guest.B1.Sig
