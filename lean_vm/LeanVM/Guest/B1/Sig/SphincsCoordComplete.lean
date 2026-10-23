/-
  LeanVM.Guest.B1.Sig.SphincsCoordComplete

  A coordinate of `verify_sig_lean_sphincs`'s forest completes: its super-child hinted and range
  checked, its leaf's address, its two sub-trees, the super-child's hash, the top fold's dispatch
  and the bound updated.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsSubComplete

/-!
# A coordinate, complete

* `CoordH`: a coordinate's hints: its super-child `s`, the top fold's siblings (the other level-3
  node last) and its two sub-trees';
* `CoordPost`: what a coordinate's valuation holds; `sCoord_complete`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

attribute [local irreducible] fkArms foldArms sSubtree

variable {C : CallRel} {rd : Reader}

/-- A coordinate's hints. -/
structure CoordH where
  s : Nat
  sibs : Nat → E
  sub0 : SubH
  sub1 : SubH

def CoordH.OK (h : CoordH) : Prop := h.s < 16 ∧ (∀ l, IsCanonical128 (h.sibs l)) ∧ h.sub0.OK ∧ h.sub1.OK

/-- The mark a coordinate's top fold checks, its leaf's address offset. -/
def coordMark (c s : Nat) : E := word (c * hiMul + s * 2 ^ 35) 0 0

/-- The encoding's terms of a coordinate's hints. -/
def hEnc (c : Nat) (h : CoordH) : E := fkWeight h.sub0.t (2 * c) + fkWeight h.sub1.t (2 * c + 1)

/-- The bound's terms of a coordinate's hints. -/
def hBound (c : Nat) (h : CoordH) : E :=
  cbMul h.sub0.a (58 + 3 * (2 * c)) + cbMul h.sub1.a (58 + 3 * (2 * c + 1)) + cbMul h.s (26 + 4 * c)

theorem coordFd_eq (c b f : Nat) : coordFd c b f = foldArms (.n (b + 6)) coordAdr 4 (.n (f + 5)) (.n (b + 1))
    (coordMark c) (fun s => cbMul s (26 + 4 * c)) (f + 18) := rfl

theorem coordAdr_ok (s : Nat) : AdrOK (coordAdr s) (4 - 1) := by
  intro l _ a h
  simp [coordAdr] at h

/-- What a coordinate's valuation holds. -/
def CoordPost (encIn boundIn : E) (c : Nat) (enc : Option V) (bound : V) (b : Nat) (h : CoordH)
    (σ : Val) : Prop :=
  σ (.n b) = ofK (gpow h.s) ∧ σ (.n (b + 1)) = coordMark c h.s ∧
    SubPost encIn boundIn c 0 enc (b + 10) h.sub0 σ ∧
    SubPost (encIn + fkWeight h.sub0.t (2 * c)) (boundIn + cbMul h.sub0.a (58 + 3 * (2 * c))) c 1
      (some (coordS0 c enc bound b).2.2.1) (coordS0 c enc bound b).2.1 h.sub1 σ ∧
    (∀ l < 3, σ (.n (flBase (coordAdr h.s) 0 l (foAB (.n (b + 6)) coordAdr 4
      (.n ((coordS1 c enc bound b).2.1 + 5)) (.n (b + 1)) (coordMark c) (fun s => cbMul s (26 + 4 * c))
      ((coordS1 c enc bound b).2.1 + 18) h.s))) = h.sibs l) ∧
    σ (if h.s / 2 ^ 3 = 0 then (coordFd c b (coordS1 c enc bound b).2.1).2.2.2.1
      else (coordFd c b (coordS1 c enc bound b).2.1).2.2.1) = h.sibs 3 ∧
    IsCanonical128 (σ (coordFd c b (coordS1 c enc bound b).2.1).2.2.1) ∧
    IsCanonical128 (σ (coordFd c b (coordS1 c enc bound b).2.1).2.2.2.1) ∧
    σ (sCoord c enc bound b).2.2.1 = encIn + hEnc c h ∧
    σ (sCoord c enc bound b).2.2.2.1 = boundIn + hBound c h

theorem coordS0_eq (c : Nat) (enc : Option V) (bound : V) (b : Nat) :
    coordS0 c enc bound b = sSubtree c 0 (.n (b + 6)) enc bound (b + 10) := rfl

theorem coordS1_eq (c : Nat) (enc : Option V) (bound : V) (b : Nat) :
    coordS1 c enc bound b = sSubtree c 1 (.n (b + 6)) (some (coordS0 c enc bound b).2.2.1)
      (coordS0 c enc bound b).2.2.2.1 (coordS0 c enc bound b).2.1 := rfl

theorem sCoord_split (c : Nat) (enc : Option V) (bound : V) (b : Nat) :
    (sCoord c enc bound b).1 =
      [hintW "sp_leaves" [.n b, .n (b + 1)]] ++ (rangeS (.n b) g15W (b + 2) ++
        ([addS (.n (b + 6)) (sNode 0) (.n (b + 1)), copyS (.n (b + 7)) sPP, cst (b + 8) (word (tw 18) 0 0),
          addS (.n (b + 9)) (.n (b + 6)) (.n (b + 8))] ++
        ((coordS0 c enc bound b).1 ++ ((coordS1 c enc bound b).1 ++
        ([copyS (.n (coordS1 c enc bound b).2.1) (coordS1 c enc bound b).2.2.2.2.1,
          copyS (.n ((coordS1 c enc bound b).2.1 + 1)) (coordS1 c enc bound b).2.2.2.2.2,
          cst ((coordS1 c enc bound b).2.1 + 2) (word 1 0 0),
          cst ((coordS1 c enc bound b).2.1 + 3) (word 0 0 0),
          cst ((coordS1 c enc bound b).2.1 + 4) (word (2 ^ 63) 0 0)] ++
        ([kecS [.n (b + 7), .n (b + 9), (coordS0 c enc bound b).2.2.2.2.1,
            (coordS0 c enc bound b).2.2.2.2.2, .n (coordS1 c enc bound b).2.1,
            .n ((coordS1 c enc bound b).2.1 + 1), .n ((coordS1 c enc bound b).2.1 + 2),
            .n ((coordS1 c enc bound b).2.1 + 3), .n ((coordS1 c enc bound b).2.1 + 4),
            .n (sPad + 1), .n (sPad + 2), .n (sPad + 3), .n (sPad + 4)]
            (runV ((coordS1 c enc bound b).2.1 + 5) 13) false false] ++
        ([.match_ (.n b) (coordFd c b (coordS1 c enc bound b).2.1).1] ++
          [addS (if c + 1 = 8 then .n 18 else .n (coordFd c b (coordS1 c enc bound b).2.1).2.1)
            (coordS1 c enc bound b).2.2.2.1 (coordFd c b (coordS1 c enc bound b).2.1).2.2.2.2]))))))) := by
  rw [sCoord_eq]
  simp

theorem sCoord_fst (c : Nat) (enc : Option V) (bound : V) (b : Nat) :
    (sCoord c enc bound b).2.1 = if c + 1 = 8 then (coordFd c b (coordS1 c enc bound b).2.1).2.1
      else (coordFd c b (coordS1 c enc bound b).2.1).2.1 + 1 := by rw [sCoord_eq]

/-- **A coordinate completes**, its hints loaded: they are kept, its two level-3 nodes canonical,
the encoding and the bound updated; the last checks the digest's cells. -/
theorem sCoord_complete {c : Nat} {enc : Option V} {bound : V} {b : Nat} (hb : 206 ≤ b)
    (henc : ∀ en, enc = some en → NBv b en) (hbd : NBv b bound) (hm : MemOK rd 256) (h : CoordH)
    (hh : h.OK) (σ : Val) (hX : ForestX σ) (hn0 : IsCanonical128 (σ (sNode 0)))
    (hlast : c + 1 = 8 → (∃ en, enc = some en) ∧ σ (.n 17) = encVal σ enc + hEnc c h ∧
      σ (.n 18) = σ bound + hBound c h) :
    Completes C rd b (sCoord c enc bound b).2.1 (sCoord c enc bound b).1 σ
      (fun σ' => ∀ σ'', AgreeBelow (sCoord c enc bound b).2.1 σ' σ'' →
        CoordPost (encVal σ enc) (σ bound) c enc bound b h σ'') := by
  obtain ⟨hs16, hsib, hh0, hh1⟩ := hh
  -- the shapes
  obtain ⟨s0a, ⟨k0, ek0, hk0⟩, s0b, L0, eL0, hL0a, hL0b⟩ :=
    sSubtree_shape c 0 (.n (b + 6)) enc bound (b := b + 10) (by omega)
  rw [← coordS0_eq] at s0a ek0 hk0 s0b eL0 hL0b
  obtain ⟨s1a, ⟨k1, ek1, hk1⟩, s1b, L1, eL1, hL1a, hL1b⟩ :=
    sSubtree_shape c 1 (.n (b + 6)) (some (coordS0 c enc bound b).2.2.1) (coordS0 c enc bound b).2.2.2.1
      (b := (coordS0 c enc bound b).2.1) (by omega)
  rw [← coordS1_eq] at s1a ek1 hk1 s1b eL1 hL1b
  set f := (coordS1 c enc bound b).2.1 with hf
  have hfo := foAB_mono (atV := .n (b + 6)) (adr := coordAdr) (height := 4) (node0 := .n (f + 5))
    (markV := .n (b + 1)) (markC := coordMark c) (wC := fun s => cbMul s (26 + 4 * c)) (b := f + 18)
  have hfdE : f + 18 ≤ (coordFd c b f).2.1 := by rw [coordFd_eq, foldArms_end]; exact (hfo 16).1
  have hfo3 := foldArms_outs (atV := .n (b + 6)) (adr := coordAdr) (height := 4) (node0 := .n (f + 5))
    (markV := .n (b + 1)) (markC := coordMark c) (wC := fun s => cbMul s (26 + 4 * c)) (f + 18)
  have hLf := flBase_ge (coordAdr 0) 0 (4 - 1) (f + 18)
  have hLfE : flBase (coordAdr 0) 0 (4 - 1) (f + 18) + 3 ≤ (coordFd c b f).2.1 := by
    have h1 : foAB (.n (b + 6)) coordAdr 4 (.n (f + 5)) (.n (b + 1)) (coordMark c)
        (fun s => cbMul s (26 + 4 * c)) (f + 18) 1 = flBase (coordAdr 0) 0 (4 - 1) (f + 18) + 3 := by
      rw [foAB_one, foldArm_snd, foldLevels_snd]; rfl
    rw [← h1, coordFd_eq, foldArms_end]; exact (hfo 1).2 16 (by omega)
  have hend : (coordFd c b f).2.1 ≤ (sCoord c enc bound b).2.1 := by
    rw [sCoord_fst, ← hf]; split <;> omega
  rw [sCoord_split]
  -- the super-child
  set σ1 := Function.update (Function.update σ (.n b) (ofK (gpow h.s))) (.n (b + 1)) (coordMark c h.s)
    with hσ1
  have he1 : Ext b (b + 2) σ σ1 := fun v hv => by
    rw [hσ1, Function.update_of_ne (hv (b + 1) (by omega) (by omega)),
      Function.update_of_ne (hv b le_rfl (by omega))]
  have h1s : σ1 (.n b) = ofK (gpow h.s) := by
    rw [hσ1, Function.update_of_ne (by simp), Function.update_self]
  have h1m : σ1 (.n (b + 1)) = coordMark c h.s := by rw [hσ1, Function.update_self]
  refine Completes.append (m := b + 2) (by omega) (by omega)
    (by rw [valsList_hint]; exact .cons ⟨b, by omega, rfl⟩ (.cons ⟨b + 1, by omega, rfl⟩ (.nil _)))
    (Completes.reload he1 (hintKeep_complete σ1 _ _ b (b + 2))) (fun σ1' _ e1 => ?_)
  subst e1
  refine Completes.append (m := b + 6) (by omega) (by omega) (rangeS_nb _ _ _ ⟨b, by omega, rfl⟩)
    (by
      rw [g15W_k]
      exact rangeS_complete (n := 256) (K := 16) hm (by norm_num) hs16 σ1 (.n b) ⟨b, by omega, rfl⟩ h1s)
    (fun σ2 he2 _ => ?_)
  -- the leaf's address
  have hs3 : SeqOK (b + 6) [addS (.n (b + 6)) (sNode 0) (.n (b + 1)), copyS (.n (b + 7)) sPP,
      cst (b + 8) (word (tw 18) 0 0), addS (.n (b + 9)) (.n (b + 6)) (.n (b + 8))] (b + 10) :=
    ⟨⟨rfl, ⟨131, by omega, rfl⟩, ⟨b + 1, by omega, rfl⟩⟩, ⟨rfl, ⟨2, by omega, rfl⟩⟩, rfl,
      ⟨rfl, ⟨b + 6, by omega, rfl⟩, ⟨b + 8, by omega, rfl⟩⟩, rfl⟩
  refine Completes.seq hs3 (by omega) (fun σ3 he3 hh3 => ?_)
  have h1σ : ∀ k < b, σ1 (.n k) = σ (.n k) := fun k hk => he1.apply (Or.inl hk)
  have h31 : ∀ k < b + 2, σ3 (.n k) = σ1 (.n k) := fun k hk => by
    rw [he3.apply (Or.inl (by omega)), he2.apply (Or.inl hk)]
  have hlow3 : ∀ k < b, σ3 (.n k) = σ (.n k) := fun k hk => by rw [h31 k (by omega), h1σ k hk]
  have e36 : σ3 (.n (b + 6)) = σ3 (sNode 0) + σ3 (.n (b + 1)) := hh3.atom (a := .add _ _ _) (by simp [addS])
  have e37 : σ3 (.n (b + 7)) = σ3 sPP := hh3.atom (a := .copy _ _) (by simp [copyS])
  have e38 : σ3 (.n (b + 8)) = word (tw 18) 0 0 := hh3.atom (a := .const _ _) (by simp [cst])
  have e39 : σ3 (.n (b + 9)) = σ3 (.n (b + 6)) + σ3 (.n (b + 8)) := hh3.atom (a := .add _ _ _) (by simp [addS])
  have hX3 : ForestX σ3 := hX.congr hb fun k hk => (hlow3 k hk).symm
  have hla3 : σ3 (.n (b + 6)) = σ (sNode 0) + coordMark c h.s := by
    rw [e36, h31 (b + 1) (by omega), h1m, show sNode 0 = V.n 131 from rfl, hlow3 131 (by omega)]
  have hlc3 : IsCanonical128 (σ3 (.n (b + 6))) := by rw [hla3]; exact canon_add hn0 (canon_word _ _)
  -- the first sub-tree
  have hsub0 := sSubtree_complete (C := C) (rd := rd) (c := c) (j := 0) (leafAt := .n (b + 6)) (enc := enc)
    (bound := bound) (b := b + 10) (by omega) ⟨b + 6, by omega, rfl⟩
    (fun en he => (henc en he).mono' (by omega)) (hbd.mono' (by omega)) hm h.sub0 hh0 σ3 hX3 hlc3
    (fun h16 => absurd h16 (by omega))
  rw [← coordS0_eq] at hsub0
  refine Completes.append (m := (coordS0 c enc bound b).2.1) (by omega) (by omega)
    (by
      rw [coordS0_eq]
      exact sSubtree_numBelow c 0 (by omega) ⟨b + 6, by omega, rfl⟩
        (fun en he => (henc en he).mono' (by omega)) (hbd.mono' (by omega)))
    hsub0 (fun σ4 he4 hp4 => ?_)
  have hlow4 : ∀ k < b, σ4 (.n k) = σ (.n k) := fun k hk => by
    rw [he4.apply (Or.inl (by omega)), hlow3 k hk]
  have hencv : encVal σ3 enc = encVal σ enc := by
    cases enc with
    | none => rfl
    | some en => obtain ⟨k, hk, rfl⟩ := henc en rfl; exact hlow3 k hk
  have hbdv : σ3 bound = σ bound := by obtain ⟨k, hk, rfl⟩ := hbd; exact hlow3 k hk
  obtain ⟨q0a, q0m, q0t, q0v, q0s, q0o, q0c1, q0c2, q0e, q0b⟩ := hp4 σ4 (fun _ _ => rfl)
  rw [hencv] at q0e
  rw [hbdv] at q0b
  simp only [Nat.add_zero] at q0e q0b
  have e0e : (coordS0 c enc bound b).2.2.1 = (subE c 0 enc (b + 10)).2.1 := by rw [coordS0_eq, sSubtree_eq]
  have e0b : (coordS0 c enc bound b).2.2.2.1 = .n (subFd c 0 enc (b + 10)).2.1 := by rw [coordS0_eq, sSubtree_eq]
  have e0t : (coordS0 c enc bound b).2.2.2.2 = ((subFd c 0 enc (b + 10)).2.2.1, (subFd c 0 enc (b + 10)).2.2.2.1) := by
    rw [coordS0_eq, sSubtree_eq]
  have hX4 : ForestX σ4 := hX.congr hb fun k hk => (hlow4 k hk).symm
  have hla4 : σ4 (.n (b + 6)) = σ3 (.n (b + 6)) := he4.apply (Or.inl (by omega))
  -- the second sub-tree
  have hsub1 := sSubtree_complete (C := C) (rd := rd) (c := c) (j := 1) (leafAt := .n (b + 6))
    (enc := some (coordS0 c enc bound b).2.2.1) (bound := (coordS0 c enc bound b).2.2.2.1)
    (b := (coordS0 c enc bound b).2.1) (by omega) ⟨b + 6, by omega, rfl⟩
    (fun en he => by cases he; rw [ek0]; exact ⟨k0, hk0, rfl⟩) (by rw [s0b]; exact ⟨_, by omega, rfl⟩) hm h.sub1 hh1
    σ4 hX4 (by rw [hla4]; exact hlc3) (fun h16 => ⟨⟨_, rfl⟩, by
      obtain ⟨-, h17, -⟩ := hlast (by omega)
      simp only [encVal]
      rw [hlow4 17 (by omega), h17, e0e, q0e, hEnc, add_assoc]⟩)
  rw [← coordS1_eq] at hsub1
  refine Completes.append (m := f) (by omega) (by omega)
    (by
      rw [hf, coordS1_eq]
      exact sSubtree_numBelow c 1 (by omega) ⟨b + 6, by omega, rfl⟩
        (fun en he => by cases he; rw [ek0]; exact ⟨k0, by omega, rfl⟩) (by rw [s0b]; exact ⟨_, by omega, rfl⟩))
    hsub1 (fun σ5 he5 hp5 => ?_)
  obtain ⟨q1a, q1m, q1t, q1v, q1s, q1o, q1c1, q1c2, q1e, q1b⟩ := hp5 σ5 (fun _ _ => rfl)
  have h54 : ∀ k < (coordS0 c enc bound b).2.1, σ5 (.n k) = σ4 (.n k) := fun k hk => he5.apply (Or.inl hk)
  have hlow5 : ∀ k < b, σ5 (.n k) = σ (.n k) := fun k hk => by rw [h54 k (by omega), hlow4 k hk]
  have he0v : encVal σ4 (some (coordS0 c enc bound b).2.2.1) = encVal σ enc + fkWeight h.sub0.t (2 * c) := by
    show σ4 _ = _
    rw [e0e, q0e]
  have hb0v : σ4 (coordS0 c enc bound b).2.2.2.1 = σ bound + cbMul h.sub0.a (58 + 3 * (2 * c)) := by
    rw [e0b, q0b]
  rw [he0v] at q1e
  rw [hb0v] at q1b
  have e1e : (coordS1 c enc bound b).2.2.1 =
      (subE c 1 (some (coordS0 c enc bound b).2.2.1) (coordS0 c enc bound b).2.1).2.1 := by
    rw [coordS1_eq, sSubtree_eq]
  have e1b : (coordS1 c enc bound b).2.2.2.1 =
      .n (subFd c 1 (some (coordS0 c enc bound b).2.2.1) (coordS0 c enc bound b).2.1).2.1 := by
    rw [coordS1_eq, sSubtree_eq]
  have e1t : (coordS1 c enc bound b).2.2.2.2 =
      ((subFd c 1 (some (coordS0 c enc bound b).2.2.1) (coordS0 c enc bound b).2.1).2.2.1,
        (subFd c 1 (some (coordS0 c enc bound b).2.2.1) (coordS0 c enc bound b).2.1).2.2.2.1) := by
    rw [coordS1_eq, sSubtree_eq]
  have hX5 : ForestX σ5 := hX.congr hb fun k hk => (hlow5 k hk).symm
  -- the super-child's hash
  have hs6 : SeqOK f [copyS (.n f) (coordS1 c enc bound b).2.2.2.2.1,
      copyS (.n (f + 1)) (coordS1 c enc bound b).2.2.2.2.2, cst (f + 2) (word 1 0 0),
      cst (f + 3) (word 0 0 0), cst (f + 4) (word (2 ^ 63) 0 0)] (f + 5) := by
    rw [eL1]
    exact ⟨⟨rfl, ⟨L1, by omega, rfl⟩⟩, ⟨rfl, ⟨L1 + 1, by omega, rfl⟩⟩, rfl, rfl, rfl, rfl⟩
  refine Completes.seq hs6 (by omega) (fun σ6 he6 hh6 => ?_)
  have h65 : ∀ k < f, σ6 (.n k) = σ5 (.n k) := fun k hk => he6.apply (Or.inl hk)
  have c0 : σ6 (.n f) = σ6 (coordS1 c enc bound b).2.2.2.2.1 :=
    hh6.atom (a := .copy _ _) (by simp [copyS, hf])
  have c1 : σ6 (.n (f + 1)) = σ6 (coordS1 c enc bound b).2.2.2.2.2 :=
    hh6.atom (a := .copy _ _) (by simp [copyS, hf])
  have c2 : σ6 (.n (f + 2)) = word 1 0 0 := hh6.atom (a := .const _ _) (by simp [cst, hf])
  have c3 : σ6 (.n (f + 3)) = word 0 0 0 := hh6.atom (a := .const _ _) (by simp [cst, hf])
  have c4 : σ6 (.n (f + 4)) = word (2 ^ 63) 0 0 := hh6.atom (a := .const _ _) (by simp [cst, hf])
  have hpad6 : PadOK σ6 sPad := (hX5.2.1).congr (b := f) (by simp only [sPad]; omega) fun k hk => (h65 k hk).symm
  have hcan6 : ∀ cc : Fin 13, IsCanonical128 (cells13 ([.n (b + 7), .n (b + 9), (coordS0 c enc bound b).2.2.2.2.1,
      (coordS0 c enc bound b).2.2.2.2.2, .n f, .n (f + 1), .n (f + 2), .n (f + 3), .n (f + 4),
      .n (sPad + 1), .n (sPad + 2), .n (sPad + 3), .n (sPad + 4)].map σ6) cc) := by
    have g7 : IsCanonical128 (σ6 (.n (b + 7))) := by
      rw [h65 _ (by omega), h54 _ (by omega), he4.apply (Or.inl (by omega)), e37,
        show sPP = V.n 2 from rfl, hlow3 2 (by omega)]
      exact hX.1
    have g9 : IsCanonical128 (σ6 (.n (b + 9))) := by
      rw [h65 _ (by omega), h54 _ (by omega), he4.apply (Or.inl (by omega)), e39, e38]
      exact canon_add hlc3 (canon_word _ _)
    have g01 : IsCanonical128 (σ6 (coordS0 c enc bound b).2.2.2.2.1) := by
      rw [eL0]; simp only
      rw [h65 _ (by omega), h54 _ (by omega), ← show (coordS0 c enc bound b).2.2.2.2.1 = .n L0 by rw [eL0]]
      rw [e0t]; exact q0c1
    have g02 : IsCanonical128 (σ6 (coordS0 c enc bound b).2.2.2.2.2) := by
      rw [eL0]; simp only
      rw [h65 _ (by omega), h54 _ (by omega), ← show (coordS0 c enc bound b).2.2.2.2.2 = .n (L0 + 1) by rw [eL0]]
      rw [e0t]; exact q0c2
    have gf0 : IsCanonical128 (σ6 (.n f)) := by
      rw [c0, eL1]; simp only
      rw [h65 _ (by omega), ← show (coordS1 c enc bound b).2.2.2.2.1 = .n L1 by rw [eL1]]
      rw [e1t]; exact q1c1
    have gf1 : IsCanonical128 (σ6 (.n (f + 1))) := by
      rw [c1, eL1]; simp only
      rw [h65 _ (by omega), ← show (coordS1 c enc bound b).2.2.2.2.2 = .n (L1 + 1) by rw [eL1]]
      rw [e1t]; exact q1c2
    obtain ⟨-, p1, p2, p3, p4⟩ := hpad6
    intro cc
    fin_cases cc <;> simp only [cells13, List.map_cons, List.map_nil, List.getD_cons_zero,
      List.getD_cons_succ]
    · exact g7
    · exact g9
    · exact g01
    · exact g02
    · exact gf0
    · exact gf1
    · rw [c2]; exact canon_word _ _
    · rw [c3]; exact canon_word _ _
    · rw [c4]; exact canon_word _ _
    · rw [p1]; exact canon_zero
    · rw [p2]; exact canon_zero
    · rw [p3]; exact canon_zero
    · rw [p4]; exact canon_zero
  have hin6 : ∀ v ∈ [.n (b + 7), .n (b + 9), (coordS0 c enc bound b).2.2.2.2.1,
      (coordS0 c enc bound b).2.2.2.2.2, .n f, .n (f + 1), .n (f + 2), .n (f + 3), .n (f + 4),
      .n (sPad + 1), .n (sPad + 2), .n (sPad + 3), .n (sPad + 4)], ∃ j < f + 5, v = V.n j := by
    rw [eL0]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro v (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      exact ⟨_, by first | omega | (simp only [sPad]; omega), rfl⟩
  refine Completes.append (m := f + 18) (by omega) (by omega)
    (by
      simp only [kecS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil]
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · obtain ⟨j, hj, rfl⟩ := hin6 v hv; exact ⟨j, by omega, rfl⟩
      · exact runV_mem_nb (by omega) hv)
    ((kecS_complete (C := C) (rd := rd) σ6 (f + 5) rfl hin6 hcan6 false false).mono le_rfl
      (by omega) (fun σ' h' => h'))
    (fun σ7 he7 h7 => ?_)
  have h76 : ∀ k < f + 5, σ7 (.n k) = σ6 (.n k) := fun k hk => he7.apply (Or.inl hk)
  have hlow7 : ∀ k < b, σ7 (.n k) = σ (.n k) := fun k hk => by
    rw [h76 k (by omega), h65 k (by omega), hlow5 k hk]
  have hX7 : ForestX σ7 := hX.congr hb fun k hk => (hlow7 k hk).symm
  have hla7 : σ7 (.n (b + 6)) = σ3 (.n (b + 6)) := by
    rw [h76 _ (by omega), h65 _ (by omega), h54 _ (by omega), hla4]
  have hs7 : IsCanonical128 (σ7 (.n (f + 5))) := by
    rw [show f + 5 = f + 5 + 0 from rfl, h7 0 (by norm_num)]; exact canon_kOut _ _ _ _
  have hb7 : σ7 (.n b) = ofK (gpow h.s) := by
    rw [h76 _ (by omega), h65 _ (by omega), h54 _ (by omega), he4.apply (Or.inl (by omega)),
      h31 b (by omega), h1s]
  have hm7 : σ7 (.n (b + 1)) = coordMark c h.s := by
    rw [h76 _ (by omega), h65 _ (by omega), h54 _ (by omega), he4.apply (Or.inl (by omega)),
      h31 _ (by omega), h1m]
  -- the top fold
  have hfd := foldArms_complete (C := C) (rd := rd) (atV := .n (b + 6)) (adr := coordAdr) (height := 4)
    (node0 := .n (f + 5)) (markV := .n (b + 1)) (markC := coordMark c) (wC := fun s => cbMul s (26 + 4 * c))
    (b := f + 18) (index := h.s) (x := .n b) (by norm_num; omega) (by norm_num) (by omega)
    (fun i _ => coordAdr_ok i) ⟨b + 6, by omega, rfl⟩ ⟨f + 5, by omega, rfl⟩ ⟨b + 1, by omega, rfl⟩
    ⟨b, by omega, rfl⟩ h.sibs (fun l _ => hsib l) σ7
    (fun v hx _ => hX7.sx (by rw [hla7]; exact hlc3) hs7 v hx) hm7 hb7
  rw [← coordFd_eq] at hfd
  have hfdo1 : (coordFd c b f).2.2.1 = .n (flBase (coordAdr 0) 0 (4 - 1) (f + 18)) := by rw [coordFd_eq, hfo3]
  have hfdo2 : (coordFd c b f).2.2.2.1 = .n (flBase (coordAdr 0) 0 (4 - 1) (f + 18) + 1) := by
    rw [coordFd_eq, hfo3]
  have hfdo3 : (coordFd c b f).2.2.2.2 = .n (flBase (coordAdr 0) 0 (4 - 1) (f + 18) + 2) := by
    rw [coordFd_eq, hfo3]
  refine Completes.append (m := (coordFd c b f).2.1) hfdE hend
    (by
      simp only [valsList_cons, valsList_nil, Stmt.vals, List.append_nil]
      refine .cons ⟨b, by omega, rfl⟩ ?_
      rw [coordFd_eq]
      exact foldArms_numBelow (by norm_num) (by omega) (fun i _ => coordAdr_ok i) ⟨b + 6, by omega, rfl⟩
        ⟨f + 5, by omega, rfl⟩ ⟨b + 1, by omega, rfl⟩)
    hfd (fun σ8 he8 ⟨f1, f2, f3, f4, f5⟩ => ?_)
  have h87 : ∀ k < f + 18, σ8 (.n k) = σ7 (.n k) := fun k hk => he8.apply (Or.inl hk)
  -- the post, from the final valuation
  have hspos : ∃ k, (sCoord c enc bound b).2.2.2.1 = .n k ∧ k < (sCoord c enc bound b).2.1 := by
    rw [sCoord_eq]
    by_cases hl : c + 1 = 8
    · simp only [hl, ↓reduceIte]; exact ⟨18, rfl, by rw [← hf]; omega⟩
    · simp only [hl, ↓reduceIte]; exact ⟨_, rfl, by rw [← hf]; omega⟩
  have post : ∀ σ9 : Val, (∀ k < (coordFd c b f).2.1, σ9 (.n k) = σ8 (.n k)) →
      σ9 (sCoord c enc bound b).2.2.2.1 = σ bound + hBound c h →
      ∀ σ'', AgreeBelow (sCoord c enc bound b).2.1 σ9 σ'' →
        CoordPost (encVal σ enc) (σ bound) c enc bound b h σ'' := by
    intro σ9 h98 hbo σ'' hag
    have t8 : ∀ k < (coordFd c b f).2.1, σ'' (.n k) = σ8 (.n k) := fun k hk => by
      rw [hag.apply ⟨k, by omega, rfl⟩, h98 k hk]
    have t5 : ∀ k < f, σ'' (.n k) = σ5 (.n k) := fun k hk => by
      rw [t8 k (by omega), h87 k (by omega), h76 k (by omega), h65 k hk]
    have t4 : ∀ k < (coordS0 c enc bound b).2.1, σ'' (.n k) = σ4 (.n k) := fun k hk => by
      rw [t5 k (by omega), h54 k hk]
    refine ⟨by rw [t8 _ (by omega), h87 _ (by omega)]; exact hb7,
      by rw [t8 _ (by omega), h87 _ (by omega)]; exact hm7, ?_, ?_, fun l hl => ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := hp4 σ'' (fun k hk => (t4 k hk).symm)
      rw [hencv, hbdv] at this
      exact this
    · have := hp5 σ'' (fun k hk => (t5 k hk).symm)
      rw [he0v, hb0v] at this
      exact this
    · obtain ⟨p1, p2⟩ := foldPos_lt (atV := .n (b + 6)) (adr := coordAdr) (height := 4) (node0 := .n (f + 5))
        (markV := .n (b + 1)) (markC := coordMark c) (wC := fun s => cbMul s (26 + 4 * c)) (b := f + 18)
        (index := h.s) (by norm_num; omega) (show l < 4 - 1 by omega)
      rw [← coordFd_eq] at p2
      show σ'' (.n (flBase (coordAdr h.s) 0 l (foAB (.n (b + 6)) coordAdr 4 (.n (f + 5)) (.n (b + 1))
        (coordMark c) (fun s => cbMul s (26 + 4 * c)) (f + 18) h.s))) = h.sibs l
      rw [t8 _ (by omega)]
      exact f1 l (by omega)
    · have e : 2 ^ (4 - 1) = 2 ^ 3 := rfl
      rw [e] at f2
      by_cases h0 : h.s / 2 ^ 3 = 0 <;> simp only [h0, ↓reduceIte] at f2 ⊢
      · rw [hfdo2] at f2 ⊢; rw [t8 _ (by omega)]; exact f2
      · rw [hfdo1] at f2 ⊢; rw [t8 _ (by omega)]; exact f2
    · rw [hfdo1] at f3 ⊢; rw [t8 _ (by omega)]; exact f3
    · rw [hfdo2] at f4 ⊢; rw [t8 _ (by omega)]; exact f4
    · have h5p := hp5 σ'' (fun k hk => (t5 k hk).symm)
      rw [he0v, hb0v] at h5p
      have hq := h5p.2.2.2.2.2.2.2.2.1
      have e : (sCoord c enc bound b).2.2.1 = (coordS1 c enc bound b).2.2.1 := by rw [sCoord_eq]
      rw [e, e1e, hq, hEnc, add_assoc]
    · obtain ⟨k, ek, hk⟩ := hspos
      rw [ek, hag.apply ⟨k, hk, rfl⟩, ← ek]
      exact hbo
  by_cases hl : c + 1 = 8
  · obtain ⟨-, -, h18⟩ := hlast hl
    have hfst : (sCoord c enc bound b).2.1 = (coordFd c b f).2.1 := by rw [sCoord_fst, ← hf]; simp [hl]
    have hsnd : (sCoord c enc bound b).2.2.2.1 = .n 18 := by rw [sCoord_eq]; simp [hl]
    have h818 : σ8 (.n 18) = σ (.n 18) := by
      rw [h87 _ (by omega), hlow7 _ (by omega)]
    have h8b1 : σ8 (coordS1 c enc bound b).2.2.2.1 = σ bound + cbMul h.sub0.a (58 + 3 * (2 * c)) +
        cbMul h.sub1.a (58 + 3 * (2 * c + 1)) := by
      have hsf : (subFd c 1 (some (coordS0 c enc bound b).2.2.1) (coordS0 c enc bound b).2.1).2.1 < f := by
        have := e1b.symm.trans s1b
        simp only [V.mk.injEq, true_and] at this
        omega
      rw [e1b, h87 _ (by omega), h76 _ (by omega), h65 _ hsf]
      exact q1b
    simp only [hl, ↓reduceIte]
    rw [hfst]
    refine completes_atoms rfl (Ext.refl _ _ _) ?_ (fun x hx => ?_)
    · rw [← hfst]
      exact post σ8 (fun _ _ => rfl) (by rw [hsnd, h818, h18])
    · simp only [addS, List.mem_singleton, Stmt.atom.injEq] at hx
      subst hx
      show σ8 (.n 18) = σ8 (coordS1 c enc bound b).2.2.2.1 + σ8 (coordFd c b f).2.2.2.2
      rw [h818, h18, h8b1, f5, hBound]
      ring
  · have hfst : (sCoord c enc bound b).2.1 = (coordFd c b f).2.1 + 1 := by rw [sCoord_fst, ← hf]; simp [hl]
    have hsnd : (sCoord c enc bound b).2.2.2.1 = .n (coordFd c b f).2.1 := by rw [sCoord_eq]; simp [hl, ← hf]
    have h8b1 : σ8 (coordS1 c enc bound b).2.2.2.1 = σ bound + cbMul h.sub0.a (58 + 3 * (2 * c)) +
        cbMul h.sub1.a (58 + 3 * (2 * c + 1)) := by
      have hsf : (subFd c 1 (some (coordS0 c enc bound b).2.2.1) (coordS0 c enc bound b).2.1).2.1 < f := by
        have := e1b.symm.trans s1b
        simp only [V.mk.injEq, true_and] at this
        omega
      rw [e1b, h87 _ (by omega), h76 _ (by omega), h65 _ hsf]
      exact q1b
    simp only [hl, ↓reduceIte]
    rw [hfst]
    obtain ⟨σ9, he9, h9, hh9⟩ := addS_complete (C := C) (rd := rd) (x := (coordS1 c enc bound b).2.2.2.1)
      (y := (coordFd c b f).2.2.2.2) σ8 (coordFd c b f).2.1 (by rw [s1b]; exact ⟨_, by omega, rfl⟩)
      (by rw [hfdo3]; exact ⟨_, by omega, rfl⟩)
    refine ⟨σ9, he9, ?_, hh9⟩
    rw [← hfst]
    exact post σ9 (fun k hk => he9.apply (Or.inl hk)) (by rw [hsnd, h9, h8b1, f5, hBound]; ring)

end
end LeanVM.Guest.B1.Sig
