/-
  LeanVM.Guest.B1.Sig.SphincsSubComplete

  A sub-tree of `verify_sig_lean_sphincs`'s forest completes: its child and codeword index hinted,
  their range checks, the forest key's dispatch, the encoding's update and the fold's dispatch.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsFoldArms
public import LeanVM.Guest.B1.Sig.SphincsBytes

/-!
# A sub-tree, complete

* `ForestX`: `P`, the padding run and the address constants are canonical;
* `SubH`: a sub-tree's hints: its codeword index `t`, its child `a`, the chains' values and the
  fold's siblings (the other level-2 node last);
* `sSubtree_complete`: the sub-tree completes, its hints kept, its two level-2 nodes canonical, the
  encoding and the bound updated.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

attribute [local irreducible] fkArms foldArms

variable {C : CallRel} {rd : Reader}

/-- `P`, the padding run and the address constants are canonical. -/
def ForestX (σ : Val) : Prop :=
  IsCanonical128 (σ sPP) ∧ PadOK σ sPad ∧ ∀ k < 41, IsCanonical128 (σ (.n (165 + k)))

theorem ForestX.congr {σ σ' : Val} (h : ForestX σ) {b : Nat} (hb : 206 ≤ b) (hag : AgreeBelow b σ σ') :
    ForestX σ' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by show IsCanonical128 (σ' (.n 2)); rw [hag.apply ⟨2, by omega, rfl⟩]; exact h1,
    h2.congr (by simp only [sPad]; omega) hag,
    fun k hk => by rw [hag.apply ⟨165 + k, by omega, rfl⟩]; exact h3 k hk⟩

theorem ForestX.sx {σ : Val} (h : ForestX σ) {a1 a2 : V} (h1 : IsCanonical128 (σ a1))
    (h2 : IsCanonical128 (σ a2)) : ∀ v, SX a1 a2 v → IsCanonical128 (σ v) := by
  obtain ⟨hp, hpad, hc⟩ := h
  rintro v (rfl | rfl | rfl | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩)
  · exact h1
  · exact h2
  · exact hp
  · exact hc k hk
  · obtain ⟨q0, q1, q2, q3, q4⟩ := hpad
    interval_cases k
    · rw [show sPad + 0 = sPad from rfl, q0]; exact canon_word _ _
    · rw [q1]; exact canon_zero
    · rw [q2]; exact canon_zero
    · rw [q3]; exact canon_zero
    · rw [q4]; exact canon_zero

/-- A sub-tree's hints. -/
structure SubH where
  t : Nat
  a : Nat
  vals : Nat → E
  sibs : Nat → E

def SubH.OK (h : SubH) : Prop :=
  h.t < 256 ∧ h.a < 8 ∧ (∀ i, IsCanonical128 (h.vals i)) ∧ ∀ l, IsCanonical128 (h.sibs l)

/-- The mark a sub-tree's fold checks. -/
def subMark (j a : Nat) : E := word (j * 2 ^ 39 + a * 2 ^ 40) 0 0

theorem sSubtree_split (c j : Nat) (leafAt : V) (enc : Option V) (bound : V) (b : Nat) :
    (sSubtree c j leafAt enc bound b).1 =
      [hintW "sp_keys" [.n b, .n (b + 1)]] ++ (rangeS (.n b) g7W (b + 2) ++
        ([hintW "sp_words" [.n (b + 6)]] ++ (rangeS (.n (b + 6)) g255W (b + 7) ++
          ([addS (.n (b + 11)) leafAt (.n (b + 1))] ++ ([.match_ (.n (b + 6)) (subFk c j b).1] ++
            ((subE c j enc b).1 ++ ([.match_ (.n b) (subFd c j enc b).1] ++
              [addS (.n (subFd c j enc b).2.1) bound (subFd c j enc b).2.2.2.2]))))))) := by
  rw [sSubtree_eq]
  simp

theorem rangeS_nb (x : V) (bound : E) (b : Nat) (hx : NBv b x) :
    NumBelow (b + 4) (Stmt.valsList (rangeS x bound b)) := by
  simp only [rangeS, cst, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil,
    List.cons_append, List.nil_append]
  exact .cons ⟨b, by omega, rfl⟩ (.cons (hx.mono' (by omega)) (.cons ⟨b + 1, by omega, rfl⟩
    (.cons ⟨b + 2, by omega, rfl⟩ (.cons ⟨b + 3, by omega, rfl⟩ (.cons ⟨b, by omega, rfl⟩ (.nil _))))))

theorem g7W_k : g7W = ofK (gpow (8 - 1)) := g7W_eq
theorem g255W_k : g255W = ofK (gpow (256 - 1)) := g255W_eq
theorem g15W_k : g15W = ofK (gpow (16 - 1)) := g15W_eq
theorem g63W_k : g63W = ofK (gpow (64 - 1)) := g63W_eq

/-- What a sub-tree's valuation holds: its hints, its level-2 nodes canonical, its encoding and
bound updated. -/
def SubPost (σ0 : Val) (c j : Nat) (enc : Option V) (bound : V) (b : Nat) (h : SubH)
    (σ : Val) : Prop :=
  σ (.n b) = ofK (gpow h.a) ∧ σ (.n (b + 1)) = subMark j h.a ∧ σ (.n (b + 6)) = ofK (gpow h.t) ∧
    (∀ i < 6, σ (.n (fkCB h.t (.n (b + 11)) 0 (fkAB (2 * c + j) (.n (b + 11)) (b + 12) h.t) i)) = h.vals i) ∧
    (∀ l < 2, σ (.n (flBase (subAdr h.a) 0 l (foAB (.n (b + 11)) subAdr 3 (subFk c j b).2.2.1 (.n (b + 1))
      (subMark j) (fun a => cbMul a (58 + 3 * (2 * c + j))) (subE c j enc b).2.2 h.a))) = h.sibs l) ∧
    σ (if h.a / 2 ^ 2 = 0 then (subFd c j enc b).2.2.2.1 else (subFd c j enc b).2.2.1) = h.sibs 2 ∧
    IsCanonical128 (σ (subFd c j enc b).2.2.1) ∧ IsCanonical128 (σ (subFd c j enc b).2.2.2.1) ∧
    σ (subE c j enc b).2.1 = encVal σ0 enc + fkWeight h.t (2 * c + j) ∧
    σ (.n (subFd c j enc b).2.1) = σ0 bound + cbMul h.a (58 + 3 * (2 * c + j))

theorem subFd_eq (c j : Nat) (enc : Option V) (b : Nat) :
    subFd c j enc b = foldArms (.n (b + 11)) subAdr 3 (subFk c j b).2.2.1 (.n (b + 1)) (subMark j)
      (fun a => cbMul a (58 + 3 * (2 * c + j))) (subE c j enc b).2.2 := rfl

theorem subAdr_ok (a : Nat) (ha : a < 8) : AdrOK (subAdr a) (3 - 1) := by
  intro l hl x hx
  simp only [subAdr, Sum.inl.injEq] at hx
  exact ⟨25 + 2 * a + l, by omega, by rw [← hx]; simp only [sSubTws]; congr 1; omega⟩

theorem subE_snd (c j : Nat) (enc : Option V) (b : Nat) :
    (subFk c j b).2.1 ≤ (subE c j enc b).2.2 ∧ (subE c j enc b).2.2 ≤ (subFk c j b).2.1 + 1 := by
  unfold subE
  split
  · simp
  · split <;> simp

theorem subFk_eq (c j b : Nat) : subFk c j b = fkArms (2 * c + j) (.n (b + 11)) (b + 12) := rfl

/-- **A sub-tree completes**, its hints loaded: they are kept, its two level-2 nodes canonical, the
encoding and the bound updated; the last checks the digest's first cell. -/
theorem sSubtree_complete {c j : Nat} {leafAt : V} {enc : Option V} {bound : V}
    {b : Nat} (hb : 206 ≤ b) (hla : NBv b leafAt) (henc : ∀ en, enc = some en → NBv b en)
    (hbd : NBv b bound) (hm : MemOK rd 256) (h : SubH) (hh : h.OK) (σ : Val) (hX : ForestX σ)
    (hlc : IsCanonical128 (σ leafAt))
    (hlast : 2 * c + j + 1 = 16 → (∃ en, enc = some en) ∧
      σ (.n 17) = encVal σ enc + fkWeight h.t (2 * c + j)) :
    Completes C rd b (sSubtree c j leafAt enc bound b).2.1 (sSubtree c j leafAt enc bound b).1 σ
      (fun σ' => ∀ σ'', AgreeBelow (sSubtree c j leafAt enc bound b).2.1 σ' σ'' →
        SubPost σ c j enc bound b h σ'') := by
  obtain ⟨ht, ha, hv, hs⟩ := hh
  have hend : (sSubtree c j leafAt enc bound b).2.1 = (subFd c j enc b).2.1 + 1 := by rw [sSubtree_eq]
  rw [sSubtree_split, hend]
  -- the bounds
  have hka : NBv (b + 12) (V.n (b + 11)) := ⟨b + 11, by omega, rfl⟩
  have hfk := fkAB_mono (w := 2 * c + j) (b := b + 12) (by omega) hka
  have hfkE : b + 12 ≤ (subFk c j b).2.1 := by rw [subFk_eq, fkArms_end]; exact (hfk 256).1
  obtain ⟨hE1, hE2⟩ := subE_snd c j enc b
  obtain ⟨o1, o2⟩ := fkArms_outs (2 * c + j) (.n (b + 11)) (b + 12)
  have hB0 : b + 12 ≤ (fkChains 0 (.n (b + 11)) 6 0 (b + 12)).2.1 :=
    KSeq.le (fkChains_kseq (t := 0) (lo := b + 12) (by omega) hka 6 0 (b + 12) (by omega) le_rfl).1
  have hB0E : (fkChains 0 (.n (b + 11)) 6 0 (b + 12)).2.1 + 17 ≤ (subFk c j b).2.1 := by
    have h1 : fkAB (2 * c + j) (.n (b + 11)) (b + 12) 1 = (fkChains 0 (.n (b + 11)) 6 0 (b + 12)).2.1 + 17 := by
      rw [fkAB_one, fkArm_snd]; rfl
    rw [← h1, subFk_eq, fkArms_end]; exact (hfk 1).2 256 (by omega)
  have hfo := foAB_mono (atV := .n (b + 11)) (adr := subAdr) (height := 3) (node0 := (subFk c j b).2.2.1)
    (markV := .n (b + 1)) (markC := subMark j) (wC := fun a => cbMul a (58 + 3 * (2 * c + j)))
    (b := (subE c j enc b).2.2)
  have hfdE : (subE c j enc b).2.2 ≤ (subFd c j enc b).2.1 := by
    rw [subFd_eq, foldArms_end]; exact (hfo 8).1
  have hfo3 := foldArms_outs (atV := .n (b + 11)) (adr := subAdr) (height := 3) (node0 := (subFk c j b).2.2.1)
    (markV := .n (b + 1)) (markC := subMark j) (wC := fun a => cbMul a (58 + 3 * (2 * c + j)))
    (subE c j enc b).2.2
  have hL0 := flBase_ge (subAdr 0) 0 (3 - 1) (subE c j enc b).2.2
  have hL0E : flBase (subAdr 0) 0 (3 - 1) (subE c j enc b).2.2 + 3 ≤ (subFd c j enc b).2.1 := by
    have h1 : foAB (.n (b + 11)) subAdr 3 (subFk c j b).2.2.1 (.n (b + 1)) (subMark j)
        (fun a => cbMul a (58 + 3 * (2 * c + j))) (subE c j enc b).2.2 1 =
        flBase (subAdr 0) 0 (3 - 1) (subE c j enc b).2.2 + 3 := by
      rw [foAB_one, foldArm_snd, foldLevels_snd]; rfl
    rw [← h1, subFd_eq, foldArms_end]; exact (hfo 1).2 8 (by omega)
  -- the keys
  set σ1 := Function.update (Function.update σ (.n b) (ofK (gpow h.a))) (.n (b + 1)) (subMark j h.a) with hσ1
  have he1 : Ext b (b + 2) σ σ1 := fun v hv => by
    rw [hσ1, Function.update_of_ne (hv (b + 1) (by omega) (by omega)),
      Function.update_of_ne (hv b le_rfl (by omega))]
  have h1a : σ1 (.n b) = ofK (gpow h.a) := by
    rw [hσ1, Function.update_of_ne (by simp), Function.update_self]
  have h1m : σ1 (.n (b + 1)) = subMark j h.a := by rw [hσ1, Function.update_self]
  refine Completes.append (m := b + 2) (by omega) (by omega)
    (by rw [valsList_hint]; exact .cons ⟨b, by omega, rfl⟩ (.cons ⟨b + 1, by omega, rfl⟩ (.nil _)))
    (Completes.reload he1 (hintKeep_complete σ1 _ _ b (b + 2))) (fun σ1' _ e1 => ?_)
  subst e1
  refine Completes.append (m := b + 6) (by omega) (by omega) (rangeS_nb _ _ _ ⟨b, by omega, rfl⟩)
    (by
      rw [g7W_k]
      exact rangeS_complete (n := 256) (K := 8) hm (by norm_num) ha σ1 (.n b) ⟨b, by omega, rfl⟩ h1a)
    (fun σ2 he2 _ => ?_)
  -- the codeword index
  set σ3 := Function.update σ2 (.n (b + 6)) (ofK (gpow h.t)) with hσ3
  have he3 : Ext (b + 6) (b + 7) σ2 σ3 := fun v hv => Function.update_of_ne (hv (b + 6) le_rfl (by omega)) _ _
  refine Completes.append (m := b + 7) (by omega) (by omega)
    (by rw [valsList_hint]; exact .cons ⟨b + 6, by omega, rfl⟩ (.nil _))
    (Completes.reload he3 (hintKeep_complete σ3 _ _ (b + 6) (b + 7))) (fun σ3' _ e3 => ?_)
  subst e3
  have h3t : σ3 (.n (b + 6)) = ofK (gpow h.t) := Function.update_self ..
  refine Completes.append (m := b + 11) (by omega) (by omega) (rangeS_nb _ _ _ ⟨b + 6, by omega, rfl⟩)
    (by
      rw [g255W_k]
      exact rangeS_complete (n := 256) (K := 256) hm le_rfl ht σ3 (.n (b + 6)) ⟨b + 6, by omega, rfl⟩ h3t)
    (fun σ4 he4 _ => ?_)
  -- the key's address
  have hlab : NBv (b + 11) leafAt := NBv.mono' hla (show b ≤ b + 11 by omega)
  refine Completes.append (m := b + 12) (by omega) (by omega)
    (by simp only [addS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil]
        exact .cons ⟨b + 11, by omega, rfl⟩ (.cons (NBv.mono' hla (show b ≤ b + 12 by omega))
          (.cons ⟨b + 1, by omega, rfl⟩ (.nil _))))
    (addS_complete σ4 (b + 11) hlab ⟨b + 1, by omega, rfl⟩) (fun σ5 he5 h5 => ?_)
  -- what the valuation holds so far
  have h41 : ∀ k < b + 2, σ4 (.n k) = σ1 (.n k) := fun k hk => by
    rw [he4.apply (Or.inl (by omega)), he3 (.n k) (fun j h1 h2 e => by simp at e; omega),
      he2.apply (Or.inl hk)]
  have h1σ : ∀ k < b, σ1 (.n k) = σ (.n k) := fun k hk => he1.apply (Or.inl hk)
  have h54 : ∀ k < b + 11, σ5 (.n k) = σ4 (.n k) := fun k hk => he5.apply (Or.inl hk)
  have h5b : σ5 (.n b) = ofK (gpow h.a) := by rw [h54 b (by omega), h41 b (by omega), h1a]
  have h5b1 : σ5 (.n (b + 1)) = subMark j h.a := by rw [h54 _ (by omega), h41 _ (by omega), h1m]
  have h5t : σ5 (.n (b + 6)) = ofK (gpow h.t) := by
    rw [h54 _ (by omega), he4.apply (Or.inl (by omega)), h3t]
  have hlow5 : ∀ k < b, σ5 (.n k) = σ (.n k) := fun k hk => by
    rw [h54 k (by omega), h41 k (by omega), h1σ k hk]
  have hla5 : σ5 leafAt = σ leafAt := by obtain ⟨k, hk, rfl⟩ := hla; exact hlow5 k hk
  have hkey : σ5 (.n (b + 11)) = σ leafAt + subMark j h.a := by
    rw [h5]
    obtain ⟨k, hk, rfl⟩ := hla
    rw [← h54 k (by omega), hlow5 k hk, h41 (b + 1) (by omega), h1m]
  have hX5 : ForestX σ5 := hX.congr hb fun k hk => (hlow5 k hk).symm
  have hkc : IsCanonical128 (σ5 (.n (b + 11))) := by rw [hkey]; exact canon_add hlc (canon_word _ _)
  -- the forest key
  have hfkc := fkArms_complete (C := C) (rd := rd) (w := 2 * c + j) (t := h.t) (keyAt := .n (b + 11))
    (x := .n (b + 6)) (b := b + 12) ht (by omega) hka ⟨b + 6, by omega, rfl⟩ h.vals (fun i _ => hv i) σ5
    (fun v hx _ => hX5.sx hkc hkc v hx) h5t
  rw [← subFk_eq] at hfkc
  refine Completes.append (m := (subFk c j b).2.1) hfkE (by omega)
    (by
      simp only [valsList_cons, valsList_nil, Stmt.vals, List.append_nil]
      exact .cons ⟨b + 6, by omega, rfl⟩ (by rw [subFk_eq]; exact fkArms_numBelow (by omega) hka))
    hfkc (fun σ6 he6 ⟨k1, k2, k3⟩ => ?_)
  have h65 : ∀ k < b + 12, σ6 (.n k) = σ5 (.n k) := fun k hk => he6.apply (Or.inl hk)
  have hfl : (subFk c j b).2.2.1 = .n ((fkChains 0 (.n (b + 11)) 6 0 (b + 12)).2.1 + 15) := by
    rw [subFk_eq]; exact o1
  have hfw : (subFk c j b).2.2.2 = .n ((fkChains 0 (.n (b + 11)) 6 0 (b + 12)).2.1 + 16) := by
    rw [subFk_eq]; exact o2
  -- the encoding
  have hS7 : Completes C rd (subFk c j b).2.1 (subE c j enc b).2.2 (subE c j enc b).1 σ6
      (fun σ' => σ' (subE c j enc b).2.1 = encVal σ enc + fkWeight h.t (2 * c + j)) := by
    unfold subE
    by_cases h16 : 2 * c + j + 1 = 16
    · simp only [h16, ↓reduceIte]
      obtain ⟨⟨en, rfl⟩, h17⟩ := hlast h16
      have hen := henc en rfl
      have h6en : σ6 en = σ en := by
        obtain ⟨k, hk, rfl⟩ := hen; rw [h65 k (by omega), hlow5 k hk]
      have h617 : σ6 (.n 17) = σ (.n 17) := by rw [h65 17 (by omega), hlow5 17 (by omega)]
      refine completes_atoms rfl (Ext.refl _ _ _) (by rw [h617]; exact h17) (fun a ha => ?_)
      simp only [addS, List.mem_singleton, Stmt.atom.injEq, Option.getD_some] at ha
      subst ha
      show σ6 (.n 17) = σ6 en + σ6 (subFk c j b).2.2.2
      rw [h617, h6en, k3, h17]
      rfl
    · simp only [h16, ↓reduceIte]
      cases enc with
      | none => exact Completes.nil' (by simp only [encVal, zero_add]; exact k3)
      | some en =>
          have hen := henc en rfl
          have h6en : σ6 en = σ en := by
            obtain ⟨k, hk, rfl⟩ := hen; rw [h65 k (by omega), hlow5 k hk]
          simp only
          refine (addS_complete σ6 (subFk c j b).2.1 (hen.mono' (by omega))
            (by rw [hfw]; exact ⟨_, by omega, rfl⟩)).mono le_rfl le_rfl (fun σ' h' => ?_)
          rw [h', h6en, k3]
          rfl
  have hnb7 : NumBelow (subE c j enc b).2.2 (Stmt.valsList (subE c j enc b).1) := by
    have hfw' : NBv (subFk c j b).2.1 (subFk c j b).2.2.2 := by rw [hfw]; exact ⟨_, by omega, rfl⟩
    unfold subE
    by_cases h16 : 2 * c + j + 1 = 16
    · simp only [h16, ↓reduceIte, addS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil]
      refine .cons ⟨17, by omega, rfl⟩ (.cons ?_ (.cons hfw' (.nil _)))
      cases enc with
      | none => exact ⟨0, by omega, rfl⟩
      | some en => exact (henc en rfl).mono' (by omega)
    · simp only [h16, ↓reduceIte]
      cases enc with
      | none => exact .nil _
      | some en =>
          simp only [addS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil]
          exact .cons ⟨_, by omega, rfl⟩ (.cons ((henc en rfl).mono' (by omega)) (.cons (hfw'.mono' (by omega))
            (.nil _)))
  refine Completes.append (m := (subE c j enc b).2.2) hE1 (by omega) hnb7 hS7 (fun σ7 he7 h7 => ?_)
  have h76 : ∀ k < (subFk c j b).2.1, σ7 (.n k) = σ6 (.n k) := fun k hk => he7.apply (Or.inl hk)
  have h75 : ∀ k < b + 12, σ7 (.n k) = σ5 (.n k) := fun k hk => by rw [h76 k (by omega), h65 k hk]
  -- the fold
  have hX7 : ForestX σ7 := hX5.congr hb fun k hk => (h75 k (by omega)).symm
  have hfl7 : IsCanonical128 (σ7 (subFk c j b).2.2.1) := by
    rw [hfl, h76 _ (by omega), ← hfl]; exact k2
  have hk7 : IsCanonical128 (σ7 (.n (b + 11))) := by rw [h75 _ (by omega)]; exact hkc
  have hfd := foldArms_complete (C := C) (rd := rd) (atV := .n (b + 11)) (adr := subAdr) (height := 3)
    (node0 := (subFk c j b).2.2.1) (markV := .n (b + 1)) (markC := subMark j)
    (wC := fun a => cbMul a (58 + 3 * (2 * c + j))) (b := (subE c j enc b).2.2) (index := h.a) (x := .n b)
    (by norm_num; omega) (by norm_num) (by omega) (fun i hi => subAdr_ok i (by norm_num at hi; omega))
    ⟨b + 11, by omega, rfl⟩ (by rw [hfl]; exact ⟨_, by omega, rfl⟩) ⟨b + 1, by omega, rfl⟩
    ⟨b, by omega, rfl⟩ h.sibs (fun l _ => hs l) σ7 (fun v hx _ => hX7.sx hk7 hfl7 v hx)
    (by rw [h75 _ (by omega)]; exact h5b1) (by rw [h75 _ (by omega)]; exact h5b)
  rw [← subFd_eq] at hfd
  refine Completes.append (m := (subFd c j enc b).2.1) hfdE (by omega)
    (by
      simp only [valsList_cons, valsList_nil, Stmt.vals, List.append_nil]
      refine .cons ⟨b, by omega, rfl⟩ ?_
      rw [subFd_eq]
      exact foldArms_numBelow (by norm_num) (by omega) (fun i hi => subAdr_ok i (by norm_num at hi; omega))
        ⟨b + 11, by omega, rfl⟩ (by rw [hfl]; exact ⟨_, by omega, rfl⟩) ⟨b + 1, by omega, rfl⟩)
    hfd (fun σ8 he8 ⟨f1, f2, f3, f4, f5⟩ => ?_)
  have h87 : ∀ k < (subE c j enc b).2.2, σ8 (.n k) = σ7 (.n k) := fun k hk => he8.apply (Or.inl hk)
  -- the bound
  have hfw8 : (subFd c j enc b).2.2.2.2 = .n (flBase (subAdr 0) 0 (3 - 1) (subE c j enc b).2.2 + 2) := by
    rw [subFd_eq, hfo3]
  obtain ⟨σ9, he9, h9, hh9⟩ := addS_complete (C := C) (rd := rd) (x := bound)
    (y := (subFd c j enc b).2.2.2.2) σ8 (subFd c j enc b).2.1
    (hbd.mono' (show b ≤ (subFd c j enc b).2.1 by omega)) (by rw [hfw8]; exact ⟨_, by omega, rfl⟩)
  refine ⟨σ9, he9, fun σ'' hag => ?_, hh9⟩
  have h98 : ∀ k < (subFd c j enc b).2.1, σ'' (.n k) = σ8 (.n k) := fun k hk => by
    rw [hag.apply ⟨k, by omega, rfl⟩, he9.apply (Or.inl hk)]
  have t5 : ∀ k < b + 12, σ'' (.n k) = σ5 (.n k) := fun k hk => by
    rw [h98 k (by omega), h87 k (by omega), h75 k hk]
  have t6 : ∀ k < (subFk c j b).2.1, σ'' (.n k) = σ6 (.n k) := fun k hk => by
    rw [h98 k (by omega), h87 k (by omega), h76 k hk]
  have t7 : ∀ k < (subE c j enc b).2.2, σ'' (.n k) = σ7 (.n k) := fun k hk => by
    rw [h98 k (by omega), h87 k hk]
  have hL0' : flBase (subAdr 0) 0 (3 - 1) (subE c j enc b).2.2 + 3 ≤ (subFd c j enc b).2.1 := hL0E
  have ho1 : (subFd c j enc b).2.2.1 = .n (flBase (subAdr 0) 0 (3 - 1) (subE c j enc b).2.2) := by
    rw [subFd_eq, hfo3]
  have ho2 : (subFd c j enc b).2.2.2.1 = .n (flBase (subAdr 0) 0 (3 - 1) (subE c j enc b).2.2 + 1) := by
    rw [subFd_eq, hfo3]
  refine ⟨by rw [t5 b (by omega)]; exact h5b, by rw [t5 _ (by omega)]; exact h5b1,
    by rw [t5 _ (by omega)]; exact h5t, fun i hi => ?_, fun l hl => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨p1, p2⟩ := fkCB_lt_end (w := 2 * c + j) (t := h.t) (keyAt := .n (b + 11)) (b := b + 12)
      (by omega) hka ht hi
    rw [← subFk_eq] at p2
    rw [t6 _ p2]
    exact k1 i hi
  · obtain ⟨p1, p2⟩ := foldPos_lt (atV := .n (b + 11)) (adr := subAdr) (height := 3)
      (node0 := (subFk c j b).2.2.1) (markV := .n (b + 1)) (markC := subMark j)
      (wC := fun a => cbMul a (58 + 3 * (2 * c + j))) (b := (subE c j enc b).2.2) (index := h.a)
      (by norm_num; omega) (show l < 3 - 1 by omega)
    rw [← subFd_eq] at p2
    rw [h98 _ (by omega)]
    exact f1 l (by omega)
  · have e : 2 ^ (3 - 1) = 2 ^ 2 := rfl
    rw [e] at f2
    by_cases h0 : h.a / 2 ^ 2 = 0 <;> simp only [h0, ↓reduceIte] at f2 ⊢
    · rw [ho2] at f2 ⊢; rw [h98 _ (by omega)]; exact f2
    · rw [ho1] at f2 ⊢; rw [h98 _ (by omega)]; exact f2
  · rw [ho1] at f3 ⊢; rw [h98 _ (by omega)]; exact f3
  · rw [ho2] at f4 ⊢; rw [h98 _ (by omega)]; exact f4
  · obtain ⟨k, ek, hk⟩ : ∃ k, (subE c j enc b).2.1 = .n k ∧ k < (subE c j enc b).2.2 := by
      unfold subE
      by_cases h16 : 2 * c + j + 1 = 16
      · simp only [h16, ↓reduceIte]; exact ⟨17, rfl, by omega⟩
      · simp only [h16, ↓reduceIte]
        cases enc with
        | none => exact ⟨_, hfw, by simp only; omega⟩
        | some en => exact ⟨_, rfl, by simp only; omega⟩
    rw [ek, t7 k hk, ← ek]
    exact h7
  · rw [hag.apply ⟨_, by omega, rfl⟩, h9]
    obtain ⟨kb, hkb, rfl⟩ := hbd
    rw [h87 kb (by omega), h75 kb (by omega), hlow5 kb hkb, f5]

end
end LeanVM.Guest.B1.Sig
