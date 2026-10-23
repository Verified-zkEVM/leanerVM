/-
  LeanVM.Guest.B1.Sig.SphincsFoldArms

  The folds' dispatch of `verify_sig_lean_sphincs` completes: arm `index`, its siblings and the
  other top loaded, on canonical cells.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsFoldComplete

/-!
# The folds' dispatch, complete

* `foLoad`: an arm's siblings, then the other top, loaded;
* `foldArm0_complete`, `foldArmN_complete`: the first arm (allocating the two tops and the weight)
  and a later one: the siblings and the other top kept, both tops canonical, the weight written,
  the mark checked;
* `foAB_*`: the arms' bases; `foldArms_complete`: the dispatch on `index`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- An arm's siblings at its levels' bases, then the other top at `other`, loaded. -/
def foLoad (adr : Nat → Sum V Nat) (height b : Nat) (other : V) (sibs : Nat → E) (σ : Val) : Val :=
  Function.update (sLoad (fun j => .n (flBase adr 0 j b)) sibs σ (height - 1)) other (sibs (height - 1))

theorem foLoad_spec {adr : Nat → Sum V Nat} {height b : Nat} {other : V} (sibs : Nat → E) (σ : Val)
    {lo hi : Nat} (hb : lo ≤ b) (hhi : flBase adr 0 (height - 1) b ≤ hi)
    (ho : ∃ k, lo ≤ k ∧ k < hi ∧ other = .n k) (hon : ∀ j < height - 1, other ≠ .n (flBase adr 0 j b)) :
    Ext lo hi σ (foLoad adr height b other sibs σ) ∧
      (∀ j < height - 1, foLoad adr height b other sibs σ (.n (flBase adr 0 j b)) = sibs j) ∧
      foLoad adr height b other sibs σ other = sibs (height - 1) := by
  have hlt : ∀ j j', j < j' → flBase adr 0 j b + 16 ≤ flBase adr 0 j' b := fun j j' h =>
    flBase_lt adr 0 j j' b h
  have hge : ∀ j, b ≤ flBase adr 0 j b := fun j => le_trans (by omega) (flBase_ge adr 0 j b)
  refine ⟨fun v hv => ?_, fun j hj => ?_, Function.update_self ..⟩
  · obtain ⟨k, hk1, hk2, rfl⟩ := ho
    unfold foLoad
    rw [Function.update_of_ne (hv k hk1 hk2)]
    refine sLoad_other _ _ σ _ fun j hj e => ?_
    have := hlt j (height - 1) hj
    exact hv _ (le_trans hb (hge j)) (by omega) e
  · unfold foLoad
    rw [Function.update_of_ne (Ne.symm (hon j hj))]
    exact sLoad_at _ sibs σ _ (fun a c h1 h2 e => by
      simp only [V.mk.injEq, true_and] at e; have := hlt a c h1; omega) j hj

theorem foldArm_split (atV : V) (adr : Nat → Sum V Nat) (height index : Nat) (node0 : V)
    (outs : V × V × V) (markV : V) (markC wC : E) (fresh : Bool) (b : Nat) :
    (foldArm atV adr height index node0 outs markV markC wC fresh b).1 =
      (foldLevels atV adr index (height - 1) 0 node0 b).1 ++
      [copyS (if index / 2 ^ (height - 1) = 0 then
            (if fresh then (V.n (foldLevels atV adr index (height - 1) 0 node0 b).2.1) else outs.1)
          else (if fresh then (V.n ((foldLevels atV adr index (height - 1) 0 node0 b).2.1 + 1)) else outs.2.1))
          (foldLevels atV adr index (height - 1) 0 node0 b).2.2,
        hintW "sp_forest_nodes" [if index / 2 ^ (height - 1) = 0 then
            (if fresh then (V.n ((foldLevels atV adr index (height - 1) 0 node0 b).2.1 + 1)) else outs.2.1)
          else (if fresh then (V.n (foldLevels atV adr index (height - 1) 0 node0 b).2.1) else outs.1)],
        .atom (.const markV markC),
        .atom (.const (if fresh then (V.n ((foldLevels atV adr index (height - 1) 0 node0 b).2.1 + 2))
          else outs.2.2) wC)] := by
  unfold foldArm
  cases fresh <;> rfl

theorem foldArm_snd (atV : V) (adr : Nat → Sum V Nat) (height index : Nat) (node0 : V)
    (outs : V × V × V) (markV : V) (markC wC : E) (fresh : Bool) (b : Nat) :
    (foldArm atV adr height index node0 outs markV markC wC fresh b).2 =
      if fresh then (foldLevels atV adr index (height - 1) 0 node0 b).2.1 + 3
      else (foldLevels atV adr index (height - 1) 0 node0 b).2.1 := rfl

variable {lo : Nat}

theorem sx2_nb {atV n0 : V} (hlo : 206 ≤ lo) (ha : NBv lo atV) (hn : NBv lo n0) {v : V}
    (hv : SX atV n0 v) : NBv lo v := by
  rcases hv with rfl | rfl | rfl | ⟨k, hk', rfl⟩ | ⟨k, hk', rfl⟩
  · exact ha
  · exact hn
  · exact ⟨2, by omega, rfl⟩
  · exact ⟨165 + k, by omega, rfl⟩
  · exact ⟨sPad + k, by simp only [sPad]; omega, rfl⟩

/-- **The first arm completes**, allocating the two tops and the weight. -/
theorem foldArm0_complete {atV : V} {adr : Nat → Sum V Nat} {height : Nat} {node0 markV : V}
    {markC wC : E} {b : Nat} (hlo : 206 ≤ b) (hh : 1 ≤ height) (hadr : AdrOK adr (height - 1)) (hat : NBv b atV)
    (hn0 : NBv b node0) (hmk : NBv b markV) (sibs : Nat → E) (hs : ∀ j < height, IsCanonical128 (sibs j))
    (σ : Val) (hX : ∀ v, SX atV node0 v → NBv b v → IsCanonical128 (σ v))
    (hmv : σ markV = markC) :
    Completes C rd b (flBase adr 0 (height - 1) b + 3)
      (foldArm atV adr height 0 node0 (.n 0, .n 0, .n 0) markV markC wC true b).1 σ
      (fun σ' => (∀ j < height - 1, σ' (.n (flBase adr 0 j b)) = sibs j) ∧
        σ' (.n (flBase adr 0 (height - 1) b + 1)) = sibs (height - 1) ∧
        IsCanonical128 (σ' (.n (flBase adr 0 (height - 1) b))) ∧
        σ' (.n (flBase adr 0 (height - 1) b + 2)) = wC) := by
  obtain ⟨k1, k2, k3⟩ := foldLevels_kseq (lo := b) (a2 := node0) (index := 0) hlo hadr hat (height - 1) 0
    node0 b (by omega) le_rfl (sx_a2 hn0)
  set L := flBase adr 0 (height - 1) b with hL
  have hbL : b ≤ L := le_trans (by omega) (flBase_ge adr 0 (height - 1) b)
  have hks : KSeq b (SX atV node0) b ((foldLevels atV adr 0 (height - 1) 0 node0 b).1 ++
      [copyS (.n L) (foldLevels atV adr 0 (height - 1) 0 node0 b).2.2,
        hintW "sp_forest_nodes" [.n (L + 1)]]) (L + 2) :=
    KSeq.append k1 ⟨L + 1, ⟨rfl, k3, rfl⟩, L + 2, ⟨by simp [runV], by omega⟩, rfl⟩
  obtain ⟨hext, hval, hoth⟩ := foLoad_spec (adr := adr) (height := height) (b := b) (other := .n (L + 1)) sibs σ
    (lo := b) (hi := L + 2) le_rfl (by omega) ⟨L + 1, by omega, by omega, rfl⟩ (fun j hj e => by
      simp only [V.mk.injEq, true_and] at e
      have := flBase_lt adr 0 j (height - 1) b hj
      omega)
  have hsplit : (foldArm atV adr height 0 node0 (.n 0, .n 0, .n 0) markV markC wC true b).1 =
      ((foldLevels atV adr 0 (height - 1) 0 node0 b).1 ++
        [copyS (.n L) (foldLevels atV adr 0 (height - 1) 0 node0 b).2.2,
          hintW "sp_forest_nodes" [.n (L + 1)]]) ++ ([.atom (.const markV markC)] ++ [cst (L + 2) wC]) := by
    rw [foldArm_split, k2]
    simp [cst]
  rw [hsplit]
  refine Completes.reload (hext.mono le_rfl (by omega)) ?_
  refine Completes.append (m := L + 2) (by omega) (by omega) (KSeq.numBelow le_rfl hks)
    (kseq_completes (C := C) (rd := rd) hks _ (fun v hx hn => ?_) (fun s vs hm v hv => ?_))
    (fun σ1 he1 ⟨ha1, hc1, hk1⟩ => ?_)
  · obtain ⟨j, hj, rfl⟩ := hn
    rw [hext.apply (Or.inl hj)]
    exact hX _ hx ⟨j, hj, rfl⟩
  · rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨j, hj, rfl⟩ := foldLevels_hints _ _ _ _ s vs hm
      simp only [List.mem_singleton] at hv
      subst hv
      rw [hval j hj]
      exact hs j (by omega)
    · simp only [copyS, hintW, List.mem_cons, Stmt.atom.injEq, reduceCtorEq, Atom.hint.injEq,
        Hint.witness.injEq, Dest.stack.injEq, false_or, List.not_mem_nil, or_false] at hm
      obtain ⟨-, rfl⟩ := hm
      simp only [List.mem_singleton] at hv
      subst hv
      rw [hoth]
      exact hs _ (by omega)
  · have hag1 : AgreeBelow b (foLoad adr height b (.n (L + 1)) sibs σ) σ1 := he1.agree
    obtain ⟨km, hkm, rfl⟩ := hmk
    have hmv1 : σ1 (.n km) = markC := by rw [← hag1 km hkm, hext.apply (Or.inl hkm)]; exact hmv
    have hq : (∀ j < height - 1, σ1 (.n (flBase adr 0 j b)) = sibs j) ∧
        σ1 (.n (L + 1)) = sibs (height - 1) ∧ IsCanonical128 (σ1 (.n L)) := by
      refine ⟨fun j hj => ?_, ?_, hc1 L hbL (by omega)⟩
      · rw [hk1 _ _ (List.mem_append_left _ (foldLevels_hint_mem (height - 1) 0 node0 b j hj)) _
          (List.mem_singleton_self _), hval j hj]
      · rw [hk1 "sp_forest_nodes" [.n (L + 1)] (List.mem_append_right _ (by simp [hintW])) _
          (List.mem_singleton_self _), hoth]
    refine Completes.checks (xs := [.atom (.const (.n km) markC)]) rfl (fun a ha => by
        simp only [List.mem_singleton, Stmt.atom.injEq] at ha; subst ha; exact hmv1)
      (by simp only [valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil]
          exact .cons ⟨km, by omega, rfl⟩ (.nil _)) (by omega)
      (((cst_complete (C := C) (rd := rd) σ1 (L + 2) wC).keep
        (Q := fun σ => (∀ j < height - 1, σ (.n (flBase adr 0 j b)) = sibs j) ∧
          σ (.n (L + 1)) = sibs (height - 1) ∧ IsCanonical128 (σ (.n L)))
        (Q' := fun σ => (∀ j < height - 1, σ (.n (flBase adr 0 j b)) = sibs j) ∧
          σ (.n (L + 1)) = sibs (height - 1) ∧ IsCanonical128 (σ (.n L))) hq
        (fun σ' he h => ⟨fun j hj => by
          have := flBase_lt adr 0 j (height - 1) b hj
          rw [he.apply (Or.inl (by omega))]; exact h.1 j hj,
          by rw [he.apply (Or.inl (by omega))]; exact h.2.1,
          by rw [he.apply (Or.inl (by omega))]; exact h.2.2⟩)).mono le_rfl le_rfl
        (fun σ2 ⟨h2, q1, q2, q3⟩ => ⟨q1, q2, q3, h2⟩))

/-- A later arm, its copy into `d` and its hint into `o`, the two tops `L0`, `L0 + 1`. -/
theorem foldArmN_aux {atV : V} {adr : Nat → Sum V Nat} {height index : Nat} {node0 markV : V}
    {markC wC : E} {bI hi L0 d o : Nat} (hlo : 206 ≤ lo) (hb : lo ≤ bI) (hadr : AdrOK adr (height - 1))
    (hat : NBv lo atV) (hn0 : NBv lo node0) (hmk : NBv lo markV) (hL0 : lo ≤ L0 ∧ L0 + 3 ≤ bI)
    (hdo : (d = L0 ∧ o = L0 + 1) ∨ (d = L0 + 1 ∧ o = L0))
    (hhi : flBase adr 0 (height - 1) bI ≤ hi) (sibs : Nat → E) (hs : ∀ j < height, IsCanonical128 (sibs j))
    (hh : 1 ≤ height) (σ : Val) (hX : ∀ v, SX atV node0 v → NBv lo v → IsCanonical128 (σ v))
    (hmv : σ markV = markC) :
    Completes C rd lo hi ((foldLevels atV adr index (height - 1) 0 node0 bI).1 ++
      [copyS (.n d) (foldLevels atV adr index (height - 1) 0 node0 bI).2.2, hintW "sp_forest_nodes" [.n o],
        .atom (.const markV markC), .atom (.const (.n (L0 + 2)) wC)]) σ
      (fun σ' => (∀ j < height - 1, σ' (.n (flBase adr 0 j bI)) = sibs j) ∧ σ' (.n o) = sibs (height - 1) ∧
        IsCanonical128 (σ' (.n L0)) ∧ IsCanonical128 (σ' (.n (L0 + 1))) ∧ σ' (.n (L0 + 2)) = wC) := by
  have hd : lo ≤ d ∧ d + 2 ≤ bI := by omega
  have ho : lo ≤ o ∧ o + 2 ≤ bI := by omega
  have hn0b : NBv bI node0 := hn0.mono' hb
  have hatb : NBv bI atV := hat.mono' hb
  obtain ⟨k1, k2, k3⟩ := foldLevels_kseq (lo := bI) (a2 := node0) (index := index) (by omega) hadr hatb
    (height - 1) 0 node0 bI (by omega) le_rfl (sx_a2 hn0b)
  set L := flBase adr 0 (height - 1) bI with hL
  have hbL : bI ≤ L := le_trans (by omega) (flBase_ge adr 0 (height - 1) bI)
  obtain ⟨hext, hval, hoth⟩ := foLoad_spec (adr := adr) (height := height) (b := bI) (other := .n o) sibs σ
    (lo := lo) (hi := hi) hb hhi ⟨o, ho.1, by omega, rfl⟩ (fun j hj e => by
      simp only [V.mk.injEq, true_and] at e
      have := flBase_ge adr 0 j bI
      omega)
  set σr := foLoad adr height bI (.n o) sibs σ with hσr
  have hXr : ∀ v, SX atV node0 v → NBv lo v → IsCanonical128 (σr v) := by
    rintro v hx ⟨j, hj, rfl⟩
    rw [hext.apply (Or.inl hj)]
    exact hX _ hx ⟨j, hj, rfl⟩
  obtain ⟨σ1, he1, ha1, hc1, hk1⟩ := kseq_complete (rd := rd) (lo := bI) le_rfl k1 σr
    (fun v hx hn => by
      obtain ⟨j, hj, rfl⟩ := sx2_nb (lo := lo) hlo hat hn0 hx
      exact hXr _ hx ⟨j, hj, rfl⟩)
    (fun j h1 h2 => by omega)
    (fun s vs hm v hv => by
      obtain ⟨j, hj, rfl⟩ := foldLevels_hints _ _ _ _ s vs hm
      simp only [List.mem_singleton] at hv
      subst hv
      rw [hval j hj]
      exact hs j (by omega))
  -- the node reached
  have hnode : ∀ k, k = d ∨ k = L0 + 2 → (foldLevels atV adr index (height - 1) 0 node0 bI).2.2 ≠ .n k := by
    intro k hk e
    rcases k3 with ⟨j, h1, h2, e'⟩ | ⟨hx, j, hj, e'⟩
    · rw [e] at e'; simp only [V.mk.injEq, true_and] at e'; omega
    · rw [e] at e'; simp only [V.mk.injEq, true_and] at e'
      obtain ⟨j', hj', e''⟩ := sx2_nb (lo := lo) hlo hat hn0 hx
      rw [e] at e''; simp only [V.mk.injEq, true_and] at e''; omega
  have hnc : IsCanonical128 (σ1 (foldLevels atV adr index (height - 1) 0 node0 bI).2.2) := by
    rcases k3 with ⟨j, h1, h2, e'⟩ | ⟨hx, hn⟩
    · rw [e']; exact hc1 j h1 h2
    · have := hXr _ hx (sx2_nb (lo := lo) hlo hat hn0 hx)
      obtain ⟨j, hj, e'⟩ := sx2_nb (lo := lo) hlo hat hn0 hx
      rw [e', ← he1.agree j (by omega), ← e']
      exact this
  set nd := (foldLevels atV adr index (height - 1) 0 node0 bI).2.2 with hnd
  set σ2 := Function.update (Function.update σ1 (.n d) (σ1 nd)) (.n (L0 + 2)) wC with hσ2
  have he2 : ∀ k, k ≠ d → k ≠ L0 + 2 → σ2 (.n k) = σ1 (.n k) := fun k h1 h2 => by
    rw [hσ2, Function.update_of_ne (by simp; omega), Function.update_of_ne (by simp; omega)]
  have hd2 : σ2 (.n d) = σ1 nd := by
    rw [hσ2, Function.update_of_ne (by simp; omega), Function.update_self]
  have hw2 : σ2 (.n (L0 + 2)) = wC := by rw [hσ2, Function.update_self]
  have hext2 : Ext lo hi σ σ2 := by
    refine (hext.comp (he1.mono hb (by omega))).comp fun v hv => ?_
    rw [hσ2, Function.update_of_ne (hv (L0 + 2) (by omega) (by omega)),
      Function.update_of_ne (hv d hd.1 (by omega))]
  have ho1 : σ1 (.n o) = sibs (height - 1) := by
    rw [← he1.agree o (by omega), hoth]
  have hmv2 : σ2 markV = markC := by
    obtain ⟨k, hk, rfl⟩ := hmk
    rw [he2 k (by omega) (by omega), ← he1.agree k (by omega), hext.apply (Or.inl hk)]
    exact hmv
  refine completes_atoms (by rw [atomsOnly_append, k1.atoms]; rfl) hext2
    ⟨fun j hj => ?_, ?_, ?_, ?_, hw2⟩ (fun a ha => ?_)
  · have := flBase_ge adr 0 j bI
    rw [he2 _ (by omega) (by omega), hk1 _ _ (foldLevels_hint_mem (height - 1) 0 node0 bI j hj) _
      (List.mem_singleton_self _), hval j hj]
  · rw [he2 _ (by omega) (by omega), ho1]
  · rcases hdo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hd2]; exact hnc
    · rw [he2 _ (by omega) (by omega), ho1]; exact hs _ (by omega)
  · rcases hdo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [he2 _ (by omega) (by omega), ho1]; exact hs _ (by omega)
    · rw [hd2]; exact hnc
  · rcases List.mem_append.mp ha with ha | ha
    · refine (atom_congr a fun v hv => ?_).mp (ha1 a ha)
      rcases KSeq.vals_rd le_rfl k1 v (mem_valsList_of_mem ha hv) with ⟨k, h1, h2, rfl⟩ | ⟨hx, -⟩
      · exact (he2 k (by omega) (by omega)).symm
      · obtain ⟨k, hk', rfl⟩ := sx2_nb (lo := lo) hlo hat hn0 hx
        exact (he2 k (by omega) (by omega)).symm
    · simp only [copyS, hintW, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
      rcases ha with rfl | rfl | rfl | rfl
      · show σ2 (.n d) = σ2 nd
        rw [hd2]
        rcases k3 with ⟨j, h1, h2, e'⟩ | ⟨hx, hn⟩
        · rw [e', he2 j (by omega) (by omega), ← e']
        · obtain ⟨j, hj, e'⟩ := sx2_nb (lo := lo) hlo hat hn0 hx
          rw [e', he2 j (by omega) (by omega), ← e']
      · trivial
      · exact hmv2
      · exact hw2

/-- **A later arm completes**, writing into the first arm's tops and weight. -/
theorem foldArmN_complete {atV : V} {adr : Nat → Sum V Nat} {height index : Nat} {node0 markV : V}
    {markC wC : E} {bI hi L0 : Nat} (hlo : 206 ≤ lo) (hb : lo ≤ bI) (hadr : AdrOK adr (height - 1))
    (hat : NBv lo atV) (hn0 : NBv lo node0) (hmk : NBv lo markV) (hL0 : lo ≤ L0 ∧ L0 + 3 ≤ bI)
    (hhi : flBase adr 0 (height - 1) bI ≤ hi) (sibs : Nat → E) (hs : ∀ j < height, IsCanonical128 (sibs j))
    (hh : 1 ≤ height) (σ : Val) (hX : ∀ v, SX atV node0 v → NBv lo v → IsCanonical128 (σ v))
    (hmv : σ markV = markC) :
    Completes C rd lo hi (foldArm atV adr height index node0 (.n L0, .n (L0 + 1), .n (L0 + 2)) markV markC wC
      false bI).1 σ
      (fun σ' => (∀ j < height - 1, σ' (.n (flBase adr 0 j bI)) = sibs j) ∧
        σ' (if index / 2 ^ (height - 1) = 0 then .n (L0 + 1) else .n L0) = sibs (height - 1) ∧
        IsCanonical128 (σ' (.n L0)) ∧ IsCanonical128 (σ' (.n (L0 + 1))) ∧ σ' (.n (L0 + 2)) = wC) := by
  rw [foldArm_split]
  by_cases h0 : index / 2 ^ (height - 1) = 0
  · simp only [h0, ↓reduceIte, Bool.false_eq_true]
    exact foldArmN_aux hlo hb hadr hat hn0 hmk hL0 (Or.inl ⟨rfl, rfl⟩) hhi sibs hs hh σ hX hmv
  · simp only [h0, ↓reduceIte, Bool.false_eq_true]
    exact foldArmN_aux hlo hb hadr hat hn0 hmk hL0 (Or.inr ⟨rfl, rfl⟩) hhi sibs hs hh σ hX hmv

/-! ## The arms' bases -/

theorem foldLevels_snd (atV : V) (adr : Nat → Sum V Nat) (index : Nat) :
    ∀ (m l : Nat) (cur : V) (b : Nat), (foldLevels atV adr index m l cur b).2.1 = flBase adr l m b
  | 0, _, _, _ => rfl
  | m + 1, l, cur, b => by
      simp only [foldLevels]
      rw [foldLevels_snd atV adr index m (l + 1), foldLevel_snd]
      rfl

theorem foldArmsRest_snd_succ (atV : V) (adr : Nat → Nat → Sum V Nat) (height : Nat) (node0 : V)
    (outs : V × V × V) (markV : V) (markC wC : Nat → E) : ∀ (m index b : Nat),
    (foldArmsRest atV adr height node0 outs markV markC wC (m + 1) index b).2 =
      (foldArm atV (adr (index + m)) height (index + m) node0 outs markV (markC (index + m)) (wC (index + m))
        false (foldArmsRest atV adr height node0 outs markV markC wC m index b).2).2
  | 0, index, b => by simp [foldArmsRest]
  | m + 1, index, b => by
      have := foldArmsRest_snd_succ atV adr height node0 outs markV markC wC m (index + 1)
        (foldArm atV (adr index) height index node0 outs markV (markC index) (wC index) false b).2
      simp only [foldArmsRest] at this ⊢
      rw [this, show index + 1 + m = index + (m + 1) by omega]

variable {atV : V} {adr : Nat → Nat → Sum V Nat} {height : Nat} {node0 markV : V} {markC wC : Nat → E}

theorem foAB_one (b : Nat) : foAB atV adr height node0 markV markC wC b 1 =
    (foldArm atV (adr 0) height 0 node0 (.n 0, .n 0, .n 0) markV (markC 0) (wC 0) true b).2 := rfl

theorem foAB_succ {b t : Nat} (ht : 1 ≤ t) :
    foAB atV adr height node0 markV markC wC b (t + 1) =
      (foldArm atV (adr t) height t node0 (foldArms atV adr height node0 markV markC wC b).2.2 markV (markC t)
        (wC t) false (foAB atV adr height node0 markV markC wC b t)).2 := by
  unfold foAB
  simp only [Nat.add_one_ne_zero, ↓reduceIte, show t ≠ 0 by omega, Nat.add_sub_cancel]
  rw [show t = t - 1 + 1 by omega, foldArmsRest_snd_succ, show 1 + (t - 1) = t - 1 + 1 by omega,
    Nat.add_sub_cancel]

theorem foldArms_end (b : Nat) : (foldArms atV adr height node0 markV markC wC b).2.1 =
    foAB atV adr height node0 markV markC wC b (2 ^ height) := by
  have : 2 ^ height ≠ 0 := by positivity
  unfold foAB foldArms
  simp only [this, ↓reduceIte]

theorem foldArms_outs (b : Nat) : (foldArms atV adr height node0 markV markC wC b).2.2 =
    (.n (flBase (adr 0) 0 (height - 1) b), .n (flBase (adr 0) 0 (height - 1) b + 1),
      .n (flBase (adr 0) 0 (height - 1) b + 2)) := by
  simp only [foldArms, foldArm_snd, ↓reduceIte, foldLevels_snd]
  congr 2

theorem foldArms_getN {b t : Nat} (ht : 1 ≤ t) (ht' : t < 2 ^ height) :
    (foldArms atV adr height node0 markV markC wC b).1[t]'(by rw [foldArms_length]; exact ht') =
      (foldArm atV (adr t) height t node0 (foldArms atV adr height node0 markV markC wC b).2.2 markV (markC t)
        (wC t) false (foAB atV adr height node0 markV markC wC b t)).1 := by
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  have := foldArmsRest_getElem atV adr height node0 (foldArms atV adr height node0 markV markC wC b).2.2 markV
    markC wC (2 ^ height - 1) 1
    (foldArm atV (adr 0) height 0 node0 (.n 0, .n 0, .n 0) markV (markC 0) (wC 0) true b).2 t'
    (by rw [foldArmsRest_length]; omega)
  rw [show 1 + t' = t' + 1 by omega] at this
  exact this

theorem foAB_mono {b : Nat} : ∀ t, b ≤ foAB atV adr height node0 markV markC wC b t ∧
    ∀ t', t ≤ t' → foAB atV adr height node0 markV markC wC b t ≤ foAB atV adr height node0 markV markC wC b t' := by
  have step : ∀ t, foAB atV adr height node0 markV markC wC b t ≤ foAB atV adr height node0 markV markC wC b (t + 1) := by
    intro t
    rcases Nat.eq_zero_or_pos t with rfl | hpos
    · rw [foAB_one, foldArm_snd, foldLevels_snd]
      simp only [↓reduceIte]
      have := flBase_ge (adr 0) 0 (height - 1) b
      unfold foAB; simp only [↓reduceIte]
      omega
    · rw [foAB_succ hpos, foldArm_snd, foldLevels_snd]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have := flBase_ge (adr t) 0 (height - 1) (foAB atV adr height node0 markV markC wC b t)
      omega
  have hge : ∀ t, b ≤ foAB atV adr height node0 markV markC wC b t := by
    intro t
    induction t with
    | zero => unfold foAB; simp
    | succ t ih => exact le_trans ih (step t)
  refine fun t => ⟨hge t, fun t' htt' => ?_⟩
  induction t' with
  | zero => have : t = 0 := by omega
            subst this; exact le_rfl
  | succ t' ih =>
      rcases Nat.lt_or_ge t (t' + 1) with h | h
      · exact le_trans (ih (by omega)) (step t')
      · have : t = t' + 1 := by omega
        subst this; exact le_rfl

/-- **The folds' dispatch completes** on `index`, its siblings and the other top loaded. -/
theorem foldArms_complete {b index : Nat} {x : V} (hidx : index < 2 ^ height) (hh : 1 ≤ height)
    (hlo : 206 ≤ b) (hadr : ∀ i < 2 ^ height, AdrOK (adr i) (height - 1)) (hat : NBv b atV) (hn0 : NBv b node0) (hmk : NBv b markV)
    (hx : NBv b x) (sibs : Nat → E) (hs : ∀ j < height, IsCanonical128 (sibs j)) (σ : Val)
    (hX : ∀ v, SX atV node0 v → NBv b v → IsCanonical128 (σ v)) (hmv : σ markV = markC index)
    (hxv : σ x = ofK (gpow index)) :
    Completes C rd b (foldArms atV adr height node0 markV markC wC b).2.1
      [.match_ x (foldArms atV adr height node0 markV markC wC b).1] σ
      (fun σ' => (∀ j < height - 1, σ' (.n (flBase (adr index) 0 j
          (foAB atV adr height node0 markV markC wC b index))) = sibs j) ∧
        σ' (if index / 2 ^ (height - 1) = 0 then (foldArms atV adr height node0 markV markC wC b).2.2.2.1
          else (foldArms atV adr height node0 markV markC wC b).2.2.1) = sibs (height - 1) ∧
        IsCanonical128 (σ' (foldArms atV adr height node0 markV markC wC b).2.2.1) ∧
        IsCanonical128 (σ' (foldArms atV adr height node0 markV markC wC b).2.2.2.1) ∧
        σ' (foldArms atV adr height node0 markV markC wC b).2.2.2.2 = wC index) := by
  have hm := foAB_mono (atV := atV) (adr := adr) (height := height) (node0 := node0) (markV := markV)
    (markC := markC) (wC := wC) (b := b)
  have ho := foldArms_outs (atV := atV) (adr := adr) (height := height) (node0 := node0) (markV := markV)
    (markC := markC) (wC := wC) b
  set L0 := flBase (adr 0) 0 (height - 1) b with hL0
  have hbL : b ≤ L0 := le_trans (by omega) (flBase_ge (adr 0) 0 (height - 1) b)
  have h1 : foAB atV adr height node0 markV markC wC b 1 = L0 + 3 := by
    rw [foAB_one, foldArm_snd, foldLevels_snd]; rfl
  have hp2 : 2 ≤ 2 ^ height := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hh)
  have hend1 : foAB atV adr height node0 markV markC wC b 1 ≤ (foldArms atV adr height node0 markV markC wC b).2.1 := by
    rw [foldArms_end b]; exact (hm 1).2 _ (by omega)
  refine match_complete (by rw [foldArms_length]; exact hidx) hx hxv ?_
  rw [ho]
  simp only
  rcases Nat.eq_zero_or_pos index with rfl | hpos
  · refine (foldArm0_complete (C := C) (rd := rd) (atV := atV) (adr := adr 0) (height := height) (node0 := node0)
      (markV := markV) (markC := markC 0) (wC := wC 0) hlo hh (hadr 0 (by omega)) hat hn0 hmk sibs hs σ hX hmv).mono le_rfl
      (by omega) (fun σ' ⟨p1, p2, p3, p4⟩ => ⟨fun j hj => ?_, by simpa using p2, p3, by rw [p2]; exact hs _ (by omega), p4⟩)
    have : foAB atV adr height node0 markV markC wC b 0 = b := by unfold foAB; simp
    rw [this]; exact p1 j hj
  · rw [foldArms_getN hpos hidx, ho]
    have hbt := (hm 1).2 index hpos
    have hnext := foAB_succ (atV := atV) (adr := adr) (height := height) (node0 := node0) (markV := markV)
      (markC := markC) (wC := wC) (b := b) hpos
    rw [foldArm_snd, foldLevels_snd] at hnext
    simp only [Bool.false_eq_true, ↓reduceIte] at hnext
    have hend : foAB atV adr height node0 markV markC wC b (index + 1) ≤ (foldArms atV adr height node0 markV markC wC b).2.1 := by
      rw [foldArms_end b]; exact (hm (index + 1)).2 _ (by omega)
    refine (foldArmN_complete (C := C) (rd := rd) (lo := b) (L0 := L0) hlo (hm index).1 (hadr index hidx) hat hn0 hmk
      ⟨hbL, by omega⟩ (by omega) sibs hs hh σ hX hmv).mono le_rfl le_rfl
      (fun σ' ⟨p1, p2, p3, p4, p5⟩ => ⟨p1, ?_, p3, p4, p5⟩)
    by_cases h0 : index / 2 ^ (height - 1) = 0 <;> simp only [h0, ↓reduceIte] at p2 ⊢ <;> exact p2

/-- **The folds' values lie below their end.** -/
theorem foldArms_numBelow {b : Nat} (hh : 1 ≤ height) (hlo : 206 ≤ b) (hadr : ∀ i < 2 ^ height, AdrOK (adr i) (height - 1))
    (hat : NBv b atV) (hn0 : NBv b node0) (hmk : NBv b markV) :
    NumBelow (foldArms atV adr height node0 markV markC wC b).2.1
      (Stmt.valsArms (foldArms atV adr height node0 markV markC wC b).1) := by
  have hm := foAB_mono (atV := atV) (adr := adr) (height := height) (node0 := node0) (markV := markV)
    (markC := markC) (wC := wC) (b := b)
  have ho := foldArms_outs (atV := atV) (adr := adr) (height := height) (node0 := node0) (markV := markV)
    (markC := markC) (wC := wC) b
  set L0 := flBase (adr 0) 0 (height - 1) b with hL0
  have hbL : b ≤ L0 := le_trans (by omega) (flBase_ge (adr 0) 0 (height - 1) b)
  have h1 : foAB atV adr height node0 markV markC wC b 1 = L0 + 3 := by
    rw [foAB_one, foldArm_snd, foldLevels_snd]; rfl
  have hp2 : 2 ≤ 2 ^ height := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hh)
  have hend1 : foAB atV adr height node0 markV markC wC b 1 ≤ (foldArms atV adr height node0 markV markC wC b).2.1 := by
    rw [foldArms_end b]; exact (hm 1).2 _ (by omega)
  have key : ∀ (i bI Bd : Nat), i < 2 ^ height → b ≤ bI → flBase (adr i) 0 (height - 1) bI ≤ Bd → ∀ (d o e : Nat),
      d < Bd → o < Bd → e < Bd →
      ∀ (mc w : E), NumBelow Bd
        (Stmt.valsList ((foldLevels atV (adr i) i (height - 1) 0 node0 bI).1 ++
          [copyS (.n d) (foldLevels atV (adr i) i (height - 1) 0 node0 bI).2.2, hintW "sp_forest_nodes" [.n o],
            .atom (.const markV mc), .atom (.const (.n e) w)])) := by
    intro i bI Bd hi hbI hBd d o e hd ho he mc w
    have hgeI := flBase_ge (adr i) 0 (height - 1) bI
    obtain ⟨k1, k2, k3⟩ := foldLevels_kseq (lo := bI) (a2 := node0) (index := i) (by omega) (hadr i hi)
      (hat.mono' hbI) (height - 1) 0 node0 bI (by omega) le_rfl (sx_a2 (hn0.mono' hbI))
    have hnd := k3.nb (show bI ≤ flBase (adr i) 0 (height - 1) bI by omega)
    rw [valsList_append]
    refine ((KSeq.numBelow le_rfl k1).mono hBd).append ?_
    simp only [copyS, hintW, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, Hint.vals, Dest.vals,
      List.append_nil, List.cons_append, List.nil_append]
    exact .cons ⟨d, hd, rfl⟩ (.cons (hnd.mono' hBd) (.cons ⟨o, ho, rfl⟩
      (.cons (hmk.mono' (by omega)) (.cons ⟨e, he, rfl⟩ (.nil _)))))
  refine numBelow_valsArms _ fun a ha => ?_
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem ha
  rw [foldArms_length] at ht
  rcases Nat.eq_zero_or_pos t with rfl | hpos
  · have e : (foldArms atV adr height node0 markV markC wC b).1[0]'(by rw [foldArms_length]; omega) =
        (foldArm atV (adr 0) height 0 node0 (.n 0, .n 0, .n 0) markV (markC 0) (wC 0) true b).1 := rfl
    rw [e, foldArm_split, foldLevels_snd]
    simp only [Nat.zero_div, ↓reduceIte]
    exact (key 0 b (L0 + 3) (by omega) le_rfl (by omega) L0 (L0 + 1) (L0 + 2) (by omega) (by omega) (by omega) _ _).mono
      (by omega)
  · rw [foldArms_getN hpos ht, ho, foldArm_split]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hbt := (hm t).1
    have hb1 := (hm 1).2 t hpos
    have hnext := foAB_succ (atV := atV) (adr := adr) (height := height) (node0 := node0) (markV := markV)
      (markC := markC) (wC := wC) (b := b) hpos
    rw [foldArm_snd, foldLevels_snd] at hnext
    simp only [Bool.false_eq_true, ↓reduceIte] at hnext
    have hend : foAB atV adr height node0 markV markC wC b (t + 1) ≤
        (foldArms atV adr height node0 markV markC wC b).2.1 := by
      rw [foldArms_end b]; exact (hm (t + 1)).2 _ (by omega)
    have hge := flBase_ge (adr t) 0 (height - 1) (foAB atV adr height node0 markV markC wC b t)
    by_cases h0 : t / 2 ^ (height - 1) = 0 <;> simp only [h0, ↓reduceIte] <;>
      exact (key t _ _ ht hbt le_rfl _ _ _ (by omega) (by omega) (by omega) _ _).mono (by omega)

/-- **Arm `index`'s levels lie below the dispatch's end.** -/
theorem foldPos_lt {b index : Nat} (hidx : index < 2 ^ height) {l : Nat} (hl : l < height - 1) :
    b ≤ flBase (adr index) 0 l (foAB atV adr height node0 markV markC wC b index) ∧
      flBase (adr index) 0 l (foAB atV adr height node0 markV markC wC b index) + 16 ≤
        (foldArms atV adr height node0 markV markC wC b).2.1 := by
  have hm := foAB_mono (atV := atV) (adr := adr) (height := height) (node0 := node0) (markV := markV)
    (markC := markC) (wC := wC) (b := b)
  have h1 := flBase_lt (adr index) 0 l (height - 1) (foAB atV adr height node0 markV markC wC b index) hl
  have h2 := flBase_ge (adr index) 0 l (foAB atV adr height node0 markV markC wC b index)
  have hbt := (hm index).1
  have hnext : flBase (adr index) 0 (height - 1) (foAB atV adr height node0 markV markC wC b index) ≤
      foAB atV adr height node0 markV markC wC b (index + 1) := by
    rcases Nat.eq_zero_or_pos index with rfl | hpos
    · rw [foAB_one, foldArm_snd, foldLevels_snd]
      simp only [↓reduceIte]
      have : foAB atV adr height node0 markV markC wC b 0 = b := by unfold foAB; simp
      rw [this]
      omega
    · rw [foAB_succ hpos, foldArm_snd, foldLevels_snd]
      simp only [Bool.false_eq_true, ↓reduceIte, le_refl]
  have hend : foAB atV adr height node0 markV markC wC b (index + 1) ≤ (foldArms atV adr height node0 markV markC wC b).2.1 := by
    rw [foldArms_end b]; exact (hm (index + 1)).2 _ (by omega)
  exact ⟨by omega, by omega⟩

end
end LeanVM.Guest.B1.Sig
