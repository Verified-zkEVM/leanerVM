/-
  LeanVM.Guest.B1.Sig.SphincsForsComplete

  The FORS trees of `verify_sig_lean_sphincs` (`sp_fors_tree`, `lean_ethereum.py:3795-3814` at
  leanVM `9d8bce81`) are complete: each tree's secret hinted, its leaf hashed and climbed up the
  hinted ordered children to its two top nodes, the FORS key.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsFieldsComplete

/-!
# FORS, complete

* `pairLevel_complete`, `pairLevel_numBelow`: a level of a path whose children are hinted under any
  name (`merkle_level_complete` hints `siblings`, a FORS level `sp_fors_nodes`);
* `pFold`, `nIter`: a path folded from the bottom, as `foldPath` folds it, and level by level;
* `fLeafAdr`, `fNodeAdr`, `fNode`, `fTops`: tree `c`'s addresses, nodes and two top nodes over
  cells, at the index `I` and the leaf `s`, its siblings `sib`;
* `sForsLevels_complete`, `sForsTree_complete`, `sForsTrees_complete`: the levels, a tree, the 24
  trees, each tree's top nodes `fTops`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat kToNat)

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- **One level of a path completes**, its children hinted (under the name `s`) in the order of its
bit: `merkle_level_complete` for any hint name. -/
theorem pairLevel_complete (s : String) {pad : Nat} {pp bit cur : V} {b c w : Nat} {nodeL : List Stmt} (σ : Val)
    (hp : PadOK σ pad) (hpb : pad + 5 ≤ b) (hpp : NBv b pp) (hbit : NBv b bit) (hcur : NBv b cur)
    (hseq : SeqOK (b + 4) ([cst (b + 4) (word w 0 0)] ++ nodeL) c) (hcb : b + 5 ≤ c)
    {Aval : E} (hA : ∀ σ', AgreeBelow b σ σ' → AtomsHold rd σ' ([cst (b + 4) (word w 0 0)] ++ nodeL) →
      σ' (.n (c - 1)) = Aval) (hAc : IsCanonical128 Aval) {bt : Bool}
    (hbv : σ bit = if bt then 1 else 0) {sib : E} (hsc : IsCanonical128 sib)
    (hcc : IsCanonical128 (σ cur)) (hppc : IsCanonical128 (σ pp))
    (hh : σ (.n b) = (mPair bt (σ cur) sib).1 ∧ σ (.n (b + 1)) = (mPair bt (σ cur) sib).2) :
    Completes C rd b (c + 14)
      ([hintW s [.n b, .n (b + 1)], addS (.n (b + 2)) cur (.n b),
          addS (.n (b + 3)) (.n b) (.n (b + 1)), mulS (.n (b + 2)) bit (.n (b + 3)), cst (b + 4) (word w 0 0)] ++
        nodeL ++ k64 pad pp (.n (c - 1)) (.n b) (.n (b + 1)) c (c + 1)) σ
      (fun σ' => σ' (.n (c + 1)) = (hcell [σ pp, Aval, (mPair bt (σ cur) sib).1,
        (mPair bt (σ cur) sib).2]).1 ∧ IsCanonical128 (σ' (.n (c + 1))) ∧ σ' (.n b) = σ (.n b) ∧
        σ' (.n (b + 1)) = σ (.n (b + 1))) := by
  have hle := hseq.le
  have hsplit : [hintW s [.n b, .n (b + 1)], addS (.n (b + 2)) cur (.n b),
      addS (.n (b + 3)) (.n b) (.n (b + 1)), mulS (.n (b + 2)) bit (.n (b + 3)), cst (b + 4) (word w 0 0)] ++
      nodeL ++ k64 pad pp (.n (c - 1)) (.n b) (.n (b + 1)) c (c + 1) =
      [hintW s [.n b, .n (b + 1)]] ++ ([addS (.n (b + 2)) cur (.n b),
        addS (.n (b + 3)) (.n b) (.n (b + 1))] ++ ([mulS (.n (b + 2)) bit (.n (b + 3))] ++
        (([cst (b + 4) (word w 0 0)] ++ nodeL) ++ k64 pad pp (.n (c - 1)) (.n b) (.n (b + 1)) c (c + 1)))) := by
    simp
  rw [hsplit]
  have hs2 : SeqOK (b + 2) [addS (.n (b + 2)) cur (.n b), addS (.n (b + 3)) (.n b) (.n (b + 1))] (b + 4) :=
    ⟨⟨rfl, hcur.mono' (by omega), ⟨b, by omega, rfl⟩⟩, ⟨rfl, ⟨b, by omega, rfl⟩, ⟨b + 1, by omega, rfl⟩⟩, rfl⟩
  refine Completes.append (m := b + 2) (by omega) (by omega)
    (by rw [valsList_hint]; exact .cons ⟨b, by omega, rfl⟩ (.cons ⟨b + 1, by omega, rfl⟩ (.nil _)))
    (hintKeep_complete σ _ _ _ _) (fun σ1 he1 hp1 => ?_)
  rw [hp1]
  refine Completes.append (m := b + 4) (by omega) (by omega) hs2.numBelow (seq_completes hs2 σ)
    (fun σ2 he2 hp2 => ?_)
  have hag2 : AgreeBelow (b + 2) σ σ2 := he2.agree
  have e2 : σ2 (.n (b + 2)) = σ2 cur + σ2 (.n b) := hp2.atom (a := .add _ _ _) (by simp [addS])
  have e3 : σ2 (.n (b + 3)) = σ2 (.n b) + σ2 (.n (b + 1)) := hp2.atom (a := .add _ _ _) (by simp [addS])
  have hb2 : σ2 (.n b) = σ (.n b) := hag2.apply ⟨b, by omega, rfl⟩
  have hb12 : σ2 (.n (b + 1)) = σ (.n (b + 1)) := hag2.apply ⟨b + 1, by omega, rfl⟩
  have hc2 : σ2 cur = σ cur := hag2.apply (hcur.mono' (by omega))
  have hbit2 : σ2 bit = σ bit := hag2.apply (hbit.mono' (by omega))
  have hmul : (Atom.mul (.n (b + 2)) bit (.n (b + 3))).Holds rd σ2 := by
    show σ2 (.n (b + 2)) = σ2 bit * σ2 (.n (b + 3))
    rw [e2, e3, hb2, hb12, hc2, hbit2, hbv, hh.1, hh.2]
    cases bt
    · simp [mPair, e_add_self]
    · simp [mPair, add_comm]
  refine Completes.append (m := b + 4) le_rfl (by omega)
    (by simp only [mulS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil]
        exact .cons ⟨b + 2, by omega, rfl⟩ (.cons (hbit.mono' (show b ≤ b + 4 by omega))
          (.cons ⟨b + 3, by omega, rfl⟩ (.nil _))))
    (check_complete hmul (b + 4)) (fun σ3 he3 hp3 => ?_)
  rw [hp3]
  refine Completes.append (m := c) (by omega) (by omega) hseq.numBelow (seq_completes hseq σ2)
    (fun σ4 he4 hp4 => ?_)
  have hag4 : AgreeBelow (b + 4) σ2 σ4 := he4.agree
  have hag24 : AgreeBelow b σ σ4 := fun j hj => (hag2 j (by omega)).trans (hag4 j (by omega))
  have hadr : σ4 (.n (c - 1)) = Aval := hA σ4 hag24 hp4
  have hpad4 : PadOK σ4 pad := hp.congr hpb hag24
  have h4b : σ4 (.n b) = σ (.n b) := (hag4.apply ⟨b, by omega, rfl⟩).trans hb2
  have h4b1 : σ4 (.n (b + 1)) = σ (.n (b + 1)) := (hag4.apply ⟨b + 1, by omega, rfl⟩).trans hb12
  have h4pp : σ4 pp = σ pp := hag24.apply hpp
  have hpc : IsCanonical128 (mPair bt (σ cur) sib).1 ∧ IsCanonical128 (mPair bt (σ cur) sib).2 := by
    cases bt <;> simp [mPair, hsc, hcc]
  obtain ⟨σ5, he5, ⟨hout, hcan⟩, hh5⟩ := k64_complete (C := C) (rd := rd) (pad := pad)
    (m0 := pp) (m1 := .n (c - 1)) (m2 := .n b) (m3 := .n (b + 1)) (c := c) σ4 hpad4 (by omega) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro v (rfl | rfl | rfl | rfl)
      · exact ⟨hpp.mono' (by omega), by rw [h4pp]; exact hppc⟩
      · exact ⟨⟨c - 1, by omega, rfl⟩, by rw [hadr]; exact hAc⟩
      · exact ⟨⟨b, by omega, rfl⟩, by rw [h4b, hh.1]; exact hpc.1⟩
      · exact ⟨⟨b + 1, by omega, rfl⟩, by rw [h4b1, hh.2]; exact hpc.2⟩)
  refine ⟨σ5, he5, ⟨?_, hcan, ?_, ?_⟩, hh5⟩
  · have := congrArg Prod.fst hout
    simp only at this
    rw [this, h4pp, hadr, h4b, h4b1, hh.1, hh.2]
  · rw [he5.apply (Or.inl (by omega)), h4b]
  · rw [he5.apply (Or.inl (by omega)), h4b1]

theorem pairLevel_numBelow (s : String) {pad : Nat} {pp bit cur : V} {b c w : Nat} {nodeL : List Stmt}
    (hpb : pad + 5 ≤ b) (hpp : NBv b pp) (hbit : NBv b bit) (hcur : NBv b cur)
    (hseq : SeqOK (b + 4) ([cst (b + 4) (word w 0 0)] ++ nodeL) c) (hcb : b + 5 ≤ c) :
    NumBelow (c + 14) (Stmt.valsList ([hintW s [.n b, .n (b + 1)], addS (.n (b + 2)) cur (.n b),
      addS (.n (b + 3)) (.n b) (.n (b + 1)), mulS (.n (b + 2)) bit (.n (b + 3)), cst (b + 4) (word w 0 0)] ++
      nodeL ++ k64 pad pp (.n (c - 1)) (.n b) (.n (b + 1)) c (c + 1))) := by
  have hn := hseq.numBelow
  rw [valsList_append] at hn
  intro x hx
  simp only [valsList_append, List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · simp only [hintW, addS, mulS, cst, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, Hint.vals,
      Dest.vals, List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact ⟨_, by omega, rfl⟩ | exact hcur.mono' (by omega) | exact hbit.mono' (by omega)
  · obtain ⟨j, hj, rfl⟩ := hn x (List.mem_append_right _ hx)
    exact ⟨j, by omega, rfl⟩
  · simp only [k64, cst, kecS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil,
      List.cons_append, List.nil_append, List.mem_cons] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hx
    all_goals first | exact ⟨_, by omega, rfl⟩ | exact hpp.mono' (by omega) |
      exact runV_nb (o := c + 1) (n := 13) (by omega) _ hx

/-! ## Folds -/

/-- A path folded from the bottom: the node at level `l + 1` is `node l` of the one at `l`
(`foldPath`'s order). -/
def pFold (node : Nat → E → E) : Nat → E → E
  | 0, v => v
  | l + 1, v => node l (pFold node l v)

/-- A path folded level by level, from level `l`, `m` levels. -/
def nIter (node : Nat → E → E) : Nat → Nat → E → E
  | _, 0, v => v
  | l, m + 1, v => nIter node (l + 1) m (node l v)

theorem nIter_pFold (node : Nat → E → E) : ∀ (m l : Nat) (v : E),
    nIter node l m (pFold node l v) = pFold node (l + m) v
  | 0, _, _ => rfl
  | m + 1, l, v => by
      rw [nIter, show node l (pFold node l v) = pFold node (l + 1) v from rfl, nIter_pFold node m (l + 1),
        show l + 1 + m = l + (m + 1) by omega]

theorem nIter_zero (node : Nat → E → E) (m : Nat) (v : E) : nIter node 0 m v = pFold node m v := by
  have := nIter_pFold node m 0 v
  rw [Nat.zero_add] at this
  exact this

/-! ## A FORS tree over cells -/

/-- The first bit of FORS tree `c`'s field. -/
def fOff (c : Nat) : Nat := 26 + 10 * c

/-- The address of tree `c`'s leaf `s` at the index `I`. -/
def fLeafAdr (I : E) (c s : Nat) : E := I + word (tw 15 + c * hiMul) 0 0 + eOfNat (2 ^ 38 * s)

/-- The address of tree `c`'s node above level `l` on the path of leaf `s`. -/
def fNodeAdr (I : E) (c l s : Nat) : E :=
  I + word (tw 17 + c * hiMul) 0 0 + word (64 * (l + 1) * hiMul) 0 0 + eOfNat (2 ^ 42 * (s >>> (l + 1)))

/-- Tree `c`'s node above level `l` from the one at `l`, its sibling `sib l`. -/
def fNode (pp I : E) (c s : Nat) (sib : Nat → E) (l : Nat) (v : E) : E :=
  (hcell [pp, fNodeAdr I c l s, (mPair (s.testBit l) v (sib l)).1, (mPair (s.testBit l) v (sib l)).2]).1

/-- Tree `c`'s leaf hashed from its secret. -/
def fLeaf (pp I : E) (c s : Nat) (secret : E) : E := (hcell [pp, fLeafAdr I c s, secret]).1

/-- **Tree `c`'s two top nodes**, in index order: the leaf climbed nine levels and the last
sibling. -/
def fTops (pp I : E) (c s : Nat) (secret : E) (sib : Nat → E) : E × E :=
  mPair (s.testBit 9) (pFold (fNode pp I c s sib) 9 (fLeaf pp I c s secret)) (sib 9)

theorem canon_fLeafAdr {I : E} (hI : IsCanonical128 I) (c s : Nat) : IsCanonical128 (fLeafAdr I c s) :=
  canon_add (canon_add hI (canon_word _ _)) (canon_eOfNat _)

theorem canon_fNodeAdr {I : E} (hI : IsCanonical128 I) (c l s : Nat) : IsCanonical128 (fNodeAdr I c l s) :=
  canon_add (canon_add (canon_add hI (canon_word _ _)) (canon_word _ _)) (canon_eOfNat _)

/-! ## Pieces -/

/-- **A 48-byte `keccak` completes** on canonical inputs, its output their `hcell`. -/
theorem k48_complete {a v : V} {c : Nat} (σ : Val) (hp : PadOK σ sPad) (hpc : sPad + 5 ≤ c)
    (hm : ∀ x ∈ [sPP, a, v], NBv c x ∧ IsCanonical128 (σ x)) :
    Completes C rd c (c + 14) (k48 a v c (c + 1)) σ
      (fun σ' => σ' (.n (c + 1)) = (hcell [σ sPP, σ a, σ v]).1 ∧ IsCanonical128 (σ' (.n (c + 1)))) := by
  have hsplit : k48 a v c (c + 1) = [cst c (word (2 ^ 63) 0 0)] ++ [kecS [sPP, a, v, .n sPad, .n (sPad + 1),
      .n (sPad + 2), .n (sPad + 3), .n (sPad + 4), .n c, .n (sPad + 1), .n (sPad + 2), .n (sPad + 3),
      .n (sPad + 4)] (runV (c + 1) 13) false false] := rfl
  rw [hsplit]
  refine Completes.append (m := c + 1) (by omega) (by omega)
    (by simp [cst, Stmt.vals, Atom.vals]; exact .cons ⟨c, by omega, rfl⟩ (.nil _))
    (cst_complete σ c _) (fun σ1 he1 hp1 => ?_)
  have hag : AgreeBelow c σ σ1 := he1.agree
  have hin : ∀ x ∈ [sPP, a, v, .n sPad, .n (sPad + 1), .n (sPad + 2), .n (sPad + 3), .n (sPad + 4), .n c,
      .n (sPad + 1), .n (sPad + 2), .n (sPad + 3), .n (sPad + 4)], NBv (c + 1) x := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ((hm _ (by simp)).1).mono' (by omega)
    · exact ((hm _ (by simp)).1).mono' (by omega)
    · exact ((hm _ (by simp)).1).mono' (by omega)
    all_goals exact ⟨_, by omega, rfl⟩
  have hp1' : PadOK σ1 sPad := hp.congr hpc hag
  obtain ⟨q0, q1, q2, q3, q4⟩ := hp1'
  have h3 : ∀ x ∈ [sPP, a, v], IsCanonical128 (σ1 x) := fun x hx => by
    rw [hag.apply (hm x hx).1]; exact (hm x hx).2
  have hcan : ∀ cc : Fin 13, IsCanonical128 (cells13 ([sPP, a, v, .n sPad, .n (sPad + 1), .n (sPad + 2),
      .n (sPad + 3), .n (sPad + 4), .n c, .n (sPad + 1), .n (sPad + 2), .n (sPad + 3), .n (sPad + 4)].map σ1) cc) := by
    intro cc
    fin_cases cc <;> simp [cells13, q0, q1, q2, q3, q4, hp1] <;>
      first | exact h3 _ (by simp) | exact canon_word _ _ | exact canon_zero
  obtain ⟨σ2, he2, hp2, hh2⟩ := kecS_complete (C := C) (rd := rd) σ1 (c + 1) rfl hin hcan false false
  refine ⟨σ2, he2.mono (by omega) (by omega), ⟨?_, ?_⟩, hh2⟩
  · have hk : AtomsHold rd σ2 (k48 a v c (c + 1)) := by
      rw [hsplit]
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · simp only [cst, List.mem_singleton, Stmt.atom.injEq] at hx
        subst hx
        show σ2 (.n c) = _
        rw [he2.apply (Or.inl (by omega))]
        exact hp1
      · exact atomsHold_of_holdsList rfl (hh2 True (fun _ => True) trivial) x hx
    have hag2 : AgreeBelow (c + 1) σ1 σ2 := he2.agree
    have hp2' : PadOK σ2 sPad := hp.congr hpc (fun j hj => (hag j hj).trans (hag2 j (by omega)))
    have := congrArg Prod.fst (k48_sound (rd := rd) hp2' hk)
    simp only at this
    have ea : ∀ x ∈ [sPP, a, v], σ2 x = σ x := fun x hx =>
      (hag2.apply ((hm x hx).1.mono' (by omega))).trans (hag.apply (hm x hx).1)
    rw [this, ea sPP (by simp), ea a (by simp), ea v (by simp)]
  · rw [hp2 0 (by norm_num)]
    exact canon_kOut _ _ _ _

/-- **`is_child` holds** of children hinted in the order of the bit. -/
theorem isChild_holds {σ : Val} {cur k0 k1 bit d0 d1 : V} {bt : Bool} {sib : E}
    (h0 : σ k0 = (mPair bt (σ cur) sib).1) (h1 : σ k1 = (mPair bt (σ cur) sib).2)
    (hb : σ bit = if bt then 1 else 0) (e0 : σ d0 = σ cur + σ k0) (e1 : σ d1 = σ k0 + σ k1) :
    (Atom.mul d0 bit d1).Holds rd σ := by
  show σ d0 = σ bit * σ d1
  rw [e0, e1, h0, h1, hb]
  cases bt
  · simp [mPair, e_add_self]
  · simp [mPair, add_comm]

/-! ## The levels -/

/-- A FORS level's node address after its constant: the base plus it, the index shifted. -/
def fNodeL (c l : Nat) (base : V) (x : Nat) : List Stmt :=
  [addS (.n (x + 5)) base (.n (x + 4)), cst (x + 6) (word (2 ^ 42) 0 0),
    mulS (.n (x + 7)) (sVal (fOff c + l + 1)) (.n (x + 6)), addS (.n (x + 8)) (.n (x + 5)) (.n (x + 7))]

theorem sForsLevel_eq (c l : Nat) (base cur : V) (x : Nat) :
    sForsLevel c l base cur x = ([hintW "sp_fors_nodes" [.n x, .n (x + 1)], addS (.n (x + 2)) cur (.n x),
      addS (.n (x + 3)) (.n x) (.n (x + 1)), mulS (.n (x + 2)) (sBit (fOff c + l)) (.n (x + 3)),
      cst (x + 4) (word (64 * (l + 1) * hiMul) 0 0)] ++ fNodeL c l base x ++
      k64 sPad sPP (.n (x + 9 - 1)) (.n x) (.n (x + 1)) (x + 9) (x + 9 + 1), x + 23, .n (x + 10)) := by
  simp [sForsLevel, isChildS, fNodeL, fOff]

theorem fNodeL_seq {c l : Nat} {base : V} {x w : Nat} (hb : NBv x base) (hv : NBv x (sVal (fOff c + l + 1))) :
    SeqOK (x + 4) ([cst (x + 4) (word w 0 0)] ++ fNodeL c l base x) (x + 9) :=
  ⟨rfl, ⟨rfl, hb.mono' (by omega), ⟨x + 4, by omega, rfl⟩⟩, rfl, ⟨rfl, hv.mono' (by omega), ⟨x + 6, by omega, rfl⟩⟩,
    ⟨rfl, ⟨x + 5, by omega, rfl⟩, ⟨x + 7, by omega, rfl⟩⟩, rfl⟩

theorem sForsLevels_succ (c : Nat) (base : V) (m l : Nat) (cur : V) (x : Nat) :
    sForsLevels c base (m + 1) l cur x = ((sForsLevel c l base cur x).1 ++
      (sForsLevels c base m (l + 1) (.n (x + 10)) (x + 23)).1,
      (sForsLevels c base m (l + 1) (.n (x + 10)) (x + 23)).2.1,
      (sForsLevels c base m (l + 1) (.n (x + 10)) (x + 23)).2.2) := by
  simp only [sForsLevels, sForsLevel_eq]

theorem sForsLevels_shape (c : Nat) (base : V) : ∀ (m l : Nat) (cur : V) (x : Nat),
    (sForsLevels c base m l cur x).2.1 = x + 23 * m ∧
      (sForsLevels c base m l cur x).2.2 = if m = 0 then cur else .n (x + 23 * m - 13)
  | 0, _, _, _ => by simp [sForsLevels]
  | m + 1, l, cur, x => by
      rw [sForsLevels_succ]
      obtain ⟨h1, h2⟩ := sForsLevels_shape c base m (l + 1) (.n (x + 10)) (x + 23)
      refine ⟨by rw [h1]; ring, ?_⟩
      rw [h2]
      split
      · rename_i hm; subst hm; simp
      · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, V.mk.injEq, true_and]; omega

theorem sVal_fors_nb {c j : Nat} (hc : c < 24) (hj : j < 10) : NBv 1225 (sVal (fOff c + j)) := by
  obtain ⟨k, hk, e⟩ := sVal_nb (i := fOff c + j) (by unfold fOff; omega)
  exact ⟨k, by omega, e⟩

theorem sBit_fors_nb {c j : Nat} (hc : c < 24) (hj : j < 10) : NBv 1225 (sBit (fOff c + j)) :=
  ⟨51 + (fOff c + j), by unfold fOff; omega, rfl⟩

theorem fNodeAdr_val {σ : Val} {c l s x : Nat} {base : V} {I : E} (hs : s < 2 ^ 10)
    (hbase : σ base = I + word (tw 17 + c * hiMul) 0 0)
    (hv : σ (sVal (fOff c + l + 1)) = eOfNat (s >>> (l + 1)))
    (h : AtomsHold rd σ ([cst (x + 4) (word (64 * (l + 1) * hiMul) 0 0)] ++ fNodeL c l base x)) :
    σ (.n (x + 8)) = fNodeAdr I c l s := by
  have c4 := h.atom (a := .const (.n (x + 4)) (word (64 * (l + 1) * hiMul) 0 0)) (by simp [cst])
  have a5 := h.atom (a := .add (.n (x + 5)) base (.n (x + 4))) (by simp [fNodeL, addS])
  have c6 := h.atom (a := .const (.n (x + 6)) (word (2 ^ 42) 0 0)) (by simp [fNodeL, cst])
  have m7 := h.atom (a := .mul (.n (x + 7)) (sVal (fOff c + l + 1)) (.n (x + 6))) (by simp [fNodeL, mulS])
  have a8 := h.atom (a := .add (.n (x + 8)) (.n (x + 5)) (.n (x + 7))) (by simp [fNodeL, addS])
  simp only [Atom.Holds] at c4 a5 c6 m7 a8
  have hsl : s >>> (l + 1) < 2 ^ 10 := lt_of_le_of_lt (Nat.shiftRight_le _ _) hs
  rw [a8, a5, m7, c4, c6, hbase, hv, word_eq_eOfNat (2 ^ 42), mul_comm (eOfNat (s >>> (l + 1))),
    eOfNat_two_pow_mul (two_pow_mul_lt hsl (by norm_num)), fNodeAdr]

/-- **FORS tree `c`'s levels `l ..< l + m` complete**: each level's children hinted in the order of
its bit, the node reached the fold of the siblings. -/
theorem sForsLevels_complete {c s : Nat} (hc : c < 24) (hs : s < 2 ^ 10) {base : V} {pp I : E}
    {sib : Nat → E} (hsib : ∀ l, IsCanonical128 (sib l)) (hI : IsCanonical128 I)
    (hppc : IsCanonical128 pp) :
    ∀ (m l : Nat) (cur : V) (x : Nat) (σ : Val), l + m ≤ 9 → 1225 ≤ x → NBv x base → NBv x cur →
      PadOK σ sPad → σ sPP = pp → σ base = I + word (tw 17 + c * hiMul) 0 0 →
      (∀ j < 10, σ (sBit (fOff c + j)) = if s.testBit j then 1 else 0) →
      (∀ j < 10, σ (sVal (fOff c + j)) = eOfNat (s >>> j)) → IsCanonical128 (σ cur) →
      Completes C rd x (x + 23 * m) (sForsLevels c base m l cur x).1 σ
        (fun σ' => σ' (sForsLevels c base m l cur x).2.2 = nIter (fNode pp I c s sib) l m (σ cur) ∧
          IsCanonical128 (σ' (sForsLevels c base m l cur x).2.2))
  | 0, l, cur, x, σ, _, _, _, _, _, _, _, _, _, hcc => by
      simp only [sForsLevels, Nat.mul_zero, Nat.add_zero, nIter]
      exact Completes.nil' ⟨rfl, hcc⟩
  | m + 1, l, cur, x, σ, hlm, hx, hbase, hcur, hp, hpp, hbv, hbits, hvals, hcc => by
      rw [sForsLevels_succ, sForsLevel_eq]
      dsimp only
      set bt := s.testBit l with hbt
      set kids := mPair bt (σ cur) (sib l) with hkids
      set g : Nat → E := fun j => if j = 0 then kids.1 else kids.2 with hg
      refine Completes.reload ((updRun_ext σ x 2 g).mono le_rfl (by omega)) ?_
      set σk := updRun σ x 2 g with hσk
      have tk : ∀ v, NBv x v → σk v = σ v := fun v hv => updRun_below σ x 2 g hv
      have hvl : NBv x (sVal (fOff c + l + 1)) := (sVal_fors_nb (j := l + 1) hc (by omega)).mono' hx
      have hbl : NBv x (sBit (fOff c + l)) := (sBit_fors_nb (j := l) hc (by omega)).mono' hx
      have hppx : NBv x sPP := ⟨2, by omega, rfl⟩
      have hpk : PadOK σk sPad := hp.congr (b := x) (by unfold sPad; omega)
        (fun j hj => (tk (.n j) ⟨j, hj, rfl⟩).symm)
      have hlev := pairLevel_complete (C := C) (rd := rd) "sp_fors_nodes" (pad := sPad) (pp := sPP)
        (bit := sBit (fOff c + l)) (cur := cur) (b := x) (c := x + 9) (w := 64 * (l + 1) * hiMul)
        (nodeL := fNodeL c l base x) σk hpk (by unfold sPad; omega) hppx hbl hcur
        (fNodeL_seq hbase hvl) (by omega) (Aval := fNodeAdr I c l s)
        (fun σ' hag hh => fNodeAdr_val hs (by rw [hag.apply hbase, tk _ hbase]; exact hbv)
          (by rw [hag.apply hvl, tk _ hvl, Nat.add_assoc]; exact hvals (l + 1) (by omega)) hh)
        (canon_fNodeAdr hI c l s) (bt := bt) (by rw [tk _ hbl]; exact hbits l (by omega)) (hsib l)
        (by rw [tk _ hcur]; exact hcc) (by rw [tk _ hppx, hpp]; exact hppc)
        ⟨by rw [tk _ hcur]; exact updRun_at σ x 2 g (j := 0) (by norm_num),
         by rw [tk _ hcur]; exact updRun_at σ x 2 g (j := 1) (by norm_num)⟩
      obtain ⟨n1, n2⟩ := sForsLevels_shape c base m (l + 1) (.n (x + 10)) (x + 23)
      refine Completes.append (m := x + 9 + 14) (by omega) (by omega)
        (pairLevel_numBelow "sp_fors_nodes" (by unfold sPad; omega) hppx hbl hcur (fNodeL_seq hbase hvl)
          (by omega)) hlev (fun σ1 he1 ⟨hv1, hc1, _, _⟩ => ?_)
      have t1 : ∀ v, NBv x v → σ1 v = σ v := fun v hv => by
        obtain ⟨j, hj, rfl⟩ := hv
        rw [he1.apply (Or.inl hj), tk _ ⟨j, hj, rfl⟩]
      have ih := sForsLevels_complete hc hs hsib hI hppc m (l + 1) (.n (x + 10)) (x + 9 + 14) σ1 (by omega)
        (by omega) (hbase.mono' (by omega)) ⟨x + 10, by omega, rfl⟩
        (hp.congr (b := x) (by unfold sPad; omega) (fun j hj => (t1 (.n j) ⟨j, hj, rfl⟩).symm))
        (by rw [t1 _ hppx]; exact hpp) (by rw [t1 _ hbase]; exact hbv)
        (fun j hj => by rw [t1 _ ((sBit_fors_nb hc hj).mono' hx)]; exact hbits j hj)
        (fun j hj => by rw [t1 _ ((sVal_fors_nb hc hj).mono' hx)]; exact hvals j hj) hc1
      rw [show x + 9 + 14 = x + 23 by omega] at ih
      refine (ih.mono (by omega) (by omega) (fun σ' ⟨q1, q2⟩ => ⟨?_, q2⟩))
      rw [q1, hv1, tk _ hppx, hpp, tk _ hcur]
      rfl

theorem sForsLevels_nb {c : Nat} (hc : c < 24) {base : V} :
    ∀ (m l : Nat) (cur : V) (x : Nat), l + m ≤ 9 → 1225 ≤ x → NBv x base → NBv x cur →
      NumBelow (x + 23 * m) (Stmt.valsList (sForsLevels c base m l cur x).1)
  | 0, _, _, _, _, _, _, _ => by simp [sForsLevels]; exact NumBelow.nil _
  | m + 1, l, cur, x, hlm, hx, hbase, hcur => by
      rw [sForsLevels_succ, sForsLevel_eq]
      dsimp only
      rw [valsList_append]
      have hvl : NBv x (sVal (fOff c + l + 1)) := (sVal_fors_nb (j := l + 1) hc (by omega)).mono' hx
      have hbl : NBv x (sBit (fOff c + l)) := (sBit_fors_nb (j := l) hc (by omega)).mono' hx
      have h1 := pairLevel_numBelow "sp_fors_nodes" (pad := sPad) (pp := sPP) (w := 64 * (l + 1) * hiMul)
        (by unfold sPad; omega) ⟨2, by omega, rfl⟩ hbl hcur (fNodeL_seq hbase hvl) (by omega)
      have h2 := sForsLevels_nb hc m (l + 1) (.n (x + 10)) (x + 23) (by omega) (by omega)
        (hbase.mono' (by omega)) ⟨x + 10, by omega, rfl⟩
      rw [show x + 23 * (m + 1) = x + 23 + 23 * m by ring]
      exact (h1.mono (by omega)).append h2

/-! ## A tree -/

/-- Tree `c`'s leaf address from base `b`. -/
def fLeafPre (c b : Nat) : List Stmt :=
  [cst (b + 1) (word (tw 15 + c * hiMul) 0 0), addS (.n (b + 2)) sIdx (.n (b + 1)), cst (b + 3) (word (2 ^ 38) 0 0),
    mulS (.n (b + 4)) (sVal (fOff c)) (.n (b + 3)), addS (.n (b + 5)) (.n (b + 2)) (.n (b + 4))]

/-- Tree `c`'s node base from base `b`. -/
def fBasePre (c b : Nat) : List Stmt :=
  [cst (b + 20) (word (tw 17 + c * hiMul) 0 0), addS (.n (b + 21)) sIdx (.n (b + 20))]

/-- Tree `c`'s top check from base `b`. -/
def fTopChk (b : Nat) : List Stmt :=
  [addS (.n (b + 231)) (.n (b + 216)) (.n (b + 229)), addS (.n (b + 232)) (.n (b + 229)) (.n (b + 230))]

theorem sForsTree_eq (c b : Nat) : sForsTree c b =
    (hintW "sp_fors_secrets" [.n b] :: (fLeafPre c b ++ (k48 (.n (b + 5)) (.n b) (b + 6) (b + 7) ++
      (fBasePre c b ++ ((sForsLevels c (.n (b + 21)) 9 0 (.n (b + 7)) (b + 22)).1 ++
        (hintW "sp_fors_nodes" [.n (b + 229), .n (b + 230)] :: (fTopChk b ++
          [mulS (.n (b + 231)) (sBit (fOff c + 9)) (.n (b + 232))])))))),
      b + 233, .n (b + 229), .n (b + 230)) := by
  obtain ⟨h1, h2⟩ := sForsLevels_shape c (.n (b + 21)) 9 0 (.n (b + 7)) (b + 22)
  simp only [sForsTree, h1, h2, fLeafPre, fBasePre, fTopChk, isChildS, fOff]
  simp

theorem k48_nb {a v : V} {c : Nat} (hpc : sPad + 5 ≤ c) (ha : NBv c a) (hv : NBv c v) :
    NumBelow (c + 14) (Stmt.valsList (k48 a v c (c + 1))) := by
  intro x hx
  simp only [k48, k48At, cst, kecS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil,
    List.cons_append, List.nil_append, List.mem_cons] at hx
  unfold sPad at hpc
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hx
  all_goals first | exact ⟨_, by omega, rfl⟩ | exact ⟨_, by simp only [sPad]; omega, rfl⟩ |
    exact ha.mono' (by omega) | exact hv.mono' (by omega) | (apply runV_nb (o := c + 1) (n := 13) (by omega); assumption)

theorem fOff_eq (c : Nat) : sFieldOff (3 + c) = fOff c := by unfold sFieldOff fOff; split_ifs <;> omega

theorem fLen_eq (c : Nat) : sFieldLen (3 + c) = 10 := by unfold sFieldLen; split_ifs <;> omega

theorem fors_bits {σ : Val} {D c : Nat} (hc : c < 24) (hb : BitsAt σ D) :
    ∀ j < 10, σ (sBit (fOff c + j)) = if (fieldNat D (3 + c)).testBit j then 1 else 0 := by
  intro j hj
  rw [hb _ (by unfold fOff; omega), testBit_fieldNat D (3 + c) j (by rw [fLen_eq]; omega), fOff_eq]

theorem fors_vals {σ : Val} {D c : Nat} (hc : c < 24) (hv : ValsAt σ D) :
    ∀ j < 10, σ (sVal (fOff c + j)) = eOfNat (fieldNat D (3 + c) >>> j) := by
  intro j hj
  have := valsAt_field hv (f := 3 + c) (by omega) (k := j) (by rw [fLen_eq]; omega)
  rwa [fOff_eq] at this

theorem fieldNat_fors_lt (D c : Nat) : fieldNat D (3 + c) < 2 ^ 10 := by
  have := fieldNat_lt D (3 + c)
  rwa [fLen_eq] at this

/-- **FORS tree `c` completes**: its secret hinted, its leaf hashed, its nine levels climbed and its
two top nodes hinted in index order. -/
theorem sForsTree_complete {c : Nat} (hc : c < 24) {D : Nat} {pp I secret : E} {sib : Nat → E}
    (hsec : IsCanonical128 secret) (hsib : ∀ l, IsCanonical128 (sib l)) (hI : IsCanonical128 I)
    (hppc : IsCanonical128 pp) (σ : Val) {b : Nat} (hb : 1225 ≤ b) (hp : PadOK σ sPad) (hpp : σ sPP = pp)
    (hidx : σ sIdx = I) (hbits : BitsAt σ D) (hvals : ValsAt σ D) :
    Completes C rd b (b + 233) (sForsTree c b).1 σ (fun σ' =>
      (σ' (.n (b + 229)), σ' (.n (b + 230))) = fTops pp I c (fieldNat D (3 + c)) secret sib) := by
  set s := fieldNat D (3 + c) with hsdef
  have hs : s < 2 ^ 10 := fieldNat_fors_lt D c
  have hb10 := fors_bits hc hbits
  have hv10 := fors_vals hc hvals
  rw [← hsdef] at hb10 hv10
  rw [sForsTree_eq]
  dsimp only
  have hidxnb : NBv 1225 sIdx := ⟨1067, by norm_num, sIdx_eq⟩
  -- the secret
  refine Completes.reload ((updRun_ext σ b 1 fun _ => secret).mono le_rfl (by omega)) ?_
  set σs := updRun σ b 1 fun _ => secret with hσs
  have ts : ∀ v, NBv b v → σs v = σ v := fun v hv => updRun_below σ b 1 _ hv
  have es : σs (.n b) = secret := by simpa using updRun_at σ b 1 (fun _ => secret) (j := 0) (by norm_num)
  refine Completes.append (xs := [hintW "sp_fors_secrets" [.n b]]) (m := b + 1) (by omega) (by omega)
    (by rw [valsList_hint]; exact .cons ⟨b, by omega, rfl⟩ (.nil _)) (hintKeep_complete _ _ _ _ _)
    (fun σ1 _ e1 => ?_)
  subst e1
  -- the leaf's address
  have hlp : SeqOK (b + 1) (fLeafPre c b) (b + 6) :=
    ⟨rfl, ⟨rfl, hidxnb.mono' (by omega), ⟨b + 1, by omega, rfl⟩⟩, rfl,
      ⟨rfl, (sVal_fors_nb (j := 0) hc (by norm_num)).mono' (by omega), ⟨b + 3, by omega, rfl⟩⟩,
      ⟨rfl, ⟨b + 2, by omega, rfl⟩, ⟨b + 4, by omega, rfl⟩⟩, rfl⟩
  refine Completes.seq hlp (by omega) (fun σ2 he2 hh2 => ?_)
  have t2 : ∀ v, NBv b v → σ2 v = σ v := fun v hv => by
    obtain ⟨j, hj, rfl⟩ := hv; rw [he2.apply (Or.inl (by omega)), ts _ ⟨j, hj, rfl⟩]
  have e2b : σ2 (.n b) = secret := by rw [he2.apply (Or.inl (by omega))]; exact es
  have hla : σ2 (.n (b + 5)) = fLeafAdr I c s := by
    have c1 := hh2.atom (a := .const (.n (b + 1)) (word (tw 15 + c * hiMul) 0 0)) (by simp [fLeafPre, cst])
    have a2 := hh2.atom (a := .add (.n (b + 2)) sIdx (.n (b + 1))) (by simp [fLeafPre, addS])
    have c3 := hh2.atom (a := .const (.n (b + 3)) (word (2 ^ 38) 0 0)) (by simp [fLeafPre, cst])
    have m4 := hh2.atom (a := .mul (.n (b + 4)) (sVal (fOff c)) (.n (b + 3))) (by simp [fLeafPre, mulS])
    have a5 := hh2.atom (a := .add (.n (b + 5)) (.n (b + 2)) (.n (b + 4))) (by simp [fLeafPre, addS])
    simp only [Atom.Holds] at c1 a2 c3 m4 a5
    have hv0 : σ2 (sVal (fOff c)) = eOfNat s := by
      have := hv10 0 (by norm_num); rw [Nat.add_zero, Nat.shiftRight_zero] at this
      rw [t2 _ (by simpa using (sVal_fors_nb (j := 0) hc (by norm_num)).mono' hb), this]
    rw [a5, a2, c1, m4, c3, hv0, t2 _ (hidxnb.mono' hb), hidx, word_eq_eOfNat (2 ^ 38),
      mul_comm (eOfNat s), eOfNat_two_pow_mul (two_pow_mul_lt hs (by norm_num)), fLeafAdr]
  -- the leaf
  have hpp2 : σ2 sPP = pp := by rw [t2 sPP ⟨2, by omega, rfl⟩]; exact hpp
  have hp2 : PadOK σ2 sPad := hp.congr (b := b) (by unfold sPad; omega) (fun j hj => (t2 (.n j) ⟨j, hj, rfl⟩).symm)
  refine Completes.append (m := b + 6 + 14) (by omega) (by omega)
    (k48_nb (by unfold sPad; omega) ⟨b + 5, by omega, rfl⟩ ⟨b, by omega, rfl⟩)
    (k48_complete (C := C) (rd := rd) (a := .n (b + 5)) (v := .n b) (c := b + 6) σ2 hp2 (by unfold sPad; omega)
      (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro x (rfl | rfl | rfl)
        · exact ⟨⟨2, by omega, rfl⟩, by rw [hpp2]; exact hppc⟩
        · exact ⟨⟨b + 5, by omega, rfl⟩, by rw [hla]; exact canon_fLeafAdr hI c s⟩
        · exact ⟨⟨b, by omega, rfl⟩, by rw [e2b]; exact hsec⟩))
    (fun σ3 he3 ⟨hl3, hc3⟩ => ?_)
  rw [hpp2, hla, e2b] at hl3
  rw [show b + 6 + 1 = b + 7 by omega] at hl3 hc3
  -- the node base
  have hbp : SeqOK (b + 20) (fBasePre c b) (b + 22) :=
    ⟨rfl, ⟨rfl, hidxnb.mono' (by omega), ⟨b + 20, by omega, rfl⟩⟩, rfl⟩
  refine Completes.seq hbp (by omega) (fun σ4 he4 hh4 => ?_)
  have t4 : ∀ v, NBv b v → σ4 v = σ v := fun v hv => by
    obtain ⟨j, hj, rfl⟩ := hv
    rw [he4.apply (Or.inl (by omega)), he3.apply (Or.inl (by omega)), t2 _ ⟨j, hj, rfl⟩]
  have hbase : σ4 (.n (b + 21)) = I + word (tw 17 + c * hiMul) 0 0 := by
    have c0 := hh4.atom (a := .const (.n (b + 20)) (word (tw 17 + c * hiMul) 0 0)) (by simp [fBasePre, cst])
    have a1 := hh4.atom (a := .add (.n (b + 21)) sIdx (.n (b + 20))) (by simp [fBasePre, addS])
    simp only [Atom.Holds] at c0 a1
    rw [a1, c0, t4 _ (hidxnb.mono' hb), hidx]
  have h7 : σ4 (.n (b + 7)) = fLeaf pp I c s secret := by
    rw [he4.apply (Or.inl (by omega))]; exact hl3
  -- the levels
  have hlev := sForsLevels_complete (C := C) (rd := rd) hc hs hsib hI hppc 9 0 (.n (b + 7)) (b + 22) σ4
    (by norm_num) (by omega) ⟨b + 21, by omega, rfl⟩ ⟨b + 7, by omega, rfl⟩
    (hp.congr (b := b) (by unfold sPad; omega) (fun j hj => (t4 (.n j) ⟨j, hj, rfl⟩).symm))
    (by rw [t4 sPP ⟨2, by omega, rfl⟩]; exact hpp) hbase
    (fun j hj => by rw [t4 _ ((sBit_fors_nb hc hj).mono' hb)]; exact hb10 j hj)
    (fun j hj => by rw [t4 _ ((sVal_fors_nb hc hj).mono' hb)]; exact hv10 j hj)
    (by rw [h7]; exact canon_hcell _)
  obtain ⟨-, hout⟩ := sForsLevels_shape c (.n (b + 21)) 9 0 (.n (b + 7)) (b + 22)
  rw [hout] at hlev
  simp only [show (9 : Nat) ≠ 0 from by norm_num, ↓reduceIte, show b + 22 + 23 * 9 - 13 = b + 216 by omega,
    show b + 22 + 23 * 9 = b + 229 by omega] at hlev
  refine Completes.append (m := b + 229) (by omega) (by omega)
    (by have := sForsLevels_nb (base := .n (b + 21)) hc 9 0 (.n (b + 7)) (b + 22) (by norm_num) (by omega)
          ⟨b + 21, by omega, rfl⟩ ⟨b + 7, by omega, rfl⟩
        rwa [show b + 22 + 23 * 9 = b + 229 by omega] at this) hlev (fun σ5 he5 ⟨hv5, hc5⟩ => ?_)
  rw [h7, nIter_zero] at hv5
  -- the top nodes
  set cur := pFold (fNode pp I c s sib) 9 (fLeaf pp I c s secret) with hcur
  set tops := mPair (s.testBit 9) cur (sib 9) with htops
  set g : Nat → E := fun j => if j = 0 then tops.1 else tops.2 with hg
  refine Completes.reload ((updRun_ext σ5 (b + 229) 2 g).mono le_rfl (by omega)) ?_
  set σt := updRun σ5 (b + 229) 2 g with hσt
  have tt : ∀ v, NBv (b + 229) v → σt v = σ5 v := fun v hv => updRun_below σ5 (b + 229) 2 g hv
  have et0 : σt (.n (b + 229)) = tops.1 := by
    have := updRun_at σ5 (b + 229) 2 g (j := 0) (by norm_num)
    rw [Nat.add_zero] at this
    show updRun σ5 (b + 229) 2 g (.n (b + 229)) = tops.1
    rw [this]; rfl
  have et1 : σt (.n (b + 229 + 1)) = tops.2 := updRun_at σ5 (b + 229) 2 g (j := 1) (by norm_num)
  refine Completes.append (xs := [hintW "sp_fors_nodes" [.n (b + 229), .n (b + 230)]]) (m := b + 231)
    (by omega) (by omega) (by rw [valsList_hint]; exact .cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.nil _)))
    (hintKeep_complete _ _ _ _ _) (fun σ6 _ e6 => ?_)
  subst e6
  have hck : SeqOK (b + 231) (fTopChk b) (b + 233) :=
    ⟨⟨rfl, ⟨b + 216, by omega, rfl⟩, ⟨b + 229, by omega, rfl⟩⟩, ⟨rfl, ⟨b + 229, by omega, rfl⟩,
      ⟨b + 230, by omega, rfl⟩⟩, rfl⟩
  refine Completes.seq hck le_rfl (fun σ7 he7 hh7 => ?_)
  have t7 : ∀ k < b + 231, σ7 (.n k) = σt (.n k) := fun k hk => he7.apply (Or.inl hk)
  have e7a := hh7.atom (a := .add (.n (b + 231)) (.n (b + 216)) (.n (b + 229))) (by simp [fTopChk, addS])
  have e7b := hh7.atom (a := .add (.n (b + 232)) (.n (b + 229)) (.n (b + 230))) (by simp [fTopChk, addS])
  have hbit9 : σ7 (sBit (fOff c + 9)) = if s.testBit 9 then 1 else 0 := by
    rw [show sBit (fOff c + 9) = .n (51 + (fOff c + 9)) from rfl, t7 _ (by unfold fOff; omega),
      tt _ ⟨_, by unfold fOff; omega, rfl⟩, he5.apply (Or.inl (by unfold fOff; omega)),
      ← show sBit (fOff c + 9) = .n (51 + (fOff c + 9)) from rfl, t4 _ ((sBit_fors_nb hc (by norm_num)).mono' hb)]
    exact hb10 9 (by norm_num)
  have h216 : σ7 (.n (b + 216)) = cur := by
    rw [t7 _ (by omega), tt _ ⟨_, by omega, rfl⟩]; exact hv5
  have hmul := isChild_holds (rd := rd) (σ := σ7) (cur := .n (b + 216)) (k0 := .n (b + 229))
    (k1 := .n (b + 230)) (bit := sBit (fOff c + 9)) (d0 := .n (b + 231)) (d1 := .n (b + 232)) (bt := s.testBit 9)
    (sib := sib 9) (by rw [h216, t7 _ (by omega), et0]) (by rw [h216, t7 _ (by omega), ← et1]) hbit9 e7a e7b
  refine Completes.checks (xs := [mulS (.n (b + 231)) (sBit (fOff c + 9)) (.n (b + 232))]) rfl
    (fun a ha => by simp only [mulS, List.mem_singleton, Stmt.atom.injEq] at ha; subst ha; exact hmul)
    (by
      simp only [mulS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil]
      exact .cons ⟨_, by omega, rfl⟩ (.cons ((sBit_fors_nb hc (by norm_num)).mono' (by omega))
        (.cons ⟨_, by omega, rfl⟩ (.nil _))))
    le_rfl (Completes.nil' ?_)
  rw [t7 _ (by omega), t7 _ (by omega), et0, show b + 230 = b + 229 + 1 by omega, et1]
  rfl

theorem sForsTree_nb {c : Nat} (hc : c < 24) {b : Nat} (hb : 1225 ≤ b) :
    NumBelow (b + 233) (Stmt.valsList (sForsTree c b).1) := by
  rw [sForsTree_eq]
  dsimp only
  have hidxnb : NBv 1225 sIdx := ⟨1067, by norm_num, sIdx_eq⟩
  have hlp : SeqOK (b + 1) (fLeafPre c b) (b + 6) :=
    ⟨rfl, ⟨rfl, hidxnb.mono' (by omega), ⟨b + 1, by omega, rfl⟩⟩, rfl,
      ⟨rfl, (sVal_fors_nb (j := 0) hc (by norm_num)).mono' (by omega), ⟨b + 3, by omega, rfl⟩⟩,
      ⟨rfl, ⟨b + 2, by omega, rfl⟩, ⟨b + 4, by omega, rfl⟩⟩, rfl⟩
  have hbp : SeqOK (b + 20) (fBasePre c b) (b + 22) :=
    ⟨rfl, ⟨rfl, hidxnb.mono' (by omega), ⟨b + 20, by omega, rfl⟩⟩, rfl⟩
  have hck : SeqOK (b + 231) (fTopChk b) (b + 233) :=
    ⟨⟨rfl, ⟨b + 216, by omega, rfl⟩, ⟨b + 229, by omega, rfl⟩⟩, ⟨rfl, ⟨b + 229, by omega, rfl⟩,
      ⟨b + 230, by omega, rfl⟩⟩, rfl⟩
  have hlv := sForsLevels_nb (base := .n (b + 21)) hc 9 0 (.n (b + 7)) (b + 22) (by norm_num) (by omega)
    ⟨b + 21, by omega, rfl⟩ ⟨b + 7, by omega, rfl⟩
  have hk := k48_nb (a := .n (b + 5)) (v := .n b) (c := b + 6) (by unfold sPad; omega) ⟨b + 5, by omega, rfl⟩
    ⟨b, by omega, rfl⟩
  intro v hv
  simp only [valsList_cons, valsList_append, List.mem_append] at hv
  rcases hv with hv | hv | hv | hv | hv | hv | hv | hv | hv
  · simp only [hintW, Stmt.vals, Atom.vals, Hint.vals, Dest.vals, List.mem_singleton] at hv
    exact ⟨b, by omega, hv⟩
  · exact (hlp.numBelow.mono (by omega)) v hv
  · exact (hk.mono (by omega)) v hv
  · exact (hbp.numBelow.mono (by omega)) v hv
  · exact (hlv.mono (by omega)) v hv
  · simp only [hintW, Stmt.vals, Atom.vals, Hint.vals, Dest.vals, List.mem_cons, List.not_mem_nil,
      or_false] at hv
    rcases hv with rfl | rfl
    · exact ⟨_, by omega, rfl⟩
    · exact ⟨_, by omega, rfl⟩
  · exact (hck.numBelow.mono (by omega)) v hv
  · simp only [mulS, Stmt.vals, Atom.vals, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact ⟨_, by omega, rfl⟩
    · exact (sBit_fors_nb hc (by norm_num)).mono' (by omega)
    · exact ⟨_, by omega, rfl⟩
  · simp at hv

theorem sForsTrees_succ (m c b : Nat) : (sForsTrees (m + 1) c b).1 =
    (sForsTree c b).1 ++ (sForsTrees m (c + 1) (b + 233)).1 ∧
    (sForsTrees (m + 1) c b).2.1 = (sForsTrees m (c + 1) (b + 233)).2.1 := by
  exact ⟨rfl, rfl⟩

theorem sForsTrees_end : ∀ (m c b : Nat), (sForsTrees m c b).2.1 = b + 233 * m
  | 0, _, _ => rfl
  | m + 1, c, b => by rw [(sForsTrees_succ m c b).2, sForsTrees_end m (c + 1) (b + 233)]; ring

theorem sForsTrees_nb : ∀ (m c b : Nat), c + m ≤ 24 → 1225 ≤ b →
    NumBelow (b + 233 * m) (Stmt.valsList (sForsTrees m c b).1)
  | 0, _, _, _, _ => by simp [sForsTrees]; exact NumBelow.nil _
  | m + 1, c, b, hcm, hb => by
      rw [(sForsTrees_succ m c b).1, valsList_append, show b + 233 * (m + 1) = b + 233 + 233 * m by ring]
      exact ((sForsTree_nb (c := c) (by omega) hb).mono (by omega)).append
        (sForsTrees_nb m (c + 1) (b + 233) (by omega) (by omega))

/-- **The FORS trees `c ..< c + m` complete**, from base `b`: tree `c + k`'s two top nodes are at
`b + 233 k + 229` and `b + 233 k + 230`. -/
theorem sForsTrees_complete {D : Nat} {pp I : E} {secret : Nat → E} {sib : Nat → Nat → E}
    (hsec : ∀ k, IsCanonical128 (secret k)) (hsib : ∀ k l, IsCanonical128 (sib k l)) (hI : IsCanonical128 I)
    (hppc : IsCanonical128 pp) :
    ∀ (m c b : Nat) (σ : Val), c + m ≤ 24 → 1225 ≤ b → PadOK σ sPad → σ sPP = pp → σ sIdx = I →
      BitsAt σ D → ValsAt σ D →
      Completes C rd b (b + 233 * m) (sForsTrees m c b).1 σ (fun σ' => ∀ k < m,
        (σ' (.n (b + 233 * k + 229)), σ' (.n (b + 233 * k + 230))) =
          fTops pp I (c + k) (fieldNat D (3 + (c + k))) (secret (c + k)) (sib (c + k)))
  | 0, c, b, σ, _, _, _, _, _, _, _ => by
      simp only [sForsTrees, Nat.mul_zero, Nat.add_zero]
      exact Completes.nil' fun k hk => absurd hk (by omega)
  | m + 1, c, b, σ, hcm, hb, hp, hpp, hidx, hbits, hvals => by
      rw [(sForsTrees_succ m c b).1, show b + 233 * (m + 1) = b + 233 + 233 * m by ring]
      refine Completes.append (m := b + 233) (by omega) (by omega) (sForsTree_nb (c := c) (by omega) hb)
        (sForsTree_complete (C := C) (rd := rd) (c := c) (by omega) (hsec c) (hsib c) hI hppc σ hb hp hpp hidx
          hbits hvals) (fun σ1 he1 h1 => ?_)
      have ag : AgreeBelow b σ σ1 := he1.agree
      have ih := sForsTrees_complete hsec hsib hI hppc m (c + 1) (b + 233) σ1 (by omega) (by omega)
        (hp.congr (b := b) (by unfold sPad; omega) ag)
        (by rw [show sPP = .n 2 from rfl, ← ag 2 (by omega)]; exact hpp)
        (by rw [sIdx_eq, ← ag 1067 (by omega), ← sIdx_eq]; exact hidx)
        (bitsAt_congr hbits (ag.mono (by omega))) (valsAt_congr hvals (ag.mono (by omega)))
      refine (ih.keep (Q := fun σ' => (σ' (.n (b + 229)), σ' (.n (b + 230))) = fTops pp I c (fieldNat D (3 + c))
          (secret c) (sib c))
        (Q' := fun σ' => (σ' (.n (b + 229)), σ' (.n (b + 230))) = fTops pp I c (fieldNat D (3 + c))
          (secret c) (sib c)) h1
        (fun σ' he q => by rw [he.apply (Or.inl (by omega)), he.apply (Or.inl (by omega))]; exact q)).mono
        le_rfl le_rfl (fun σ' ⟨q1, q2⟩ k hk => ?_)
      rcases k with _ | k
      · simpa using q2
      · have := q1 k (by omega)
        rw [show b + 233 + 233 * k + 229 = b + 233 * (k + 1) + 229 by ring,
          show b + 233 + 233 * k + 230 = b + 233 * (k + 1) + 230 by ring,
          show c + 1 + k = c + (k + 1) by omega] at this
        exact this

end
end LeanVM.Guest.B1.Sig
