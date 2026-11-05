/-
  LeanVM.Guest.B1.Sig.SphincsPathComplete

  A path in one tree of `verify_sig_lean_sphincs`'s hypertree (`sp_path`, `lean_ethereum.py:3847-3864`
  at leanVM `9d8bce81`) is complete: each level's children hinted in the order of the leaf index's
  bit, the parent hashed at the tree's node address.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsForsComplete

/-!
# A hypertree path, complete

* `tAdr`, `tNode`: the node address `lane + TW_NODE + (l + 1)·2^32 + (e >> (l + 1))` of the tree
  whose address's high lane is `lane` and the node above level `l` on the path of the leaf `e`;
* `sPath_eq_last`, `sPath_eq_step`, `sPath_shape`, `sPath_nb`: the template's levels;
* `sPath_complete`: the path from the leaf `v` reaches `pFold (tNode …) h v`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat kToNat)

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- The address of the node above level `l` whose index is `q`, in the tree of the lane `L`. -/
def tAdr (L : E) (l q : Nat) : E := L + word (tw 3 + (l + 1) * hiMul) 0 0 + eOfNat q

/-- The node above level `l` on the path of leaf `e`, from the node `v` at `l` and the sibling. -/
def tNode (pp L : E) (e : Nat) (sib : Nat → E) (l : Nat) (v : E) : E :=
  (hcell [pp, tAdr L l (e >>> (l + 1)), (mPair (e.testBit l) v (sib l)).1, (mPair (e.testBit l) v (sib l)).2]).1

theorem canon_tAdr {L : E} (hL : IsCanonical128 L) (l q : Nat) : IsCanonical128 (tAdr L l q) :=
  canon_add (canon_add hL (canon_word _ _)) (canon_eOfNat _)

theorem sPath_eq_last (lane : V) (off l : Nat) (cur : V) (x : Nat) :
    sPath lane off 1 l cur x = ([hintW "siblings" [.n x, .n (x + 1)], addS (.n (x + 2)) cur (.n x),
      addS (.n (x + 3)) (.n x) (.n (x + 1)), mulS (.n (x + 2)) (sBit (off + l)) (.n (x + 3)),
      cst (x + 4) (word (tw 3 + (l + 1) * hiMul) 0 0)] ++ [addS (.n (x + 5)) lane (.n (x + 4))] ++
      k64 sPad sPP (.n (x + 6 - 1)) (.n x) (.n (x + 1)) (x + 6) (x + 6 + 1), x + 20, .n (x + 7)) := by
  simp [sPath, isChildS]

theorem sPath_eq_step (lane : V) (off m l : Nat) (cur : V) (x : Nat) :
    sPath lane off (m + 2) l cur x = (([hintW "siblings" [.n x, .n (x + 1)], addS (.n (x + 2)) cur (.n x),
      addS (.n (x + 3)) (.n x) (.n (x + 1)), mulS (.n (x + 2)) (sBit (off + l)) (.n (x + 3)),
      cst (x + 4) (word (tw 3 + (l + 1) * hiMul) 0 0)] ++
      [addS (.n (x + 5)) lane (.n (x + 4)), addS (.n (x + 6)) (.n (x + 5)) (sVal (off + l + 1))] ++
      k64 sPad sPP (.n (x + 7 - 1)) (.n x) (.n (x + 1)) (x + 7) (x + 7 + 1)) ++
        (sPath lane off (m + 1) (l + 1) (.n (x + 8)) (x + 21)).1,
      (sPath lane off (m + 1) (l + 1) (.n (x + 8)) (x + 21)).2.1,
      (sPath lane off (m + 1) (l + 1) (.n (x + 8)) (x + 21)).2.2) := by
  simp [sPath, isChildS]

theorem sPath_shape (lane : V) (off : Nat) : ∀ (m l : Nat) (cur : V) (x : Nat),
    (sPath lane off (m + 1) l cur x).2.1 = x + 21 * (m + 1) - 1 ∧
      (sPath lane off (m + 1) l cur x).2.2 = .n (x + 21 * (m + 1) - 14)
  | 0, l, cur, x => by rw [sPath_eq_last]; simp
  | m + 1, l, cur, x => by
      rw [sPath_eq_step]
      obtain ⟨h1, h2⟩ := sPath_shape lane off m (l + 1) (.n (x + 8)) (x + 21)
      refine ⟨by rw [h1]; omega, by rw [h2]; congr 1; omega⟩

theorem sPath_nb {lane : V} {off : Nat} (hoff : off ≤ 16) : ∀ (m l : Nat) (cur : V) (x : Nat),
    l + m + 1 ≤ 10 → 1225 ≤ x → NBv x lane → NBv x cur →
      NumBelow (x + 21 * (m + 1) - 1) (Stmt.valsList (sPath lane off (m + 1) l cur x).1)
  | 0, l, cur, x, hlm, hx, hl, hc => by
      rw [sPath_eq_last]
      have h := pairLevel_numBelow "siblings" (pad := sPad) (pp := sPP) (bit := sBit (off + l)) (cur := cur)
        (b := x) (c := x + 6) (w := tw 3 + (l + 1) * hiMul) (nodeL := [addS (.n (x + 5)) lane (.n (x + 4))])
        (by unfold sPad; omega) ⟨2, by omega, rfl⟩ ⟨51 + (off + l), by omega, rfl⟩ hc
        ⟨rfl, ⟨rfl, hl.mono' (by omega), ⟨x + 4, by omega, rfl⟩⟩, rfl⟩ (by omega)
      exact h.mono (by omega)
  | m + 1, l, cur, x, hlm, hx, hl, hc => by
      rw [sPath_eq_step]
      dsimp only
      obtain ⟨k, hk, ek⟩ := sVal_nb (i := off + l + 1) (by omega)
      have h := pairLevel_numBelow "siblings" (pad := sPad) (pp := sPP) (bit := sBit (off + l)) (cur := cur)
        (b := x) (c := x + 7) (w := tw 3 + (l + 1) * hiMul)
        (nodeL := [addS (.n (x + 5)) lane (.n (x + 4)), addS (.n (x + 6)) (.n (x + 5)) (sVal (off + l + 1))])
        (by unfold sPad; omega) ⟨2, by omega, rfl⟩ ⟨51 + (off + l), by omega, rfl⟩ hc
        ⟨rfl, ⟨rfl, hl.mono' (by omega), ⟨x + 4, by omega, rfl⟩⟩, ⟨rfl, ⟨x + 5, by omega, rfl⟩, ⟨k, by omega, ek⟩⟩,
          rfl⟩ (by omega)
      have ih := sPath_nb hoff m (l + 1) (.n (x + 8)) (x + 21) (by omega) (by omega) (hl.mono' (by omega))
        ⟨x + 8, by omega, rfl⟩
      rw [valsList_append]
      exact (h.mono (by omega)).append (ih.mono (by omega))

/-- **A path completes** from level `l`, `m + 1` levels to the top of a tree of height `l + m + 1`:
each level's children hinted in the order of the leaf `e`'s bit, the node reached the fold. -/
theorem sPath_complete {lane : V} {off : Nat} (hoff : off ≤ 16) {e : Nat} {pp L : E} {sib : Nat → E}
    (hsib : ∀ l, IsCanonical128 (sib l)) (hL : IsCanonical128 L) (hppc : IsCanonical128 pp) :
    ∀ (m l : Nat) (cur : V) (x : Nat) (σ : Val), l + m + 1 ≤ 10 → e < 2 ^ (l + m + 1) → 1225 ≤ x →
      NBv x lane → NBv x cur → PadOK σ sPad → σ sPP = pp → σ lane = L →
      (∀ j < l + m + 1, σ (sBit (off + j)) = if e.testBit j then 1 else 0) →
      (∀ j, j + 1 < l + m + 1 → σ (sVal (off + j + 1)) = eOfNat (e >>> (j + 1))) → IsCanonical128 (σ cur) →
      Completes C rd x (x + 21 * (m + 1) - 1) (sPath lane off (m + 1) l cur x).1 σ
        (fun σ' => σ' (sPath lane off (m + 1) l cur x).2.2 = nIter (tNode pp L e sib) l (m + 1) (σ cur) ∧
          IsCanonical128 (σ' (sPath lane off (m + 1) l cur x).2.2))
  | 0, l, cur, x, σ, hlm, he, hx, hlane, hcur, hp, hpp, hL', hbits, hvals, hcc => by
      set bt := e.testBit l with hbt
      set kids := mPair bt (σ cur) (sib l) with hkids
      set g : Nat → E := fun j => if j = 0 then kids.1 else kids.2 with hg
      have hppx : NBv x sPP := ⟨2, by omega, rfl⟩
      have hbl : NBv x (sBit (off + l)) := ⟨51 + (off + l), by omega, rfl⟩
      have tk : ∀ v, NBv x v → updRun σ x 2 g v = σ v := fun v hv => updRun_below σ x 2 g hv
      have hpk : PadOK (updRun σ x 2 g) sPad := hp.congr (b := x) (by unfold sPad; omega)
        (fun j hj => (tk (.n j) ⟨j, hj, rfl⟩).symm)
      have hkid : updRun σ x 2 g (.n x) = (mPair bt (updRun σ x 2 g cur) (sib l)).1 ∧
          updRun σ x 2 g (.n (x + 1)) = (mPair bt (updRun σ x 2 g cur) (sib l)).2 := by
        rw [tk _ hcur]
        have h0 := updRun_at σ x 2 g (j := 0) (by norm_num)
        rw [Nat.add_zero] at h0
        exact ⟨h0, updRun_at σ x 2 g (j := 1) (by norm_num)⟩
      have hbv : updRun σ x 2 g (sBit (off + l)) = if bt then 1 else 0 := by
        rw [tk _ hbl]; exact hbits l (by omega)
      refine Completes.reload ((updRun_ext σ x 2 g).mono le_rfl (by omega)) ?_
      rw [sPath_eq_last]
      dsimp only
      have hq : e >>> (l + 1) = 0 := by
        rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt (by simpa using he)
      have hlev := pairLevel_complete (C := C) (rd := rd) "siblings" (pad := sPad) (pp := sPP)
        (bit := sBit (off + l)) (cur := cur) (b := x) (c := x + 6) (w := tw 3 + (l + 1) * hiMul)
        (nodeL := [addS (.n (x + 5)) lane (.n (x + 4))]) (updRun σ x 2 g) hpk (by unfold sPad; omega) hppx hbl hcur
        ⟨rfl, ⟨rfl, hlane.mono' (by omega), ⟨x + 4, by omega, rfl⟩⟩, rfl⟩ (by omega)
        (Aval := tAdr L l (e >>> (l + 1)))
        (fun σ' hag hh => by
          have c4 := hh.atom (a := .const (.n (x + 4)) (word (tw 3 + (l + 1) * hiMul) 0 0)) (by simp [cst])
          have a5 := hh.atom (a := .add (.n (x + 5)) lane (.n (x + 4))) (by simp [addS])
          simp only [Atom.Holds] at c4 a5
          show σ' (.n (x + 5)) = _
          rw [a5, c4, hag.apply hlane, tk _ hlane, hL', tAdr, hq, Value.eOfNat_zero, add_zero])
        (canon_tAdr hL l _) (bt := bt) hbv (hsib l) (by rw [tk _ hcur]; exact hcc)
        (by rw [tk _ hppx, hpp]; exact hppc) hkid
      refine hlev.mono le_rfl (by omega) (fun σ' ⟨q1, q2, _, _⟩ => ⟨?_, q2⟩)
      rw [q1, tk _ hppx, hpp, tk _ hcur]
      rfl
  | m + 1, l, cur, x, σ, hlm, he, hx, hlane, hcur, hp, hpp, hL', hbits, hvals, hcc => by
      set bt := e.testBit l with hbt
      set kids := mPair bt (σ cur) (sib l) with hkids
      set g : Nat → E := fun j => if j = 0 then kids.1 else kids.2 with hg
      have hppx : NBv x sPP := ⟨2, by omega, rfl⟩
      have hbl : NBv x (sBit (off + l)) := ⟨51 + (off + l), by omega, rfl⟩
      have tk : ∀ v, NBv x v → updRun σ x 2 g v = σ v := fun v hv => updRun_below σ x 2 g hv
      have hpk : PadOK (updRun σ x 2 g) sPad := hp.congr (b := x) (by unfold sPad; omega)
        (fun j hj => (tk (.n j) ⟨j, hj, rfl⟩).symm)
      have hkid : updRun σ x 2 g (.n x) = (mPair bt (updRun σ x 2 g cur) (sib l)).1 ∧
          updRun σ x 2 g (.n (x + 1)) = (mPair bt (updRun σ x 2 g cur) (sib l)).2 := by
        rw [tk _ hcur]
        have h0 := updRun_at σ x 2 g (j := 0) (by norm_num)
        rw [Nat.add_zero] at h0
        exact ⟨h0, updRun_at σ x 2 g (j := 1) (by norm_num)⟩
      have hbv : updRun σ x 2 g (sBit (off + l)) = if bt then 1 else 0 := by
        rw [tk _ hbl]; exact hbits l (by omega)
      refine Completes.reload ((updRun_ext σ x 2 g).mono le_rfl (by omega)) ?_
      rw [sPath_eq_step]
      dsimp only
      obtain ⟨k, hk, ek⟩ := sVal_nb (i := off + l + 1) (by omega)
      have hvl : NBv x (sVal (off + l + 1)) := ⟨k, by omega, ek⟩
      have hlev := pairLevel_complete (C := C) (rd := rd) "siblings" (pad := sPad) (pp := sPP)
        (bit := sBit (off + l)) (cur := cur) (b := x) (c := x + 7) (w := tw 3 + (l + 1) * hiMul)
        (nodeL := [addS (.n (x + 5)) lane (.n (x + 4)), addS (.n (x + 6)) (.n (x + 5)) (sVal (off + l + 1))])
        (updRun σ x 2 g) hpk (by unfold sPad; omega) hppx hbl hcur
        ⟨rfl, ⟨rfl, hlane.mono' (by omega), ⟨x + 4, by omega, rfl⟩⟩, ⟨rfl, ⟨x + 5, by omega, rfl⟩,
          hvl.mono' (by omega)⟩, rfl⟩ (by omega)
        (Aval := tAdr L l (e >>> (l + 1)))
        (fun σ' hag hh => by
          have c4 := hh.atom (a := .const (.n (x + 4)) (word (tw 3 + (l + 1) * hiMul) 0 0)) (by simp [cst])
          have a5 := hh.atom (a := .add (.n (x + 5)) lane (.n (x + 4))) (by simp [addS])
          have a6 := hh.atom (a := .add (.n (x + 6)) (.n (x + 5)) (sVal (off + l + 1))) (by simp [addS])
          simp only [Atom.Holds] at c4 a5 a6
          show σ' (.n (x + 6)) = _
          rw [a6, a5, c4, hag.apply hlane, tk _ hlane, hL', hag.apply hvl, tk _ hvl, hvals l (by omega), tAdr])
        (canon_tAdr hL l _) (bt := bt) hbv (hsib l) (by rw [tk _ hcur]; exact hcc)
        (by rw [tk _ hppx, hpp]; exact hppc) hkid
      have hnb := pairLevel_numBelow "siblings" (pad := sPad) (pp := sPP) (bit := sBit (off + l)) (cur := cur)
        (b := x) (c := x + 7) (w := tw 3 + (l + 1) * hiMul)
        (nodeL := [addS (.n (x + 5)) lane (.n (x + 4)), addS (.n (x + 6)) (.n (x + 5)) (sVal (off + l + 1))])
        (by unfold sPad; omega) hppx hbl hcur
        ⟨rfl, ⟨rfl, hlane.mono' (by omega), ⟨x + 4, by omega, rfl⟩⟩, ⟨rfl, ⟨x + 5, by omega, rfl⟩,
          hvl.mono' (by omega)⟩, rfl⟩ (by omega)
      refine Completes.append (m := x + 7 + 14) (by omega) (by omega) hnb hlev (fun σ1 he1 ⟨hv1, hc1, _, _⟩ => ?_)
      have t1 : ∀ v, NBv x v → σ1 v = σ v := fun v hv => by
        obtain ⟨j, hj, rfl⟩ := hv
        rw [he1.apply (Or.inl hj), tk _ ⟨j, hj, rfl⟩]
      have ih := sPath_complete hoff hsib hL hppc m (l + 1) (.n (x + 8)) (x + 21) σ1 (by omega)
        (by rw [show l + 1 + m + 1 = l + (m + 1) + 1 by omega]; exact he) (by omega)
        (hlane.mono' (by omega)) ⟨x + 8, by omega, rfl⟩
        (hp.congr (b := x) (by unfold sPad; omega) (fun j hj => (t1 (.n j) ⟨j, hj, rfl⟩).symm))
        (by rw [t1 _ hppx]; exact hpp) (by rw [t1 _ hlane]; exact hL')
        (fun j hj => by
          rw [show sBit (off + j) = .n (51 + (off + j)) from rfl, t1 _ ⟨51 + (off + j), by omega, rfl⟩]
          exact hbits j (by omega))
        (fun j hj => by
          obtain ⟨k', hk', ek'⟩ := sVal_nb (i := off + j + 1) (by omega)
          rw [ek', t1 _ ⟨k', by omega, rfl⟩, ← ek']; exact hvals j (by omega)) hc1
      rw [show x + 7 + 14 = x + 21 by omega] at ih
      refine ih.mono (by omega) (by omega) (fun σ' ⟨q1, q2⟩ => ⟨?_, q2⟩)
      rw [q1, hv1, tk _ hppx, hpp, tk _ hcur]
      rfl

end
end LeanVM.Guest.B1.Sig
