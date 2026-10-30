/-
  LeanVM.Guest.B1.KeccakGkr.LayerSecC

  `keccak_layer`'s tail (G:2690-2718): the final check, the squeeze of `β`, the next claim's
  record, the return.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerT

/-!
# The tail

`tailT_holds`: from the local point (its lane weights `f` and its words at `loc`), `t`'s words
packed, and the capacity after the local rounds, the tail's statements give the final check, the
squeeze of `β` after `t`, the next claim's value, point, local point, lanes (`lanesOut`) and slices
(`eqKernel` of the local point's first six coordinates), and the return: the capacity after `β`
and the cursor past `t`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- The next claim's lanes. -/
theorem lanesOutT_holds {beta lp B : ℕ} {f : ℕ → ℕ} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (lanesOutT beta f lp B) next kret) :
    (∀ i < 25, σ (.n (B + 4 * i + 3)) = σ (.n (f i)) + σ (.n beta) *
        (σ (.n (f ((i % 5 + 4) % 5 + 5 * (i / 5)))) + σ (.n beta) *
          σ (.n (f ((i % 5 + 3) % 5 + 5 * (i / 5))))) ∧
      LoadHolds rd (σ (.n lp)) i (σ (.n (B + 4 * i + 3)))) ∧ next := by
  rw [lanesOutT, holdsList_range_flatten _ _ (fun _ ↦ rfl)] at h
  refine ⟨fun i hi ↦ ?_, h.2⟩
  have hi' := h.1 i hi
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hi'
  obtain ⟨e0, e1, e2, e3, l⟩ := hi'
  exact ⟨by rw [e3, e2, e1, e0], l⟩

theorem word_2p36 : word 68719476736 0 0 = gen ^ 36 := by
  rw [show (68719476736 : ℕ) = 2 ^ 36 from rfl]; exact word_two_pow (by decide)

/-- **The tail** (G:2690-2718). -/
theorem tailT_holds {d W wv : ℕ} {locPt : List E} (hlocL : locPt.length = 11)
    (hloc : ReadsAt rd (σ (.n (d + 1325))) locPt)
    (hf : ∀ i < 25, σ (.n (laneW d i)) = eqAt (locPt.drop 6) i)
    (p1 : FsPackOk σ (.n (d + 1986)) (d + 1986 + 1) dsObserve)
    (p2 : FsPackOk σ (.n (d + 1996)) (d + 1996 + 1) dsObserve)
    (p3 : FsPackOk σ (.n (d + 2006)) (d + 2006 + 1) dsObserve)
    {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (tailT d W wv) next kret) :
    LoadHolds rd (σ (.n (d + 1317))) 112 (σ (.n (W + 1))) ∧
      σ (.n (W + 1)) * σ (.n wv) * (σ (.n 1215) * σ (.n (d + 1986)) +
        (σ (.n 1215) + σ (.n (d + 1996))) * σ (.n (d + 2006))) = σ (.n (d + 1985)) ∧
      ((⟨(cap5 (d + 1966)).map σ, []⟩ : Fs).absorbAll
        [σ (.n (d + 1986)), σ (.n (d + 1996)), σ (.n (d + 2006))] dsObserve).squeeze =
        (σ (.n (W + 29)), ⟨(cap5 (W + 18)).map σ, []⟩) ∧
      LoadHolds rd (σ (.n 12)) 0 (σ (.n (d + 1986)) + σ (.n (W + 29)) *
        (σ (.n (d + 1996)) + σ (.n (W + 29)) * σ (.n (d + 2006)))) ∧
      LoadHolds rd (σ (.n 12)) 2 (σ (.n 1309)) ∧
      LoadHolds rd (σ (.n 12)) 4 (σ (.n (d + 1325))) ∧
      LoadHolds rd (σ (.n 12)) 3 (σ (.n (W + 34))) ∧
      ReadsAt rd (σ (.n (W + 34))) (lanesOut locPt (σ (.n (W + 29)))) ∧
      LoadHolds rd (σ (.n 12)) 5 (σ (.n (W + 278))) ∧
      ReadsAt rd (σ (.n (W + 278))) (eqKernel (locPt.take 6)) ∧
      kret ((cap5 (W + 18)).map σ ++ [σ (.n (d + 1323)) * gen ^ 36]) := by
  simp only [tailT, holdsList_append, List.append_assoc, holds_challengeT] at h
  simp only [Stmt.HoldsList, Stmt.Holds, keccakA] at h
  obtain ⟨e0, lsc, e2, e3, e4, e5, e6, e7, heq, z0, z1, hk, hch, h⟩ := h
  obtain ⟨o1, o2, o3, o4, lo0, lo2, lo4, -, h⟩ := h
  simp only [Atom.Holds] at e0 lsc e2 e3 e4 e5 e6 e7 heq z0 z1 o1 o2 o3 o4 lo0 lo2 lo4
  obtain ⟨hl, h⟩ := lanesOutT_holds h
  obtain ⟨lo3, h⟩ := h
  simp only [Atom.Holds] at lo3
  obtain ⟨⟨rs, hrsL, hrs, hent⟩, h⟩ := eqfT_holds (by omega) (by omega) (by decide) (by decide) h
  obtain ⟨-, h⟩ := h
  rw [holdsList_map_atoms] at h
  obtain ⟨hst, lo5, h⟩ := h
  rw [holdsList_map_atoms] at h
  obtain ⟨hcp, c0, c1, c2, hret⟩ := h
  simp only [Atom.Holds] at hst lo5 hcp c0 c1 c2
  have hsq := sq3_atoms (a := d + 1986) (o := W + 10) (cap := (cap5 (d + 1966)).map σ) p1
    (by simpa [Nat.add_assoc] using p2) (by simpa [Nat.add_assoc] using p3)
    (by simpa [cap5, Nat.add_assoc] using hk) (by simpa [Nat.add_assoc] using hch)
    (by rw [z0, word_zero]) (by rw [z1, word_zero]) rfl
  simp only [Nat.add_assoc, Nat.reduceAdd] at hsq
  have hrs6 : rs = locPt.take 6 := by
    apply List.ext_getElem (by simp [hrsL, hlocL])
    intro k h1 h2
    have := hloc k (by omega)
    simp only [Nat.zero_add] at hrs
    rw [List.getElem_take]
    exact loadHolds_unique (hrs k h1) this
  refine ⟨lsc, ?_, ?_, ?_, lo2, lo4, lo3, ?_, lo5, ?_, ?_⟩
  · rw [← eq_of_add_eq_zero' heq, e7, e6, e5, e4, e3, e2, e0]
  · refine Prod.ext hsq.1.symm ?_
    have hs : ∀ s : Fs, s.squeeze.2 = ⟨s.squeeze.2.cap, []⟩ := fun _ ↦ rfl
    rw [hs, ← hsq.2]
    rfl
  · rw [o4, o3, o2, o1] at lo0
    exact lo0
  · intro k hk
    simp only [lanesOut, List.length_map, List.length_range] at hk
    have := (hl k hk).2
    rw [(hl k hk).1, hf k hk, hf ((k % 5 + 4) % 5 + 5 * (k / 5)) (by omega),
      hf ((k % 5 + 3) % 5 + 5 * (k / 5)) (by omega)] at this
    simp only [lanesOut, List.getElem_map, List.getElem_range]
    exact this
  · intro k hk
    have hk' : k < 64 := by simpa [eqKernel_length, hlocL] using hk
    have e : (eqKernel (locPt.take 6))[k] = eqAt (locPt.take 6) k := by
      rw [← List.getD_eq_getElem _ 0 hk, eqKernel_getD]
      simp [hlocL, hk']
    rw [e, ← hrs6, ← hent k hk']
    exact hst k hk'
  · have h0 : σ (.n (W + 279)) = σ (.n (W + 18)) := by simpa using hcp 0 (by omega)
    have h1 : σ (.n (W + 280)) = σ (.n (W + 19)) := by simpa [Nat.add_assoc] using hcp 1 (by omega)
    have h2 : σ (.n (W + 281)) = σ (.n (W + 20)) := by simpa [Nat.add_assoc] using hcp 2 (by omega)
    have h3 : σ (.n (W + 282)) = σ (.n (W + 21)) := by simpa [Nat.add_assoc] using hcp 3 (by omega)
    have h4 : σ (.n (W + 283)) = σ (.n (W + 22)) := by simpa [Nat.add_assoc] using hcp 4 (by omega)
    convert hret using 1
    simp only [cap5, List.map_cons, List.map_nil, List.cons_append, List.nil_append, c2, c1, c0,
      word_2p36, h0, h1, h2, h3, h4, Nat.add_assoc, Nat.reduceAdd]

end
end LeanVM.Guest.B1.VerifySub
