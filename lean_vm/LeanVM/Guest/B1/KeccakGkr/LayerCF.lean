/-
  LeanVM.Guest.B1.KeccakGkr.LayerCF

  `keccak_layer`'s tail, completely: the final check, the squeeze of `β`, the next claim's record,
  the return.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerCE
public import LeanVM.Guest.B1.KeccakGkr.LayerCD

/-!
# The tail, completely

`layer_tail_complete`: on an evaluated valuation, with the last record's scale in memory, `t`'s packed
cells and the capacity canonical, the lane weights of the local point (at `loc`, in memory), and
the honest final check, `β` and the capacity are the squeeze's; and with the next claim's record
(its value, its pointers, its lanes and slices) in memory, the tail holds and returns the
capacity and the cursor past `t`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr LeanVM.Guest.B1.Fwd

@[expose] public section

variable {C : CallRel} {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val}

/-- The tail up to the squeeze of `β`. -/
def tailP1 (d W wv : ℕ) : List Stmt :=
  [.atom (.copy (.n W) (.n wv)), .atom (.load (.n (W + 1)) (.n (d + 1317)) 112),
    .atom (.mul (.n (W + 2)) (.n (W + 1)) (.n W)),
    .atom (.mul (.n (W + 3)) (.n 1215) (.n (d + 1986))),
    .atom (.add (.n (W + 4)) (.n 1215) (.n (d + 1996))),
    .atom (.mul (.n (W + 5)) (.n (W + 4)) (.n (d + 2006))),
    .atom (.add (.n (W + 6)) (.n (W + 3)) (.n (W + 5))),
    .atom (.mul (.n (W + 7)) (.n (W + 2)) (.n (W + 6))),
    .atom (.assertEq (.n (W + 7)) (.n (d + 1985))),
    .atom (.const (.n (W + 8)) (word 0 0 0)), .atom (.const (.n (W + 9)) (word 0 0 0)),
    keccakA ([.n (d + 1993), .n (d + 1995), .n (d + 2003), .n (d + 2005), .n (d + 2013),
      .n (d + 2015), .n (W + 8), .n (W + 9)] ++ cap5 (d + 1966))
      ((List.range 13).map fun k ↦ .n (W + 10 + k))]

/-- The next claim's value and pointers. -/
def tailP2 (d W : ℕ) : List Stmt :=
  [.atom (.mul (.n (W + 30)) (.n (W + 29)) (.n (d + 2006))),
    .atom (.add (.n (W + 31)) (.n (d + 1996)) (.n (W + 30))),
    .atom (.mul (.n (W + 32)) (.n (W + 29)) (.n (W + 31))),
    .atom (.add (.n (W + 33)) (.n (d + 1986)) (.n (W + 32))),
    .atom (.load (.n (W + 33)) (.n 12) 0), .atom (.load (.n 1309) (.n 12) 2),
    .atom (.load (.n (d + 1325)) (.n 12) 4), .atom (.hint (.alloc (.n (W + 34)) 25))]

/-- The slices stored. -/
def tailSl (W : ℕ) : List Stmt :=
  (List.range 64).map (fun z ↦ .atom (.load (.n (eqfVal (W + 135) 6 64 5 z)) (.n (W + 278)) z))

/-- The return's copies. -/
def tailP3 (d W : ℕ) : List Stmt :=
  (List.range 5).map (fun j ↦ .atom (.copy (.n (W + 279 + j)) (.n (W + 18 + j)))) ++
  [.atom (.const (.n (W + 284)) (word 68719476736 0 0)),
    .atom (.mul (.n (W + 285)) (.n (d + 1323)) (.n (W + 284))),
    .atom (.copy (.n (W + 286)) (.n (W + 285)))]

/-- The local point's equality weights, for the slices. -/
def tailEqf (d W : ℕ) : List Stmt := eqfT (.n (d + 1325)) 0 6 64 (W + 135)

/-- The tail but its return. -/
def tailPre (d W wv : ℕ) : List Stmt :=
  tailP1 d W wv ++ challengeT (.n (W + 10)) (.n (W + 11)) (W + 23) ++ tailP2 d W ++
    lanesOutT (W + 29) (laneW d) (W + 34) (W + 35) ++ [.atom (.load (.n (W + 34)) (.n 12) 3)] ++
    tailEqf d W ++ [.atom (.hint (.alloc (.n (W + 278)) 64))] ++ tailSl W ++
    [.atom (.load (.n (W + 278)) (.n 12) 5)] ++ tailP3 d W

theorem tailT_split (d W wv : ℕ) : tailT d W wv = tailPre d W wv ++
    [.ret [.n (W + 279), .n (W + 280), .n (W + 281), .n (W + 282), .n (W + 283), .n (W + 286)]] := by
  simp [tailT, tailPre, tailP1, tailP2, tailP3, tailSl, tailEqf, keccakA, List.append_assoc]

/-- The canonical inputs of the squeeze of `β`. -/
def tailA (d : ℕ) : List ℕ :=
  [d + 1993, d + 1995, d + 2003, d + 2005, d + 2013, d + 2015, d + 1966, d + 1967, d + 1968,
    d + 1969, d + 1970]

/-- The residual atoms of the tail before and after the slices' weights. -/
def tailR1 (d W : ℕ) : List Atom :=
  [.load (.n (W + 1)) (.n (d + 1317)) 112, .assertEq (.n (W + 7)) (.n (d + 1985)),
    .assertInK (.n (W + 23)) (.n (W + 26)), .load (.n (W + 33)) (.n 12) 0,
    .load (.n 1309) (.n 12) 2, .load (.n (d + 1325)) (.n 12) 4] ++
  (List.range 25).map (fun i ↦ .load (.n (W + 38 + 4 * i)) (.n (W + 34)) i) ++
  [.load (.n (W + 34)) (.n 12) 3]

def tailR2 (W : ℕ) : List Atom :=
  (List.range 64).map (fun z ↦ .load (.n (eqfVal (W + 135) 6 64 5 z)) (.n (W + 278)) z) ++
    [.load (.n (W + 278)) (.n 12) 5]

theorem tail_kernel {first odd : ℕ} (hf : first < 2) (ho : odd < 2) :
    (tailPre (4 * odd) (weightEnd first (4 * odd)) (weightVal first (4 * odd))).all isAtom = true ∧
    canonChk (tailA (4 * odd)) (atomsL ([] ++ tailPre (4 * odd) (weightEnd first (4 * odd))
      (weightVal first (4 * odd)))) = true ∧
    resid (atomsL (tailPre (4 * odd) (weightEnd first (4 * odd)) (weightVal first (4 * odd)))) =
      tailR1 (4 * odd) (weightEnd first (4 * odd)) ++
        resid (atomsL (tailEqf (4 * odd) (weightEnd first (4 * odd)))) ++
        tailR2 (weightEnd first (4 * odd)) ∧
    (tailEqf (4 * odd) (weightEnd first (4 * odd))).all isAtom = true ∧
    canonChk [] (atomsL ([] ++ tailEqf (4 * odd) (weightEnd first (4 * odd)))) = true ∧
    (resid (atomsL (tailEqf (4 * odd) (weightEnd first (4 * odd))))).all
      (ldIn [(.n (4 * odd + 1325), 6)]) = true ∧
    weightVal first (4 * odd) < weightEnd first (4 * odd) ∧
    4 * odd + 2006 < weightEnd first (4 * odd) ∧
    (List.range 25).all (fun j ↦ decide (laneW (4 * odd) j < weightEnd first (4 * odd))) = true := by
  interval_cases first <;> interval_cases odd
  all_goals exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The squeeze of `β`: after the capacity of the last position round, `t`'s three words. -/
def tailSq (σ : Val) (d : ℕ) : E × Fs :=
  sq3 ((cap5 (d + 1966)).map σ) (σ (.n (d + 1986))) (σ (.n (d + 1996))) (σ (.n (d + 2006)))

set_option maxRecDepth 20000 in
/-- **The tail, completely.** -/
theorem layer_tail_complete {first odd : ℕ} (hf : first < 2) (ho : odd < 2)
    (hσ : ∀ v, σ v = σ (.n v.idx))
    (hg : ∀ s ∈ tailPre (4 * odd) (weightEnd first (4 * odd)) (weightVal first (4 * odd)),
      GoodS rd S w σ s)
    (hS1 : Atom.load (.n (weightEnd first (4 * odd) + 1)) (.n (4 * odd + 1317)) 112 ∉ S)
    (hSe : ∀ a ∈ resid (atomsL (tailEqf (4 * odd) (weightEnd first (4 * odd)))), a ∉ S)
    (hA : ∀ i ∈ tailA (4 * odd), IsCanonical128 (σ (.n i)))
    (p1 : FsPackOk σ (.n (4 * odd + 1986)) (4 * odd + 1986 + 1) dsObserve)
    (p2 : FsPackOk σ (.n (4 * odd + 1996)) (4 * odd + 1996 + 1) dsObserve)
    (p3 : FsPackOk σ (.n (4 * odd + 2006)) (4 * odd + 2006 + 1) dsObserve)
    {locPt : List E} (hlocL : locPt.length = 11) (hloc : ReadsAt rd (σ (.n (4 * odd + 1325))) locPt)
    (hfw : ∀ i < 25, σ (.n (laneW (4 * odd) i)) = eqAt (locPt.drop 6) i)
    {scL : E} (hsc : LoadHolds rd (σ (.n (4 * odd + 1317))) 112 scL)
    (hfin : scL * σ (.n (weightVal first (4 * odd))) * (σ (.n 1215) * σ (.n (4 * odd + 1986)) +
      (σ (.n 1215) + σ (.n (4 * odd + 1996))) * σ (.n (4 * odd + 2006))) =
      σ (.n (4 * odd + 1985))) :
    σ (.n (weightEnd first (4 * odd) + 29)) = (tailSq σ (4 * odd)).1 ∧
      (cap5 (weightEnd first (4 * odd) + 18)).map σ = (tailSq σ (4 * odd)).2.cap ∧
      ∀ {next : Prop} {kret : List E → Prop},
        LoadHolds rd (σ (.n 12)) 0 (σ (.n (4 * odd + 1986)) + (tailSq σ (4 * odd)).1 *
          (σ (.n (4 * odd + 1996)) + (tailSq σ (4 * odd)).1 * σ (.n (4 * odd + 2006)))) →
        LoadHolds rd (σ (.n 12)) 2 (σ (.n 1309)) →
        LoadHolds rd (σ (.n 12)) 4 (σ (.n (4 * odd + 1325))) →
        LoadHolds rd (σ (.n 12)) 3 (σ (.n (weightEnd first (4 * odd) + 34))) →
        ReadsAt rd (σ (.n (weightEnd first (4 * odd) + 34))) (lanesOut locPt (tailSq σ (4 * odd)).1) →
        LoadHolds rd (σ (.n 12)) 5 (σ (.n (weightEnd first (4 * odd) + 278))) →
        ReadsAt rd (σ (.n (weightEnd first (4 * odd) + 278))) (eqKernel (locPt.take 6)) →
        kret ((cap5 (weightEnd first (4 * odd) + 18)).map σ ++
          [σ (.n (4 * odd + 1323)) * gen ^ 36]) →
        Stmt.HoldsList C rd σ (tailT (4 * odd) (weightEnd first (4 * odd))
          (weightVal first (4 * odd))) next kret := by
  obtain ⟨hall, hk, hr, halle, hke, hre, hwv, h2006, hlw0⟩ := tail_kernel hf ho
  generalize weightEnd first (4 * odd) = W at *
  generalize weightVal first (4 * odd) = wv at *
  generalize 4 * odd = d at *
  have mem : ∀ s, s ∈ tailPre d W wv → GoodS rd S w σ s := hg
  unfold tailPre at mem
  have g1 : ∀ s ∈ tailP1 d W wv, GoodS rd S w σ s := fun s hs ↦ mem s (by simp [hs])
  have gc : ∀ s ∈ challengeT (.n (W + 10)) (.n (W + 11)) (W + 23), GoodS rd S w σ s :=
    fun s hs ↦ mem s (by simp [hs])
  have g2 : ∀ s ∈ tailP2 d W, GoodS rd S w σ s := fun s hs ↦ mem s (by simp [hs])
  have gl : ∀ s ∈ lanesOutT (W + 29) (laneW d) (W + 34) (W + 35), GoodS rd S w σ s :=
    fun s hs ↦ mem s (by simp [hs])
  have ge : ∀ s ∈ tailEqf d W, GoodS rd S w σ s := fun s hs ↦ mem s (by simp [hs])
  have g3 : ∀ s ∈ tailP3 d W, GoodS rd S w σ s := fun s hs ↦ mem s (by simp [hs])
  -- the final check's values
  have g1' := g1
  simp only [tailP1, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true] at g1'
  obtain ⟨e0, l1, e2, e3, e4, e5, e6, e7, -, z0, z1, gk⟩ := g1'
  simp only [GoodS, Good] at e0 e4 e6 z0 z1
  have e1 := load_val (w := w) l1 hS1 hsc
  have e2' := mul_good (by omega) (by omega) e2
  have e3' := mul_good (by omega) (by omega) e3
  have e5' := mul_good (by omega) (by omega) e5
  have e7' := mul_good (by omega) (by omega) e7
  -- the squeeze of `β`
  have zc : IsCanonical128 (word 0 0 0) := by
    rw [word_zero]; unfold IsCanonical128; exact limb_zero 2
  have hcanI : AllCanonical (([V.n (d + 1993), .n (d + 1995), .n (d + 2003), .n (d + 2005),
      .n (d + 2013), .n (d + 2015), .n (W + 8), .n (W + 9)] ++ cap5 (d + 1966)).map σ) := by
    intro c hc
    simp only [cap5, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    have h' := fun i hi ↦ hA i hi
    simp only [tailA, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at h'
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := h'
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact a0
    · exact a1
    · exact a2
    · exact a3
    · exact a4
    · exact a5
    · rw [z0]; exact zc
    · rw [z1]; exact zc
    · exact a6
    · simpa [Nat.add_assoc] using a7
    · simpa [Nat.add_assoc] using a8
    · simpa [Nat.add_assoc] using a9
    · simpa [Nat.add_assoc] using a10
  have kc := keccakA_complete (show Good rd S w σ (.keccak _ ((List.range 13).map fun k ↦
    .n (W + 10 + k)) false false) from gk) hcanI
  obtain ⟨-, -, -, hout⟩ := keccak_outs kc
  have c11 : IsCanonical128 (σ (.n (W + 11))) := by
    have := hout 1 (by norm_num)
    simp only [range13_map, List.getD_cons_succ, List.getD_cons_zero] at this
    rw [this]; exact cellsOfState_canonical _ _ _
  obtain ⟨ch, fc⟩ := challenge_complete (C := C) gc c11
  have hsq := sq3_atoms (a := d + 1986) (o := W + 10) (cap := (cap5 (d + 1966)).map σ) p1
    (by simpa [Nat.add_assoc] using p2) (by simpa [Nat.add_assoc] using p3)
    (by simpa [cap5, Nat.add_assoc] using kc) (by simpa [Nat.add_assoc] using ch)
    (by rw [z0, word_zero]) (by rw [z1, word_zero]) rfl
  simp only [Nat.add_assoc, Nat.reduceAdd] at hsq
  have eβ : σ (.n (W + 29)) = (tailSq σ d).1 := by
    rw [tailSq, sq3]; simpa [Nat.add_assoc] using hsq.1
  have ecap : (cap5 (W + 18)).map σ = (tailSq σ d).2.cap := by
    rw [tailSq, sq3, ← hsq.2]
    simp [cap5, Nat.add_assoc]
  refine ⟨eβ, ecap, fun {next kret} ho0 ho2 ho4 ho3 hlan ho5 hsl hret ↦ ?_⟩
  -- the next claim's value
  have g2' := g2
  simp only [tailP2, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true] at g2'
  obtain ⟨f30, f31, f32, f33, -, -, -, -⟩ := g2'
  simp only [GoodS, Good] at f31 f33
  have f30' := mul_good (by omega) (by omega) f30
  have f32' := mul_good (by omega) (by omega) f32
  have ev : σ (.n (W + 33)) = σ (.n (d + 1986)) + (tailSq σ d).1 *
      (σ (.n (d + 1996)) + (tailSq σ d).1 * σ (.n (d + 2006))) := by
    rw [f33, f32', f31, f30', eβ]
  -- the lanes' values
  have hlv : ∀ i < 25, σ (.n (W + 38 + 4 * i)) = (lanesOut locPt (tailSq σ d).1).getD i 0 := by
    intro i hi
    have gi := fun s hs ↦ gl s (List.mem_flatten.mpr ⟨_, List.mem_map.mpr
      ⟨i, List.mem_range.mpr hi, rfl⟩, hs⟩)
    simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
      and_true] at gi
    obtain ⟨a0, a1, a2, a3, -⟩ := gi
    simp only [GoodS, Good] at a1 a3
    have hlw : ∀ j < 25, laneW d j < W := fun j hj ↦ by
      have := List.all_eq_true.mp hlw0 j (List.mem_range.mpr hj)
      simpa using this
    have hl3 := hlw ((i % 5 + 3) % 5 + 5 * (i / 5)) (by omega)
    have a0' := mul_good (h := a0) (by omega) (by omega)
    have a2' := mul_good (h := a2) (by omega) (by omega)
    rw [show W + 35 + 4 * i + 3 = W + 38 + 4 * i by omega] at a3
    rw [a3, a2', a1, a0', eβ, hfw i hi, hfw _ (by omega), hfw _ (by omega)]
    simp only [lanesOut, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
      Option.map_some, Option.getD_some]
  -- the slices' values
  have hEq : ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList C rd σ (tailEqf d W) next kret :=
    block_holdsP (P := []) halle hσ hke (by simpa using ge) (A := []) (by simp)
      (resid_ldIn hre hSe fun q hq ↦ by
        simp only [List.mem_singleton] at hq
        subst hq
        exact ⟨locPt, hloc, by omega⟩)
  obtain ⟨⟨rs, hrsL, hrs, hent⟩, -⟩ := eqfT_holds (pt := .n (d + 1325)) (off := 0) (n := 6)
    (count := 64) (b := W + 135) (by norm_num) (by norm_num) (by decide) (by decide)
    (hEq (kret := fun _ ↦ True) trivial)
  have hrs6 : rs = locPt.take 6 := by
    apply List.ext_getElem (by simp [hrsL, hlocL])
    intro k h1 h2
    have := hloc k (by omega)
    have h' := hrs k h1
    rw [Nat.zero_add] at h'
    rw [List.getElem_take]
    exact loadHolds_unique h' this
  have hsv : ∀ z < 64, σ (.n (eqfVal (W + 135) 6 64 5 z)) = (eqKernel (locPt.take 6)).getD z 0 := by
    intro z hz
    rw [eqKernel_getD, ← hrs6, hrsL]
    simp only [show z < 2 ^ 6 by omega, ↓reduceIte]
    exact hent z hz
  -- the return
  have g3' := g3
  simp only [tailP3, List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil,
    IsEmpty.forall_iff, implies_true, and_true, List.mem_map, List.mem_range,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at g3'
  obtain ⟨hcp, c84, c85, c86⟩ := g3'
  simp only [GoodS, Good] at c84 c86
  have c85' := mul_good (by omega) (by omega) c85
  have hcp' : ∀ j < 5, σ (.n (W + 279 + j)) = σ (.n (W + 18 + j)) := fun j hj ↦ by
    have := hcp j hj
    simpa [GoodS, Good] using this
  -- the block
  rw [tailT_split, holdsList_append]
  refine block_holdsP (P := []) hall hσ hk (by simpa using hg) hA ?_ ?_
  · rw [hr]
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · simp only [tailR1, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
          List.mem_map, List.mem_range] at ha
        rcases ha with ((rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩) | rfl
        · exact Or.inr (side_load hS1 hsc)
        · left
          show σ (.n (W + 7)) + σ (.n (d + 1985)) = 0
          rw [e7', e2', e1, e0, e6, e3', e5', e4, ← hfin]
          exact e_add_self _
        · exact Or.inl ⟨ch.2.2.2.1, ch.2.2.2.2.1⟩
        · left
          show LoadHolds rd _ _ _
          rw [ev]; exact ho0
        · exact Or.inl ho2
        · exact Or.inl ho4
        · left
          show LoadHolds rd _ _ _
          rw [hlv i hi]
          have := hlan i (by simp [lanesOut]; omega)
          rwa [List.getD_eq_getElem _ _ (by simp [lanesOut]; omega)]
        · exact Or.inl ho3
      · exact resid_ldIn hre hSe (fun q hq ↦ by
          simp only [List.mem_singleton] at hq
          subst hq
          exact ⟨locPt, hloc, by omega⟩) a ha
    · simp only [tailR2, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at ha
      rcases ha with ⟨z, hz, rfl⟩ | rfl
      · left
        show LoadHolds rd _ _ _
        rw [hsv z hz]
        have hz' : z < (eqKernel (locPt.take 6)).length := by
          rw [eqKernel_length]; simp [hlocL]; omega
        rw [List.getD_eq_getElem _ _ hz']
        exact hsl z hz'
      · exact Or.inl ho5
  · simp only [Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil]
    convert hret using 1
    have h0 := hcp' 0 (by omega)
    have h1 := hcp' 1 (by omega)
    have h2 := hcp' 2 (by omega)
    have h3 := hcp' 3 (by omega)
    have h4 := hcp' 4 (by omega)
    simp only [Nat.add_zero, Nat.add_assoc, Nat.reduceAdd] at h0 h1 h2 h3 h4
    simp only [cap5, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      Nat.add_assoc, Nat.reduceAdd, h0, h1, h2, h3, h4, c86, c85', c84, word_2p36]

end
end LeanVM.Guest.B1.VerifySub
