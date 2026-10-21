/-
  LeanVM.Guest.B1.Comp.Sig.Arm

  The walks of one digit group's arm and the arm itself, complete over a completeness model
  (`cWalks_complete`, `armTail_complete`, `cArm_complete`).
-/

module

public import LeanVM.Guest.B1.Comp.Sig.Chain

/-!
# An arm over a completeness model

`Arm.lean`'s completeness over a `CompModel`: the tips preset to the model's chain ends
(`TipSetC`), each chain's steps answered (`TipAnsC`).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.E2E.Complete

@[expose] public section

variable {CM : CompModel} {C : CallRel} {rd : Reader}

/-- **An arm's walks are complete over the model** (`cWalks_complete`): from the values `xs`, their
steps answered, the tips preset to the chains' ends. -/
theorem cWalks_comp {w : Wots} {tips : Nat → V × V} {first k : Nat} {fresh : Bool} {xs : Nat → E} :
    ∀ (m r b : Nat) (σ : Val), w.Below b → TipsPos w.lx tips k fresh m r b →
      σ w.md = mdw (stepCount w.lx) true → w.Canon σ →
      (∀ r', r ≤ r' → r' < r + m →
        IsCanonical128 (xs r') ∧ TipAnsC CM w σ (first + r') (armDigit k r') (xs r') ∧
          TipSetC CM w σ (first + r') (armDigit k r') (xs r') (tips r')) →
      CompletesB CM.sem C rd b (cWalks w tips first k fresh m r b).2 (cWalks w tips first k fresh m r b).1 σ
        (fun σ' => ∀ r', r ≤ r' → r' < r + m → σ' (tips r').1 = σ (tips r').1 ∧ σ' (tips r').2 = σ (tips r').2)
  | 0, _, b, σ, _, _, _, _, _ => ⟨σ, Ext.refl _ _ _, fun _ _ _ => ⟨rfl, rfl⟩, fun _ _ hn => hn⟩
  | m + 1, r, b, σ, hw, hp, hmd, hc, hx => by
      rw [cWalks_eq]
      dsimp only
      obtain ⟨ho1, ho2, hb1, hb2⟩ := hp.head
      have hnext : b + walkSize w.lx (armDigit k r) ≤ walkNext w.lx fresh k r b := by
        unfold walkNext; omega
      refine CompletesB.append (m := walkNext w.lx fresh k r b)
        (P := fun σ' => Ext b (b + walkSize w.lx (armDigit k r)) σ σ') (by omega)
        (cWalks_snd w tips first k fresh m (r + 1) _) ?_ ?_ ?_
      · exact cWalk_below (hw.mono (by omega)) hb1 hb2 hnext
      · obtain ⟨hxc, hxa, hxs⟩ := hx r le_rfl (by omega)
        exact (cWalk_comp hw ho1 ho2 hmd hc hxc hxa hxs.1 hxs.2).withExt.mono le_rfl hnext fun _ h => h.2
      · intro σ' he hp'
        have hk := hw.keep he
        refine (cWalks_comp (xs := xs) m (r + 1) _ σ' (hw.mono (by omega))
          hp.tail (by rw [hk.2.2.2, hmd]) (hc.congr hk) fun r' h1 h2 => ?_).withExt.mono le_rfl le_rfl
          fun σ'' h => fun r' h1 h2 => ?_
        · obtain ⟨hxc, hxa, hxs⟩ := hx r' (by omega) (by omega)
          obtain ⟨o1, o2⟩ := hp.later (show r < r' by omega) (by omega)
          exact ⟨hxc, hxa.congr hk, hxs.congr hk (he.out o1) (he.out o2)⟩
        · by_cases e : r' = r
          · subst e
            have hb1' : Out (walkNext w.lx fresh k r' b) (cWalks w tips first k fresh m (r' + 1)
                (walkNext w.lx fresh k r' b)).2 (tips r').1 := out_of_lt hb1
            have hb2' : Out (walkNext w.lx fresh k r' b) (cWalks w tips first k fresh m (r' + 1)
                (walkNext w.lx fresh k r' b)).2 (tips r').2 := out_of_lt hb2
            exact ⟨(h.2.out hb1').trans (hp'.out ho1), (h.2.out hb2').trans (hp'.out ho2)⟩
          · obtain ⟨o1, o2⟩ := hp.later (show r < r' by omega) (by omega)
            have := h.1 r' (by omega) (by omega)
            exact ⟨this.1.trans (hp'.out (o1.mono le_rfl hnext)), this.2.trans (hp'.out (o2.mono le_rfl hnext))⟩

/-- The statements after an arm's walks complete under any model (`armTail_complete`). -/
theorem armTail_comp {power : Nat → V} {prodIn encIn prodOut encOut : V} {first n k : Nat}
    {fold : Bool} {b1 b : Nat} {σ : Val}
    (hlt : (∃ j < b1, prodIn = .n j) ∧ (∃ j < b1, encIn = .n j) ∧ (∃ j < b1, prodOut = .n j) ∧
      (∃ j < b1, encOut = .n j) ∧ (∃ j < b1, power (digitSum k n) = .n j) ∧ (fold = true → b < b1))
    (hprod : σ prodOut = (if fold then 1 else σ prodIn) * σ (power (digitSum k n)))
    (henc : σ encOut = (if fold then σ (.n b) else σ encIn) + lit (k * 4 ^ first)) :
    CompletesB CM.sem C rd b1 (b1 + (if k = 0 then 0 else 1))
      (armTail power prodIn encIn prodOut encOut first n k fold b1 b) σ (fun _ => True) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hlt
  by_cases hk : k = 0
  · subst hk
    refine ⟨σ, Ext.refl _ _ _, trivial, fun next kret hn => ?_⟩
    rw [Nat.zero_mul, lit_zero, add_zero] at henc
    cases fold <;> simp_all [armTail, mulS, Atom.HoldsB]
  · let σ' := Function.update σ (.n b1) (lit (k * 4 ^ first))
    have he : Ext b1 (b1 + 1) σ σ' := ext_update σ _ le_rfl (by omega)
    have hk' := fun {v : V} (hv : ∃ j < b1, v = .n j) => he.below hv
    refine ⟨σ', by simpa [hk] using he, trivial, fun next kret hn => ?_⟩
    have hb1 : σ' (.n b1) = lit (k * 4 ^ first) := by simp [σ']
    cases fold
    · simp only [armTail, hk, ↓reduceIte, Bool.false_eq_true, mulS, cst, addS, holdsListB_cons_atom,
        holdsListB_nil, Atom.HoldsB]
      rw [hk' h1, hk' h2, hk' h3, hk' h4, hk' h5, hb1]
      simp only [Bool.false_eq_true, ↓reduceIte] at hprod henc
      exact ⟨hprod, rfl, henc, hn⟩
    · simp only [armTail, hk, ↓reduceIte, cst, addS, holdsListB_cons_atom, holdsListB_nil, Atom.HoldsB]
      rw [hk' h3, hk' h4, hk' h5, hb1, hk' ⟨b, h6 rfl, rfl⟩]
      simp only [↓reduceIte, one_mul] at hprod henc
      exact ⟨hprod, rfl, henc, hn⟩

/-- **An arm is complete over the model** (`cArm_complete`): its tips, product and encoding preset
to what the arm computes, its chains answered. -/
theorem cArm_comp {w : Wots} {tips : Nat → V × V} {power : Nat → V}
    {prodIn encIn prodOut encOut : V} {first n k : Nat} {fold fresh : Bool} {b : Nat} {xs : Nat → E}
    {σ : Val} (hw : w.Below b) (hpos : TipsPos w.lx tips k fresh n 0 (if fresh then armStart fold b else b))
    (hout : if fresh then prodOut = .n (armWalksEnd w tips first n k fold fresh b) ∧
        encOut = .n (armWalksEnd w tips first n k fold fresh b + 1)
      else (∃ j < b, prodOut = .n j) ∧ (∃ j < b, encOut = .n j))
    (hin : (∃ j < b, prodIn = .n j) ∧ (∃ j < b, encIn = .n j) ∧ ∃ j < b, power (digitSum k n) = .n j)
    (hmd : σ w.md = mdw (stepCount w.lx) true) (hc : w.Canon σ)
    (hx : ∀ r < n, IsCanonical128 (xs r) ∧ TipAnsC CM w σ (first + r) (armDigit k r) (xs r) ∧
      TipSetC CM w σ (first + r) (armDigit k r) (xs r) (tips r))
    (hf : ArmFold σ power prodIn encIn prodOut encOut first n k fold) :
    CompletesB CM.sem C rd b (cArm w tips power prodIn encIn prodOut encOut first n k fold fresh b).2
      (cArm w tips power prodIn encIn prodOut encOut first n k fold fresh b).1 σ (fun σ' =>
        (∀ r < n, σ' (tips r).1 = σ (tips r).1 ∧ σ' (tips r).2 = σ (tips r).2) ∧
          σ' prodOut = σ prodOut ∧ σ' encOut = σ encOut) := by
  set e := armWalksEnd w tips first n k fold fresh b with he_def
  have hab : b ≤ armStart fold b := by unfold armStart; split <;> omega
  have he0 := armWalksEnd_ge w tips first n k fold fresh b
  rw [← he_def] at he0
  have hsnd := cArm_snd w tips power prodIn encIn prodOut encOut first n k fold fresh b
  rw [← he_def] at hsnd
  rw [hsnd]
  -- the outputs are outside the walks and the first constant
  have hO : Out b e prodOut ∧ Out b e encOut ∧ (∃ j < e + (if fresh then 2 else 0), prodOut = .n j) ∧
      ∃ j < e + (if fresh then 2 else 0), encOut = .n j := by
    cases fresh
    · simp only [Bool.false_eq_true, ↓reduceIte] at hout ⊢
      exact ⟨out_of_lt hout.1, out_of_lt hout.2, let ⟨j, hj, e'⟩ := hout.1; ⟨j, by omega, e'⟩,
        let ⟨j, hj, e'⟩ := hout.2; ⟨j, by omega, e'⟩⟩
    · simp only [↓reduceIte] at hout ⊢
      rw [hout.1, hout.2]
      exact ⟨out_of_ge ⟨e, le_rfl, rfl⟩, out_of_ge ⟨e + 1, by omega, rfl⟩, ⟨e, by omega, rfl⟩,
        ⟨e + 1, by omega, rfl⟩⟩
  have hpos' : TipsPos w.lx tips k fresh n 0 (armStart fold b) := by
    cases fresh
    · simp only [TipsPos, Bool.false_eq_true, ↓reduceIte] at hpos ⊢
      exact fun r h1' h2' => let ⟨⟨j1, h1, e1⟩, ⟨j2, h2, e2⟩⟩ := hpos r h1' h2'
        ⟨⟨j1, by omega, e1⟩, ⟨j2, by omega, e2⟩⟩
    · simpa using hpos
  have hk0 : fresh = true → k = 0 := fun h => by
    simp only [TipsPos, h, ↓reduceIte] at hpos; exact hpos.1
  -- the walks' tips are outside the first constant
  have htb : ∀ r < n, Out b (b + 1) (tips r).1 ∧ Out b (b + 1) (tips r).2 := by
    intro r hr
    cases fresh
    · simp only [TipsPos, Bool.false_eq_true, ↓reduceIte] at hpos
      exact ⟨out_of_lt (hpos r (Nat.zero_le _) (by omega)).1, out_of_lt (hpos r (Nat.zero_le _) (by omega)).2⟩
    · simp only [TipsPos, ↓reduceIte] at hpos
      rw [hpos.2 r (Nat.zero_le r) (by omega)]
      have : 1 ≤ walkSize w.lx 0 := by rw [walkSize_eq _ (by decide)]; omega
      exact ⟨out_of_ge ⟨_, by omega, rfl⟩, out_of_ge ⟨_, by omega, rfl⟩⟩
  have hpre : CompletesB CM.sem C rd b (armStart fold b) (if fold then [cst b (word 0 0 0)] else []) σ
      (fun σ' => fold = true → σ' (.n b) = 0) := by
    cases fold
    · exact ⟨σ, Ext.refl _ _ _, fun h => absurd h (by simp), fun _ _ hn => hn⟩
    · refine ⟨Function.update σ (.n b) 0, ext_update σ 0 le_rfl (by simp [armStart]), fun _ => by simp,
        fun next kret hn => ?_⟩
      simp [cst, Atom.HoldsB, word_zero, hn]
  have hend : (if fresh = true then e = armStart fold b + chainStride w.lx * n else True) := by
    cases fresh
    · trivial
    · simp only [↓reduceIte]
      rw [he_def, armWalksEnd, hk0 rfl, cWalks_snd_fresh]
  have htips : ∀ r', r' < n → (∃ j < e, (tips r').1 = .n j) ∧ (∃ j < e, (tips r').2 = .n j) := by
    intro r' hr'
    cases fresh
    · simp only [TipsPos, Bool.false_eq_true, ↓reduceIte] at hpos
      exact ⟨let ⟨j, hj, e'⟩ := (hpos r' (Nat.zero_le _) (by omega)).1; ⟨j, by omega, e'⟩,
        let ⟨j, hj, e'⟩ := (hpos r' (Nat.zero_le _) (by omega)).2; ⟨j, by omega, e'⟩⟩
    · simp only [TipsPos, ↓reduceIte] at hpos hend
      rw [hpos.2 r' (Nat.zero_le _) (by omega), Nat.sub_zero]
      have : chainStride w.lx * r' + chainStride w.lx ≤ chainStride w.lx * n := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hr'
      have hcs : chainStride w.lx = walkSize w.lx 0 + 2 := rfl
      exact ⟨⟨_, by omega, rfl⟩, ⟨_, by omega, rfl⟩⟩
  have hpe : (cWalks w tips first k fresh n 0 (armStart fold b)).2 = e := rfl
  rw [cArm_fst]
  refine CompletesB.append (m := e + (if fresh then 2 else 0)) (P := fun σ' => (fold = true → σ' (.n b) = 0) ∧
    Ext b e σ σ' ∧ ∀ r < n, σ' (tips r).1 = σ (tips r).1 ∧ σ' (tips r).2 = σ (tips r).2) (by omega) (by omega)
    ?_ ?_ ?_
  · rw [valsList_append]
    refine NumBelow.append ?_ ?_
    · cases fold
      · exact NumBelow.nil _
      · simp only [↓reduceIte, cst, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil]
        exact NumBelow.cons ⟨b, by simp only [armStart, ↓reduceIte] at he0; omega, rfl⟩ (NumBelow.nil _)
    · exact (cWalks_below (hw.mono (by omega)) _ _ _
        (fun r' _ h2 => let ⟨⟨j1, h1, e1⟩, ⟨j2, h2', e2⟩⟩ := htips r' (by omega)
          ⟨⟨j1, by omega, e1⟩, ⟨j2, by omega, e2⟩⟩) le_rfl).mono (by omega)
  · have hsb : armStart fold b ≤ b + 1 := by unfold armStart; split <;> omega
    refine CompletesB.append (m := armStart fold b) (P := fun σ' => fold = true → σ' (.n b) = 0) hab
      (by omega) ?_ hpre ?_
    · cases fold
      · exact NumBelow.nil _
      · simp only [↓reduceIte, cst, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil]
        exact NumBelow.cons ⟨b, by simp [armStart], rfl⟩ (NumBelow.nil _)
    · intro σ' he' hp
      have hk := hw.keep he'
      have hcw := cWalks_comp (CM := CM) (C := C) (rd := rd) (xs := xs) n 0 (armStart fold b) σ' (hw.mono hab)
        hpos' (by rw [hk.2.2.2, hmd]) (hc.congr hk) (fun r' _ h2 =>
          ⟨(hx r' (by omega)).1, (hx r' (by omega)).2.1.congr hk, (hx r' (by omega)).2.2.congr hk
            (he'.out ((htb r' (by omega)).1.mono le_rfl hsb))
            (he'.out ((htb r' (by omega)).2.mono le_rfl hsb))⟩)
      rw [hpe] at hcw
      refine hcw.withExt.mono le_rfl (by omega) fun σ'' h => ⟨fun hf => ?_, he'.trans h.2 hab he0,
        fun r hr => ?_⟩
      · rw [h.2.apply (Or.inl (by unfold armStart; simp [hf]))]
        exact hp hf
      · have := h.1 r (Nat.zero_le _) (by omega)
        exact ⟨this.1.trans (he'.out ((htb r hr).1.mono le_rfl hsb)),
          this.2.trans (he'.out ((htb r hr).2.mono le_rfl hsb))⟩
  · intro σ'' _ hp
    obtain ⟨hb0, hext, htips'⟩ := hp
    have hkb : ∀ {v : V}, (∃ j < b, v = .n j) → σ'' v = σ v := fun hv => hext.below hv
    refine (armTail_comp (CM := CM) (C := C) (rd := rd) (σ := σ'') ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_).withExt.mono le_rfl
      le_rfl fun σ3 h => ⟨fun r hr => ?_, ?_, ?_⟩
    · exact let ⟨j, hj, e'⟩ := hin.1; ⟨j, by omega, e'⟩
    · exact let ⟨j, hj, e'⟩ := hin.2.1; ⟨j, by omega, e'⟩
    · exact hO.2.2.1
    · exact hO.2.2.2
    · exact let ⟨j, hj, e'⟩ := hin.2.2; ⟨j, by omega, e'⟩
    · intro hf; subst hf; simp only [armStart, ↓reduceIte] at he0; omega
    · rw [hext.out hO.1, hkb hin.1, hkb hin.2.2]; exact hf.1
    · rw [hext.out hO.2.1, hkb hin.2.1, hf.2]
      cases fold
      · rfl
      · simp only [↓reduceIte, forall_const] at hb0 ⊢; rw [hb0]
    · obtain ⟨⟨j1, h1, e1⟩, ⟨j2, h2, e2⟩⟩ := htips r hr
      exact ⟨(h.2.below ⟨j1, by omega, e1⟩).trans (htips' r hr).1,
        (h.2.below ⟨j2, by omega, e2⟩).trans (htips' r hr).2⟩
    · exact (h.2.below hO.2.2.1).trans (hext.out hO.1)
    · exact (h.2.below hO.2.2.2).trans (hext.out hO.2.1)

end
end LeanVM.Guest.B1.Sig
