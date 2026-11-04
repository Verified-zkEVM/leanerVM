/-
  LeanVM.Guest.B1.Sig.SpWotsArmComplete

  An arm of `sp_wots`'s digit dispatch completes, its chains' starts loaded: evaluated with its
  padding run at the group's digit cells, then moved where the compiler allocates the run.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsArmFacts
public import LeanVM.Guest.B1.Sig.CwKeep

/-!
# An arm, complete

* `padPull σ B P`: the valuation the arm with its run at `B` is evaluated from: the run's
  constants at `B`, `σ` read through the renaming `padRen B P` elsewhere;
* `armT_digits3`, `armT_noKec3`: an arm whose digits are all `3` takes no step: it does not depend
  on the step and has no `KECCAK`;
* `spArm_complete`: arm `k` of a group completes on the group's arms' range, its tips canonical and
  its chains' starts (`spStartOf`) holding `vals`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-! ## Numbers -/

theorem spSlot_eq (fold : Bool) (B : Nat) : spSlot fold B = slotsT (spWp B) fold (B + 5) := by
  funext r s
  simp only [spSlot, slotsT, groupStart, chainStride, spW, spWp]
  omega

theorem spProd_eq (fold : Bool) (n B : Nat) : V.n (spProd fold n B) = prodT (spWp B) fold n (B + 5) := by
  simp only [spProd, prodT, groupStart, chainStride, spW, spWp, V.mk.injEq, true_and]
  omega

theorem spEnc_eq (fold : Bool) (n B : Nat) : V.n (spEnc fold n B) = encT (spWp B) fold n (B + 5) := by
  simp only [spEnc, spProd, encT, groupStart, chainStride, spW, spWp, V.mk.injEq, true_and]
  omega

theorem spArmEnd_zero (first n : Nat) (fold : Bool) (B : Nat) (prodIn encIn : V) :
    spArmEnd first n fold B prodIn encIn 0 (B + 5) = groupStart fold B + chainStride (spWp B) * n + 2 := by
  simp only [spArmEnd, spArmV, armT_snd, ↓reduceIte, walkBase_zero, chainStride_eq]
  have : (if fold then B + 5 + 1 else B + 5) = groupStart fold B := by cases fold <;> rfl
  rw [this]
  simp only [spW, spWp]
  ring

theorem spArmEnd_pos (first n : Nat) (fold : Bool) (B : Nat) (prodIn encIn : V) {k : Nat} (hk : k ≠ 0)
    (a : Nat) : spArmEnd first n fold B prodIn encIn k a = walkBase 3 k 0 n (if fold then a + 1 else a) + 1 := by
  simp only [spArmEnd, spArmV, armT_snd, hk, ↓reduceIte, Nat.add_zero]
  rfl

theorem withPad_none {X : Nat} {sel : Stmt → Bool} {L : List Stmt} (h : L.findIdx? sel = none) :
    withPad X sel L = (L, 0) := by
  simp [withPad, h]

theorem withPad_some {X : Nat} {sel : Stmt → Bool} {L : List Stmt} {i : Nat} (h : L.findIdx? sel = some i) :
    withPad X sel L = ((Stmt.renameList (padShift X (firstDef (L.getD i default))) L).take i ++
      padRun (firstDef (L.getD i default)) ++
      (Stmt.renameList (padShift X (firstDef (L.getD i default))) L).drop i, 5) := by
  simp [withPad, h]

theorem spArmB_succ (first n : Nat) (fold : Bool) (B : Nat) (prodIn encIn : V) (k : Nat) :
    spArmB first n fold B prodIn encIn (k + 1) =
      spArmEnd first n fold B prodIn encIn k (spArmB first n fold B prodIn encIn k) +
        (withPad spVPad isTopConst (spArmV first n fold B prodIn encIn k
          (spArmB first n fold B prodIn encIn k)).1).2 := by
  rw [spArmB, spArmK_eq, spArmEnd]
  by_cases hk : k = 0 <;> simp only [hk, ↓reduceIte] <;> omega

/-! ## Arms without a step -/

theorem walksT_digits3 (W W' : WotsT) (slots : Nat → Nat → Nat) (first k stride : Nat) :
    ∀ m r b, (∀ t < m, dig k (r + t) = 3) →
      (walksT W slots first k stride m r b).1 = (walksT W' slots first k stride m r b).1
  | 0, _, _, _ => rfl
  | m + 1, r, b, h => by
      simp only [walksT]
      have h0 := h 0 (by omega)
      simp only [Nat.add_zero] at h0
      rw [walksT_digits3 W W' slots first k stride m (r + 1) _ fun t ht => by
        rw [show r + 1 + t = r + (t + 1) by omega]; exact h (t + 1) (by omega)]
      simp [walkT, dig] at h0 ⊢
      simp [h0]

theorem armT_digits3 {W W' : WotsT} (hsz : W.size = W'.size) (hpw : W.power = W'.power)
    (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool) (prodIn encIn po eo : V) (k a : Nat)
    (h : ∀ t < n, dig k t = 3) :
    (armT W slots first n fold prodIn encIn po eo k a).1 = (armT W' slots first n fold prodIn encIn po eo k a).1 := by
  unfold armT
  dsimp only
  rw [hsz, hpw, walksT_digits3 W W' slots first k _ n 0 _ (by simpa using h), walksT_snd, walksT_snd]

theorem walksT_hints3 (W : WotsT) (slots : Nat → Nat → Nat) (first k stride : Nat) :
    ∀ m r b, (∀ t < m, dig k (r + t) = 3) → ∀ x ∈ (walksT W slots first k stride m r b).1,
      ∃ vs, x = hintW "chain_starts" vs
  | 0, _, _, _ => by simp [walksT]
  | m + 1, r, b, h => by
      intro x hx
      simp only [walksT, List.mem_append] at hx
      have h0 := h 0 (by omega)
      simp only [Nat.add_zero] at h0
      rcases hx with hx | hx
      · simp only [walkT, dig] at h0 hx
        simp only [h0, ↓reduceIte, List.mem_singleton] at hx
        exact ⟨_, hx⟩
      · exact walksT_hints3 W slots first k stride m (r + 1) _ (fun t ht => by
          rw [show r + 1 + t = r + (t + 1) by omega]; exact h (t + 1) (by omega)) x hx

theorem armT_noKec3 {W : WotsT} (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn po eo : V) (k a : Nat) (h : ∀ t < n, dig k t = 3) (σ : Val) :
    KCanon σ (armT W slots first n fold prodIn encIn po eo k a).1 := by
  refine kcanon_noKec fun x hx ins outs i o e => ?_
  subst e
  have hw := walksT_hints3 W slots first k (if k = 0 then W.size + 13 else W.size) n 0
    (if fold then a + 1 else a) (by simpa using h)
  unfold armT at hx
  dsimp only at hx
  by_cases hk : k = 0
  · simp only [hk, ↓reduceIte, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx hw
    rcases hx with (hx | hx) | hx
    · cases fold <;> simp [cst] at hx
    · obtain ⟨vs, e⟩ := hw _ hx; simp [hintW] at e
    · cases fold <;> simp [copyS, mulS] at hx
  · simp only [hk, ↓reduceIte, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx hw
    rcases hx with (hx | hx) | hx
    · cases fold <;> simp [cst] at hx
    · obtain ⟨vs, e⟩ := hw _ hx; simp [hintW] at e
    · cases fold <;> simp [copyS, mulS, cst, addS] at hx

/-! ## The valuation an arm is evaluated from -/

/-- `σ` read through `padRen B P`, the run's constants at `B`. -/
def padPull (σ : Val) (B P : Nat) : Val := fun v =>
  if v.path = [] ∧ v.tag = 0 ∧ B ≤ v.idx ∧ v.idx < B + 5 then padC (v.idx - B) else σ (padRen B P v)

theorem padPull_run (σ : Val) {B P j : Nat} (hj : j < 5) : padPull σ B P (.n (B + j)) = padC j := by
  have e : B ≤ B + j ∧ B + j < B + 5 := by omega
  simp only [padPull, e, and_self, ↓reduceIte, Nat.add_sub_cancel_left]

theorem padPull_below (σ : Val) {B P j : Nat} (hj : j < B) (hP : B ≤ P) :
    padPull σ B P (.n j) = σ (.n j) := by
  have e : ¬ (B ≤ j ∧ j < B + 5) := by omega
  simp only [padPull, V.n, true_and, e, ↓reduceIte, padRen_n, show ¬ P ≤ j by omega]

theorem padOK_padPull (σ : Val) (B P : Nat) : PadOK (padPull σ B P) B := by
  have h := fun j (hj : j < 5) => padPull_run σ (B := B) (P := P) hj
  refine ⟨by simpa [padC] using h 0 (by norm_num), ?_, ?_, ?_, ?_⟩ <;>
    [have := h 1 (by norm_num); have := h 2 (by norm_num); have := h 3 (by norm_num);
      have := h 4 (by norm_num)] <;> simpa [padC, word_zero] using this

/-! ## An arm -/

/-- What arm `k` gives the group: its tips canonical, its starts holding `vals`. -/
def SpArmPost (first n : Nat) (fold : Bool) (B : Nat) (prodIn encIn : V) (k : Nat) (vals : Nat → E)
    (σ : Val) : Prop :=
  (∀ t < n, IsCanonical128 (σ (.n (spSlot fold B t 2)))) ∧
    ∀ t < n, σ (spStartOf first n fold B prodIn encIn k (spArmB first n fold B prodIn encIn k) t) = vals t

/-- **An arm completes, moved**: the shared arm over `spW` with its facts, its run moved where
`withPad` puts it (or not at all, when it takes no step), from any valuation whose `pp` and address
are canonical: its tips canonical and its starts holding `vals`, where the renaming puts them. -/
theorem spArm_core {B : Nat} {slots : Nat → Nat → Nat} {first n : Nat} {fold : Bool}
    {prodIn encIn po eo : V} {k a En hi : Nat}
    (F : SpArmFacts B slots first n fold prodIn encIn po eo k a En) (hB : 13 ≤ B) (hEhi0 : En ≤ hi)
    (hEhi : ∀ i, (armT spW slots first n fold prodIn encIn po eo k a).1.findIdx? isTopConst = some i →
      En + 5 ≤ hi) (hEX : En ≤ spVPad)
    (hP : ∀ i, (armT spW slots first n fold prodIn encIn po eo k a).1.findIdx? isTopConst = some i →
      B + 5 ≤ firstDef ((armT spW slots first n fold prodIn encIn po eo k a).1.getD i default) ∧
      firstDef ((armT spW slots first n fold prodIn encIn po eo k a).1.getD i default) ≤ En)
    (hnone : (armT spW slots first n fold prodIn encIn po eo k a).1.findIdx? isTopConst = none →
      ∀ t < n, dig k t = 3)
    (σ : Val) (hg0 : IsCanonical128 (σ (.n 0))) (hg1 : IsCanonical128 (σ (.n 1))) (vals : Nat → E)
    (hv : ∀ t < n, IsCanonical128 (vals t)) :
    Completes C rd (B + 5) hi
      (withPad spVPad isTopConst (armT spW slots first n fold prodIn encIn po eo k a).1).1 σ
      (fun σ' => (∀ t < n, IsCanonical128 (σ' (padRenOf spVPad isTopConst
          (armT spW slots first n fold prodIn encIn po eo k a).1 (.n (slots t 2))))) ∧
        ∀ t < n, σ' (padRenOf spVPad isTopConst (armT spW slots first n fold prodIn encIn po eo k a).1
          (armStart spW slots fold k a t)) = vals t) := by
  set LX := (armT spW slots first n fold prodIn encIn po eo k a).1 with hLX
  set Lb := (armT (spWp B) slots first n fold prodIn encIn po eo k a).1 with hLb
  have hat : atomsOnly Lb = true := F.ssa.atoms
  have hout : ∀ v ∈ outsList Lb, ∃ j, B + 5 ≤ j ∧ j < En ∧ v = .n j := fun v hv =>
    let ⟨j, e, h1, h2⟩ := F.outs v hv; ⟨j, h1, h2, e⟩
  -- the starts
  have hst : ∀ t < n, ∃ j, armStart spW slots fold k a t = .n j ∧ B + 5 ≤ j ∧ j < En := F.starts
  set σ0 := fun (σb : Val) => sLoad (armStart spW slots fold k a) vals σb n with hσ0
  have s_at : ∀ σb, ∀ t < n, σ0 σb (armStart spW slots fold k a t) = vals t := fun σb t ht =>
    sLoad_at _ vals σb n (fun t t' h h' => F.startsNe t t' h h') t ht
  have s_off : ∀ σb j, (j < B + 5) → σ0 σb (.n j) = σb (.n j) := fun σb j hj =>
    sLoad_other _ vals σb n fun t ht e => by
      obtain ⟨j', e', h1, -⟩ := hst t ht
      rw [e'] at e; simp only [V.mk.injEq, true_and] at e; omega
  have hkeep : ∀ σb, ∀ t < n, fwd Lb (σ0 σb) (armStart spW slots fold k a t) = vals t := fun σb t ht => by
    exact (fwd_hint_keep Lb _ F.ssa (armStart_mem (spWp B) slots first n fold prodIn encIn po eo k a ht) _
      (List.mem_singleton_self _)).trans (s_at σb t ht)
  cases hf : LX.findIdx? isTopConst with
  | none =>
      have h3 := hnone hf
      have hreal : (withPad spVPad isTopConst LX).1 = Lb := by
        rw [withPad_none hf, hLX, hLb]
        exact armT_digits3 (W := spW) (W' := spWp B) rfl rfl slots first n fold prodIn encIn po eo k a h3
      have hren : padRenOf spVPad isTopConst LX = id := by simp only [padRenOf, hf]
      rw [hreal, hren]
      have hext : Ext (B + 5) hi σ (σ0 σ) := fun v hv => by
        refine sLoad_other _ vals σ n fun t ht e => ?_
        obtain ⟨j, e', h1, h2⟩ := hst t ht
        rw [e'] at e; exact hv j h1 (by omega) e
      refine ((fwd_completes (C := C) (rd := rd) (lo := B + 5) (hi := En) F.ssa hout (σ0 σ)
        (armT_noKec3 slots first n fold prodIn encIn po eo k a h3 _)).mono le_rfl hEhi0
        (fun σ' hσ' => ⟨fun t ht => ?_, fun t ht => ?_⟩)).reload hext
      · have e : armStart spW slots fold k a t = .n (slots t 2) := by
          simp [armStart, walkStartV, h3 t ht]
        simp only [id, hσ', ← e]
        exact (congrArg IsCanonical128 (hkeep σ t ht)).mpr (hv t ht)
      · simp only [id, hσ']
        exact hkeep σ t ht
  | some i =>
      obtain ⟨hP1, hP2⟩ := hP i hf
      have hEhi := hEhi i hf
      set P := firstDef (LX.getD i default) with hPdef
      have hren : padRenOf spVPad isTopConst LX = padShift spVPad P := by
        simp only [padRenOf, hf, hPdef]
      have hpar : Stmt.renameList (padShift spVPad P) LX = Stmt.renameList (padRen B P) Lb :=
        (spArm_par (by omega) (by omega) hEX F.vals F.lay F.tail).symm
      have hreal : (withPad spVPad isTopConst LX).1 = (Stmt.renameList (padRen B P) Lb).take i ++
          padRun P ++ (Stmt.renameList (padRen B P) Lb).drop i := by
        rw [withPad_some hf, ← hPdef, hpar]
      rw [hreal, hren]
      set σs := σ0 (padPull σ B P) with hσs
      have hgood : SpGood B σs := by
        refine ⟨?_, ?_, ?_⟩
        · rw [hσs, s_off _ 0 (by omega), padPull_below σ (by omega) (by omega)]; exact hg0
        · rw [hσs, s_off _ 1 (by omega), padPull_below σ (by omega) (by omega)]; exact hg1
        · have := padOK_padPull σ B P
          obtain ⟨q0, q1, q2, q3, q4⟩ := this
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · rw [hσs, s_off _ _ (by omega)]; exact q0
          · rw [hσs, s_off _ _ (by omega)]; exact q1
          · rw [hσs, s_off _ _ (by omega)]; exact q2
          · rw [hσs, s_off _ _ (by omega)]; exact q3
          · rw [hσs, s_off _ _ (by omega)]; exact q4
      obtain ⟨kc, ktip⟩ := F.canon σs hgood (fun t ht => by
        show IsCanonical128 (σs (armStart spW slots fold k a t))
        rw [hσs, s_at _ t ht]; exact hv t ht)
      obtain ⟨σ1, -, hσ1, hh1⟩ := fwd_completes (C := C) (rd := rd) (lo := B + 5) (hi := En) F.ssa hout σs kc
      have hA : AtomsHold rd σ1 Lb := atomsHold_of_holdsList (C := C) (kret := fun _ => True) hat
        (hh1 True (fun _ => True) trivial)
      have hfo : ∀ j, (j < B + 5) → σ1 (.n j) = σs (.n j) := fun j hj => by
        rw [hσ1]
        refine fwd_of_not_mem Lb σs fun hm => ?_
        obtain ⟨j', h1, -, e⟩ := hout _ hm
        simp only [V.mk.injEq, true_and] at e; omega
      have hpadv : ∀ j < 5, σ1 (.n (B + j)) = padC j := fun j hj => by
        rw [hfo _ (by omega), hσs, s_off _ _ (by omega), padPull_run σ hj]
      have hag : ∀ j < B + 5, (j < B ∨ B + 5 ≤ j) → σ1 (.n j) = σ (.n j) := fun j hj h => by
        rw [hfo _ hj, hσs, s_off _ _ hj, padPull_below σ (by omega) (by omega)]
      refine (padMove_completes (C := C) (rd := rd) hat hP1 hP2 hEhi F.vals hpadv hag hA i).mono le_rfl
        le_rfl (fun σ' hσ' => ⟨fun t ht => ?_, fun t ht => ?_⟩)
      · have hs := (F.lay t ht).slotB 2 (by norm_num)
        have hsE : slots t 2 < En := F.tipsE t ht
        rw [← padGood_agree (padGood_of (Or.inr hs) (by omega)), hσ', padVal_ren hP1 hP2 hEhi hag hsE,
          hσ1]
        exact ktip t ht
      · obtain ⟨j, e, h1, h2⟩ := hst t ht
        rw [e, ← padGood_agree (padGood_of (Or.inr h1) (by omega)), hσ', padVal_ren hP1 hP2 hEhi hag h2,
          ← e, hσ1]
        exact hkeep _ t ht

/-- **The moved arm's values** are numbered below the group's end. -/
theorem spArm_core_nb {B : Nat} {slots : Nat → Nat → Nat} {first n : Nat} {fold : Bool}
    {prodIn encIn po eo : V} {k a En hi : Nat}
    (F : SpArmFacts B slots first n fold prodIn encIn po eo k a En) (hB : 13 ≤ B) (hEhi0 : En ≤ hi)
    (hEhi : ∀ i, (armT spW slots first n fold prodIn encIn po eo k a).1.findIdx? isTopConst = some i →
      En + 5 ≤ hi) (hEX : En ≤ spVPad)
    (hP : ∀ i, (armT spW slots first n fold prodIn encIn po eo k a).1.findIdx? isTopConst = some i →
      B + 5 ≤ firstDef ((armT spW slots first n fold prodIn encIn po eo k a).1.getD i default) ∧
      firstDef ((armT spW slots first n fold prodIn encIn po eo k a).1.getD i default) ≤ En)
    (hnone : (armT spW slots first n fold prodIn encIn po eo k a).1.findIdx? isTopConst = none →
      ∀ t < n, dig k t = 3) :
    NumBelow hi (Stmt.valsList
      (withPad spVPad isTopConst (armT spW slots first n fold prodIn encIn po eo k a).1).1) := by
  cases hf : (armT spW slots first n fold prodIn encIn po eo k a).1.findIdx? isTopConst with
  | none =>
      rw [withPad_none hf]
      rw [armT_digits3 (W := spW) (W' := spWp B) rfl rfl slots first n fold prodIn encIn po eo k a
        (hnone hf)]
      intro v hv
      obtain ⟨j, rfl, hj⟩ := F.vals v hv
      exact ⟨j, by omega, rfl⟩
  | some i =>
      obtain ⟨hP1, hP2⟩ := hP i hf
      rw [withPad_some hf, (spArm_par (by omega) (by omega) hEX F.vals F.lay F.tail).symm]
      exact (padMove_numBelow F.ssa.atoms hP2 F.vals i).mono (hEhi i hf)

theorem padBase_eq {sel : Stmt → Bool} {L : List Stmt} {i : Nat} (h : L.findIdx? sel = some i) :
    padBase sel L = firstDef (L.getD i default) := by
  simp only [padBase, h]

theorem padRenOf_some {X : Nat} {sel : Stmt → Bool} {L : List Stmt} {i : Nat} (h : L.findIdx? sel = some i) :
    padRenOf X sel L = padShift X (firstDef (L.getD i default)) := by
  simp only [padRenOf, h]

theorem padRenOf_none {X : Nat} {sel : Stmt → Bool} {L : List Stmt} (h : L.findIdx? sel = none) :
    padRenOf X sel L = id := by
  simp only [padRenOf, h]

/-- **Arm `k` of a group completes**, on the group's arms' range, from any valuation whose `pp` and
address are canonical, its layout and padding facts checked: its tips canonical and its starts
holding `vals`. -/
theorem spArm_complete {first n : Nat} {fold : Bool} {B : Nat} {prodIn encIn : V} {k : Nat}
    (hn0 : 0 < n) (hn : n ≤ 3) (hB : 13 ≤ B) (hpi : NBv B prodIn) (hei : NBv B encIn)
    (hend : spArmB first n fold B prodIn encIn (4 ^ n) + 5 < spVPad)
    (hlay : spLayoutOK first n fold B prodIn encIn k (spArmB first n fold B prodIn encIn k) = true)
    (hpad : spPadOK first n fold B prodIn encIn k = true)
    (σ : Val) (hg0 : IsCanonical128 (σ (.n 0))) (hg1 : IsCanonical128 (σ (.n 1))) (vals : Nat → E)
    (hv : ∀ t < n, IsCanonical128 (vals t)) :
    Completes C rd (B + 5) (spArmB first n fold B prodIn encIn (4 ^ n))
      (spArmK first n fold B prodIn encIn k (spArmB first n fold B prodIn encIn k)).1 σ
      (SpArmPost first n fold B prodIn encIn k vals) ∧
    NumBelow (spArmB first n fold B prodIn encIn (4 ^ n)) (Stmt.valsList
      (spArmK first n fold B prodIn encIn k (spArmB first n fold B prodIn encIn k)).1) := by
  set a := spArmB first n fold B prodIn encIn k with ha
  set hi := spArmB first n fold B prodIn encIn (4 ^ n) with hhi
  set L := (spArmV first n fold B prodIn encIn k a).1 with hL
  unfold spPadOK at hpad
  simp only [← ha, ← hL, Bool.and_eq_true, decide_eq_true_eq] at hpad
  obtain ⟨⟨hm, hkpos⟩, hsucc⟩ := hpad
  have hsucc' := spArmB_succ first n fold B prodIn encIn k
  rw [← ha] at hsucc'
  have hEhi0 : spArmEnd first n fold B prodIn encIn k a ≤ hi := by omega
  have hEhi : ∀ i, L.findIdx? isTopConst = some i → spArmEnd first n fold B prodIn encIn k a + 5 ≤ hi := by
    intro i hf
    rw [← hL, withPad_some hf] at hsucc'
    omega
  have hP : ∀ i, L.findIdx? isTopConst = some i →
      B + 5 ≤ firstDef (L.getD i default) ∧ firstDef (L.getD i default) ≤ spArmEnd first n fold B prodIn encIn k a := by
    intro i hf
    rw [hf] at hm
    simpa [Bool.and_eq_true, decide_eq_true_eq] using hm
  unfold spLayoutOK at hlay
  simp only [← hL] at hlay
  have hnone : L.findIdx? isTopConst = none → ∀ t < n, dig k t = 3 := by
    intro hf t ht
    rw [hf] at hlay
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at hlay
    exact hlay t ht
  rw [spArmK_eq]
  unfold SpArmPost spStartOf
  rw [← ha, ← hL]
  have hds := digitSum_le_nine' k n hn
  by_cases hk : k = 0
  · subst hk
    have ha0 : a = B + 5 := rfl
    have hE0 := spArmEnd_zero first n fold B prodIn encIn
    rw [← ha0] at hE0
    have F := spArm0_facts (first := first) (fold := fold) hB hn hpi hei (by rw [← hE0]; omega)
    rw [← ha0, ← hE0] at F
    have hLx : L = (armT spW (slotsT (spWp B) fold B) first n fold prodIn encIn (prodT (spWp B) fold n B)
        (encT (spWp B) fold n B) 0 a).1 := rfl
    have hc := spArm_core (C := C) (rd := rd) F hB hEhi0 (by rw [← hLx]; exact hEhi) (by omega)
      (by rw [← hLx]; exact hP) (by rw [← hLx]; exact hnone) σ hg0 hg1 vals hv
    have hnb := spArm_core_nb F hB hEhi0 (by rw [← hLx]; exact hEhi) (by omega)
      (by rw [← hLx]; exact hP) (by rw [← hLx]; exact hnone)
    rw [← hLx] at hc hnb
    refine ⟨hc.mono le_rfl le_rfl (fun σ' ⟨h1, h2⟩ => ⟨fun t ht => ?_, fun t ht => h2 t ht⟩), hnb⟩
    cases hf : L.findIdx? isTopConst with
    | none => exact absurd (hnone hf 0 hn0) (by simp [dig])
    | some i =>
        have h1t := h1 t ht
        rw [padRenOf_some hf] at h1t
        rw [hf] at hlay
        simp only [↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
          List.mem_range, padBase_eq hf] at hlay
        obtain ⟨-, ⟨⟨hsl, -⟩, hen⟩⟩ := hlay
        have hsl' := hsl t ht 2 (by norm_num)
        have hlt : slotsT spW fold B t 2 < spVPad := by
          have := spSlot fold B t 2
          unfold spEnc spProd at hen
          have := slot_bounds spW fold B t 2 (by norm_num)
          have : chainStride spW * (t + 1) ≤ chainStride spW * n := Nat.mul_le_mul_left _ (by omega)
          omega
        rw [show slotsT (spWp B) fold B t 2 = slotsT spW fold B t 2 from rfl,
          padShift_above hsl' hlt] at h1t
        exact h1t
  · have hV : L = (armT spW (slotsT (spWp B) fold (B + 5)) first n fold prodIn encIn
        (prodT (spWp B) fold n (B + 5)) (encT (spWp B) fold n (B + 5)) k a).1 := by
      simp only [hL, spArmV, spSlots, spPo, spEo, hk, ↓reduceIte, spSlot_eq, spProd_eq, spEnc_eq]
    have hEp := spArmEnd_pos first n fold B prodIn encIn hk a
    have F := spArmPos_facts (first := first) hB hn hk hpi hei (hkpos hk) (by rw [← hEp]; omega)
    rw [← hEp] at F
    have hc := spArm_core (C := C) (rd := rd) F hB hEhi0 (by rw [← hV]; exact hEhi) (by omega)
      (by rw [← hV]; exact hP) (by rw [← hV]; exact hnone) σ hg0 hg1 vals hv
    have hnb := spArm_core_nb F hB hEhi0 (by rw [← hV]; exact hEhi) (by omega)
      (by rw [← hV]; exact hP) (by rw [← hV]; exact hnone)
    rw [← hV] at hc hnb
    have hsl : spSlots fold B k = slotsT (spWp B) fold (B + 5) := by
      simp only [spSlots, hk, ↓reduceIte, spSlot_eq]
    rw [hsl]
    refine ⟨hc.mono le_rfl le_rfl (fun σ' ⟨h1, h2⟩ => ⟨fun t ht => ?_, fun t ht => h2 t ht⟩), hnb⟩
    have h1t := h1 t ht
    rw [spSlot_eq]
    cases hf : L.findIdx? isTopConst with
    | none =>
        rw [padRenOf_none hf] at h1t
        exact h1t
    | some i =>
        rw [padRenOf_some hf] at h1t
        rw [hf] at hlay
        simp only [hk, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
          List.mem_range, padBase_eq hf] at hlay
        obtain ⟨-, ⟨⟨hsl', -⟩, hPX⟩⟩ := hlay
        have := hsl' t ht 2 (by norm_num)
        rw [spSlot_eq] at this
        rw [padShift_below this (by omega)] at h1t
        exact h1t

end
end LeanVM.Guest.B1.Sig
