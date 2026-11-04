/-
  LeanVM.Guest.B1.Sig.SpWotsArms

  An arm of `sp_wots`'s digit dispatch, sound: its walks reach their tips from the hinted starts,
  its product and encoding are folded, read through the renaming `withPad` made.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsLayout
public import LeanVM.Guest.B1.Sig.SphincsKec
public import LeanVM.Guest.B1.Sig.SphincsHash

/-!
# `sp_wots`'s arms, sound

An arm of the template is the shared arm `armT spW …` with its padding run moved (`withPad`): its
values renamed by `padShift X P` and the run's five constants inserted at `P`. So when its atoms
hold under `σ`, the shared arm's hold under `σ ∘ padRenOf …` (`withPad_sound`), whose virtual run
then holds `[0x01, 0, 0, 0, 0]` (`padOK_shift`), and the shared arm's soundness (`armT_sound`)
applies with the chain step `spStepF` (`spW_step_sound`). An arm with no step (every digit `3`)
inserts nothing; any step function serves it (`spAnyF`, `spW_step_any`).

Where the renaming moves the arm's slots, outputs and inputs is a fact about numbers, checked for
every arm the body has by the kernel (`spLayoutOK`, decided in `SpWotsLayout`): the parameters,
the powers and the group's inputs lie below the run, arm `0`'s slots and outputs above it (moved
five up, to `spSlot`, `spProd`, `spEnc`), every other arm's slots and outputs below it.

* `withPad_sound`, `padOK_shift`: the renaming's soundness;
* `SpArmOK`, `spArmK_sound`: what arm `k` establishes, its chain `r` started at `spStartOf … r`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-! ## The renaming -/

theorem renameList_eq_map (r : V → V) : ∀ L : List Stmt, Stmt.renameList r L = L.map (Stmt.rename r)
  | [] => rfl
  | s :: L => by rw [Stmt.renameList, renameList_eq_map r L]; rfl

/-- The atoms of a renamed block hold under `σ` exactly when the block's hold under `σ ∘ r`. -/
theorem atomsHold_rename {r : V → V} {L : List Stmt} (h : AtomsHold rd σ (Stmt.renameList r L)) :
    AtomsHold rd (σ ∘ r) L := by
  intro a ha
  have hm : Stmt.atom (a.rename r) ∈ Stmt.renameList r L := by
    rw [renameList_eq_map]
    exact List.mem_map.mpr ⟨_, ha, rfl⟩
  rw [← Atom.holds_rename]
  exact h _ hm

/-- The base `withPad` moves the padding run to. -/
def padBase (sel : Stmt → Bool) (L : List Stmt) : Nat :=
  match L.findIdx? sel with
  | none => 0
  | some i => firstDef (L.getD i default)

theorem padShift_n (X P k : Nat) :
    padShift X P (.n k) = .n (if X ≤ k then P + (k - X) else if P ≤ k then k + 5 else k) := by
  simp [padShift]

theorem padShift_below {X P k : Nat} (hP : k < P) (hX : k < X) : padShift X P (.n k) = .n k := by
  rw [padShift_n]
  simp [show ¬ X ≤ k by omega, show ¬ P ≤ k by omega]

theorem padShift_above {X P k : Nat} (hP : P ≤ k) (hX : k < X) : padShift X P (.n k) = .n (k + 5) := by
  rw [padShift_n]
  simp [show ¬ X ≤ k by omega, hP]

theorem padRun_ok {P : Nat} (h : AtomsHold rd σ (padRun P)) : PadOK σ P := by
  have e : ∀ k < 5, σ (.n (P + k)) = word (if k = 0 then 1 else 0) 0 0 := fun k hk =>
    h.atom (a := .const (.n (P + k)) _) (by
      simp only [padRun, cst, List.mem_map, List.mem_range]
      exact ⟨k, hk, rfl⟩)
  refine ⟨by simpa using e 0 (by norm_num), ?_, ?_, ?_, ?_⟩ <;>
    [have := e 1 (by norm_num); have := e 2 (by norm_num); have := e 3 (by norm_num);
      have := e 4 (by norm_num)] <;> simpa [word_zero] using this

/-- **The virtual run holds the padding** under the renaming that moved it to a run that does. -/
theorem padOK_shift {X P : Nat} (h : PadOK σ P) : PadOK (σ ∘ padShift X P) X := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  simp only [PadOK, Function.comp, padShift_n, le_refl, ↓reduceIte, Nat.sub_self, Nat.add_zero,
    show ∀ j, X ≤ X + j from fun j => Nat.le_add_right X j, Nat.add_sub_cancel_left]
  exact ⟨h0, h1, h2, h3, h4⟩

/-- **`withPad`, sound**: the block's atoms hold under the renaming, the run where it was inserted
holds the padding, and it adds five values exactly when it inserted the run. -/
theorem withPad_sound {X : Nat} {sel : Stmt → Bool} {L : List Stmt}
    (h : AtomsHold rd σ (withPad X sel L).1) :
    AtomsHold rd (σ ∘ padRenOf X sel L) L ∧
      ((L.findIdx? sel).isSome → PadOK σ (padBase sel L)) ∧
      (withPad X sel L).2 = if (L.findIdx? sel).isSome then 5 else 0 := by
  unfold withPad at h ⊢
  unfold padRenOf padBase
  cases hf : L.findIdx? sel with
  | none =>
      simp only [hf] at h
      exact ⟨h, by simp, by simp⟩
  | some i =>
      simp only [hf] at h
      refine ⟨atomsHold_rename (h.sub fun x hx => ?_), fun _ => padRun_ok (h.sub fun x hx => ?_),
        by simp⟩
      · rw [← List.take_append_drop i (Stmt.renameList _ L)] at hx
        simp only [List.mem_append] at hx ⊢
        tauto
      · simp only [List.mem_append]
        tauto

/-! ## The chain step -/

/-- **`sp_wots`'s step, sound**, its virtual run holding the padding: the output's first cell is
the step's hash of cells. -/
theorem spW_step_sound (hp : PadOK σ spVPad) : StepSound rd σ spW (spStepF (σ (.n 0)) (σ (.n 1))) := by
  intro i s v c o h
  have h1 : σ (.n c) = word (tw 1 + i * hiMul + s * stepMul) 0 0 :=
    h.atom (a := .const (.n c) _) (by simp [spW, cst])
  have h2 : σ (.n (c + 1)) = σ (.n 1) + σ (.n c) :=
    h.atom (a := .add (.n (c + 1)) (.n 1) (.n c)) (by simp [spW, addS])
  have hk := k48At_sound hp (pp := .n 0) (a := .n (c + 1)) (v := v) (c := c + 2) (o := o)
    (h.sub fun x hx => by simp only [spW, List.mem_cons]; tauto)
  rw [spStepF, ← h1, ← h2]
  exact congrArg Prod.fst hk

/-- A chain step's output from any valuation: `KECCAK` of the step's thirteen input cells. -/
def spAnyF (σ : Val) (i s : Nat) (x : E) : E :=
  cellsOfState (keccakF1600 (stateOfCells (cells13 [σ (.n 0),
    σ (.n 1) + word (tw 1 + i * hiMul + s * stepMul) 0 0, x, σ (.n spVPad), σ (.n (spVPad + 1)),
    σ (.n (spVPad + 2)), σ (.n (spVPad + 3)), σ (.n (spVPad + 4)), word (2 ^ 63) 0 0,
    σ (.n (spVPad + 1)), σ (.n (spVPad + 2)), σ (.n (spVPad + 3)), σ (.n (spVPad + 4))]) false))
    false 0

/-- **`sp_wots`'s step, sound under any valuation**, its output `spAnyF`. -/
theorem spW_step_any : StepSound rd σ spW (spAnyF σ) := by
  intro i s v c o h
  have h1 : σ (.n c) = word (tw 1 + i * hiMul + s * stepMul) 0 0 :=
    h.atom (a := .const (.n c) _) (by simp [spW, cst])
  have h2 : σ (.n (c + 1)) = σ (.n 1) + σ (.n c) :=
    h.atom (a := .add (.n (c + 1)) (.n 1) (.n c)) (by simp [spW, addS])
  have h3 : σ (.n (c + 2)) = word (2 ^ 63) 0 0 :=
    h.atom (a := .const (.n (c + 2)) _) (by simp [spW, k48At, cst])
  have hk := h.atom (a := .keccak [.n 0, .n (c + 1), v, .n spVPad, .n (spVPad + 1), .n (spVPad + 2),
    .n (spVPad + 3), .n (spVPad + 4), .n (c + 2), .n (spVPad + 1), .n (spVPad + 2), .n (spVPad + 3),
    .n (spVPad + 4)] (runV o 13) false false) (by simp [spW, k48At, kecS])
  obtain ⟨-, -, -, hk⟩ := hk
  have := hk 0
  rw [spAnyF, ← h1, ← h2, ← h3]
  simpa [cells13, runV] using this

/-! ## An arm -/

/-- **Chain `r`'s start in arm `k`**: its hint, or its tip at digit `3`, as the arm holds it. -/
def spStartOf (first n : Nat) (fold : Bool) (B : Nat) (prodIn encIn : V) (k b r : Nat) : V :=
  padRenOf spVPad isTopConst (spArmV first n fold B prodIn encIn k b).1
    (armStart spW (spSlots fold B k) fold k b r)

/-- **The layout facts of arm `k`**, decided: without a step every digit is `3`; with one, the
parameters, the powers and the group's inputs are below the run, arm `0`'s slots and outputs above
it, another arm's slots and outputs below it. -/
def spLayoutOK (first n : Nat) (fold : Bool) (B : Nat) (prodIn encIn : V) (k b : Nat) : Bool :=
  let L := (spArmV first n fold B prodIn encIn k b).1
  match L.findIdx? isTopConst with
  | none => (List.range n).all fun r => k / 4 ^ r % 4 == 3
  | some _ =>
      let P := padBase isTopConst L
      decide (13 ≤ P) && decide (prodIn = .n prodIn.idx) && decide (prodIn.idx < P) &&
        decide (encIn = .n encIn.idx) && decide (encIn.idx < P) &&
        if k = 0 then
          (List.range n).all (fun r => (List.range 3).all fun s => decide (P ≤ slotsT spW fold B r s)) &&
            decide (P ≤ spProd fold n B - 5) && decide (spEnc fold n B < spVPad)
        else
          (List.range n).all (fun r => (List.range 3).all fun s => decide (spSlot fold B r s < P)) &&
            decide (spEnc fold n B < P) && decide (P < spVPad)

/-- **What arm `k` of a group establishes**, chain `r` starting at `start r`: each walk reaches the
real slot of its last step from its start, the product and the encoding are folded into the
group's outputs. -/
structure SpArmOK (σ : Val) (first n : Nat) (fold : Bool) (B : Nat) (prodIn encIn : V) (k : Nat)
    (start : Nat → V) : Prop where
  tip : ∀ r < n, σ (.n (spSlot fold B r 2)) =
    chainT (spStepF (σ (.n 0)) (σ (.n 1))) (first + r) (3 - k / 4 ^ r % 4) (k / 4 ^ r % 4)
      (σ (start r))
  prod : σ (.n (spProd fold n B)) = (if fold then 1 else σ prodIn) * σ (.n (3 + digitSum k n))
  enc : σ (.n (spEnc fold n B)) = (if fold then 0 else σ encIn) + lit (k * 4 ^ first)

theorem slotsT_lt_prod (fold : Bool) (B r s : Nat) (hr : r < 3) (hs : s < 3) :
    slotsT spW fold B r s < spProd fold 3 B - 5 := by
  simp only [slotsT, spProd, chainStride, spW]
  omega

theorem slotsT_lt_prod1 (fold : Bool) (B s : Nat) (hs : s < 3) :
    slotsT spW fold B 0 s < spProd fold 1 B - 5 := by
  simp only [slotsT, spProd, chainStride, spW]
  omega

theorem digitSum_le_three (k : Nat) : ∀ n, digitSum k n ≤ 3 * n
  | 0 => le_refl _
  | n + 1 => by
      have := digitSum_le_three k n
      have := Nat.mod_lt (k / 4 ^ n) (show 4 > 0 by norm_num)
      simp only [digitSum]
      omega

theorem digitSum_le_nine (k n : Nat) (hn : n ≤ 3) : digitSum k n ≤ 9 :=
  le_trans (digitSum_le_three k n) (by omega)

/-- **Arm `k`, sound**: when its layout checks and its atoms hold, it establishes `SpArmOK` with
its chains started at `spStartOf`. -/
theorem spArmK_sound {first n : Nat} {fold : Bool} {B : Nat} {prodIn encIn : V} {k b : Nat}
    (hn0 : 0 < n) (hn : n ≤ 3) (hlay : spLayoutOK first n fold B prodIn encIn k b = true)
    (h : AtomsHold rd σ (spArmK first n fold B prodIn encIn k b).1) :
    SpArmOK σ first n fold B prodIn encIn k (spStartOf first n fold B prodIn encIn k b) := by
  rw [spArmK_eq] at h
  obtain ⟨hL, hpad, -⟩ := withPad_sound h
  set L := (spArmV first n fold B prodIn encIn k b).1 with hLdef
  have hds : 3 + digitSum k n ≤ 12 := by have := digitSum_le_nine k n hn; omega
  unfold spLayoutOK at hlay
  simp only [← hLdef] at hlay
  cases hf : L.findIdx? isTopConst with
  | none =>
      simp only [hf, List.all_eq_true, List.mem_range, beq_iff_eq] at hlay
      have hr : padRenOf spVPad isTopConst L = id := by simp only [padRenOf, hf]
      have hk0 : k ≠ 0 := fun hk => by have := hlay 0 hn0; subst hk; simp at this
      rw [hr] at hL
      have ha := armT_sound (W := spW) (spW_step_any (σ := σ) (rd := rd))
        (show AtomsHold rd σ (armT spW (spSlot fold B) first n fold prodIn encIn (.n (spProd fold n B))
          (.n (spEnc fold n B)) k b).1 by simpa [hLdef, spArmV, spSlots, spPo, spEo, hk0] using hL)
      refine ⟨fun r hr' => ?_, ?_, ?_⟩
      · have := ha.tip r hr'
        rw [hlay r hr'] at this ⊢
        simpa [spStartOf, ← hLdef, hr, spSlots, hk0, chainT] using this
      · simpa [spW] using ha.prod
      · exact ha.enc
  | some i =>
      have hsome : (L.findIdx? isTopConst).isSome := by rw [hf]; rfl
      set P := padBase isTopConst L with hPdef
      have hP := hpad hsome
      have hr : padRenOf spVPad isTopConst L = padShift spVPad P := by
        simp only [padRenOf, hf, hPdef, padBase]
      rw [hr] at hL
      simp only [hf, Bool.and_eq_true, decide_eq_true_eq] at hlay
      obtain ⟨⟨⟨⟨⟨h13, hpi⟩, hpiP⟩, hei⟩, heiP⟩, hrest⟩ := hlay
      have hX : ∀ j, j < 13 → j < spVPad := fun j hj => by simp [spVPad]; omega
      have fix : ∀ j < P, j < spVPad → (σ ∘ padShift spVPad P) (.n j) = σ (.n j) := fun j hj hjX => by
        simp only [Function.comp, padShift_below hj hjX]
      have hstep := spW_step_sound (rd := rd) (padOK_shift (X := spVPad) hP)
      rw [fix 0 (by omega) (hX 0 (by omega)), fix 1 (by omega) (hX 1 (by omega))] at hstep
      have hpw : (σ ∘ padShift spVPad P) (.n (3 + digitSum k n)) = σ (.n (3 + digitSum k n)) :=
        fix _ (by omega) (hX _ (by omega))
      by_cases hk : k = 0
      · subst hk
        simp only [↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
          List.mem_range] at hrest
        obtain ⟨⟨hsl, hpr⟩, hen⟩ := hrest
        have hencX : spEnc fold n B < spVPad := hen
        have hprX : spProd fold n B - 5 + 1 < spVPad := by unfold spEnc at hencX; omega
        have hpin : (σ ∘ padShift spVPad P) prodIn = σ prodIn := by
          rw [hpi]; exact fix _ hpiP (by omega)
        have hein : (σ ∘ padShift spVPad P) encIn = σ encIn := by
          rw [hei]; exact fix _ heiP (by omega)
        have ha := armT_sound hstep (show AtomsHold rd (σ ∘ padShift spVPad P) (armT spW (slotsT spW fold B)
          first n fold prodIn encIn (prodT spW fold n B) (encT spW fold n B) 0 b).1 by
            simpa [hLdef, spArmV, spSlots, spPo, spEo] using hL)
        have hgs : ∀ m, (prodT spW fold m B).idx = spProd fold m B - 5 := fun m => by
          simp only [prodT, spProd]; rfl
        refine ⟨fun r hr' => ?_, ?_, ?_⟩
        · have hsl' := hsl r hr' 2 (by norm_num)
          have hslX : slotsT spW fold B r 2 < spVPad := by
            have : slotsT spW fold B r 2 < spProd fold n B - 5 := by
              rcases (show n = 1 ∨ n = 2 ∨ n = 3 by omega) with h | h | h <;> subst h
              · have : r = 0 := by omega
                subst this; exact slotsT_lt_prod1 fold B 2 (by norm_num)
              · simp only [slotsT, spProd, chainStride, spW]; omega
              · exact slotsT_lt_prod fold B r 2 hr' (by norm_num)
            omega
          have := ha.tip r hr'
          simp only [Function.comp, padShift_above hsl' hslX] at this
          simpa [spStartOf, ← hLdef, hr, spSlots, spSlot] using this
        · have := ha.prod
          rw [hpin, show spW.power (digitSum 0 n) = .n (3 + digitSum 0 n) from rfl, hpw] at this
          rw [← this]
          simp only [Function.comp, prodT]
          rw [padShift_above (by have := hgs n; simp only [prodT] at this; omega) (by
            have := hgs n; simp only [prodT] at this; omega)]
          congr 2
        · have := ha.enc
          rw [hein] at this
          rw [← this]
          simp only [Function.comp, encT]
          rw [padShift_above (by have := hgs n; simp only [prodT] at this; omega) (by
            have := hgs n; simp only [prodT] at this; unfold spEnc at hencX; omega)]
          congr 2
      · simp only [hk, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
          List.mem_range] at hrest
        obtain ⟨⟨hsl, hen⟩, hPX⟩ := hrest
        have hpin : (σ ∘ padShift spVPad P) prodIn = σ prodIn := by
          rw [hpi]; exact fix _ hpiP (by omega)
        have hein : (σ ∘ padShift spVPad P) encIn = σ encIn := by
          rw [hei]; exact fix _ heiP (by omega)
        have ha := armT_sound hstep (show AtomsHold rd (σ ∘ padShift spVPad P) (armT spW (spSlot fold B)
          first n fold prodIn encIn (.n (spProd fold n B)) (.n (spEnc fold n B)) k b).1 by
            simpa [hLdef, spArmV, spSlots, spPo, spEo, hk] using hL)
        refine ⟨fun r hr' => ?_, ?_, ?_⟩
        · have := ha.tip r hr'
          rw [fix _ (hsl r hr' 2 (by norm_num)) (by have := hsl r hr' 2 (by norm_num); omega)] at this
          simpa [spStartOf, ← hLdef, hr, spSlots, hk] using this
        · have := ha.prod
          rw [hpin, show spW.power (digitSum k n) = .n (3 + digitSum k n) from rfl, hpw,
            fix _ (by unfold spEnc at hen; omega) (by unfold spEnc at hen; omega)] at this
          exact this
        · have := ha.enc
          rw [hein, fix _ hen (by omega)] at this
          exact this

end
end LeanVM.Guest.B1.Sig
