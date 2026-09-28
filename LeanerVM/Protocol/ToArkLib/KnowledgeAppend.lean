/-
  LeanerVM.Protocol.ToArkLib.KnowledgeAppend

  Round-by-round knowledge soundness composes across `Verifier.append` when the first verifier
  is guarded. Ported from ArkLib pull request #615 at `ca7a2577`,
  `ArkLib/OracleReduction/Composition/Sequential/Append/Knowledge.lean`.

  Copyright (c) 2026 ArkLib Contributors. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: ArkLib Contributors
-/

module

public import ArkLib.OracleReduction.Composition.Sequential.Append.StateFunction
public import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Guarded

/-!
# Knowledge soundness of append, for a guarded first verifier

When the first of two verifiers is a Boolean check followed by a pure verdict (a `GuardedForm`),
round-by-round knowledge soundness composes across `Verifier.append`, for a named extractor and
knowledge state function. The extractor is ArkLib's `Extractor.RoundByRound.append`, which hands
the first verdict to the second extractor. Its knowledge state function,
`Verifier.KnowledgeStateFunction.appendGuarded`, is the first component's state up to the seam,
then the first check together with the second component's state on the first verdict.
`Verifier.append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first` proves worst-case
round-by-round knowledge soundness for the two, each challenge keeping the error of the component
it comes from. The second verifier is arbitrary, and either component may have no round.

ArkLib at the pinned revision states the composition only in its existential form averaged over
transcript prefixes, with no guard (`Verifier.append_rbrKnowledgeSoundness`), and admits it. This
file is a verbatim port of the proof from ArkLib pull request #615, under `LeanerVM.Protocol` with
ArkLib's names, except that its two lemmas on the witness type reuse the pinned ArkLib's proofs;
the wrappers into the existential and averaged forms are left out. When the ArkLib pin moves to a
revision containing that pull request, delete this file and replace its two names in
`Component.lean` by ArkLib's.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

@[expose] public section

namespace Verifier.KnowledgeAppend

variable {ι : Type} {oSpec : OracleSpec ι}
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type} {m n : ℕ}
  {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  {W₁ : Fin (m + 1) → Type} {W₂ : Fin (n + 1) → Type}

/-- The append extractor retains the first witness type through the seam. -/
abbrev Witness (W₁ : Fin (m + 1) → Type) (W₂ : Fin (n + 1) → Type) :=
  Fin.append (m := m + 1) W₁ (Fin.tail W₂) ∘ Fin.cast (show m + n + 1 = m + 1 + n by omega)

/-- In the first component's range, `Witness` is the first witness type (ArkLib's
`Extractor.wit_mid_append_left`). -/
theorem witness_left (k : Fin (m + n + 1)) (j : Fin (m + 1)) (h : k.val = j.val) :
    Witness W₁ W₂ k = W₁ j :=
  Extractor.wit_mid_append_left k j h

/-- Past the seam, `Witness` is the second witness type (ArkLib's
`Extractor.wit_mid_append_right`). -/
theorem witness_right (k : Fin (m + n + 1)) (j : Fin (n + 1))
    (h : k.val = m + j.val) (hj : 0 < j.val) : Witness W₁ W₂ k = W₂ j :=
  Extractor.wit_mid_append_right k j h hj

/-- An available prefix in the first component, with all transports explicit. -/
def left {k : Fin (m + n + 1)} (tr : (pSpec₁ ++ₚ pSpec₂).Transcript k)
    (j : Fin (m + 1)) (hj : j.val ≤ k.val) : pSpec₁.Transcript j := fun i =>
  cast (append_Type_castAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
    ⟨i.val, by have := i.isLt; have := j.isLt; omega⟩)
    (tr ⟨i.val, by have := i.isLt; omega⟩)

/-- An available prefix in the second component, with all transports explicit. -/
def right {k : Fin (m + n + 1)} (tr : (pSpec₁ ++ₚ pSpec₂).Transcript k)
    (j : Fin (n + 1)) (hj : m + j.val ≤ k.val) : pSpec₂.Transcript j := fun i =>
  cast (append_Type_natAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
    ⟨i.val, by have := i.isLt; have := j.isLt; omega⟩)
    (tr ⟨m + i.val, by have := i.isLt; omega⟩)

private theorem transcript_heq {N : ℕ} {p : ProtocolSpec N} {k j : Fin (N + 1)}
    {a : p.Transcript k} {b : p.Transcript j} (h : k.val = j.val)
    (hab : ∀ i hi hj, HEq (a ⟨i, hi⟩) (b ⟨i, hj⟩)) : HEq a b := by
  obtain rfl : k = j := Fin.ext h
  exact heq_of_eq (funext fun i => eq_of_heq (hab i.val i.isLt i.isLt))

/-- The first component's prefix of a full transcript is its first half. -/
theorem left_full (tr : (pSpec₁ ++ₚ pSpec₂).FullTranscript) :
    left (k := Fin.last (m + n)) tr (Fin.last m) (by simp) = tr.fst := rfl

/-- The second component's prefix of a full transcript is its second half. -/
theorem right_full (tr : (pSpec₁ ++ₚ pSpec₂).FullTranscript) :
    right (k := Fin.last (m + n)) tr (Fin.last n) (by simp) = tr.snd := rfl

/-- Extending a transcript leaves an earlier prefix in the first component unchanged. -/
theorem left_concat_eq {i : Fin (m + n)} (tr : (pSpec₁ ++ₚ pSpec₂).Transcript i.castSucc)
    (x : (pSpec₁ ++ₚ pSpec₂).Type i) (j : Fin (m + 1)) (hj : j.val ≤ i.val) :
    left (tr.concat x) j (by simp; omega) = left tr j hj := by
  funext a
  apply eq_of_heq
  exact (cast_heq _ _).trans ((Transcript.concat_apply_lt tr x a.val
    (by have := a.isLt; omega) (by have := a.isLt; simp; omega)).trans
    (cast_heq _ _).symm)

/-- Extending a transcript in the first component extends its prefix there. -/
theorem left_concat {i : Fin (m + n)} (tr : (pSpec₁ ++ₚ pSpec₂).Transcript i.castSucc)
    (x : (pSpec₁ ++ₚ pSpec₂).Type i) (j : Fin m) (h : i.val = j.val)
    (ht : (pSpec₁ ++ₚ pSpec₂).Type i = pSpec₁.Type j) :
    left (tr.concat x) j.succ (by simp; omega) =
      (left tr j.castSucc (by simp; omega)).concat (cast ht x) := by
  funext a
  apply eq_of_heq
  have ha := a.isLt
  change a.val < j.val + 1 at ha
  by_cases haj : a.val < j.val
  · exact (cast_heq _ _).trans ((Transcript.concat_apply_lt tr x a.val
      (by omega) (by simp; omega)).trans
      ((Transcript.concat_apply_lt _ (cast ht x) a.val haj ha).trans
        (cast_heq _ _)).symm)
  · have hea : a.val = j.val := by omega
    exact (cast_heq _ _).trans ((Transcript.concat_apply_last tr x a.val
      (by omega) (by simp; omega)).trans
      ((Transcript.concat_apply_last _ (cast ht x) a.val hea ha).trans
        (cast_heq _ _)).symm)

/-- Extending a transcript in the second component extends its prefix there. -/
theorem right_concat {i : Fin (m + n)} (tr : (pSpec₁ ++ₚ pSpec₂).Transcript i.castSucc)
    (x : (pSpec₁ ++ₚ pSpec₂).Type i) (j : Fin n) (h : i.val = m + j.val)
    (ht : (pSpec₁ ++ₚ pSpec₂).Type i = pSpec₂.Type j) :
    right (tr.concat x) j.succ (by simp; omega) =
      (right tr j.castSucc (by simp; omega)).concat (cast ht x) := by
  funext a
  apply eq_of_heq
  have ha := a.isLt
  change a.val < j.val + 1 at ha
  by_cases haj : a.val < j.val
  · exact (cast_heq _ _).trans ((Transcript.concat_apply_lt tr x (m + a.val)
      (by omega) (by simp; omega)).trans
      ((Transcript.concat_apply_lt _ (cast ht x) a.val haj ha).trans
        (cast_heq _ _)).symm)
  · have hea : a.val = j.val := by omega
    exact (cast_heq _ _).trans ((Transcript.concat_apply_last tr x (m + a.val)
      (by omega) (by simp; omega)).trans
      ((Transcript.concat_apply_last _ (cast ht x) a.val hea ha).trans
        (cast_heq _ _)).symm)

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {R₁ : Set (Stmt₁ × Wit₁)} {R₂ : Set (Stmt₂ × Wit₂)} {R₃ : Set (Stmt₃ × Wit₃)}
  {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁} {V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂}
  {E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ W₁}
  {E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ W₂}

private theorem knowledge_congr
    {N : ℕ} {p : ProtocolSpec N} {A B X Y : Type} {W : Fin (N + 1) → Type}
    {V : Verifier oSpec A B p} {E : Extractor.RoundByRound oSpec A X Y p W}
    {R : Set (A × X)} {S : Set (B × Y)}
    (K : V.KnowledgeStateFunction init impl R S E)
    {i j : Fin (N + 1)} (h : i.val = j.val) {s : A}
    {tr : p.Transcript i} {tr' : p.Transcript j} (ht : HEq tr tr')
    {w : W i} {w' : W j} (hw : HEq w w') : K i s tr w ↔ K j s tr' w' := by
  obtain rfl : i = j := Fin.ext h
  obtain rfl := eq_of_heq ht
  obtain rfl := eq_of_heq hw
  rfl

private theorem extractMid_heq
    {N : ℕ} {p : ProtocolSpec N} {A X Y : Type} {W : Fin (N + 1) → Type}
    (E : Extractor.RoundByRound oSpec A X Y p W)
    {i j : Fin N} (h : i.val = j.val) {s : A}
    {tr : p.Transcript i.succ} {tr' : p.Transcript j.succ} (ht : HEq tr tr')
    {w : W i.succ} {w' : W j.succ} (hw : HEq w w') :
    HEq (E.extractMid i s tr w) (E.extractMid j s tr' w') := by
  obtain rfl : i = j := Fin.ext h
  obtain rfl := eq_of_heq ht
  obtain rfl := eq_of_heq hw
  rfl

/-- The state uses the left extractor through the seam and the guarded right state thereafter. -/
def state (G : V₁.GuardedForm)
    (K₁ : V₁.KnowledgeStateFunction init impl R₁ R₂ E₁)
    (K₂ : V₂.KnowledgeStateFunction init impl R₂ R₃ E₂)
    (k : Fin (m + n + 1)) (s : Stmt₁) (tr : (pSpec₁ ++ₚ pSpec₂).Transcript k)
    (w : Witness W₁ W₂ k) : Prop :=
  if hk : k.val ≤ m then
    K₁ ⟨k.val, by omega⟩ s (left tr ⟨k.val, by omega⟩ (by rfl))
      (cast (witness_left k ⟨k.val, by omega⟩ rfl) w)
  else
    let tr₁ := left tr (Fin.last m) (by simp; omega)
    G.check s tr₁ = true ∧
      K₂ ⟨k.val - m, by have := k.isLt; omega⟩ (G.out s tr₁)
        (right tr ⟨k.val - m, by have := k.isLt; omega⟩ (by simp; omega))
        (cast (witness_right k ⟨k.val - m, by have := k.isLt; omega⟩
          (by simp; omega) (by simp; omega)) w)

/-- Up to the seam, the state is the first component's knowledge state. -/
theorem state_left (G : V₁.GuardedForm)
    (K₁ : V₁.KnowledgeStateFunction init impl R₁ R₂ E₁)
    (K₂ : V₂.KnowledgeStateFunction init impl R₂ R₃ E₂)
    {k : Fin (m + n + 1)} (j : Fin (m + 1)) (h : k.val = j.val)
    (s : Stmt₁) (tr : (pSpec₁ ++ₚ pSpec₂).Transcript k) (w : Witness W₁ W₂ k) :
    state G K₁ K₂ k s tr w ↔
      K₁ j s (left tr j (by omega)) (cast (witness_left k j h) w) := by
  rcases k with ⟨k, hk⟩
  rcases j with ⟨j, hj⟩
  change k = j at h
  subst j
  simp only [state, Fin.val_mk, dif_pos (show k ≤ m by omega)]

/-- Past the seam, the state is the first check and the second component's state. -/
theorem state_right (G : V₁.GuardedForm)
    (K₁ : V₁.KnowledgeStateFunction init impl R₁ R₂ E₁)
    (K₂ : V₂.KnowledgeStateFunction init impl R₂ R₃ E₂)
    {k : Fin (m + n + 1)} (j : Fin (n + 1)) (h : k.val = m + j.val) (hj : 0 < j.val)
    (s : Stmt₁) (tr : (pSpec₁ ++ₚ pSpec₂).Transcript k) (w : Witness W₁ W₂ k) :
    state G K₁ K₂ k s tr w ↔
      G.check s (left tr (Fin.last m) (by simp; omega)) = true ∧
      K₂ j (G.out s (left tr (Fin.last m) (by simp; omega)))
        (right tr j (by omega)) (cast (witness_right k j h hj) w) := by
  rcases k with ⟨k, hk⟩
  rcases j with ⟨j, hjn⟩
  change k = m + j at h
  change 0 < j at hj
  subst k
  have hsub : m + j - m = j := by omega
  simp only [state, Fin.val_mk, dif_neg (show ¬ m + j ≤ m by omega)]
  apply and_congr Iff.rfl
  apply knowledge_congr K₂ hsub
  · apply transcript_heq hsub
    intros
    rfl
  · exact (cast_heq _ _).trans (cast_heq _ _).symm

/-- Before the seam, the append extractor is the first extractor. -/
theorem extractMid_left (G : V₁.GuardedForm)
    {i : Fin (m + n)} (j : Fin m) (h : i.val = j.val) (s : Stmt₁)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript i.succ) (w : Witness W₁ W₂ i.succ) :
    cast (witness_left i.castSucc j.castSucc h)
      ((E₁.append E₂ G.out).extractMid i s tr w) =
    E₁.extractMid j s (left tr j.succ (by simp; omega))
      (cast (witness_left i.succ j.succ (by simp; omega)) w) := by
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  change i = j at h
  subst i
  simp only [Extractor.RoundByRound.append, Fin.val_mk, dif_pos hj, cast_cast, cast_eq]
  rfl

/-- Past the seam, the append extractor is the second extractor, on the first verdict. -/
theorem extractMid_right (G : V₁.GuardedForm)
    {i : Fin (m + n)} (j : Fin n) (h : i.val = m + j.val) (hj : 0 < j.val) (s : Stmt₁)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript i.succ) (w : Witness W₁ W₂ i.succ) :
    cast (witness_right i.castSucc j.castSucc h hj)
      ((E₁.append E₂ G.out).extractMid i s tr w) =
    E₂.extractMid j (G.out s (left tr (Fin.last m) (by simp; omega)))
      (right tr j.succ (by simp; omega))
      (cast (witness_right i.succ j.succ (by simp; omega) (by simp)) w) := by
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hjn⟩
  change i = m + j at h
  change 0 < j at hj
  subst i
  simp only [Extractor.RoundByRound.append, Fin.val_mk,
    dif_neg (show ¬ m + j < m by omega), dif_neg (show ¬ m + j = m by omega),
    cast_cast]
  apply eq_of_heq
  refine (cast_heq _ _).trans (extractMid_heq E₂ (by simp) ?_ ?_)
  · exact transcript_heq (p := pSpec₂)
      (k := (⟨m + j - m, by omega⟩ : Fin n).succ)
      (j := (⟨j, hjn⟩ : Fin n).succ) (by simp) (fun _ _ _ => HEq.rfl)
  · exact (cast_heq _ _).trans (cast_heq _ _).symm

/-- At the seam, the append extractor feeds the second extractor's first step to the
first extractor's output. -/
theorem extractMid_seam (G : V₁.GuardedForm)
    {i : Fin (m + n)} (h : i.val = m) (s : Stmt₁)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript i.succ) (w : Witness W₁ W₂ i.succ) :
    cast (witness_left i.castSucc (Fin.last m) h)
      ((E₁.append E₂ G.out).extractMid i s tr w) =
    E₁.extractOut s (left tr (Fin.last m) (by simp; omega))
      (cast (show W₂ (⟨0, by have := i.isLt; omega⟩ : Fin n).castSucc = Wit₂ from E₂.eqIn)
        (E₂.extractMid ⟨0, by have := i.isLt; omega⟩
          (G.out s (left tr (Fin.last m) (by simp; omega)))
          (right tr ⟨1, by have := i.isLt; omega⟩ (by simp; omega))
          (cast (witness_right i.succ ⟨1, by have := i.isLt; omega⟩
            (by simp; omega) (by simp)) w))) := by
  rcases i with ⟨i, hi⟩
  change i = m at h
  subst i
  simp only [Extractor.RoundByRound.append, Fin.val_mk,
    dif_neg (Nat.lt_irrefl m), ↓reduceDIte, cast_cast, cast_eq]
  rfl

/-- With a second round, the final extraction is the second extractor's. -/
theorem extractOut_right (G : V₁.GuardedForm) (hn : 0 < n) (s : Stmt₁)
    (tr : (pSpec₁ ++ₚ pSpec₂).FullTranscript) (w : Wit₃) :
    cast (witness_right (Fin.last (m + n)) (Fin.last n) (by simp) hn)
      ((E₁.append E₂ G.out).extractOut s tr w) =
      E₂.extractOut (G.out s tr.fst) tr.snd w := by
  simp only [Extractor.RoundByRound.append, dif_pos hn, cast_cast, cast_eq]

/-- With no second round, the final extraction feeds the second extractor's output to the
first's. -/
theorem extractOut_zero (G : V₁.GuardedForm) (hn : n = 0) (s : Stmt₁)
    (tr : (pSpec₁ ++ₚ pSpec₂).FullTranscript) (w : Wit₃) :
    cast (witness_left (Fin.last (m + n)) (Fin.last m) (by simp [hn]))
      ((E₁.append E₂ G.out).extractOut s tr w) =
    E₁.extractOut s tr.fst
      (cast (show W₂ (Fin.last n) = Wit₂ by
          rw [show Fin.last n = 0 by ext; simp; omega]
          exact E₂.eqIn)
        (E₂.extractOut (G.out s tr.fst) tr.snd w)) := by
  simp only [Extractor.RoundByRound.append, dif_neg (show ¬ 0 < n by omega), cast_cast,
    cast_eq]

variable [∀ i, SampleableType (pSpec₁.Challenge i)]

/-- A related passing verdict supplies the left extractor's final knowledge state. -/
theorem left_related (G : V₁.GuardedForm)
    (K₁ : V₁.KnowledgeStateFunction init impl R₁ R₂ E₁)
    (s : Stmt₁) (tr : pSpec₁.FullTranscript) (w : Wit₂)
    (hc : G.check s tr = true) (hw : (G.out s tr, w) ∈ R₂) :
    K₁ (Fin.last m) s tr (E₁.extractOut s tr w) := by
  apply K₁.toFun_full
  have hp := Verifier.guarded_accepting_of_mem init impl V₁ G.check G.out G.verify_eq
    s tr hc {t | (t, w) ∈ R₂} hw
  exact lt_of_lt_of_eq zero_lt_one hp.symm

private theorem empty_relation
    (K₂ : V₂.KnowledgeStateFunction init impl R₂ R₃ E₂)
    (j : Fin (n + 1)) (hj : j.val = 0) (s : Stmt₂)
    (tr : pSpec₂.Transcript j) (w : W₂ j) (hw : K₂ j s tr w) :
    (s, cast ((congrArg W₂ (show j = 0 from Fin.ext hj)).trans E₂.eqIn) w) ∈ R₂ := by
  obtain rfl : j = 0 := Fin.ext hj
  have ht : tr = default := by funext i; exact Fin.elim0 i
  subst tr
  exact (K₂.toFun_empty s w).mpr hw

/-- A right transition whose extracted predecessor is valid cannot create a bad composite
transition, including the first right round where the left extractor runs at the seam. -/
theorem backward_right (G : V₁.GuardedForm)
    (K₁ : V₁.KnowledgeStateFunction init impl R₁ R₂ E₁)
    (K₂ : V₂.KnowledgeStateFunction init impl R₂ R₃ E₂)
    {i : Fin (m + n)} (j : Fin n) (h : i.val = m + j.val)
    (ht : (pSpec₁ ++ₚ pSpec₂).Type i = pSpec₂.Type j)
    (s : Stmt₁) (tr : (pSpec₁ ++ₚ pSpec₂).Transcript i.castSucc)
    (x : (pSpec₁ ++ₚ pSpec₂).Type i) (w : Witness W₁ W₂ i.succ)
    (hc : G.check s (left tr (Fin.last m) (by simp; omega)) = true)
    (hw : K₂ j.castSucc (G.out s (left tr (Fin.last m) (by simp; omega)))
      (right tr j.castSucc (by simp; omega))
      (E₂.extractMid j (G.out s (left tr (Fin.last m) (by simp; omega)))
        ((right tr j.castSucc (by simp; omega)).concat (cast ht x))
        (cast (witness_right i.succ j.succ (by simp; omega) (by simp)) w))) :
    state G K₁ K₂ i.castSucc s tr ((E₁.append E₂ G.out).extractMid i s (tr.concat x) w) := by
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hjn⟩
  change i = m + j at h
  subst i
  by_cases hj : j = 0
  · subst j
    rw [state_left G K₁ K₂ (Fin.last m) (by simp),
      extractMid_seam G (by simp), left_concat_eq tr x (Fin.last m) (by simp)]
    apply left_related G K₁ s _ _ hc
    have he := empty_relation K₂ _ rfl _ _ _ hw
    erw [right_concat tr x (⟨0, hjn⟩ : Fin n) (by simp) ht]
    exact he
  · rw [state_right G K₁ K₂ (⟨j, hjn⟩ : Fin n).castSucc (by simp) (by simp; omega),
      extractMid_right G (⟨j, hjn⟩ : Fin n) (by simp) (by simp; omega),
      left_concat_eq tr x (Fin.last m) (by simp),
      right_concat _ _ (⟨j, hjn⟩ : Fin n) (by simp) ht]
    exact ⟨hc, hw⟩

/-- Prover messages preserve the composed knowledge state under the append extractor. -/
theorem state_next (G : V₁.GuardedForm)
    (K₁ : V₁.KnowledgeStateFunction init impl R₁ R₂ E₁)
    (K₂ : V₂.KnowledgeStateFunction init impl R₂ R₃ E₂)
    (i : Fin (m + n)) (hi : (pSpec₁ ++ₚ pSpec₂).dir i = .P_to_V)
    (s : Stmt₁) (tr : (pSpec₁ ++ₚ pSpec₂).Transcript i.castSucc)
    (x : (pSpec₁ ++ₚ pSpec₂).Type i) (w : Witness W₁ W₂ i.succ)
    (hw : state G K₁ K₂ i.succ s (tr.concat x) w) :
    state G K₁ K₂ i.castSucc s tr ((E₁.append E₂ G.out).extractMid i s (tr.concat x) w) := by
  have hii := i.isLt
  change Fin.vappend pSpec₁.dir pSpec₂.dir i = .P_to_V at hi
  by_cases hl : i.val < m
  · let j : Fin m := ⟨i.val, hl⟩
    have ht : (pSpec₁ ++ₚ pSpec₂).Type i = pSpec₁.Type j :=
      Fin.vappend_left_of_lt _ _ i hl
    have hd : pSpec₁.dir j = .P_to_V := by
      simpa only [Fin.vappend_left_of_lt _ _ i hl] using hi
    rw [state_left G K₁ K₂ j.castSucc rfl, extractMid_left G j rfl,
      left_concat tr x j rfl ht]
    apply K₁.toFun_next j hd
    have hnext := (state_left G K₁ K₂ j.succ rfl s (tr.concat x) w).mp hw
    rwa [left_concat tr x j rfl ht] at hnext
  · let j : Fin n := ⟨i.val - m, by omega⟩
    have hij : i.val = m + j.val := by dsimp [j]; omega
    have ht : (pSpec₁ ++ₚ pSpec₂).Type i = pSpec₂.Type j :=
      Fin.vappend_right_of_not_lt _ _ i (by omega)
    have hd : pSpec₂.dir j = .P_to_V := by
      simpa only [Fin.vappend_right_of_not_lt _ _ i (by omega)] using hi
    have hnext := (state_right G K₁ K₂ j.succ (by simp; omega) (by simp)
      s (tr.concat x) w).mp hw
    rw [left_concat_eq tr x (Fin.last m) (by simp; omega),
      right_concat tr x j hij ht] at hnext
    exact backward_right G K₁ K₂ j hij ht s tr x w hnext.1
      (K₂.toFun_next j hd _ _ _ _ hnext.2)

omit [∀ i, SampleableType (pSpec₁.Challenge i)] in
/-- Operational normalization: the left guard rejects the entire append. -/
theorem run_guarded (G : V₁.GuardedForm) (s : Stmt₁)
    (tr : (pSpec₁ ++ₚ pSpec₂).FullTranscript) :
    (V₁.append V₂).run s tr =
      if G.check s tr.fst then V₂.run (G.out s tr.fst) tr.snd else failure := by
  have h := Verifier.append_run_guardedLeft V₁ V₂ G.check G.out G.verify_eq s tr.fst tr.snd
  rwa [FullTranscript.append_fst_snd] at h

private theorem failure_probability (p : Stmt₃ → Prop) :
    Pr[p | OptionT.mk do
      (simulateQ impl (failure : OptionT (OracleComp oSpec) Stmt₃)).run' (← init)] = 0 := by
  rw [probEvent_eq_zero_iff]
  intro x hx
  rw [OptionT.mem_support_iff] at hx
  have hc : (do (simulateQ impl (failure : OptionT (OracleComp oSpec) Stmt₃)).run' (← init) :
      ProbComp (Option Stmt₃)) = (init >>= fun _ => pure none) := by congr 1
  simp only [OptionT.run_mk, hc, support_bind_const, support_pure, Set.mem_ofPred_eq] at hx
  have hbad : some x = (none : Option Stmt₃) := hx.1
  cases hbad

/-- A positive related output yields the terminal knowledge state, also for an empty right side. -/
theorem state_full (G : V₁.GuardedForm)
    (K₁ : V₁.KnowledgeStateFunction init impl R₁ R₂ E₁)
    (K₂ : V₂.KnowledgeStateFunction init impl R₂ R₃ E₂)
    (s : Stmt₁) (tr : (pSpec₁ ++ₚ pSpec₂).FullTranscript) (w : Wit₃)
    (hp : Pr[ fun t => (t, w) ∈ R₃ | OptionT.mk do
      (simulateQ impl ((V₁.append V₂).run s tr)).run' (← init)] > 0) :
    state G K₁ K₂ (Fin.last (m + n)) s tr ((E₁.append E₂ G.out).extractOut s tr w) := by
  rw [run_guarded G] at hp
  by_cases hc : G.check s tr.fst = true
  · rw [if_pos hc] at hp
    have h₂ := K₂.toFun_full (G.out s tr.fst) tr.snd w hp
    by_cases hn : 0 < n
    · erw [state_right G K₁ K₂ (k := Fin.last (m + n)) (Fin.last n) (by simp) hn,
        extractOut_right G hn, left_full, right_full]
      exact ⟨hc, h₂⟩
    · have hn0 : n = 0 := by omega
      erw [state_left G K₁ K₂ (k := Fin.last (m + n)) (Fin.last m) (by simp [hn0]),
        extractOut_zero G hn0, left_full]
      exact left_related G K₁ s tr.fst _ hc
        (empty_relation K₂ (Fin.last n) (by simp [hn0]) _ _ _ h₂)
  · rw [if_neg hc, failure_probability] at hp
    exact False.elim (lt_irrefl _ hp)

end Verifier.KnowledgeAppend

namespace Verifier.KnowledgeStateFunction

open KnowledgeAppend

variable {ι : Type} {oSpec : OracleSpec ι}
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type} {m n : ℕ}
  {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)]
  {W₁ : Fin (m + 1) → Type} {W₂ : Fin (n + 1) → Type}
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {R₁ : Set (Stmt₁ × Wit₁)} {R₂ : Set (Stmt₂ × Wit₂)} {R₃ : Set (Stmt₃ × Wit₃)}
  {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁} {V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂}
  {E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ W₁}
  {E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ W₂}

/-- Exact knowledge-state composition for the proven append extractor and a guarded left
verifier. -/
def appendGuarded (G : V₁.GuardedForm)
    (K₁ : V₁.KnowledgeStateFunction init impl R₁ R₂ E₁)
    (K₂ : V₂.KnowledgeStateFunction init impl R₂ R₃ E₂) :
    (V₁.append V₂).KnowledgeStateFunction init impl R₁ R₃ (E₁.append E₂ G.out) where
  toFun := state G K₁ K₂
  toFun_empty := by
    intro s w
    rw [state_left G K₁ K₂ 0 rfl]
    have ht : left (default : (pSpec₁ ++ₚ pSpec₂).Transcript 0) 0 (by simp) = default := by
      funext i
      exact Fin.elim0 i
    rw [ht]
    simpa only [cast_cast] using K₁.toFun_empty s (cast (witness_left 0 0 rfl) w)
  toFun_next := state_next G K₁ K₂
  toFun_full := state_full G K₁ K₂

end Verifier.KnowledgeStateFunction

namespace Verifier

open KnowledgeAppend

variable {ι : Type} {oSpec : OracleSpec ι}
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type} {m n : ℕ}
  {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)]
  [∀ i, SampleableType (pSpec₂.Challenge i)]
  {W₁ : Fin (m + 1) → Type} {W₂ : Fin (n + 1) → Type}
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {R₁ : Set (Stmt₁ × Wit₁)} {R₂ : Set (Stmt₂ × Wit₂)} {R₃ : Set (Stmt₃ × Wit₃)}
  {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁} {V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂}
  {E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ W₁}
  {E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ W₂}

/-- Guarded-left composition preserves worst-case knowledge error for these exact component
extractors and knowledge states. The first round of the right component is included. -/
theorem append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first (G : V₁.GuardedForm)
    (K₁ : V₁.KnowledgeStateFunction init impl R₁ R₂ E₁)
    (K₂ : V₂.KnowledgeStateFunction init impl R₂ R₃ E₂)
    {ε₁ : pSpec₁.ChallengeIdx → ℝ≥0} {ε₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (h₁ : V₁.rbrKnowledgeSoundnessWorstCaseWith init impl R₁ R₂ W₁ E₁ K₁ ε₁)
    (h₂ : V₂.rbrKnowledgeSoundnessWorstCaseWith init impl R₂ R₃ W₂ E₂ K₂ ε₂) :
    (V₁.append V₂).rbrKnowledgeSoundnessWorstCaseWith init impl R₁ R₃
      (Witness W₁ W₂) (E₁.append E₂ G.out) (KnowledgeStateFunction.appendGuarded G K₁ K₂)
      (Sum.elim ε₁ ε₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  classical
  intro s i
  obtain ⟨i, rfl⟩ := ChallengeIdx.sumEquiv.surjective i
  rcases i with i | i
  · intro tr
    simp only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl]
    let tr₁ := left tr i.1.castSucc (by rfl)
    calc
      _ ≤ Pr[fun c => ∃ w₁,
          ¬ K₁ i.1.castSucc s tr₁
            (E₁.extractMid i.1 s (tr₁.concat (cast (challenge_append_inl i) c)) w₁) ∧
          K₁ i.1.succ s (tr₁.concat (cast (challenge_append_inl i) c)) w₁
        | $ᵗ ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl i))] := by
        apply probEvent_mono
        intro c _ hc
        obtain ⟨w, hprev, hnext⟩ := hc
        change ¬ state G K₁ K₂ _ s tr _ at hprev
        change state G K₁ K₂ _ s (tr.concat c) w at hnext
        refine ⟨cast (witness_left (ChallengeIdx.inl i).1.succ i.1.succ rfl) w, ?_, ?_⟩
        · intro hk
          apply hprev
          rw [state_left G K₁ K₂ i.1.castSucc rfl, extractMid_left G i.1 rfl,
            left_concat tr c i.1 rfl (challenge_append_inl i)]
          exact hk
        · have hk := (state_left G K₁ K₂ i.1.succ rfl s (tr.concat c) w).mp hnext
          rwa [left_concat tr c i.1 rfl (challenge_append_inl i)] at hk
      _ = Pr[fun c => ∃ w₁,
          ¬ K₁ i.1.castSucc s tr₁ (E₁.extractMid i.1 s (tr₁.concat c) w₁) ∧
          K₁ i.1.succ s (tr₁.concat c) w₁ | $ᵗ (pSpec₁.Challenge i)] := by
        rw [← uniformSample_challenge_append_inl (pSpec₂ := pSpec₂) i, probEvent_map]
        rfl
      _ ≤ _ := h₁ s i tr₁
  · intro tr
    simp only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr]
    let tr₁ := left tr (Fin.last m) (by simp [ChallengeIdx.inr])
    let s₂ := G.out s tr₁
    let tr₂ := right tr i.1.castSucc (by rfl)
    calc
      _ ≤ Pr[fun c => ∃ w₂,
          ¬ K₂ i.1.castSucc s₂ tr₂
            (E₂.extractMid i.1 s₂ (tr₂.concat (cast (challenge_append_inr i) c)) w₂) ∧
          K₂ i.1.succ s₂ (tr₂.concat (cast (challenge_append_inr i) c)) w₂
        | $ᵗ ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr i))] := by
        apply probEvent_mono
        intro c _ hc
        obtain ⟨w, hprev, hnext⟩ := hc
        change ¬ state G K₁ K₂ _ s tr _ at hprev
        change state G K₁ K₂ _ s (tr.concat c) w at hnext
        have hk := (state_right G K₁ K₂ i.1.succ
          (by simp [ChallengeIdx.inr, Nat.add_assoc]) (by simp)
          s (tr.concat c) w).mp hnext
        rw [left_concat_eq tr c (Fin.last m) (by simp [ChallengeIdx.inr]),
          right_concat tr c i.1 rfl (challenge_append_inr i)] at hk
        refine ⟨cast (witness_right (ChallengeIdx.inr i).1.succ i.1.succ
          (by simp [ChallengeIdx.inr, Nat.add_assoc]) (by simp)) w, ?_, hk.2⟩
        intro hp
        exact hprev (backward_right G K₁ K₂ i.1 rfl (challenge_append_inr i)
          s tr c w hk.1 hp)
      _ = Pr[fun c => ∃ w₂,
          ¬ K₂ i.1.castSucc s₂ tr₂ (E₂.extractMid i.1 s₂ (tr₂.concat c) w₂) ∧
          K₂ i.1.succ s₂ (tr₂.concat c) w₂ | $ᵗ (pSpec₂.Challenge i)] := by
        rw [← uniformSample_challenge_append_inr (pSpec₁ := pSpec₁) i, probEvent_map]
        rfl
      _ ≤ _ := h₂ s₂ i tr₂

end Verifier

end
end LeanerVM.Protocol
