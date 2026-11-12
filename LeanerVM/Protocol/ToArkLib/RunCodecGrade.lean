/-
  LeanerVM.Protocol.ToArkLib.RunCodecGrade

  A count of a prover's run against a wire, from a count of each round of the wire on the
  transcripts the prover's honest runs write. Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.RunCodec
public import LeanerVM.Protocol.ToVCVio.MonadRel

/-!
# Counting a run against a wire

For a property `𝓖 : MonadGrade w` of computations graded by a count additive along `bind` (the
hash queries a run asks, say), `RoundCodec.GradedOn 𝓖 c G k` says that the wire `c` has a count
per round summing to at most `k`, each challenge's read within its round's count and each
message's write within it on every transcript satisfying `G`. Wires compose (`GradedOn.append`,
the transcript split at the seam), and the one-round wires and the rounds of a sumcheck have their
counts (`gradedOn_msg`, `gradedOn_chal`, `gradedOn_chals`, `gradedOn_rounds`).

`Prover.runWith_graded`: if every transcript of the prover's run on given challenges
(`runWithChallenges`) satisfies `G`, the prover's run against `c` has the count `k`. A message's
write is counted at the message the prover sends, which is the message of the run on any
challenges agreeing with those drawn so far (`Prover.runToRoundWith_isRunTo`); so a write whose
count depends on the message, a list of values say, is counted on the honest messages only. The
grade must forget a map of a computation's value and be monotone in the count.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec

@[expose] public section

namespace RoundCodec

variable {w : Type → Type} [Monad w] (𝓖 : MonadGrade w)

/-- **A count of every round of a wire**, summing to at most `k`: each challenge's read within its
round's count, each message's write within it on the transcripts satisfying `G`. -/
def GradedOn {n : ℕ} {pSpec : ProtocolSpec n} (c : RoundCodec w pSpec)
    (G : pSpec.FullTranscript → Prop) (k : ℕ) : Prop :=
  ∃ g : Fin n → ℕ, ∑ i, g i ≤ k ∧
    (∀ tr, G tr → ∀ i h, 𝓖.P (c.send i h (tr i)) (g i)) ∧ ∀ i h, 𝓖.P (c.draw i h) (g i)

variable {𝓖}

theorem GradedOn.mono {n : ℕ} {pSpec : ProtocolSpec n} {c : RoundCodec w pSpec}
    {G G' : pSpec.FullTranscript → Prop} {k k' : ℕ} (h : c.GradedOn 𝓖 G k)
    (hG : ∀ tr, G' tr → G tr) (hk : k ≤ k') : c.GradedOn 𝓖 G' k' := by
  obtain ⟨g, hs, hS, hD⟩ := h
  exact ⟨g, hs.trans hk, fun tr htr ↦ hS tr (hG tr htr), hD⟩

/-! ### The seam -/

private theorem send_heq' {R : Type} {A A' : Direction} {B B' : Type}
    {f : A = .P_to_V → B → R} {f' : A' = .P_to_V → B' → R} (hA : A = A') (hB : B = B')
    (hf : HEq f f') (h : A = .P_to_V) (h' : A' = .P_to_V) {x : B} {x' : B'} (hx : HEq x x') :
    f h x = f' h' x' := by
  subst hA hB
  obtain rfl := eq_of_heq hf
  obtain rfl := eq_of_heq hx
  rfl

omit [Monad w] in
private theorem draw_heq' {A A' : Direction} {B B' : Type} {f : A = .V_to_P → w B}
    {f' : A' = .V_to_P → w B'} (hA : A = A') (hB : B = B') (hf : HEq f f') (h : A = .V_to_P)
    (h' : A' = .V_to_P) : HEq (f h) (f' h') := by
  subst hA hB
  obtain rfl := eq_of_heq hf
  rfl

private theorem grade_heq {α β : Type} (hab : α = β) {x : w α} {y : w β} (hxy : HEq x y)
    {k : ℕ} (hx : 𝓖.P x k) : 𝓖.P y k := by
  subst hab
  obtain rfl := eq_of_heq hxy
  exact hx

section Seam

variable {m n : ℕ} {p₁ : ProtocolSpec m} {p₂ : ProtocolSpec n} (c₁ : RoundCodec w p₁)
  (c₂ : RoundCodec w p₂)

omit [Monad w] in
private theorem send_left (i : Fin m) :
    HEq ((c₁.append c₂).send (Fin.castAdd n i)) (c₁.send i) := by
  change HEq (Fin.fappend₂ (A := Direction) (B := Type)
    (F := fun dir type ↦ dir = .P_to_V → type → w Unit) c₁.send c₂.send (Fin.castAdd n i)) _
  rw [Fin.fappend₂_left]
  exact cast_heq _ _

omit [Monad w] in
private theorem send_right (i : Fin n) :
    HEq ((c₁.append c₂).send (Fin.natAdd m i)) (c₂.send i) := by
  change HEq (Fin.fappend₂ (A := Direction) (B := Type)
    (F := fun dir type ↦ dir = .P_to_V → type → w Unit) c₁.send c₂.send (Fin.natAdd m i)) _
  rw [Fin.fappend₂_right]
  exact cast_heq _ _

omit [Monad w] in
private theorem draw_left (i : Fin m) :
    HEq ((c₁.append c₂).draw (Fin.castAdd n i)) (c₁.draw i) := by
  change HEq (Fin.fappend₂ (A := Direction) (B := Type)
    (F := fun dir type ↦ dir = .V_to_P → w type) c₁.draw c₂.draw (Fin.castAdd n i)) _
  rw [Fin.fappend₂_left]
  exact cast_heq _ _

omit [Monad w] in
private theorem draw_right (i : Fin n) :
    HEq ((c₁.append c₂).draw (Fin.natAdd m i)) (c₂.draw i) := by
  change HEq (Fin.fappend₂ (A := Direction) (B := Type)
    (F := fun dir type ↦ dir = .V_to_P → w type) c₁.draw c₂.draw (Fin.natAdd m i)) _
  rw [Fin.fappend₂_right]
  exact cast_heq _ _

variable {c₁ c₂}

/-- **Two wires in sequence**: their counts add, each on its half of the transcript. -/
theorem GradedOn.append {G₁ : p₁.FullTranscript → Prop} {G₂ : p₂.FullTranscript → Prop}
    {k₁ k₂ : ℕ} (h₁ : c₁.GradedOn 𝓖 G₁ k₁) (h₂ : c₂.GradedOn 𝓖 G₂ k₂) :
    (c₁.append c₂).GradedOn 𝓖 (fun tr ↦ G₁ tr.fst ∧ G₂ tr.snd) (k₁ + k₂) := by
  obtain ⟨g₁, hs₁, hS₁, hD₁⟩ := h₁
  obtain ⟨g₂, hs₂, hS₂, hD₂⟩ := h₂
  refine ⟨Fin.append g₁ g₂, ?_, fun tr hG i h ↦ ?_, fun i h ↦ ?_⟩
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    omega
  · induction i using Fin.addCases with
    | left j =>
      have hA : (p₁ ++ₚ p₂).dir (Fin.castAdd n j) = p₁.dir j := Fin.vappend_left _ _ _
      have hB : (p₁ ++ₚ p₂).Type (Fin.castAdd n j) = p₁.Type j := Fin.vappend_left _ _ _
      rw [send_heq' hA hB (send_left c₁ c₂ j) h (hA.symm.trans h)
        (FullTranscript.fst_apply_heq tr j).symm, Fin.append_left]
      exact hS₁ _ hG.1 j _
    | right j =>
      have hA : (p₁ ++ₚ p₂).dir (Fin.natAdd m j) = p₂.dir j := Fin.vappend_right _ _ _
      have hB : (p₁ ++ₚ p₂).Type (Fin.natAdd m j) = p₂.Type j := Fin.vappend_right _ _ _
      rw [send_heq' hA hB (send_right c₁ c₂ j) h (hA.symm.trans h)
        (FullTranscript.snd_apply_heq tr j).symm, Fin.append_right]
      exact hS₂ _ hG.2 j _
  · induction i using Fin.addCases with
    | left j =>
      have hA : (p₁ ++ₚ p₂).dir (Fin.castAdd n j) = p₁.dir j := Fin.vappend_left _ _ _
      have hB : (p₁ ++ₚ p₂).Type (Fin.castAdd n j) = p₁.Type j := Fin.vappend_left _ _ _
      rw [Fin.append_left]
      exact grade_heq hB.symm (draw_heq' hA hB (draw_left c₁ c₂ j) h (hA.symm.trans h)).symm
        (hD₁ j _)
    | right j =>
      have hA : (p₁ ++ₚ p₂).dir (Fin.natAdd m j) = p₂.dir j := Fin.vappend_right _ _ _
      have hB : (p₁ ++ₚ p₂).Type (Fin.natAdd m j) = p₂.Type j := Fin.vappend_right _ _ _
      rw [Fin.append_right]
      exact grade_heq hB.symm (draw_heq' hA hB (draw_right c₁ c₂ j) h (hA.symm.trans h)).symm
        (hD₂ j _)

end Seam

/-! ### The schedules' wires -/

theorem gradedOn_empty {G : (!p[] : ProtocolSpec 0).FullTranscript → Prop} :
    (empty : RoundCodec w !p[]).GradedOn 𝓖 G 0 :=
  ⟨fun i ↦ i.elim0, by simp, fun _ _ i ↦ i.elim0, fun i ↦ i.elim0⟩

theorem gradedOn_msg {M : Type} {enc : M → w Unit} {G : (say M).FullTranscript → Prop} {k : ℕ}
    (h : ∀ x, 𝓖.P (enc x) k) : (msg enc).GradedOn 𝓖 G k :=
  ⟨fun _ ↦ k, by simp, fun tr _ i hi ↦ (match i, hi with | ⟨0, _⟩, _ => h _),
    fun i hi ↦ match i, hi with | ⟨0, _⟩, h => nomatch h⟩

theorem gradedOn_sendOne {M : Type} {enc : M → w Unit}
    {G : (⟨!v[.P_to_V], !v[M]⟩ : ProtocolSpec 1).FullTranscript → Prop} {k : ℕ}
    (h : ∀ x, 𝓖.P (enc x) k) : (sendOne enc).GradedOn 𝓖 G k :=
  ⟨fun _ ↦ k, by simp, fun tr _ i hi ↦ (match i, hi with | ⟨0, _⟩, _ => h _),
    fun i hi ↦ match i, hi with | ⟨0, _⟩, h => nomatch h⟩

theorem gradedOn_chal {C : Type} {smp : w C} {G : (Protocol.draw C).FullTranscript → Prop}
    {k : ℕ} (h : 𝓖.P smp k) : (chal smp).GradedOn 𝓖 G k :=
  ⟨fun _ ↦ k, by simp, fun _ _ i hi ↦ (match i, hi with | ⟨0, _⟩, h => nomatch h),
    fun i hi ↦ match i, hi with | ⟨0, _⟩, _ => h⟩

theorem gradedOn_chals {C : Type} {smp : w C} {k : ℕ} (h : 𝓖.P smp k) :
    ∀ r, (chals smp r).GradedOn 𝓖 (fun _ ↦ True) (r * k)
  | 0 => gradedOn_empty.mono (fun _ _ ↦ trivial) (by simp)
  | r + 1 => ((gradedOn_chals h r).append (gradedOn_chal (G := fun _ ↦ True) h)).mono
      (fun _ _ ↦ ⟨trivial, trivial⟩) (by rw [Nat.succ_mul])

theorem gradedOn_rounds {C : Type} {d : ℕ} {enc : Vector C (d + 1) → w Unit} {smp : w C}
    {a b : ℕ} (henc : ∀ x, 𝓖.P (enc x) a) (hsmp : 𝓖.P smp b) :
    ∀ r, (rounds enc smp r).GradedOn 𝓖 (fun _ ↦ True) (r * (a + b))
  | 0 => gradedOn_empty.mono (fun _ _ ↦ trivial) (by simp)
  | r + 1 => (((gradedOn_msg (G := fun _ ↦ True) henc).append
      (gradedOn_chal (G := fun _ ↦ True) hsmp)).append (gradedOn_rounds henc hsmp r)).mono
      (fun _ _ ↦ ⟨⟨trivial, trivial⟩, trivial⟩) (by rw [Nat.succ_mul]; omega)

end RoundCodec

/-! ## The run, counted -/

namespace Prover

variable {S W S' W' : Type} {n : ℕ} {pSpec : ProtocolSpec n} (P : Prover []ₒ S W S' W' pSpec)
  (stmt : S) (wit : W)

/-- The run on given challenges up to round `i`. -/
abbrev runTo (ch : pSpec.Challenges) (i : Fin (n + 1)) :
    pSpec.Transcript i × P.PrvState i :=
  Id.run (runToRoundWith (RoundCodec.ofChallenges ch) P i stmt wit)

/-- Round `j` on given challenges extends the transcript before it. -/
private theorem runTo_succ (ch : pSpec.Challenges) (j : Fin n) :
    ∃ x, (runTo P stmt wit ch j.succ).1 = (runTo P stmt wit ch j.castSucc).1.concat x := by
  show ∃ x, (Id.run (stepWith (RoundCodec.ofChallenges ch) P j
    (runTo P stmt wit ch j.castSucc).1 (runTo P stmt wit ch j.castSucc).2)).1 = _
  unfold stepWith
  split <;> exact ⟨_, rfl⟩

/-- A message round on given challenges appends the message the prover sends. -/
private theorem runTo_succ_send (ch : pSpec.Challenges) (j : Fin n)
    (h : pSpec.dir j = .P_to_V) :
    (runTo P stmt wit ch j.succ).1 = (runTo P stmt wit ch j.castSucc).1.concat
      (Id.run (runNoOracle (P.sendMessage ⟨j, h⟩ (runTo P stmt wit ch j.castSucc).2))).1 := by
  show (Id.run (stepWith (RoundCodec.ofChallenges ch) P j
    (runTo P stmt wit ch j.castSucc).1 (runTo P stmt wit ch j.castSucc).2)).1 = _
  unfold stepWith
  split
  · rename_i h'
    exact absurd (h.symm.trans h') (by decide)
  · rfl

/-- A round's value is kept by the later rounds. -/
private theorem runTo_prefix (ch : pSpec.Challenges) :
    ∀ (i : Fin (n + 1)) (k : ℕ) (hk : k < i.val),
      HEq ((runTo P stmt wit ch i).1 ⟨k, hk⟩)
        ((runTo P stmt wit ch ⟨k + 1, by omega⟩).1 ⟨k, by simp⟩) := by
  intro i
  induction i using Fin.induction with
  | zero => intro k hk; exact absurd hk (by simp)
  | succ j ih =>
    intro k hk
    obtain ⟨x, hx⟩ := runTo_succ P stmt wit ch j
    by_cases hkj : k < j.val
    · rw [hx]
      exact (Transcript.concat_apply_lt _ x k hkj hk).trans (ih k hkj)
    · have hk' : k = j.val := by simp at hk; omega
      subst hk'
      rfl

/-- **The message of round `j` of the run on given challenges** is the message the prover sends
from its state before round `j`. -/
theorem runWithChallenges_message (ch : pSpec.Challenges) (j : Fin n)
    (h : pSpec.dir j = .P_to_V) :
    (runWithChallenges P ch stmt wit).1 j =
      (Id.run (runNoOracle (P.sendMessage ⟨j, h⟩ (runTo P stmt wit ch j.castSucc).2))).1 := by
  have h₁ := runTo_prefix P stmt wit ch (Fin.last n) j.val (by simp)
  have h₂ : HEq ((runTo P stmt wit ch j.succ).1 ⟨j.val, by simp⟩)
      (Id.run (runNoOracle (P.sendMessage ⟨j, h⟩ (runTo P stmt wit ch j.castSucc).2))).1 := by
    rw [runTo_succ_send P stmt wit ch j h]
    exact Transcript.concat_apply_last _ _ _ rfl _
  exact eq_of_heq (h₁.trans h₂)

variable {w : Type → Type} [Monad w] [LawfulMonad w] {𝓖 : MonadGrade w}
  (hmap : ∀ {α β : Type} (f : α → β) (x : w α) (k : ℕ), 𝓖.P (f <$> x) k → 𝓖.P x k)
  (hmono : ∀ {α : Type} (x : w α) (k k' : ℕ), 𝓖.P x k → k ≤ k' → 𝓖.P x k')
include hmap hmono

/-- **A run against a counted wire is counted**: if every transcript of the prover's runs on
given challenges satisfies `G`, its run against a wire with count `k` on `G` has the count `k`. -/
theorem runWith_graded [∀ i, Nonempty (pSpec.Challenge i)] {c : RoundCodec w pSpec}
    {G : pSpec.FullTranscript → Prop} {k : ℕ} (hc : c.GradedOn 𝓖 G k)
    (hG : ∀ ch, G (runWithChallenges P ch stmt wit).1) : 𝓖.P (runWith c P stmt wit) k := by
  obtain ⟨g, hs, hS, hD⟩ := hc
  have step : ∀ (j : Fin n) (r : pSpec.Transcript j.castSucc × P.PrvState j.castSucc),
      IsRunTo P stmt wit r → 𝓖.P (stepWith c P j r.1 r.2) (g j) := by
    intro j r hr
    unfold stepWith
    split
    · rename_i hDir
      rw [runNoOracle_eq_pure]
      simp only [pure_bind]
      exact 𝓖.of_eq (𝓖.bind (hD j hDir) fun _ ↦ 𝓖.pure _) (Nat.add_zero _)
    · rename_i hDir
      rw [runNoOracle_eq_pure]
      simp only [pure_bind]
      refine 𝓖.of_eq (𝓖.bind ?_ fun _ ↦ 𝓖.pure _) (Nat.add_zero _)
      classical
      let ch : pSpec.Challenges := fun i ↦
        if hi : i.1.val < j.val then r.1 ⟨i.1.val, hi⟩ else Classical.choice inferInstance
      have hag : ChallengesAgree r.1 ch := fun i hi ↦ dite_eq_left hi
      have hm := runWithChallenges_message P stmt wit ch j hDir
      rw [show runTo P stmt wit ch j.castSucc = r from hr ch hag] at hm
      rw [← hm]
      exact hS _ (hG ch) j hDir
  have hround : ∀ i : Fin (n + 1), 𝓖.P (runToRoundWith c P i stmt wit)
      (∑ j ∈ Finset.univ.filter fun j : Fin n ↦ j.val < i.val, g j) := by
    intro i
    induction i using Fin.induction with
    | zero => exact 𝓖.of_eq (𝓖.pure _) (by simp)
    | succ j ih =>
      rw [runToRoundWith_succ, processRoundWith]
      obtain ⟨cur, hcur⟩ := runToRoundWith_isRunTo P c stmt wit j.castSucc
      rw [← hcur] at ih ⊢
      rw [bind_map_left]
      refine 𝓖.of_eq (𝓖.bind (hmap _ _ _ ih) fun r ↦ step j r.1 r.2) ?_
      have : (Finset.univ.filter fun i : Fin n ↦ i.val < j.succ.val) =
          insert j (Finset.univ.filter fun i : Fin n ↦ i.val < j.castSucc.val) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Fin.val_succ, Fin.val_castSucc]
        constructor
        · intro h
          by_cases hij : i = j
          · exact .inl hij
          · exact .inr (by have := Fin.val_ne_of_ne hij; omega)
        · rintro (rfl | h) <;> omega
      rw [this, Finset.sum_insert (by simp), add_comm]
  unfold runWith
  refine hmono _ _ _ (𝓖.of_eq (𝓖.bind (hround (Fin.last n)) fun r ↦
    (by rw [runNoOracle_eq_pure, pure_bind]; exact 𝓖.pure _ : 𝓖.P _ 0)) (Nat.add_zero _)) ?_
  refine le_trans (Finset.sum_le_sum_of_subset (fun _ _ ↦ Finset.mem_univ _)) hs

end Prover

end
end LeanerVM.Protocol
