/-
  LeanerVM.Protocol.Core.Solved

  A transcript the verifier's chain history decodes to is solved: every round polynomial of WHIR's
  opening passes its check against the oracle verifier's running claim, as the front phases' do.
-/

module

public import LeanerVM.Protocol.Core.Decoded
public import LeanerVM.Protocol.Compile.Agree

/-!
# The decoded transcript is solved

The decoder reads each of WHIR's round polynomials by `polySlot`, which keeps only polynomials
that pass their check against the decoder's running claim. The decoder's running claims are the
oracle verifier's (`Compile.foldsOut`, `Compile.levelQuery`, `Compile.levelNext`,
`Compile.finalQuery`, `Compile.finalTail`): the fold rounds' verdict has the challenges as its
point and the decoder's claim as its claim (`out_roundsFront`), the query batch is the decoder's
batch of the word's folded rows at the positions, and the claim a level hands on is the decoder's.
So the decoded opening is solved (`Compile.WhirSolved`, `whirSolved_of_decode`), and with the
front (`front_of_decode`) the whole transcript is (`Compile.Solved`, `solved_of_decode`).
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics Blake2sHash LeanIsa ProtocolSpec StepSchedule Verify
open DecodeChain Whir SlotDecoder Compile SumcheckRound CompPoly CMlPolynomialEval

@[expose] public section

namespace Core

/-! ## Checks and rounds -/

private theorem chk_of_check {claim : E} {q : SumcheckRound.Message E 2}
    (h : RoundPoly.Check claim none q) : Whir.chk q claim = true := by
  rw [Whir.chk, decide_eq_true_iff, show unitDom = eqDomain none from rfl, ← check_iff]
  exact h

/-- Rounds with no equality weight pass their checks whatever round they start at. -/
private theorem roundsSolved_none {d : ℕ} :
    ∀ (m j j' : ℕ) (c : E) (t : (roundsSpec E d m).FullTranscript),
      RoundsSolved (fun _ ↦ none) m j c t → RoundsSolved (fun _ ↦ none) m j' c t
  | 0, _, _, _, _, _ => trivial
  | m + 1, _, _, _, _, h => ⟨h.1, roundsSolved_none m _ _ _ _ h.2⟩

private theorem seqHead_append {a : Step} {l : List Step} (t₁ : a.spec.FullTranscript)
    (T : (seqSpec l).FullTranscript) : seqHead (a := a) (l := l) (t₁ ++ₜ T) = t₁ :=
  FullTranscript.append_fst t₁ T

private theorem seqTail_append {a : Step} {l : List Step} (t₁ : a.spec.FullTranscript)
    (T : (seqSpec l).FullTranscript) : seqTail (a := a) (l := l) (t₁ ++ₜ T) = T :=
  FullTranscript.append_snd t₁ T

/-- A list of steps' decoder, through its first step, on the whole transcript's head and tail. -/
private theorem always_cons {a : Step} {l : List Step} {D : SeqDecoder Reading (a :: l)}
    {P : a.spec.FullTranscript → Prop} {Q : (seqSpec (a :: l)).FullTranscript → Prop}
    (h₁ : Always D.1.toSlot P)
    (h₂ : ∀ t₁, P t₁ → Always (D.2 t₁).toDecoder.toSlot fun T ↦
      ∀ t : (seqSpec (a :: l)).FullTranscript, seqHead t = t₁ → seqTail t = T → Q t) :
    Always D.toDecoder.toSlot Q :=
  always_append h₁ (fun t₁ h ↦ (h₂ t₁ h).mono fun T hT ↦
    hT _ (seqHead_append t₁ T) (seqTail_append t₁ T)) fun _ _ _ h ↦ h

/-- The fold rounds' verdict: its point the challenges, its claim the decoder's running claim. -/
private theorem foldsOut_eq {sh : Whir.Shape} {κ : ℕ} {l : List Step} (W : Weight E (sh.ℓ + κ))
    (claim : E) (quad : SumcheckRound.Message E 2)
    (t : (seqSpec (.chal E inferInstance :: .rds E inferInstance 2 sh.lm1 :: l)).FullTranscript) :
    (foldsOut W claim quad t).2.1 =
        toVec sh.ℓ (drawOf (seqHead t) :: roundsChals sh.lm1 (seqHead (seqTail t))) ∧
      (foldsOut W claim quad t).2.2 =
        (roundsNext (Thunk.mk fun _ ↦ RoundPoly.eval quad (drawOf (seqHead t)), 0) sh.lm1
          (seqHead (seqTail t))).1.get := by
  obtain ⟨-, h₂, h₃⟩ := out_roundsFront (levelFamily sh κ).poly (levelFamily sh κ).weight sh.ℓ
    sh.lm1 (0 + 1) (by simp only [Whir.Shape.ℓ]; omega)
    (SumcheckRound.next 0 (W, (#v[], claim)) (SumcheckRound.evaluate 2 quad (drawOf (seqHead t)))
      (drawOf (seqHead t))) (seqHead (seqTail t))
    (Thunk.mk fun _ ↦ RoundPoly.eval quad (drawOf (seqHead t)), 0) (eval_eq_evaluate _ _)
  exact ⟨by rw [← toVec_toList (foldsOut W claim quad t).2.1]; exact congrArg _ h₂, h₃⟩

/-! ## A level -/

/-- A level's query batch is the batch of the word's folded rows at the positions, folded at the
level's challenges. -/
private theorem levelQuery_eq {sh sh' : Whir.Shape} {κ' : ℕ} {k : List Step}
    (W : Weight E (sh.ℓ + Kap sh' κ')) (claim : E) (quad : SumcheckRound.Message E 2)
    (x : WordOf sh (Kap sh' κ')) (t : (seqSpec (levelSteps sh sh' κ' k)).FullTranscript) :
    levelQuery W claim quad x t =
      queryClaim x (toVec sh.ℓ (drawOf (seqHead t) :: roundsChals sh.lm1 (seqHead (seqTail t))))
        (Prove.levelPositions t) (levelWire t).1.lam := by
  rw [levelQuery, (foldsOut_eq W claim quad t).1]
  simp only [queryClaim, foldRows_getElem]


/-- **A level's decoded rounds are solved**, from the decoder's running claim and polynomial: the
level's round polynomials pass their checks, the word it sends is the supplied one, and the decoder
goes on from the claim and polynomial the oracle verifier hands on. -/
private theorem always_levelDec_solved (sh sh' : Whir.Shape) (κ' : ℕ) {k : List Step}
    (σ : Thunk E × Thunk (Vector E 3)) (w : WordOf sh (Kap sh' κ')) (next : WordOf sh' κ')
    {cont : Thunk E × Thunk (Vector E 3) → SeqDecoder Reading k}
    {P : Thunk E × Thunk (Vector E 3) → (seqSpec k).FullTranscript → Prop}
    (hc : ∀ σ', Always (cont σ').toDecoder.toSlot (P σ')) :
    Always (levelDec sh sh' κ' σ w next cont).toDecoder.toSlot fun t ↦
      (∀ W, LevelSolved W σ.1.get σ.2.get w t) ∧ Prove.levelWord t = next ∧
        ∃ σ' : Thunk E × Thunk (Vector E 3),
          (∀ W, σ'.1.get = (levelNext W σ.1.get σ.2.get w t).1.2.2 ∧
            σ'.2.get = (levelNext W σ.1.get σ.2.get w t).2) ∧ P σ' (levelWire t).2 := by
  have key : Always ((fun _ ↦ next) <$> historyOps.nextRoot : Slot Reading (WordOf sh' κ'))
      (· = next) :=
    Always.map ((Always.true _).mono fun _ _ ↦ rfl)
  refine always_cons (Always.true _) fun t₁ _ ↦ ?_
  refine always_cons (always_roundsDec 2 (fun _ ↦ none) sh.lm1
    (Thunk.mk fun _ ↦ RoundPoly.eval σ.2.get (drawOf t₁), 0)) fun t₂ h₂ ↦ ?_
  refine always_cons (always_single (always_polySlot 2
    (roundsNext (Thunk.mk fun _ ↦ RoundPoly.eval σ.2.get (drawOf t₁), 0) sh.lm1 t₂).1
    (Thunk.pure none))) fun t₃ h₃ ↦ ?_
  refine always_cons (always_single (pSpec := (Step.oracle (WordOf sh' κ') inferInstance).spec)
    (P := fun x ↦ x = next) key) fun t₄ h₄ ↦ ?_
  refine always_cons (Always.true _) fun t₅ _ ↦ ?_
  refine always_cons (Always.true _) fun t₆ _ ↦ ?_
  refine always_cons (always_single (always_polySlot 2 (Thunk.mk fun _ ↦ msgOf t₆)
    (Thunk.pure none))) fun t₇ h₇ ↦ ?_
  refine always_cons (Always.true _) fun t₈ _ ↦ ?_
  refine always_cons (Always.true _) fun t₉ _ ↦ ?_
  refine always_cons (Always.true _) fun t₁₀ _ ↦ ?_
  refine always_cons (Always.true _) fun t₁₁ _ ↦ ?_
  refine always_cons (always_single (always_polySlot 2
    (Thunk.mk fun _ ↦ queryClaim w
      (Thunk.mk fun _ ↦ toVec sh.ℓ (drawOf t₁ :: roundsChals sh.lm1 t₂)).get (drawOf t₉)
      (drawOf t₁₀)) (Thunk.pure none))) fun t₁₂ h₁₂ ↦ ?_
  refine always_cons (Always.true _) fun t₁₃ _ ↦ ?_
  refine (hc _).mono fun T hT ↦ ?_
  rintro _ rfl rfl _ rfl rfl _ rfl rfl _ rfl rfl _ rfl rfl _ rfl rfl _ rfl rfl _ rfl rfl _ rfl rfl
    _ rfl rfl _ rfl rfl _ rfl rfl t rfl rfl
  refine ⟨fun W ↦ ?_, h₄, _, fun W ↦ ⟨?_, ?_⟩, hT⟩
  · rw [LevelSolved, levelQuery_eq, (foldsOut_eq W _ _ _).2]
    exact ⟨roundsSolved_none _ _ _ _ _ h₂, chk_of_check h₃, chk_of_check h₇, chk_of_check h₁₂⟩
  · rw [levelNext, levelQuery_eq, (foldsOut_eq W _ _ _).2]
    rfl
  · rfl

/-! ## The final level -/

/-- The final level's query batch is the batch of the word's folded rows at the positions, folded
at the level's challenges. -/
private theorem finalQuery_eq {sh : Whir.Shape} {nf : ℕ} (W : Weight E (sh.ℓ + (nf + 1)))
    (claim : E) (quad : SumcheckRound.Message E 2) (x : WordOf sh (nf + 1))
    (t : (seqSpec (finalSteps sh nf)).FullTranscript) :
    finalQuery W claim quad x t =
      queryClaim x (toVec sh.ℓ (drawOf (seqHead t) :: roundsChals sh.lm1 (seqHead (seqTail t))))
        (Prove.finalPositions t) (finalWire t).lam := by
  rw [finalQuery, (foldsOut_eq W claim quad t).1]
  simp only [queryClaim, foldRows_getElem]

/-- **The final level's decoded rounds are solved**, from the decoder's running claim and
polynomial. -/
private theorem always_finalDec_solved (sh : Whir.Shape) (nf : ℕ)
    (σ : Thunk E × Thunk (Vector E 3)) (w : WordOf sh (nf + 1)) :
    Always (finalDec sh nf σ w).toDecoder.toSlot fun t ↦
      ∀ W, FinalSolved W σ.1.get σ.2.get w t := by
  refine always_cons (Always.true _) fun t₁ _ ↦ ?_
  refine always_cons (always_roundsDec 2 (fun _ ↦ none) sh.lm1
    (Thunk.mk fun _ ↦ RoundPoly.eval σ.2.get (drawOf t₁), 0)) fun t₂ h₂ ↦ ?_
  refine always_cons (always_single (always_polySlot 2
    (roundsNext (Thunk.mk fun _ ↦ RoundPoly.eval σ.2.get (drawOf t₁), 0) sh.lm1 t₂).1
    (Thunk.pure none))) fun t₃ h₃ ↦ ?_
  refine always_cons (Always.true _) fun t₄ _ ↦ ?_
  refine always_cons (Always.true _) fun t₅ _ ↦ ?_
  refine always_cons (Always.true _) fun t₆ _ ↦ ?_
  refine always_cons (Always.true _) fun t₇ _ ↦ ?_
  refine always_cons (Always.true _) fun t₈ _ ↦ ?_
  refine always_cons (always_single (always_polySlot 2
    (Thunk.mk fun _ ↦ queryClaim w
      (Thunk.mk fun _ ↦ toVec sh.ℓ (drawOf t₁ :: roundsChals sh.lm1 t₂)).get (drawOf t₆)
      (drawOf t₇)) (Thunk.pure none))) fun t₉ h₉ ↦ ?_
  refine always_cons (Always.true _) fun t₁₀ _ ↦ ?_
  refine always_cons (Always.true _) fun t₁₁ _ ↦ ?_
  refine always_cons (always_roundsDec 2 (fun _ ↦ none) nf
    (Thunk.mk fun _ ↦ RoundPoly.eval
      (Thunk.mk fun _ ↦ batchMessage ![msgOf t₃, msgOf t₉] (drawOf t₇)).get (drawOf t₁₁), 0))
    fun t₁₂ h₁₂ ↦ ?_
  refine (Always.true _).mono fun T _ ↦ ?_
  rintro _ rfl rfl _ rfl rfl _ rfl rfl _ rfl rfl _ rfl rfl _ rfl rfl
    _ rfl rfl _ rfl rfl _ rfl rfl _ rfl rfl _ rfl rfl t rfl rfl W
  rw [FinalSolved, finalQuery_eq, (foldsOut_eq W _ _ _).2]
  exact ⟨roundsSolved_none _ _ _ _ _ h₂, chk_of_check h₃, chk_of_check h₉,
    roundsSolved_none _ _ _ _ _ h₁₂⟩

/-! ## The chain and the opening -/

/-- **A chain of levels' decoded rounds are solved**, from the decoder's running claim and
polynomial, on the supplied words. -/
private theorem always_ladderDec_solved : ∀ {sh : Whir.Shape} {κ : ℕ} (L : Ladder sh κ)
    (σ : Thunk E × Thunk (Vector E 3)) (w : WordOf sh κ) (ws : L.Words),
    Always (ladderDec L σ w ws).toDecoder.toSlot fun t ↦
      ∀ W, LadderSolved L W σ.1.get σ.2.get w t
  | _, _, .last sh nf, σ, w, _ => always_finalDec_solved sh nf σ w
  | _, _, @Ladder.cons sh sh' κ' L, σ, w, ws =>
    (always_levelDec_solved sh sh' κ' σ w ws.1
      (P := fun σ' T ↦ ∀ W, LadderSolved L W σ'.1.get σ'.2.get ws.1 T)
      fun σ' ↦ always_ladderDec_solved L σ' ws.1 ws.2).mono fun t ⟨hs, hw, σ', hσ', hP⟩ W ↦ by
      have h := hP (levelNext W σ.1.get σ.2.get w t).1.1
      rw [(hσ' W).1, (hσ' W).2, ← hw] at h
      exact ⟨hs W, h⟩

/-- **WHIR's decoded opening is solved**, on the opening claim's value `c` and the supplied
words. -/
private theorem always_whirDec_solved {sh : Whir.Shape} {κ : ℕ} (L : Ladder sh κ) (c : E)
    (w : WordOf sh κ) (ws : L.Words) :
    Always (whirDec L (Thunk.mk fun _ ↦ c) w ws).toDecoder.toSlot fun t ↦
      ∀ W, WhirSolved L W c w t := by
  refine always_cons (Always.true _) fun t₁ _ ↦ ?_
  refine always_cons (always_single (always_polySlot 2 (Thunk.mk fun _ ↦ c) (Thunk.pure none)))
    fun t₂ h₂ ↦ ?_
  refine (always_ladderDec_solved L _ w ws).mono fun T hT ↦ ?_
  rintro _ rfl rfl t rfl rfl W
  exact ⟨chk_of_check h₂, hT _⟩

/-- A decoder's two halves, each transcript's property read on the halves of the whole. -/
private theorem always_append_halves {m n : ℕ} {pSpec₁ : ProtocolSpec m}
    {pSpec₂ : ProtocolSpec n} {D₁ : SlotDecoder Reading pSpec₁}
    {D₂ : pSpec₁.FullTranscript → SlotDecoder Reading pSpec₂}
    {R : pSpec₁.FullTranscript → pSpec₂.FullTranscript → Prop}
    (h : ∀ t₁, Always (D₂ t₁).toSlot (R t₁)) :
    Always (D₁.append D₂).toSlot fun t ↦ R t.fst t.snd :=
  always_append (Always.true _) (fun t₁ _ ↦ h t₁) fun t₁ t₂ _ h₂ ↦ by
    rw [FullTranscript.append_fst, FullTranscript.append_snd]
    exact h₂

/-! ## The whole transcript -/

-- The stack's size is never computed here: sealed, unification does not evaluate it on a
-- symbolic program.
attribute [local irreducible] LeanIsa.leanIsaμ LeanIsa.blocks

/-- **A decoded transcript is solved**: at leanVM, the round polynomials of a transcript the
verifier's history decodes to pass their checks against the oracle verifier's claims. -/
theorem solved_of_decode {prog : Program} {input : PublicInput} {s : Sizes}
    {hs : s.Admissible prog} {ρ : ℕ} {hρ : validRate ρ} {W : LeanWords prog s hs ρ hρ}
    {hist : List Reading}
    {tr : (deployedSpec Blake2sFlock.blake2sFlockSpec prog s hs ρ hρ).FullTranscript}
    (h : DecodeChain.decode prog input s hs ρ hρ W hist = some tr) :
    Solved prog s hs ρ hρ input tr := by
  obtain ⟨h0, hB, hT, hF⟩ := front_of_decode h
  have hdec : (compiledDec (leanVm prog s) (leanIsa_conditions _ prog s) input (announcement s ρ)
      (leanIsaChain prog s hs ρ hρ) W).decode hist = some tr := h
  have hW := Always.of_decode (always_append_halves
    (R := fun t₁ t₂ ↦ ∀ Wt, WhirSolved (leanIsaChain prog s hs ρ hρ).ladder Wt
      (targetOf (leanVm prog s) (leanIsa_conditions _ prog s) input t₁) W.level0.lift t₂)
    fun _ ↦ always_whirDec_solved _ _ _ _) hdec
  refine ⟨hB, hT, hF, ?_⟩
  rw [h0]
  exact hW _

end Core

end

end LeanerVM.Protocol
