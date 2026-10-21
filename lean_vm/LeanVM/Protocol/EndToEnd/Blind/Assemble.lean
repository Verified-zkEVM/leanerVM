/-
  LeanVM.Protocol.EndToEnd.Blind.Assemble

  The specification of the Flock-blind verifier program V°, composed from the deployed phase
  specifications at the leanISA instance without a Flock region, at `εmax = 2^-128` per group of
  challenges, and the doom certificate it gives.
-/

module

public import LeanVM.Protocol.EndToEnd.Sound.Assemble
public import LeanVM.Protocol.EndToEnd.Blind.Relation
public import LeanVM.Spec.Ideal.Blind

/-!
# The specification of the Flock-blind verifier

`blindSpec prog input` is a specification of `blindProgram (bytecodeWords prog)
(publicDigest input)` (`LeanVM.Spec.Ideal.Blind`: the deployed program with the lincheck's terminal
check deleted) from no doom, with postcondition rejection, at `εmax = 2^-128` and lead `0`;
`blindCert` is its doom certificate. It composes as `leanVmSpec` does (`Sound.Assemble`), with
three changes:

1. the stack's root creates `CommitPostBlind`: no candidate of the committed word satisfies
   `M3HoldsBlind`, the relation without Flock's R1CS, which is `M3Holds` of the leanISA instance
   without a Flock region (`m3Holds_none_iff`);
2. the bus, the table sumcheck and the public input are the deployed phase specifications at that
   instance (`busTableSpec_leanIsa`, `pubPhaseSpecWith` at `fl = none`): their doom carries no
   Flock predicate, and after the public input it is `ClaimsDoom`, no candidate satisfies the
   column claims;
3. Flock (`verifyFlockBlind`) and ring switching make no claim the doom depends on: each keeps
   it (`Spec.keep`), ring switching to `RingPost` (no candidate satisfies the claims and the ring
   claim, since none satisfies the claims), and the stacked opening is the deployed one
   (`stackedPart`).

Ring switching's challenges and the opening's batching challenge are one group, as deployed; the
public input's challenge is a group alone (Flock's first prover move ends it), charged
`L₀ · 231/|E|` with the lead after it (`pubLeadBlind_le`). Every group's escape is at most
`2^-128`.
-/

namespace LeanVM.Protocol.EndToEnd.Blind

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Sound
open LeanVM.Protocol.EndToEnd.Complete (publicDigest)
open scoped ENNReal NNReal

@[expose] public section

/-! ## A phase that keeps the doom -/

section Keep

variable {α : Type} {p : Prog α} {J : List Ev → Prop} {Post : α → List Ev → Prop}
  {εmax T : ℝ≥0∞}

/-- The average over a challenge of a constant is the constant. -/
theorem avg_const (x : ℝ≥0∞) : (Fintype.card E : ℝ≥0∞)⁻¹ * ∑ _c : E, x = x := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]

open Classical in
/-- **A phase that keeps the doom**: from `J` to `Post`, where every return after a history in
`J` is in `Post`. No challenge of the phase is charged: the potential is the follower's lead `T`
throughout. -/
noncomputable def Spec.keep (hT : T ≤ εmax)
    (hpost : ∀ h₀ l a, p.Reach h₀ l → p.after l = some (.ret a) → J h₀ → Post a (h₀ ++ l)) :
    Spec p J Post εmax T T where
  D h₀ _ := J h₀
  V h₀ _ := if J h₀ then min 1 T else 1
  le_one h₀ _ := by split_ifs; exacts [min_le_left _ _, le_rfl]
  start_D _ h := h
  start_V h₀ h := by simp only [h, ↓reduceIte]; exact min_le_right _ _
  read _ _ _ h := h
  grind _ _ h := h
  commit _ _ _ _ h := h
  sample _ _ := (avg_const _).le
  query _ _ _ := le_rfl
  moveEnd _ _ _ hD := by simp [hD]
  retEnd _ _ hD := by simp [hD]
  retDoom _ _ hD := by simp [hD]
  post hl ha hD := hpost _ _ _ hl ha hD
  bound _ _ _ hD := by
    simp only [hD, ↓reduceIte]
    refine (mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le ?_)).trans
      ((min_le_right _ _).trans hT)
    exact ENNReal.inv_le_one.2 (by norm_num)

end Keep

/-! ## The program after the announced sizes -/

/-- `verifyExecutionBlind` after the announced sizes `(layout, ρ)`. -/
def veBodyBlind (publicInput : Digest) (layout : Verifier.Layout) (ρ : ℕ) : Prog Unit := do
  Verifier.commitStack layout.stackLog ρ
  let bus ← Verifier.verifyBusBalance .computed layout
  let claims ← Verifier.tablePhase layout bus
  let publicClaims ← Verifier.publicInputPhase layout publicInput
  let claims := claims ++ publicClaims
  let (flockPoint, flockS) ←
    verifyFlockBlind (blake2sR1csLogSize + layout.tableLogHeights.getD opBlake2s 0)
  let (ringTarget, ringWeight) ← Verifier.ringSwitch flockPoint flockS
  Verifier.verifyStackedOpening layout.stackLog ρ
    (Verifier.ringSwitchClaim layout ringTarget ringWeight :: claims.map (·.onStack layout))

/-- `verifyExecutionBlind` is the announced sizes, then `veBodyBlind`. -/
theorem verifyExecutionBlind_eq (bytecode : List K) (publicInput : Digest) :
    verifyExecutionBlind bytecode publicInput =
      (readSizes bytecode).bind fun a ↦ veBodyBlind publicInput a.1 a.2 := rfl

/-! ## The prover's moves -/

section Moves

attribute [local irreducible] MovesOK

/-- The lincheck without its terminal check is reads and samples. -/
theorem movesOK_verifyFlockLincheckBlind (zc : ZerocheckResult) :
    MovesOK (fun _ ↦ False) False (verifyFlockLincheckBlind zc) := by
  refine MovesOK.seq MovesOK.sampleE fun _ ↦ MovesOK.seq (movesOK_sumcheck _ _ _) fun r ↦ ?_
  obtain ⟨roundChallenges, rLc⟩ := r
  exact MovesOK.seq (MovesOK.readN _) fun _ ↦ MovesOK.pure _

/-- Flock without its terminal check makes no prover move other than reads. -/
theorem movesOK_verifyFlockBlind (logN : ℕ) :
    MovesOK (fun _ ↦ False) False (verifyFlockBlind logN) :=
  MovesOK.seq (movesOK_verifyFlockZerocheck logN) fun zc ↦ movesOK_verifyFlockLincheckBlind zc

/-- `verifyExecutionBlind`: commitments, and proofs of work of `Whir.queryGrindingBits` bits. -/
theorem movesOK_verifyExecutionBlind (bytecode : List K) (publicInput : Digest) :
    MovesOK (· = Whir.queryGrindingBits) True (verifyExecutionBlind bytecode publicInput) := by
  refine MovesOK.seq (MovesOK.of_none (movesOK_readSizes bytecode)) fun p ↦ ?_
  obtain ⟨layout, logInverseRate⟩ := p
  refine MovesOK.seq ((movesOK_commitStack _ _).mono (fun _ h ↦ h.elim) id) fun _ ↦
    MovesOK.seq (MovesOK.of_none (movesOK_verifyBusBalance layout)) fun bus ↦
      MovesOK.seq (MovesOK.of_none (movesOK_tablePhase layout bus)) fun _ ↦
        MovesOK.seq (MovesOK.of_none (movesOK_publicInputPhase layout publicInput)) fun _ ↦
          MovesOK.seq (MovesOK.of_none (movesOK_verifyFlockBlind _)) fun r ↦ ?_
  obtain ⟨flockPoint, flockS⟩ := r
  refine MovesOK.seq (MovesOK.of_none (movesOK_ringSwitch flockPoint flockS)) fun r ↦ ?_
  obtain ⟨ringTarget, ringWeight⟩ := r
  exact movesOK_verifyStackedOpening _ _ _

end Moves

/-- **The Flock-blind verifier program**: its commitments, and proofs of work of
`Whir.queryGrindingBits = 17` bits. -/
theorem movesOK_blindProgram (bytecode : List K) (publicInput : Digest) :
    MovesOK (· = Whir.queryGrindingBits) True (blindProgram bytecode publicInput) :=
  MovesOK.seq (movesOK_verifyExecutionBlind bytecode publicInput) fun _ ↦ MovesOK.pure _

/-- Every reachable history of the Flock-blind verifier ends with a proof of work of at most
`64` bits. -/
theorem grindBits_le_of_reachable_blind (bytecode : List K) (publicInput : Digest)
    {h : List Ev} (hh : (blindProgram bytecode publicInput).Reachable h) : grindBits h ≤ 64 :=
  ((movesOK_blindProgram bytecode publicInput).mono (fun _ hb ↦ hb ▸ queryGrindingBits_le)
    id).grindBits_le hh

/-! ## The errors -/

/-- The level-0 batching challenge's escape, for at most `231` claims, is at most
`L₀ · 230/|E|`. -/
theorem eBatch_le_blind {μ R : ℕ} (hw : Whir.Admissible μ R) {J : ℕ} (hJ : J ≤ 231) :
    eBatch J (code₀ μ R) ≤ (L₀ : ℝ≥0∞) * ((overE 230 : ℝ≥0) : ℝ≥0∞) := by
  rw [mul_overE, Nat.mul_comm]
  exact eBatch_le J _ hJ (listMax_le hw)

/-- `L₀ · 230/|E|` is at most `2^-128`. -/
theorem mul_overE_230_le : (L₀ : ℝ≥0∞) * ((overE 230 : ℝ≥0) : ℝ≥0∞) ≤ εLean := by
  rw [mul_overE]; exact le_eps_of_nat le_rfl (by norm_num)

/-- **The lead after the table sumcheck**: the public input's challenge, and the lead after it, at
most `L₀ · 230/|E|`, are at most `L₀ · 231/|E|`. -/
theorem pubLeadBlind_le :
    (L₀ : ℝ≥0∞) * ((overE 1 : ℝ≥0) : ℝ≥0∞) + (L₀ : ℝ≥0∞) * ((overE 230 : ℝ≥0) : ℝ≥0∞) ≤
      (L₀ : ℝ≥0∞) * ((overE 231 : ℝ≥0) : ℝ≥0∞) := by
  rw [mul_overE, mul_overE, mul_overE, div_E_add]
  exact ENNReal.div_le_div_right (Nat.cast_le.2 (by omega)) _

/-- **The table sumcheck's error hypotheses**, at a lead of `L₀ · 231/|E|` after it: each is at most
`2^-128`. -/
theorem table_errors_blind (I : M3Instance) (hB : I.B ≤ 2 ^ 20) :
    roundError L₀ 3 + (L₀ : ℝ≥0∞) * ((overE 231 : ℝ≥0) : ℝ≥0∞) ≤ εLean ∧
    (L₀ : ℝ≥0∞) * ((overE 231 : ℝ≥0) : ℝ≥0∞) ≤ εLean ∧
    ∀ n, xiError I L₀ + sumcheckLead n ((L₀ : ℝ≥0∞) * ((overE 231 : ℝ≥0) : ℝ≥0∞)) ≤ εLean := by
  refine ⟨?_, ?_, fun n ↦ ?_⟩
  · rw [roundError_eq, mul_overE, div_E_add]; exact le_eps_of_nat le_rfl (by norm_num)
  · rw [mul_overE]; exact le_eps_of_nat le_rfl (by norm_num)
  · refine le_eps_of_nat (n := L₀ * (I.B + 3 - 1) + L₀ * 231)
      ((add_le_add le_rfl (sumcheckLead_le _ _)).trans (le_of_eq ?_)) ?_
    · rw [xiError_eq, mul_overE, div_E_add]
    · simp only [L₀]; omega

/-! ## The doom the stack's root creates -/

/-- **The commitment's doom, without Flock**, for the value `(layout, ρ)` the announced sizes
gave: `layout` is the verifier's layout at sizes `s`, the history's first commitment is the word
`W₀`, and no candidate of `W₀` satisfies the leanISA relation without Flock at `s`. -/
def CommitDoomBlind (prog : Program) (input : PublicInput) (A : ℕ → ℕ → ℕ)
    (a : Verifier.Layout × ℕ) (h : List Ev) : Prop :=
  ∃ s W₀, a.1 = verifierLayout prog s ∧ firstWord h = some W₀ ∧
    ∀ q ∈ Candidates (leanIsaμ prog s) a.2 (A (leanIsaμ prog s) a.2) W₀,
      ¬ M3HoldsBlind (leanIsaInstance F₀ prog s) input q

/-- **The doom the stack's root creates for V°**: no candidate satisfies the relation without
Flock, and the stack's is the only commitment. -/
def CommitPostBlind (prog : Program) (input : PublicInput) (a : Verifier.Layout × ℕ) (_ : Unit)
    (h : List Ev) : Prop :=
  CommitDoomBlind prog input thrOf a h ∧ StackShape a.1.stackLog a.2 h

/-- **The commitment's doom is the bus phase's**, at the instance without a Flock region. -/
theorem commitDoomBlind_hdoom (prog : Program) (s : Sizes) (input : PublicInput)
    (A : ℕ → ℕ → ℕ) (ρ : ℕ) (h : List Ev)
    (hD : CommitDoomBlind prog input A (verifierLayout prog s, ρ) h) :
    HDoom (candsOf F₀ prog s ρ A) (Seam.commit (leanIsaWith F₀ prog s none)) input h := by
  obtain ⟨s', W, hs, hW, hq⟩ := hD
  obtain rfl := verifierLayout_injective prog hs.symm
  exact ⟨W, hW, by
    rintro _ ⟨q, hq', rfl⟩ hin
    exact hq q hq' ((m3Holds_none_iff F₀ prog _ input q).1 hin)⟩

/-! ## The phases at sizes `s` and rate `ρ` -/

section Phases

variable (prog : Program) (input : PublicInput) (s : Sizes) (ρ : ℕ)

/-- **The doom after the public input**: no candidate of the stack's word satisfies the claims
`cl`, and the stack's is the only commitment. -/
abbrev ClaimsDoom (cl : List Verifier.ColumnClaim) (h : List Ev) : Prop :=
  Doomed (Cs prog s ρ) (ColumnClaimsHold (verifierLayout prog s) cl) h ∧
    StackShape (verifierLayout prog s).stackLog ρ h

/-- The claims' doom is kept by a phase without commitments. -/
theorem claimsDoom_keep {α : Type} {p : Prog α} (hp : MovesOK (fun _ ↦ False) False p)
    (cl : List Verifier.ColumnClaim) {h₀ l : List Ev} (hl : p.Reach h₀ l)
    (hD : ClaimsDoom prog s ρ cl h₀) : ClaimsDoom prog s ρ cl (h₀ ++ l) := by
  refine ⟨fun q hq ↦ ?_, stackShape_keep hp _ _ h₀ l hl hD.2⟩
  rw [cs_stable prog s ρ h₀ l (hp.reach_commits hl)] at hq
  exact hD.1 q hq

variable {prog s ρ}

/-- **Ring switching, then the stacked opening**, from the claims' doom: ring switching keeps it,
as `RingPost` (no candidate satisfies the claims and the ring claim). -/
noncomputable def ringPartBlind (hw : Whir.Admissible (verifierLayout prog s).stackLog ρ)
    (cl : List Verifier.ColumnClaim) (hcl : cl.length ≤ 230) (pt sv : List E) :
    Spec ((ringSwitch pt sv).bind fun y ↦ verifyStackedOpening (verifierLayout prog s).stackLog ρ
        (ringSwitchClaim (verifierLayout prog s) y.1 y.2 ::
          cl.map (·.onStack (verifierLayout prog s))))
      (ClaimsDoom prog s ρ cl) (fun _ _ ↦ False) εLean
      (eBatch (cl.length + 1) (code₀ (verifierLayout prog s).stackLog ρ)) 0 :=
  (Spec.frame (Spec.retInv (Spec.keep (p := ringSwitch pt sv)
      (J := Doomed (Cs prog s ρ) (ColumnClaimsHold (verifierLayout prog s) cl))
      (Post := RingPost (verifierLayout prog s) (Cs prog s ρ) cl)
      ((eBatch_le_blind hw (by omega)).trans mul_overE_230_le) fun h₀ l _ hl _ hD q hq hc ↦ by
        rw [cs_stable prog s ρ h₀ l ((movesOK_ringSwitch pt sv).reach_commits hl)] at hq
        exact hD q hq hc.1)
      _ (ringSwitch_ret_multilinear _ pt sv))
    _ (stackShape_keep (movesOK_ringSwitch pt sv) _ _)).bind' fun y ↦ stackedPart hw cl y

/-- **Flock without its terminal check, ring switching and the stacked opening**, for at most
`230` claims: Flock keeps the claims' doom. -/
noncomputable def flockPartBlind (hw : Whir.Admissible (verifierLayout prog s).stackLog ρ)
    (cl : List Verifier.ColumnClaim) (hcl : cl.length ≤ 230) :
    Spec ((verifyFlockBlind (blake2sR1csLogSize +
          (verifierLayout prog s).tableLogHeights.getD opBlake2s 0)).bind fun x ↦
        (ringSwitch x.1 x.2).bind fun y ↦ verifyStackedOpening (verifierLayout prog s).stackLog ρ
          (ringSwitchClaim (verifierLayout prog s) y.1 y.2 ::
            cl.map (·.onStack (verifierLayout prog s))))
      (ClaimsDoom prog s ρ cl) (fun _ _ ↦ False) εLean
      (eBatch (cl.length + 1) (code₀ (verifierLayout prog s).stackLog ρ)) 0 :=
  (Spec.keep (J := ClaimsDoom prog s ρ cl) (Post := fun _ ↦ ClaimsDoom prog s ρ cl)
      ((eBatch_le_blind hw (by omega)).trans mul_overE_230_le) fun _ _ _ hl _ hD ↦
        claimsDoom_keep prog s ρ (movesOK_verifyFlockBlind _) cl hl hD).bind' fun x ↦
    ringPartBlind hw cl hcl x.1 x.2

open Classical in
/-- **The public input, then Flock, ring switching and the opening**, after at most `227` claims
of the table phase: the public input's phase at the instance without a Flock region, whose
postcondition is the claims' doom. -/
noncomputable def pubPartBlind (hw : Whir.Admissible (verifierLayout prog s).stackLog ρ)
    (cl : List Verifier.ColumnClaim) (hcl : cl.length ≤ 227) :
    Spec ((Verifier.publicInputPhase (verifierLayout prog s) (publicDigest input)).bind fun pc ↦
        (verifyFlockBlind (blake2sR1csLogSize +
          (verifierLayout prog s).tableLogHeights.getD opBlake2s 0)).bind fun x ↦
        (ringSwitch x.1 x.2).bind fun y ↦ verifyStackedOpening (verifierLayout prog s).stackLog ρ
          (ringSwitchClaim (verifierLayout prog s) y.1 y.2 ::
            (cl ++ pc).map (·.onStack (verifierLayout prog s))))
      (fun h ↦ PubPreWith F₀ prog s none (verifierLayout prog s) (Cs prog s ρ) (toI prog s) cl
          input h ∧ StackShape (verifierLayout prog s).stackLog ρ h)
      (fun _ _ ↦ False) εLean ((L₀ : ℝ≥0∞) * ((overE 231 : ℝ≥0) : ℝ≥0∞)) 0 :=
  ((Spec.frame (Spec.retInv (pubPhaseSpecWith F₀ prog s none (verifierLayout prog s) (Cs prog s ρ)
      (toI prog s) cl input (pubLayoutHyp_verifierLayout prog s F₀)
      (EndToEnd.Complete.digestScalars_publicDigest input) (cs_stable prog s ρ)
      (cs_ncard prog s ρ hw) (T := (L₀ : ℝ≥0∞) * ((overE 230 : ℝ≥0) : ℝ≥0∞)))
      (fun pc ↦ pc.length ≤ 3) (retOK_publicInputPhase _ _))
    _ (stackShape_keep (movesOK_publicInputPhase _ _) _ _)).bind' fun pc ↦
    if hpc : pc.length ≤ 3 then
      (flockPartBlind hw (cl ++ pc) (by rw [List.length_append]; omega)).mono
        (fun _ hp ↦ ⟨fun q hq hc ↦ hp.1.1 q hq ⟨hc, aux_none F₀ prog s _⟩, hp.2⟩)
        (fun _ _ h ↦ h) le_rfl (eBatch_le_blind hw (by rw [List.length_append]; omega)) le_rfl
    else Spec.dead.mono (fun _ hp ↦ hpc hp.1.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).mono
    (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl pubLeadBlind_le le_rfl

open Classical in
/-- **Everything after the stack's root**: the bus and the table sumcheck at the instance without a
Flock region, from the root's doom, then the public input, Flock, ring switching and the
opening. -/
noncomputable def restSpecBlind (hw : Whir.Admissible (verifierLayout prog s).stackLog ρ)
    (hlb : LayoutBounds (verifierLayout prog s)) :
    Spec ((verifyBusBalance .computed (verifierLayout prog s)).bind fun bus ↦
        (tablePhase (verifierLayout prog s) bus).bind fun cl ↦
        (Verifier.publicInputPhase (verifierLayout prog s) (publicDigest input)).bind fun pc ↦
        (verifyFlockBlind (blake2sR1csLogSize +
          (verifierLayout prog s).tableLogHeights.getD opBlake2s 0)).bind fun x ↦
        (ringSwitch x.1 x.2).bind fun y ↦ verifyStackedOpening (verifierLayout prog s).stackLog ρ
          (ringSwitchClaim (verifierLayout prog s) y.1 y.2 ::
            (cl ++ pc).map (·.onStack (verifierLayout prog s))))
      (fun h ↦ CommitPostBlind prog input (verifierLayout prog s, ρ) () h)
      (fun _ _ ↦ False) εLean (abError (leanIsaWith F₀ prog s none) L₀ + 0) 0 :=
  have he := phase_errors (leanIsaWith F₀ prog s none) (μBus_le prog s hlb)
    (B_leanIsa_le F₀ prog s)
  have hb := table_errors_blind (leanIsaWith F₀ prog s none) (B_leanIsa_le F₀ prog s)
  Spec.congr (Prog.bind_assoc _ _ _) <|
    ((Spec.frame (Spec.retInv (busTableSpec_leanIsa F₀ prog s (fl := none) input
        (candsOf F₀ prog s ρ thrOf) (fun W ↦ (candsOf_bound hw W).1)
        (fun W ↦ (candsOf_bound hw W).2) he.2.1 he.2.2.1 he.2.2.2.1 he.2.2.2.2.1
        hb.1 hb.2.1 (hb.2.2 _))
        (fun cl ↦ cl.length ≤ 227) (retOK_busTable _))
      _ (stackShape_keep (movesOK_busTable _) _ _)).mono
      (fun h hp ↦ ⟨commitDoomBlind_hdoom prog s input thrOf ρ h hp.1, hp.2⟩) (fun _ _ h ↦ h)
      le_rfl le_rfl le_rfl).bind' fun cl ↦
      if hcl : cl.length ≤ 227 then
        (pubPartBlind input hw cl hcl).mono
          (fun h hp ↦ ⟨tablePost_pubPre F₀ prog s (candsOf F₀ prog s ρ thrOf) input rfl
            (Cs prog s ρ) (candsL_mem F₀ prog s ρ thrOf) cl h hp.1.1, hp.2⟩) (fun _ _ h ↦ h)
          le_rfl le_rfl le_rfl
      else Spec.dead.mono (fun _ hp ↦ hcl hp.1.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- **`verifyExecutionBlind` after the announced sizes**, at good sizes: the stack's root, then
`restSpecBlind`. -/
noncomputable def realSpecBlind (hw : Whir.Admissible (verifierLayout prog s).stackLog ρ)
    (hlb : LayoutBounds (verifierLayout prog s)) :
    Spec (veBodyBlind (publicDigest input) (verifierLayout prog s) ρ) (fun _ ↦ False)
      (fun _ _ ↦ False) εLean 0 0 :=
  (commitSpec (CommitPostBlind prog input (verifierLayout prog s, ρ))
      (verifierLayout prog s).stackLog ρ
      (phase_errors (leanIsaWith F₀ prog s none) (μBus_le prog s hlb)
        (B_leanIsa_le F₀ prog s)).1).bind' fun _ ↦
    restSpecBlind input hw hlb

end Phases

/-! ## The whole program -/

section Whole

variable (prog : Program) (input : PublicInput)

open Classical in
/-- `verifyExecutionBlind` after the announced value `a`: `realSpecBlind` at good sizes, dead
otherwise. -/
noncomputable def bodySpecBlind (a : Verifier.Layout × ℕ) :
    Spec (veBodyBlind (publicDigest input) a.1 a.2) (fun _ ↦ False) (fun _ _ ↦ False) εLean 0 0 :=
  if h : ∃ s, Good prog a s then
    (realSpecBlind (prog := prog) (s := h.choose) (ρ := a.2) input
      (by rw [← h.choose_spec.1]; exact h.choose_spec.2.2.1)
      (by rw [← h.choose_spec.1]; exact h.choose_spec.2.2.2)).congr
      (by rw [h.choose_spec.1])
  else Spec.dead

/-- **The specification of `verifyExecutionBlind`.** -/
noncomputable def veSpecBlind :
    Spec (verifyExecutionBlind (bytecodeWords prog) (publicDigest input)) (fun _ ↦ False)
      (fun _ _ ↦ False) εLean 0 0 :=
  (readSizesSpec (bytecodeWords prog) (fun _ _ ↦ False)).bind' (bodySpecBlind prog input)

/-- **The specification of the Flock-blind verifier program**: from no doom, rejecting where it
returns in doom, every group's escape at most `2^-128` (discounted by its proof of work), lead
`0`. -/
noncomputable def blindSpec :
    Spec (blindProgram (bytecodeWords prog) (publicDigest input)) (fun _ ↦ False)
      (fun b _ ↦ b = false) εLean 0 0 :=
  (veSpecBlind prog input).bind' fun _ ↦
    (Spec.ret (Post := fun b _ ↦ b = false) true).mono (fun _ h ↦ h.elim) (fun _ _ h ↦ h)
      le_rfl le_rfl le_rfl

/-- **The doom certificate of the Flock-blind verifier.** -/
noncomputable def blindCert : Cert (blindProgram (bytecodeWords prog) (publicDigest input)) :=
  (blindSpec prog input).toCert

end Whole

end
end LeanVM.Protocol.EndToEnd.Blind
