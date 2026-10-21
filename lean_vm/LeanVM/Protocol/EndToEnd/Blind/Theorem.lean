/-
  LeanVM.Protocol.EndToEnd.Blind.Theorem

  Knowledge soundness of the Flock-blind verifier V° for one statement: the doom bound, the
  extractor of a stack satisfying the leanISA relation without Flock, and the step from an
  accepted proof without such a stack to doom.
-/

module

public import LeanVM.Protocol.EndToEnd.Blind.Assemble
public import LeanVM.Protocol.EndToEnd.Sound.Theorem

/-!
# Knowledge soundness of V°, one statement

For `P = blindProgram (bytecodeWords prog) (publicDigest input)` and its seed
`leanVmSeed (bytecodeWords prog) (publicDigest input)` (the deployed one):

* `blindCert_bound`: every escape bound of `blindCert`, discounted by the proof of work before
  its group, is at most `2^-128`;
* `extractStackBlind prog input c π`: **the extractor**, `extractStack` with the relation without
  Flock: from the cache `c`, the extracted history of `π` under V°, the sizes and rate it
  announced and the stack's committed word, a candidate at level 0's Johnson threshold satisfying
  `M3HoldsBlind (leanIsaInstance blake2sFlockSpec prog s) input` (a classical choice);
* `doomed_of_not_extractedBlind`: a proof V° accepts while the extractor finds no such candidate
  has a doomed boundary prefix, after the stack's root, where the doom is `CommitDoomBlind`.
-/

namespace LeanVM.Protocol.EndToEnd.Blind

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.EndToEnd.Sound
open LeanVM.Protocol.EndToEnd.Complete (publicDigest)
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Rom
open scoped ENNReal

@[expose] public section

/- The enumeration of `Digest` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest

variable (prog : Program) (input : PublicInput)

/-! ## The doom bound -/

/-- `verifyExecutionBlind` does not return without an event. -/
theorem verifyExecutionBlind_ne_ret (bytecode : List K) (publicInput : Digest) (u : Unit) :
    verifyExecutionBlind bytecode publicInput ≠ .ret u := by
  intro h
  obtain ⟨a, ha, -⟩ := bind_eq_ret_iff h
  exact readSizes_ne_ret bytecode a ha

/-- Doom never holds at the empty history: the announced sizes are not at stake. -/
theorem blindSpec_D_nil : ¬ (blindSpec prog input).D [] [] := by
  intro hD
  have hs : (verifyExecutionBlind (bytecodeWords prog) (publicDigest input)).retSplit [] = none :=
    retSplit_eq_none_of_after rfl (verifyExecutionBlind_ne_ret _ _)
  have h1 : (veSpecBlind prog input).D [] [] := (Spec.bindD_none hs).1 hD
  have hs' : (readSizes (bytecodeWords prog)).retSplit [] = none :=
    retSplit_eq_none_of_after rfl (readSizes_ne_ret _)
  exact (Spec.bindD_none hs').1 h1

/-- **The certificate's bound**: every escape bound of `blindCert`, discounted by the proof of
work before its group, is at most `2^-128`. -/
theorem blindCert_bound (h : List Ev) :
    (2 : ℝ≥0∞)⁻¹ ^ min (grindBits h) 64 * (blindCert prog input).ε h ≤ εLean := by
  by_cases hr : (blindProgram (bytecodeWords prog) (publicDigest input)).Reachable h
  · rw [min_eq_left (grindBits_le_of_reachable_blind _ _ hr)]
    exact Spec.toCert_bound _ (fun hD ↦ absurd hD (blindSpec_D_nil prog input)) h
  · simp only [blindCert, Spec.toCert_ε, hr, false_and, ↓reduceIte, mul_zero, zero_le]

/-! ## The doom after the stack's root -/

/-- The doom of `verifyExecutionBlind` after the announced sizes, at good sizes, right after the
stack's root: the root's postcondition. -/
theorem realSpecBlind_D {s : Sizes} {ρ : ℕ}
    (hw : Whir.Admissible (verifierLayout prog s).stackLog ρ)
    (hlb : LayoutBounds (verifierLayout prog s)) {l₁ : List Ev} {e : Ev}
    (hce : (commitStack (verifierLayout prog s).stackLog ρ).after [e] = some (.ret ()))
    (hpost : CommitPostBlind prog input (verifierLayout prog s, ρ) () (l₁ ++ [e])) :
    (realSpecBlind input hw hlb).D l₁ [e] := by
  refine (Spec.bindD_some (Prog.retSplit_self hce)).2 ⟨fun _ ↦ ?_, ?_⟩
  · obtain ⟨q₀, rest, hc, -⟩ := Whir.Complete.exists_ladder hw
    exact (commitSpec_D _ _ hc l₁ e).2 hpost
  · exact (restSpecBlind input hw hlb).start_D _ hpost

/-- **After the stack's root, the certificate's doom is the root's postcondition**: along a
history where `readSizes` returned a good value `a` and the root was committed by `e`, the
doom holds if no candidate of the root satisfies the relation without Flock and the stack's is
the only commitment. -/
theorem blindSpec_D_commit {l₁ : List Ev} {a : Verifier.Layout × ℕ}
    (hl₁ : (readSizes (bytecodeWords prog)).after l₁ = some (.ret a)) {s : Sizes}
    (hg : Good prog a s) {e : Ev}
    (hce : (commitStack a.1.stackLog a.2).after [e] = some (.ret ()))
    (hpost : CommitPostBlind prog input a () (l₁ ++ [e])) :
    (blindSpec prog input).D [] (l₁ ++ [e]) := by
  obtain ⟨lay, ρ⟩ := a
  have hve : (verifyExecutionBlind (bytecodeWords prog) (publicDigest input)).after (l₁ ++ [e]) =
      some ((verifyBusBalance .computed lay).bind fun bus ↦ (tablePhase lay bus).bind fun cl ↦
        (Verifier.publicInputPhase lay (publicDigest input)).bind fun pc ↦
        (verifyFlockBlind (blake2sR1csLogSize + lay.tableLogHeights.getD opBlake2s 0)).bind
          fun x ↦ (ringSwitch x.1 x.2).bind fun y ↦ verifyStackedOpening lay.stackLog ρ
            (ringSwitchClaim lay y.1 y.2 :: (cl ++ pc).map (·.onStack lay))) := by
    rw [verifyExecutionBlind_eq, Prog.after_bind_append _ hl₁]
    exact Prog.after_bind_append _ hce []
  have hs : (verifyExecutionBlind (bytecodeWords prog) (publicDigest input)).retSplit
      (l₁ ++ [e]) = none := by
    refine retSplit_eq_none_of_after hve fun u h ↦ ?_
    obtain ⟨b, hb, -⟩ := bind_eq_ret_iff h
    exact verifyBusBalance_ne_ret _ _ hb
  refine (Spec.bindD_none hs).2 ?_
  refine (Spec.bindD_after (Prog.retSplit_of_after _ l₁ [e] hl₁) (List.cons_ne_nil _ _)).2 ?_
  have hex : ∃ s, Good prog (lay, ρ) s := ⟨s, hg⟩
  have hlay : lay = verifierLayout prog hex.choose := hex.choose_spec.1
  simp only [bodySpecBlind, hex, ↓reduceDIte, Spec.congr_D]
  refine realSpecBlind_D prog input _ _ (by rw [← hlay]; exact hce) ?_
  rw [← hlay]
  exact hpost

/-! ## The extractor -/

open Classical in
/-- **The extractor of V°.** From the cache `c` and the proof `π`: the extracted history of V°'s
run, the sizes `s` and rate `ρ` it announced, and the stack's committed word `W₀`; a candidate of
`W₀` at level 0's Johnson threshold satisfying `M3HoldsBlind (leanIsaInstance blake2sFlockSpec
prog s) input`, if one exists (a classical choice). -/
noncomputable def extractStackBlind (c : HashSpec.QueryCache) (π : Proof) :
    Option (Σ s : Sizes, Column (leanIsaμ prog s)) :=
  let hist := extractedHistory (fun x ↦ c x) (leanVmSeed (bytecodeWords prog) (publicDigest input))
    (blindProgram (bytecodeWords prog) (publicDigest input)) π
  match announced prog hist, firstWord hist with
  | some (s, ρ), some W =>
    if hq : ∃ q ∈ Candidates (leanIsaμ prog s) ρ (thrOf (leanIsaμ prog s) ρ) W,
        M3HoldsBlind (leanIsaInstance F₀ prog s) input q then
      some ⟨s, hq.choose⟩
    else none
  | _, _ => none

/-- **The extractor of V° succeeds**: it returns admissible sizes and a stack satisfying the
leanISA relation without Flock. -/
def ExtractedBlind (c : HashSpec.QueryCache) (π : Proof) : Prop :=
  ∃ (s : Sizes) (q : Column (leanIsaμ prog s)), extractStackBlind prog input c π = some ⟨s, q⟩ ∧
    s.Admissible prog ∧ M3HoldsBlind (leanIsaInstance F₀ prog s) input q

/-! ## Accepted without extraction is doomed -/

/-- **Accepted by V°, and the extractor fails, is doomed**: the prefix of the extracted history
up to the stack's root is a boundary at which the certificate's doom holds. -/
theorem doomed_of_not_extractedBlind {c : HashSpec.QueryCache} {π : Proof}
    (hv : Rom.verify (fun x ↦ c x) (leanVmSeed (bytecodeWords prog) (publicDigest input))
      (blindProgram (bytecodeWords prog) (publicDigest input)) π = some true)
    (hne : ¬ ExtractedBlind prog input c π) :
    DoomedRun (blindCert prog input) (leanVmSeed (bytecodeWords prog) (publicDigest input)) π
      c := by
  set hist := extractedHistory (fun x ↦ c x) (leanVmSeed (bytecodeWords prog) (publicDigest input))
    (blindProgram (bytecodeWords prog) (publicDigest input)) π with hhist
  obtain ⟨hafter, hws⟩ := after_extractedHistory (fun x ↦ c x) hv
  rw [← hhist] at hafter hws
  -- The run: the announced sizes, the root, the rest.
  obtain ⟨u, m, m', hm, hve, -⟩ := after_bind_ret hafter
  rw [verifyExecutionBlind_eq] at hve
  obtain ⟨a, l₁, r, rfl, hl₁, hbody⟩ := after_bind_ret hve
  obtain ⟨v, r₁, r₂, rfl, hce, -⟩ := after_bind_ret hbody
  obtain ⟨level, rest, W, hc, rfl⟩ := commitStack_after_ret hce
  set e := Ev.commit (levelShape a.1.stackLog level (2 ^ level.fold)).1
    (levelShape a.1.stackLog level (2 ^ level.fold)).2 W with he
  have hpre : l₁ ++ [e] <+: hist := by
    rw [hm]
    exact ⟨r₂ ++ m', by simp⟩
  obtain ⟨s, hg⟩ := good_of_readSizes prog hl₁
  obtain ⟨s', -, -, -, hreads⟩ := readSizes_ret_sizes prog hl₁
  -- The root's shape.
  have hcomm : commits (l₁ ++ [e]) = [((levelShape a.1.stackLog level (2 ^ level.fold)).1,
      (levelShape a.1.stackLog level (2 ^ level.fold)).2, W)] := by
    rw [hreads]; exact commits_reads_commit _ _ _ _
  obtain ⟨q₀, rest', hc', -⟩ := Whir.Complete.exists_ladder hg.2.2.1
  rw [hc] at hc'
  simp only [Option.some.injEq, List.cons.injEq] at hc'
  obtain ⟨rfl, rfl⟩ := hc'
  obtain ⟨-, -, hκ, hR, -⟩ := Whir.Params.deployed_spec_hyps hg.2.2.1 hc
  have hshape : StackShape a.1.stackLog a.2 (l₁ ++ [e]) := by
    have hmem : e ∈ hist := by rw [hm]; simp
    have hWs : WellShaped (2 ^ laneBits) W := by rw [he] at hmem; exact hws _ _ W hmem
    refine ⟨by rw [hcomm]; rfl, W, ?_, hWs⟩
    rw [hcomm]
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq, levelShape, wdOf,
      ↓reduceIte, and_true]
    simp only [code₀, hκ, hR]
  -- The first word.
  have hfw : firstWord (l₁ ++ [e]) = some W := by
    simp [firstWord, hcomm]
  -- No good candidate.
  have hdoom : CommitDoomBlind prog input thrOf a (l₁ ++ [e]) := by
    refine ⟨s, W, hg.1, hfw, fun q hq hM ↦ hne ?_⟩
    have hann : announced prog hist = some (s, a.2) :=
      announced_eq prog ((List.prefix_append l₁ [e]).trans hpre) hl₁ hg.1
    have hfw' : firstWord hist = some W := by
      rw [hm]
      have := firstWord_append hfw (r₂ ++ m')
      simpa [he] using this
    have hq' : ∃ q ∈ Candidates (leanIsaμ prog s) a.2 (thrOf (leanIsaμ prog s) a.2) W,
        M3HoldsBlind (leanIsaInstance F₀ prog s) input q := ⟨q, hq, hM⟩
    refine ⟨s, hq'.choose, ?_, hg.2.1, hq'.choose_spec.2⟩
    simp only [extractStackBlind, ← hhist, hann, hfw', hq', ↓reduceDIte]
  exact ⟨l₁ ++ [e], hpre, by simp [Boundary, he], (blindSpec_D_commit prog input hl₁ hg
    (by cases v; exact hce) ⟨hdoom, hshape⟩)⟩

end
end LeanVM.Protocol.EndToEnd.Blind
