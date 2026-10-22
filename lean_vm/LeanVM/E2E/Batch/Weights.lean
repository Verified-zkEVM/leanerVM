/-
  LeanVM.E2E.Batch.Weights

  T6-prob's good event G2 in the random-oracle model: a potential of the log, `weightsPot`, that
  starts at `0`, rises by at most `2^-192 + failBound` per fresh query, and is at least one on a
  log where an inner node's batching ends with both matrix weights zero.
-/

module

public import LeanVM.Guest.Batch.WeightsRom
public import LeanVM.E2E.Batch
public import LeanVM.E2E.Complete.Hints
public import LeanVM.Guest.End
public import LeanVM.Guest.B1.Main.AggSoundM

/-!
# The matrices' weights, in the random-oracle model

`docs/roadmap/t6-prob.md` §1.4 and §4.5 (package P5). The honest prover of a node solves the
batching's final check for the matrices' values (`Complete.honestHints`), which fails only when
both matrix weights at the end vanish (T6-det's good event G2, `HonestTree.WeightsNonzero`).

* `weightsWith L s0 cs rounds`: the two weights at the end of the batching from `s0` of the
  children `cs`, its bytecode rounds `rounds`, its matrix rounds zero (as the honest prover's),
  every hash answered by `L`; `weightsWith_someH`: at a total hash and the honest bytecode rounds
  it is `Complete.honestWeights`.
* `WeightsVanish ℓ cs`: on the log `ℓ`, from the guest's baked start `aggSeedD`, some bytecode
  rounds of the bytecode's size end with both weights zero.
* `weightsPot ℓ`: the potential of the weights' program (`Guest.Batch.weightsCert`), for every
  child count (`batchSeedsAll`), on the log read from the constant start (`startLog`, as
  `batchPot`).
* `weightsPot_nil`, `weightsPot_step` (one fresh query raises it, in expectation, by at most
  `2^-192 + failBound batchSeedsAll (|ℓ| + 2)`, the extra entry the constant start's), and
  `one_le_weightsPot`: a vanishing of at least one and at most `16` children of the bytecode's
  shapes makes it at least one (`final_ineq`).

The escape bound is `1/|E| = 2^-192` per group of challenges: the weight of `A0` is affine in each
challenge and not identically zero (`Guest.Batch.weightsRestSpec`).
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Protocol.Rom
open LeanVM.Node LeanVM.Guest.Batch LeanVM.Guest.B1.Main OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

/- The enumeration of `Digest` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest

/-! ## The weights with an answered hash -/

/-- **The matrices' weights at the end of a batching** from `s0` whose bytecode rounds are
`rounds` and whose matrix rounds are zero, every hash answered by `L`. -/
def weightsWith (L : Bytes → Option Digest) (s0 : Digest) (cs : List ChildClaims)
    (rounds : List (E × E)) : Option (E × E) := do
  let cv ← obsAllW L s0 (ofK (gpow cs.length) :: cs.flatMap childCells)
  let b ← sq2W L cs.length cv
  let rb ← (batchRoundsWith L (claimBOf cs b.1) rounds).run b.2
  let m ← sq3W L cs.length rb.2
  let rm ← (batchRoundsWith L (claimMOf cs m.1) Complete.zeroRounds).run m.2
  pure (matrixWeightA cs m.1 rm.1.1, matrixWeightB cs m.1 rm.1.1)

/-- **An inner node's batching ends, on the log, with both matrix weights zero**: from the
guest's baked start, some bytecode rounds of the bytecode's size. -/
def WeightsVanish (ℓ : Log) (cs : List ChildClaims) : Prop :=
  ∃ rounds : List (E × E), rounds.length = Nat.log2 Guest.End.bytecode.length ∧
    weightsWith (look ℓ) Guest.B1.Main.aggSeedD cs rounds = some (0, 0)

/-- **The honest weights are the answered weights**: at a total hash and the honest bytecode
rounds, `weightsWith` is `Complete.honestWeights`. -/
theorem weightsWith_someH (H : Bytes → Digest) (s0 : Digest) (bytecode : List K)
    (cs : List ChildClaims) :
    weightsWith (Complete.someH H) s0 cs (Complete.bRounds H s0 bytecode cs) =
      some (Complete.honestWeights H s0 bytecode cs) := by
  obtain ⟨cvA, hA⟩ := Complete.obsAllW_someH H s0 (ofK (gpow cs.length) :: cs.flatMap childCells)
  obtain ⟨lB, cv1, hB, -⟩ := Complete.sq2W_someH H cs.length cvA
  have hbs : Complete.bStart H s0 cs = (lB, cv1) := by
    simp only [Complete.bStart, hA, hB, Option.getD_some]
  obtain ⟨rB, fB, cv2, hrB⟩ := Complete.batchRoundsWith_someH H
    (Complete.bRounds H s0 bytecode cs) (claimBOf cs lB) cv1
  have hbe : Complete.bEnd H s0 bytecode cs = ((rB, fB), cv2) := by
    simp only [Complete.bEnd, hbs, hrB, Option.getD_some]
  obtain ⟨lM, cv3, hM, -⟩ := Complete.sq3W_someH H cs.length cv2
  have hms : Complete.mStart H s0 bytecode cs = (lM, cv3) := by
    simp only [Complete.mStart, hbe, hM, Option.getD_some]
  obtain ⟨rM, fM, cv4, hrM⟩ := Complete.batchRoundsWith_someH H Complete.zeroRounds
    (claimMOf cs lM) cv3
  have hme : Complete.mEnd H s0 bytecode cs = ((rM, fM), cv4) := by
    simp only [Complete.mEnd, hms, hrM, Option.getD_some]
  simp only [weightsWith, hA, hB, hrB, hM, hrM, Complete.honestWeights, hms, hme, bind,
    Option.bind_some, pure]

/-! ## The answered weights are an accepted run -/

section Runs

variable (H : Bytes → Option Digest)

/-- The matrices' lambdas are `sq3W`'s. -/
theorem runsW_sampleLM : ∀ (n : ℕ) (cv : Digest) {ls : List (E × E × E)} {cv' : Digest},
    sq3W H n cv = some (ls, cv') → RunsW H (sampleLM n) cv [] ls cv'
  | 0, cv, ls, cv', h => by
    simp only [sq3W, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact runsW_ret H _ _
  | n + 1, cv, ls, cv', h => by
    simp only [sq3W, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨c1, h1, c2, h2, c3, h3, ⟨ls', cv''⟩, h4, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact (runsW_sampleE H h1).bind
      (f := fun a ↦ do
        let b ← Prog.sampleE
        let c ← Prog.sampleE
        let l ← sampleLM n
        return (a, b, c) :: l)
      ((runsW_sampleE H h2).bind
        (f := fun b ↦ do
          let c ← Prog.sampleE
          let l ← sampleLM n
          return (challengeOf c1, b, c) :: l)
        ((runsW_sampleE H h3).bind
          (f := fun c ↦ do
            let l ← sampleLM n
            return (challengeOf c1, challengeOf c2, c) :: l)
          ((runsW_sampleLM n c3 h4).bind
            (f := fun l ↦ (pure (_ :: l) : Prog (List (E × E × E)))) (runsW_ret H _ _))))

end Runs

/-- The prover's stream of the weights' program: the children's cells, the bytecode sumcheck's
messages, the matrices' zero messages. -/
def weightsStream (cs : List ChildClaims) (rounds : List (E × E)) : List E :=
  cs.flatMap childCells ++
    (rounds.flatMap (fun g ↦ [g.1, g.2]) ++ Complete.zeroRounds.flatMap fun g ↦ [g.1, g.2])

/-- **The answered weights, both zero, are an accepted run of the weights' program.** If the
batching with the hash `H` from `s0`, of children of the bytecode's shapes and bytecode rounds of
its size, ends with both weights zero, then the child count's absorb from `s0` is answered, `cv`,
and from `cv` the program `weightsProg` accepts the stream of the cells and the rounds' messages
under every hash `H'` answering the chain's inputs as `H` does. -/
theorem runProof_weightsProg_of_weightsWith {H H' : Bytes → Option Digest}
    (hH : ∀ (c : Digest) (x : E) (t : ℕ),
      H' (digestBytes c ++ blockOf x t) = H (digestBytes c ++ blockOf x t))
    {bytecode : List K} {s0 : Digest} {cs : List ChildClaims} {rounds : List (E × E)}
    (hs : ∀ c ∈ cs, ChildShaped bytecode c) (hr : rounds.length = Nat.log2 bytecode.length)
    (hw : weightsWith H s0 cs rounds = some (0, 0)) :
    ∃ cv, H (digestBytes s0 ++ blockOf (ofK (gpow cs.length)) 1) = some cv ∧
      runProof H' (weightsProg bytecode cs.length) cv ⟨weightsStream cs rounds, []⟩ =
        some true := by
  simp only [weightsWith, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hw
  obtain ⟨cvA, hA, ⟨lB, cv1⟩, hsq, ⟨⟨rB, fB⟩, cv2⟩, hrB, ⟨lM, cv3⟩, hsq3, ⟨⟨rM, fM⟩, cv4⟩,
    hrM, heq⟩ := hw
  simp only [Prod.mk.injEq] at heq
  rw [obsAllW_cons, Option.bind_eq_some_iff] at hA
  obtain ⟨cv, hcv, hA⟩ := hA
  refine ⟨cv, hcv, ?_⟩
  rw [← obsAllW_congr hH] at hA
  rw [← sq2W_congr hH] at hsq
  rw [← batchRoundsWith_congr hH] at hrB
  rw [← sq3W_congr hH] at hsq3
  rw [← batchRoundsWith_congr hH] at hrM
  have r3 := runsW_roundsProg H' _ _ _ hrB
  rw [hr] at r3
  have r5 := runsW_roundsProg H' _ _ _ hrM
  have hz : Complete.zeroRounds.length = 2 * blake2sR1csLogSize := by simp [Complete.zeroRounds]
  rw [hz] at r5
  have hrest : RunsW H' (weightsRest bytecode cs) cvA ([] ++ ((rounds.flatMap fun g ↦ [g.1, g.2]) ++
      ([] ++ ((Complete.zeroRounds.flatMap fun g ↦ [g.1, g.2]) ++ [])))) true cv4 := by
    unfold weightsRest
    exact (runsW_sampleLB H' _ _ hsq).bind (r3.bind ((runsW_sampleLM H' _ _ hsq3).bind
      (r5.bind (runsW_require_true H'
        (c := matrixWeightA cs lM rM = 0 ∧ matrixWeightB cs lM rM = 0) heq cv4))))
  have hrun := (runsW_readChildren H' hs hA).bind (f := fun cs ↦ weightsRest bytecode cs) hrest
  have hst : cs.flatMap childCells ++ ([] ++ ((rounds.flatMap fun g ↦ [g.1, g.2]) ++
      ([] ++ ((Complete.zeroRounds.flatMap fun g ↦ [g.1, g.2]) ++ [])))) =
        weightsStream cs rounds := by
    simp [weightsStream]
  rw [hst] at hrun
  have h0 : run H' (weightsProg bytecode cs.length) ⟨cv, weightsStream cs rounds, [], []⟩ =
      some (some (true, ⟨cv4, [], [], []⟩)) := by
    have := hrun [] [] []
    rwa [List.append_nil] at this
  unfold runProof
  rw [h0]
  rfl

/-! ## The potential -/

/-- **The weights' potential** on the log `ℓ`, from the constant start `s0`: the potential of the
weights' certificate, for every child count, on the log read from `s0`. -/
noncomputable def weightsPotAt (s0 : Digest) (bytecode : List K) (ℓ : Log) : ℝ≥0∞ :=
  pot (weightsCert bytecode).D batchSeedsAll (weightsAny bytecode) (startLog s0 ℓ)

/-- **G2's potential**: the weights' potential from the guest's baked start, at the guest's
bytecode. -/
noncomputable def weightsPot (ℓ : Log) : ℝ≥0∞ :=
  weightsPotAt Guest.B1.Main.aggSeedD Guest.End.bytecode ℓ

/-- The empty log has potential zero: read from `s0`, its one entry starts nothing. -/
theorem weightsPotAt_nil (s0 : Digest) (bytecode : List K) : weightsPotAt s0 bytecode [] = 0 := by
  unfold weightsPotAt
  have hroot : rootAt batchSeedsAll [] batchLabel = none := by
    unfold rootAt
    split
    · rename_i hex
      obtain ⟨x, hx⟩ := hex
      simp [pend, look, logLookup, batchSeedsAll, batchSeeds] at hx
    · rfl
  have hstep : (step batchSeedsAll (weightsAny bytecode) [] Dec.init batchLabel).1 =
      Shape.none := by
    simp only [step, hroot, parse_label]
  have hsum : termSum (weightsCert bytecode).D batchSeedsAll (weightsAny bytecode)
      (startLog s0 []) = 0 := by
    have hk : (decode batchSeedsAll (weightsAny bytecode) (startLog s0 [])).kinds =
        [(Shape.none, s0)] := by
      rw [show startLog s0 [] = [] ++ [(batchLabel, s0)] from rfl, kinds_decode_append,
        decode_nil, hstep]
      rfl
    simp only [termSum, hk, List.map_cons, List.map_nil, term, List.sum_cons, List.sum_nil,
      add_zero]
  simp only [pot, not_fail_startLog_nil, ↓reduceIte, hsum, min_eq_right (zero_le_one' ℝ≥0∞)]

/-- **The empty log has G2's potential zero.** -/
theorem weightsPot_nil : weightsPot [] = 0 := weightsPotAt_nil _ _

/-- `1/|E|` is `2^-192`, whichever enumeration of `E` counts it. -/
theorem invE_eq : invE = (2 : ℝ≥0∞)⁻¹ ^ 192 := by
  have hE : ∀ i : Fintype E, @Fintype.card E i = 2 ^ 192 := fun i ↦ by
    convert card_E
  rw [invE, hE, Nat.cast_pow, Nat.cast_ofNat, ENNReal.inv_pow]

/-- **The potential's step**: one fresh hash query raises the weights' potential, in expectation,
by at most `2^-192 + failBound batchSeedsAll (|ℓ| + 2)`: the certificate's escape bound and the
failure of the new answer in the log read from `s0`, one entry longer. A fresh query at the label
changes nothing. -/
theorem weightsPotAt_step (s0 : Digest) (bytecode : List K) {ℓ : Log} {t : Bytes}
    (ht : look ℓ t = none) :
    (∑ u, weightsPotAt s0 bytecode (ℓ ++ [(t, u)])) / Fintype.card Digest ≤
      weightsPotAt s0 bytecode ℓ +
        ((2 : ℝ≥0∞)⁻¹ ^ 192 + failBound batchSeedsAll (ℓ.length + 2)) := by
  have ht' : t ∉ ℓ.map Prod.fst := (logLookup_eq_none_iff ℓ t).mp ht
  unfold weightsPotAt
  by_cases hl : t = batchLabel
  · subst hl
    simp only [startLog_append_label]
    exact (avg_le_of_le fun _ ↦ le_rfl).trans le_self_add
  · simp only [startLog_append_of_ne s0 ℓ hl]
    refine (step_ineq (weightsCert bytecode) (weightsCert_bound bytecode) (startLog s0 ℓ) t
      (not_mem_startLog ht' hl)).trans (add_le_add le_rfl (add_le_add invE_eq.le ?_))
    simp only [failBound, card_digest, Nat.cast_pow, Nat.cast_ofNat]
    refine ENNReal.div_le_div_right ?_ _
    have hlen := length_startLog_le s0 ℓ
    exact_mod_cast Nat.mul_le_mul_left _ (by omega)

/-- **G2's step**: one fresh hash query raises `weightsPot`, in expectation, by at most
`2^-192 + failBound batchSeedsAll (|ℓ| + 2)`. -/
theorem weightsPot_step {ℓ : Log} {t : Bytes} (ht : look ℓ t = none) :
    (∑ u, weightsPot (ℓ ++ [(t, u)])) / Fintype.card Digest ≤
      weightsPot ℓ + ((2 : ℝ≥0∞)⁻¹ ^ 192 + failBound batchSeedsAll (ℓ.length + 2)) :=
  weightsPotAt_step _ _ ht

/-- **Vanishing weights make the potential at least one**: on a log whose batching from `s0`, of
at least one and fewer than `2^64 - 1` children of the bytecode's shapes, with bytecode rounds of
its size, ends with both weights zero. -/
theorem one_le_weightsPotAt {s0 : Digest} {bytecode : List K} {ℓ : Log} {cs : List ChildClaims}
    {rounds : List (E × E)} (hr : rounds.length = Nat.log2 bytecode.length)
    (hw : weightsWith (look ℓ) s0 cs rounds = some (0, 0)) (hne : cs ≠ [])
    (hs : ∀ c ∈ cs, ChildShaped bytecode c) (hn : cs.length < 2 ^ 64 - 1) :
    1 ≤ weightsPotAt s0 bytecode ℓ := by
  unfold weightsPotAt
  by_cases hf : Fail batchSeedsAll (startLog s0 ℓ)
  · simp only [pot, hf, ↓reduceIte, le_refl]
  obtain ⟨cv, hcv, hrun⟩ := runProof_weightsProg_of_weightsWith (H := look ℓ)
    (H' := look (startLog s0 ℓ)) (look_startLog_chain s0 ℓ) hs hr hw
  let x : Fin (2 ^ 64 - 1) := ⟨cs.length, hn⟩
  have hx : (x : ℕ) < 2 ^ 64 := by have := x.2; omega
  have hv : Rom.verify (look (startLog s0 ℓ)) (batchSeedsAll.seed x)
      (nodeAt (weightsAny bytecode) (batchSeedsAll.root x)) ⟨weightsStream cs rounds, []⟩ =
        some true := by
    have hcv' : look ℓ (digestBytes s0 ++ blockOf (ofK (gpow (x : ℕ))) 1) = some cv := hcv
    rw [show batchSeedsAll.root x = countRoot x from rfl, nodeAt_countRoot_weights bytecode hx]
    simp only [Rom.verify, seed_run_startLog, hcv', bind, Option.bind_some]
    exact hrun
  exact final_ineq (weightsCert bytecode) hf (rootOk_countRoot_weights bytecode hx) hv
    (doomed_of_weightsRun le_rfl hv ⟨cs, rfl, hs, hne, List.prefix_append _ _⟩)

/-- **G2's final inequality**: an inner node's batching whose weights both vanish on the log, of
at least one and at most `16` children of the guest's shapes, makes `weightsPot` at least one. -/
theorem one_le_weightsPot {ℓ : Log} {cs : List ChildClaims} (h : WeightsVanish ℓ cs)
    (hne : cs ≠ []) (hs : ∀ c ∈ cs, ChildShaped Guest.End.bytecode c) (hlen : cs.length ≤ 16) :
    1 ≤ weightsPot ℓ := by
  obtain ⟨rounds, hr, hw⟩ := h
  exact one_le_weightsPotAt hr hw hne hs (by omega)

end
end LeanVM.E2E
