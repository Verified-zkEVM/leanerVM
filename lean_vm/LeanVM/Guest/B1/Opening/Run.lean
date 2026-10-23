/-
  LeanVM.Guest.B1.Opening.Run

  The WHIR opening helpers' meanings are the Spec steps they mirror, run on the carried sponge.
-/

module

public import LeanVM.Guest.B1.Opening.Meaning
public import LeanVM.Guest.B1.Sumcheck.Run
public import LeanVM.Guest.B1.Bits.Meaning

/-!
# The opening's steps as Spec runs

* `opening_fold_run`: a fold round of `foldRounds` (V:1750) or `tailRounds` (V:1761): the sample
  with two scalars waiting, the claim folded (`fold_claim`: the guest's `(c2·r + c1)·r + c0` is
  `polyEval [c0, c1, c2] r`), the next quadratic read (`sumcheckRoundPoly 3 _ none`), its two
  words left waiting.
* `opening_ood_point_run`: `sampleN n` from a sponge whose waiting scalars have the rate cells the
  function permutes first.
* `opening_final_message_run`: `readN n`, then `grindP 17` (V:533), its proof of work being
  `grind_check`'s meaning on the first cell (`challengeOf_limb0`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The guest's fold of a quadratic. -/
theorem fold_claim (c0 c1 c2 r : E) : (c2 * r + c1) * r + c0 = polyEval [c0, c1, c2] r := by
  simp only [polyEval, List.foldr, zero_mul, zero_add]

/-- **A fold round**: from the sponge with `w0`, `w1` waiting, the sample `r`, then the next
quadratic's `d0`, `d2` read (absorbed, so waiting): the Spec's steps of `foldRounds`. -/
theorem opening_fold_run (cap : List E) (w0 w1 c0 c1 c2 d0 d2 : E) :
    let s := (⟨cap, [(w0, dsObserve), (w1, dsObserve)]⟩ : Fs)
    RunsTo (do
        let challenge ← Prog.sampleE
        let quad ← sumcheckRoundPoly 3 (polyEval [c0, c1, c2] challenge) none
        return (challenge, quad)) s [d0, d2]
      (s.squeeze.1, [d0, polyEval [c0, c1, c2] s.squeeze.1 + sumE [d2], d2])
      ⟨s.squeeze.2.cap, [(d0, dsObserve), (d2, dsObserve)]⟩ := by
  intro s
  have h := (runsTo_sampleE s).bind (f := fun challenge ↦ do
      let quad ← sumcheckRoundPoly 3 (polyEval [c0, c1, c2] challenge) none
      return (challenge, quad))
    ((runsTo_roundPolyNone s.squeeze.2 (polyEval [c0, c1, c2] s.squeeze.1) d0 [d2] 3 rfl).bind
      (f := fun quad ↦ (pure (s.squeeze.1, quad) : Prog (E × List E))) (runsTo_ret _ _))
  refine h.of_eq rfl (by simp) rfl ?_
  simp [s, Fs.squeeze, Fs.absorbAll, Fs.absorb, rateScalars]

/-- **`opening_ood_point`'s challenges are `sampleN n`** from the sponge carried as
`⟨cap, pend⟩`, the rate cells it permutes first being `rateOf pend`. -/
theorem opening_ood_point_run (cap : List E) (pend : List (E × ℕ)) (n : ℕ) (hn : 1 ≤ n) :
    let S := permOf (rateOf pend ++ cap)
    let rest := (⟨capOf S, []⟩ : Fs).squeezeN (n - 1)
    RunsTo (Prog.sampleN n) ⟨cap, pend⟩ [] (challengeOf S :: rest.1) rest.2 := by
  intro S rest
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact (runsTo_sampleN (k + 1) ⟨cap, pend⟩).of_eq rfl rfl rfl rfl

/-- **`opening_final_message` and `grind_check` are `readN n` then `grindP 17`.** -/
theorem opening_final_message_run (cap : List E) (w0 w1 nonce : E) (ms : List E)
    (hpow : MeaningGrindCheck 17
      [cellsOfState (((⟨cap, [(w0, dsObserve), (w1, dsObserve)]⟩ : Fs).absorbAll ms
        dsObserve).absorb nonce dsPowNonce).perm false 0] []) :
    let s0 := (⟨cap, [(w0, dsObserve), (w1, dsObserve)]⟩ : Fs)
    RunsTo (do
        let m ← Prog.readN ms.length
        Prog.grindP Whir.queryGrindingBits
        return m) s0 (ms ++ [nonce]) ms
      (((s0.absorbAll ms dsObserve).absorb nonce dsPowNonce).squeeze.2) := by
  intro s0
  obtain ⟨-, -, hlow⟩ := hpow
  have hok : powOk Whir.queryGrindingBits nonce
      ((s0.absorbAll ms dsObserve).absorb nonce dsPowNonce).squeeze.1 = true := by
    simp only [powOk, Whir.queryGrindingBits, Fs.squeeze, Keccak.challengeOf_limb0,
      show (17 : ℕ) ≠ 0 by decide, ↓reduceIte]
    exact decide_eq_true hlow
  have h := (runsTo_readN s0 ms).bind (f := fun m ↦ do
      Prog.grindP Whir.queryGrindingBits
      return m)
    ((runsTo_grindP Whir.queryGrindingBits _ nonce hok).bind (f := fun _ ↦ (pure ms : Prog (List E)))
      (runsTo_ret _ _))
  exact h.of_eq rfl (by simp) rfl rfl

end
end LeanVM.Guest.B1
