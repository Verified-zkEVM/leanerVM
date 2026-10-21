/-
  LeanVM.E2E.Complete.Hints

  The honest batching's hints (L11 of `docs/roadmap/t6-completeness.md`): the bytecode sumcheck's
  honest rounds, zero rounds for the matrices with the final values solved for, and the batching
  accepting them, with a deferred claim whose bytecode part is true, when the matrices' two
  weights at the end are not both zero.
-/

module

public import LeanVM.E2E.Batch.With
public import LeanVM.Guest.Batch.Bytecode
public import LeanVM.Guest.Batch.Matrix

/-!
# The honest batching's hints

A node's batching (`batchWith`) absorbs its children's claims, squeezes the lambdas and runs two
sumchecks; the hints give the rounds and the final values. The honest hints
(`honestHints H s0 bytecode cs`), with every hash answered by `H`:

* **the bytecode**: the honest rounds (`honestRounds`) of the cube sum of the bytecode's extension
  times the batched weight (`bytecodePoly`): each round sends the round polynomial's value at `1`
  and its leading coefficient (`lead`), so the round's fold is the cube sum with one more
  coordinate fixed (`roundPoly_lead`), and the final claim is the polynomial at the challenges
  (`run_honestRounds`); the final value is the bytecode's extension there;
* **the matrices**: zero rounds; the matrices' values solve the final check
  `final = A·w_A + B·w_B` (`A := final / w_A` when `w_A ≠ 0`, else `B := final / w_B`).

`batchWith_honestHints`: when the children's bytecode claims are true at points of `log₂` of the
bytecode's length and the matrices' weights at the end are not both zero (`honestWeights`, the
good event of the batching), the batching accepts the honest hints, with a deferred claim whose
bytecode part is true (`DeferredClaim.BytecodeHolds`). The bytecode's sumcheck is complete
deterministically: its first claim is the cube sum (`bytecode_cubeSum`) because the children's
values are true.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Node LeanVM.Guest.Batch LeanVM.Guest.B1.Main LeanVM.E2E

@[expose] public section

variable (H : Bytes → Digest)

/-- Every hash answered by `H`. -/
abbrev someH (x : Bytes) : Option Digest := some (H x)

/-! ## One round -/

open Classical in
/-- **The leading coefficient** of a polynomial of degree at most two (`0` for another function). -/
noncomputable def lead (g : E → E) : E := if h : Quadratic g then h.choose else 0

/-- The leading coefficient of a quadratic. -/
theorem lead_spec {g : E → E} (hg : Quadratic g) :
    ∃ b c : E, ∀ x, g x = lead g * x ^ 2 + b * x + c := by
  unfold lead
  split
  · rename_i h
    exact h.choose_spec
  · exact absurd hg ‹_›

/-- **The honest round**: from the claim `g(0) + g(1)`, the message `(g(1), lead g)` folds to
`g` at the challenge. -/
theorem roundPoly_lead {g : E → E} (hg : Quadratic g) (x : E) :
    roundPoly (g 0 + g 1) (g 1, lead g) x = g x := by
  obtain ⟨b, c, h⟩ := lead_spec hg
  simp only [roundPoly, h]
  linear_combination ((2 * lead g + b + 2 * c) * x + (lead g + b + c)) *
    Whir.Complete.two_eq_zero_E

/-! ## The honest rounds -/

/-- The chain state after a round's message `m` from `cv`: its two scalars absorbed, then the
challenge squeezed. -/
def roundCv (cv : Digest) (m : E × E) : Digest :=
  H (digestBytes (H (digestBytes (H (digestBytes cv ++ blockOf m.1 1)) ++ blockOf m.2 1)) ++
    blockOf 0 2)

/-- **The honest rounds** of the cube sum of `f` over points of `n` coordinates, `k` of them,
from the prefix `pre` of challenges and the chain state `cv`. -/
noncomputable def honestRounds (n : ℕ) (f : List E → E) : ℕ → List E → Digest → List (E × E)
  | 0, _, _ => []
  | k + 1, pre, cv =>
    (cubeSum n f (pre ++ [1]), lead fun x ↦ cubeSum n f (pre ++ [x])) ::
      honestRounds n f k
        (pre ++ [challengeOf (roundCv H cv
          (cubeSum n f (pre ++ [1]), lead fun x ↦ cubeSum n f (pre ++ [x])))])
        (roundCv H cv (cubeSum n f (pre ++ [1]), lead fun x ↦ cubeSum n f (pre ++ [x])))

/-- **The honest rounds close**: from the cube sum over the points extending `pre`, the rounds
end at `f` at `pre` and their challenges. -/
theorem run_honestRounds {n : ℕ} {f : List E → E} (hf : QuadraticIn n f) :
    ∀ (k : ℕ) (pre : List E) (cv : Digest), pre.length + k = n →
      ∃ rs cv', rs.length = k ∧
        (batchRoundsWith (someH H) (cubeSum n f pre) (honestRounds H n f k pre cv)).run cv =
          some ((rs, f (pre ++ rs)), cv')
  | 0, pre, cv, h => by
    refine ⟨[], cv, rfl, ?_⟩
    rw [cubeSum_full (by omega)]
    simp [honestRounds, batchRoundsWith]
  | k + 1, pre, cv, h => by
    have hq := quadratic_cubeSum hf (pre := pre) (by omega)
    have hclaim : cubeSum n f pre = cubeSum n f (pre ++ [0]) + cubeSum n f (pre ++ [1]) :=
      cubeSum_split (by omega)
    set m : E × E := (cubeSum n f (pre ++ [1]), lead fun x ↦ cubeSum n f (pre ++ [x])) with hm
    obtain ⟨rs, cv', hlen, hrun⟩ := run_honestRounds hf k (pre ++ [challengeOf (roundCv H cv m)])
      (roundCv H cv m) (by simp; omega)
    refine ⟨challengeOf (roundCv H cv m) :: rs, cv', by simp [hlen], ?_⟩
    rw [honestRounds, ← hm, batchRoundsWith_run_cons]
    simp only [someH, Option.bind_some]
    have hr : roundPoly (cubeSum n f pre) m (challengeOf (roundCv H cv m)) =
        cubeSum n f (pre ++ [challengeOf (roundCv H cv m)]) := by
      rw [hclaim, hm]
      exact roundPoly_lead (g := fun x ↦ cubeSum n f (pre ++ [x])) hq _
    have hcv : H (digestBytes (H (digestBytes (H (digestBytes cv ++ blockOf m.1 1)) ++
        blockOf m.2 1)) ++ blockOf 0 2) = roundCv H cv m := rfl
    rw [hcv, hr, hrun]
    simp

/-! ## The chain answers everything -/

/-- Absorbing with every hash answered answers. -/
theorem obsAllW_someH : ∀ (cv : Digest) (xs : List E), ∃ d, obsAllW (someH H) cv xs = some d
  | cv, [] => ⟨cv, rfl⟩
  | cv, x :: xs => by
    obtain ⟨d, hd⟩ := obsAllW_someH (H (digestBytes cv ++ blockOf x 1)) xs
    exact ⟨d, by rw [obsAllW_cons]; exact hd⟩

/-- The bytecode's lambdas, with every hash answered. -/
theorem sq2W_someH : ∀ (n : ℕ) (cv : Digest), ∃ l d, sq2W (someH H) n cv = some (l, d) ∧ l.length = n
  | 0, cv => ⟨[], cv, rfl, rfl⟩
  | n + 1, cv => by
    obtain ⟨l, d, hl, hlen⟩ := sq2W_someH n
      (H (digestBytes (H (digestBytes cv ++ blockOf 0 2)) ++ blockOf 0 2))
    refine ⟨(challengeOf (H (digestBytes cv ++ blockOf 0 2)), challengeOf (H (digestBytes
      (H (digestBytes cv ++ blockOf 0 2)) ++ blockOf 0 2))) :: l, d, ?_, by simp [hlen]⟩
    rw [sq2W]
    simp only [someH, bind, Option.bind_some]
    rw [hl]
    rfl

/-- The matrices' lambdas, with every hash answered. -/
theorem sq3W_someH : ∀ (n : ℕ) (cv : Digest), ∃ l d, sq3W (someH H) n cv = some (l, d) ∧ l.length = n
  | 0, cv => ⟨[], cv, rfl, rfl⟩
  | n + 1, cv => by
    obtain ⟨l, d, hl, hlen⟩ := sq3W_someH n (H (digestBytes (H (digestBytes
      (H (digestBytes cv ++ blockOf 0 2)) ++ blockOf 0 2)) ++ blockOf 0 2))
    refine ⟨(challengeOf (H (digestBytes cv ++ blockOf 0 2)), challengeOf (H (digestBytes
      (H (digestBytes cv ++ blockOf 0 2)) ++ blockOf 0 2)), challengeOf (H (digestBytes (H
        (digestBytes (H (digestBytes cv ++ blockOf 0 2)) ++ blockOf 0 2)) ++ blockOf 0 2))) :: l,
      d, ?_, by simp [hlen]⟩
    rw [sq3W]
    simp only [someH, bind, Option.bind_some]
    rw [hl]
    rfl

/-- A batching sumcheck, with every hash answered. -/
theorem batchRoundsWith_someH : ∀ (rounds : List (E × E)) (claim : E) (cv : Digest),
    ∃ rs fin cv', (batchRoundsWith (someH H) claim rounds).run cv = some ((rs, fin), cv')
  | [], claim, cv => ⟨[], claim, cv, rfl⟩
  | (g1, gInf) :: rest, claim, cv => by
    obtain ⟨rs, fin, cv', h⟩ := batchRoundsWith_someH rest
      (roundPoly claim (g1, gInf) (challengeOf (roundCv H cv (g1, gInf)))) (roundCv H cv (g1, gInf))
    refine ⟨challengeOf (roundCv H cv (g1, gInf)) :: rs, fin, cv', ?_⟩
    rw [batchRoundsWith_run_cons]
    simp only [someH, Option.bind_some]
    rw [show H (digestBytes (H (digestBytes (H (digestBytes cv ++ blockOf g1 1)) ++
      blockOf gInf 1)) ++ blockOf 0 2) = roundCv H cv (g1, gInf) from rfl, h]
    rfl

/-! ## The honest hints -/

/-- The bytecode's lambdas and the chain state after them, from `s0`. -/
def bStart (s0 : Digest) (cs : List ChildClaims) : List (E × E) × Digest :=
  (sq2W (someH H) cs.length
    ((obsAllW (someH H) s0 (ofK (gpow cs.length) :: cs.flatMap childCells)).getD s0)).getD ([], s0)

/-- The bytecode's honest rounds. -/
noncomputable def bRounds (s0 : Digest) (bytecode : List K) (cs : List ChildClaims) :
    List (E × E) :=
  honestRounds H (Nat.log2 bytecode.length) (bytecodePoly bytecode cs (bStart H s0 cs).1)
    (Nat.log2 bytecode.length) [] (bStart H s0 cs).2

/-- The bytecode sumcheck's challenges, final claim and chain state. -/
noncomputable def bEnd (s0 : Digest) (bytecode : List K) (cs : List ChildClaims) :
    (List E × E) × Digest :=
  ((batchRoundsWith (someH H) (claimBOf cs (bStart H s0 cs).1) (bRounds H s0 bytecode cs)).run
    (bStart H s0 cs).2).getD (([], 0), s0)

/-- The matrices' rounds: zero. -/
def zeroRounds : List (E × E) := List.replicate (2 * blake2sR1csLogSize) (0, 0)

/-- The matrices' lambdas and the chain state after them. -/
noncomputable def mStart (s0 : Digest) (bytecode : List K) (cs : List ChildClaims) :
    List (E × E × E) × Digest :=
  (sq3W (someH H) cs.length (bEnd H s0 bytecode cs).2).getD ([], s0)

/-- The matrices' sumcheck's challenges, final claim and chain state. -/
noncomputable def mEnd (s0 : Digest) (bytecode : List K) (cs : List ChildClaims) :
    (List E × E) × Digest :=
  ((batchRoundsWith (someH H) (claimMOf cs (mStart H s0 bytecode cs).1) zeroRounds).run
    (mStart H s0 bytecode cs).2).getD (([], 0), s0)

/-- **The matrices' weights at the end of the honest batching**; the batching's good event is
that they are not both zero. -/
noncomputable def honestWeights (s0 : Digest) (bytecode : List K) (cs : List ChildClaims) : E × E :=
  (matrixWeightA cs (mStart H s0 bytecode cs).1 (mEnd H s0 bytecode cs).1.1,
    matrixWeightB cs (mStart H s0 bytecode cs).1 (mEnd H s0 bytecode cs).1.1)

/-- **The honest hints**: the bytecode's honest rounds and its extension at their challenges,
zero rounds for the matrices and their values solving the final check. -/
noncomputable def honestHints (s0 : Digest) (bytecode : List K) (cs : List ChildClaims) :
    BatchHints where
  bytecodeRounds := bRounds H s0 bytecode cs
  matrixRounds := zeroRounds
  bytecodeValue := multilinearEval (bytecode.map ofK) (bEnd H s0 bytecode cs).1.1
  matrixA := if (honestWeights H s0 bytecode cs).1 ≠ 0 then
    (mEnd H s0 bytecode cs).1.2 / (honestWeights H s0 bytecode cs).1 else 0
  matrixB := if (honestWeights H s0 bytecode cs).1 ≠ 0 then 0 else
    if (honestWeights H s0 bytecode cs).2 ≠ 0 then
      (mEnd H s0 bytecode cs).1.2 / (honestWeights H s0 bytecode cs).2 else 0

/-- The honest matrices' values solve the final check when the weights are not both zero. -/
theorem honestHints_matrix {s0 : Digest} {bytecode : List K} {cs : List ChildClaims}
    (hw : (honestWeights H s0 bytecode cs).1 ≠ 0 ∨ (honestWeights H s0 bytecode cs).2 ≠ 0) :
    (mEnd H s0 bytecode cs).1.2 =
      (honestHints H s0 bytecode cs).matrixA * (honestWeights H s0 bytecode cs).1 +
        (honestHints H s0 bytecode cs).matrixB * (honestWeights H s0 bytecode cs).2 := by
  simp only [honestHints]
  by_cases h1 : (honestWeights H s0 bytecode cs).1 = 0
  · have h2 : (honestWeights H s0 bytecode cs).2 ≠ 0 := hw.resolve_left (not_not.mpr h1)
    simp only [h1, ne_eq, not_true_eq_false, ↓reduceIte, zero_mul, h2, not_false_eq_true,
      zero_add]
    field_simp
  · simp only [ne_eq, h1, not_false_eq_true, ↓reduceIte, zero_mul, add_zero]
    field_simp

/-! ## The batching accepts the honest hints -/

/-- With true children's values, the bytecode's batched claim is the true values'
combination. -/
theorem claimBOf_eq_true {bytecode : List K} :
    ∀ (cs : List ChildClaims) (lB : List (E × E)), (∀ c ∈ cs,
      multilinearEval (bytecode.map ofK) c.fresh.bytecodePoint = c.fresh.bytecodeValue ∧
      multilinearEval (bytecode.map ofK) c.carried.bytecodePoint = c.carried.bytecodeValue) →
      claimBOf cs lB = bytecodeTrue bytecode cs lB
  | [], _, _ => by simp [claimBOf, bytecodeTrue]
  | _ :: _, [], _ => by simp [claimBOf, bytecodeTrue]
  | c :: cs, l :: lB, h => by
    have ih := claimBOf_eq_true cs lB fun c' hc' ↦ h c' (List.mem_cons_of_mem _ hc')
    obtain ⟨h1, h2⟩ := h c List.mem_cons_self
    simp only [claimBOf, bytecodeTrue, List.zipWith_cons_cons, Whir.Complete.sumE_eq,
      List.sum_cons] at ih ⊢
    rw [ih, h1, h2]

/-- **L11: the batching accepts the honest hints**: for children whose bytecode claims are true at
points of `log₂` of the bytecode's length, and the matrices' weights at the end not both zero,
the batching from `s0` with every hash answered by `H` defers a claim whose bytecode part is
true. -/
theorem batchWith_honestHints {s0 : Digest} {bytecode : List K} {cs : List ChildClaims}
    (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length)
    (hcs : ∀ c ∈ cs, c.fresh.bytecodePoint.length = Nat.log2 bytecode.length ∧
      c.carried.bytecodePoint.length = Nat.log2 bytecode.length ∧
      multilinearEval (bytecode.map ofK) c.fresh.bytecodePoint = c.fresh.bytecodeValue ∧
      multilinearEval (bytecode.map ofK) c.carried.bytecodePoint = c.carried.bytecodeValue)
    (hw : (honestWeights H s0 bytecode cs).1 ≠ 0 ∨ (honestWeights H s0 bytecode cs).2 ≠ 0) :
    ∃ d, batchWith (someH H) s0 cs (honestHints H s0 bytecode cs) = some (some d) ∧
      d.BytecodeHolds bytecode := by
  obtain ⟨cvA, hA⟩ := obsAllW_someH H s0 (ofK (gpow cs.length) :: cs.flatMap childCells)
  obtain ⟨lB, cv1, hB, hlB⟩ := sq2W_someH H cs.length cvA
  have hbs : bStart H s0 cs = (lB, cv1) := by simp only [bStart, hA, hB, Option.getD_some]
  have hclaim : claimBOf cs lB = cubeSum (Nat.log2 bytecode.length) (bytecodePoly bytecode cs lB) [] := by
    rw [bytecode_cubeSum hb (fun c hc ↦ ⟨(hcs c hc).1, (hcs c hc).2.1⟩)]
    exact claimBOf_eq_true cs lB fun c hc ↦ (hcs c hc).2.2
  have hq := bytecode_quadraticIn hb (fun c hc ↦ ⟨(hcs c hc).1, (hcs c hc).2.1⟩) lB
  obtain ⟨rB, cv2, hrBlen, hrun⟩ := run_honestRounds H hq (Nat.log2 bytecode.length) [] cv1 (by simp)
  simp only [List.nil_append] at hrun
  rw [← hclaim] at hrun
  have hbe : bEnd H s0 bytecode cs = ((rB, bytecodePoly bytecode cs lB rB), cv2) := by
    simp only [bEnd, bRounds, hbs, hrun, Option.getD_some]
  obtain ⟨lM, cv3, hM, hlM⟩ := sq3W_someH H cs.length cv2
  have hms : mStart H s0 bytecode cs = (lM, cv3) := by
    simp only [mStart, hbe, hM, Option.getD_some]
  obtain ⟨rM, fM, cv4, hrunM⟩ := batchRoundsWith_someH H zeroRounds (claimMOf cs lM) cv3
  have hme : mEnd H s0 bytecode cs = ((rM, fM), cv4) := by
    simp only [mEnd, hms, hrunM, Option.getD_some]
  have hrMlen := length_batchRoundsWith (someH H) _ _ _ hrunM
  have hmat := honestHints_matrix H hw
  rw [hme] at hmat
  simp only [honestWeights, hms, hme] at hmat
  have hA' : obsAllW (someH H) (H (digestBytes s0 ++ blockOf (ofK (gpow cs.length)) 1))
      (cs.flatMap childCells) = some cvA := by
    rw [obsAllW_cons] at hA
    exact hA
  have hbr : (honestHints H s0 bytecode cs).bytecodeRounds =
      honestRounds H (Nat.log2 bytecode.length) (bytecodePoly bytecode cs lB)
        (Nat.log2 bytecode.length) [] cv1 := by
    simp only [honestHints, bRounds, hbs]
  have hmr : (honestHints H s0 bytecode cs).matrixRounds = zeroRounds := rfl
  have hbv : (honestHints H s0 bytecode cs).bytecodeValue =
      multilinearEval (bytecode.map ofK) rB := by
    simp only [honestHints, hbe]
  simp only [claimBOf] at hrun
  simp only [claimMOf] at hrunM
  simp only [batchWith, batchWith.go, StateT.run'_eq, StateT.run_bind, observeWith_run,
    forIn_childrenW, forIn_sq2W, forIn_sq3W, someH, Option.map_some, Option.bind_eq_bind,
    Option.bind_some, hA', hB, List.nil_append, hbr, hmr, hrun, hM, hrunM]
  split_ifs with hc
  · refine ⟨_, rfl, ⟨?_, ?_⟩, ?_, ?_⟩
    · exact hrBlen
    · rw [hrMlen]
      simp [zeroRounds]
    · rw [hrBlen]
      exact hb.symm
    · exact hbv.symm
  · exact (hc ⟨by rw [hbv]; rfl, hmat⟩).elim

end
end LeanVM.E2E.Complete
