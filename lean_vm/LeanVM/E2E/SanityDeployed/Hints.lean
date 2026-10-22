/-
  LeanVM.E2E.SanityDeployed.Hints

  The deployed batching's honest hints: the honest rounds of both sumchecks, the bytecode's and
  the matrices' true values at their ends; the batching accepts them with a true deferred claim
  when the children's claims are true. No good event.
-/

module

public import LeanVM.E2E.Complete.Hints
public import LeanVM.E2E.Complete.Assemble

/-!
# The deployed batching's honest hints

T6-det's honest hints (`Complete.honestHints`) leave the matrices' sumcheck at zero rounds and
solve the final check for the matrices' values: V° does not read them. The deployed outer verifier
checks the root's deferred claim in full (`DeferredClaim.Holds`), so the deployed prover runs the
matrices' sumcheck honestly too:

* `honestHintsDep H s0 bytecode cs`: the bytecode's honest rounds and its extension at their
  challenges (as `honestHints`), then the honest rounds (`honestRounds`) of the cube sum of the
  matrices' batched polynomial (`matrixPoly`) and the matrices' extensions (`matrixValues`) at
  their challenges;
* `batchWith_honestHintsDep`: when every child's claims are true (the bytecode's at both points,
  the proof's lincheck value `blake2sBilinear …`, the statement's matrix values) and shaped, the
  batching accepts with a deferred claim that **holds** (`DeferredClaim.Holds`). The matrices'
  first claim is the cube sum (`matrix_cubeSum`), the polynomial quadratic along each coordinate
  (`matrix_quadraticIn`), and the final check is the definition of `matrixPoly`: no event on the
  weights;
* `leafDeferDep`: a leaf's deferred claim, the zero points with the polynomials' true values there
  (`DeferredClaim::leaf` with its values computed), which holds.
-/

namespace LeanVM.E2E.SanityDeployed

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Node LeanVM.Guest.Batch LeanVM.Guest.B1.Main LeanVM.E2E
open LeanVM.E2E.Complete

@[expose] public section

variable (H : Bytes → Digest)

/-! ## The honest hints -/

/-- The matrices' honest rounds. -/
noncomputable def mRoundsDep (s0 : Digest) (bytecode : List K) (cs : List ChildClaims) :
    List (E × E) :=
  honestRounds H (2 * blake2sR1csLogSize) (matrixPoly cs (mStart H s0 bytecode cs).1)
    (2 * blake2sR1csLogSize) [] (mStart H s0 bytecode cs).2

/-- The matrices' honest sumcheck's challenges, final claim and chain state. -/
noncomputable def mEndDep (s0 : Digest) (bytecode : List K) (cs : List ChildClaims) :
    (List E × E) × Digest :=
  ((batchRoundsWith (someH H) (claimMOf cs (mStart H s0 bytecode cs).1)
    (mRoundsDep H s0 bytecode cs)).run (mStart H s0 bytecode cs).2).getD (([], 0), s0)

/-- **The deployed batching's honest hints**: both sumchecks' honest rounds and the polynomials'
true values at their challenges. -/
noncomputable def honestHintsDep (s0 : Digest) (bytecode : List K) (cs : List ChildClaims) :
    BatchHints where
  bytecodeRounds := bRounds H s0 bytecode cs
  matrixRounds := mRoundsDep H s0 bytecode cs
  bytecodeValue := multilinearEval (bytecode.map ofK) (bEnd H s0 bytecode cs).1.1
  matrixA := (matrixValues (mEndDep H s0 bytecode cs).1.1).1
  matrixB := (matrixValues (mEndDep H s0 bytecode cs).1.1).2

/-- **A child's claims are true**, of the bytecode `bytecode` and of Flock's matrices, with the
shapes the batching's identities need. -/
def ChildTrue (bytecode : List K) (c : ChildClaims) : Prop :=
  c.fresh.bytecodePoint.length = Nat.log2 bytecode.length ∧
    c.carried.bytecodePoint.length = Nat.log2 bytecode.length ∧
    multilinearEval (bytecode.map ofK) c.fresh.bytecodePoint = c.fresh.bytecodeValue ∧
    multilinearEval (bytecode.map ofK) c.carried.bytecodePoint = c.carried.bytecodeValue ∧
    MatrixShaped c ∧
    blake2sBilinear c.fresh.alpha (lincheckRowWeights c.fresh.zSkip c.fresh.rowPoint)
      (lincheckColumnWeights c.fresh.columnPoint c.fresh.slices) = c.fresh.matrixValue ∧
    matrixValues c.carried.matrixPoint = (c.carried.matrixA, c.carried.matrixB)

/-- With true children's matrix values, the matrices' batched claim is the true values'
combination. -/
theorem claimMOf_eq_true {bytecode : List K} :
    ∀ (cs : List ChildClaims) (lM : List (E × E × E)), (∀ c ∈ cs, ChildTrue bytecode c) →
      claimMOf cs lM = matrixTrue cs lM
  | [], _, _ => by simp [claimMOf, matrixTrue]
  | _ :: _, [], _ => by simp [claimMOf, matrixTrue]
  | c :: cs, l :: lM, h => by
    have ih := claimMOf_eq_true cs lM fun c' hc' ↦ h c' (List.mem_cons_of_mem _ hc')
    obtain ⟨-, -, -, -, -, h1, h2⟩ := h c List.mem_cons_self
    have hA : c.carried.matrixA = (matrixValues c.carried.matrixPoint).1 := by rw [h2]
    have hB : c.carried.matrixB = (matrixValues c.carried.matrixPoint).2 := by rw [h2]
    simp only [claimMOf, matrixTrue, List.zipWith_cons_cons, Whir.Complete.sumE_eq,
      List.sum_cons] at ih ⊢
    rw [ih, ← h1, hA, hB]

/-- A pair is its two components (stated so that no projection of an unevaluated pair is
reduced). -/
theorem pair_eq_of_dep {α β : Type} {x : α × β} {a : α} {b : β} (ha : a = x.1) (hb : b = x.2) :
    x = (a, b) := by
  subst ha hb
  rfl

/-- **The batching accepts the deployed honest hints with a true deferred claim**: for children
whose claims are true and shaped, the batching from `s0` with every hash answered by `H` defers a
claim that holds of the bytecode. -/
theorem batchWith_honestHintsDep {s0 : Digest} {bytecode : List K} {cs : List ChildClaims}
    (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length)
    (hcs : ∀ c ∈ cs, ChildTrue bytecode c) :
    ∃ d, batchWith (someH H) s0 cs (honestHintsDep H s0 bytecode cs) = some (some d) ∧
      d.Holds bytecode := by
  obtain ⟨cvA, hA⟩ := obsAllW_someH H s0 (ofK (gpow cs.length) :: cs.flatMap childCells)
  obtain ⟨lB, cv1, hB, hlB⟩ := sq2W_someH H cs.length cvA
  have hbs : bStart H s0 cs = (lB, cv1) := by simp only [bStart, hA, hB, Option.getD_some]
  have hclaim : claimBOf cs lB =
      cubeSum (Nat.log2 bytecode.length) (bytecodePoly bytecode cs lB) [] := by
    rw [bytecode_cubeSum hb (fun c hc ↦ ⟨(hcs c hc).1, (hcs c hc).2.1⟩)]
    exact claimBOf_eq_true cs lB fun c hc ↦ ⟨(hcs c hc).2.2.1, (hcs c hc).2.2.2.1⟩
  have hq := bytecode_quadraticIn hb (fun c hc ↦ ⟨(hcs c hc).1, (hcs c hc).2.1⟩) lB
  obtain ⟨rB, cv2, hrBlen, hrun⟩ := run_honestRounds H hq (Nat.log2 bytecode.length) [] cv1
    (by simp)
  simp only [List.nil_append] at hrun
  rw [← hclaim] at hrun
  have hbe : bEnd H s0 bytecode cs = ((rB, bytecodePoly bytecode cs lB rB), cv2) := by
    simp only [bEnd, bRounds, hbs, hrun, Option.getD_some]
  obtain ⟨lM, cv3, hM, hlM⟩ := sq3W_someH H cs.length cv2
  have hms : mStart H s0 bytecode cs = (lM, cv3) := by
    simp only [mStart, hbe, hM, Option.getD_some]
  have hshM : ∀ c ∈ cs, MatrixShaped c := fun c hc ↦ (hcs c hc).2.2.2.2.1
  have hclaimM : claimMOf cs lM = cubeSum (2 * blake2sR1csLogSize) (matrixPoly cs lM) [] := by
    rw [matrix_cubeSum hshM]
    exact claimMOf_eq_true cs lM hcs
  have hqM := matrix_quadraticIn hshM lM
  obtain ⟨rM, cv4, hrMlen, hrunM⟩ := run_honestRounds H hqM (2 * blake2sR1csLogSize) [] cv3
    (by simp)
  simp only [List.nil_append] at hrunM
  rw [← hclaimM] at hrunM
  have hme : mEndDep H s0 bytecode cs = ((rM, matrixPoly cs lM rM), cv4) := by
    simp only [mEndDep, mRoundsDep, hms, hrunM, Option.getD_some]
  have hA' : obsAllW (someH H) (H (digestBytes s0 ++ blockOf (ofK (gpow cs.length)) 1))
      (cs.flatMap childCells) = some cvA := by
    rw [obsAllW_cons] at hA
    exact hA
  have hbr : (honestHintsDep H s0 bytecode cs).bytecodeRounds =
      honestRounds H (Nat.log2 bytecode.length) (bytecodePoly bytecode cs lB)
        (Nat.log2 bytecode.length) [] cv1 := by
    simp only [honestHintsDep, bRounds, hbs]
  have hmr : (honestHintsDep H s0 bytecode cs).matrixRounds =
      honestRounds H (2 * blake2sR1csLogSize) (matrixPoly cs lM) (2 * blake2sR1csLogSize) []
        cv3 := by
    simp only [honestHintsDep, mRoundsDep, hms]
  have hbv : (honestHintsDep H s0 bytecode cs).bytecodeValue =
      multilinearEval (bytecode.map ofK) rB := by
    simp only [honestHintsDep, hbe]
  have hmA : (honestHintsDep H s0 bytecode cs).matrixA = (matrixValues rM).1 := by
    simp only [honestHintsDep, hme]
  have hmB : (honestHintsDep H s0 bytecode cs).matrixB = (matrixValues rM).2 := by
    simp only [honestHintsDep, hme]
  simp only [claimBOf] at hrun
  simp only [claimMOf] at hrunM
  simp only [batchWith, batchWith.go, StateT.run'_eq, StateT.run_bind, observeWith_run,
    forIn_childrenW, forIn_sq2W, forIn_sq3W, someH, Option.map_some, Option.bind_eq_bind,
    Option.bind_some, hA', hB, List.nil_append, hbr, hmr, hrun, hM, hrunM]
  split_ifs with hc
  · refine ⟨_, rfl, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · exact hrBlen
    · exact hrMlen
    · rw [hrBlen]
      exact hb.symm
    · exact hbv.symm
    · dsimp only
      exact pair_eq_of_dep hmA hmB
  · refine (hc ⟨by rw [hbv]; rfl, ?_⟩).elim
    rw [hmA, hmB]
    simp only [matrixPoly, matrixWeightA, matrixWeightB]

/-! ## A leaf's deferred claim -/

/-- **A leaf's deferred claim, deployed**: the zero points, the bytecode's and the matrices' true
values there. -/
def leafDeferDep : DeferredClaim where
  bytecodePoint := List.replicate (Nat.log2 Guest.End.bytecode.length) 0
  bytecodeValue := multilinearEval (Guest.End.bytecode.map ofK)
    (List.replicate (Nat.log2 Guest.End.bytecode.length) 0)
  matrixPoint := List.replicate (2 * blake2sR1csLogSize) 0
  matrixA := (matrixValues (List.replicate (2 * blake2sR1csLogSize) 0)).1
  matrixB := (matrixValues (List.replicate (2 * blake2sR1csLogSize) 0)).2

/-- A leaf's deployed deferred claim holds. -/
theorem leafDeferDep_holds : leafDeferDep.Holds Guest.End.bytecode := by
  refine ⟨⟨?_, ?_⟩, ?_, by simp only [leafDeferDep], by simp only [leafDeferDep]⟩
  · simp only [leafDeferDep, List.length_replicate]
  · simp only [leafDeferDep, List.length_replicate]
  · simp only [leafDeferDep, List.length_replicate]
    exact two_pow_log2_bytecode

/-- A leaf's deployed deferred claim is at the zero points. -/
theorem leafDeferDep_atZero : leafDeferDep.AtZero Guest.End.bytecode :=
  ⟨by simp only [leafDeferDep], by simp only [leafDeferDep]⟩

end
end LeanVM.E2E.SanityDeployed
