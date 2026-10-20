/-
  LeanVM.Guest.Batch.Prog

  The batching as a program of the verifier language: the children's claims and the sumchecks'
  messages are prover scalars, the lambdas and the sumchecks' challenges are samples.
-/

module

public import LeanVM.Guest.Batch.Sound

/-!
# The batching as a verifier program

`Node.batch` runs on the Fiat-Shamir chain of the verifier language: `observe` is a read's
absorb and `squeeze` a sample's, with the same blocks (`blockOf x 1`, `blockOf 0 2`). So the
batching of `n` children is a program `batchProg bytecode n` (`LeanVM.Protocol.Compile.Prog`),
whose prover sends the children's cells (`childCells`), the sumchecks' messages and the three
final values, and whose challenges are the lambdas and the sumchecks' challenges. It checks the
two final claims and that the deferred claim holds of `bytecode`, then accepts.

`runProof_batchProg`: run with BLAKE2s from the chain after the label and the child count, on the
stream of the children's cells, the rounds' messages and the final values, it accepts exactly
where `batch` defers a claim that holds, for children of the bytecode's shapes and rounds of its
sizes. So the random-oracle theorem of this program (`LeanVM.Guest.Batch.Rom`) is the batching's,
with BLAKE2s modelled as the oracle.
-/

namespace LeanVM.Guest.Batch

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Node LeanVM.Guest.B1 LeanVM.Guest.B1.Main

@[expose] public section

/-! ## Children -/

/-- The cells of a child, `2 + (nB + 84) + (nB + 31)` for the bytecode's `nB` coordinates. -/
def childLen (nB : ℕ) : ℕ := 2 + (nB + 84) + (nB + 31)

/-- A child read off its cells (`childCells`), at `nB` bytecode coordinates; `none` where the
public input does not decode. -/
def parseChild (nB : ℕ) (xs : List E) : Option ChildClaims := do
  let pi ← digestOfScalars (xs.getD 0 0, xs.getD 1 0)
  let ys := xs.drop 2
  let zs := ys.drop (nB + 84)
  return ⟨pi,
    ⟨ys.take nB, ys.getD nB 0, ys.getD (nB + 1) 0, ys.getD (nB + 2) 0,
      (ys.drop (nB + 3)).take 8, ((ys.drop (nB + 11)).take 8).reverse,
      (ys.drop (nB + 19)).take 64, ys.getD (nB + 83) 0⟩,
    ⟨zs.take nB, zs.getD nB 0, (zs.drop (nB + 1)).take 28, zs.getD (nB + 29) 0,
      zs.getD (nB + 30) 0⟩⟩

/-- A child has the bytecode's shapes: its proof's claims (`FreshShapedFor`) and its statement's
deferred claim (`DeferredClaim.Shaped`). -/
def ChildShaped (bytecode : List K) (c : ChildClaims) : Prop :=
  FreshShapedFor bytecode c.fresh ∧ c.carried.Shaped bytecode

/-- Read a child's cells. -/
def readChild (nB : ℕ) : Prog ChildClaims := do
  let xs ← Prog.readN (childLen nB)
  liftOption (parseChild nB xs)

/-- Read `n` children. -/
def readChildren (nB : ℕ) : ℕ → Prog (List ChildClaims)
  | 0 => pure []
  | n + 1 => do
    let c ← readChild nB
    let cs ← readChildren nB n
    return c :: cs

/-! ## The lambdas and the rounds -/

/-- Sample a pair of lambdas per child. -/
def sampleLB : ℕ → Prog (List (E × E))
  | 0 => pure []
  | n + 1 => do
    let a ← Prog.sampleE
    let b ← Prog.sampleE
    let l ← sampleLB n
    return (a, b) :: l

/-- Sample a triple of lambdas per child. -/
def sampleLM : ℕ → Prog (List (E × E × E))
  | 0 => pure []
  | n + 1 => do
    let a ← Prog.sampleE
    let b ← Prog.sampleE
    let c ← Prog.sampleE
    let l ← sampleLM n
    return (a, b, c) :: l

/-- `k` rounds of a batching sumcheck from `claim`: read `g(1)` and `g(∞)`, sample the challenge,
fold. The challenges and the final claim. -/
def roundsProg : E → ℕ → Prog (List E × E)
  | claim, 0 => pure ([], claim)
  | claim, k + 1 => do
    let g1 ← Prog.readE
    let gInf ← Prog.readE
    let r ← Prog.sampleE
    let rest ← roundsProg (roundPoly claim (g1, gInf) r) k
    return (r :: rest.1, rest.2)

/-- The bytecode's batched claim at the lambdas `lB`. -/
def claimBOf (cs : List ChildClaims) (lB : List (E × E)) : E :=
  sumE (List.zipWith (fun c l ↦ l.1 * c.fresh.bytecodeValue + l.2 * c.carried.bytecodeValue) cs lB)

/-- The matrices' batched claim at the lambdas `lM`. -/
def claimMOf (cs : List ChildClaims) (lM : List (E × E × E)) : E :=
  sumE (List.zipWith (fun c l ↦ l.1 * c.fresh.matrixValue + l.2.1 * c.carried.matrixA +
    l.2.2 * c.carried.matrixB) cs lM)

/-! ## The program -/

open Classical in
/-- **The batching after its children**: the lambdas and the two sumchecks, the final values, the
two final checks, and the deferred claim true of `bytecode`. -/
noncomputable def batchRest (bytecode : List K) (cs : List ChildClaims) : Prog Bool := do
  let lB ← sampleLB cs.length
  let rb ← roundsProg (claimBOf cs lB) (Nat.log2 bytecode.length)
  let lM ← sampleLM cs.length
  let rm ← roundsProg (claimMOf cs lM) (2 * blake2sR1csLogSize)
  let bv ← Prog.readE
  let mA ← Prog.readE
  let mB ← Prog.readE
  Prog.require (rb.2 = bv * bytecodeWeight cs lB rb.1 ∧
    rm.2 = mA * matrixWeightA cs lM rm.1 + mB * matrixWeightB cs lM rm.1 ∧
    DeferredClaim.Holds bytecode ⟨rb.1, bv, rm.1, mA, mB⟩)
  return true

/-- **The batching of `n` children as a verifier program.** -/
noncomputable def batchProg (bytecode : List K) (n : ℕ) : Prog Bool := do
  let cs ← readChildren (Nat.log2 bytecode.length) n
  batchRest bytecode cs

/-- The prover's stream of a batching: the children's cells, the rounds' messages, the final
values. -/
def batchStream (cs : List ChildClaims) (h : BatchHints) : List E :=
  cs.flatMap childCells ++ h.bytecodeRounds.flatMap (fun g ↦ [g.1, g.2]) ++
    h.matrixRounds.flatMap (fun g ↦ [g.1, g.2]) ++ [h.bytecodeValue, h.matrixA, h.matrixB]

/-- The chain where the batching of `n` children starts: the label's hash, then the child count
absorbed. -/
def batchSeedCv (n : ℕ) : Digest := obsCv (blake2sBytes batchLabel) (ofK (gpow n))

/-! ## The children's cells -/

/-- A child of the bytecode's shapes has `childLen` cells. -/
theorem length_childCells {bytecode : List K} {c : ChildClaims} (hc : ChildShaped bytecode c) :
    (childCells c).length = childLen (Nat.log2 bytecode.length) := by
  obtain ⟨⟨h1, h2, h3, h4⟩, h5, h6⟩ := hc
  simp only [childCells, fixedCells, DeferredClaim.cells, childLen, List.length_append,
    List.length_cons, List.length_nil, List.length_reverse, h1, h2, h3, h4, h5, h6,
    blake2sR1csLogSize]

/-- A child of the bytecode's shapes is read back off its cells. -/
theorem parseChild_childCells {bytecode : List K} {c : ChildClaims} (hc : ChildShaped bytecode c) :
    parseChild (Nat.log2 bytecode.length) (childCells c) = some c := by
  obtain ⟨pi, ⟨bp, bv, al, z, rp, cp, sl, mv⟩, ⟨bp', bv', mp, mA, mB⟩⟩ := c
  obtain ⟨⟨h1, h2, h3, h4⟩, h5, h6⟩ := hc
  simp only [blake2sR1csLogSize] at h1 h2 h3 h4 h5 h6
  generalize Nat.log2 bytecode.length = nB at *
  subst h1
  simp [parseChild, childCells, fixedCells, DeferredClaim.cells, digestOfScalars_digestScalars,
    List.getD_eq_getElem?_getD, List.getElem?_append, List.drop_append, h2, h3, h4, h5, h6,
    List.drop_eq_nil_of_le]

/-! ## The run, piece by piece -/

/-- A run continues where its first program's run ends. -/
theorem runId_bind_of_runsTo {α β : Type} {p : Prog α} {f : α → Prog β} {cv cv' : Digest}
    {xs : List E} {a : α} (hp : RunsTo p cv xs a cv') (rest : List E) (os : List Opening)
    (roots : List (Digest × ℕ × ℕ)) :
    runId (p >>= f) ⟨cv, xs ++ rest, os, roots⟩ = runId (f a) ⟨cv', rest, os, roots⟩ := by
  rw [prog_bind_eq, run_bind, hp]
  rfl

/-- A run continues where its first program's run, reading nothing, ends. -/
theorem runId_bind_of_runsTo_nil {α β : Type} {p : Prog α} {f : α → Prog β} {cv cv' : Digest}
    {a : α} (hp : RunsTo p cv [] a cv') (rest : List E) (os : List Opening)
    (roots : List (Digest × ℕ × ℕ)) :
    runId (p >>= f) ⟨cv, rest, os, roots⟩ = runId (f a) ⟨cv', rest, os, roots⟩ :=
  runId_bind_of_runsTo hp rest os roots

/-- A read absorbs the stream's next scalar. -/
theorem runId_readE_bind {β : Type} (f : E → Prog β) (cv : Digest) (x : E) (rest : List E)
    (os : List Opening) (roots : List (Digest × ℕ × ℕ)) :
    runId (Prog.readE >>= f) ⟨cv, x :: rest, os, roots⟩ =
      runId (f x) ⟨obsCv cv x, rest, os, roots⟩ :=
  runId_bind_of_runsTo (runsTo_readE cv x) rest os roots

/-- A check followed by acceptance. -/
theorem runId_require_true (c : Prop) [Decidable c] (s : St) :
    runId (Prog.require c >>= fun _ ↦ (pure true : Prog Bool)) s =
      if c then some (true, s) else none := by
  unfold Prog.require
  split_ifs <;> rfl

/-- Absorbing two lists is absorbing one, then the other. -/
theorem obsAll_append (cv : Digest) (xs ys : List E) :
    obsAll cv (xs ++ ys) = obsAll (obsAll cv xs) ys := List.foldl_append ..

/-- A shaped child is read off its cells. -/
theorem runsTo_readChild {bytecode : List K} {c : ChildClaims} (hc : ChildShaped bytecode c)
    (cv : Digest) :
    RunsTo (readChild (Nat.log2 bytecode.length)) cv (childCells c) c
      (obsAll cv (childCells c)) := by
  have h := (runsTo_readN cv (childCells c)).bind
    (f := fun xs ↦ liftOption (parseChild (Nat.log2 bytecode.length) xs)) (ys := []) (b := c)
    (cv2 := obsAll cv (childCells c)) (by rw [parseChild_childCells hc]; exact runsTo_ret c _)
  rw [List.append_nil, length_childCells hc] at h
  exact h

/-- Shaped children are read off their cells. -/
theorem runsTo_readChildren {bytecode : List K} :
    ∀ {cs : List ChildClaims}, (∀ c ∈ cs, ChildShaped bytecode c) → ∀ cv : Digest,
      RunsTo (readChildren (Nat.log2 bytecode.length) cs.length) cv (cs.flatMap childCells) cs
        (obsAll cv (cs.flatMap childCells))
  | [], _, cv => runsTo_ret _ cv
  | c :: cs, hs, cv => by
    have h := (runsTo_readChild (hs c List.mem_cons_self) cv).bind
      (f := fun c ↦ do
        let cs ← readChildren (Nat.log2 bytecode.length) cs.length
        return c :: cs)
      ((runsTo_readChildren (fun c' h' ↦ hs c' (List.mem_cons_of_mem c h')) _).bind
        (f := fun cs' ↦ (pure (c :: cs') : Prog (List ChildClaims))) (runsTo_ret _ _))
    rw [List.append_nil, ← obsAll_append, ← List.flatMap_cons] at h
    exact h

/-- The bytecode's lambdas are `sq2`'s. -/
theorem runsTo_sampleLB :
    ∀ (n : ℕ) (cv : Digest), RunsTo (sampleLB n) cv [] (sq2 n cv).1 (sq2 n cv).2
  | 0, cv => runsTo_ret _ cv
  | n + 1, cv =>
    (runsTo_sampleE cv).bind
      (f := fun a ↦ do
        let b ← Prog.sampleE
        let l ← sampleLB n
        return (a, b) :: l)
      ((runsTo_sampleE (sqCv cv)).bind
        (f := fun b ↦ do
          let l ← sampleLB n
          return (challengeOf (sqCv cv), b) :: l)
        ((runsTo_sampleLB n _).bind
          (f := fun l ↦ (pure (_ :: l) : Prog (List (E × E)))) (runsTo_ret _ _)))

/-- The matrices' lambdas are `sq3`'s. -/
theorem runsTo_sampleLM :
    ∀ (n : ℕ) (cv : Digest), RunsTo (sampleLM n) cv [] (sq3 n cv).1 (sq3 n cv).2
  | 0, cv => runsTo_ret _ cv
  | n + 1, cv =>
    (runsTo_sampleE cv).bind
      (f := fun a ↦ do
        let b ← Prog.sampleE
        let c ← Prog.sampleE
        let l ← sampleLM n
        return (a, b, c) :: l)
      ((runsTo_sampleE (sqCv cv)).bind
        (f := fun b ↦ do
          let c ← Prog.sampleE
          let l ← sampleLM n
          return (challengeOf (sqCv cv), b, c) :: l)
        ((runsTo_sampleE (sqCv (sqCv cv))).bind
          (f := fun c ↦ do
            let l ← sampleLM n
            return (challengeOf (sqCv cv), challengeOf (sqCv (sqCv cv)), c) :: l)
          ((runsTo_sampleLM n _).bind
            (f := fun l ↦ (pure (_ :: l) : Prog (List (E × E × E)))) (runsTo_ret _ _))))

/-- The rounds of a batching sumcheck are `bsRun`'s. -/
theorem runsTo_roundsProg : ∀ (rounds : List (E × E)) (claim : E) (cv : Digest) {k : ℕ},
    rounds.length = k →
      RunsTo (roundsProg claim k) cv (rounds.flatMap fun g ↦ [g.1, g.2])
        (bsRun rounds claim cv).1 (bsRun rounds claim cv).2
  | [], claim, cv, _, hk => by subst hk; exact runsTo_ret _ cv
  | (g1, gInf) :: rounds, claim, cv, _, hk => by
    subst hk
    have h := (runsTo_readE cv g1).bind
      (f := fun g1 ↦ do
        let gInf ← Prog.readE
        let r ← Prog.sampleE
        let rest ← roundsProg (roundPoly claim (g1, gInf) r) rounds.length
        return (r :: rest.1, rest.2))
      ((runsTo_readE (obsCv cv g1) gInf).bind
        (f := fun gInf ↦ do
          let r ← Prog.sampleE
          let rest ← roundsProg (roundPoly claim (g1, gInf) r) rounds.length
          return (r :: rest.1, rest.2))
        ((runsTo_sampleE (obsCv (obsCv cv g1) gInf)).bind
          (f := fun r ↦ do
            let rest ← roundsProg (roundPoly claim (g1, gInf) r) rounds.length
            return (r :: rest.1, rest.2))
          ((runsTo_roundsProg rounds _ _ rfl).bind
            (f := fun rest ↦ (pure (_ :: rest.1, rest.2) : Prog (List E × E)))
            (runsTo_ret _ _))))
    exact h.of_eq (by simp) rfl rfl

/-- **The program is the batching**: with BLAKE2s, from the chain after the label and the child
count, on the stream of children of the bytecode's shapes and rounds of its sizes, the program
accepts exactly where `batch` defers a claim that holds of `bytecode`. -/
theorem runProof_batchProg {bytecode : List K} {cs : List ChildClaims} {h : BatchHints}
    (hs : ∀ c ∈ cs, ChildShaped bytecode c)
    (hrb : h.bytecodeRounds.length = Nat.log2 bytecode.length)
    (hrm : h.matrixRounds.length = 2 * blake2sR1csLogSize) :
    Id.run (runProof blake2sBytes (batchProg bytecode cs.length) (batchSeedCv cs.length)
        ⟨batchStream cs h, []⟩) = true ↔
      ∃ d, batch cs h = some d ∧ d.Holds bytecode := by
  have hstream : batchStream cs h = cs.flatMap childCells ++
      (h.bytecodeRounds.flatMap (fun g ↦ [g.1, g.2]) ++
        (h.matrixRounds.flatMap (fun g ↦ [g.1, g.2]) ++
          [h.bytecodeValue, h.matrixA, h.matrixB])) := by
    simp only [batchStream, List.append_assoc]
  show (match runId (batchProg bytecode cs.length)
      ⟨batchSeedCv cs.length, batchStream cs h, [], []⟩ with
      | some (true, s) => s.stream.isEmpty && s.openings.isEmpty
      | _ => false) = true ↔ _
  rw [hstream, batchProg, runId_bind_of_runsTo (cv := batchSeedCv cs.length) (cv' := batchCv cs)
      (runsTo_readChildren hs _),
    batchRest,
    runId_bind_of_runsTo_nil (a := lambdasB cs) (cv' := cvB cs) (runsTo_sampleLB _ _),
    runId_bind_of_runsTo (a := (bsRun h.bytecodeRounds (claimB cs) (cvB cs)).1) (cv' := cvB' cs h)
      (runsTo_roundsProg h.bytecodeRounds (claimBOf cs (lambdasB cs)) (cvB cs) hrb),
    runId_bind_of_runsTo_nil (a := lambdasM cs h) (cv' := cvM cs h) (runsTo_sampleLM _ _),
    runId_bind_of_runsTo (a := (bsRun h.matrixRounds (claimM cs h) (cvM cs h)).1)
      (runsTo_roundsProg h.matrixRounds (claimMOf cs (lambdasM cs h)) (cvM cs h) hrm),
    runId_readE_bind, runId_readE_bind, runId_readE_bind, runId_require_true, batch_eq]
  split_ifs <;> simp_all

end
end LeanVM.Guest.Batch
