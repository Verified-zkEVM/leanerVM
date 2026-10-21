/-
  LeanVM.E2E.Batch.With

  The batching with an answered hash, from any chain state, as a run of the bytecode part's
  program: a batching that defers a claim whose bytecode part holds is a run the program accepts,
  every hash it makes answered as the batching's.
-/

module

public import LeanVM.E2E.Batch.Prog
public import LeanVM.Protocol.Verifier.DeferredShape

/-!
# The answered batching is an accepted run

`Node.batchWith H s0 cs h` is the batching of `LeanVM/Spec/NodeWith.lean` with the hash `H :
Bytes → Option Digest` (a log's lookup) from the chain state `s0`, a constant given as data
(decision D5). Its transcript is a Fiat-Shamir chain: it absorbs the child count from `s0`, then
the children's cells, squeezes the lambdas, runs the two sumchecks. The compiled run of a
verifier program (`Compile.run H`) is the same chain, absorbing what it reads and squeezing what
it samples.

`run_bytecodeProg_of_batchWith`: if `batchWith H s0 cs h = some (some d)` and `d`'s bytecode part
holds (`DeferredClaim.BytecodeHolds`), for children of the bytecode's shapes, then the count's
absorb from `s0` is answered, `H (s0 ‖ (count, 1)) = some cv`, and the program `bytecodeProg`
runs from `cv` on the stream `bytecodeStream cs h` (the cells, the bytecode sumcheck's messages)
to acceptance under every hash `H'` that answers the chain's inputs as `H` does. The batching
makes every hash the run makes: the program reads no final value, so no hash beyond the
batching's is needed.

`verifyDeferredWith_shaped`: a proof the deferring verifier accepts with every hash answered
claims of the bytecode's shapes, as the deployed `verifyDeferred_shaped`; with it a node's
children (`NodeRelWith`) have the shapes the program reads.

The pieces: `RunsW H p cv xs a cv'` (the program `p` runs from `cv`, reading exactly `xs`, to `a`
and `cv'`, under `H`), closed under `bind` (`run_bind_of_some`); the chain's absorbs and squeezes
(`obsAllW`, `sq2W`, `sq3W`) and `batchWith` unrolled into them (`batchWith_some`).
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Node LeanVM.Guest.Batch LeanVM.Guest.B1.Main

@[expose] public section

section Runs

variable (H : Bytes → Option Digest)

/-! ## Runs under an answered hash -/

/-- The program `p` runs from the chain state `cv` under `H`, reading exactly `xs`, to `a` and
the chain state `cv'`, on any stream continuing `xs`, any openings and any roots. -/
def RunsW {α : Type} (p : Prog α) (cv : Digest) (xs : List E) (a : α) (cv' : Digest) : Prop :=
  ∀ (rest : List E) (os : List Opening) (roots : List (Digest × ℕ × ℕ)),
    run H p ⟨cv, xs ++ rest, os, roots⟩ = some (some (a, ⟨cv', rest, os, roots⟩))

/-- **A run continues where its first program's run ends.** -/
theorem run_bind_of_some {α β : Type} (f : α → Prog β) :
    ∀ (p : Prog α) (s : St) {r : α × St}, run H p s = some (some r) →
      run H (p.bind f) s = run H (f r.1) r.2
  | .ret a, s, r, h => by
    simp only [run, pure, Option.some.injEq] at h
    subst h
    rfl
  | .fail, s, r, h => by simp [run, pure] at h
  | .read k, ⟨cv, stream, os, roots⟩, r, h => by
    cases stream with
    | nil => simp [run, pure] at h
    | cons x xs =>
      simp only [run, bind, Option.bind_eq_some_iff] at h
      obtain ⟨cv', hcv, h⟩ := h
      simp only [Prog.bind, run, bind, hcv, Option.bind_some]
      exact run_bind_of_some f (k x) _ h
  | .sample k, ⟨cv, stream, os, roots⟩, r, h => by
    simp only [run, bind, Option.bind_eq_some_iff] at h
    obtain ⟨cv', hcv, h⟩ := h
    simp only [Prog.bind, run, bind, hcv, Option.bind_some]
    exact run_bind_of_some f (k _) _ h
  | .grind bits k, ⟨cv, stream, os, roots⟩, r, h => by
    cases stream with
    | nil => simp [run, pure] at h
    | cons n xs =>
      simp only [run, bind, Option.bind_eq_some_iff] at h
      obtain ⟨base, hbase, d, hd, cv', hcv, h⟩ := h
      simp only [Prog.bind, run, bind, hbase, hd, hcv, Option.bind_some]
      split at h
      · rename_i hp
        simp only [hp, ↓reduceIte]
        exact run_bind_of_some f k _ h
      · simp [pure] at h
  | .commit height width k, ⟨cv, stream, os, roots⟩, r, h => by
    match stream, h with
    | [], h => simp [run, pure] at h
    | [_], h => simp [run, pure] at h
    | x0 :: x1 :: xs, h =>
      simp only [run, bind, Option.bind_eq_some_iff] at h
      obtain ⟨cv0, hcv0, cv1, hcv1, h⟩ := h
      simp only [Prog.bind, run, bind, hcv0, hcv1, Option.bind_some]
      split at h
      · exact run_bind_of_some f k _ h
      · simp [pure] at h
  | .query i ps k, ⟨cv, stream, os, roots⟩, r, h => by
    simp only [run] at h
    split at h
    · simp [pure] at h
    · rename_i root height width hroot
      simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨o, ho, h⟩ := h
      rcases o with _ | ⟨rows, rest⟩
      · simp [pure] at h
      · simp only [Prog.bind, run, hroot, bind, ho, Option.bind_some]
        exact run_bind_of_some f (k rows) _ h

/-- A return reads nothing. -/
theorem runsW_ret {α : Type} (a : α) (cv : Digest) : RunsW H (pure a : Prog α) cv [] a cv :=
  fun _ _ _ ↦ rfl

/-- Runs compose: the second program runs from where the first ends. -/
theorem RunsW.bind {H : Bytes → Option Digest} {α β : Type} {p : Prog α} {f : α → Prog β}
    {cv cv1 cv2 : Digest}
    {xs ys : List E} {a : α} {b : β} (h1 : RunsW H p cv xs a cv1)
    (h2 : RunsW H (f a) cv1 ys b cv2) : RunsW H (p >>= f) cv (xs ++ ys) b cv2 := by
  intro rest os roots
  show run H (p.bind f) _ = _
  rw [List.append_assoc, run_bind_of_some H f p _ (h1 (ys ++ rest) os roots)]
  exact h2 rest os roots

/-- A run, restated along equalities of its read scalars, value and state. -/
theorem RunsW.of_eq {H : Bytes → Option Digest} {α : Type} {p : Prog α} {cv : Digest}
    {xs xs' : List E} {a a' : α}
    {c c' : Digest} (h : RunsW H p cv xs a c) (hx : xs = xs') (ha : a = a') (hc : c = c') :
    RunsW H p cv xs' a' c' := by
  subst hx ha hc; exact h

/-- A read absorbs the next scalar, its chain step answered. -/
theorem runsW_readE {cv cv' : Digest} {x : E} (h : H (digestBytes cv ++ blockOf x 1) = some cv') :
    RunsW H Prog.readE cv [x] x cv' := by
  intro rest os roots
  simp only [Prog.readE, run, absorbBlock, List.cons_append, List.nil_append, bind, h,
    Option.bind_some]
  rfl

/-- A sample squeezes the chain, its step answered. -/
theorem runsW_sampleE {cv cv' : Digest} (h : H (digestBytes cv ++ blockOf 0 2) = some cv') :
    RunsW H Prog.sampleE cv [] (challengeOf cv') cv' := by
  intro rest os roots
  simp only [Prog.sampleE, run, absorbBlock, bind, h, Option.bind_some]
  rfl

/-! ## The chain under an answered hash -/

/-- Absorb the scalars `xs` from `cv` under `H`. -/
def obsAllW (cv : Digest) (xs : List E) : Option Digest :=
  xs.foldlM (fun cv x ↦ H (digestBytes cv ++ blockOf x 1)) cv

/-- Two squeezes per child under `H`: the lambdas and the state after them. -/
def sq2W : ℕ → Digest → Option (List (E × E) × Digest)
  | 0, cv => some ([], cv)
  | n + 1, cv => do
    let c1 ← H (digestBytes cv ++ blockOf 0 2)
    let c2 ← H (digestBytes c1 ++ blockOf 0 2)
    let r ← sq2W n c2
    pure ((challengeOf c1, challengeOf c2) :: r.1, r.2)

/-- Three squeezes per child under `H`. -/
def sq3W : ℕ → Digest → Option (List (E × E × E) × Digest)
  | 0, cv => some ([], cv)
  | n + 1, cv => do
    let c1 ← H (digestBytes cv ++ blockOf 0 2)
    let c2 ← H (digestBytes c1 ++ blockOf 0 2)
    let c3 ← H (digestBytes c2 ++ blockOf 0 2)
    let r ← sq3W n c3
    pure ((challengeOf c1, challengeOf c2, challengeOf c3) :: r.1, r.2)

/-- Absorbing two lists is absorbing one, then the other. -/
theorem obsAllW_append (cv : Digest) (xs ys : List E) :
    obsAllW H cv (xs ++ ys) = (obsAllW H cv xs).bind fun cv' ↦ obsAllW H cv' ys := by
  simp only [obsAllW, List.foldlM_append]
  rfl

/-- Absorbing a scalar, then the rest. -/
theorem obsAllW_cons (cv : Digest) (x : E) (xs : List E) :
    obsAllW H cv (x :: xs) =
      (H (digestBytes cv ++ blockOf x 1)).bind fun cv' ↦ obsAllW H cv' xs := by
  simp only [obsAllW, List.foldlM_cons]
  rfl

/-- `observeWith`, run: the chain step's answer. -/
theorem observeWith_run (x : E) (cv : Digest) :
    (observeWith H x).run cv = (H (digestBytes cv ++ blockOf x 1)).map fun d ↦ ((), d) := by
  simp [observeWith]
  cases H (digestBytes cv ++ blockOf x 1) <;> rfl

/-- `squeezeWith`, run: the chain step's answer and its challenge. -/
theorem squeezeWith_run (cv : Digest) :
    (squeezeWith H).run cv =
      (H (digestBytes cv ++ blockOf 0 2)).map fun d ↦ (challengeOf d, d) := by
  simp [squeezeWith]
  cases H (digestBytes cv ++ blockOf 0 2) <;> rfl


/-- The bytecode's lambda loop of `batchWith`, run: `sq2W`. -/
theorem forIn_sq2W {α : Type} (l : List α) (acc : List (E × E)) (cv : Digest) :
    (forIn l acc (fun _ acc ↦ do
        let lf ← squeezeWith H
        let lc ← squeezeWith H
        pure (ForInStep.yield (acc ++ [(lf, lc)]))) : ChainWith (m := Option) _).run cv =
      (sq2W H l.length cv).map fun r ↦ (acc ++ r.1, r.2) := by
  induction l generalizing acc cv with
  | nil => simp [sq2W]
  | cons a l ih =>
    simp only [List.forIn_cons, StateT.run_bind, squeezeWith_run, List.length_cons, sq2W]
    rcases h1 : H (digestBytes cv ++ blockOf 0 2) with _ | c1
    · rfl
    · rcases h2 : H (digestBytes c1 ++ blockOf 0 2) with _ | c2
      · simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, h2, Option.map_none,
          Option.bind_none]
      · simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, StateT.run_pure,
          Option.pure_def, h2]
        rw [ih]
        cases sq2W H l.length c2 <;> simp

/-- An absorbing loop of `batchWith`, run: `obsAllW`. -/
theorem forIn_observeW (xs : List E) (cv : Digest) :
    (forIn xs PUnit.unit (fun x _ ↦ do
        observeWith H x
        pure (ForInStep.yield PUnit.unit)) : ChainWith (m := Option) PUnit).run cv =
      (obsAllW H cv xs).map fun d ↦ ((), d) := by
  induction xs generalizing cv with
  | nil => rfl
  | cons x xs ih =>
    rw [obsAllW_cons]
    simp only [List.forIn_cons, StateT.run_bind, observeWith_run]
    rcases h1 : H (digestBytes cv ++ blockOf x 1) with _ | d
    · rfl
    · simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, StateT.run_pure,
        Option.pure_def]
      exact ih d

/-- The matrices' lambda loop of `batchWith`, run: `sq3W`. -/
theorem forIn_sq3W {α : Type} (l : List α) (acc : List (E × E × E)) (cv : Digest) :
    (forIn l acc (fun _ acc ↦ do
        let lf ← squeezeWith H
        let la ← squeezeWith H
        let lb ← squeezeWith H
        pure (ForInStep.yield (acc ++ [(lf, la, lb)]))) : ChainWith (m := Option) _).run cv =
      (sq3W H l.length cv).map fun r ↦ (acc ++ r.1, r.2) := by
  induction l generalizing acc cv with
  | nil => simp [sq3W]
  | cons a l ih =>
    simp only [List.forIn_cons, StateT.run_bind, squeezeWith_run, List.length_cons, sq3W]
    rcases h1 : H (digestBytes cv ++ blockOf 0 2) with _ | c1
    · rfl
    · rcases h2 : H (digestBytes c1 ++ blockOf 0 2) with _ | c2
      · simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, h2, Option.map_none,
          Option.bind_none]
      · rcases h3 : H (digestBytes c2 ++ blockOf 0 2) with _ | c3
        · simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, h2, h3,
            Option.map_none, Option.bind_none]
        · simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, StateT.run_pure,
            Option.pure_def, h2, h3]
          rw [ih]
          cases sq3W H l.length c3 <;> simp

/-- The children's loop of `batchWith`, run: their cells absorbed. -/
theorem forIn_childrenW (cs : List ChildClaims) (cv : Digest) :
    (forIn cs PUnit.unit fun c _ ↦ do
        observeWith H (digestScalars c.publicInput).1
        observeWith H (digestScalars c.publicInput).2
        forIn (fixedCells c.fresh ++ c.carried.cells) PUnit.unit fun x _ ↦ do
          observeWith H x
          pure (ForInStep.yield PUnit.unit)
        pure (ForInStep.yield PUnit.unit) : ChainWith (m := Option) PUnit).run cv =
      (obsAllW H cv (cs.flatMap childCells)).map fun d ↦ ((), d) := by
  induction cs generalizing cv with
  | nil => rfl
  | cons c cs ih =>
    have e : (c :: cs).flatMap childCells = (digestScalars c.publicInput).1 ::
        (digestScalars c.publicInput).2 ::
          ((fixedCells c.fresh ++ c.carried.cells) ++ cs.flatMap childCells) := by
      simp [childCells]
    rw [e]
    simp only [obsAllW_cons, obsAllW_append H _ (fixedCells c.fresh ++ c.carried.cells),
      List.forIn_cons, StateT.run_bind, observeWith_run]
    rcases h1 : H (digestBytes cv ++ blockOf (digestScalars c.publicInput).1 1) with _ | d1
    · rfl
    · rcases h2 : H (digestBytes d1 ++ blockOf (digestScalars c.publicInput).2 1) with _ | d2
      · simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, h2, Option.map_none,
          Option.bind_none]
      · simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, h2, forIn_observeW]
        rcases h3 : obsAllW H d2 (fixedCells c.fresh ++ c.carried.cells) with _ | d3
        · simp
        · simp only [Option.map_some, Option.bind_some, StateT.run_pure, Option.pure_def]
          exact ih d3

/-- **`batchWith`, unrolled**: a batching that defers `d` absorbed the count and the cells from
`s0`, squeezed the bytecode's lambdas, and ran the bytecode's sumcheck to a final claim that its
check accepts, at `d`'s bytecode point and value. -/
theorem batchWith_some {s0 : Digest} {cs : List ChildClaims} {h : BatchHints}
    {d : DeferredClaim} (hbw : batchWith H s0 cs h = some (some d)) :
    ∃ cvA lB cv1 rB fB cv2,
      obsAllW H s0 (ofK (gpow cs.length) :: cs.flatMap childCells) = some cvA ∧
      sq2W H cs.length cvA = some (lB, cv1) ∧
      (batchRoundsWith H (claimBOf cs lB) h.bytecodeRounds).run cv1 = some ((rB, fB), cv2) ∧
      fB = h.bytecodeValue * bytecodeWeight cs lB rB ∧ d.bytecodePoint = rB ∧
      d.bytecodeValue = h.bytecodeValue := by
  simp only [batchWith, batchWith.go, StateT.run'_eq, StateT.run_bind, observeWith_run,
    forIn_childrenW, forIn_sq2W, forIn_sq3W] at hbw
  simp only [Option.map_eq_map, Option.bind_eq_bind, Option.map_eq_some_iff,
    Option.bind_eq_some_iff] at hbw
  obtain ⟨r, ⟨_, ⟨cvc, hcvc, rfl⟩, _, ⟨cvA, hcvA, rfl⟩, _, ⟨⟨lB, cv1⟩, hsq, rfl⟩,
    ⟨⟨rB, fB⟩, cv2⟩, hrB, _, ⟨⟨lM, cv3⟩, hsq3, rfl⟩, ⟨⟨rM, fM⟩, cv4⟩, hrM, hif⟩, hd⟩ := hbw
  simp only [List.nil_append] at hrB hif hrM
  split_ifs at hif with hc
  · simp only [StateT.run_pure, Option.pure_def, Option.some.injEq] at hif
    subst hif
    simp only [Option.some.injEq] at hd
    subst hd
    refine ⟨cvA, lB, cv1, rB, fB, cv2, ?_, hsq, hrB, hc.1, rfl, rfl⟩
    rw [obsAllW_cons, hcvc]
    exact hcvA
  · simp only [StateT.run_pure, Option.pure_def, Option.some.injEq] at hif
    subst hif
    simp at hd

/-- One round of `batchRoundsWith`, run. -/
theorem batchRoundsWith_run_cons (claim : E) (g1 gInf : E) (rest : List (E × E)) (cv : Digest) :
    (batchRoundsWith H claim ((g1, gInf) :: rest)).run cv =
      (H (digestBytes cv ++ blockOf g1 1)).bind fun c1 ↦
        (H (digestBytes c1 ++ blockOf gInf 1)).bind fun c2 ↦
          (H (digestBytes c2 ++ blockOf 0 2)).bind fun c3 ↦
            ((batchRoundsWith H (roundPoly claim (g1, gInf) (challengeOf c3)) rest).run c3).map
              fun r ↦ ((challengeOf c3 :: r.1.1, r.1.2), r.2) := by
  simp only [batchRoundsWith, StateT.run_bind, observeWith_run, squeezeWith_run]
  rcases H (digestBytes cv ++ blockOf g1 1) with _ | c1
  · rfl
  · rcases h2 : H (digestBytes c1 ++ blockOf gInf 1) with _ | c2
    · simp [h2]
    · rcases h3 : H (digestBytes c2 ++ blockOf 0 2) with _ | c3
      · simp [h2, h3]
      · simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, h2, h3]
        simp only [roundPoly]
        rcases (batchRoundsWith H ((gInf * challengeOf c3 + (claim + g1 + g1 + gInf)) *
          challengeOf c3 + (claim + g1)) rest).run c3 with _ | r <;> rfl

/-! ## Hashes that answer the chain's inputs alike -/

section Congr

variable {H} {H' : Bytes → Option Digest}
  (hH : ∀ (c : Digest) (x : E) (t : ℕ),
    H' (digestBytes c ++ blockOf x t) = H (digestBytes c ++ blockOf x t))
include hH

/-- Absorbing under two hashes that answer chain inputs alike. -/
theorem obsAllW_congr : ∀ (cv : Digest) (xs : List E), obsAllW H' cv xs = obsAllW H cv xs
  | _, [] => rfl
  | cv, x :: xs => by
    rw [obsAllW_cons, obsAllW_cons, hH]
    cases H (digestBytes cv ++ blockOf x 1) with
    | none => rfl
    | some d => exact obsAllW_congr d xs

/-- Squeezing pairs under two hashes that answer chain inputs alike. -/
theorem sq2W_congr : ∀ (n : ℕ) (cv : Digest), sq2W H' n cv = sq2W H n cv
  | 0, _ => rfl
  | n + 1, cv => by
    simp only [sq2W, hH, sq2W_congr n]

/-- Squeezing triples under two hashes that answer chain inputs alike. -/
theorem sq3W_congr : ∀ (n : ℕ) (cv : Digest), sq3W H' n cv = sq3W H n cv
  | 0, _ => rfl
  | n + 1, cv => by
    simp only [sq3W, hH, sq3W_congr n]

/-- The sumcheck under two hashes that answer chain inputs alike. -/
theorem batchRoundsWith_congr : ∀ (rounds : List (E × E)) (claim : E) (cv : Digest),
    (batchRoundsWith H' claim rounds).run cv = (batchRoundsWith H claim rounds).run cv
  | [], _, _ => rfl
  | (g1, gInf) :: rest, claim, cv => by
    simp only [batchRoundsWith_run_cons, hH, batchRoundsWith_congr rest]

end Congr

/-- Reading `n` scalars absorbs them. -/
theorem runsW_readN : ∀ (xs : List E) (cv cv' : Digest), obsAllW H cv xs = some cv' →
    RunsW H (Prog.readN xs.length) cv xs xs cv'
  | [], cv, cv', h => by
    simp only [obsAllW, List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact runsW_ret H _ _
  | x :: xs, cv, cv', h => by
    rw [obsAllW_cons, Option.bind_eq_some_iff] at h
    obtain ⟨c1, h1, h⟩ := h
    have := (runsW_readE H h1).bind (f := fun x ↦ do let xs ← Prog.readN xs.length; return x :: xs)
      ((runsW_readN xs c1 cv' h).bind (f := fun xs ↦ (pure (x :: xs) : Prog (List E)))
        (runsW_ret H (x :: xs) _))
    simpa [Prog.readN] using this

/-- A shaped child is read off its cells. -/
theorem runsW_readChild {bytecode : List K} {c : ChildClaims} (hc : ChildShaped bytecode c)
    {cv cv' : Digest} (h : obsAllW H cv (childCells c) = some cv') :
    RunsW H (readChild (Nat.log2 bytecode.length)) cv (childCells c) c cv' := by
  have h' := (runsW_readN H (childCells c) cv cv' h).bind
    (f := fun xs ↦ liftOption (parseChild (Nat.log2 bytecode.length) xs)) (ys := []) (b := c)
    (cv2 := cv') (by rw [parseChild_childCells hc]; exact runsW_ret H c _)
  rw [List.append_nil, length_childCells hc] at h'
  exact h'

/-- Shaped children are read off their cells. -/
theorem runsW_readChildren {bytecode : List K} :
    ∀ {cs : List ChildClaims}, (∀ c ∈ cs, ChildShaped bytecode c) → ∀ {cv cv' : Digest},
      obsAllW H cv (cs.flatMap childCells) = some cv' →
      RunsW H (readChildren (Nat.log2 bytecode.length) cs.length) cv (cs.flatMap childCells) cs cv'
  | [], _, cv, cv', h => by
    simp only [List.flatMap_nil, obsAllW, List.foldlM_nil, Option.pure_def,
      Option.some.injEq] at h
    subst h
    exact runsW_ret H _ _
  | c :: cs, hs, cv, cv', h => by
    rw [List.flatMap_cons, obsAllW_append, Option.bind_eq_some_iff] at h
    obtain ⟨c1, h1, h⟩ := h
    have h' := (runsW_readChild H (hs c List.mem_cons_self) h1).bind
      (f := fun c ↦ do
        let cs ← readChildren (Nat.log2 bytecode.length) cs.length
        return c :: cs)
      ((runsW_readChildren (fun c' h' ↦ hs c' (List.mem_cons_of_mem c h')) h).bind
        (f := fun cs' ↦ (pure (c :: cs') : Prog (List ChildClaims))) (runsW_ret H _ _))
    rw [List.append_nil, ← List.flatMap_cons] at h'
    exact h'

/-- The bytecode's lambdas are `sq2W`'s. -/
theorem runsW_sampleLB : ∀ (n : ℕ) (cv : Digest) {ls : List (E × E)} {cv' : Digest},
    sq2W H n cv = some (ls, cv') → RunsW H (sampleLB n) cv [] ls cv'
  | 0, cv, ls, cv', h => by
    simp only [sq2W, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact runsW_ret H _ _
  | n + 1, cv, ls, cv', h => by
    simp only [sq2W, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨c1, h1, c2, h2, ⟨ls', cv''⟩, h3, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have := (runsW_sampleE H h1).bind
      (f := fun a ↦ do
        let b ← Prog.sampleE
        let l ← sampleLB n
        return (a, b) :: l)
      ((runsW_sampleE H h2).bind
        (f := fun b ↦ do
          let l ← sampleLB n
          return (challengeOf c1, b) :: l)
        ((runsW_sampleLB n c2 h3).bind
          (f := fun l ↦ (pure (_ :: l) : Prog (List (E × E)))) (runsW_ret H _ _)))
    exact this

/-- The program's sumcheck rounds are `batchRoundsWith`'s. -/
theorem runsW_roundsProg : ∀ (rounds : List (E × E)) (claim : E) (cv : Digest)
    {rs : List E} {fin : E} {cv' : Digest},
    (batchRoundsWith H claim rounds).run cv = some ((rs, fin), cv') →
      RunsW H (roundsProg claim rounds.length) cv (rounds.flatMap fun g ↦ [g.1, g.2]) (rs, fin) cv'
  | [], claim, cv, rs, fin, cv', h => by
    simp only [batchRoundsWith, StateT.run_pure, Option.pure_def, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    exact runsW_ret H _ _
  | (g1, gInf) :: rounds, claim, cv, rs, fin, cv', h => by
    simp only [batchRoundsWith_run_cons, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨c1, h1, c2, h2, c3, h3, ⟨⟨rs', fin'⟩, cv''⟩, h4, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
    have h' := (runsW_readE H h1).bind
      (f := fun g1 ↦ do
        let gInf ← Prog.readE
        let r ← Prog.sampleE
        let rest ← roundsProg (roundPoly claim (g1, gInf) r) rounds.length
        return (r :: rest.1, rest.2))
      ((runsW_readE H h2).bind
        (f := fun gInf ↦ do
          let r ← Prog.sampleE
          let rest ← roundsProg (roundPoly claim (g1, gInf) r) rounds.length
          return (r :: rest.1, rest.2))
        ((runsW_sampleE H h3).bind
          (f := fun r ↦ do
            let rest ← roundsProg (roundPoly claim (g1, gInf) r) rounds.length
            return (r :: rest.1, rest.2))
          ((runsW_roundsProg rounds _ _ h4).bind
            (f := fun rest ↦ (pure (_ :: rest.1, rest.2) : Prog (List E × E)))
            (runsW_ret H _ _))))
    exact h'.of_eq (by simp) rfl rfl

/-- The sumcheck's challenges are one per round. -/
theorem length_batchRoundsWith : ∀ (rounds : List (E × E)) (claim : E) (cv : Digest)
    {rs : List E} {fin : E} {cv' : Digest},
    (batchRoundsWith H claim rounds).run cv = some ((rs, fin), cv') → rs.length = rounds.length
  | [], claim, cv, rs, fin, cv', h => by
    simp only [batchRoundsWith, StateT.run_pure, Option.pure_def, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    rfl
  | (g1, gInf) :: rounds, claim, cv, rs, fin, cv', h => by
    simp only [batchRoundsWith_run_cons, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨c1, -, c2, -, c3, -, ⟨⟨rs', fin'⟩, cv''⟩, h4, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
    simp [length_batchRoundsWith rounds _ _ h4]

/-- A true check, then acceptance, reads nothing and accepts. -/
theorem runsW_require_true {c : Prop} [Decidable c] (hc : c) (cv : Digest) :
    RunsW H (Prog.require c >>= fun _ ↦ (pure true : Prog Bool)) cv [] true cv := by
  intro rest os roots
  simp only [Prog.require, hc, ↓reduceIte]
  rfl

/-! ## The shapes of a child's claims, under an answered hash -/

/-- **A successful run returns what the program may return**, for a hash in `Option`
(`Prog.returns_of_run`, in `Id`). -/
theorem returns_of_run_option {α : Type} :
    ∀ (p : Prog α) (s : St) {r : α × St}, run H p s = some (some r) → Prog.Returns p r.1
  | .ret a, s, r, h => by
    simp only [run, pure, Option.some.injEq] at h
    subst h
    exact .ret a
  | .fail, s, r, h => by simp [run, pure] at h
  | .read k, ⟨cv, stream, os, roots⟩, r, h => by
    cases stream with
    | nil => simp [run, pure] at h
    | cons x xs =>
      simp only [run, bind, Option.bind_eq_some_iff] at h
      obtain ⟨cv', -, h⟩ := h
      exact .read x (returns_of_run_option (k x) _ h)
  | .sample k, ⟨cv, stream, os, roots⟩, r, h => by
    simp only [run, bind, Option.bind_eq_some_iff] at h
    obtain ⟨cv', -, h⟩ := h
    exact .sample _ (returns_of_run_option (k _) _ h)
  | .grind bits k, ⟨cv, stream, os, roots⟩, r, h => by
    cases stream with
    | nil => simp [run, pure] at h
    | cons n xs =>
      simp only [run, bind, Option.bind_eq_some_iff] at h
      obtain ⟨base, -, d, -, cv', -, h⟩ := h
      split at h
      · exact .grind bits (returns_of_run_option k _ h)
      · simp [pure] at h
  | .commit height width k, ⟨cv, stream, os, roots⟩, r, h => by
    match stream, h with
    | [], h => simp [run, pure] at h
    | [_], h => simp [run, pure] at h
    | x0 :: x1 :: xs, h =>
      simp only [run, bind, Option.bind_eq_some_iff] at h
      obtain ⟨cv0, -, cv1, -, h⟩ := h
      split at h
      · exact .commit height width (returns_of_run_option k _ h)
      · simp [pure] at h
  | .query i ps k, ⟨cv, stream, os, roots⟩, r, h => by
    simp only [run] at h
    split at h
    · simp [pure] at h
    · simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨o, -, h⟩ := h
      rcases o with _ | ⟨rows, rest⟩
      · simp [pure] at h
      · exact .query i ps rows (returns_of_run_option (k rows) _ h)

/-- An accepted proof's program may return `true`, for a hash in `Option`. -/
theorem returns_of_runProof_option {P : Prog Bool} {seed : Digest} {π : Proof}
    (h : runProof H P seed π = some true) : Prog.Returns P true := by
  simp only [runProof, bind, Option.bind_eq_some_iff] at h
  obtain ⟨o, ho, h⟩ := h
  rcases o with _ | ⟨_ | _, s⟩
  · simp [pure] at h
  · simp [pure] at h
  · exact returns_of_run_option H P _ ho

/-- **A proof the deferring verifier accepts, with every hash answered, claims of the bytecode's
shapes** (`verifyDeferred_shaped`, under an answered hash). -/
theorem verifyDeferredWith_shaped {bytecode : List K} {iv publicInput : Digest}
    {c : FixedClaims} {π : Proof}
    (h : verifyDeferredWith H bytecode iv publicInput c π = some true) :
    FreshShapedFor bytecode c := by
  simp only [verifyDeferredWith, bind, Option.bind_eq_some_iff] at h
  obtain ⟨seed, -, h⟩ := h
  have hP := returns_of_runProof_option H h
  unfold deferredProgram at hP
  obtain ⟨_, hu, -⟩ := Prog.returns_bind hP
  exact verifyExecution_shaped hu

end Runs

/-! ## The answered batching is an accepted run -/

/-- **The answered batching is an accepted run of the bytecode part's program.** If the batching
with the hash `H` from the chain state `s0` defers `d`, whose bytecode part holds, of children of
the bytecode's shapes, then the child count's absorb from `s0` is answered, `cv`, and from `cv`
the program `bytecodeProg` accepts the stream of the children's cells and the bytecode
sumcheck's messages under every hash `H'` answering the chain's inputs as `H` does. -/
theorem runProof_bytecodeProg_of_batchWith {H H' : Bytes → Option Digest}
    (hH : ∀ (c : Digest) (x : E) (t : ℕ),
      H' (digestBytes c ++ blockOf x t) = H (digestBytes c ++ blockOf x t))
    {bytecode : List K} {s0 : Digest} {cs : List ChildClaims} {h : BatchHints}
    {d : DeferredClaim} (hs : ∀ c ∈ cs, ChildShaped bytecode c)
    (hbw : batchWith H s0 cs h = some (some d)) (hd : d.BytecodeHolds bytecode) :
    ∃ cv, H (digestBytes s0 ++ blockOf (ofK (gpow cs.length)) 1) = some cv ∧
      runProof H' (bytecodeProg bytecode cs.length) cv ⟨bytecodeStream cs h, []⟩ = some true := by
  obtain ⟨cvA, lB, cv1, rB, fB, cv2, hA, hsq, hrB, hfB, hdp, hdv⟩ := batchWith_some H hbw
  rw [obsAllW_cons, Option.bind_eq_some_iff] at hA
  obtain ⟨cv, hcv, hA⟩ := hA
  refine ⟨cv, hcv, ?_⟩
  obtain ⟨⟨hlogB, -⟩, -, hval⟩ := hd
  have hlen : h.bytecodeRounds.length = Nat.log2 bytecode.length := by
    rw [← length_batchRoundsWith H _ _ _ hrB, ← hdp, hlogB]
  have hreq : fB = bytecodePoly bytecode cs lB rB := by
    rw [hfB, bytecodePoly, ← hdv, ← hval, hdp]
  rw [← obsAllW_congr hH] at hA
  rw [← sq2W_congr hH] at hsq
  rw [← batchRoundsWith_congr hH] at hrB
  have r3 := runsW_roundsProg H' _ _ _ hrB
  rw [hlen] at r3
  have hrun := (runsW_readChildren H' hs hA).bind (f := fun cs ↦ bytecodeRest bytecode cs)
    ((runsW_sampleLB H' _ _ hsq).bind
      (f := fun lB ↦ do
        let rb ← roundsProg (claimBOf cs lB) (Nat.log2 bytecode.length)
        Prog.require (rb.2 = bytecodePoly bytecode cs lB rb.1)
        return true)
      (r3.bind (f := fun rb ↦ do
          Prog.require (rb.2 = bytecodePoly bytecode cs lB rb.1)
          return true)
        (runsW_require_true H' (c := fB = bytecodePoly bytecode cs lB rB) hreq cv2)))
  have hst : cs.flatMap childCells ++ ([] ++ ((h.bytecodeRounds.flatMap fun g ↦ [g.1, g.2]) ++
      [])) = bytecodeStream cs h := by
    simp [bytecodeStream]
  rw [hst] at hrun
  have h0 : run H' (bytecodeProg bytecode cs.length) ⟨cv, bytecodeStream cs h, [], []⟩ =
      some (some (true, ⟨cv2, [], [], []⟩)) := by
    have := hrun [] [] []
    rwa [List.append_nil] at this
  unfold runProof
  rw [h0]
  rfl

end
end LeanVM.E2E
