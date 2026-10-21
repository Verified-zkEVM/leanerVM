/-
  LeanVM.Guest.B1.Main.HashH

  The batching's Fiat-Shamir chain with the hash a parameter: absorbs, squeezes and the batching
  run over a total hash `Ht`, and their agreement with a partial hash answering them.
-/

module

public import LeanVM.Guest.B1.Main.AggComplete
public import LeanVM.Guest.B1.Main.BatchSpecM

/-!
# The batching's chain over any hash

`BatchSpec.lean`, `AggSound.lean` and `AggComplete.lean` run the batching on BLAKE2s (`obsCv`,
`sqCv`, `sq2`, `sqIt2`, `Node.batch`). Their completeness over a completeness model computes the
same values over a total hash `Ht`: `obsCvH Ht`, `sqCvH Ht`, `obsAllH Ht`, `sq2H Ht`, `sq3H Ht`,
`sqIt2H Ht`, `sqIt3H Ht`, and the batching from the chain state `s0`,
`batchWith (m := Id) Ht s0` (`batchWithH_spec`, `batch_spec` over `Ht`). At `blake2sBytes` they
are the deployed ones (`obsCvH_blake`, …).

**Answered** (`Ans`): a run over a partial hash `H` agreeing with `Ht` where it answers
(`∀ x d, H x = some d → d = Ht x`) that returns a value returns the run's value over `Ht`. The
batching over `H` from `s0` (`batchWith (m := Option) H s0`) closing on a claim gives the claim
over `Ht` (`batchWith_ans`), and every absorb and squeeze of its chain answered by `H` at the
values over `Ht` (`batchWith_ansSteps`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node

@[expose] public section

/-! ## The chain over a total hash -/

section Total

variable (Ht : List UInt8 → Digest)

/-- The chain after absorbing a word, over `Ht` (`obsCv`). -/
def obsCvH (cv : Digest) (x : E) : Digest := Ht (digestBytes cv ++ blockOf x 1)

/-- The chain after a squeeze, over `Ht` (`sqCv`). -/
def sqCvH (cv : Digest) : Digest := Ht (digestBytes cv ++ blockOf 0 2)

/-- The chain after absorbing `xs`, over `Ht` (`obsAll`). -/
def obsAllH (cv : Digest) (xs : List E) : Digest := xs.foldl (obsCvH Ht) cv

/-- Two squeezes per child, over `Ht` (`sq2`). -/
def sq2H : ℕ → Digest → List (E × E) × Digest
  | 0, cv => ([], cv)
  | n + 1, cv => ((challengeOf (sqCvH Ht cv), challengeOf (sqCvH Ht (sqCvH Ht cv))) ::
      (sq2H n (sqCvH Ht (sqCvH Ht cv))).1, (sq2H n (sqCvH Ht (sqCvH Ht cv))).2)

/-- Three squeezes per child, over `Ht` (`sq3`). -/
def sq3H : ℕ → Digest → List (E × E × E) × Digest
  | 0, cv => ([], cv)
  | n + 1, cv => ((challengeOf (sqCvH Ht cv), challengeOf (sqCvH Ht (sqCvH Ht cv)),
      challengeOf (sqCvH Ht (sqCvH Ht (sqCvH Ht cv)))) ::
      (sq3H n (sqCvH Ht (sqCvH Ht (sqCvH Ht cv)))).1,
      (sq3H n (sqCvH Ht (sqCvH Ht (sqCvH Ht cv)))).2)

/-- The state after `c` children's double squeeze, over `Ht` (`sqIt2`). -/
def sqIt2H (cv : Digest) (c : ℕ) : Digest := (fun d => sqCvH Ht (sqCvH Ht d))^[c] cv

/-- The state after `c` children's triple squeeze, over `Ht` (`sqIt3`). -/
def sqIt3H (cv : Digest) (c : ℕ) : Digest := (fun d => sqCvH Ht (sqCvH Ht (sqCvH Ht d)))^[c] cv

theorem obsAllH_take_succ (cv : Digest) (xs : List E) (k : ℕ) (hk : k < xs.length) :
    obsAllH Ht cv (xs.take (k + 1)) = obsCvH Ht (obsAllH Ht cv (xs.take k)) (xs.getD k 0) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, List.getD_eq_getElem _ _ hk, obsAllH,
    obsAllH, Option.toList_some, List.foldl_append]
  rfl

theorem obsAllH_append (cv : Digest) (xs ys : List E) :
    obsAllH Ht cv (xs ++ ys) = obsAllH Ht (obsAllH Ht cv xs) ys := by
  simp [obsAllH, List.foldl_append]

theorem obsAllH_cons (cv : Digest) (x : E) (xs : List E) :
    obsAllH Ht cv (x :: xs) = obsAllH Ht (obsCvH Ht cv x) xs := rfl

theorem sq2H_spec : ∀ (n : ℕ) (cv : Digest), (sq2H Ht n cv).2 = sqIt2H Ht cv n ∧
    (sq2H Ht n cv).1.length = n ∧
    ∀ c (h : c < (sq2H Ht n cv).1.length), (sq2H Ht n cv).1[c] =
      (challengeOf (sqCvH Ht (sqIt2H Ht cv c)), challengeOf (sqCvH Ht (sqCvH Ht (sqIt2H Ht cv c))))
  | 0, cv => ⟨rfl, rfl, fun c h => absurd h (by simp [sq2H])⟩
  | n + 1, cv => by
    obtain ⟨h1, h2, h3⟩ := sq2H_spec n (sqCvH Ht (sqCvH Ht cv))
    refine ⟨by rw [sq2H, h1]; rfl, by simp [sq2H, h2], fun c hc => ?_⟩
    cases c with
    | zero => rfl
    | succ c =>
      simp only [sq2H, List.getElem_cons_succ]
      rw [h3 c (by simpa [sq2H] using hc)]
      rfl

theorem sq3H_spec : ∀ (n : ℕ) (cv : Digest), (sq3H Ht n cv).2 = sqIt3H Ht cv n ∧
    (sq3H Ht n cv).1.length = n ∧
    ∀ c (h : c < (sq3H Ht n cv).1.length), (sq3H Ht n cv).1[c] =
      (challengeOf (sqCvH Ht (sqIt3H Ht cv c)), challengeOf (sqCvH Ht (sqCvH Ht (sqIt3H Ht cv c))),
        challengeOf (sqCvH Ht (sqCvH Ht (sqCvH Ht (sqIt3H Ht cv c)))))
  | 0, cv => ⟨rfl, rfl, fun c h => absurd h (by simp [sq3H])⟩
  | n + 1, cv => by
    obtain ⟨h1, h2, h3⟩ := sq3H_spec n (sqCvH Ht (sqCvH Ht (sqCvH Ht cv)))
    refine ⟨by rw [sq3H, h1]; rfl, by simp [sq3H, h2], fun c hc => ?_⟩
    cases c with
    | zero => rfl
    | succ c =>
      simp only [sq3H, List.getElem_cons_succ]
      rw [h3 c (by simpa [sq3H] using hc)]
      rfl

theorem sqIt2H_succ (cv : Digest) (c : ℕ) :
    sqIt2H Ht cv (c + 1) = sqCvH Ht (sqCvH Ht (sqIt2H Ht cv c)) :=
  Function.iterate_succ_apply' _ _ _

theorem sqIt3H_succ (cv : Digest) (c : ℕ) :
    sqIt3H Ht cv (c + 1) = sqCvH Ht (sqCvH Ht (sqCvH Ht (sqIt3H Ht cv c))) :=
  Function.iterate_succ_apply' _ _ _

/-! ## The batching over `Ht` -/

theorem observeWithH_run (x : E) (cv : Digest) :
    (observeWith (m := Id) Ht x).run cv = ((), obsCvH Ht cv x) := rfl

theorem squeezeWithH_run (cv : Digest) :
    (squeezeWith (m := Id) Ht).run cv = (challengeOf (sqCvH Ht cv), sqCvH Ht cv) := rfl

theorem forIn_unitH_run {α : Type} (l : List α) (f : α → ChainWith (m := Id) PUnit) (cv : Digest) :
    (forIn l PUnit.unit (fun a _ => do f a; pure (ForInStep.yield PUnit.unit))).run cv =
      ((), l.foldl (fun cv a => ((f a).run cv).2) cv) := by
  induction l generalizing cv with
  | nil => rfl
  | cons a l ih =>
    simp only [List.forIn_cons, List.foldl_cons]
    rw [← ih]
    rfl

theorem forIn_observeH_run (xs : List E) (cv : Digest) :
    (forIn xs PUnit.unit (fun x _ => do
        observeWith (m := Id) Ht x
        pure (ForInStep.yield PUnit.unit))).run cv = ((), obsAllH Ht cv xs) := by
  rw [forIn_unitH_run]
  rfl

theorem forIn_sq2H_run {α : Type} (l : List α) (acc : List (E × E)) (cv : Digest) :
    (forIn l acc (fun _ acc => do
        let lf ← squeezeWith (m := Id) Ht
        let lc ← squeezeWith (m := Id) Ht
        pure (ForInStep.yield (acc ++ [(lf, lc)])))).run cv =
      (acc ++ (sq2H Ht l.length cv).1, (sq2H Ht l.length cv).2) := by
  induction l generalizing acc cv with
  | nil => simp [sq2H]; rfl
  | cons a l ih =>
    simp only [List.forIn_cons, List.length_cons, sq2H]
    rw [← List.singleton_append, ← List.append_assoc, ← ih]
    rfl

theorem forIn_sq3H_run {α : Type} (l : List α) (acc : List (E × E × E)) (cv : Digest) :
    (forIn l acc (fun _ acc => do
        let lf ← squeezeWith (m := Id) Ht
        let la ← squeezeWith (m := Id) Ht
        let lb ← squeezeWith (m := Id) Ht
        pure (ForInStep.yield (acc ++ [(lf, la, lb)])))).run cv =
      (acc ++ (sq3H Ht l.length cv).1, (sq3H Ht l.length cv).2) := by
  induction l generalizing acc cv with
  | nil => simp [sq3H]; rfl
  | cons a l ih =>
    simp only [List.forIn_cons, List.length_cons, sq3H]
    rw [← List.singleton_append, ← List.append_assoc, ← ih]
    rfl

theorem forIn_childrenH_run (cs : List ChildClaims) (cv : Digest) :
    (forIn cs PUnit.unit fun c _ => do
        observeWith (m := Id) Ht (digestScalars c.publicInput).1
        observeWith (m := Id) Ht (digestScalars c.publicInput).2
        forIn (fixedCells c.fresh ++ c.carried.cells) PUnit.unit fun x _ => do
          observeWith (m := Id) Ht x
          pure (ForInStep.yield PUnit.unit)
        pure (ForInStep.yield PUnit.unit) : ChainWith (m := Id) PUnit).run cv =
      ((), obsAllH Ht cv (cs.flatMap childCells)) := by
  induction cs generalizing cv with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.forIn_cons, StateT.run_bind, observeWithH_run, forIn_observeH_run]
    rw [List.flatMap_cons, show obsAllH Ht cv (childCells c ++ cs.flatMap childCells) =
      obsAllH Ht (obsAllH Ht cv (childCells c)) (cs.flatMap childCells) by
        simp [obsAllH, List.foldl_append], ← ih]
    rfl

theorem idH_bind {α β : Type} (x : Id α) (f : α → Id β) : x >>= f = f x := rfl

/-- **The batching over `Ht` from `s0`, run** on the chain (`batch_spec` over `Ht`). -/
theorem batchWithH_spec (s0 : Digest) (cs : List ChildClaims) (h : BatchHints) :
    Id.run (batchWith (m := Id) Ht s0 cs h) =
      let cvA := obsAllH Ht (obsCvH Ht s0 (ofK (Parameters.gpow cs.length))) (cs.flatMap childCells)
      let lB := (sq2H Ht cs.length cvA).1
      let rb := (batchRoundsWith (m := Id) Ht (sumE (List.zipWith (fun c l ↦
        l.1 * c.fresh.bytecodeValue + l.2 * c.carried.bytecodeValue) cs lB)) h.bytecodeRounds).run
          (sq2H Ht cs.length cvA).2
      let lM := (sq3H Ht cs.length rb.2).1
      let rm := (batchRoundsWith (m := Id) Ht (sumE (List.zipWith (fun c l ↦ l.1 * c.fresh.matrixValue +
        l.2.1 * c.carried.matrixA + l.2.2 * c.carried.matrixB) cs lM)) h.matrixRounds).run
        (sq3H Ht cs.length rb.2).2
      if rb.1.2 = h.bytecodeValue * sumE (List.zipWith (fun c l ↦
            l.1 * eqEval c.fresh.bytecodePoint rb.1.1 + l.2 * eqEval c.carried.bytecodePoint rb.1.1)
            cs lB) ∧
          rm.1.2 = h.matrixA * sumE (List.zipWith (fun c l ↦ l.1 * freshWeight c.fresh rm.1.1 +
            l.2.1 * eqEval c.carried.matrixPoint rm.1.1) cs lM) +
            h.matrixB * sumE (List.zipWith (fun c l ↦ l.1 * c.fresh.alpha * freshWeight c.fresh rm.1.1 +
              l.2.2 * eqEval c.carried.matrixPoint rm.1.1) cs lM) then
        some ⟨rb.1.1, h.bytecodeValue, rm.1.1, h.matrixA, h.matrixB⟩
      else none := by
  rw [show Id.run (batchWith (m := Id) Ht s0 cs h) = ((batchWith.go (m := Id) Ht cs h).run s0).1 from rfl]
  unfold batchWith.go
  simp only [StateT.run_bind, observeWithH_run, forIn_childrenH_run, forIn_sq2H_run, forIn_sq3H_run,
    List.nil_append, idH_bind]
  split_ifs <;> rfl

/-- An `Id` run of the rounds over `Ht` draws one challenge per round. -/
theorem batchRoundsWithH_length : ∀ (claim : E) (rounds : List (E × E)) (cv : Digest),
    ((batchRoundsWith (m := Id) Ht claim rounds).run cv).1.1.length = rounds.length
  | _, [], _ => rfl
  | claim, (g1, gInf) :: rest, cv => by
    simp only [batchRoundsWith, StateT.run_bind, observeWithH_run, squeezeWithH_run]
    show (((batchRoundsWith (m := Id) Ht _ rest).run _).1.1.length + 1) = rest.length + 1
    rw [batchRoundsWithH_length]

end Total

/-! ## At BLAKE2s -/

theorem obsCvH_blake : obsCvH blake2sBytes = obsCv := rfl

theorem sqCvH_blake : sqCvH blake2sBytes = sqCv := rfl

theorem obsAllH_blake : obsAllH blake2sBytes = obsAll := rfl

theorem sq2H_blake : sq2H blake2sBytes = sq2 := by
  funext n cv
  induction n generalizing cv with
  | zero => rfl
  | succ n ih => simp only [sq2H, sq2, ih]; rfl

theorem sq3H_blake : sq3H blake2sBytes = sq3 := by
  funext n cv
  induction n generalizing cv with
  | zero => rfl
  | succ n ih => simp only [sq3H, sq3, ih]; rfl

theorem sqIt2H_blake : sqIt2H blake2sBytes = sqIt2 := rfl

theorem sqIt3H_blake : sqIt3H blake2sBytes = sqIt3 := rfl

/-! ## A hash model of the answers -/

/-- The semantics checking nothing. -/
def semNoneC : BlakeSem := ⟨fun _ _ _ _ _ _ ↦ False, fun _ _ _ _ _ _ ↦ instDecidableFalse⟩

/-- **An answered hash as a hash model**, its semantics checking nothing (so the laws hold
vacuously): the hash-model forms of the batching (`BatchSpecM.lean`) read only `H`. -/
def hmOfC (H : List UInt8 → Option Digest) : HashModel where
  sem := semNoneC
  canonical h := h.elim
  H := H
  Prefix bs st := bs = [] ∧ st = ivCells
  prefix_nil := ⟨rfl, rfl⟩
  prefix_step _ h := h.elim
  final _ _ _ _ h := h.elim

/-! ## Answered runs -/

/-- **A partial hash read as a total one**: its answer, `default` where it does not answer. -/
def HdOf (H : List UInt8 → Option Digest) : List UInt8 → Digest := fun x => (H x).getD default

/-- A partial hash agrees with its total reading where it answers. -/
theorem hag_HdOf (H : List UInt8 → Option Digest) : ∀ x d, H x = some d → d = HdOf H x :=
  fun x d h => by simp [HdOf, h]


/-- **`x` answers `y`**: a run over a partial hash that returns a value returns `y`. -/
def Ans {α : Type} (x : Option α) (y : α) : Prop := ∀ v, x = some v → v = y

/-- `Ans` on chain computations: from every state. -/
def AnsS {α : Type} (x : ChainWith (m := Option) α) (y : ChainWith (m := Id) α) : Prop :=
  ∀ cv, Ans (x.run cv) (y.run cv)

theorem ans_pure {α : Type} (a : α) : Ans (pure a : Option α) a := fun _ h => (Option.some.inj h).symm

theorem ans_bind {α β : Type} {x : Option α} {y : α} {f : α → Option β} {g : α → β}
    (hx : Ans x y) (hf : ∀ a, Ans (f a) (g a)) : Ans (x >>= f) (g y) := by
  intro v hv
  rcases hx' : x with _ | a
  · rw [hx'] at hv; cases hv
  · rw [hx'] at hv
    obtain rfl := hx a hx'
    exact hf a v hv

theorem ansS_pure {α : Type} (a : α) : AnsS (pure a : ChainWith (m := Option) α) (pure a) :=
  fun _ => ans_pure _

theorem ansS_bind {α β : Type} {x : ChainWith (m := Option) α} {y : ChainWith (m := Id) α}
    {f : α → ChainWith (m := Option) β} {g : α → ChainWith (m := Id) β}
    (hx : AnsS x y) (hf : ∀ a, AnsS (f a) (g a)) : AnsS (x >>= f) (y >>= g) := by
  intro cv
  simp only [StateT.run_bind]
  exact ans_bind (hx cv) fun p => hf p.1 p.2

theorem ansS_forIn {α β : Type} (f : α → β → ChainWith (m := Option) (ForInStep β))
    (g : α → β → ChainWith (m := Id) (ForInStep β)) (hf : ∀ a b, AnsS (f a b) (g a b)) :
    ∀ (l : List α) (b : β), AnsS (forIn l b f) (forIn l b g)
  | [], _ => ansS_pure _
  | a :: l, b => by
    rw [List.forIn_cons, List.forIn_cons]
    exact ansS_bind (hf a b) fun s => by
      cases s
      · exact ansS_pure _
      · exact ansS_forIn f g hf l _

variable {H : List UInt8 → Option Digest} {Ht : List UInt8 → Digest}

theorem ansS_observe (hag : ∀ x d, H x = some d → d = Ht x) (x : E) :
    AnsS (observeWith (m := Option) H x) (observeWith (m := Id) Ht x) := by
  intro cv v hv
  rw [show (observeWith (m := Option) H x).run cv = (observeWith (m := Option) (hmOfC H).H x).run cv
    from rfl, observeWith_runM, Option.map_eq_some_iff] at hv
  obtain ⟨d, hd, rfl⟩ := hv
  rw [observeWithH_run, hag _ _ hd]
  rfl

theorem ansS_squeeze (hag : ∀ x d, H x = some d → d = Ht x) :
    AnsS (squeezeWith (m := Option) H) (squeezeWith (m := Id) Ht) := by
  intro cv v hv
  rw [show (squeezeWith (m := Option) H).run cv = (squeezeWith (m := Option) (hmOfC H).H).run cv
    from rfl, squeezeWith_runM, Option.map_eq_some_iff] at hv
  obtain ⟨d, hd, rfl⟩ := hv
  rw [squeezeWithH_run, hag _ _ hd]
  rfl

theorem ansS_batchRounds (hag : ∀ x d, H x = some d → d = Ht x) : ∀ (claim : E) (rounds : List (E × E)),
    AnsS (batchRoundsWith (m := Option) H claim rounds) (batchRoundsWith (m := Id) Ht claim rounds)
  | _, [] => ansS_pure _
  | claim, (g1, gInf) :: rest => by
    simp only [batchRoundsWith]
    exact ansS_bind (ansS_observe hag g1) fun _ => ansS_bind (ansS_observe hag gInf) fun _ =>
      ansS_bind (ansS_squeeze hag) fun r => ansS_bind (ansS_batchRounds hag _ rest) fun p =>
        ansS_pure _

/-- **The batching over a partial hash, answered**: closing on a result, it is the batching's over
`Ht`. -/
theorem batchWith_ans (hag : ∀ x d, H x = some d → d = Ht x) (s0 : Digest) (cs : List ChildClaims) (h : BatchHints) :
    Ans (batchWith (m := Option) H s0 cs h) (Id.run (batchWith (m := Id) Ht s0 cs h)) := by
  intro v hv
  have key : AnsS (batchWith.go H cs h) (batchWith.go Ht cs h) := by
    unfold batchWith.go
    refine ansS_bind (ansS_observe hag _) fun _ => ansS_bind ?_ fun _ => ansS_bind ?_ fun lB =>
      ansS_bind (ansS_batchRounds hag _ _) fun p => ansS_bind ?_ fun lM =>
        ansS_bind (ansS_batchRounds hag _ _) fun q => ?_
    · exact ansS_forIn _ _ (fun c _ => ansS_bind (ansS_observe hag _) fun _ =>
        ansS_bind (ansS_observe hag _) fun _ => ansS_bind (ansS_forIn _ _ (fun x _ =>
          ansS_bind (ansS_observe hag x) fun _ => ansS_pure _) _ _) fun _ => ansS_pure _) _ _
    · exact ansS_forIn _ _ (fun _ acc => ansS_bind (ansS_squeeze hag) fun _ =>
        ansS_bind (ansS_squeeze hag) fun _ => ansS_pure _) _ _
    · exact ansS_forIn _ _ (fun _ acc => ansS_bind (ansS_squeeze hag) fun _ =>
        ansS_bind (ansS_squeeze hag) fun _ => ansS_bind (ansS_squeeze hag) fun _ => ansS_pure _) _ _
    · rcases q with ⟨rM, fM⟩
      dsimp only
      split_ifs
      · exact ansS_pure _
      · exact ansS_pure _
  simp only [batchWith, StateT.run'_eq] at hv ⊢
  obtain ⟨p, he, rfl⟩ := Option.map_eq_some_iff.mp hv
  rw [key s0 p he]
  rfl


/-! ## The answered steps of a chain -/

/-- **Every absorb of `xs` from `cv` is answered** by `H` at its value over `Ht`. -/
def ObsAns (H : List UInt8 → Option Digest) (Ht : List UInt8 → Digest) : Digest → List E → Prop
  | _, [] => True
  | cv, x :: xs => H (digestBytes cv ++ blockOf x 1) = some (obsCvH Ht cv x) ∧
      ObsAns H Ht (obsCvH Ht cv x) xs

/-- **`n` double squeezes from `cv` are answered.** -/
def Sq2Ans (H : List UInt8 → Option Digest) (Ht : List UInt8 → Digest) : ℕ → Digest → Prop
  | 0, _ => True
  | n + 1, cv => H (digestBytes cv ++ blockOf 0 2) = some (sqCvH Ht cv) ∧
      H (digestBytes (sqCvH Ht cv) ++ blockOf 0 2) = some (sqCvH Ht (sqCvH Ht cv)) ∧
      Sq2Ans H Ht n (sqCvH Ht (sqCvH Ht cv))

/-- **`n` triple squeezes from `cv` are answered.** -/
def Sq3Ans (H : List UInt8 → Option Digest) (Ht : List UInt8 → Digest) : ℕ → Digest → Prop
  | 0, _ => True
  | n + 1, cv => H (digestBytes cv ++ blockOf 0 2) = some (sqCvH Ht cv) ∧
      H (digestBytes (sqCvH Ht cv) ++ blockOf 0 2) = some (sqCvH Ht (sqCvH Ht cv)) ∧
      H (digestBytes (sqCvH Ht (sqCvH Ht cv)) ++ blockOf 0 2) =
        some (sqCvH Ht (sqCvH Ht (sqCvH Ht cv))) ∧
      Sq3Ans H Ht n (sqCvH Ht (sqCvH Ht (sqCvH Ht cv)))

theorem obsAns_append : ∀ (cv : Digest) (xs ys : List E),
    ObsAns H Ht cv (xs ++ ys) ↔ ObsAns H Ht cv xs ∧ ObsAns H Ht (obsAllH Ht cv xs) ys
  | cv, [], ys => by simp [ObsAns, obsAllH]
  | cv, x :: xs, ys => by
    simp only [List.cons_append, ObsAns, obsAns_append (obsCvH Ht cv x) xs ys, obsAllH_cons, and_assoc]

/-- The answered absorbs, by index. -/
theorem obsAns_get : ∀ {cv : Digest} {xs : List E}, ObsAns H Ht cv xs → ∀ k < xs.length,
    H (digestBytes (obsAllH Ht cv (xs.take k)) ++ blockOf (xs.getD k 0) 1) =
      some (obsAllH Ht cv (xs.take (k + 1)))
  | _, [], _, k, hk => absurd hk (by simp)
  | cv, x :: xs, ⟨h1, h2⟩, 0, _ => by simpa [obsAllH] using h1
  | cv, x :: xs, ⟨_, h2⟩, k + 1, hk => by
    have := obsAns_get h2 k (by simpa using hk)
    simpa [obsAllH_cons] using this

/-- The answered double squeezes, by index. -/
theorem sq2Ans_get : ∀ {n : ℕ} {cv : Digest}, Sq2Ans H Ht n cv → ∀ c < n,
    H (digestBytes (sqIt2H Ht cv c) ++ blockOf 0 2) = some (sqCvH Ht (sqIt2H Ht cv c)) ∧
      H (digestBytes (sqCvH Ht (sqIt2H Ht cv c)) ++ blockOf 0 2) =
        some (sqCvH Ht (sqCvH Ht (sqIt2H Ht cv c)))
  | 0, _, _, c, hc => absurd hc (by omega)
  | n + 1, cv, ⟨h1, h2, _⟩, 0, _ => ⟨h1, h2⟩
  | n + 1, cv, ⟨_, _, h3⟩, c + 1, hc => by
    have := sq2Ans_get h3 c (by omega)
    rwa [show sqIt2H Ht cv (c + 1) = sqIt2H Ht (sqCvH Ht (sqCvH Ht cv)) c from
      Function.iterate_succ_apply _ _ _]

/-- The answered triple squeezes, by index. -/
theorem sq3Ans_get : ∀ {n : ℕ} {cv : Digest}, Sq3Ans H Ht n cv → ∀ c < n,
    H (digestBytes (sqIt3H Ht cv c) ++ blockOf 0 2) = some (sqCvH Ht (sqIt3H Ht cv c)) ∧
      H (digestBytes (sqCvH Ht (sqIt3H Ht cv c)) ++ blockOf 0 2) =
        some (sqCvH Ht (sqCvH Ht (sqIt3H Ht cv c))) ∧
      H (digestBytes (sqCvH Ht (sqCvH Ht (sqIt3H Ht cv c))) ++ blockOf 0 2) =
        some (sqCvH Ht (sqCvH Ht (sqCvH Ht (sqIt3H Ht cv c))))
  | 0, _, _, c, hc => absurd hc (by omega)
  | n + 1, cv, ⟨h1, h2, h3, _⟩, 0, _ => ⟨h1, h2, h3⟩
  | n + 1, cv, ⟨_, _, _, h4⟩, c + 1, hc => by
    have := sq3Ans_get h4 c (by omega)
    rwa [show sqIt3H Ht cv (c + 1) = sqIt3H Ht (sqCvH Ht (sqCvH Ht (sqCvH Ht cv))) c from
      Function.iterate_succ_apply _ _ _]

/-- An answered run of absorbs is answered step by step, at the values over `Ht`. -/
theorem obsAllM_ans (hag : ∀ x d, H x = some d → d = Ht x) : ∀ {cv c : Digest} {xs : List E}, obsAllM (hmOfC H) cv xs = some c →
    ObsAns H Ht cv xs ∧ c = obsAllH Ht cv xs
  | cv, c, [], h => ⟨trivial, (Option.some.inj h).symm⟩
  | cv, c, x :: xs, h => by
    simp only [obsAllM, Option.bind_eq_some_iff] at h
    obtain ⟨d, hd, h⟩ := h
    have e : d = obsCvH Ht cv x := hag _ _ hd
    subst e
    obtain ⟨h1, h2⟩ := obsAllM_ans hag h
    exact ⟨⟨hd, h1⟩, h2⟩

theorem sq2M_ans (hag : ∀ x d, H x = some d → d = Ht x) : ∀ {n : ℕ} {cv : Digest} {r : List (E × E) × Digest},
    sq2M (hmOfC H) n cv = some r → Sq2Ans H Ht n cv ∧ r = sq2H Ht n cv
  | 0, cv, r, h => ⟨trivial, (Option.some.inj h).symm⟩
  | n + 1, cv, r, h => by
    simp only [sq2M, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, b, hb, q, hq, rfl⟩ := h
    have ea : a = sqCvH Ht cv := hag _ _ ha
    subst ea
    have eb : b = sqCvH Ht (sqCvH Ht cv) := hag _ _ hb
    subst eb
    obtain ⟨h1, rfl⟩ := sq2M_ans hag hq
    exact ⟨⟨ha, hb, h1⟩, rfl⟩

theorem sq3M_ans (hag : ∀ x d, H x = some d → d = Ht x) : ∀ {n : ℕ} {cv : Digest} {r : List (E × E × E) × Digest},
    sq3M (hmOfC H) n cv = some r → Sq3Ans H Ht n cv ∧ r = sq3H Ht n cv
  | 0, cv, r, h => ⟨trivial, (Option.some.inj h).symm⟩
  | n + 1, cv, r, h => by
    simp only [sq3M, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, b, hb, e, he, q, hq, rfl⟩ := h
    have ea : a = sqCvH Ht cv := hag _ _ ha
    subst ea
    have eb : b = sqCvH Ht (sqCvH Ht cv) := hag _ _ hb
    subst eb
    have ee : e = sqCvH Ht (sqCvH Ht (sqCvH Ht cv)) := hag _ _ he
    subst ee
    obtain ⟨h1, rfl⟩ := sq3M_ans hag hq
    exact ⟨⟨ha, hb, he, h1⟩, rfl⟩

theorem observeWith_runH (x : E) (cv : Digest) :
    (observeWith (m := Option) H x).run cv = (obsCvM (hmOfC H) cv x).map fun d => ((), d) :=
  observeWith_runM (M := hmOfC H) x cv

theorem forIn_children_runH (cs : List ChildClaims) (cv : Digest) :
    (forIn cs PUnit.unit fun (c : ChildClaims) _ => do
        observeWith (m := Option) H (digestScalars c.publicInput).1
        observeWith (m := Option) H (digestScalars c.publicInput).2
        forIn (fixedCells c.fresh ++ c.carried.cells) PUnit.unit fun x _ => do
          observeWith (m := Option) H x
          pure (ForInStep.yield PUnit.unit)
        pure (ForInStep.yield PUnit.unit)).run cv =
      (obsAllM (hmOfC H) cv (cs.flatMap childCells)).map fun d => ((), d) :=
  forIn_children_runM (M := hmOfC H) cs cv

theorem forIn_sq2_runH {α : Type} (l : List α) (acc : List (E × E)) (cv : Digest) :
    (forIn l acc (fun _ acc => do
        let lf ← squeezeWith (m := Option) H
        let lc ← squeezeWith (m := Option) H
        pure (ForInStep.yield (acc ++ [(lf, lc)])))).run cv =
      (sq2M (hmOfC H) l.length cv).map fun r => (acc ++ r.1, r.2) :=
  forIn_sq2_runM (M := hmOfC H) l acc cv

theorem forIn_sq3_runH {α : Type} (l : List α) (acc : List (E × E × E)) (cv : Digest) :
    (forIn l acc (fun _ acc => do
        let lf ← squeezeWith (m := Option) H
        let la ← squeezeWith (m := Option) H
        let lb ← squeezeWith (m := Option) H
        pure (ForInStep.yield (acc ++ [(lf, la, lb)])))).run cv =
      (sq3M (hmOfC H) l.length cv).map fun r => (acc ++ r.1, r.2) :=
  forIn_sq3_runM (M := hmOfC H) l acc cv

/-- **The batching over a partial hash, taken apart**: closing from `s0`, its count's absorb, its
children's absorbs, its two lambda squeezes and its two rounds' runs are answered, at the values
over `Ht`. -/
theorem batchWith_steps (hag : ∀ x d, H x = some d → d = Ht x) {s0 : Digest} {cs : List ChildClaims}
    {h : BatchHints} {r : Option DeferredClaim}
    (hb : batchWith (m := Option) H s0 cs h = some r) :
    let cv1 := obsCvH Ht s0 (ofK (Parameters.gpow cs.length))
    let cvA := obsAllH Ht cv1 (cs.flatMap childCells)
    let lB := (sq2H Ht cs.length cvA).1
    let rb := (batchRoundsWith (m := Id) Ht (sumE (List.zipWith (fun c l ↦
      l.1 * c.fresh.bytecodeValue + l.2 * c.carried.bytecodeValue) cs lB)) h.bytecodeRounds).run
        (sq2H Ht cs.length cvA).2
    let lM := (sq3H Ht cs.length rb.2).1
    H (digestBytes s0 ++ blockOf (ofK (Parameters.gpow cs.length)) 1) = some cv1 ∧
      ObsAns H Ht cv1 (cs.flatMap childCells) ∧ Sq2Ans H Ht cs.length cvA ∧
      (batchRoundsWith (m := Option) H (sumE (List.zipWith (fun c l ↦
        l.1 * c.fresh.bytecodeValue + l.2 * c.carried.bytecodeValue) cs lB)) h.bytecodeRounds).run
          (sq2H Ht cs.length cvA).2 = some rb ∧
      Sq3Ans H Ht cs.length rb.2 ∧
      (batchRoundsWith (m := Option) H (sumE (List.zipWith (fun c l ↦ l.1 * c.fresh.matrixValue +
        l.2.1 * c.carried.matrixA + l.2.2 * c.carried.matrixB) cs lM)) h.matrixRounds).run
          (sq3H Ht cs.length rb.2).2 =
        some ((batchRoundsWith (m := Id) Ht (sumE (List.zipWith (fun c l ↦ l.1 * c.fresh.matrixValue +
          l.2.1 * c.carried.matrixA + l.2.2 * c.carried.matrixB) cs lM)) h.matrixRounds).run
            (sq3H Ht cs.length rb.2).2) := by
  intro cv1 cvA lB rb lM
  have hrun : ∀ claim rounds cv q, (batchRoundsWith (m := Option) H claim rounds).run cv = some q →
      q = (batchRoundsWith (m := Id) Ht claim rounds).run cv :=
    fun claim rounds cv q hq => ansS_batchRounds hag claim rounds cv q hq
  have hgo : ∃ q, (batchWith.go H cs h).run s0 = some q := by
    unfold batchWith at hb
    rw [StateT.run'_eq] at hb
    rcases e : (batchWith.go H cs h).run s0 with _ | q
    · rw [e] at hb; cases hb
    · exact ⟨q, rfl⟩
  obtain ⟨q, hq⟩ := hgo
  unfold batchWith.go at hq
  simp only [StateT.run_bind, observeWith_runH, forIn_children_runH, forIn_sq2_runH,
    forIn_sq3_runH, Option.bind_eq_bind] at hq
  rw [Option.bind_eq_some_iff] at hq
  obtain ⟨⟨_, c1⟩, h1, hq⟩ := hq
  rw [Option.map_eq_some_iff] at h1
  obtain ⟨d1, hd1, he1⟩ := h1
  simp only [Prod.mk.injEq, true_and] at he1
  subst he1
  have ec1 : d1 = cv1 := hag _ _ hd1
  subst ec1
  rw [Option.bind_eq_some_iff] at hq
  obtain ⟨⟨_, c2⟩, h2, hq⟩ := hq
  rw [Option.map_eq_some_iff] at h2
  obtain ⟨d2, hd2, he2⟩ := h2
  simp only [Prod.mk.injEq, true_and] at he2
  subst he2
  obtain ⟨hA, rfl⟩ := obsAllM_ans hag hd2
  rw [Option.bind_eq_some_iff] at hq
  obtain ⟨⟨lB', c3⟩, h3, hq⟩ := hq
  rw [Option.map_eq_some_iff] at h3
  obtain ⟨q3, hq3, he3⟩ := h3
  obtain ⟨hB, rfl⟩ := sq2M_ans hag hq3
  simp only [List.nil_append, Prod.mk.injEq] at he3
  obtain ⟨rfl, rfl⟩ := he3
  rw [Option.bind_eq_some_iff] at hq
  obtain ⟨⟨⟨rs, fin⟩, c4⟩, h4, hq⟩ := hq
  have e4 := hrun _ _ _ _ h4
  rw [Option.bind_eq_some_iff] at hq
  obtain ⟨⟨lM', c5⟩, h5, hq⟩ := hq
  rw [Option.map_eq_some_iff] at h5
  obtain ⟨q5, hq5, he5⟩ := h5
  simp only [List.nil_append, Prod.mk.injEq] at he5
  obtain ⟨rfl, rfl⟩ := he5
  have ec4 : c4 = rb.2 := congrArg Prod.snd e4
  subst ec4
  obtain ⟨hC, rfl⟩ := sq3M_ans hag hq5
  rw [Option.bind_eq_some_iff] at hq
  obtain ⟨⟨⟨rM, finM⟩, c6⟩, h6, -⟩ := hq
  have e6 := hrun _ _ _ _ h6
  exact ⟨hd1, hA, hB, by rw [h4, e4], hC, by rw [h6, e6]⟩

end
end LeanVM.Guest.B1.Main
