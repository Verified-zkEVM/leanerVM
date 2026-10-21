/-
  LeanVM.Guest.B1.Sumcheck

  B1 for `batch_sumcheck`, the claim-batching sumcheck, at each of its specializations: one
  generic argument over the number of rounds.
-/

module

public import LeanVM.Guest.B1.Opening
public import LeanVM.Guest.Value.NodeSome

/-!
# `batch_sumcheck` (TRIAGE #27)

`batch_sumcheck(fs0, fs1, msgs, running, point, n)` (G:879-893) runs `n` rounds of a batching
sumcheck: per round two stream words `g(1)`, `g(∞)` at `msgs[2r]`, `msgs[2r + 1]`, absorbed
(`fs_next`), a squeeze, the challenge stored at `point[r]`, the claim folded. That is
`Node.batchRounds` (N:215). Its expansion is `n` rounds `bsBlock r` of 51 values from
`(7 + 51 * r) = 7 + 51·r` (two `fs_next`, a `squeeze`, a store and the fold), the state of round
`r ≥ 1` being the previous squeeze's output and its claim the previous fold; `bsBody n` is equal
by `rfl` to each specialization (`__L22`, `__L28`).

Under a hash model: `batch_sumcheck_model` concludes `Node.batchRoundsWith` over the model's hash
(`Spec/NodeWith.lean`) answered (`MeaningBatchSumcheckWith`), round by round from the answered
digests of each block (`BsOkB`, `batchRoundsWith_cons_run`); the deployed iff's forward direction
is it at `HashModel.deployed` (`meaningBatchSumcheckWith_deployed`, by `batchRoundsWith_some`).

`bsRun` mirrors `Node.batchRounds` on the chain (`batchRounds_run`), and `bsSt` gives its state
and claim after each prefix of the rounds.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## The specification's rounds, as a function -/

/-- One round: absorb `g(1)`, `g(∞)`, squeeze, fold. The new claim and state. -/
def bsStep (st : E × Digest) (g : E × E) : E × Digest :=
  let cv := sqCv (obsCv (obsCv st.2 g.1) g.2)
  let r := challengeOf cv
  let g0 := st.1 + g.1
  ((g.2 * r + (g0 + g.1 + g.2)) * r + g0, cv)

/-- `Node.batchRounds` on the chain: the challenges, the final claim, the final state. -/
def bsRun : List (E × E) → E → Digest → (List E × E) × Digest
  | [], claim, cv => (([], claim), cv)
  | g :: rest, claim, cv =>
    let st := bsStep (claim, cv) g
    let res := bsRun rest st.1 st.2
    ((challengeOf st.2 :: res.1.1, res.1.2), res.2)

theorem batchRounds_run (rounds : List (E × E)) (claim : E) (cv : Digest) :
    (Node.batchRounds claim rounds).run cv = bsRun rounds claim cv := by
  induction rounds generalizing claim cv with
  | nil => rfl
  | cons g rest ih =>
    obtain ⟨g1, gInf⟩ := g
    simp only [Node.batchRounds, Node.observe, Node.squeeze, StateT.run_bind, StateT.run_modify,
      StateT.run_get, StateT.run_set, StateT.run_pure, ih]
    rfl

/-- The claim and state after the first `i` rounds. -/
def bsSt (rounds : List (E × E)) (claim : E) (cv : Digest) : ℕ → E × Digest
  | 0 => (claim, cv)
  | i + 1 => bsStep (bsSt rounds claim cv i) (rounds.getD i (0, 0))

theorem bsSt_cons (g : E × E) (rest : List (E × E)) (claim : E) (cv : Digest) :
    ∀ i, bsSt (g :: rest) claim cv (i + 1) =
      bsSt rest (bsStep (claim, cv) g).1 (bsStep (claim, cv) g).2 i
  | 0 => rfl
  | i + 1 => by
    rw [bsSt, bsSt_cons g rest claim cv i, List.getD_cons_succ]
    rfl

theorem bsRun_eq (rounds : List (E × E)) (claim : E) (cv : Digest) :
    bsRun rounds claim cv =
      (((List.range rounds.length).map fun j => challengeOf (bsSt rounds claim cv (j + 1)).2,
        (bsSt rounds claim cv rounds.length).1), (bsSt rounds claim cv rounds.length).2) := by
  induction rounds generalizing claim cv with
  | nil => rfl
  | cons g rest ih =>
    rw [bsRun, ih, List.length_cons, List.range_succ_eq_map, bsSt_cons]
    simp only [List.map_cons, List.map_map, Function.comp_def, bsSt_cons]
    rfl

/-! ## The template -/

/-- Round `r`'s state cell: the arguments at `r = 0`, the previous squeeze's output after. -/
def bsS : ℕ → ℕ
  | 0 => 5
  | r + 1 => 42 + 51 * r

/-- Round `r`'s claim: the argument at `r = 0`, the previous fold after. -/
def bsC : ℕ → ℕ
  | 0 => 3
  | r + 1 => 57 + 51 * r

/-- Round `r`. -/
def bsBlock (r : ℕ) : List Stmt :=
  fsNextT (.n (bsS r)) (.n (bsS r + 1)) (.n 2) (2 * r) ((7 + 51 * r)) ++
    fsNextT (.n ((7 + 51 * r) + 13)) (.n ((7 + 51 * r) + 14)) (.n 2) (2 * r + 1) ((7 + 51 * r) + 15) ++
    squeezeT (.n ((7 + 51 * r) + 28)) (.n ((7 + 51 * r) + 29)) ((7 + 51 * r) + 30) ++
    [.atom (.load (.n ((7 + 51 * r) + 43)) (.n 4) r),
      .atom (.add (.n ((7 + 51 * r) + 44)) (.n (bsC r)) (.n ((7 + 51 * r)))),
      .atom (.add (.n ((7 + 51 * r) + 45)) (.n ((7 + 51 * r) + 44)) (.n ((7 + 51 * r)))),
      .atom (.add (.n ((7 + 51 * r) + 46)) (.n ((7 + 51 * r) + 45)) (.n ((7 + 51 * r) + 15))),
      .atom (.mul (.n ((7 + 51 * r) + 47)) (.n ((7 + 51 * r) + 15)) (.n ((7 + 51 * r) + 43))),
      .atom (.add (.n ((7 + 51 * r) + 48)) (.n ((7 + 51 * r) + 47)) (.n ((7 + 51 * r) + 46))),
      .atom (.mul (.n ((7 + 51 * r) + 49)) (.n ((7 + 51 * r) + 48)) (.n ((7 + 51 * r) + 43))),
      .atom (.add (.n ((7 + 51 * r) + 50)) (.n ((7 + 51 * r) + 49)) (.n ((7 + 51 * r) + 44)))]

/-- The expansion of `batch_sumcheck` at `n ≥ 1` rounds. -/
def bsBody (n : ℕ) : List Stmt :=
  [.atom (.copy (.n 5) (.n 0)), .atom (.copy (.n 6) (.n 1))] ++
    ((List.range n).map bsBlock).flatten ++
    [.atom (.copy (.n (7 + 51 * n)) (.n (51 * n - 9))),
      .atom (.copy (.n (8 + 51 * n)) (.n (51 * n - 8))),
      .atom (.copy (.n (9 + 51 * n)) (.n (51 * n + 6))),
      .ret [.n (7 + 51 * n), .n (8 + 51 * n), .n (9 + 51 * n)]]

/-- What round `r` asks of a valuation. -/
def BsOk (rd : Reader) (σ : Val) (r : ℕ) : Prop :=
  (LoadHolds rd (σ (.n 2)) (2 * r) (σ (.n ((7 + 51 * r)))) ∧
    ∃ cv, (σ (.n (bsS r)), σ (.n (bsS r + 1))) = digestScalars cv ∧
      ∀ k, 2 ≤ k → k < 14 → σ (.n ((7 + 51 * r) + 1 + k)) = fsVals (σ (.n ((7 + 51 * r)))) cv 1 k) ∧
  (LoadHolds rd (σ (.n 2)) (2 * r + 1) (σ (.n ((7 + 51 * r) + 15))) ∧
    ∃ cv, (σ (.n ((7 + 51 * r) + 13)), σ (.n ((7 + 51 * r) + 14))) = digestScalars cv ∧
      ∀ k, 2 ≤ k → k < 14 →
        σ (.n ((7 + 51 * r) + 15 + 1 + k)) = fsVals (σ (.n ((7 + 51 * r) + 15))) cv 1 k) ∧
  (∃ cv, (σ (.n ((7 + 51 * r) + 28)), σ (.n ((7 + 51 * r) + 29))) = digestScalars cv ∧
    ∀ k < 14, σ (.n ((7 + 51 * r) + 30 + k)) = sqVals cv k) ∧
  LoadHolds rd (σ (.n 4)) r (σ (.n ((7 + 51 * r) + 43))) ∧
  σ (.n ((7 + 51 * r) + 44)) = σ (.n (bsC r)) + σ (.n ((7 + 51 * r))) ∧
  σ (.n ((7 + 51 * r) + 45)) = σ (.n ((7 + 51 * r) + 44)) + σ (.n ((7 + 51 * r))) ∧
  σ (.n ((7 + 51 * r) + 46)) = σ (.n ((7 + 51 * r) + 45)) + σ (.n ((7 + 51 * r) + 15)) ∧
  σ (.n ((7 + 51 * r) + 47)) = σ (.n ((7 + 51 * r) + 15)) * σ (.n ((7 + 51 * r) + 43)) ∧
  σ (.n ((7 + 51 * r) + 48)) = σ (.n ((7 + 51 * r) + 47)) + σ (.n ((7 + 51 * r) + 46)) ∧
  σ (.n ((7 + 51 * r) + 49)) = σ (.n ((7 + 51 * r) + 48)) * σ (.n ((7 + 51 * r) + 43)) ∧
  σ (.n ((7 + 51 * r) + 50)) = σ (.n ((7 + 51 * r) + 49)) + σ (.n ((7 + 51 * r) + 44))

theorem holds_bsBlock (r : ℕ) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (bsBlock r) True kret ↔ BsOk rd σ r := by
  rw [bsBlock, holdsList_append, holdsList_append, holdsList_append, holds_fsNextT,
    holds_fsNextT, holds_squeezeT]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, BsOk]

/-! ## The meaning -/

/-- **`batch_sumcheck(n)`** (G:879-893; TRIAGE #27): from the state of `cv`, the `n` rounds'
words at `msgs`, `g(1)` then `g(∞)` per round, are `Node.batchRounds running rounds` (N:215),
which returns the challenges `rs`, stored at `point`, the final claim and the final state; the
function returns that state's cells and the claim. -/
def MeaningBatchSumcheck (n : ℕ) (rd : Reader) : List E → List E → Prop
  | [s0, s1, msgs, running, point], rets =>
      ∃ cv rounds rs final cv', (s0, s1) = digestScalars cv ∧ rounds.length = n ∧
        (∀ r (hr : r < rounds.length),
          LoadHolds rd msgs (2 * r) rounds[r].1 ∧ LoadHolds rd msgs (2 * r + 1) rounds[r].2) ∧
        (Node.batchRounds running rounds).run cv = ((rs, final), cv') ∧ ReadsAt rd point rs ∧
        rets = [(digestScalars cv').1, (digestScalars cv').2, final]
  | _, _ => False

theorem core568_body : Fn.body Data.core568 = bsBody 22 := stmtsEqb_sound (by decide +kernel)

theorem core571_body : Fn.body Data.core571 = bsBody 28 := stmtsEqb_sound (by decide +kernel)

/-! ## The honest valuation -/

/-- Round `r`'s 51 values, from its state and claim `st` and its words `g`. -/
def bsVals (st : E × Digest) (g : E × E) (k : ℕ) : E :=
  let cvB := obsCv st.2 g.1
  let cvC := obsCv cvB g.2
  let rv := challengeOf (sqCv cvC)
  let g0 := st.1 + g.1
  if k = 0 then g.1 else if k < 15 then fsVals g.1 st.2 1 (k - 1)
  else if k = 15 then g.2 else if k < 30 then fsVals g.2 cvB 1 (k - 16)
  else if k < 44 then sqVals cvC (k - 30)
  else [g0, g0 + g.1, g0 + g.1 + g.2, g.2 * rv, g.2 * rv + (g0 + g.1 + g.2),
    (g.2 * rv + (g0 + g.1 + g.2)) * rv, (g.2 * rv + (g0 + g.1 + g.2)) * rv + g0].getD (k - 44) 0

/-- The honest valuation after `i` rounds. -/
def bsSig (base : Val) (rounds : List (E × E)) (claim : E) (cv : Digest) : ℕ → Val
  | 0 => setl base 5 [(digestScalars cv).1, (digestScalars cv).2]
  | i + 1 => setv (bsSig base rounds claim cv i) ((7 + 51 * i)) 51
      (bsVals (bsSt rounds claim cv i) (rounds.getD i (0, 0)))

theorem bsSig_lt (base : Val) (rounds : List (E × E)) (claim : E) (cv : Digest) :
    ∀ (m i k : ℕ), i ≤ m → k < (7 + 51 * i) →
      bsSig base rounds claim cv m (.n k) = bsSig base rounds claim cv i (.n k)
  | 0, i, k, h, _ => by rw [show i = 0 by omega]
  | m + 1, i, k, h, hk => by
    rcases Nat.lt_or_ge i (m + 1) with hi | hi
    · rw [bsSig, set_n_lt (by omega)]
      exact bsSig_lt base rounds claim cv m i k (by omega) hk
    · rw [show i = m + 1 by omega]

theorem bsSig_blk (base : Val) (rounds : List (E × E)) (claim : E) (cv : Digest) (m r k : ℕ)
    (hr : r < m) (hk : k < 51) :
    bsSig base rounds claim cv m (.n ((7 + 51 * r) + k)) =
      bsVals (bsSt rounds claim cv r) (rounds.getD r (0, 0)) k := by
  rw [bsSig_lt base rounds claim cv m (r + 1) _ hr (by omega), bsSig, set_n_in (by omega) (by omega),
    Nat.add_sub_cancel_left]

theorem bsSig_base (base : Val) (rounds : List (E × E)) (claim : E) (cv : Digest) (m k : ℕ)
    (hk : k < 5) : bsSig base rounds claim cv m (.n k) = base (.n k) := by
  rw [bsSig_lt base rounds claim cv m 0 k (by omega) (by omega), bsSig, setl, set_n_lt hk]

/-- The state cells and the claim each round starts from. -/
theorem bsSig_start (base : Val) (rounds : List (E × E)) (claim : E) (cv : Digest) (m r : ℕ)
    (hr : r ≤ m) (h3 : base (.n 3) = claim) :
    (bsSig base rounds claim cv m (.n (bsS r)), bsSig base rounds claim cv m (.n (bsS r + 1))) =
        digestScalars (bsSt rounds claim cv r).2 ∧
      bsSig base rounds claim cv m (.n (bsC r)) = (bsSt rounds claim cv r).1 := by
  cases r with
  | zero =>
    rw [bsSig_lt base rounds claim cv m 0 _ (by omega) (by simp [bsS]),
      bsSig_lt base rounds claim cv m 0 _ (by omega) (by simp [bsS]),
      bsSig_lt base rounds claim cv m 0 _ (by omega) (by simp [bsC])]
    simp only [bsSig, setl, bsS, bsC, List.length_cons, List.length_nil]
    rw [set_n_in (by omega) (by omega), set_n_in (by omega) (by omega), set_n_lt (by omega), h3]
    exact ⟨rfl, rfl⟩
  | succ r =>
    have e35 := bsSig_blk base rounds claim cv m r 35 (by omega) (by omega)
    have e36 := bsSig_blk base rounds claim cv m r 36 (by omega) (by omega)
    have e50 := bsSig_blk base rounds claim cv m r 50 (by omega) (by omega)
    rw [show bsS (r + 1) = (7 + 51 * r) + 35 by simp [bsS]; omega,
      show (7 + 51 * r) + 35 + 1 = (7 + 51 * r) + 36 by omega, show bsC (r + 1) = (7 + 51 * r) + 50 by simp [bsC]; omega,
      e35, e36, e50]
    refine ⟨?_, rfl⟩
    simp only [bsVals]
    rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega),
      ite_pos' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega),
      ite_neg' (by omega), ite_pos' (by omega)]
    show ((digestScalars (absorbCv _ 0 2)).1, (digestScalars (absorbCv _ 0 2)).2) = _
    rw [Prod.mk.eta]
    rfl

/-! ## The theorem -/

theorem bs_fs1 (st : E × Digest) (g : E × E) (k : ℕ) (hk1 : 2 ≤ k) (hk2 : k < 14) :
    bsVals st g (1 + k) = fsVals g.1 st.2 1 k := by
  simp only [bsVals]
  rw [ite_neg' (by omega), ite_pos' (by omega), show 1 + k - 1 = k by omega]

theorem bs_fs2 (st : E × Digest) (g : E × E) (k : ℕ) (hk1 : 2 ≤ k) (hk2 : k < 14) :
    bsVals st g (15 + 1 + k) = fsVals g.2 (obsCv st.2 g.1) 1 k := by
  simp only [bsVals]
  rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_pos' (by omega),
    show 15 + 1 + k - 16 = k by omega]

theorem bs_sq (st : E × Digest) (g : E × E) (k : ℕ) (hk : k < 14) :
    bsVals st g (30 + k) = sqVals (obsCv (obsCv st.2 g.1) g.2) k := by
  simp only [bsVals]
  rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega),
    ite_pos' (by omega), show 30 + k - 30 = k by omega]

/-! ## Under a hash model -/

/-- What round `r` gives under a hash model: `BsOk` with the two absorptions' and the squeeze's
hashes answered, each output the answered digest's cells. -/
def BsOkB (M : HashModel) (rd : Reader) (σ : Val) (r : ℕ) : Prop :=
  (LoadHolds rd (σ (.n 2)) (2 * r) (σ (.n ((7 + 51 * r)))) ∧
    ∃ cv d, (σ (.n (bsS r)), σ (.n (bsS r + 1))) = digestScalars cv ∧
      obsCvM M cv (σ (.n (7 + 51 * r))) = some d ∧
      ∀ k, 2 ≤ k → k < 14 → σ (.n ((7 + 51 * r) + 1 + k)) = fsValsD (σ (.n ((7 + 51 * r)))) d 1 k) ∧
  (LoadHolds rd (σ (.n 2)) (2 * r + 1) (σ (.n ((7 + 51 * r) + 15))) ∧
    ∃ cv d, (σ (.n ((7 + 51 * r) + 13)), σ (.n ((7 + 51 * r) + 14))) = digestScalars cv ∧
      obsCvM M cv (σ (.n ((7 + 51 * r) + 15))) = some d ∧
      ∀ k, 2 ≤ k → k < 14 →
        σ (.n ((7 + 51 * r) + 15 + 1 + k)) = fsValsD (σ (.n ((7 + 51 * r) + 15))) d 1 k) ∧
  (∃ cv d, (σ (.n ((7 + 51 * r) + 28)), σ (.n ((7 + 51 * r) + 29))) = digestScalars cv ∧
    sqCvM M cv = some d ∧ ∀ k < 14, σ (.n ((7 + 51 * r) + 30 + k)) = sqValsD d k) ∧
  LoadHolds rd (σ (.n 4)) r (σ (.n ((7 + 51 * r) + 43))) ∧
  σ (.n ((7 + 51 * r) + 44)) = σ (.n (bsC r)) + σ (.n ((7 + 51 * r))) ∧
  σ (.n ((7 + 51 * r) + 45)) = σ (.n ((7 + 51 * r) + 44)) + σ (.n ((7 + 51 * r))) ∧
  σ (.n ((7 + 51 * r) + 46)) = σ (.n ((7 + 51 * r) + 45)) + σ (.n ((7 + 51 * r) + 15)) ∧
  σ (.n ((7 + 51 * r) + 47)) = σ (.n ((7 + 51 * r) + 15)) * σ (.n ((7 + 51 * r) + 43)) ∧
  σ (.n ((7 + 51 * r) + 48)) = σ (.n ((7 + 51 * r) + 47)) + σ (.n ((7 + 51 * r) + 46)) ∧
  σ (.n ((7 + 51 * r) + 49)) = σ (.n ((7 + 51 * r) + 48)) * σ (.n ((7 + 51 * r) + 43)) ∧
  σ (.n ((7 + 51 * r) + 50)) = σ (.n ((7 + 51 * r) + 49)) + σ (.n ((7 + 51 * r) + 44))

theorem holdsB_bsBlock {M : HashModel} (r : ℕ) (kret : List E → Prop)
    (h : Stmt.HoldsListB M.sem C rd σ (bsBlock r) True kret) : BsOkB M rd σ r := by
  rw [bsBlock, holdsListB_append, holdsListB_append, holdsListB_append] at h
  obtain ⟨hA, h⟩ := holdsB_fsNextT _ _ _ _ _ h
  obtain ⟨hB, h⟩ := holdsB_fsNextT _ _ _ _ _ h
  obtain ⟨hC, h⟩ := holdsB_squeezeT _ _ _ h
  simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, and_true] at h
  exact ⟨hA, hB, hC, h⟩

/-- **`batch_sumcheck(n)` under a hash model** (the meaning of `MeaningBatchSumcheck`, every hash
answered): the rounds are `Node.batchRoundsWith` over the model's hash (`Spec/NodeWith.lean`),
answered. -/
def MeaningBatchSumcheckWith (M : HashModel) (n : ℕ) (rd : Reader) : List E → List E → Prop
  | [s0, s1, msgs, running, point], rets =>
      ∃ cv rounds rs final cv', (s0, s1) = digestScalars cv ∧ rounds.length = n ∧
        (∀ r (hr : r < rounds.length),
          LoadHolds rd msgs (2 * r) rounds[r].1 ∧ LoadHolds rd msgs (2 * r + 1) rounds[r].2) ∧
        (Node.batchRoundsWith (m := Option) M.H running rounds).run cv = some ((rs, final), cv') ∧
        ReadsAt rd point rs ∧
        rets = [(digestScalars cv').1, (digestScalars cv').2, final]
  | _, _ => False

/-- At the deployed model it is `MeaningBatchSumcheck`. -/
theorem meaningBatchSumcheckWith_deployed (n : ℕ) (rd : Reader) (args rets : List E) :
    MeaningBatchSumcheckWith HashModel.deployed n rd args rets ↔
      MeaningBatchSumcheck n rd args rets := by
  unfold MeaningBatchSumcheckWith MeaningBatchSumcheck
  split
  · have hH : HashModel.deployed.H = someBlake := rfl
    simp only [hH, batchRoundsWith_some, Option.some.injEq]
  · exact Iff.rfl

/-- One round of `Node.batchRoundsWith` over a hash model, from the answered hashes of its two
absorptions and its squeeze. -/
theorem batchRoundsWith_cons_run {M : HashModel} {c d1 d2 d3 : Digest} {claim g1 gInf : E}
    {rest : List (E × E)}
    (h1 : obsCvM M c g1 = some d1) (h2 : obsCvM M d1 gInf = some d2) (h3 : sqCvM M d2 = some d3) :
    (Node.batchRoundsWith (m := Option) M.H claim ((g1, gInf) :: rest)).run c =
      ((Node.batchRoundsWith (m := Option) M.H
        ((gInf * challengeOf d3 + (claim + g1 + g1 + gInf)) * challengeOf d3 + (claim + g1))
          rest).run d3).map fun p ↦ ((challengeOf d3 :: p.1.1, p.1.2), p.2) := by
  unfold obsCvM at h1 h2
  unfold sqCvM at h3
  simp only [Node.batchRoundsWith, Node.observeWith, Node.squeezeWith, StateT.run_bind,
    StateT.run_get, StateT.run_set, StateT.run_monadLift, monadLift_self, StateT.run_pure,
    Option.pure_def, Option.bind_eq_bind, Option.bind_some, h1, h2, h3]
  cases StateT.run (Node.batchRoundsWith M.H _ rest) d3 <;> rfl

/-- **`batch_sumcheck` is sound under a hash model**, at every `n ≥ 1`, for a compiled function
whose body is `bsBody n`: the rounds' words are `Node.batchRoundsWith` over the model's hash,
every hash answered. -/
theorem batch_sumcheck_model {M : HashModel} {name : String} {f : Fn} (n : ℕ) (hn : 0 < n)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [.n 0, .n 1, .n 2, .n 3, .n 4])
    (hbody : f.body = bsBody n) (rd : Reader) (args rets : List E)
    (h : coreProgram.RelB M.sem rd name args rets) : MeaningBatchSumcheckWith M n rd args rets := by
  rw [relB_iff_sem hfind, hbody, hparams, bsBody] at h
  simp only [holdsListB_append, holdsListB_flatten_range n bsBlock (fun _ => rfl),
    Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil] at h
  obtain ⟨σ, hp, h5, h6, hblk, t1, t2, t3, hret⟩ := h
  subst hp
  have hblk : ∀ r < n, BsOkB M rd σ r := fun r hr ↦ holdsB_bsBlock r _ (hblk r hr)
  set rounds := (List.range n).map fun r => (σ (.n ((7 + 51 * r))), σ (.n ((7 + 51 * r) + 15)))
  set rs := (List.range n).map fun r => σ (.n ((7 + 51 * r) + 43))
  have hlen : rounds.length = n := by simp [rounds]
  have hrlen : rs.length = n := by simp [rs]
  have hdrop : ∀ i < n, rounds.drop i =
      (σ (.n ((7 + 51 * i))), σ (.n ((7 + 51 * i) + 15))) :: rounds.drop (i + 1) := fun i hi ↦ by
    rw [List.drop_eq_getElem_cons (by omega)]
    simp [rounds]
  have hdrop' : ∀ i < n, rs.drop i = σ (.n ((7 + 51 * i) + 43)) :: rs.drop (i + 1) := fun i hi ↦ by
    rw [List.drop_eq_getElem_cons (by omega)]
    simp [rs]
  have key : ∀ j i, i + j = n → ∀ c, (σ (.n (bsS i)), σ (.n (bsS i + 1))) = digestScalars c →
      ∃ c', (σ (.n (bsS n)), σ (.n (bsS n + 1))) = digestScalars c' ∧
        (Node.batchRoundsWith (m := Option) M.H (σ (.n (bsC i))) (rounds.drop i)).run c =
          some ((rs.drop i, σ (.n (bsC n))), c') := by
    intro j
    induction j with
    | zero =>
      intro i hi c hc
      obtain rfl : i = n := by omega
      refine ⟨c, hc, ?_⟩
      rw [List.drop_of_length_le (by omega), List.drop_of_length_le (by omega)]
      rfl
    | succ j ih =>
      intro i hi c hc
      obtain ⟨⟨-, cvA, dA, hA, hdA, eA⟩, ⟨-, cvB, dB, hB, hdB, eB⟩, ⟨cvC, dC, hC, hdC, eC⟩, -, a44,
        a45, a46, a47, a48, a49, a50⟩ := hblk i (by omega)
      obtain rfl : cvA = c := digestScalars_injective (hA.symm.trans hc)
      have f13 : σ (.n ((7 + 51 * i) + 13)) = (digestScalars dA).1 := by
        rw [show (7 + 51 * i) + 13 = (7 + 51 * i) + 1 + 12 by omega]; exact eA 12 (by omega) (by omega)
      have f14 : σ (.n ((7 + 51 * i) + 14)) = (digestScalars dA).2 := by
        rw [show (7 + 51 * i) + 14 = (7 + 51 * i) + 1 + 13 by omega]; exact eA 13 (by omega) (by omega)
      obtain rfl : cvB = dA := digestScalars_injective (by rw [← hB, f13, f14])
      have f28 : σ (.n ((7 + 51 * i) + 28)) = (digestScalars dB).1 := by
        rw [show (7 + 51 * i) + 28 = (7 + 51 * i) + 15 + 1 + 12 by omega]
        exact eB 12 (by omega) (by omega)
      have f29 : σ (.n ((7 + 51 * i) + 29)) = (digestScalars dB).2 := by
        rw [show (7 + 51 * i) + 29 = (7 + 51 * i) + 15 + 1 + 13 by omega]
        exact eB 13 (by omega) (by omega)
      have s35 : σ (.n ((7 + 51 * i) + 35)) = (digestScalars dC).1 := by
        rw [show (7 + 51 * i) + 35 = (7 + 51 * i) + 30 + 5 by omega]; exact eC 5 (by omega)
      have s36 : σ (.n ((7 + 51 * i) + 36)) = (digestScalars dC).2 := by
        rw [show (7 + 51 * i) + 36 = (7 + 51 * i) + 30 + 6 by omega]; exact eC 6 (by omega)
      have s43 : σ (.n ((7 + 51 * i) + 43)) = challengeOf dC := by
        rw [show (7 + 51 * i) + 43 = (7 + 51 * i) + 30 + 13 by omega]; exact eC 13 (by omega)
      have hS : (σ (.n (bsS (i + 1))), σ (.n (bsS (i + 1) + 1))) = digestScalars dC := by
        rw [show bsS (i + 1) = (7 + 51 * i) + 35 by simp only [bsS]; omega,
          show (7 + 51 * i) + 35 + 1 = (7 + 51 * i) + 36 by omega, s35, s36]
      obtain ⟨c', hc', hrun⟩ := ih (i + 1) (by omega) dC hS
      obtain rfl : cvC = dB := digestScalars_injective (by rw [← hC, f28, f29])
      have hcl : σ (.n (bsC (i + 1))) = (σ (.n ((7 + 51 * i) + 15)) * challengeOf dC +
          (σ (.n (bsC i)) + σ (.n (7 + 51 * i)) + σ (.n (7 + 51 * i)) +
            σ (.n ((7 + 51 * i) + 15)))) * challengeOf dC + (σ (.n (bsC i)) + σ (.n (7 + 51 * i))) := by
        rw [show bsC (i + 1) = (7 + 51 * i) + 50 by simp only [bsC]; omega, a50, a49, a48, a47,
          a46, a45, a44, s43]
      refine ⟨c', hc', ?_⟩
      rw [hdrop i (by omega), hdrop' i (by omega), batchRoundsWith_cons_run hdA hdB hdC, ← hcl,
        hrun, s43]
      rfl
  obtain ⟨cv, -, hcv, -⟩ := (hblk 0 hn).1.2
  obtain ⟨cv', hcv', hrun⟩ := key n 0 (by omega) cv hcv
  simp only [List.drop_zero] at hrun
  have hcv0 : (σ (.n 0), σ (.n 1)) = digestScalars cv := by rw [← h5, ← h6]; exact hcv
  refine ⟨cv, rounds, rs, _, cv', hcv0, hlen, fun r hr => ?_, hrun, ?_, ?_⟩
  · have hr' : r < n := hlen ▸ hr
    have hgr : rounds[r] = (σ (.n (7 + 51 * r)), σ (.n ((7 + 51 * r) + 15))) := by
      simp [rounds]
    rw [hgr]
    exact ⟨(hblk r hr').1.1, (hblk r hr').2.1.1⟩
  · intro k hk
    simp only [rs, List.length_map, List.length_range] at hk
    simp only [rs, List.getElem_map, List.getElem_range]
    exact (hblk k hk).2.2.2.1
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [bsS] at hcv'
    rw [← hret, t1, t2, t3]
    rw [show 51 * (m + 1) - 9 = 42 + 51 * m by omega, show 51 * (m + 1) - 8 = 42 + 51 * m + 1 by omega,
      show 51 * (m + 1) + 6 = 57 + 51 * m by omega,
      show σ (.n (42 + 51 * m)) = (digestScalars cv').1 from congrArg Prod.fst hcv',
      show σ (.n (42 + 51 * m + 1)) = (digestScalars cv').2 from congrArg Prod.snd hcv']
    rfl

/-- **`batch_sumcheck` at every `n ≥ 1`**, for a compiled function whose body is `bsBody n`. -/
theorem batch_sumcheck_iff {name : String} {f : Fn} (n : ℕ) (hn : 0 < n)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [.n 0, .n 1, .n 2, .n 3, .n 4])
    (hbody : f.body = bsBody n) (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd name args rets ↔ MeaningBatchSumcheck n rd args rets := by
  constructor
  · intro h
    rw [← relB_deployed] at h
    exact (meaningBatchSumcheckWith_deployed n rd args rets).mp
      (batch_sumcheck_model (M := HashModel.deployed) n hn hfind hparams hbody rd args rets h)
  rw [rel_iff_sem hfind, hbody, hparams, bsBody]
  simp only [holdsList_append, holdsList_range_flatten n bsBlock (fun _ => rfl), holds_bsBlock,
    Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]
  · intro hm
    obtain ⟨s0, s1, msgs, running, point, rfl⟩ : ∃ s0 s1 msgs running point,
        args = [s0, s1, msgs, running, point] := by
      match args, hm with
      | [a, b, c, d, e], _ => exact ⟨a, b, c, d, e, rfl⟩
    obtain ⟨cv, rounds, rs, final, cv', hcv, hlen, hmsg, hrun, hpt, hret⟩ := hm
    rw [batchRounds_run, bsRun_eq] at hrun
    have e1 := congrArg (fun p : (List E × E) × Digest => p.1.1) hrun
    have e2 := congrArg (fun p : (List E × E) × Digest => p.1.2) hrun
    have e3 := congrArg (fun p : (List E × E) × Digest => p.2) hrun
    dsimp only at e1 e2 e3
    subst e1 e2 e3
    subst hret
    set base := Val.ofArgs [s0, s1, msgs, running, point]
    set st := bsSt rounds running cv
    set τ := setl (bsSig base rounds running cv n) (7 + 51 * n)
      [(digestScalars (st n).2).1, (digestScalars (st n).2).2, (st n).1]
    have hτ : ∀ k < 7 + 51 * n, τ (.n k) = bsSig base rounds running cv n (.n k) := fun k hk => by
      simp only [τ, setl]; rw [set_n_lt hk]
    have hbase : ∀ k < 5, τ (.n k) = base (.n k) := fun k hk => by
      rw [hτ k (by omega), bsSig_base _ _ _ _ _ _ hk]
    have hblk : ∀ r < n, ∀ k < 51, τ (.n ((7 + 51 * r) + k)) = bsVals (st r) (rounds.getD r (0, 0)) k :=
      fun r hr k hk => by rw [hτ _ (by omega), bsSig_blk _ _ _ _ _ _ _ hr hk]
    have hstart : ∀ r ≤ n, (τ (.n (bsS r)), τ (.n (bsS r + 1))) = digestScalars (st r).2 ∧
        τ (.n (bsC r)) = (st r).1 := fun r hr => by
      have hs : bsS r + 1 < 7 + 51 * n := by cases r <;> simp only [bsS] <;> omega
      have hc : bsC r < 7 + 51 * n := by cases r <;> simp only [bsC] <;> omega
      rw [hτ _ (by omega), hτ _ hs, hτ _ hc]
      exact bsSig_start base rounds running cv n r hr rfl
    have hl : rounds.length = n := hlen
    refine ⟨τ, ?_, ?_, ?_, ?blk, ?tail⟩
    · simp only [hbase 0 (by omega), hbase 1 (by omega), hbase 2 (by omega), hbase 3 (by omega),
        hbase 4 (by omega)]
      rfl
    · rw [hbase 0 (by omega), hτ 5 (by omega), bsSig_lt base rounds running cv n 0 5 (by omega)
        (by omega)]
      simp only [bsSig, setl, List.length_cons, List.length_nil]
      rw [set_n_in (by omega) (by omega)]
      exact (congrArg Prod.fst hcv).symm
    · rw [hbase 1 (by omega), hτ 6 (by omega), bsSig_lt base rounds running cv n 0 6 (by omega)
        (by omega)]
      simp only [bsSig, setl, List.length_cons, List.length_nil]
      rw [set_n_in (by omega) (by omega)]
      exact (congrArg Prod.snd hcv).symm
    case blk =>
      intro r hr
      have hr' : r < rounds.length := hl ▸ hr
      set g := rounds.getD r (0, 0)
      have hgr : g = rounds[r] := by simp [g, List.getD_eq_getElem?_getD, hr']
      have v : ∀ k < 51, τ (.n ((7 + 51 * r) + k)) = bsVals (st r) g k := hblk r hr
      have v0 : τ (.n (7 + 51 * r)) = g.1 := v 0 (by omega)
      have v15 : τ (.n ((7 + 51 * r) + 15)) = g.2 := v 15 (by omega)
      obtain ⟨hs, hc⟩ := hstart r (by omega)
      have h2 : τ (.n 2) = msgs := hbase 2 (by omega)
      have h4 : τ (.n 4) = point := hbase 4 (by omega)
      have lv : ∀ k, 44 ≤ k → k < 51 → τ (.n ((7 + 51 * r) + k)) =
          [(st r).1 + g.1, (st r).1 + g.1 + g.1, (st r).1 + g.1 + g.1 + g.2,
            g.2 * challengeOf (sqCv (obsCv (obsCv (st r).2 g.1) g.2)),
            g.2 * challengeOf (sqCv (obsCv (obsCv (st r).2 g.1) g.2)) + ((st r).1 + g.1 + g.1 + g.2),
            (g.2 * challengeOf (sqCv (obsCv (obsCv (st r).2 g.1) g.2)) +
              ((st r).1 + g.1 + g.1 + g.2)) * challengeOf (sqCv (obsCv (obsCv (st r).2 g.1) g.2)),
            (g.2 * challengeOf (sqCv (obsCv (obsCv (st r).2 g.1) g.2)) +
              ((st r).1 + g.1 + g.1 + g.2)) * challengeOf (sqCv (obsCv (obsCv (st r).2 g.1) g.2)) +
              ((st r).1 + g.1)].getD (k - 44) 0 := fun k hk1 hk2 => by
        rw [v k hk2]
        simp only [bsVals]
        rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega),
          ite_neg' (by omega)]
      have v43 : τ (.n ((7 + 51 * r) + 43)) = challengeOf (sqCv (obsCv (obsCv (st r).2 g.1) g.2)) := by
        rw [show (7 + 51 * r) + 43 = (7 + 51 * r) + (30 + 13) by omega, v _ (by omega), bs_sq _ _ _ (by omega)]
        rfl
      refine ⟨⟨?_, (st r).2, hs, fun k hk1 hk2 => ?_⟩, ⟨?_, obsCv (st r).2 g.1, ?_, fun k hk1 hk2 => ?_⟩,
        ⟨obsCv (obsCv (st r).2 g.1) g.2, ?_, fun k hk => ?_⟩, ?_, ?_⟩
      · rw [h2, v0, hgr]; exact (hmsg r hr').1
      · rw [show (7 + 51 * r) + 1 + k = (7 + 51 * r) + (1 + k) by omega, v _ (by omega),
          bs_fs1 _ _ _ hk1 hk2, v0]
      · rw [h2, v15, hgr]; exact (hmsg r hr').2
      · rw [v 13 (by omega), v 14 (by omega)]
        simp only [bsVals]
        rw [ite_neg' (by omega), ite_pos' (by omega), ite_neg' (by omega), ite_pos' (by omega)]
        show ((digestScalars (absorbCv (st r).2 g.1 1)).1, (digestScalars (absorbCv (st r).2 g.1 1)).2) = _
        rw [Prod.mk.eta]; rfl
      · rw [show (7 + 51 * r) + 15 + 1 + k = (7 + 51 * r) + (15 + 1 + k) by omega, v _ (by omega),
          bs_fs2 _ _ _ hk1 hk2, v15]
      · rw [v 28 (by omega), v 29 (by omega)]
        simp only [bsVals]
        rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_pos' (by omega),
          ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_pos' (by omega)]
        show ((digestScalars (absorbCv (obsCv (st r).2 g.1) g.2 1)).1,
          (digestScalars (absorbCv (obsCv (st r).2 g.1) g.2 1)).2) = _
        rw [Prod.mk.eta]; rfl
      · rw [show (7 + 51 * r) + 30 + k = (7 + 51 * r) + (30 + k) by omega, v _ (by omega),
          bs_sq _ _ _ hk]
      · rw [h4, v43]
        have := hpt r (by simpa [hl] using hr)
        simp only [List.getElem_map, List.getElem_range] at this
        exact this
      · rw [lv 44 (by omega) (by omega), lv 45 (by omega) (by omega), lv 46 (by omega) (by omega),
          lv 47 (by omega) (by omega), lv 48 (by omega) (by omega), lv 49 (by omega) (by omega),
          lv 50 (by omega) (by omega), hc, v0, v15, v43]
        simp only [Nat.sub_self, List.getD_cons_zero, List.getD_cons_succ, Nat.reduceSub]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial
    case tail =>
      have lt : ∀ j < 3, τ (.n (7 + 51 * n + j)) =
          [(digestScalars (st n).2).1, (digestScalars (st n).2).2, (st n).1].getD j 0 := fun j hj => by
        simp only [τ, setl]
        rw [set_n_in (by omega) (by simp only [List.length_cons, List.length_nil]; omega),
          Nat.add_sub_cancel_left]
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      obtain ⟨hs, hc⟩ := hstart (m + 1) le_rfl
      simp only [bsS, bsC] at hs hc
      have l0 := lt 0 (by omega)
      have l1 := lt 1 (by omega)
      have l2 := lt 2 (by omega)
      simp only [Nat.add_zero, List.getD_cons_zero, List.getD_cons_succ,
        show 7 + 51 * (m + 1) + 1 = 8 + 51 * (m + 1) by omega,
        show 7 + 51 * (m + 1) + 2 = 9 + 51 * (m + 1) by omega] at l0 l1 l2
      rw [show 51 * (m + 1) - 9 = 42 + 51 * m by omega, show 51 * (m + 1) - 8 = 42 + 51 * m + 1 by omega,
        show 51 * (m + 1) + 6 = 57 + 51 * m by omega, l0, l1, l2, hc, hl,
        show τ (.n (42 + 51 * m)) = (digestScalars (st (m + 1)).2).1 from congrArg Prod.fst hs,
        show τ (.n (42 + 51 * m + 1)) = (digestScalars (st (m + 1)).2).2 from congrArg Prod.snd hs]
      exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## The specializations -/

set_option maxRecDepth 100000 in
theorem batch_sumcheck_L22_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "batch_sumcheck__L22" args rets ↔ MeaningBatchSumcheck 22 rd args rets :=
  batch_sumcheck_iff 22 (by decide) (Program.find?_of_indexOf? (j := 568) (by decide +kernel)
    rfl) rfl core568_body
    rd args rets

set_option maxRecDepth 100000 in
theorem batch_sumcheck_L28_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "batch_sumcheck__L28" args rets ↔ MeaningBatchSumcheck 28 rd args rets :=
  batch_sumcheck_iff 28 (by decide) (Program.find?_of_indexOf? (j := 571) (by decide +kernel)
    rfl) rfl core571_body
    rd args rets

set_option maxRecDepth 100000 in
/-- `batch_sumcheck__L22` under a hash model. -/
theorem batch_sumcheck_L22_model {M : HashModel} (rd : Reader) (args rets : List E)
    (h : coreProgram.RelB M.sem rd "batch_sumcheck__L22" args rets) :
    MeaningBatchSumcheckWith M 22 rd args rets :=
  batch_sumcheck_model 22 (by decide) (Program.find?_of_indexOf? (j := 568) (by decide +kernel)
    rfl) rfl core568_body rd args rets h

set_option maxRecDepth 100000 in
/-- `batch_sumcheck__L28` under a hash model. -/
theorem batch_sumcheck_L28_model {M : HashModel} (rd : Reader) (args rets : List E)
    (h : coreProgram.RelB M.sem rd "batch_sumcheck__L28" args rets) :
    MeaningBatchSumcheckWith M 28 rd args rets :=
  batch_sumcheck_model 28 (by decide) (Program.find?_of_indexOf? (j := 571) (by decide +kernel)
    rfl) rfl core571_body rd args rets h

end
end LeanVM.Guest.B1
