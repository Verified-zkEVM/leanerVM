/-
  LeanVM.Guest.B1.Comp.Sumcheck

  `batch_sumcheck` over a completeness model.
-/

module

public import LeanVM.Guest.B1.Comp.Opening
public import LeanVM.Guest.B1.Sumcheck

/-!
# `batch_sumcheck` over a completeness model

The backward half of `batch_sumcheck_iff` over a `CompModel`: from the meaning over the model's
answers (`MeaningBatchSumcheckComp CM n`: `batchRoundsWith CM.H` answers every round), the run is
taken apart round by round (`batchRoundsWith_inv_cons`, `batchRoundsWith_steps`) into the answered
absorbs and squeezes, whose states (`bsStH`, the deployed `bsSt` at BLAKE2s) are the honest values
(`bsValsC`), each block's row the model's (`holdsB_bsBlock_comp`). `batch_sumcheck_comp` and its
specializations `batch_sumcheck_L22_comp`, `batch_sumcheck_L28_comp`; at `CompModel.deployed` the
deployed backward direction (`batch_sumcheck_of_comp`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.E2E.Complete LeanVM.Node

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## The rounds over an answered hash -/

/-- The absorb of a word, read off an answered hash (`default` where it does not answer). -/
def obsH (H : Bytes → Option Digest) (cv : Digest) (x : E) : Digest :=
  (H (digestBytes cv ++ blockOf x 1)).getD default

/-- A squeeze, read off an answered hash. -/
def sqH (H : Bytes → Option Digest) (cv : Digest) : Digest :=
  (H (digestBytes cv ++ blockOf 0 2)).getD default

/-- One round over an answered hash (`bsStep`). -/
def bsStepH (H : Bytes → Option Digest) (st : E × Digest) (g : E × E) : E × Digest :=
  let cv := sqH H (obsH H (obsH H st.2 g.1) g.2)
  let r := challengeOf cv
  let g0 := st.1 + g.1
  ((g.2 * r + (g0 + g.1 + g.2)) * r + g0, cv)

/-- The claim and state after the first `i` rounds over an answered hash (`bsSt`). -/
def bsStH (H : Bytes → Option Digest) (rounds : List (E × E)) (claim : E) (cv : Digest) :
    ℕ → E × Digest
  | 0 => (claim, cv)
  | i + 1 => bsStepH H (bsStH H rounds claim cv i) (rounds.getD i (0, 0))

theorem bsStH_cons (H : Bytes → Option Digest) (g : E × E) (rest : List (E × E)) (claim : E)
    (cv : Digest) : ∀ i, bsStH H (g :: rest) claim cv (i + 1) =
      bsStH H rest (bsStepH H (claim, cv) g).1 (bsStepH H (claim, cv) g).2 i
  | 0 => rfl
  | i + 1 => by
    rw [bsStH, bsStH_cons H g rest claim cv i, List.getD_cons_succ]
    rfl

theorem bsStH_deployed (rounds : List (E × E)) (claim : E) (cv : Digest) :
    ∀ i, bsStH (fun x ↦ some (blake2sBytes x)) rounds claim cv i = bsSt rounds claim cv i
  | 0 => rfl
  | i + 1 => by
    rw [bsStH, bsSt, bsStH_deployed rounds claim cv i]
    rfl

/-- One round of an answered `batchRoundsWith`, taken apart. -/
theorem batchRoundsWith_inv_cons {H : Bytes → Option Digest} {claim g1 gInf : E}
    {rest : List (E × E)} {cv : Digest} {out : (List E × E) × Digest}
    (h : (batchRoundsWith (m := Option) H claim ((g1, gInf) :: rest)).run cv = some out) :
    ∃ c1 c2 c3, H (digestBytes cv ++ blockOf g1 1) = some c1 ∧
      H (digestBytes c1 ++ blockOf gInf 1) = some c2 ∧ H (digestBytes c2 ++ blockOf 0 2) = some c3 ∧
      ∃ out', (batchRoundsWith (m := Option) H
          ((gInf * challengeOf c3 + (claim + g1 + g1 + gInf)) * challengeOf c3 + (claim + g1))
            rest).run c3 = some out' ∧
        out = ((challengeOf c3 :: out'.1.1, out'.1.2), out'.2) := by
  cases e1 : H (digestBytes cv ++ blockOf g1 1) with
  | none => simp [batchRoundsWith, observeWith, squeezeWith, e1] at h
  | some c1 =>
    cases e2 : H (digestBytes c1 ++ blockOf gInf 1) with
    | none => simp [batchRoundsWith, observeWith, squeezeWith, e1, e2] at h
    | some c2 =>
      cases e3 : H (digestBytes c2 ++ blockOf 0 2) with
      | none => simp [batchRoundsWith, observeWith, squeezeWith, e1, e2, e3] at h
      | some c3 =>
        refine ⟨c1, c2, c3, rfl, by first | rfl | exact e2,
          by first | rfl | exact e3, ?_⟩
        cases e4 : (batchRoundsWith (m := Option) H
          ((gInf * challengeOf c3 + (claim + g1 + g1 + gInf)) * challengeOf c3 + (claim + g1))
            rest).run c3 with
        | none => simp [batchRoundsWith, observeWith, squeezeWith, e1, e2, e3, e4] at h
        | some o =>
          refine ⟨o, rfl, ?_⟩
          simp [batchRoundsWith, observeWith, squeezeWith, e1, e2, e3, e4] at h
          exact h.symm

/-- **An answered `batchRoundsWith`, round by round**: every round's two absorbs and squeeze
answered, from the state after the rounds before it (`bsStH`); the challenges, the final claim and
state those of `bsStH`. -/
theorem batchRoundsWith_steps {H : Bytes → Option Digest} : ∀ {rounds : List (E × E)}
    {claim : E} {cv : Digest} {rs : List E} {final : E} {cv' : Digest},
    (batchRoundsWith (m := Option) H claim rounds).run cv = some ((rs, final), cv') →
      (∀ r < rounds.length,
        H (digestBytes (bsStH H rounds claim cv r).2 ++ blockOf (rounds.getD r (0, 0)).1 1) =
          some (obsH H (bsStH H rounds claim cv r).2 (rounds.getD r (0, 0)).1) ∧
        H (digestBytes (obsH H (bsStH H rounds claim cv r).2 (rounds.getD r (0, 0)).1) ++
            blockOf (rounds.getD r (0, 0)).2 1) =
          some (obsH H (obsH H (bsStH H rounds claim cv r).2 (rounds.getD r (0, 0)).1)
            (rounds.getD r (0, 0)).2) ∧
        H (digestBytes (obsH H (obsH H (bsStH H rounds claim cv r).2 (rounds.getD r (0, 0)).1)
            (rounds.getD r (0, 0)).2) ++ blockOf 0 2) =
          some (bsStH H rounds claim cv (r + 1)).2) ∧
      rs = (List.range rounds.length).map (fun j ↦ challengeOf (bsStH H rounds claim cv (j + 1)).2) ∧
      final = (bsStH H rounds claim cv rounds.length).1 ∧
      cv' = (bsStH H rounds claim cv rounds.length).2
  | [], claim, cv, rs, final, cv', h => by
    simp only [batchRoundsWith, StateT.run_pure] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    exact ⟨fun r hr => absurd hr (Nat.not_lt_zero _), rfl, rfl, rfl⟩
  | (g1, gInf) :: rest, claim, cv, rs, final, cv', h => by
    obtain ⟨c1, c2, c3, e1, e2, e3, out', e4, hout⟩ := batchRoundsWith_inv_cons h
    obtain ⟨⟨rs', final'⟩, cv''⟩ := out'
    simp only [Prod.mk.injEq] at hout
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hout
    have hs1 : obsH H cv g1 = c1 := by simp [obsH, e1]
    have hs2 : obsH H c1 gInf = c2 := by simp [obsH, e2]
    have hs3 : sqH H c2 = c3 := by simp [sqH, e3]
    have hst : bsStepH H (claim, cv) (g1, gInf) =
        ((gInf * challengeOf c3 + (claim + g1 + g1 + gInf)) * challengeOf c3 + (claim + g1), c3) := by
      simp only [bsStepH, hs1, hs2, hs3]
    obtain ⟨hR, hrs, hfin, hcv⟩ := batchRoundsWith_steps e4
    have hc : ∀ i, bsStH H ((g1, gInf) :: rest) claim cv (i + 1) =
        bsStH H rest ((gInf * challengeOf c3 + (claim + g1 + g1 + gInf)) * challengeOf c3 +
          (claim + g1)) c3 i := fun i => by
      rw [bsStH_cons, hst]
    refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
    · rcases r with _ | r
      · show H (digestBytes cv ++ blockOf g1 1) = some (obsH H cv g1) ∧
          H (digestBytes (obsH H cv g1) ++ blockOf gInf 1) = some (obsH H (obsH H cv g1) gInf) ∧
          H (digestBytes (obsH H (obsH H cv g1) gInf) ++ blockOf 0 2) =
            some (bsStH H ((g1, gInf) :: rest) claim cv (0 + 1)).2
        rw [hc 0, hs1, hs2]
        exact ⟨e1, e2, e3⟩
      · rw [hc r, hc (r + 1), List.getD_cons_succ]
        exact hR r (by simp at hr; omega)
    · simp only [hrs, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
        List.cons.injEq]
      refine ⟨by rw [hc 0]; rfl, List.map_congr_left fun j _ => ?_⟩
      show challengeOf (bsStH H rest _ c3 (j + 1)).2 =
        challengeOf (bsStH H ((g1, gInf) :: rest) claim cv (j + 1 + 1)).2
      rw [hc (j + 1)]
    · rw [List.length_cons, hc, hfin]
    · rw [List.length_cons, hc, hcv]

/-! ## The honest valuation -/

/-- Round `r`'s 51 values over an answered hash (`bsVals`). -/
def bsValsC (H : Bytes → Option Digest) (st : E × Digest) (g : E × E) (k : ℕ) : E :=
  let cvB := obsH H st.2 g.1
  let cvC := obsH H cvB g.2
  let rv := challengeOf (sqH H cvC)
  let g0 := st.1 + g.1
  if k = 0 then g.1 else if k < 15 then fsValsD g.1 cvB 1 (k - 1)
  else if k = 15 then g.2 else if k < 30 then fsValsD g.2 cvC 1 (k - 16)
  else if k < 44 then sqValsD (sqH H cvC) (k - 30)
  else [g0, g0 + g.1, g0 + g.1 + g.2, g.2 * rv, g.2 * rv + (g0 + g.1 + g.2),
    (g.2 * rv + (g0 + g.1 + g.2)) * rv, (g.2 * rv + (g0 + g.1 + g.2)) * rv + g0].getD (k - 44) 0

/-- The honest valuation after `i` rounds over an answered hash (`bsSig`). -/
def bsSigC (H : Bytes → Option Digest) (base : Val) (rounds : List (E × E)) (claim : E)
    (cv : Digest) : ℕ → Val
  | 0 => setl base 5 [(digestScalars cv).1, (digestScalars cv).2]
  | i + 1 => setv (bsSigC H base rounds claim cv i) ((7 + 51 * i)) 51
      (bsValsC H (bsStH H rounds claim cv i) (rounds.getD i (0, 0)))

section
variable (H : Bytes → Option Digest)

theorem bsSigC_lt (base : Val) (rounds : List (E × E)) (claim : E) (cv : Digest) :
    ∀ (m i k : ℕ), i ≤ m → k < (7 + 51 * i) →
      bsSigC H base rounds claim cv m (.n k) = bsSigC H base rounds claim cv i (.n k)
  | 0, i, k, h, _ => by rw [show i = 0 by omega]
  | m + 1, i, k, h, hk => by
    rcases Nat.lt_or_ge i (m + 1) with hi | hi
    · rw [bsSigC, set_n_lt (by omega)]
      exact bsSigC_lt base rounds claim cv m i k (by omega) hk
    · rw [show i = m + 1 by omega]

theorem bsSigC_blk (base : Val) (rounds : List (E × E)) (claim : E) (cv : Digest) (m r k : ℕ)
    (hr : r < m) (hk : k < 51) :
    bsSigC H base rounds claim cv m (.n ((7 + 51 * r) + k)) =
      bsValsC H (bsStH H rounds claim cv r) (rounds.getD r (0, 0)) k := by
  rw [bsSigC_lt H base rounds claim cv m (r + 1) _ hr (by omega), bsSigC,
    set_n_in (by omega) (by omega), Nat.add_sub_cancel_left]

theorem bsSigC_base (base : Val) (rounds : List (E × E)) (claim : E) (cv : Digest) (m k : ℕ)
    (hk : k < 5) : bsSigC H base rounds claim cv m (.n k) = base (.n k) := by
  rw [bsSigC_lt H base rounds claim cv m 0 k (by omega) (by omega), bsSigC, setl, set_n_lt hk]

theorem bsSigC_start (base : Val) (rounds : List (E × E)) (claim : E) (cv : Digest) (m r : ℕ)
    (hr : r ≤ m) (h3 : base (.n 3) = claim) :
    (bsSigC H base rounds claim cv m (.n (bsS r)), bsSigC H base rounds claim cv m (.n (bsS r + 1))) =
        digestScalars (bsStH H rounds claim cv r).2 ∧
      bsSigC H base rounds claim cv m (.n (bsC r)) = (bsStH H rounds claim cv r).1 := by
  cases r with
  | zero =>
    rw [bsSigC_lt H base rounds claim cv m 0 _ (by omega) (by simp [bsS]),
      bsSigC_lt H base rounds claim cv m 0 _ (by omega) (by simp [bsS]),
      bsSigC_lt H base rounds claim cv m 0 _ (by omega) (by simp [bsC])]
    simp only [bsSigC, setl, bsS, bsC, List.length_cons, List.length_nil]
    rw [set_n_in (by omega) (by omega), set_n_in (by omega) (by omega), set_n_lt (by omega), h3]
    exact ⟨rfl, rfl⟩
  | succ r =>
    have e35 := bsSigC_blk H base rounds claim cv m r 35 (by omega) (by omega)
    have e36 := bsSigC_blk H base rounds claim cv m r 36 (by omega) (by omega)
    have e50 := bsSigC_blk H base rounds claim cv m r 50 (by omega) (by omega)
    rw [show bsS (r + 1) = (7 + 51 * r) + 35 by simp [bsS]; omega,
      show (7 + 51 * r) + 35 + 1 = (7 + 51 * r) + 36 by omega,
      show bsC (r + 1) = (7 + 51 * r) + 50 by simp [bsC]; omega, e35, e36, e50]
    refine ⟨?_, rfl⟩
    simp only [bsValsC]
    rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega),
      ite_pos' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega),
      ite_neg' (by omega), ite_pos' (by omega)]
    rfl

theorem bsC_fs1 (st : E × Digest) (g : E × E) (k : ℕ) (hk1 : 2 ≤ k) (hk2 : k < 14) :
    bsValsC H st g (1 + k) = fsValsD g.1 (obsH H st.2 g.1) 1 k := by
  simp only [bsValsC]
  rw [ite_neg' (by omega), ite_pos' (by omega), show 1 + k - 1 = k by omega]

theorem bsC_fs2 (st : E × Digest) (g : E × E) (k : ℕ) (hk1 : 2 ≤ k) (hk2 : k < 14) :
    bsValsC H st g (15 + 1 + k) = fsValsD g.2 (obsH H (obsH H st.2 g.1) g.2) 1 k := by
  simp only [bsValsC]
  rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_pos' (by omega),
    show 15 + 1 + k - 16 = k by omega]

theorem bsC_sq (st : E × Digest) (g : E × E) (k : ℕ) (hk : k < 14) :
    bsValsC H st g (30 + k) = sqValsD (sqH H (obsH H (obsH H st.2 g.1) g.2)) k := by
  simp only [bsValsC]
  rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega),
    ite_pos' (by omega), show 30 + k - 30 = k by omega]

end

/-- Round `r` over a completeness model, backward (`holds_bsBlock`). -/
theorem holdsB_bsBlock_comp {CM : CompModel} (r : ℕ) (kret : List E → Prop)
    (h1 : LoadHolds rd (σ (.n 2)) (2 * r) (σ (.n ((7 + 51 * r)))) ∧
      ∃ cv d, (σ (.n (bsS r)), σ (.n (bsS r + 1))) = digestScalars cv ∧
        obsCvM CM.hm cv (σ (.n ((7 + 51 * r)))) = some d ∧
        ∀ k, 2 ≤ k → k < 14 → σ (.n ((7 + 51 * r) + 1 + k)) = fsValsD (σ (.n ((7 + 51 * r)))) d 1 k)
    (h2 : LoadHolds rd (σ (.n 2)) (2 * r + 1) (σ (.n ((7 + 51 * r) + 15))) ∧
      ∃ cv d, (σ (.n ((7 + 51 * r) + 13)), σ (.n ((7 + 51 * r) + 14))) = digestScalars cv ∧
        obsCvM CM.hm cv (σ (.n ((7 + 51 * r) + 15))) = some d ∧
        ∀ k, 2 ≤ k → k < 14 →
          σ (.n ((7 + 51 * r) + 15 + 1 + k)) = fsValsD (σ (.n ((7 + 51 * r) + 15))) d 1 k)
    (h3 : ∃ cv d, (σ (.n ((7 + 51 * r) + 28)), σ (.n ((7 + 51 * r) + 29))) = digestScalars cv ∧
      sqCvM CM.hm cv = some d ∧ ∀ k < 14, σ (.n ((7 + 51 * r) + 30 + k)) = sqValsD d k)
    (h4 : LoadHolds rd (σ (.n 4)) r (σ (.n ((7 + 51 * r) + 43))) ∧
      σ (.n ((7 + 51 * r) + 44)) = σ (.n (bsC r)) + σ (.n ((7 + 51 * r))) ∧
      σ (.n ((7 + 51 * r) + 45)) = σ (.n ((7 + 51 * r) + 44)) + σ (.n ((7 + 51 * r))) ∧
      σ (.n ((7 + 51 * r) + 46)) = σ (.n ((7 + 51 * r) + 45)) + σ (.n ((7 + 51 * r) + 15)) ∧
      σ (.n ((7 + 51 * r) + 47)) = σ (.n ((7 + 51 * r) + 15)) * σ (.n ((7 + 51 * r) + 43)) ∧
      σ (.n ((7 + 51 * r) + 48)) = σ (.n ((7 + 51 * r) + 47)) + σ (.n ((7 + 51 * r) + 46)) ∧
      σ (.n ((7 + 51 * r) + 49)) = σ (.n ((7 + 51 * r) + 48)) * σ (.n ((7 + 51 * r) + 43)) ∧
      σ (.n ((7 + 51 * r) + 50)) = σ (.n ((7 + 51 * r) + 49)) + σ (.n ((7 + 51 * r) + 44))) :
    Stmt.HoldsListB CM.sem C rd σ (bsBlock r) True kret := by
  rw [bsBlock, holdsListB_append, holdsListB_append, holdsListB_append]
  obtain ⟨l1, cv1, d1, a1, b1, c1⟩ := h1
  obtain ⟨l2, cv2, d2, a2, b2, c2⟩ := h2
  obtain ⟨cv3, d3, a3, b3, c3⟩ := h3
  refine holdsB_fsNextT_comp _ _ _ _ _ ⟨⟨l1, cv1, d1, a1, b1, c1⟩,
    holdsB_fsNextT_comp _ _ _ _ _ ⟨⟨l2, cv2, d2, a2, b2, c2⟩,
    holdsB_squeezeT_comp _ _ _ ⟨⟨cv3, d3, a3, b3, c3⟩, ?_⟩⟩⟩
  simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, and_true]
  exact h4

/-! ## The meaning and the theorem -/

/-- **`batch_sumcheck(n)` over a completeness model** (`MeaningBatchSumcheck`, the rounds the model's
answered `batchRoundsWith`). -/
def MeaningBatchSumcheckComp (CM : CompModel) (n : ℕ) (rd : Reader) : List E → List E → Prop
  | [s0, s1, msgs, running, point], rets =>
      ∃ cv rounds rs final cv', (s0, s1) = digestScalars cv ∧ rounds.length = n ∧
        (∀ r (hr : r < rounds.length),
          LoadHolds rd msgs (2 * r) rounds[r].1 ∧ LoadHolds rd msgs (2 * r + 1) rounds[r].2) ∧
        (batchRoundsWith (m := Option) CM.H running rounds).run cv = some ((rs, final), cv') ∧
        ReadsAt rd point rs ∧ rets = [(digestScalars cv').1, (digestScalars cv').2, final]
  | _, _ => False

theorem meaningBatchSumcheckComp_deployed (n : ℕ) (rd : Reader) (args rets : List E) :
    MeaningBatchSumcheckComp CompModel.deployed n rd args rets ↔
      MeaningBatchSumcheck n rd args rets := by
  match args with
  | [s0, s1, msgs, running, point] =>
    simp only [MeaningBatchSumcheckComp, MeaningBatchSumcheck]
    have e : ∀ running rounds cv,
        (batchRoundsWith (m := Option) CompModel.deployed.H running rounds).run cv =
          some ((batchRounds running rounds).run cv) := fun running rounds cv =>
      batchRoundsWith_some running rounds cv
    simp only [e, Option.some.injEq]
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | _ :: _ :: _ :: _ :: _ :: _ :: _ => exact Iff.rfl

/-- **`batch_sumcheck` at every `n ≥ 1` is complete over a completeness model**, for a compiled
function whose body is `bsBody n`. -/
theorem batch_sumcheck_comp {CM : CompModel} {name : String} {f : Fn} (n : ℕ) (hn : 0 < n)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [.n 0, .n 1, .n 2, .n 3, .n 4])
    (hbody : f.body = bsBody n) (rd : Reader) (args rets : List E)
    (hm : MeaningBatchSumcheckComp CM n rd args rets) :
    coreProgram.RelB CM.sem rd name args rets := by
  obtain ⟨s0, s1, msgs, running, point, rfl⟩ : ∃ s0 s1 msgs running point,
      args = [s0, s1, msgs, running, point] := by
    match args, hm with
    | [a, b, c, d, e], _ => exact ⟨a, b, c, d, e, rfl⟩
  obtain ⟨cv, rounds, rs, final, cv', hcv, hlen, hmsg, hrun, hpt, hret⟩ := hm
  obtain ⟨hR, e1, e2, e3⟩ := batchRoundsWith_steps hrun
  subst e1 e2 e3 hret
  rw [relB_iff_sem hfind, hbody, hparams, bsBody]
  simp only [holdsListB_append, range_flatten_holdsListB n bsBlock (fun _ => rfl),
    Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil]
  set H := CM.H
  set base := Val.ofArgs [s0, s1, msgs, running, point]
  set st := bsStH H rounds running cv
  set τ := setl (bsSigC H base rounds running cv n) (7 + 51 * n)
    [(digestScalars (st n).2).1, (digestScalars (st n).2).2, (st n).1]
  have hτ : ∀ k < 7 + 51 * n, τ (.n k) = bsSigC H base rounds running cv n (.n k) := fun k hk => by
    simp only [τ, setl]; rw [set_n_lt hk]
  have hbase : ∀ k < 5, τ (.n k) = base (.n k) := fun k hk => by
    rw [hτ k (by omega), bsSigC_base _ _ _ _ _ _ _ hk]
  have hblk : ∀ r < n, ∀ k < 51, τ (.n ((7 + 51 * r) + k)) =
      bsValsC H (st r) (rounds.getD r (0, 0)) k :=
    fun r hr k hk => by rw [hτ _ (by omega), bsSigC_blk _ _ _ _ _ _ _ _ hr hk]
  have hstart : ∀ r ≤ n, (τ (.n (bsS r)), τ (.n (bsS r + 1))) = digestScalars (st r).2 ∧
      τ (.n (bsC r)) = (st r).1 := fun r hr => by
    have hs : bsS r + 1 < 7 + 51 * n := by cases r <;> simp only [bsS] <;> omega
    have hc : bsC r < 7 + 51 * n := by cases r <;> simp only [bsC] <;> omega
    rw [hτ _ (by omega), hτ _ hs, hτ _ hc]
    exact bsSigC_start H base rounds running cv n r hr rfl
  have hl : rounds.length = n := hlen
  refine ⟨τ, ?_, ?_, ?_, ?blk, ?tail⟩
  · simp only [hbase 0 (by omega), hbase 1 (by omega), hbase 2 (by omega), hbase 3 (by omega),
      hbase 4 (by omega)]
    rfl
  · rw [hbase 0 (by omega), hτ 5 (by omega), bsSigC_lt H base rounds running cv n 0 5 (by omega)
      (by omega)]
    simp only [bsSigC, setl, List.length_cons, List.length_nil]
    rw [set_n_in (by omega) (by omega)]
    exact (congrArg Prod.fst hcv).symm
  · rw [hbase 1 (by omega), hτ 6 (by omega), bsSigC_lt H base rounds running cv n 0 6 (by omega)
      (by omega)]
    simp only [bsSigC, setl, List.length_cons, List.length_nil]
    rw [set_n_in (by omega) (by omega)]
    exact (congrArg Prod.snd hcv).symm
  case blk =>
    intro r hr
    have hr' : r < rounds.length := hl ▸ hr
    set g := rounds.getD r (0, 0)
    have hgr : g = rounds[r] := by simp [g, List.getD_eq_getElem?_getD, hr']
    have v : ∀ k < 51, τ (.n ((7 + 51 * r) + k)) = bsValsC H (st r) g k := hblk r hr
    have v0 : τ (.n (7 + 51 * r)) = g.1 := v 0 (by omega)
    have v15 : τ (.n ((7 + 51 * r) + 15)) = g.2 := v 15 (by omega)
    obtain ⟨hs, hc⟩ := hstart r (by omega)
    obtain ⟨a1, a2, a3⟩ := hR r hr'
    have h2 : τ (.n 2) = msgs := hbase 2 (by omega)
    have h4 : τ (.n 4) = point := hbase 4 (by omega)
    set cvB := obsH H (st r).2 g.1
    set cvC := obsH H cvB g.2
    set rv := challengeOf (sqH H cvC)
    have hst1 : (st (r + 1)).2 = sqH H cvC := rfl
    have lv : ∀ k, 44 ≤ k → k < 51 → τ (.n ((7 + 51 * r) + k)) =
        [(st r).1 + g.1, (st r).1 + g.1 + g.1, (st r).1 + g.1 + g.1 + g.2, g.2 * rv,
          g.2 * rv + ((st r).1 + g.1 + g.1 + g.2), (g.2 * rv + ((st r).1 + g.1 + g.1 + g.2)) * rv,
          (g.2 * rv + ((st r).1 + g.1 + g.1 + g.2)) * rv + ((st r).1 + g.1)].getD (k - 44) 0 :=
      fun k hk1 hk2 => by
        rw [v k hk2]
        simp only [bsValsC]
        rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega),
          ite_neg' (by omega)]
    have v43 : τ (.n ((7 + 51 * r) + 43)) = rv := by
      rw [show (7 + 51 * r) + 43 = (7 + 51 * r) + (30 + 13) by omega, v _ (by omega),
        bsC_sq _ _ _ _ (by omega)]
      rfl
    refine holdsB_bsBlock_comp r _ ⟨?_, (st r).2, cvB, hs, ?_, fun k hk1 hk2 => ?_⟩
      ⟨?_, cvB, cvC, ?_, ?_, fun k hk1 hk2 => ?_⟩
      ⟨cvC, sqH H cvC, ?_, ?_, fun k hk => ?_⟩ ⟨?_, ?_⟩
    · rw [h2, v0, hgr]; exact (hmsg r hr').1
    · rw [v0]; exact a1
    · rw [show (7 + 51 * r) + 1 + k = (7 + 51 * r) + (1 + k) by omega, v _ (by omega),
        bsC_fs1 _ _ _ _ hk1 hk2, v0]
    · rw [h2, v15, hgr]; exact (hmsg r hr').2
    · rw [v 13 (by omega), v 14 (by omega)]
      simp only [bsValsC]
      rw [ite_neg' (by omega), ite_pos' (by omega), ite_neg' (by omega), ite_pos' (by omega)]
      rfl
    · rw [v15]; exact a2
    · rw [show (7 + 51 * r) + 15 + 1 + k = (7 + 51 * r) + (15 + 1 + k) by omega, v _ (by omega),
        bsC_fs2 _ _ _ _ hk1 hk2, v15]
    · rw [v 28 (by omega), v 29 (by omega)]
      simp only [bsValsC]
      rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_pos' (by omega),
        ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_pos' (by omega)]
      rfl
    · rw [← hst1]; exact a3
    · rw [show (7 + 51 * r) + 30 + k = (7 + 51 * r) + (30 + k) by omega, v _ (by omega),
        bsC_sq _ _ _ _ hk]
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
        [(digestScalars (st n).2).1, (digestScalars (st n).2).2, (st n).1].getD j 0 :=
      fun j hj => by
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
    rw [show 51 * (m + 1) - 9 = 42 + 51 * m by omega,
      show 51 * (m + 1) - 8 = 42 + 51 * m + 1 by omega,
      show 51 * (m + 1) + 6 = 57 + 51 * m by omega, l0, l1, l2, hc, hl,
      show τ (.n (42 + 51 * m)) = (digestScalars (st (m + 1)).2).1 from congrArg Prod.fst hs,
      show τ (.n (42 + 51 * m + 1)) = (digestScalars (st (m + 1)).2).2 from congrArg Prod.snd hs]
    exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## The specializations -/

set_option maxRecDepth 100000 in
theorem batch_sumcheck_L22_comp {CM : CompModel} (rd : Reader) (args rets : List E)
    (hm : MeaningBatchSumcheckComp CM 22 rd args rets) :
    coreProgram.RelB CM.sem rd "batch_sumcheck__L22" args rets :=
  batch_sumcheck_comp 22 (by decide) (Program.find?_of_indexOf? (j := 568) (by decide +kernel)
    rfl) rfl core568_body rd args rets hm

set_option maxRecDepth 100000 in
theorem batch_sumcheck_L28_comp {CM : CompModel} (rd : Reader) (args rets : List E)
    (hm : MeaningBatchSumcheckComp CM 28 rd args rets) :
    coreProgram.RelB CM.sem rd "batch_sumcheck__L28" args rets :=
  batch_sumcheck_comp 28 (by decide) (Program.find?_of_indexOf? (j := 571) (by decide +kernel)
    rfl) rfl core571_body rd args rets hm

/-! ## At the deployed model -/

theorem batch_sumcheck_of_comp {name : String} {f : Fn} (n : ℕ) (hn : 0 < n)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [.n 0, .n 1, .n 2, .n 3, .n 4])
    (hbody : f.body = bsBody n) (rd : Reader) (args rets : List E)
    (h : MeaningBatchSumcheck n rd args rets) : coreProgram.Rel rd name args rets := by
  rw [← relB_deployed]
  exact batch_sumcheck_comp (CM := CompModel.deployed) n hn hfind hparams hbody rd args rets
    ((meaningBatchSumcheckComp_deployed n rd args rets).mpr h)

end
end LeanVM.Guest.B1
