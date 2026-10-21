/-
  LeanVM.Guest.B1.Comp.VsInv.Caps

  The opening's caps over a total hash agree when the run's do, on a run over a completeness
  model: `DeferredCaps` over the model.
-/

module

public import LeanVM.Guest.B1.Comp.VsInv.Inv
public import LeanVM.E2E.Complete.Interfaces

/-!
# The opening's caps from the run's, over a completeness model

The caps' hypothesis of the stacked opening over a total hash `Ht`, in T6-det's terms
(`queriesOfWith Ht`, `BatchAgreesWith Ht`, what `CapsAgreeWith` reads): `CapAgreesWith Ht`, at
`blake2sBytes` the deployed `CapAgrees` (`capAgreesWith_blake2s`). Over a completeness model `CM`
the caps' agreement `CapAgreesC CM` holds at some total hash `CM` agrees with; at the deployed
model it is `CapAgrees` (`capAgreesC_deployed`).

`deferredCapsC` (`deferredCaps` over the model): on a run record of the model's answers and a run
within the limits over the model, the deferring verifier's run over `Ht` from the seed's state
passes through every phase to the stacked opening at the run record's batching state, the
opening's words and openings and the committed root alone (each phase's run over the model is
its run over `Ht`, `runsM_runsW`), so the opening's query steps are among the run's
(`mem_queriesOfW_bind_left`, `mem_queriesOfW_bind_right`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.E2E.Complete

@[expose] public section

/-! ## The caps' agreement over a total hash and over a model -/

/-- **The shared caps' hypothesis over a total hash** (`CapAgrees` with `Ht`): at every query step
of `whirOpen μ r target` over `Ht` from the chain state `cv`, the words `xs`, the openings `os`
and the committed root, the step's openings agree wherever they meet over `Ht`. -/
def CapAgreesWith (Ht : Bytes → Digest) (μ r : ℕ) (root cv : Digest) (xs : List E)
    (os : List Opening) (target : E) : Prop :=
  ∀ b ∈ queriesOfWith Ht (whirOpen μ r target) ⟨cv, xs, os, [(root, stackShape μ r)]⟩,
    BatchAgreesWith Ht b.1 b.2

/-- **The caps' agreement over a completeness model**: over some total hash the model agrees
with. -/
def CapAgreesC (CM : CompModel) (μ r : ℕ) (root cv : Digest) (xs : List E) (os : List Opening)
    (target : E) : Prop :=
  ∃ Ht : Bytes → Digest, (∀ x d, CM.H x = some d → d = Ht x) ∧ CapAgreesWith Ht μ r root cv xs os target

theorem batchAgreesWith_blake2s (depth : ℕ) (qs : List (ℕ × Opening)) :
    BatchAgreesWith blake2sBytes depth qs ↔ BatchAgrees depth qs := Iff.rfl

theorem capAgreesWith_blake2s (μ r : ℕ) (root cv : Digest) (xs : List E) (os : List Opening)
    (target : E) : CapAgreesWith blake2sBytes μ r root cv xs os target ↔ CapAgrees μ r root cv xs os target := by
  simp only [CapAgreesWith, CapAgrees, queriesOfWith_blake2s, batchAgreesWith_blake2s]

/-- At the deployed model the caps' agreement is `CapAgrees`. -/
theorem capAgreesC_deployed (μ r : ℕ) (root cv : Digest) (xs : List E) (os : List Opening)
    (target : E) : CapAgreesC CompModel.deployed μ r root cv xs os target ↔ CapAgrees μ r root cv xs os target := by
  constructor
  · rintro ⟨Ht, hag, h⟩
    obtain rfl : Ht = blake2sBytes := funext fun x => (hag x _ rfl).symm
    exact (capAgreesWith_blake2s _ _ _ _ _ _ _).mp h
  · intro h
    exact ⟨blake2sBytes, fun x d h => (Option.some.inj h).symm, (capAgreesWith_blake2s _ _ _ _ _ _ _).mpr h⟩

/-! ## Query steps over a total hash -/

/-- `queriesOfW` (`Comp/Whir/RunW.lean`) is `queriesOfWith`. -/
theorem queriesOfW_with (Ht : Bytes → Digest) {α : Type} :
    ∀ (p : Prog α) (s : St), queriesOfW Ht p s = queriesOfWith Ht p s
  | .ret _, _ => rfl
  | .fail, _ => rfl
  | .read k, ⟨cv, stream, os, roots⟩ => by
    rcases stream with _ | ⟨x, xs⟩
    · rfl
    · simp only [queriesOfW, queriesOfWith, queriesOfW_with]
  | .sample k, s => by simp only [queriesOfW, queriesOfWith, queriesOfW_with]
  | .grind bits k, ⟨cv, stream, os, roots⟩ => by
    rcases stream with _ | ⟨n, xs⟩
    · rfl
    · simp only [queriesOfW, queriesOfWith, queriesOfW_with]
  | .commit h w k, ⟨cv, stream, os, roots⟩ => by
    rcases stream with _ | ⟨x0, _ | ⟨x1, xs⟩⟩
    · rfl
    · rfl
    · simp only [queriesOfW, queriesOfWith]
      rcases digestOfScalars (x0, x1) with _ | root
      · rfl
      · simp only [queriesOfW_with]
  | .query i ps k, ⟨cv, stream, os, roots⟩ => by
    simp only [queriesOfW, queriesOfWith]
    rcases roots[i]? with _ | ⟨root, hh, ww⟩
    · rfl
    · simp only
      rcases openAll (m := Id) Ht root hh ww ps os with _ | ⟨rows, rest⟩
      · rfl
      · simp only [queriesOfW_with]

variable {Ht : Bytes → Digest}

/-- **A program's query steps over `Ht` are among its bind's.** -/
theorem mem_queriesOfW_bind_left {α β : Type} (p : Prog α) (f : α → Prog β) :
    ∀ (s : St) {b : ℕ × List (ℕ × Opening)}, b ∈ queriesOfW Ht p s → b ∈ queriesOfW Ht (p.bind f) s := by
  induction p with
  | ret a0 => intro s b h; simp [queriesOfW] at h
  | fail => intro s b h; simp [queriesOfW] at h
  | read k ih =>
    intro s b h
    obtain ⟨cv, xs, os, roots⟩ := s
    cases xs with
    | nil => simp [queriesOfW] at h
    | cons x xs => exact ih x _ h
  | sample k ih => intro s b h; exact ih _ _ h
  | grind bits k ih =>
    intro s b h
    obtain ⟨cv, xs, os, roots⟩ := s
    cases xs with
    | nil => simp [queriesOfW] at h
    | cons n xs =>
      simp only [queriesOfW, Prog.bind] at h ⊢
      split at h
      · rename_i hp
        simp only [hp, ↓reduceIte]
        exact ih _ h
      · simp at h
  | commit hh ww k ih =>
    intro s b h
    obtain ⟨cv, xs, os, roots⟩ := s
    match xs, h with
    | [], h => simp [queriesOfW] at h
    | [_], h => simp [queriesOfW] at h
    | x0 :: x1 :: xs, h =>
      simp only [queriesOfW, Prog.bind] at h ⊢
      split at h
      · rename_i root hr
        try simp only [hr]
        exact ih _ h
      · simp at h
  | query i ps k ih =>
    intro s b h
    simp only [queriesOfW, Prog.bind] at h ⊢
    split at h
    · simp at h
    · rename_i root hh ww hr
      try simp only [hr]
      split at h
      · rename_i rows rest hoa
        simp only [List.mem_cons] at h ⊢
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (ih rows _ h)
      · simp at h

/-- A continuation's query steps over `Ht`, from where the first program ends, are among the
bind's. -/
theorem mem_queriesOfW_bind_right {α β : Type} {p : Prog α} {f : α → Prog β} {s s' : St} {a : α}
    (h : RunsW Ht p s a s') {b : ℕ × List (ℕ × Opening)} (hb : b ∈ queriesOfW Ht (f a) s') :
    b ∈ queriesOfW Ht (p.bind f) s := by
  rw [os_queriesOf_bindW p f s h]
  exact List.mem_append_right _ hb

/-! ## The model's squeezes, assembled -/

theorem sqAllM_of_states {M : HashModel} : ∀ (n : ℕ) (st : ℕ → Digest),
    (∀ k < n, sqCvM M (st k) = some (st (k + 1))) →
    sqAllM M n (st 0) = some ((List.range n).map fun k ↦ challengeOf (st (k + 1)), st n)
  | 0, st, _ => rfl
  | n + 1, st, h => by
    have ih := sqAllM_of_states n (fun k => st (k + 1)) fun k hk => h (k + 1) (by omega)
    simp only [sqAllM, h 0 (by omega), Option.bind_some, ih, Option.map_some]
    congr
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    rfl

/-! ## The opening's caps -/

/-- **The opening's caps agree when the run's do, over a completeness model** (`deferredCaps`):
on a run record of the model's answers and a run within the limits over the model, the query
steps of the stacked opening over `Ht` from the run record's batching state are among those of
the deferring verifier's run over `Ht` from the seed's state on the run's proof. -/
theorem deferredCapsC {CM : CompModel} {bytecode : List K} (hb : bytecode.length = 2 ^ 22)
    (hag : ∀ x d, CM.H x = some d → d = Ht x) {D : VsData} {R : VsRunC}
    (hR : R.Ans CM D) (hok : D.OkC CM bytecode R)
    (hall : ∀ b ∈ queriesOfWith Ht (deferredProgram (R.fresh D) bytecode D.pi)
        ⟨Ht (digestBytes D.seed ++ digestBytes D.pi), D.stream, D.os, []⟩,
      BatchAgreesWith Ht b.1 b.2) :
    CapAgreesWith Ht (layoutOf bytecode D.logMem D.rows).stackLog D.rate D.root R.cvL D.xsW D.os
      (R.target D) := by
  intro b hbq
  apply hall
  rw [← queriesOfW_with] at hbq ⊢
  have hagM : ∀ x d, CM.hm.H x = some d → d = Ht x := hag
  have e0 : Ht (digestBytes D.seed ++ digestBytes D.pi) = R.cv0 := (hag _ _ hR.cv0).symm
  rw [e0]
  have hs1 := hok.stack_ge
  have hs2 := hok.stack_le
  have hcfg : configOk (layoutOf bytecode D.logMem D.rows).stackLog D.rate = true :=
    configOk_window _ (by omega) hs1 _ (by have := hok.rate_le; omega) hok.rate_ge
  have htau : (layoutOf bytecode D.logMem D.rows).tableLogHeights.getD opBlake2s 0 = D.tau := by
    simp only [VsData.tau, VsData.hs]
    simp [layoutOf, opBlake2s]
  -- the phases' runs over the model
  have h1 := runs_readSizesM (M := CM.hm) hb hok.logMem_ge hok.logMem_le hok.rate_ge hok.rate_le
    hok.rows_length (fun n hn => (le_two_pow_log2Ceil n).trans
      (Nat.pow_le_pow_right (by decide) (by have := hok.rows_log n hn; omega)))
    (by unfold minStackedLog Whir.minLogStack; omega) (by unfold maxStackedLog Whir.maxLogStack; omega)
    hR.cvA (D.x0 :: D.x1 :: D.tail) D.os []
  have h2 := runs_commitStackM (M := CM.hm) hcfg (x0 := D.x0) (x1 := D.x1) (root := D.root) rfl
    hR.cv10 D.tail D.os ([] ++ [])
  have hB := sqAllM_of_states 4 R.stB hR.stB
  rw [hR.stB0] at hB
  have h3 := RunsToM.runs (runsToM_sampleN hB) D.tail D.os
    ([] ++ [(D.root, stackShape (layoutOf bytecode D.logMem D.rows).stackLog D.rate)])
  have h4 := RunsToM.runs (runsToM_sampleE hR.cvB) D.tail D.os
    ([] ++ [(D.root, stackShape (layoutOf bytecode D.logMem D.rows).stackLog D.rate)])
  have h5 := RunsToM.runs hok.gkr (D.xsT ++ (D.xsF ++ D.xsW)) D.os
    ([] ++ [(D.root, stackShape (layoutOf bytecode D.logMem D.rows).stackLog D.rate)])
  have hT := hok.tables (.claimed (R.fresh D)) (by
    rw [layoutOf_logBytecode hb]
    exact bytecodeAtM_claimed (R.fresh D) bytecode)
  have h6 := RunsToM.runs hT (D.xsF ++ D.xsW) D.os
    ([] ++ [(D.root, stackShape (layoutOf bytecode D.logMem D.rows).stackLog D.rate)])
  have hF := hok.flock (.claimed (R.fresh D)) (matricesAtM_claimed (R.fresh D))
  rw [← htau] at hF
  have h7 := RunsToM.runs hF D.xsW D.os
    ([] ++ [(D.root, stackShape (layoutOf bytecode D.logMem D.rows).stackLog D.rate)])
  have hR6 := sqAllM_of_states 6 R.stR hR.stR
  rw [hR.stR0] at hR6
  have h8 := runs_ringSwitchM (M := CM.hm) D.fpoint D.s hR6 D.xsW D.os
    ([] ++ [(D.root, stackShape (layoutOf bytecode D.logMem D.rows).stackLog D.rate)])
  have h9 := RunsToM.runs (runsToM_sampleE hR.cvL) D.xsW D.os
    ([] ++ [(D.root, stackShape (layoutOf bytecode D.logMem D.rows).stackLog D.rate)])
  -- the deferring verifier's run passes through them
  unfold deferredProgram
  rw [verifyExecution_split]
  refine mem_queriesOfW_bind_left _ _ _ ?_
  refine mem_queriesOfW_bind_right (runsM_runsW hagM _ h1).1 ?_
  refine mem_queriesOfW_bind_right (runsM_runsW hagM _ h2).1 ?_
  refine mem_queriesOfW_bind_right (runsM_runsW hagM _ h3).1 ?_
  refine mem_queriesOfW_bind_right (runsM_runsW hagM _ h4).1 ?_
  refine mem_queriesOfW_bind_right (runsM_runsW hagM _ h5).1 ?_
  refine mem_queriesOfW_bind_right (runsM_runsW hagM _ h6).1 ?_
  refine mem_queriesOfW_bind_right (runsM_runsW hagM _ h7).1 ?_
  refine mem_queriesOfW_bind_right (runsM_runsW hagM _ h8).1 ?_
  unfold verifyStackedOpening
  simp only [verifyWhir_split, Prog.bind_eq]
  refine mem_queriesOfW_bind_right (runsM_runsW hagM _ h9).1 ?_
  refine mem_queriesOfW_bind_left _ _ _ ?_
  convert hbq using 4
  all_goals simp [VsRunC.target, VsRunC.lam, VsRunC.mcs, mcsOf, ringSwitchClaim,
    ColumnClaim.onStack, Function.comp_def]

end
end LeanVM.Guest.B1.VerifySub
