/-
  LeanVM.Guest.B1.Tables.GkrBaseM

  `GkrBase.lean` under any semantics of `BLAKE2S` and over a hash model: a body's statements read
  by position, its Fiat-Shamir blocks answered by the model, and the GKR walk's runs over the
  model.
-/

module

public import LeanVM.Guest.B1.Tables.GkrBase
public import LeanVM.Guest.B1.ModelAux
public import LeanVM.Guest.B1.Opening

/-!
# Reading a body by position under any semantics; the GKR walk over a hash model

`GkrBase.lean` over `S : BlakeSem` (`Core.Stmt.HoldsListB`) and a hash model `M`:

* `holdsB_slice`, `holdsB_call`, `holdsB_callIf`: a body without `ret` holding under `S` gives
  every run of its statements under `S`; `holdsB_sliceF`, `holdsB_atom`: a run with no `BLAKE2S`
  atom (`Stmt.noBlakeList`, checked with the statements by the kernel) holds as deployed, at the
  same call relation, so its deployed facts carry over with their proofs;
* `holdsB_fsNextAt`, `holdsB_squeezeAt`: an `fs_next` and a `squeeze` under `M.sem`, the new
  state the model's answer (`obsCvM`, `sqCvM`);
* `relB_pre`: a function's relation under `S` is a valuation satisfying its body before `ret`;
* `fsM_chain`, `fsM_chainAll`: `fs_next` blocks chained from a known state, `obsAllM`;
* `runsToM_require`, `RunsToM.sumcheck_cons`, `runsToM_gkrStep`: `GkrBase.lean`'s runs over `M`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Reading a body by position under any semantics -/

section Slices

variable {S : BlakeSem} {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- **A run of statements of a body without `ret`** holds under `S`: `blk`, equal to the
statements at position `n` (`holds_slice`). -/
theorem holdsB_slice {pre : List Stmt} (hnr : Stmt.noRetList pre = true)
    (h : Stmt.HoldsListB S C rd σ pre True kret) (n : ℕ) (blk : List Stmt)
    (heq : stmtsEqb blk ((pre.drop n).take blk.length) = true) :
    Stmt.HoldsListB S C rd σ blk True kret := by
  have hsplit : pre = pre.take n ++ (((pre.drop n).take blk.length) ++
      (pre.drop n).drop blk.length) := by simp
  rw [hsplit] at h hnr
  rw [gkr_noRetList_append, gkr_noRetList_append, Bool.and_eq_true, Bool.and_eq_true] at hnr
  rw [holdsListB_append, holdsListB_noRet _ hnr.1, holdsListB_append,
    holdsListB_noRet _ hnr.2.1] at h
  rw [stmtsEqb_sound heq]
  exact h.2.1

/-- **A run with no `BLAKE2S` atom** of a body holding under `S` holds as deployed, at the same
call relation; the absence checked with the statements. -/
theorem holdsB_sliceF {pre : List Stmt} (hnr : Stmt.noRetList pre = true)
    (h : Stmt.HoldsListB S C rd σ pre True kret) (n : ℕ) (blk : List Stmt)
    (heq : (stmtsEqb blk ((pre.drop n).take blk.length) && Stmt.noBlakeList blk) = true) :
    Stmt.HoldsList C rd σ blk True kret := by
  rw [Bool.and_eq_true] at heq
  exact (holdsListB_iff_of_noBlake heq.2 True kret).mp (holdsB_slice hnr h n blk heq.1)

/-- One atom other than `BLAKE2S` of a body holding under `S` holds as deployed. -/
theorem holdsB_atom {pre : List Stmt} (hnr : Stmt.noRetList pre = true)
    (h : Stmt.HoldsListB S C rd σ pre True kret) (n : ℕ) (a : Atom)
    (heq : (stmtsEqb [.atom a] ((pre.drop n).take 1) && Stmt.noBlakeList [.atom a]) = true) :
    a.Holds rd σ := by
  have := holdsB_sliceF hnr h n [.atom a] heq
  simpa [Stmt.HoldsList, Stmt.Holds] using this

/-- One call of a body holding under `S`. -/
theorem holdsB_call {pre : List Stmt} (hnr : Stmt.noRetList pre = true)
    (h : Stmt.HoldsListB S C rd σ pre True kret) (n : ℕ) (f : String) (args rets : List V)
    (heq : stmtsEqb [.call f args rets] ((pre.drop n).take 1) = true) :
    C f (args.map σ) (rets.map σ) := by
  have := holdsB_slice hnr h n [.call f args rets] heq
  simpa [Stmt.HoldsListB, Stmt.HoldsB] using this

/-- One conditional call of a body holding under `S`. -/
theorem holdsB_callIf {pre : List Stmt} (hnr : Stmt.noRetList pre = true)
    (h : Stmt.HoldsListB S C rd σ pre True kret) (n : ℕ) (c : V) (f : String) (args : List V)
    (heq : stmtsEqb [.callIf c f args] ((pre.drop n).take 1) = true) :
    σ c ≠ 0 → C f (args.map σ) [] := by
  have := holdsB_slice hnr h n [.callIf c f args] heq
  simp only [Stmt.HoldsListB, Stmt.HoldsB, and_true] at this
  exact this.2

/-- A conditional whose branches have no `ret`, under `S` (`holds_ite_noRet`). -/
theorem holdsB_ite_noRet (c : V) (z n : List Stmt) (hz : Stmt.noRetList z = true)
    (hn : Stmt.noRetList n = true) (next : Prop) :
    Stmt.HoldsB S C rd σ (.ite c z n) next kret ↔
      (IsInK (σ c) ∧ (σ c = 0 → Stmt.HoldsListB S C rd σ z True kret) ∧
        (σ c ≠ 0 → Stmt.HoldsListB S C rd σ n True kret)) ∧ next := by
  rw [holdsB_noRet (.ite c z n) (by simp [Stmt.noRet, hz, hn]) next kret]
  rfl

end Slices

section Model

variable {M : HashModel} {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- **An `fs_next` over a hash model**: the word at the cursor's offset `j`, absorbed, the new
state the model's answer `obsCvM M cv w` (`holds_fsNextAt`). -/
theorem holdsB_fsNextAt {pre : List Stmt} (hnr : Stmt.noRetList pre = true)
    (h : Stmt.HoldsListB M.sem C rd σ pre True kret) (n : ℕ) (s0 s1 cur : V) (j b : ℕ)
    (heq : stmtsEqb (fsNextT s0 s1 cur j b) ((pre.drop n).take 13) = true) :
    LoadHolds rd (σ cur) j (σ (.n b)) ∧ ∃ cv d, (σ s0, σ s1) = digestScalars cv ∧
      obsCvM M cv (σ (.n b)) = some d ∧
      (σ (.n (b + 13)), σ (.n (b + 14))) = digestScalars d := by
  obtain ⟨⟨hl, cv, d, hcv, hd, hv⟩, -⟩ := holdsB_fsNextT s0 s1 cur j b (holdsB_slice hnr h n _ (by
      rw [show (fsNextT s0 s1 cur j b).length = 13 by simp [fsNextT, fsCompressT]]; exact heq))
  refine ⟨hl, cv, d, hcv, hd, ?_⟩
  have h12 := hv 12 (by omega) (by omega)
  have h13 := hv 13 (by omega) (by omega)
  rw [show b + 1 + 12 = b + 13 by omega] at h12
  rw [show b + 1 + 13 = b + 14 by omega] at h13
  rw [h12, h13]
  rfl

/-- **A `squeeze` over a hash model**: the new state the model's answer `sqCvM M cv`, and the
challenge `challengeOf` of it (`holds_squeezeAt`). -/
theorem holdsB_squeezeAt {pre : List Stmt} (hnr : Stmt.noRetList pre = true)
    (h : Stmt.HoldsListB M.sem C rd σ pre True kret) (n : ℕ) (s0 s1 : V) (b : ℕ)
    (heq : stmtsEqb (squeezeT s0 s1 b) ((pre.drop n).take 14) = true) :
    ∃ cv d, (σ s0, σ s1) = digestScalars cv ∧ sqCvM M cv = some d ∧
      (σ (.n (b + 5)), σ (.n (b + 6))) = digestScalars d ∧ σ (.n (b + 13)) = challengeOf d := by
  obtain ⟨⟨cv, d, hcv, hd, hv⟩, -⟩ := holdsB_squeezeT s0 s1 b (holdsB_slice hnr h n _ (by
      rw [show (squeezeT s0 s1 b).length = 14 by simp [squeezeT, squeezeStateT, challengeT]]
      exact heq))
  refine ⟨cv, d, hcv, hd, ?_, hv 13 (by omega)⟩
  rw [hv 5 (by omega), hv 6 (by omega)]
  rfl

end Model

/-- A function whose body is `pre ++ [ret vs]`, `pre` without `ret`: its relation under `S` is
some valuation of its parameters satisfying `pre` under `S` and returning `vs` (`rel_pre`). -/
theorem relB_pre {S : BlakeSem} {rd : Reader} {f : String} {fn : Fn}
    (hf : coreProgram.find? f = some fn) {pre : List Stmt} {vs : List V}
    (hb : fn.body = pre ++ [.ret vs]) (hnr : Stmt.noRetList pre = true) {args rets : List E}
    (h : coreProgram.RelB S rd f args rets) :
    ∃ σ : Val, fn.params.map σ = args ∧
      Stmt.HoldsListB S (coreProgram.RelB S rd) rd σ pre True (fun rs => rs = rets) ∧
      vs.map σ = rets := by
  rw [relB_iff_sem hf, hb] at h
  obtain ⟨σ, hp, hb⟩ := h
  rw [holdsListB_append, holdsListB_noRet _ hnr] at hb
  exact ⟨σ, hp, hb.1, hb.2⟩

/-- **A guarded loop, forward**, for any call relation `C` (`Main.loop_sound`). -/
theorem loop_soundB {C : CallRel} {f : String} {ps : List E} {N : E} {m : ℕ} {B : E → Prop}
    (hm : m < ordG) (hN : N = gen ^ m)
    (hstep : ∀ x, C f (x :: ps) [] → B x ∧ (x * gen + N ≠ 0 → C f (x * gen :: ps) []))
    (h : 1 + N ≠ 0 → C f (1 :: ps) []) : ∀ j < m, B (gen ^ j) := by
  have key : ∀ t k, k + t = m → C f (gen ^ k :: ps) [] → ∀ j, k ≤ j → j < m → B (gen ^ j) := by
    intro t
    induction t with
    | zero => intro k hk _ j h1 h2; omega
    | succ t ih =>
      intro k hk hrun j h1 h2
      obtain ⟨hB, hnext⟩ := hstep _ hrun
      rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
      · exact hB
      · have hne : gen ^ k * gen + N ≠ 0 := by
          intro he
          rw [gen_pow_add_eq_zero_iff, hN] at he
          have := gen_pow_inj hm (by unfold ordG at hm; omega) he
          omega
        have := hnext hne
        rw [gen_pow_mul_gen] at this
        exact ih (k + 1) (by omega) this j hlt h2
  intro j hj
  have h1 := h (by rw [hN]; exact Main.one_add_gen_pow_ne_zero (by omega) hm)
  rw [← pow_zero gen] at h1
  exact key m 0 (by omega) h1 j (Nat.zero_le j) hj

/-! ## Chains of `fs_next` over a hash model -/

section Chains

variable {M : HashModel}

/-- An `fs_next` from a known state: the model's answer for it (`fs_chain`). -/
theorem fsM_chain {X : Digest} {p q r s w : E} (h : (p, q) = digestScalars X)
    (hb : ∃ cv d, (p, q) = digestScalars cv ∧ obsCvM M cv w = some d ∧ (r, s) = digestScalars d) :
    ∃ d, obsCvM M X w = some d ∧ (r, s) = digestScalars d := by
  obtain ⟨cv, d, h1, hd, h2⟩ := hb
  obtain rfl := digestScalars_injective (h1.symm.trans h)
  exact ⟨d, hd, h2⟩

/-- The chain over the model, one word more. -/
theorem obsAllM_snoc (cv : Digest) (xs : List E) (x : E) :
    obsAllM M cv (xs ++ [x]) = (obsAllM M cv xs).bind fun c ↦ obsCvM M c x := by
  rw [obsAllM_append_eq]
  congr 1
  funext c
  simp only [obsAllM]
  cases obsCvM M c x <;> rfl

/-- **One more `fs_next` of a chain**: from the state `X` the model reached on `xs`, the word `w`
absorbed, the state the model's answer on `xs ++ [w]`. -/
theorem fsM_chainAll {X0 X : Digest} {xs : List E} (hX : obsAllM M X0 xs = some X)
    {p q r s w : E} (h : (p, q) = digestScalars X)
    (hb : ∃ cv d, (p, q) = digestScalars cv ∧ obsCvM M cv w = some d ∧ (r, s) = digestScalars d) :
    ∃ d, obsAllM M X0 (xs ++ [w]) = some d ∧ (r, s) = digestScalars d := by
  obtain ⟨d, hd, hrs⟩ := fsM_chain h hb
  exact ⟨d, by rw [obsAllM_snoc, hX, Option.bind_some, hd], hrs⟩

/-- No word absorbed, the chain unchanged. -/
theorem obsAllM_nil (cv : Digest) : obsAllM M cv [] = some cv := rfl

end Chains

/-! ## Runs over a hash model -/

section Runs

variable {M : HashModel}

/-- A requirement that holds, over the model (`runsTo_require`). -/
theorem runsToM_require {c : Prop} [Decidable c] (hc : c) (cv : Digest) :
    RunsToM M (Prog.require c) cv [] () cv := by
  simp only [Prog.require, hc, ↓reduceIte]
  exact runsToM_ret () cv

/-- `n` words read over the model, the chain answered (`runsTo_readN_of_length`). -/
theorem runsToM_readN_of_length {n : ℕ} {cv cv' : Digest} {xs : List E} (h : xs.length = n)
    (ho : obsAllM M cv xs = some cv') : RunsToM M (Prog.readN n) cv xs xs cv' := by
  subst h; exact runsToM_readN ho

/-- A round, then the rest of a sumcheck, over the model (`RunsTo.sumcheck_cons`). -/
theorem RunsToM.sumcheck_cons {claim claim' ch fin : E} {count : ℕ} {e : Option E}
    {es : List (Option E)} {cv cv1 cv2 : Digest} {xs ys pt : List E}
    (h1 : RunsToM M (roundPoly count claim e) cv xs (claim', ch) cv1)
    (h2 : RunsToM M (sumcheck claim' count es) cv1 ys (pt, fin) cv2) :
    RunsToM M (sumcheck claim count (e :: es)) cv (xs ++ ys) (ch :: pt, fin) cv2 := by
  rw [sumcheck_cons_eq]
  exact (h1.bind (RunsToM.bind (f := fun q => (pure (ch :: q.1, q.2) : Prog (List E × E))) h2
    (runsToM_ret _ _))).of_eq (by simp) rfl rfl

/-- **A GKR step of `step` levels over the model** (`runsTo_gkrStep`): the combiner squeezed
from `cv` to `cL`, the sumcheck over the point, the three trees' `2^step` children absorbed, the
products' check, and `step` new coordinates squeezed (`sqAllM`). -/
theorem runsToM_gkrStep (step : ℕ) {cv cL cvS d0 d1 d2 : Digest} {s : GkrState}
    {ws chs c0 c1 c2 : List E} {cl : E} {r : List E × Digest} (hL : sqCvM M cv = some cL)
    (hsc : RunsToM M (sumcheck (polyEval s.values (challengeOf cL)) (2 ^ step + 1)
      (s.point.map some)) cL ws (chs, cl) cvS)
    (h0 : c0.length = 2 ^ step) (h1 : c1.length = 2 ^ step) (h2 : c2.length = 2 ^ step)
    (o0 : obsAllM M cvS c0 = some d0) (o1 : obsAllM M d0 c1 = some d1)
    (o2 : obsAllM M d1 c2 = some d2)
    (hreq : cl = polyEval [prodE c0, prodE c1, prodE c2] (challengeOf cL))
    (hsq : sqAllM M step d2 = some r) :
    RunsToM M (gkrStep step s) cv (ws ++ (c0 ++ (c1 ++ c2)))
      ⟨[c0, c1, c2].map (multilinearEval · r.1), r.1 ++ chs⟩ r.2 := by
  refine RunsToM.of_eq (xs := [] ++ (ws ++ (c0 ++ (c1 ++ (c2 ++ ([] ++ ([] ++ []))))))) ?_
    (by simp) rfl rfl
  unfold gkrStep
  refine (runsToM_sampleE hL).bind ?_
  refine hsc.bind ?_
  refine (runsToM_readN_of_length h0 o0).bind ?_
  refine (runsToM_readN_of_length h1 o1).bind ?_
  refine (runsToM_readN_of_length h2 o2).bind ?_
  refine (runsToM_require hreq _).bind ?_
  refine (runsToM_sampleN (cs := r.1) (cv' := r.2) hsq).bind ?_
  exact runsToM_ret _ _

end Runs

end
end LeanVM.Guest.B1.VerifySub
