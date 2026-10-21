/-
  LeanVM.Guest.B1.Whir.StackedRunM

  Runs of the stacked opening's programs over a hash model: `Compile.run` at `Option` over the
  model's answered hash, from the runs of their pieces.
-/

module

public import LeanVM.Guest.B1.Whir.StackedRun
public import LeanVM.Guest.B1.Whir.CapM
public import LeanVM.Guest.B1.VerifySub.RunM

/-!
# Runs of the stacked opening over a hash model (TRIAGE #36)

`Whir/StackedRun.lean` over a `HashModel`, the runs `VerifySub.RunsM M p s a s'` (`p` at `Option`
over `M.H`, `B1.runM`, from `s` to `a` and `s'`, every hash it makes answered). The pieces of
`whirLevelsOpen`: the reads and samples (`RunsToM`), the next commitment (`os_runsM_commitP`), the
proof of work (`os_runsM_grindP`), the query positions from the answered challenges
(`osPosOfL`, `os_runsToM_sampleQueries`), and the openings: **`os_openAll_ofM`**, `Compile.openAll`
at `Option` over `M.H` accepting openings whose leaves the model hashes and whose paths climb to
the root, which `os_runsM_queryP` reads.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

variable {M : HashModel}

/-! ## Runs -/

theorem RunsToM.runsM {α : Type} {p : Prog α} {cv cv' : Digest} {xs : List E} {a : α}
    (h : RunsToM M p cv xs a cv') (rest : List E) (os : List Opening)
    (roots : List (Digest × ℕ × ℕ)) :
    RunsM M p ⟨cv, xs ++ rest, os, roots⟩ a ⟨cv', rest, os, roots⟩ := h rest os roots

/-- At the deployed model it is `VerifySub.Runs`. -/
theorem runsM_deployed {α : Type} {p : Prog α} {s : St} {a : α} {s' : St} :
    RunsM HashModel.deployed p s a s' ↔ VerifySub.Runs p s a s' := by
  simp only [RunsM, VerifySub.Runs, runM_deployed, Option.some.injEq]

/-! ## Runs of the pieces -/

/-- A sumcheck round of three coefficients (`sumcheckRoundPoly 3`, V:1313) over a hash model. -/
theorem runsToM_roundPoly3 {cv d1 d2 : Digest} (claim c0 c2 : E) (h1 : obsCvM M cv c0 = some d1)
    (h2 : obsCvM M d1 c2 = some d2) :
    RunsToM M (sumcheckRoundPoly 3 claim none) cv [c0, c2] [c0, claim + c2, c2] d2 := by
  have hN : obsAllM M d1 [c2] = some d2 := by simp [obsAllM, h2]
  have h := (runsToM_readE h1).bind (f := fun constant => do
      let tail ← Prog.readN 1
      return constant :: (claim + sumE tail) :: tail)
    ((runsToM_readN hN).bind (f := fun tail => (pure (c0 :: (claim + sumE tail) :: tail) :
      Prog (List E))) (runsToM_ret _ _))
  refine h.of_eq rfl ?_ rfl
  simp only [sumE, List.foldl, zero_add]

/-- The next commitment over a hash model (`commitP`, V:1730): two words absorbed, their digest
the root read. -/
theorem os_runsM_commitP {cv d0 d1 : Digest} {x0 x1 : E} {root : Digest}
    (h : digestOfScalars (x0, x1) = some root) (h0 : obsCvM M cv x0 = some d0)
    (h1 : obsCvM M d0 x1 = some d1) (height width : ℕ) (rest : List E)
    (os : List Opening) (roots : List (Digest × ℕ × ℕ)) :
    RunsM M (Prog.commitP height width) ⟨cv, x0 :: x1 :: rest, os, roots⟩ ()
      ⟨d1, rest, os, roots ++ [(root, height, width)]⟩ := by
  unfold obsCvM at h0 h1
  simp only [RunsM, runM, Prog.commitP, Compile.run, absorbBlock, h, Option.bind_eq_bind]
  rw [show M.H (digestBytes cv ++ blockOf x0 1) = some d0 from h0]
  simp only [Option.bind_some]
  rw [show M.H (digestBytes d0 ++ blockOf x1 1) = some d1 from h1]
  rfl

/-- **The proof of work over a hash model** (`grindP`, V:566-572): the base and the digest the
model answers pass `powOk`, and the chain absorbs the nonce at tag 4. -/
theorem runsToM_grindP {cv B D cv' : Digest} {bits : ℕ} {n : E}
    (hB : M.H (digestBytes cv ++ blockOf 0 3) = some B) (hD : M.H (digestBytes B ++ blockOf n 4) = some D)
    (hpow : powOk bits n D = true) (hcv : M.H (digestBytes cv ++ blockOf n 4) = some cv') :
    RunsToM M (Prog.grindP bits) cv [n] () cv' := fun r o rts ↦ by
  simp only [runM, Prog.grindP, Compile.run, absorbBlock, List.cons_append, List.nil_append,
    Option.bind_eq_bind]
  rw [hB, Option.bind_some, hD, Option.bind_some, hcv, Option.bind_some, ite_pos' hpow]
  rfl

/-- The opening of the `i`-th commitment at `ps` over a hash model (`queryP`): the rows
`Compile.openAll` at `Option` over `M.H` gives. -/
theorem os_runsM_queryP {cv : Digest} {i : ℕ} {ps : List ℕ} {xs : List E} {os orest : List Opening}
    {roots : List (Digest × ℕ × ℕ)} {root : Digest} {height width : ℕ} {rows : List (List K)}
    (hr : roots[i]? = some (root, height, width))
    (ho : openAll (m := Option) M.H root height width ps os = some (some (rows, orest))) :
    RunsM M (Prog.queryP i ps) ⟨cv, xs, os, roots⟩ rows ⟨cv, xs, orest, roots⟩ := by
  simp only [RunsM, runM, Prog.queryP, Compile.run, hr]
  simp only [bind] at ho ⊢
  rw [ho]
  rfl

/-- **`openAll` over a hash model**: openings each of the shape, whose leaf the model hashes and
whose path climbs (V:526, at `Option` over `M.H`) to the root, are accepted, in order. -/
theorem os_openAll_ofM {root : Digest} {height width : ℕ} :
    ∀ (ps : List ℕ) (os orest : List Opening), ps.length = os.length →
      (∀ j (hj : j < os.length), (os[j]).leaf.length = width ∧ (os[j]).path.length = height ∧
        ∃ ld, M.H ((os[j]).leaf.flatMap kBytes) = some ld ∧
          climb (m := Option) M.H ld (ps.getD j 0) (os[j]).path = some root) →
      openAll (m := Option) M.H root height width ps (os ++ orest) =
        some (some (os.map (·.leaf), orest))
  | [], [], orest, _, _ => rfl
  | [], _ :: _, _, h, _ => absurd h (by simp)
  | _ :: _, [], _, h, _ => absurd h (by simp)
  | q :: ps, o :: os, orest, hl, hj => by
    obtain ⟨h1, h2, ld, hld, h3⟩ := hj 0 (by simp)
    have hone : openOne (m := Option) M.H root height width q o = some true := by
      simp only [List.getElem_cons_zero, List.getD_cons_zero] at h1 h2 hld h3
      simp only [openOne, h1, h2, and_self, ↓reduceIte, bind, hld, Option.bind_some, h3]
      rfl
    have ih := os_openAll_ofM ps os orest (by simpa using hl) fun j hj' => by
      have := hj (j + 1) (by simpa using hj')
      simp only [List.getElem_cons_succ, List.getD_cons_succ] at this
      exact this
    simp only [List.cons_append, openAll, bind, hone, Option.bind_some, ↓reduceIte, ih]
    rfl

/-! ## The query positions -/

/-- Query position `i` from the challenges `cs` (V:1598-1608): chunk `i % (192/depth)` of the
challenge `i / (192/depth)`. -/
def osPosOfL (depth : ℕ) (cs : List E) (i : ℕ) : ℕ :=
  (eToNat (cs.getD (i / (192 / depth)) 0) >>> (i % (192 / depth) * depth)) % 2 ^ depth

/-- **`sampleQueriesAux`** (V:1598) over a hash model: `k` answered samples cover `rem`
positions, `per = 192/depth` at a time. -/
theorem runsToM_sampleQueriesAux (depth : ℕ) (hd : 0 < 192 / depth) :
    ∀ (k fuel rem : ℕ) (cv : Digest) (cs : List E) (cv' : Digest), sqAllM M k cv = some (cs, cv') →
      rem ≤ k * (192 / depth) → (k - 1) * (192 / depth) < rem ∨ k = 0 → k ≤ fuel →
      RunsToM M (sampleQueriesAux depth fuel rem) cv [] ((List.range rem).map (osPosOfL depth cs)) cv' := by
  intro k
  induction k with
  | zero =>
    intro fuel rem cv cs cv' hs h1 _ _
    simp only [sqAllM, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    obtain rfl : rem = 0 := by omega
    show RunsToM M (sampleQueriesAux depth fuel 0) cv [] [] cv
    cases fuel with
    | zero => exact runsToM_ret _ _
    | succ f =>
      simp only [sampleQueriesAux, ↓reduceIte]
      exact runsToM_ret _ _
  | succ k IH =>
    intro fuel rem cv cs cv' hs h1 h2 h3
    obtain ⟨c, hc, hrest⟩ := Option.bind_eq_some_iff.mp hs
    obtain ⟨r, hr, hrr⟩ := Option.map_eq_some_iff.mp hrest
    simp only [Prod.mk.injEq] at hrr
    obtain ⟨rfl, rfl⟩ := hrr
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hrem : rem ≠ 0 := by rcases h2 with h2 | h2 <;> omega
    have hn : min (192 / depth) rem = if k = 0 then rem else 192 / depth := by
      generalize 192 / depth = per at *
      split
      · subst_vars; simp at h1; omega
      · rcases h2 with h2 | h2
        · have : per ≤ k * per := Nat.le_mul_of_pos_left per (by omega)
          rw [show k + 1 - 1 = k by omega] at h2
          omega
        · omega
    have hr1 : rem - min (192 / depth) rem ≤ k * (192 / depth) := by
      rw [hn]
      generalize 192 / depth = per at *
      split
      · omega
      · rw [Nat.add_mul, Nat.one_mul] at h1; omega
    have hr2 : (k - 1) * (192 / depth) < rem - min (192 / depth) rem ∨ k = 0 := by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · exact Or.inr hk
      · left
        rw [hn, ite_neg' (by omega)]
        generalize 192 / depth = per at *
        rcases h2 with h2 | h2
        · rw [show k + 1 - 1 = k by omega] at h2
          have : (k - 1) * per + per = k * per := by
            rw [← Nat.succ_mul, show (k - 1).succ = k by omega]
          omega
        · omega
    have ih := IH f (rem - min (192 / depth) rem) c r.1 r.2 hr hr1 hr2 (by omega)
    unfold sampleQueriesAux
    simp only [hrem, ↓reduceIte]
    refine RunsToM.of_eq (RunsToM.bind (runsToM_sampleE hc) (RunsToM.bind ih (runsToM_ret _ _)))
      (by simp) ?_ rfl
    have hr' : List.range rem = List.range (min (192 / depth) rem) ++
        (List.range (rem - min (192 / depth) rem)).map (min (192 / depth) rem + ·) := by
      rw [← List.range_add]; congr 1; omega
    rw [hr', List.map_append, List.map_map]
    refine congrArg₂ (· ++ ·) ?_ ?_
    · refine List.map_congr_left fun i hi => ?_
      have hi' : i < min (192 / depth) rem := List.mem_range.mp hi
      have e1 : i / (192 / depth) = 0 := Nat.div_eq_of_lt (by omega)
      have e2 : i % (192 / depth) = i := Nat.mod_eq_of_lt (by omega)
      simp only [osPosOfL]
      rw [e1, e2]
      rfl
    · refine List.map_congr_left fun i hi => ?_
      simp only [Function.comp, osPosOfL]
      rcases Nat.eq_zero_or_pos k with hk | hk
      · have : rem - min (192 / depth) rem = 0 := by rw [hn, ite_pos' hk]; omega
        rw [this] at hi; simp at hi
      · rw [show min (192 / depth) rem = 192 / depth by rw [hn, ite_neg' (by omega)],
          show (192 / depth + i) / (192 / depth) = i / (192 / depth) + 1 by
            rw [Nat.add_comm, Nat.add_div_right _ hd],
          Nat.add_mod_left, List.getD_cons_succ]

/-- `sampleQueries` (V:1610) over a hash model, over `nq` positions in `k = ⌈nq / per⌉` answered
samples. -/
theorem os_runsToM_sampleQueries {depth nq k : ℕ} (hd : 0 < 192 / depth) (h1 : nq ≤ k * (192 / depth))
    (h2 : (k - 1) * (192 / depth) < nq ∨ k = 0) (hk : k ≤ nq) {cv cv' : Digest} {cs : List E}
    (hs : sqAllM M k cv = some (cs, cv')) :
    RunsToM M (sampleQueries depth nq) cv [] ((List.range nq).map (osPosOfL depth cs)) cv' :=
  runsToM_sampleQueriesAux depth hd k nq nq cv cs cv' hs h1 h2 hk

/-- `n` answered squeezes give `n` challenges. -/
theorem length_sqAllM : ∀ {n : ℕ} {cv : Digest} {cs : List E} {cv' : Digest},
    sqAllM M n cv = some (cs, cv') → cs.length = n
  | 0, _, _, _, h => by
    simp only [sqAllM, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; rfl
  | n + 1, _, _, _, h => by
    obtain ⟨c, -, hrest⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r, hr, hrr⟩ := Option.map_eq_some_iff.mp hrest
    simp only [Prod.mk.injEq] at hrr
    rw [← hrr.1, List.length_cons, length_sqAllM hr]

/-- **A run of squeezes over a hash model is `sqAllM`**: `sampleN m` reads nothing, and its run
answers every squeeze. -/
theorem sqAllM_of_runM : ∀ {m : ℕ} {cv : Digest} {rest : List E} {os : List Opening}
    {roots : List (Digest × ℕ × ℕ)} {rs : List E} {st : St},
    runM M (Prog.sampleN m) ⟨cv, rest, os, roots⟩ = some (some (rs, st)) →
      sqAllM M m cv = some (rs, st.cv)
  | 0, cv, rest, os, roots, rs, st, h => by
    simp only [runM, Prog.sampleN, Compile.run, Option.pure_def, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | m + 1, cv, rest, os, roots, rs, st, h => by
    have e : Prog.sampleN (m + 1) = Prog.sampleE >>= fun x => do
        let xs ← Prog.sampleN m
        return x :: xs := rfl
    rw [e, prog_bind_eq, runM_bind] at h
    simp only [runM, Prog.sampleE, Compile.run, absorbBlock, Option.bind_eq_bind] at h
    cases hc : M.H (digestBytes cv ++ blockOf 0 2) with
    | none => rw [hc] at h; simp at h
    | some c =>
      rw [hc] at h
      simp only [Option.bind_some, Option.pure_def, Option.elim] at h
      change runM M ((Prog.sampleN m).bind fun xs => pure (challengeOf c :: xs)) ⟨c, rest, os, roots⟩ =
        _ at h
      rw [runM_bind] at h
      cases hr : runM M (Prog.sampleN m) ⟨c, rest, os, roots⟩ with
      | none => rw [hr] at h; simp at h
      | some o =>
        cases o with
        | none => rw [hr] at h; simp at h
        | some r =>
          rw [hr] at h
          simp only [Option.bind_some, Option.elim, runM, Prog.pure_eq, Compile.run,
            Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have ih := sqAllM_of_runM (m := m) hr
          simp only [sqAllM, sqCvM, hc, Option.bind_some, ih, Option.map_some]

/-- `RunsToM` of `sampleN m` is `sqAllM`. -/
theorem sqAllM_of_runsToM {m : ℕ} {cv cv' : Digest} {rs : List E}
    (h : RunsToM M (Prog.sampleN m) cv [] rs cv') : sqAllM M m cv = some (rs, cv') :=
  sqAllM_of_runM (h [] [] [])

end
end LeanVM.Guest.B1
