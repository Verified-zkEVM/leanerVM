/-
  LeanVM.Guest.B1.Comp.Whir.RunW

  The specification's runs over a total hash, and the runs a hash model answers: the foundation of
  `open_stacked`'s completeness over a completeness model.
-/

module

public import LeanVM.Guest.B1.Comp.FsBlocks
public import LeanVM.Guest.B1.Comp.Whir.Queries
public import LeanVM.Guest.B1.Whir.OsSteps
public import LeanVM.Guest.B1.Whir.StackedRunM

/-!
# Runs over a total hash, and answered runs

The deployed stacked opening's completeness (`Whir/StackedC*.lean`) reads its honest values off a
run of the specification at BLAKE2s (`Runs`, `runId`, the chain states `obsCv`, `sqCv`, …). Over a
completeness model the run is the model's (`RunsM M`, `Compile.run` at `Option` over `M.H`), and
the honest values are those of a total hash `Ht` the model agrees with where it answers
(`∀ x d, M.H x = some d → d = Ht x`, as `GuestCompleteModel` states it):

* the chain states over `Ht`: `obsCvW`, `sqCvW`, `obsAllW`, `sqAllW`, `absorbCvW`, `gcDigestW`,
  the values `fsValsW`, `sqValsW`, the query positions `osPosOfW`, the query steps `queriesOfW`,
  each at `blake2sBytes` the deployed one (`…W_blake`);
* the runs over `Ht`: `runW Ht`, `RunsW Ht`, `RunsToW Ht`, `RunsWithW Ht` (at `blake2sBytes`
  the deployed `runId`, `Runs`, `RunsTo`, `RunsWith`), with their bind and step lemmas;
* **answered runs**: `AnsRun H Ht p s`, every hash the run of `p` from `s` over `Ht` makes
  answered by `H` with `Ht`'s digest. `runsM_runsW`: a run the model answers is the run over `Ht`,
  answered; `ansRun_blake`: at the deployed model every run is answered. The guest's `BLAKE2S`
  rows are the model's exactly at the answered strings, which `AnsRun` names step by step.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub LeanVM.E2E.Complete

@[expose] public section

/-! ## The chain over a total hash -/

section Hash

variable (Ht : Bytes → Digest)

/-- The chain after absorbing a stream word over `Ht` (`obsCv`). -/
def obsCvW (cv : Digest) (x : E) : Digest := Ht (digestBytes cv ++ blockOf x 1)

/-- The chain after a squeeze over `Ht` (`sqCv`). -/
def sqCvW (cv : Digest) : Digest := Ht (digestBytes cv ++ blockOf 0 2)

/-- The chain after absorbing the words `xs` over `Ht` (`obsAll`). -/
def obsAllW (cv : Digest) (xs : List E) : Digest := xs.foldl (obsCvW Ht) cv

/-- `n` squeezes over `Ht` (`sqAll`). -/
def sqAllW : ℕ → Digest → List E × Digest
  | 0, cv => ([], cv)
  | n + 1, cv => (challengeOf (sqCvW Ht cv) :: (sqAllW n (sqCvW Ht cv)).1, (sqAllW n (sqCvW Ht cv)).2)

/-- The state after absorbing `x` with the tag over `Ht` (`absorbCv`). -/
def absorbCvW (cv : Digest) (x : E) (tag : ℕ) : Digest := Ht (digestBytes cv ++ blockOf x tag)

/-- The digest `.grind` checks over `Ht` (`gcDigest`). -/
def gcDigestW (cv : Digest) (nonce : E) : Digest :=
  Ht (digestBytes (Ht (digestBytes cv ++ blockOf 0 3)) ++ blockOf nonce 4)

/-- The honest values of `fsCompressT` over `Ht` (`fsVals`). -/
def fsValsW (x : E) (cv : Digest) (tag : ℕ) : ℕ → E
  | 0 => ofK (x.limb 0)
  | 1 => ofK (x.limb 1)
  | 2 => ofK (x.limb 2)
  | 3 => eOfNat tag
  | 4 => y * y
  | 5 => y * y * ofK (x.limb 2)
  | 6 => x + y * y * ofK (x.limb 2)
  | 7 => y * eOfNat tag
  | 8 => ofK (x.limb 2) + y * eOfNat tag
  | 9 => Value.ivCells.1
  | 10 => Value.ivCells.2
  | 11 => metadataCell 64 true
  | 12 => (digestScalars (absorbCvW Ht cv x tag)).1
  | 13 => (digestScalars (absorbCvW Ht cv x tag)).2
  | _ => 0

/-- The honest values of `squeezeStateT` over `Ht` (`sqStateVals`). -/
def sqStateValsW (cv : Digest) (tag : ℕ) : ℕ → E
  | 0 => 0
  | 1 => y * eOfNat tag
  | 2 => Value.ivCells.1
  | 3 => Value.ivCells.2
  | 4 => metadataCell 64 true
  | 5 => (digestScalars (absorbCvW Ht cv 0 tag)).1
  | 6 => (digestScalars (absorbCvW Ht cv 0 tag)).2
  | _ => 0

/-- The honest values of `squeezeT` over `Ht` (`sqVals`). -/
def sqValsW (cv : Digest) : ℕ → E
  | 7 => ofK ((digestScalars (sqCvW Ht cv)).2.limb 0)
  | 8 => (digestScalars (sqCvW Ht cv)).2 + ofK ((digestScalars (sqCvW Ht cv)).2.limb 0)
  | 9 => word 1 0 1
  | 10 => ((digestScalars (sqCvW Ht cv)).2 + ofK ((digestScalars (sqCvW Ht cv)).2.limb 0)) * word 1 0 1
  | 11 => y * y
  | 12 => y * y * ofK ((digestScalars (sqCvW Ht cv)).2.limb 0)
  | 13 => challengeOf (sqCvW Ht cv)
  | k => sqStateValsW Ht cv 2 k

/-- Query position `i` from the chain state `cv` over `Ht` (`osPosOf`). -/
def osPosOfW (depth : ℕ) (cv : Digest) (i : ℕ) : ℕ :=
  (eToNat (challengeOf (sqCvW Ht (sqAllW Ht (i / (192 / depth)) cv).2)) >>> (i % (192 / depth) * depth)) %
    2 ^ depth

end Hash

theorem obsCvW_blake : obsCvW blake2sBytes = obsCv := rfl

theorem sqCvW_blake : sqCvW blake2sBytes = sqCv := rfl

theorem obsAllW_blake : obsAllW blake2sBytes = obsAll := rfl

theorem absorbCvW_blake : absorbCvW blake2sBytes = absorbCv := rfl

theorem gcDigestW_blake : gcDigestW blake2sBytes = gcDigest := rfl

theorem sqAllW_blake : ∀ (n : ℕ) (cv : Digest), sqAllW blake2sBytes n cv = sqAll n cv
  | 0, _ => rfl
  | n + 1, cv => by rw [sqAllW, sqAll, sqAllW_blake n]; rfl

theorem fsValsW_blake (x : E) (cv : Digest) (tag k : ℕ) : fsValsW blake2sBytes x cv tag k = fsVals x cv tag k := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;> rfl

theorem sqValsW_blake (cv : Digest) (k : ℕ) : sqValsW blake2sBytes cv k = sqVals cv k := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;> rfl

theorem osPosOfW_blake (depth : ℕ) (cv : Digest) (i : ℕ) : osPosOfW blake2sBytes depth cv i = osPosOf depth cv i := by
  rw [osPosOfW, osPosOf, sqAllW_blake]; rfl

/-- The honest values of `fsCompressT` over `Ht` are those with its output the digest. -/
theorem fsValsW_eq (Ht : Bytes → Digest) (x : E) (cv : Digest) (tag : ℕ) {k : ℕ} (hk : k < 14) :
    fsValsW Ht x cv tag k = fsValsD x (absorbCvW Ht cv x tag) tag k := by
  interval_cases k <;> rfl

/-- The honest values of `squeezeT` over `Ht` are those with its output the digest. -/
theorem sqValsW_eq (Ht : Bytes → Digest) (cv : Digest) {k : ℕ} (hk : k < 14) :
    sqValsW Ht cv k = sqValsD (sqCvW Ht cv) k := by
  interval_cases k <;> rfl

/-! ## Runs over a total hash -/

/-- `Compile.run` over the hash `Ht` (`runId`). -/
abbrev runW (Ht : Bytes → Digest) {α : Type} (p : Prog α) (s : St) : Option (α × St) :=
  Compile.run (m := Id) Ht p s

/-- `p` runs from `s` to `a` and `s'` over `Ht` (`Runs`). -/
def RunsW (Ht : Bytes → Digest) {α : Type} (p : Prog α) (s : St) (a : α) (s' : St) : Prop :=
  runW Ht p s = some (a, s')

/-- `p` runs from `cv` reading exactly `xs` over `Ht` (`RunsTo`). -/
def RunsToW (Ht : Bytes → Digest) {α : Type} (p : Prog α) (cv : Digest) (xs : List E) (a : α)
    (cv' : Digest) : Prop :=
  ∀ (rest : List E) (os : List Opening) (roots : List (Digest × ℕ × ℕ)),
    runW Ht p ⟨cv, xs ++ rest, os, roots⟩ = some (a, ⟨cv', rest, os, roots⟩)

/-- `p` runs consuming exactly `xs` and `os` over `Ht` (`RunsWith`). -/
def RunsWithW (Ht : Bytes → Digest) {α : Type} (p : Prog α) (cv : Digest) (xs : List E) (os : List Opening)
    (roots : List (Digest × ℕ × ℕ)) (a : α) (cv' : Digest) (roots' : List (Digest × ℕ × ℕ)) : Prop :=
  ∀ (rest : List E) (orest : List Opening),
    runW Ht p ⟨cv, xs ++ rest, os ++ orest, roots⟩ = some (a, ⟨cv', rest, orest, roots'⟩)

theorem runsW_blake {α : Type} {p : Prog α} {s : St} {a : α} {s' : St} :
    RunsW blake2sBytes p s a s' ↔ Runs p s a s' := Iff.rfl

theorem runsToW_blake {α : Type} {p : Prog α} {cv : Digest} {xs : List E} {a : α} {cv' : Digest} :
    RunsToW blake2sBytes p cv xs a cv' ↔ RunsTo p cv xs a cv' := Iff.rfl

theorem runsWithW_blake {α : Type} {p : Prog α} {cv : Digest} {xs : List E} {os : List Opening}
    {roots : List (Digest × ℕ × ℕ)} {a : α} {cv' : Digest} {roots' : List (Digest × ℕ × ℕ)} :
    RunsWithW blake2sBytes p cv xs os roots a cv' roots' ↔ RunsWith p cv xs os roots a cv' roots' := Iff.rfl

section Runs

variable {Ht : Bytes → Digest}

theorem runW_bind {α β : Type} (p : Prog α) (f : α → Prog β) (s : St) :
    runW Ht (p.bind f) s = (runW Ht p s).bind (fun r => runW Ht (f r.1) r.2) := by
  induction p generalizing s with
  | ret a => rfl
  | fail => rfl
  | read k ih =>
    simp only [runW, Prog.bind, Compile.run]
    split
    · rfl
    · exact ih _ _
  | sample k ih => exact ih _ _
  | grind b k ih =>
    simp only [runW, Prog.bind, Compile.run]
    split
    · rfl
    · simp only [bind, pure]
      split
      · exact ih _
      · rfl
  | commit h w k ih =>
    simp only [runW, Prog.bind, Compile.run]
    split
    · simp only [bind]
      split
      · exact ih _
      · rfl
    · rfl
  | query i ps k ih =>
    simp only [runW, Prog.bind, Compile.run]
    split
    · rfl
    · simp only [bind]
      split
      · exact ih _ _
      · rfl

theorem RunsW.bind {α β : Type} {p : Prog α} {f : α → Prog β} {s s1 s2 : St} {a : α} {b : β}
    (h1 : RunsW Ht p s a s1) (h2 : RunsW Ht (f a) s1 b s2) : RunsW Ht (p >>= f) s b s2 := by
  unfold RunsW at *
  rw [prog_bind_eq, runW_bind, h1]
  exact h2

theorem RunsW.ret {α : Type} (a : α) (s : St) : RunsW Ht (Prog.ret a) s a s := rfl

theorem RunsW.bind_inv {α β : Type} {p : Prog α} {f : α → Prog β} {s s'' : St} {b : β}
    (h : RunsW Ht (p >>= f) s b s'') : ∃ a s', RunsW Ht p s a s' ∧ RunsW Ht (f a) s' b s'' := by
  unfold RunsW at *
  rw [prog_bind_eq, runW_bind] at h
  match hp : runW Ht p s, h with
  | some (a, s'), h => exact ⟨a, s', rfl, h⟩

theorem RunsToW.runs {α : Type} {p : Prog α} {cv cv' : Digest} {xs : List E} {a : α}
    (h : RunsToW Ht p cv xs a cv') (rest : List E) (os : List Opening) (roots : List (Digest × ℕ × ℕ)) :
    RunsW Ht p ⟨cv, xs ++ rest, os, roots⟩ a ⟨cv', rest, os, roots⟩ := h rest os roots

theorem runsToW_ret {α : Type} (a : α) (cv : Digest) : RunsToW Ht (pure a : Prog α) cv [] a cv :=
  fun _ _ _ => rfl

theorem RunsToW.bind {α β : Type} {p : Prog α} {f : α → Prog β} {cv cv1 cv2 : Digest}
    {xs ys : List E} {a : α} {b : β} (h1 : RunsToW Ht p cv xs a cv1) (h2 : RunsToW Ht (f a) cv1 ys b cv2) :
    RunsToW Ht (p >>= f) cv (xs ++ ys) b cv2 := by
  intro rest os roots
  rw [prog_bind_eq, runW_bind, List.append_assoc, h1]
  exact h2 rest os roots

theorem runsToW_readE (cv : Digest) (x : E) : RunsToW Ht Prog.readE cv [x] x (obsCvW Ht cv x) :=
  fun _ _ _ => rfl

theorem runsToW_sampleE (cv : Digest) :
    RunsToW Ht Prog.sampleE cv [] (challengeOf (sqCvW Ht cv)) (sqCvW Ht cv) := fun _ _ _ => rfl

theorem runsToW_readN (cv : Digest) (xs : List E) :
    RunsToW Ht (Prog.readN xs.length) cv xs xs (obsAllW Ht cv xs) := by
  induction xs generalizing cv with
  | nil => exact runsToW_ret _ _
  | cons x xs ih =>
    have h := (runsToW_readE cv x).bind (f := fun x => do let xs ← Prog.readN xs.length; return x :: xs)
      ((ih (obsCvW Ht cv x)).bind (f := fun xs => (pure (x :: xs) : Prog (List E)))
        (runsToW_ret (x :: xs) _))
    simpa [Prog.readN, obsAllW, List.foldl] using h

theorem runsToW_sampleN (n : ℕ) (cv : Digest) :
    RunsToW Ht (Prog.sampleN n) cv [] (sqAllW Ht n cv).1 (sqAllW Ht n cv).2 := by
  induction n generalizing cv with
  | zero => exact runsToW_ret _ _
  | succ n ih =>
    have h := (runsToW_sampleE cv).bind (f := fun x => do let xs ← Prog.sampleN n; return x :: xs)
      ((ih (sqCvW Ht cv)).bind (f := fun xs => (pure (challengeOf (sqCvW Ht cv) :: xs) : Prog (List E)))
        (runsToW_ret _ _))
    simpa [Prog.sampleN, sqAllW] using h

end Runs

/-! ## The query steps over a total hash -/

/-- **The query steps of a run over `Ht`** (`queriesOf`). -/
def queriesOfW (Ht : Bytes → Digest) {α : Type} : Prog α → St → List (ℕ × List (ℕ × Opening))
  | .ret _, _ => []
  | .fail, _ => []
  | .read k, s => match s.stream with
    | [] => []
    | x :: xs => queriesOfW Ht (k x)
        { s with cv := absorbBlock (m := Id) Ht s.cv (blockOf x 1), stream := xs }
  | .sample k, s =>
    let cv := absorbBlock (m := Id) Ht s.cv (blockOf 0 2)
    queriesOfW Ht (k (challengeOf cv)) { s with cv := cv }
  | .grind bits k, s => match s.stream with
    | [] => []
    | n :: xs =>
      let base := absorbBlock (m := Id) Ht s.cv (blockOf 0 3)
      let d := absorbBlock (m := Id) Ht base (blockOf n 4)
      let cv := absorbBlock (m := Id) Ht s.cv (blockOf n 4)
      if powOk bits n d then queriesOfW Ht k { s with cv := cv, stream := xs } else []
  | .commit height width k, s => match s.stream with
    | x0 :: x1 :: xs =>
      let cv0 := absorbBlock (m := Id) Ht s.cv (blockOf x0 1)
      let cv1 := absorbBlock (m := Id) Ht cv0 (blockOf x1 1)
      match digestOfScalars (x0, x1) with
      | some root =>
        queriesOfW Ht k { s with cv := cv1, stream := xs, roots := s.roots ++ [(root, height, width)] }
      | none => []
    | _ => []
  | .query i ps k, s => match s.roots[i]? with
    | none => []
    | some (root, height, width) =>
      match openAll (m := Id) Ht root height width ps s.openings with
      | some (rows, rest) => (height, ps.zip s.openings) :: queriesOfW Ht (k rows) { s with openings := rest }
      | none => []

theorem queriesOfW_blake {α : Type} : ∀ (p : Prog α) (s : St), queriesOfW blake2sBytes p s = queriesOf p s
  | .ret _, _ => rfl
  | .fail, _ => rfl
  | .read k, ⟨cv, stream, os, roots⟩ => by
    rcases stream with _ | ⟨x, xs⟩
    · rfl
    · simp only [queriesOfW, queriesOf, queriesOfW_blake]
  | .sample k, s => by simp only [queriesOfW, queriesOf, queriesOfW_blake]
  | .grind bits k, ⟨cv, stream, os, roots⟩ => by
    rcases stream with _ | ⟨n, xs⟩
    · rfl
    · simp only [queriesOfW, queriesOf, queriesOfW_blake]
  | .commit h w k, ⟨cv, stream, os, roots⟩ => by
    rcases stream with _ | ⟨x0, _ | ⟨x1, xs⟩⟩
    · rfl
    · rfl
    · simp only [queriesOfW, queriesOf]
      rcases digestOfScalars (x0, x1) with _ | root
      · rfl
      · simp only [queriesOfW_blake]
  | .query i ps k, ⟨cv, stream, os, roots⟩ => by
    simp only [queriesOfW, queriesOf]
    rcases roots[i]? with _ | ⟨root, hh, ww⟩
    · rfl
    · simp only
      rcases openAll (m := Id) blake2sBytes root hh ww ps os with _ | ⟨rows, rest⟩
      · rfl
      · simp only [queriesOfW_blake]

/-! ## Answered runs -/

/-- `openAll` over `H` answers with `Ht`'s result. -/
def OpenAns (H : Bytes → Option Digest) (Ht : Bytes → Digest) (root : Digest) (height width : ℕ)
    (ps : List ℕ) (os : List Opening) : Prop :=
  openAll (m := Option) H root height width ps os = some (openAll (m := Id) Ht root height width ps os)

/-- **An answered run**: every hash the run of `p` from `s` over `Ht` makes, `H` answers with
`Ht`'s digest (along the run's path; a rejecting step asks nothing further). -/
def AnsRun (H : Bytes → Option Digest) (Ht : Bytes → Digest) {α : Type} : Prog α → St → Prop
  | .ret _, _ => True
  | .fail, _ => True
  | .read k, s => match s.stream with
    | [] => True
    | x :: xs => H (digestBytes s.cv ++ blockOf x 1) = some (Ht (digestBytes s.cv ++ blockOf x 1)) ∧
        AnsRun H Ht (k x) { s with cv := Ht (digestBytes s.cv ++ blockOf x 1), stream := xs }
  | .sample k, s => H (digestBytes s.cv ++ blockOf 0 2) = some (Ht (digestBytes s.cv ++ blockOf 0 2)) ∧
      AnsRun H Ht (k (challengeOf (Ht (digestBytes s.cv ++ blockOf 0 2))))
        { s with cv := Ht (digestBytes s.cv ++ blockOf 0 2) }
  | .grind _bits k, s => match s.stream with
    | [] => True
    | n :: xs => H (digestBytes s.cv ++ blockOf 0 3) = some (Ht (digestBytes s.cv ++ blockOf 0 3)) ∧
        H (digestBytes (Ht (digestBytes s.cv ++ blockOf 0 3)) ++ blockOf n 4) =
          some (Ht (digestBytes (Ht (digestBytes s.cv ++ blockOf 0 3)) ++ blockOf n 4)) ∧
        H (digestBytes s.cv ++ blockOf n 4) = some (Ht (digestBytes s.cv ++ blockOf n 4)) ∧
        AnsRun H Ht k { s with cv := Ht (digestBytes s.cv ++ blockOf n 4), stream := xs }
  | .commit height width k, s => match s.stream with
    | x0 :: x1 :: xs =>
      let cv0 := Ht (digestBytes s.cv ++ blockOf x0 1)
      let cv1 := Ht (digestBytes cv0 ++ blockOf x1 1)
      H (digestBytes s.cv ++ blockOf x0 1) = some cv0 ∧ H (digestBytes cv0 ++ blockOf x1 1) = some cv1 ∧
        ∀ root, digestOfScalars (x0, x1) = some root →
          AnsRun H Ht k { s with cv := cv1, stream := xs, roots := s.roots ++ [(root, height, width)] }
    | _ => True
  | .query i ps k, s => match s.roots[i]? with
    | none => True
    | some (root, height, width) => OpenAns H Ht root height width ps s.openings ∧
        ∀ rows rest, openAll (m := Id) Ht root height width ps s.openings = some (rows, rest) →
          AnsRun H Ht (k rows) { s with openings := rest }

/-- An opening the model answers is the opening over `Ht`, answered (`climb_answered`). -/
theorem openOne_option_of {H : Bytes → Option Digest} {Ht : Bytes → Digest}
    (hHt : ∀ x d, H x = some d → d = Ht x) {root : Digest} {height width q : ℕ} {o : Opening} {b : Bool}
    (h : openOne (m := Option) H root height width q o = some b) :
    openOne (m := Option) H root height width q o = some (openOne (m := Id) Ht root height width q o) := by
  unfold openOne at h ⊢
  split
  · rename_i hc
    rw [ite_pos' hc] at h
    obtain ⟨ld, hld, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨t, ht, -⟩ := Option.bind_eq_some_iff.mp h
    have e1 := hHt _ _ hld
    subst e1
    obtain ⟨et, -⟩ := climb_answered hHt ht
    subst et
    show (H _).bind _ = _
    rw [hld, Option.bind_some]
    show (climb (m := Option) H _ q o.path).bind _ = _
    rw [ht, Option.bind_some]
    rfl
  · rfl

theorem openAll_option_of {H : Bytes → Option Digest} {Ht : Bytes → Digest}
    (hHt : ∀ x d, H x = some d → d = Ht x) {root : Digest} {height width : ℕ} :
    ∀ {ps : List ℕ} {os : List Opening} {r : Option (List (List K) × List Opening)},
      openAll (m := Option) H root height width ps os = some r → OpenAns H Ht root height width ps os
  | [], os, r, h => rfl
  | _ :: _, [], r, h => rfl
  | q :: qs, o :: os, r, h => by
    unfold OpenAns
    simp only [openAll, bind, Option.bind_eq_some_iff] at h
    obtain ⟨b, hb, h⟩ := h
    have e := openOne_option_of hHt hb
    rw [hb] at e
    have e' := Option.some.inj e
    simp only [openAll, bind, hb, Option.bind_some]
    rw [show openOne (m := Id) Ht root height width q o = b from e'.symm]
    cases b
    · rfl
    · simp only [↓reduceIte] at h ⊢
      obtain ⟨r', hr', -⟩ := Option.bind_eq_some_iff.mp h
      have ih := openAll_option_of hHt hr'
      unfold OpenAns at ih
      rw [ih]
      rfl

variable {M : HashModel} {Ht : Bytes → Digest}

/-- **A run the model answers is the run over `Ht`, answered**: with `Ht` agreeing with the model
where it answers, a run `RunsM M` is a run `RunsW Ht` with every hash answered. -/
theorem runsM_runsW (hHt : ∀ x d, M.H x = some d → d = Ht x) {α : Type} :
    ∀ (p : Prog α) {s : St} {a : α} {s' : St}, RunsM M p s a s' → RunsW Ht p s a s' ∧ AnsRun M.H Ht p s
  | .ret a0, s, a, s', h => by
    unfold RunsM at h
    simp only [runM, Compile.run, pure, Option.some.injEq] at h
    exact ⟨by rw [RunsW, ← h]; rfl, trivial⟩
  | .fail, s, a, s', h => by
    unfold RunsM at h
    simp [runM, Compile.run, pure] at h
  | .read k, ⟨cv, stream, os, roots⟩, a, s', h => by
    unfold RunsM at h
    rcases stream with _ | ⟨x, xs⟩
    · simp [runM, Compile.run, pure] at h
    · simp only [runM, Compile.run, absorbBlock, bind, Option.bind_eq_some_iff] at h
      obtain ⟨c, hc, h⟩ := h
      have e := hHt _ _ hc
      subst e
      obtain ⟨h1, h2⟩ := runsM_runsW hHt (k x) h
      exact ⟨h1, hc, h2⟩
  | .sample k, ⟨cv, stream, os, roots⟩, a, s', h => by
    unfold RunsM at h
    simp only [runM, Compile.run, absorbBlock, bind, Option.bind_eq_some_iff] at h
    obtain ⟨c, hc, h⟩ := h
    have e := hHt _ _ hc
    subst e
    obtain ⟨h1, h2⟩ := runsM_runsW hHt _ h
    exact ⟨h1, hc, h2⟩
  | .grind bits k, ⟨cv, stream, os, roots⟩, a, s', h => by
    unfold RunsM at h
    rcases stream with _ | ⟨n, xs⟩
    · simp [runM, Compile.run, pure] at h
    · simp only [runM, Compile.run, absorbBlock, bind, Option.bind_eq_some_iff] at h
      obtain ⟨c1, hc1, c2, hc2, c3, hc3, h⟩ := h
      have e1 := hHt _ _ hc1
      subst e1
      have e2 := hHt _ _ hc2
      subst e2
      have e3 := hHt _ _ hc3
      subst e3
      split at h
      · obtain ⟨h1, h2⟩ := runsM_runsW hHt k h
        refine ⟨?_, hc1, hc2, hc3, h2⟩
        unfold RunsW
        simp only [runW, Compile.run, absorbBlock, bind, ↓reduceIte, *]
        exact h1
      · simp [pure] at h
  | .commit height width k, ⟨cv, stream, os, roots⟩, a, s', h => by
    unfold RunsM at h
    match stream, h with
    | [], h => simp [runM, Compile.run, pure] at h
    | [_], h => simp [runM, Compile.run, pure] at h
    | x0 :: x1 :: xs, h =>
      simp only [runM, Compile.run, absorbBlock, bind, Option.bind_eq_some_iff] at h
      obtain ⟨c1, hc1, c2, hc2, h⟩ := h
      have e1 := hHt _ _ hc1
      subst e1
      have e2 := hHt _ _ hc2
      subst e2
      split at h
      · rename_i root hr
        obtain ⟨h1, h2⟩ := runsM_runsW hHt k h
        refine ⟨?_, hc1, hc2, fun root' hr' => ?_⟩
        · unfold RunsW
          simp only [runW, Compile.run, absorbBlock, bind, hr]
          exact h1
        · rw [hr] at hr'
          obtain rfl := Option.some.inj hr'
          exact h2
      · simp [pure] at h
  | .query i ps k, ⟨cv, stream, os, roots⟩, a, s', h => by
    unfold RunsM at h
    simp only [runM, Compile.run] at h
    split at h
    · simp [pure] at h
    · rename_i root hh ww hr
      simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨o, ho, h⟩ := h
      have hoa := openAll_option_of hHt ho
      unfold OpenAns at hoa
      rw [hoa] at ho
      obtain rfl := Option.some.inj ho
      split at h
      · rename_i rows rest hrr
        obtain ⟨h1, h2⟩ := runsM_runsW hHt _ h
        refine ⟨?_, ?_⟩
        · unfold RunsW
          simp only [runW, Compile.run]
          rw [hr]
          dsimp only [bind]
          rw [hrr]
          exact h1
        · simp only [AnsRun, hr]
          refine ⟨hoa, fun rows' rest' h' => ?_⟩
          rw [hrr] at h'
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h')
          exact h2
      · simp [pure] at h

/-- At the deployed hash, an opening answers. -/
theorem openAll_some_blake {root : Digest} {height width : ℕ} :
    ∀ (ps : List ℕ) (os : List Opening),
      OpenAns (fun x => some (blake2sBytes x)) blake2sBytes root height width ps os
  | [], os => rfl
  | _ :: _, [] => rfl
  | q :: qs, o :: os => by
    have h1 : openOne (m := Option) (fun x => some (blake2sBytes x)) root height width q o =
        some (openOne (m := Id) blake2sBytes root height width q o) := by
      unfold openOne
      split
      · simp only [bind, Option.bind_some, climb_some_blake, pure]
      · rfl
    unfold OpenAns
    simp only [openAll, bind, h1, Option.bind_some]
    cases openOne (m := Id) blake2sBytes root height width q o
    · rfl
    · simp only [↓reduceIte]
      rw [openAll_some_blake qs os]
      rfl

/-- **At the deployed model every run is answered.** -/
theorem ansRun_blake {α : Type} : ∀ (p : Prog α) (s : St), AnsRun (fun x => some (blake2sBytes x)) blake2sBytes p s
  | .ret _, _ => trivial
  | .fail, _ => trivial
  | .read k, ⟨cv, stream, os, roots⟩ => by
    rcases stream with _ | ⟨x, xs⟩
    · trivial
    · exact ⟨rfl, ansRun_blake _ _⟩
  | .sample k, s => ⟨rfl, ansRun_blake _ _⟩
  | .grind bits k, ⟨cv, stream, os, roots⟩ => by
    rcases stream with _ | ⟨n, xs⟩
    · trivial
    · exact ⟨rfl, rfl, rfl, ansRun_blake _ _⟩
  | .commit h w k, ⟨cv, stream, os, roots⟩ => by
    match stream with
    | [] => trivial
    | [_] => trivial
    | x0 :: x1 :: xs => exact ⟨rfl, rfl, fun _ _ => ansRun_blake _ _⟩
  | .query i ps k, ⟨cv, stream, os, roots⟩ => by
    simp only [AnsRun]
    split
    · trivial
    · exact ⟨openAll_some_blake _ _, fun _ _ _ => ansRun_blake _ _⟩

/-- An answered bind: the first program's run answered, and the continuation's from where it
ends. -/
theorem AnsRun.bind_inv {H : Bytes → Option Digest} {α β : Type} :
    ∀ (p : Prog α) (f : α → Prog β) {s : St} {a : α} {s' : St},
      AnsRun H Ht (p >>= f) s → RunsW Ht p s a s' → AnsRun H Ht p s ∧ AnsRun H Ht (f a) s'
  | .ret a0, f, s, a, s', h, hr => by
    unfold RunsW at hr
    simp only [runW, Compile.run, pure, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨trivial, h⟩
  | .fail, f, s, a, s', h, hr => by cases hr
  | .read k, f, ⟨cv, stream, os, roots⟩, a, s', h, hr => by
    rcases stream with _ | ⟨x, xs⟩
    · cases hr
    · obtain ⟨h1, h2⟩ := h
      obtain ⟨i1, i2⟩ := AnsRun.bind_inv (k x) f h2 hr
      exact ⟨⟨h1, i1⟩, i2⟩
  | .sample k, f, s, a, s', h, hr => by
    obtain ⟨h1, h2⟩ := h
    obtain ⟨i1, i2⟩ := AnsRun.bind_inv _ f h2 hr
    exact ⟨⟨h1, i1⟩, i2⟩
  | .grind bits k, f, ⟨cv, stream, os, roots⟩, a, s', h, hr => by
    rcases stream with _ | ⟨n, xs⟩
    · cases hr
    · obtain ⟨h1, h2, h3, h4⟩ := h
      unfold RunsW at hr
      simp only [runW, Compile.run, absorbBlock, bind, pure] at hr
      by_cases hp : powOk bits n (Ht (digestBytes (Ht (digestBytes cv ++ blockOf 0 3)) ++ blockOf n 4)) = true
      · simp only [hp, ↓reduceIte] at hr
        obtain ⟨i1, i2⟩ := AnsRun.bind_inv k f h4 hr
        exact ⟨⟨h1, h2, h3, i1⟩, i2⟩
      · simp [hp] at hr
  | .commit hh ww k, f, ⟨cv, stream, os, roots⟩, a, s', h, hr => by
    match stream, h, hr with
    | [], _, hr => cases hr
    | [_], _, hr => cases hr
    | x0 :: x1 :: xs, h, hr =>
      obtain ⟨h1, h2, h3⟩ := h
      unfold RunsW at hr
      simp only [runW, Compile.run, absorbBlock, bind] at hr
      split at hr
      · rename_i root hroot
        obtain ⟨i1, i2⟩ := AnsRun.bind_inv k f (h3 root hroot) hr
        refine ⟨⟨h1, h2, fun root' hr' => ?_⟩, i2⟩
        rw [hroot] at hr'
        obtain rfl := Option.some.inj hr'
        exact i1
      · cases hr
  | .query i ps k, f, ⟨cv, stream, os, roots⟩, a, s', h, hr => by
    unfold RunsW at hr
    simp only [runW, Compile.run] at hr
    rw [prog_bind_eq] at h
    simp only [AnsRun, Prog.bind] at h ⊢
    split at hr
    · cases hr
    · rename_i root hh ww hroot
      rw [hroot] at h ⊢
      obtain ⟨h1, h2⟩ := h
      dsimp only [bind] at hr
      split at hr
      · rename_i rows rest hrr
        obtain ⟨i1, i2⟩ := AnsRun.bind_inv _ f (h2 rows rest hrr) hr
        refine ⟨⟨h1, fun rows' rest' h' => ?_⟩, i2⟩
        rw [hrr] at h'
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h')
        exact i1
      · cases hr

end
end LeanVM.Guest.B1
