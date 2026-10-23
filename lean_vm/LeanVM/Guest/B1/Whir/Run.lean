/-
  LeanVM.Guest.B1.Whir.Run

  Runs of the stacked opening's Spec programs on the carried sponge, with openings and
  commitments: `RunsWith` composes, the reads, samples, commitments and queries are its steps,
  and `whirLevelsOpen` is split into a level's pieces.
-/

module

public import LeanVM.Guest.B1.Common.Run
public import LeanVM.Guest.B1.Whir.Interface

/-!
# Runs of the stacked opening (TRIAGE G #42)

The Spec's side of `open_stacked`, no guest value in it.

* `RunsTo.withRoots`, `RunsWith.bind`, `runsWith_ret`: `RunsTo` (`B1/Common/Sponge.lean`) is a
  `RunsWith` reading no opening; runs compose.
* `runsWith_commitP`: a commitment reads the root's two scalars (absorbed with `dsObserve`) and
  appends the root with its shape; `runsWith_queryP`: a query consumes one opening per position,
  each passing `openOne` (V:501) against the commitment's root, and returns their leaves.
* `levelMid`, `levelQueries`, `whirLevelsOpen_cons`: a level of `whirLevelsOpen` (V:1732) is its
  fold rounds, its claims after them (the residual, or the next commitment with its
  out-of-domain claim), its queries and their glue, then the next level or the tail.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Composing runs -/

/-- A run reading no opening, at any commitments. -/
theorem RunsTo.withRoots {α : Type} {p : Prog α} {s s' : Fs} {xs : List E} {a : α}
    (h : RunsTo p s xs a s') (roots : List (Digest × ℕ × ℕ)) : RunsWith p s xs [] roots a s' roots :=
  fun sp hs rest orest ↦ h sp hs rest ([] ++ orest) roots

theorem runsWith_ret {α : Type} (a : α) (s : Fs) (roots : List (Digest × ℕ × ℕ)) :
    RunsWith (pure a : Prog α) s [] [] roots a s roots :=
  fun sp h _ _ ↦ ⟨sp, h, rfl⟩

theorem RunsWith.bind {α β : Type} {p : Prog α} {f : α → Prog β} {s s1 s2 : Fs}
    {xs ys : List E} {os1 os2 : List Opening} {r0 r1 r2 : List (Digest × ℕ × ℕ)} {a : α} {b : β}
    (h1 : RunsWith p s xs os1 r0 a s1 r1) (h2 : RunsWith (f a) s1 ys os2 r1 b s2 r2) :
    RunsWith (p >>= f) s (xs ++ ys) (os1 ++ os2) r0 b s2 r2 := by
  intro sp hs rest orest
  obtain ⟨sp1, hs1, e1⟩ := h1 sp hs (ys ++ rest) (os2 ++ orest)
  obtain ⟨sp2, hs2, e2⟩ := h2 sp1 hs1 rest orest
  refine ⟨sp2, hs2, ?_⟩
  rw [prog_bind_eq, run_bind, List.append_assoc, List.append_assoc, e1]
  exact e2

/-- `RunsTo.bind` on `Prog.bind`. -/
theorem RunsTo.bind' {α β : Type} {p : Prog α} {f : α → Prog β} {s s1 s2 : Fs} {xs ys : List E}
    {a : α} {b : β} (h1 : RunsTo p s xs a s1) (h2 : RunsTo (f a) s1 ys b s2) :
    RunsTo (p.bind f) s (xs ++ ys) b s2 := RunsTo.bind h1 h2

/-- `RunsWith.bind` on `Prog.bind`. -/
theorem RunsWith.bind' {α β : Type} {p : Prog α} {f : α → Prog β} {s s1 s2 : Fs}
    {xs ys : List E} {os1 os2 : List Opening} {r0 r1 r2 : List (Digest × ℕ × ℕ)} {a : α} {b : β}
    (h1 : RunsWith p s xs os1 r0 a s1 r1) (h2 : RunsWith (f a) s1 ys os2 r1 b s2 r2) :
    RunsWith (p.bind f) s (xs ++ ys) (os1 ++ os2) r0 b s2 r2 := RunsWith.bind h1 h2

theorem RunsWith.of_eq {α : Type} {p : Prog α} {s s' t t' : Fs} {xs xs' : List E}
    {os os' : List Opening} {r r' q q' : List (Digest × ℕ × ℕ)} {a a' : α}
    (h : RunsWith p s xs os r a t q) (hs : s = s') (hx : xs = xs') (ho : os = os') (hr : r = r')
    (ha : a = a') (ht : t = t') (hq : q = q') : RunsWith p s' xs' os' r' a' t' q' := by
  subst hs hx ho hr ha ht hq; exact h

/-! ## Commitments and queries -/

/-- **A commitment** reads the root's two scalars, absorbs them, and appends the root with its
shape. -/
theorem runsWith_commitP (s : Fs) (x0 x1 : E) {d : Digest} (hd : digestOfScalars (x0, x1) = some d)
    (height width : ℕ) (roots : List (Digest × ℕ × ℕ)) :
    RunsWith (Prog.commitP height width) s [x0, x1] [] roots ()
      ((s.absorb x0 dsObserve).absorb x1 dsObserve) (roots ++ [(d, height, width)]) := by
  intro sp hs rest orest
  have h1 := carries_absorb hs x0 dsObserve
  have h2 := carries_absorb h1 x1 dsObserve
  refine ⟨_, h2, ?_⟩
  show (match digestOfScalars (x0, x1) with
    | some root => runId (Prog.ret ()) _
    | none => none) = _
  rw [hd]
  rfl

/-- Every opening passes `openAll`: their leaves, the rest of the openings. -/
theorem openAll_eq (root : Digest) (height width : ℕ) :
    ∀ (ps : List ℕ) (os : List Opening) (orest : List Opening), os.length = ps.length →
      (∀ k (hk : k < ps.length) (ho : k < os.length),
        Id.run (Compile.openOne (m := Id) keccak256 root height width ps[k] os[k]) = true) →
      Id.run (Compile.openAll (m := Id) keccak256 root height width ps (os ++ orest)) =
        some (os.map (·.leaf), orest)
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h
  | q :: qs, o :: os, orest, hl, hok => by
    have h0 := hok 0 (by simp) (by simp)
    simp only [List.getElem_cons_zero] at h0
    have ih := openAll_eq root height width qs os orest (by simpa using hl)
      (fun k hk ho ↦ hok (k + 1) (by simpa using hk) (by simpa using ho))
    simp only [List.cons_append, Compile.openAll, Id.run] at h0 ih ⊢
    simp only [bind, h0, ↓reduceIte, ih, Option.map_some, List.map_cons]
    rfl

/-- **A query** consumes one opening per position, each passing `openOne` against commitment
`i`'s root, and returns their leaves. -/
theorem runsWith_queryP (s : Fs) (roots : List (Digest × ℕ × ℕ)) {i : ℕ} {root : Digest}
    {height width : ℕ} (hi : roots[i]? = some (root, height, width)) (ps : List ℕ)
    (os : List Opening) (hl : os.length = ps.length)
    (hok : ∀ k (hk : k < ps.length) (ho : k < os.length),
      Id.run (Compile.openOne (m := Id) keccak256 root height width ps[k] os[k]) = true) :
    RunsWith (Prog.queryP i ps) s [] os roots (os.map (·.leaf)) s roots := by
  intro sp hs rest orest
  refine ⟨sp, hs, ?_⟩
  have := openAll_eq root height width ps os orest hl hok
  simp only [Id.run] at this
  simp only [runId, Prog.queryP, Compile.run, hi, List.nil_append, bind, this]
  rfl

/-! ## A level of `whirLevelsOpen` -/

/-- A level's claims after its folds (V:1739-1751): the residual at the last level, otherwise the
next commitment and its out-of-domain claim. -/
def levelMid (messageLog : ℕ) : List Whir.Level →
    Prog (List E × List (E × List E × (List E → E)))
  | [] => do
    let residual ← Prog.readN (2 ^ messageLog)
    pure (residual, ([] : List (E × List E × (List E → E))))
  | next :: _ => do
    let (height, width) := levelShape messageLog next (3 * 2 ^ next.fold)
    Prog.commitP height width
    let oodPoint ← Prog.sampleN messageLog
    let oodValue ← Prog.readE
    let intro ← sumcheckRoundPoly 3 oodValue none
    pure ([], [(oodValue, intro, fun x ↦ eqEval oodPoint x)])

/-- A level's proof of work, queries and glue (V:1752-1764), after its folds and its claims. -/
def levelQueries (messageLog index : ℕ) (level : Whir.Level) (levelFolds : List E)
    (s : WhirState) (pending : List (E × List E × (List E → E))) : Prog WhirState := do
  Prog.grindP Whir.queryGrindingBits
  let queries ← sampleQueries (messageLog + level.logInvRate) level.queries
  let lam ← Prog.sampleE
  let queryWeights := powers lam queries.length
  let words ← Prog.queryP index queries
  let rows : List (List E) :=
    if index = 0 then words.map fun row ↦ row.reverse.map ofK else words.map extRow
  let enforced := enforcedSum rows levelFolds queryWeights
  let intro ← sumcheckRoundPoly 3 enforced none
  return glue lam s (pending ++
    [(enforced, intro, fun x ↦ inducedWeight messageLog queries queryWeights x)])

/-- The last level's tail (V:1765-1774), from its glued state and its residual. -/
def levelTail (laneFolds messageLog : ℕ) (residual : List E) (s : WhirState) : Prog WhirEnd := do
  let (tailFolds, target) ← tailRounds messageLog s.target s.quad
  let point := s.folds ++ tailFolds
  let inner := s.glued.foldl
    (fun weight claim ↦
      weight + claim.scalar * claim.weightAt (s.folds.drop claim.foldStart ++ tailFolds)) 0
  return ⟨point.drop laneFolds ++ point.take laneFolds, inner,
    multilinearEval residual tailFolds, target⟩

/-- **A level of `whirLevelsOpen`**: its folds, its claims, its queries and glue, then the tail
(the last level) or the next level. -/
theorem whirLevelsOpen_cons (logN laneFolds index : ℕ) (level : Whir.Level)
    (rest : List Whir.Level) (s : WhirState) :
    whirLevelsOpen logN laneFolds index (level :: rest) s = (do
      let (s, levelFolds) ← foldRounds level.fold s []
      let messageLog := logN - s.folds.length
      let (residual, pending) ← levelMid messageLog rest
      let s ← levelQueries messageLog index level levelFolds s pending
      match rest with
      | [] => levelTail laneFolds messageLog residual s
      | _ :: _ => whirLevelsOpen logN laneFolds (index + 1) rest s) := by
  rw [whirLevelsOpen]
  rcases rest with _ | ⟨next, rest⟩ <;>
    simp only [levelMid, levelQueries, levelTail, Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc,
      Prog.ret_bind]

end
end LeanVM.Guest.B1.Whir
