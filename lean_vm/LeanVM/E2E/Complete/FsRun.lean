/-
  LeanVM.E2E.Complete.FsRun

  The interactive run of a program at the challenges the compiled honest prover squeezes: its
  acceptance gives the compiled verifier's, and two programs that agree along it have the same
  honest proof.
-/

module

public import LeanVM.Protocol.Compile.Prover

/-!
# The run along the Fiat–Shamir challenges

The compilation's completeness (`runProof_prove`) asks the strategy to win against *every*
challenge. A program whose checks name one transcript's values (the deferring verifier's claimed
values, `Evaluations.claimed`) wins only against the challenges the compiled prover actually
squeezes. This module runs a program at those challenges:

* `fsRun H S fuel p cv h`: the strategy's moves, each challenge squeezed from the chain state as
  `proveFrom` squeezes it, each proof of work at `findNonce`'s nonce, each commitment well shaped,
  each opening from the committed words; the result with the chain state and the history;
* `run_proveFrom_fs`, `runProof_of_fsRun`: **acceptance along the run gives the compiled
  verifier's** on the honest proof (`run_proveFrom` with `fsRun` in place of `AcceptsFrom`);
* `fsRun_bind`, `proveFrom_bind_of_fsRun`: both compose along `bind`;
* `fsRun_of_acceptsFrom`: a strategy winning against every challenge wins along the run;
* `FsSame`, `fsSame_bind`: two programs with the same run and the same honest proof from a
  state, and their continuations' agreement at the state the common prefix reaches.
-/

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters LeanVM.Protocol.Blake2sHash

@[expose] public section

section FS

variable (H : Bytes → Digest) (S : Strategy) (fuel : ℕ)

open Classical in
/-- **The run along the Fiat–Shamir challenges** from the chain state `cv` and the history `h`:
the result, the chain state and the history at its end; `none` on rejection, a failed proof of
work, an ill-shaped commitment or an opening of a missing commitment. -/
noncomputable def fsRun {α : Type} : Prog α → Digest → List Ev → Option (α × Digest × List Ev)
  | .ret a, cv, h => some (a, cv, h)
  | .fail, _, _ => none
  | .read k, cv, h =>
    fsRun (k (S.msg h)) (H (digestBytes cv ++ blockOf (S.msg h) 1)) (h ++ [Ev.read (S.msg h)])
  | .sample k, cv, h =>
    fsRun (k (challengeOf (H (digestBytes cv ++ blockOf 0 2)))) (H (digestBytes cv ++ blockOf 0 2))
      (h ++ [Ev.sample (challengeOf (H (digestBytes cv ++ blockOf 0 2)))])
  | .grind bits k, cv, h => match findNonce H bits cv fuel with
    | none => none
    | some n => fsRun k (H (digestBytes cv ++ blockOf n 4)) (h ++ [Ev.grind bits])
  | .commit ht w k, cv, h =>
    if WellShaped w (S.word h) then
      fsRun k
        (H (digestBytes (H (digestBytes cv ++ blockOf (digestScalars (treeRoot H ht (S.word h))).1 1))
          ++ blockOf (digestScalars (treeRoot H ht (S.word h))).2 1))
        (h ++ [Ev.commit ht w (S.word h)])
    else none
  | .query i ps k, cv, h => match (commits h)[i]? with
    | none => none
    | some (ht, _, word) =>
      fsRun (k (ps.map fun q ↦ word (q % 2 ^ ht))) cv
        (h ++ [Ev.query (ps.map fun q ↦ word (q % 2 ^ ht))])

/-- **Acceptance along the run gives the compiled verifier's**: on any stream and openings that
start with the honest prover's, the compiled verifier accepts, leaving what follows them. -/
theorem run_proveFrom_fs :
    ∀ (p : Prog Bool) (h : List Ev) (cv : Digest) (xs : List E) (os : List Opening)
      (restS : List E) (restO : List Opening) (cv' : Digest) (h' : List Ev),
      fsRun H S fuel p cv h = some (true, cv', h') → (∀ c ∈ commits h, WellShaped c.2.1 c.2.2) →
      proveFrom H S fuel p cv h = some (xs, os) →
      ∃ s', run (m := Id) H p ⟨cv, xs ++ restS, os ++ restO, rootsOf H (commits h)⟩ =
          some (true, s') ∧ s'.stream = restS ∧ s'.openings = restO := by
  intro p
  induction p with
  | ret b =>
    intro h cv xs os restS restO cv' h' hacc _ hp
    simp only [fsRun, Option.some.injEq, Prod.mk.injEq] at hacc
    simp only [proveFrom, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    exact ⟨_, by rw [hacc.1]; rfl, rfl, rfl⟩
  | fail =>
    intro h cv xs os restS restO cv' h' hacc
    simp [fsRun] at hacc
  | read k ih =>
    intro h cv xs os restS restO cv' h' hacc hws hp
    simp only [proveFrom] at hp
    obtain ⟨t, ht, he⟩ := Option.map_eq_some_iff.mp hp
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have hws' : ∀ c ∈ commits (h ++ [Ev.read (S.msg h)]), WellShaped c.2.1 c.2.2 := by
      simpa [commits_append, commits] using hws
    obtain ⟨s', hrun, hs1, hs2⟩ := ih _ _ _ t.1 t.2 restS restO cv' h' hacc hws' ht
    refine ⟨s', ?_, hs1, hs2⟩
    rw [← hrun]
    simp [run, absorbBlock, commits_append, commits]
    rfl
  | sample k ih =>
    intro h cv xs os restS restO cv' h' hacc hws hp
    simp only [proveFrom] at hp
    have hws' : ∀ c ∈ commits (h ++ [Ev.sample (challengeOf (H (digestBytes cv ++ blockOf 0 2)))]),
        WellShaped c.2.1 c.2.2 := by
      simpa [commits_append, commits] using hws
    obtain ⟨s', hrun, hs1, hs2⟩ := ih _ _ _ xs os restS restO cv' h' hacc hws' hp
    refine ⟨s', ?_, hs1, hs2⟩
    rw [← hrun]
    simp [run, absorbBlock, commits_append, commits]
    rfl
  | grind b k ih =>
    intro h cv xs os restS restO cv' h' hacc hws hp
    simp only [proveFrom] at hp
    split at hp
    · exact absurd hp (by simp)
    · rename_i n hn
      simp only [fsRun, hn] at hacc
      obtain ⟨t, ht, he⟩ := Option.map_eq_some_iff.mp hp
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hws' : ∀ c ∈ commits (h ++ [Ev.grind b]), WellShaped c.2.1 c.2.2 := by
        simpa [commits_append, commits] using hws
      obtain ⟨s', hrun, hs1, hs2⟩ := ih _ _ t.1 t.2 restS restO cv' h' hacc hws' ht
      refine ⟨s', ?_, hs1, hs2⟩
      have hpow := powOk_of_findNonce H hn
      rw [← hrun]
      simp only [commits_append, commits, List.append_nil] at *
      simp only [run, absorbBlock, List.cons_append]
      show (if powOk b n (powDigest H cv n) = true then _ else pure none) = _
      simp only [hpow, ↓reduceIte]
  | commit ht w k ih =>
    intro h cv xs os restS restO cv' h' hacc hws hp
    simp only [fsRun] at hacc
    split at hacc
    · rename_i hw
      simp only [proveFrom] at hp
      obtain ⟨t, htt, he⟩ := Option.map_eq_some_iff.mp hp
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hws' : ∀ c ∈ commits (h ++ [Ev.commit ht w (S.word h)]), WellShaped c.2.1 c.2.2 := by
        simp only [commits_append, commits, List.mem_append, List.mem_singleton]
        rintro c (hc | rfl)
        · exact hws c hc
        · exact hw
      obtain ⟨s', hrun, hs1, hs2⟩ := ih _ _ t.1 t.2 restS restO cv' h' hacc hws' htt
      refine ⟨s', ?_, hs1, hs2⟩
      rw [← hrun]
      have hdec : digestOfScalars ((digestScalars (treeRoot H ht (S.word h))).1,
          (digestScalars (treeRoot H ht (S.word h))).2) = some (treeRoot H ht (S.word h)) :=
        digestOfScalars_digestScalars _
      have hroots : rootsOf H (commits (h ++ [Ev.commit ht w (S.word h)])) =
          rootsOf H (commits h) ++ [(treeRoot H ht (S.word h), ht, w)] := by
        simp [rootsOf, commits_append, commits]
      simp only [run, absorbBlock, List.cons_append, hdec]
      rw [hroots]
      rfl
    · exact absurd hacc (by simp)
  | query i ps k ih =>
    intro h cv xs os restS restO cv' h' hacc hws hp
    simp only [fsRun] at hacc
    simp only [proveFrom] at hp
    split at hp
    · rename_i hc
      simp [hc] at hacc
    · rename_i ht w word hc
      simp only [hc] at hacc
      obtain ⟨t, htt, he⟩ := Option.map_eq_some_iff.mp hp
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hws' : ∀ c ∈ commits (h ++ [Ev.query (ps.map fun q ↦ word (q % 2 ^ ht))]),
          WellShaped c.2.1 c.2.2 := by
        simpa [commits_append, commits] using hws
      have hw : WellShaped w word := hws _ (List.mem_of_getElem? hc)
      obtain ⟨s', hrun, hs1, hs2⟩ := ih _ _ _ t.1 t.2 restS restO cv' h' hacc hws' htt
      refine ⟨s', ?_, hs1, hs2⟩
      rw [← hrun]
      have hroot : (rootsOf H (commits h))[i]? = some (treeRoot H ht word, ht, w) := by
        simp [rootsOf, hc]
      have hopen := openAll_openingAt H hw (height := ht) ps (t.2 ++ restO)
      simp only [run, hroot, List.append_assoc]
      simp only [bind] at hopen ⊢
      rw [hopen]
      simp [commits_append, commits]

/-- **The compiled verifier accepts the honest proof** of a program the strategy wins along the
Fiat–Shamir run. -/
theorem runProof_of_fsRun (P : Prog Bool) (seed : Digest) {cv' : Digest} {h' : List Ev}
    (hacc : fsRun H S fuel P seed [] = some (true, cv', h')) {π : Proof}
    (hπ : prove H P S seed fuel = some π) : runProof (m := Id) H P seed π = true := by
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hπ
  obtain ⟨s', hrun, hs1, hs2⟩ :=
    run_proveFrom_fs H S fuel P [] seed t.1 t.2 [] [] cv' h' hacc (by simp [commits]) ht
  simp only [List.append_nil] at hrun
  simp only [runProof, bind]
  show (match run (m := Id) H P ⟨seed, t.1, t.2, rootsOf H (commits [])⟩ with
    | some (true, s) => _ | _ => _) = true
  rw [hrun]
  simp [hs1, hs2]
  rfl

/-- The run composes along `bind`. -/
theorem fsRun_bind {α β : Type} (f : α → Prog β) :
    ∀ (p : Prog α) (cv : Digest) (h : List Ev),
      fsRun H S fuel (p.bind f) cv h =
        (fsRun H S fuel p cv h).bind fun r ↦ fsRun H S fuel (f r.1) r.2.1 r.2.2
  | .ret a, cv, h => rfl
  | .fail, cv, h => rfl
  | .read k, cv, h => fsRun_bind f (k _) _ _
  | .sample k, cv, h => fsRun_bind f (k _) _ _
  | .grind b k, cv, h => by
    simp only [Prog.bind, fsRun]
    split
    · rfl
    · exact fsRun_bind f k _ _
  | .commit ht w k, cv, h => by
    simp only [Prog.bind, fsRun]
    split
    · exact fsRun_bind f k _ _
    · rfl
  | .query i ps k, cv, h => by
    simp only [Prog.bind, fsRun]
    split
    · rfl
    · exact fsRun_bind f (k _) _ _

/-- The honest proof composes along `bind`, at the state the prefix's run reaches. -/
theorem proveFrom_bind_of_fsRun {α β : Type} (f : α → Prog β) :
    ∀ (p : Prog α) (cv : Digest) (h : List Ev) {a : α} {cv' : Digest} {h' : List Ev},
      fsRun H S fuel p cv h = some (a, cv', h') →
      proveFrom H S fuel (p.bind f) cv h =
        (proveFrom H S fuel p cv h).bind fun t ↦
          (proveFrom H S fuel (f a) cv' h').map fun t' ↦ (t.1 ++ t'.1, t.2 ++ t'.2)
  | .ret a, cv, h, a', cv', h', hr => by
    simp only [fsRun, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl, rfl⟩ := hr
    simp only [Prog.bind, proveFrom, Option.bind_some, List.nil_append]
    cases proveFrom H S fuel (f a) cv h <;> rfl
  | .fail, cv, h, _, _, _, hr => by simp [fsRun] at hr
  | .read k, cv, h, a, cv', h', hr => by
    simp only [Prog.bind, proveFrom]
    rw [proveFrom_bind_of_fsRun f (k _) _ _ hr]
    cases proveFrom H S fuel (k (S.msg h)) _ _ <;> simp [Function.comp_def]
  | .sample k, cv, h, a, cv', h', hr => proveFrom_bind_of_fsRun f (k _) _ _ hr
  | .grind b k, cv, h, a, cv', h', hr => by
    simp only [fsRun] at hr
    simp only [Prog.bind, proveFrom]
    split
    · rfl
    · rename_i n hn
      simp only [hn] at hr
      rw [proveFrom_bind_of_fsRun f k _ _ hr]
      cases proveFrom H S fuel k _ _ <;> simp [Function.comp_def]
  | .commit ht w k, cv, h, a, cv', h', hr => by
    simp only [fsRun] at hr
    split at hr
    · simp only [Prog.bind, proveFrom]
      rw [proveFrom_bind_of_fsRun f k _ _ hr]
      cases proveFrom H S fuel k _ _ <;> simp [Function.comp_def]
    · simp at hr
  | .query i ps k, cv, h, a, cv', h', hr => by
    simp only [fsRun] at hr
    simp only [Prog.bind, proveFrom]
    split
    · rename_i hc
      simp [hc] at hr
    · rename_i ht w word hc
      simp only [hc] at hr
      rw [proveFrom_bind_of_fsRun f (k _) _ _ hr]
      cases proveFrom H S fuel (k _) _ _ <;> simp [Function.comp_def, List.append_assoc]

/-- **A strategy winning against every challenge wins along the Fiat–Shamir run**, when every
proof of work finds its nonce. -/
theorem fsRun_of_acceptsFrom :
    ∀ (p : Prog Bool) (cv : Digest) (h : List Ev), S.AcceptsFrom p h →
      proveFrom H S fuel p cv h ≠ none → ∃ cv' h', fsRun H S fuel p cv h = some (true, cv', h')
  | .ret b, cv, h, hacc, _ => ⟨cv, h, by simp only [Strategy.AcceptsFrom] at hacc; rw [hacc]; rfl⟩
  | .fail, _, _, hacc, _ => absurd hacc id
  | .read k, cv, h, hacc, hp => by
    simp only [proveFrom, ne_eq, Option.map_eq_none_iff] at hp
    exact fsRun_of_acceptsFrom (k _) _ _ hacc hp
  | .sample k, cv, h, hacc, hp => fsRun_of_acceptsFrom (k _) _ _ (hacc _) hp
  | .grind b k, cv, h, hacc, hp => by
    simp only [proveFrom] at hp
    simp only [fsRun]
    split
    · rename_i hn
      simp [hn] at hp
    · rename_i n hn
      simp only [hn, ne_eq, Option.map_eq_none_iff] at hp
      exact fsRun_of_acceptsFrom k _ _ hacc hp
  | .commit ht w k, cv, h, hacc, hp => by
    obtain ⟨hw, hacc⟩ := hacc
    simp only [proveFrom, ne_eq, Option.map_eq_none_iff] at hp
    simp only [fsRun, hw, ↓reduceIte]
    exact fsRun_of_acceptsFrom k _ _ hacc hp
  | .query i ps k, cv, h, hacc, hp => by
    obtain ⟨rows, hans, hacc⟩ := hacc
    simp only [fsRun]
    split
    · rename_i hc
      simp [answer, hc] at hans
    · rename_i ht w word hc
      have hrows : rows = ps.map fun q ↦ word (q % 2 ^ ht) := by
        simp only [answer, hc, Option.map_some, Option.some.injEq] at hans
        exact hans.symm
      subst hrows
      simp only [proveFrom, hc, ne_eq, Option.map_eq_none_iff] at hp
      exact fsRun_of_acceptsFrom (k _) _ _ hacc hp

/-! ## Agreement along the run -/

/-- **Two programs agree from a state**: the same run along the Fiat–Shamir challenges and the
same honest proof. -/
def FsSame {α : Type} (p q : Prog α) (cv : Digest) (h : List Ev) : Prop :=
  fsRun H S fuel p cv h = fsRun H S fuel q cv h ∧ proveFrom H S fuel p cv h = proveFrom H S fuel q cv h

/-- A program agrees with itself. -/
theorem fsSame_refl {α : Type} (p : Prog α) (cv : Digest) (h : List Ev) : FsSame H S fuel p p cv h :=
  ⟨rfl, rfl⟩

/-- **Agreement composes along `bind`**: a common prefix whose run reaches a state, and
continuations agreeing from it at its result. -/
theorem fsSame_bind {α β : Type} {p : Prog α} {f g : α → Prog β} {cv : Digest} {h : List Ev}
    {a : α} {cv' : Digest} {h' : List Ev} (hp : fsRun H S fuel p cv h = some (a, cv', h'))
    (hfg : FsSame H S fuel (f a) (g a) cv' h') : FsSame H S fuel (p.bind f) (p.bind g) cv h := by
  refine ⟨?_, ?_⟩
  · rw [fsRun_bind, fsRun_bind, hp, Option.bind_some, Option.bind_some, hfg.1]
  · rw [proveFrom_bind_of_fsRun H S fuel f p cv h hp, proveFrom_bind_of_fsRun H S fuel g p cv h hp,
      hfg.2]

/-- Agreement from programs that are equal. -/
theorem fsSame_of_eq {α : Type} {p q : Prog α} (e : p = q) (cv : Digest) (h : List Ev) :
    FsSame H S fuel p q cv h := e ▸ fsSame_refl H S fuel p cv h

end FS

end
end LeanVM.Protocol.Compile
