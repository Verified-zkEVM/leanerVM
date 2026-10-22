/-
  LeanVM.E2E.Knowledge.Node

  What V_I's acceptance gives, every hash answered by a log: the closure of the nodes it checked,
  and at each node, the word, its tree and its candidates' runs, table checks and children.
-/

module

public import LeanVM.E2E.Knowledge.Word

/-!
# V_I's acceptance, unfolded

V_I (`idealVerify`, `LeanVM/E2E/Statement.lean`) runs in any monad; with the hash `look ℓ` in
`Option` (every hash answered by the log), its acceptance unfolds into facts about the log.

* **The closure** (`closure_checked`): an accepted closure from the root has checked a set of
  nodes containing the root and the children of each of its nodes (`ν ∈ done` skips a node
  already checked; a node's children are queued). Neither the fuel nor cycles matter here: an
  accepted closure finished.
* **A node** (`nodeStep_some`): its announced sizes, its stack root, the partial word under
  it, well shaped, whose partial tree the log answers with that root; the word is full or has a
  candidate satisfying the relation without Flock (E2E-10); every candidate satisfying the relation
  without Flock runs under the Flock-blind semantics, passes the table check, and each child its
  memory decodes is a node, under the digest of its statement.
* **The table check** (`tableOK_of_tableOKWith`): an accepted table check is `TableOK`.
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom

@[expose] public section

section Closure

variable {H : Bytes → Option Digest} {prog : Program} {seed : Digest} {ip : IdealProof}

/-- **An accepted closure has checked a closed set of nodes**: a set containing the nodes to do
and the nodes done, each of whose nodes not done was checked, with its children in the set. -/
theorem closure_checked :
    ∀ (fuel : ℕ) (todo done : List Node), closure H prog seed ip fuel todo done = some true →
      ∃ D : List Node, (∀ ν ∈ todo, ν ∈ D) ∧ (∀ ν ∈ done, ν ∈ D) ∧
        ∀ ν ∈ D, ν ∉ done → ∃ kids, nodeStep H prog seed ip ν = some (some kids) ∧
          ∀ κ ∈ kids, κ ∈ D
  | _, [], done, _ => ⟨done, by simp, fun _ h ↦ h, fun _ h h' ↦ absurd h h'⟩
  | 0, _ :: _, _, h => by simp [closure] at h
  | fuel + 1, ν :: todo, done, h => by
    unfold closure at h
    split at h
    · rename_i hν
      obtain ⟨D, htodo, hdone, hD⟩ := closure_checked fuel todo done h
      refine ⟨D, fun μ hμ ↦ ?_, hdone, hD⟩
      rcases List.mem_cons.mp hμ with rfl | hμ
      · exact hdone _ hν
      · exact htodo μ hμ
    · rename_i hν
      simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨o, ho, h⟩ := h
      rcases o with _ | kids
      · simp [pure] at h
      · obtain ⟨D, htodo, hdone, hD⟩ := closure_checked fuel (todo ++ kids) (ν :: done) h
        refine ⟨D, fun μ hμ ↦ ?_, fun μ hμ ↦ hdone μ (List.mem_cons_of_mem _ hμ),
          fun μ hμ hμd ↦ ?_⟩
        · rcases List.mem_cons.mp hμ with rfl | hμ
          · exact hdone _ List.mem_cons_self
          · exact htodo μ (List.mem_append_left _ hμ)
        · by_cases he : μ = ν
          · subst he
            exact ⟨kids, ho, fun κ hκ ↦ htodo κ (List.mem_append_right _ hκ)⟩
          · exact hD μ hμ (by simp [he, hμd])

end Closure

/-! ## The loops of a node -/

section Loops

/-- **The candidates' loop** of `nodeStep`, abstractly: a body whose early exits carry
`some none` and whose steps carry `none` and extend the children. An exit-free run ends with
`none`, and then every element took a step, its children a prefix of the final ones. -/
theorem forIn_candidates {α γ : Type} (L : List α)
    (f : α → Option γ × List Node → Option (ForInStep (Option γ × List Node)))
    {bad : γ} (hdone : ∀ a st st', f a st = some (.done st') → st'.1 = some bad)
    (hyield : ∀ a st st', f a st = some (.yield st') → st'.1 = none ∧ st.2 <+: st'.2) :
    ∀ (k0 kf : List Node) (r : Option γ), forIn L (none, k0) f = some (r, kf) →
      (r = none ∨ r = some bad) ∧
        (r = none → k0 <+: kf ∧
          ∀ a ∈ L, ∃ k k', f a (none, k) = some (.yield (none, k')) ∧ k' <+: kf) := by
  induction L with
  | nil =>
    intro k0 kf r h
    simp only [List.forIn_nil, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨Or.inl rfl, fun _ ↦ ⟨List.prefix_refl _, by simp⟩⟩
  | cons a L ih =>
    intro k0 kf r h
    rw [List.forIn_cons] at h
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨step, hstep, h⟩ := h
    rcases step with st' | st'
    · simp only [Option.pure_def, Option.some.injEq] at h
      subst h
      have hb : r = some bad := hdone a _ _ hstep
      exact ⟨Or.inr hb, fun hr ↦ absurd (hb.symm.trans hr) (by simp)⟩
    · obtain ⟨h1, hpre⟩ := hyield a _ _ hstep
      obtain ⟨r', k1⟩ := st'
      simp only at h1 hpre
      subst h1
      obtain ⟨hr, hrest⟩ := ih k1 kf r h
      refine ⟨hr, fun hn ↦ ?_⟩
      obtain ⟨hk1, hall⟩ := hrest hn
      refine ⟨hpre.trans hk1, fun b hb ↦ ?_⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨k0, k1, hstep, hk1⟩
      · exact hall b hb

/-- **The children's loop** of `nodeStep`: each child queued under its statement's answered
digest. -/
theorem forIn_children {H : Bytes → Option Digest} {seed : Digest} :
    ∀ (cs : List Node.Child) (k k' : List Node),
      (forIn cs k fun c (kids : List Node) ↦ (Node.statementDigestWith H seed c.statement).bind
          fun pc ↦ pure (ForInStep.yield (kids ++ [(pc, c.proof)]))) = some k' →
        k <+: k' ∧ ∀ c ∈ cs, ∃ pc, Node.statementDigestWith H seed c.statement = some pc ∧
          (pc, c.proof) ∈ k'
  | [], k, k', h => by
    simp only [List.forIn_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact ⟨List.prefix_refl _, by simp⟩
  | c :: cs, k, k', h => by
    rw [List.forIn_cons] at h
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨step, hstep, h⟩ := h
    obtain ⟨pc, hpc, hstep⟩ := hstep
    simp only [Option.pure_def, Option.some.injEq] at hstep
    subst hstep
    obtain ⟨hk, hall⟩ := forIn_children cs _ k' h
    refine ⟨(List.prefix_append _ _).trans hk, fun c' hc' ↦ ?_⟩
    rcases List.mem_cons.mp hc' with rfl | hc'
    · exact ⟨pc, hpc, hk.subset (List.mem_append_right _ (List.mem_singleton_self _))⟩
    · exact hall c' hc'

end Loops

/-! ## The table check -/

section Table

/-- An `Option` conjunction over a list that holds holds of every element. -/
theorem allM_some_true {α : Type} {f : α → Option Bool} :
    ∀ {l : List α}, l.allM f = some true → ∀ a ∈ l, f a = some true
  | [], _, a, ha => absurd ha List.not_mem_nil
  | b :: l, h, a, ha => by
    rw [List.allM_cons] at h
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, h⟩ := h
    cases x
    · simp [pure] at h
    · rcases List.mem_cons.mp ha with rfl | ha
      · exact hx
      · exact allM_some_true h a ha

/-- **An accepted table check is `TableOK`**: every standard chain among the rows ends at the
log's answer for its string. -/
theorem tableOK_of_tableOKWith {H : Bytes → Option Digest} {rows : List BlakeRow}
    (h : tableOKWith H rows = some true) : TableOK H rows := by
  unfold tableOKWith at h
  split at h
  · split at h
    · rename_i hfin
      intro x c hc hmem hstd
      have hx : x ∈ hfin.toFinset.toList := by
        rw [Finset.mem_toList, Set.Finite.mem_toFinset]
        exact ⟨c, hc, hmem, hstd⟩
      have := allM_some_true h x hx
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq,
        decide_eq_true_eq] at this
      obtain ⟨d, hd, hends⟩ := this
      rw [hd, hends c hc hmem hstd]
    · simp [pure] at h
  · simp [pure] at h

end Table

/-! ## A node -/

section Node

variable {H : Bytes → Option Digest} {prog : Program} {seed : Digest} {ip : IdealProof}

/-- **What V_I checked at a node**, every hash answered by `H`: the announced sizes and rate, the
stack root, the partial word the idealized proof gives it, well shaped, whose partial tree `H`
answers with that root, full or with a candidate satisfying the relation without Flock; the
candidates satisfying the relation without Flock are finitely many, and each runs
under the Flock-blind semantics, passes the table check, and has each child its memory decodes
(under its table's semantics, at the frames the idealized proof names for the node) among the
node's children, under its statement's answered digest. -/
theorem nodeStep_some {pi : Digest} {π : Proof} {kids : List Node}
    (h : nodeStep H prog seed ip (pi, π) = some (some kids)) :
    ∃ (layout : Verifier.Layout) (ρ : ℕ) (s : LeanIsa.Sizes) (r : E × E) (ht w : ℕ) (P : PWord)
      (root : Digest),
      Verifier.announced (bytecodeWords prog) π.stream = some (layout, ρ) ∧
      sizesOf prog layout = some s ∧ stackRoot π = some r ∧ stackShape layout ρ = some (ht, w) ∧
      ip.word (pi, π) = some P ∧ WellShaped w P.word ∧ pTreeRootM H ht P = some root ∧
      digestScalars root = r ∧ (P.Full ht ∨ ∃ q, q ∈ blindCandidatesS prog s ρ ht pi P) ∧
      ∀ q ∈ blindCandidatesS prog s ρ ht pi P, ∃ t, candidateRun prog s q = some t ∧
        tableOKWith H (t.blakeRows blakeFree) = some true ∧
        ∀ c ∈ (Guest.End.decodeAt (Guest.Value.tableSem (t.blakeRows blakeFree)) (ip.frames (pi, π))
            t.image).witness.children,
          ∃ pc, Node.statementDigestWith H seed c.statement = some pc ∧ (pc, c.proof) ∈ kids := by
  unfold nodeStep at h
  dsimp only at h
  split at h
  · rename_i layout ρ hann
    split at h
    · rename_i s hs
      split at h
      · rename_i r hr
        split at h
        · rename_i ht w hsh
          split at h
          · rename_i P hW
            split at h
            · simp [pure] at h
            · rename_i hws
              simp only [bind, Option.bind_eq_some_iff] at h
              obtain ⟨root, hroot, h⟩ := h
              split at h
              · simp [pure] at h
              · rename_i hrr
                split at h
                · simp [pure] at h
                rename_i hne
                have hne' : P.Full ht ∨ ∃ q, q ∈ blindCandidatesS prog s ρ ht pi P := by
                  by_cases hF : P.Full ht
                  · exact Or.inl hF
                  · refine Or.inr (Set.nonempty_iff_ne_empty.mpr fun he ↦ hne ⟨he, hF⟩)
                rw [Option.bind_eq_some_iff] at h
                obtain ⟨⟨r', kf⟩, hfor, h⟩ := h
                obtain ⟨hr', hall⟩ : _ ∧ _ := by
                  refine forIn_candidates (bad := none) _ _ ?_ ?_ [] kf r' hfor
                  · intro q st st' hq
                    split at hq
                    · rw [Option.bind_eq_some_iff] at hq
                      obtain ⟨b, -, hq⟩ := hq
                      split at hq
                      · simp only [pure, Option.some.injEq, ForInStep.done.injEq] at hq
                        rw [← hq]
                      · rw [Option.bind_eq_some_iff] at hq
                        obtain ⟨_, -, hq⟩ := hq
                        simp [pure] at hq
                    · simp only [pure, Option.some.injEq, ForInStep.done.injEq] at hq
                      rw [← hq]
                  · intro q st st' hq
                    split at hq
                    · rw [Option.bind_eq_some_iff] at hq
                      obtain ⟨b, -, hq⟩ := hq
                      split at hq
                      · simp [pure] at hq
                      · rw [Option.bind_eq_some_iff] at hq
                        obtain ⟨k'', hk'', hq⟩ := hq
                        simp only [pure, Option.some.injEq, ForInStep.yield.injEq] at hq
                        rw [← hq]
                        exact ⟨rfl, (forIn_children _ _ _ hk'').1⟩
                    · simp [pure] at hq
                rcases hr' with rfl | rfl
                · simp only [pure, Option.some.injEq] at h
                  subst h
                  obtain ⟨-, hall⟩ := hall rfl
                  refine ⟨layout, ρ, s, r, ht, w, P, root, hann, hs, hr, hsh, hW,
                    not_not.mp hws, hroot, not_not.mp hrr, hne', fun q hq ↦ ?_⟩
                  have hq' :
                      q ∈ (Set.toFinite (blindCandidatesS prog s ρ ht pi P)).toFinset.toList := by
                    rw [Finset.mem_toList, Set.Finite.mem_toFinset]
                    exact hq
                  obtain ⟨k, k', hstep, hk'⟩ := hall q hq'
                  dsimp only at hstep
                  split at hstep
                  · rename_i t ht
                    rw [Option.bind_eq_some_iff] at hstep
                    obtain ⟨b, hb, hstep⟩ := hstep
                    cases b
                    · simp [pure] at hstep
                    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                        Option.bind_eq_some_iff, pure, Option.some.injEq] at hstep
                      obtain ⟨k'', hk'', hst⟩ := hstep
                      cases hst
                      obtain ⟨-, hch⟩ := forIn_children _ _ _ hk''
                      refine ⟨t, ht, hb, fun c hc ↦ ?_⟩
                      obtain ⟨pc, hpc, hmem⟩ := hch c hc
                      exact ⟨pc, hpc, hk'.subset hmem⟩
                  · simp [pure] at hstep
                · simp [pure] at h
          · simp [pure] at h
        · simp [pure] at h
      · simp [pure] at h
    · simp [pure] at h
  · simp [pure] at h

end Node

end
end LeanVM.E2E
