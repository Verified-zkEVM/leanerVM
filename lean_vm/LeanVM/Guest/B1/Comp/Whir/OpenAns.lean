/-
  LeanVM.Guest.B1.Comp.Whir.OpenAns

  The openings a completeness model answers: each opened leaf's hash and each level of its path,
  what `oqIter_holdsC` takes of a query.
-/

module

public import LeanVM.Guest.B1.Comp.Whir.RunW

/-!
# Answered openings (TRIAGE #28, #35)

`openOne_answered`: an opening the model accepts (`openOne` at `Option` over `H`) has a leaf and a
path of the commitment's shape, the model answers its leaf's bytes by `Ht`'s digest
(`hashWordsW`), each level of its climb by the next node (`climbLvlBytes`, `climbAtW`), and the
climb over `Ht` reaches the root. `openAll_answered`: so does every opening of an accepted
`openAll`, with its position; these are `oqIter_holdsC`'s `hleafA` and `hpathA`.
`sqAllM_steps`: `k` answered squeezes answer each one from the state over `Ht` before it, what
`sqIter_holdsC` takes of an iteration of the squeeze loop.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {H : Bytes → Option Digest} {Ht : Bytes → Digest}

/-- What the model answers of an opening it accepts. -/
def OpeningAns (H : Bytes → Option Digest) (Ht : Bytes → Digest) (root : Digest) (height width q : ℕ)
    (o : Opening) : Prop :=
  o.leaf.length = width ∧ o.path.length = height ∧
    H (o.leaf.flatMap kBytes) = some (hashWordsW Ht o.leaf) ∧
    (∀ l < o.path.length, H (climbLvlBytes Ht (hashWordsW Ht o.leaf) q o.path l) =
      some (climbAtW Ht (hashWordsW Ht o.leaf) q o.path (l + 1))) ∧
    (climb (m := Id) Ht (hashWordsW Ht o.leaf) q o.path).toList = root.toList

/-- **An opening the model accepts is answered.** -/
theorem openOne_answered (hHt : ∀ x d, H x = some d → d = Ht x) {root : Digest} {height width q : ℕ}
    {o : Opening} (h : openOne (m := Option) H root height width q o = some true) :
    OpeningAns H Ht root height width q o := by
  unfold openOne at h
  split at h
  · rename_i hc
    obtain ⟨ld, hld, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.mp h
    have e1 := hHt _ _ hld
    subst e1
    obtain ⟨et, hl⟩ := climb_answered hHt ht
    subst et
    have hd : decide ((climb (m := Id) Ht (Ht (o.leaf.flatMap kBytes)) q o.path).toList = root.toList) = true :=
      Option.some.inj h
    exact ⟨hc.1, hc.2, hld, hl, of_decide_eq_true hd⟩
  · simp [pure] at h

/-- **Every opening of an accepted `openAll` is answered**, at its position. -/
theorem openAll_answered (hHt : ∀ x d, H x = some d → d = Ht x) {root : Digest} {height width : ℕ} :
    ∀ {ps : List ℕ} {os : List Opening} {rows : List (List K)} {rest : List Opening},
      openAll (m := Option) H root height width ps os = some (some (rows, rest)) →
      ps.length ≤ os.length ∧ ∀ a ∈ ps.zip os, OpeningAns H Ht root height width a.1 a.2
  | [], os, rows, rest, _ => ⟨by simp, fun a ha => by simp at ha⟩
  | _ :: _, [], rows, rest, h => by simp [openAll, pure] at h
  | q :: qs, o :: os, rows, rest, h => by
    simp only [openAll, bind, Option.bind_eq_some_iff] at h
    obtain ⟨b, hb, h⟩ := h
    cases b
    · simp [pure] at h
    · simp only [↓reduceIte] at h
      obtain ⟨r', hr', h⟩ := Option.bind_eq_some_iff.mp h
      cases r' with
      | none => simp [pure] at h
      | some r' =>
        obtain ⟨hl, hall⟩ := openAll_answered hHt hr'
        refine ⟨by simp; omega, fun a ha => ?_⟩
        rw [List.zip_cons_cons, List.mem_cons] at ha
        rcases ha with rfl | ha
        · exact openOne_answered hHt hb
        · exact hall a ha

/-- **Answered squeezes, step by step, over `Ht`**: each squeeze of an answered run of `k` is
answered from the state over `Ht` after the squeezes before it. -/
theorem sqAllM_steps {M : HashModel} (hHt : ∀ x d, M.H x = some d → d = Ht x) :
    ∀ {k : ℕ} {cv : Digest} {cs : List E} {c' : Digest}, sqAllM M k cv = some (cs, c') →
      ∀ j < k, sqCvM M (sqAllW Ht j cv).2 = some (sqCvW Ht (sqAllW Ht j cv).2)
  | 0, _, _, _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | k + 1, cv, cs, c', h, j, hj => by
    obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r, hr, -⟩ := Option.map_eq_some_iff.mp h
    have e := hHt _ _ hc
    subst e
    rcases j with _ | j
    · exact hc
    · have := sqAllM_steps hHt hr j (by omega)
      exact this

end
end LeanVM.Guest.B1
