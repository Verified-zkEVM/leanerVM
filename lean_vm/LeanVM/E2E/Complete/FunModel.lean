/-
  LeanVM.E2E.Complete.FunModel

  Every functional semantics of `BLAKE2S` with canonical cells is the semantics of a hash model:
  the prefixes are the chains of its rows from the IV, and the answered hash of a string is the
  output of its chain's last row.
-/

module

public import LeanVM.E2E.Complete.Table

/-!
# The hash model of a functional semantics

The guest's soundness (T2, `Guest/EndKnowB.lean`) holds over every hash model (`HashModel`,
`Guest/Value/HashModel.lean`). A hash model is a semantics with a notion of prefix and an answered
hash, closed under the steps of a chain and answering every final row. A functional semantics
(`Functional`: a row's inputs determine its output) of canonical cells is one
(`HashModel.ofFunctional`): a prefix of whole blocks reaches the cells of its chain of rows from
the IV (`FunPrefix`, unique by functionality: `FunPrefix.unique`), and a string's answer is the
output of the final row after the prefix of its whole blocks (`funH`), unique as well since a
string splits into whole blocks and a last part in one way (`split_unique`).

So T2 applies under the table semantics of any run whose rows a functional semantics checks
(`E2E/Complete/HonestRows.lean`).
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Guest.Value

@[expose] public section

variable (S : BlakeSem)

/-- **A prefix under `S`**: the cells after absorbing the whole blocks `bs` from the IV, one row of
`S` a block at the counter of the bytes up to it. -/
inductive FunPrefix : List (List UInt8) → E × E → Prop
  | nil : FunPrefix [] ivCells
  | step {bs : List (List UInt8)} {st st' : E × E} {m : Fin 4 → E} :
      FunPrefix bs st → S.check m st.1 st.2 st'.1 st'.2 (metadataCell (64 * (bs.length + 1)) false) →
      FunPrefix (bs ++ [blockBytes m]) st'

variable {S}

theorem FunPrefix.inv {bs : List (List UInt8)} {st : E × E} (h : FunPrefix S bs st) :
    (bs = [] ∧ st = ivCells) ∨ ∃ bs0 st0 m, bs = bs0 ++ [blockBytes m] ∧ FunPrefix S bs0 st0 ∧
      S.check m st0.1 st0.2 st.1 st.2 (metadataCell (64 * (bs0.length + 1)) false) := by
  cases h with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | step h hc => exact Or.inr ⟨_, _, _, rfl, h, hc⟩

/-- The blocks of a prefix have 64 bytes. -/
theorem FunPrefix.length {bs : List (List UInt8)} {st : E × E} (h : FunPrefix S bs st) :
    ∀ b ∈ bs, b.length = 64 := by
  induction h with
  | nil => intro b hb; exact absurd hb List.not_mem_nil
  | step _ _ ih =>
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact ih b hb
    · rw [List.mem_singleton.mp hb, length_blockBytes]

/-- **A prefix reaches one pair of cells**, the semantics being functional and of canonical cells. -/
theorem FunPrefix.unique (hfun : Functional S)
    (hcan : ∀ {m : Fin 4 → E} {cv0 cv1 o0 o1 md : E}, S.check m cv0 cv1 o0 o1 md →
      CanonicalCells m cv0 cv1 o0 o1 md)
    {bs : List (List UInt8)} {st : E × E} (h : FunPrefix S bs st) :
    ∀ {st' : E × E}, FunPrefix S bs st' → st = st' := by
  induction h with
  | nil =>
    intro st' h'
    rcases h'.inv with ⟨-, rfl⟩ | ⟨bs0, st0, m, he, -, -⟩
    · rfl
    · exact absurd he.symm (by simp)
  | step h0 hc ih =>
    rename_i bs st st' m
    intro st'' h'
    rcases h'.inv with ⟨he, -⟩ | ⟨bs0, st0, m', he, h0', hc'⟩
    · exact absurd he (by simp)
    · obtain ⟨rfl, hb⟩ := List.append_inj' he rfl
      have hb' : blockBytes m = blockBytes m' := by simpa using hb
      obtain rfl := ih h0'
      obtain rfl := eq_of_blockBytes_eq (hcan hc).1 (hcan hc').1 hb'
      obtain ⟨e0, e1⟩ := hfun hc hc'
      exact Prod.ext e0 e1

/-- **A string splits into whole blocks and a last part in one way**: the last part has at most
64 bytes and is not empty unless the string is. -/
theorem split_unique : ∀ {bs bs' : List (List UInt8)} {r r' : List UInt8},
    (∀ b ∈ bs, b.length = 64) → (∀ b ∈ bs', b.length = 64) → r.length ≤ 64 → r'.length ≤ 64 →
    (bs = [] ∨ r ≠ []) → (bs' = [] ∨ r' ≠ []) → bs.flatten ++ r = bs'.flatten ++ r' →
    bs = bs' ∧ r = r'
  | [], [], r, r', _, _, _, _, _, _, h => ⟨rfl, by simpa using h⟩
  | [], b' :: bs', r, r', _, hl', hr, _, _, hn', h => by
    exfalso
    simp only [List.flatten_nil, List.nil_append, List.flatten_cons, List.append_assoc] at h
    have hlen := congrArg List.length h
    simp only [List.length_append, hl' b' List.mem_cons_self] at hlen
    have h0 : r'.length = 0 := by omega
    rcases hn' with h1 | h1
    · cases h1
    · exact h1 (List.length_eq_zero_iff.mp h0)
  | b :: bs, [], r, r', hl, _, _, hr', hn, _, h => by
    exfalso
    simp only [List.flatten_nil, List.nil_append, List.flatten_cons, List.append_assoc] at h
    have hlen := congrArg List.length h
    simp only [List.length_append, hl b List.mem_cons_self] at hlen
    have h0 : r.length = 0 := by omega
    rcases hn with h1 | h1
    · cases h1
    · exact h1 (List.length_eq_zero_iff.mp h0)
  | b :: bs, b' :: bs', r, r', hl, hl', hr, hr', hn, hn', h => by
    simp only [List.flatten_cons, List.append_assoc] at h
    obtain ⟨rfl, h2⟩ := List.append_inj h (by rw [hl b List.mem_cons_self, hl' b' List.mem_cons_self])
    have hn1 : bs = [] ∨ r ≠ [] := by
      rcases hn with h1 | h1
      · cases h1
      · exact Or.inr h1
    have hn1' : bs' = [] ∨ r' ≠ [] := by
      rcases hn' with h1 | h1
      · cases h1
      · exact Or.inr h1
    obtain ⟨rfl, rfl⟩ := split_unique (fun x hx ↦ hl x (List.mem_cons_of_mem _ hx))
      (fun x hx ↦ hl' x (List.mem_cons_of_mem _ hx)) hr hr' hn1 hn1' h2
    exact ⟨rfl, rfl⟩

variable (S) in
/-- **A final row of a string under `S`**: the string is the whole blocks `q.1` absorbed to the
cells `q.2.2.1` and the last part `q.2.1`, zero-filled into the message cells `q.2.2.2.1`, whose row
at the counter of the string with the last-block flag outputs `q.2.2.2.2`. -/
def FinalRow (x : List UInt8)
    (q : List (List UInt8) × List UInt8 × (E × E) × (Fin 4 → E) × (E × E)) : Prop :=
  FunPrefix S q.1 q.2.2.1 ∧ q.2.1.length ≤ 64 ∧ (q.1 = [] ∨ q.2.1 ≠ []) ∧
    blockBytes q.2.2.2.1 = q.2.1 ++ List.replicate (64 - q.2.1.length) 0 ∧
    S.check q.2.2.2.1 q.2.2.1.1 q.2.2.1.2 q.2.2.2.2.1 q.2.2.2.2.2
      (metadataCell (64 * q.1.length + q.2.1.length) true) ∧
    x = q.1.flatten ++ q.2.1

open Classical in
variable (S) in
/-- **The answered hash under `S`**: the output of a final row of the string, if any. -/
noncomputable def funH (x : List UInt8) : Option Digest :=
  if h : ∃ q, FinalRow S x q then
    some (cellWords h.choose.2.2.2.2.1 ++ cellWords h.choose.2.2.2.2.2) else none

/-- A string's final rows have one output. -/
theorem finalRow_unique (hfun : Functional S)
    (hcan : ∀ {m : Fin 4 → E} {cv0 cv1 o0 o1 md : E}, S.check m cv0 cv1 o0 o1 md →
      CanonicalCells m cv0 cv1 o0 o1 md)
    {x : List UInt8} {q q' : List (List UInt8) × List UInt8 × (E × E) × (Fin 4 → E) × (E × E)}
    (h : FinalRow S x q) (h' : FinalRow S x q') : q.2.2.2.2 = q'.2.2.2.2 := by
  obtain ⟨hp, hr, hn, hb, hc, hx⟩ := h
  obtain ⟨hp', hr', hn', hb', hc', hx'⟩ := h'
  obtain ⟨e1, e2⟩ := split_unique hp.length hp'.length hr hr' hn hn' (hx.symm.trans hx')
  have est : q.2.2.1 = q'.2.2.1 := hp.unique hfun hcan (by rw [e1]; exact hp')
  have em : q.2.2.2.1 = q'.2.2.2.1 :=
    eq_of_blockBytes_eq (hcan hc).1 (hcan hc').1 (by rw [hb, hb', e2])
  rw [est, em, e1, e2] at hc
  obtain ⟨e0, e1'⟩ := hfun hc hc'
  exact Prod.ext e0 e1'

/-- **The hash model of a functional semantics of canonical cells.** -/
noncomputable def HashModel.ofFunctional (S : BlakeSem) (hfun : Functional S)
    (hcan : ∀ {m : Fin 4 → E} {cv0 cv1 o0 o1 md : E}, S.check m cv0 cv1 o0 o1 md →
      CanonicalCells m cv0 cv1 o0 o1 md) : HashModel where
  sem := S
  canonical := hcan
  H := funH S
  Prefix := FunPrefix S
  prefix_nil := FunPrefix.nil
  prefix_step := fun hp hc ↦ FunPrefix.step hp hc
  final := by
    intro bs st m r out0 out1 hp hr hn hb hc
    have hq : FinalRow S (bs.flatten ++ r) ⟨bs, r, st, m, (out0, out1)⟩ :=
      ⟨hp, hr, hn, hb, hc, rfl⟩
    have hex : ∃ q, FinalRow S (bs.flatten ++ r) q := ⟨_, hq⟩
    refine ⟨cellWords hex.choose.2.2.2.2.1 ++ cellWords hex.choose.2.2.2.2.2,
      by unfold funH; simp only [hex, ↓reduceDIte], ?_⟩
    have e := finalRow_unique hfun hcan hex.choose_spec hq
    have hcc := hcan hc
    rw [e]
    exact pair_eq_digestScalars_iff.mpr ⟨hcc.2.2.2.1, hcc.2.2.2.2.1, rfl⟩

@[simp] theorem HashModel.ofFunctional_sem (S : BlakeSem) (hfun : Functional S)
    (hcan : ∀ {m : Fin 4 → E} {cv0 cv1 o0 o1 md : E}, S.check m cv0 cv1 o0 o1 md →
      CanonicalCells m cv0 cv1 o0 o1 md) : (HashModel.ofFunctional S hfun hcan).sem = S := rfl

end
end LeanVM.E2E.Complete
