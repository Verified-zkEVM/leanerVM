/-
  LeanVM.Guest.Memory.StaticWordsB

  Words bounds from the static checker (`StaticWords.lean`) under any semantics of `BLAKE2S`.
-/

module

public import LeanVM.Guest.Memory.StaticWords
public import LeanVM.Guest.Memory.StaticSoundB
public import LeanVM.Guest.Memory.SizeTotalB

/-!
# Words bounds under any `BLAKE2S` semantics

`StaticWords.lean`'s `HandOk` and lemmas with `S : BlakeSem` a parameter (`HandOkB`,
`totalLeB_of_stat`, `totalB_le_of_stat`, `totalB_le_of_loop`; `handOkB_deployed` at
`blakeDeployed`).
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

variable {S : BlakeSem}

variable {P : Core.Program} {fs : String → ℕ}

variable {rd : Reader} {cert : String → Cert}

variable (S) in
/-- **Hand bounds**: every valid tree of a function of `X` satisfies its certificate, in words. -/
def HandOkB (P : Core.Program) (fs : String → ℕ) (cert : String → Cert) (X : String → Prop) : Prop :=
  ∀ f, X f → ∀ (rd : Reader) (t : Tree) (args rets : List E), t.name = f → t.ValidB S P rd args rets →
    t.BufsOk P → Bound P true cert fs t args

/-- A hand bound on the words of `f`'s trees, under its certificate's preconditions, is what
`HandOkB` asks of a `stat` certificate. -/
theorem boundB_of_total {f : String} {pre : List (ℕ × ℕ)} {b : Aff} {ks : List (V × ℕ)}
    (hcf : cert f = .stat pre b ks)
    (h : ∀ (rd : Reader) (t : Tree) (args rets : List E), t.name = f → t.ValidB S P rd args rets →
      t.BufsOk P → ArgsPre pre args → t.total fs ≤ b.eval args)
    {t : Tree} {args rets : List E} (hn : t.name = f) (hv : t.ValidB S P rd args rets) (hb : t.BufsOk P) :
    Bound P true cert fs t args := by
  unfold Bound
  rw [hn, hcf]
  intro hpre
  rw [← total_eq_cost t hb]
  exact h rd t args rets hn hv hb hpre

/-- **A certificate checked counting words bounds the words**, under its preconditions. -/
theorem totalB_le_of_stat {X : String → Prop} (hchk : CheckedExcept P true cert fs X)
    (hX : HandOkB S P fs cert X) {f : String} {pre : List (ℕ × ℕ)} {b : Aff} {ks : List (V × ℕ)}
    (hcf : cert f = .stat pre b ks) {t : Tree} {args rets : List E} (hn : t.name = f)
    (hv : t.ValidB S P rd args rets) (hb : t.BufsOk P) (hpre : ArgsPre pre args) :
    t.total fs ≤ b.eval args := by
  rw [total_eq_cost t hb]
  exact costB_le_of_stat hchk (fun f hf => hX f hf rd) hcf hn hv hb hpre

/-- **A loop checked counting words**: from `g^a` to `g^e`, `e - a` times its iteration's
bound. -/
theorem totalB_le_of_loop {X : String → Prop} (hchk : CheckedExcept P true cert fs X)
    (hX : HandOkB S P fs cert X) {f : String} {endc : Option ℕ} {pre : List (ℕ × ℕ)} {b : Aff}
    {ks : List (V × ℕ)} (hcf : cert f = .loop endc pre b ks) {t : Tree} {args rets : List E}
    (hn : t.name = f) (hv : t.ValidB S P rd args rets) (hb : t.BufsOk P) {a e : ℕ}
    (ha : args.getD 0 0 = ofK (gpow a)) (he : endOf endc args = ofK (gpow e)) (hae : a < e)
    (heo : e < 2 ^ 64 - 1) (hpre : ArgsPre pre args) : t.total fs ≤ (e - a) * b.eval args := by
  rw [total_eq_cost t hb]
  exact costB_le_of_loop hchk (fun f hf => hX f hf rd) hcf hn hv hb ha he hae heo hpre

/-- **A constant certificate checked counting words** is a `TotalLeB`. -/
theorem totalLeB_of_stat {X : String → Prop} (hchk : CheckedExcept P true cert fs X)
    (hX : HandOkB S P fs cert X) {f : String} {B : ℕ} {ks : List (V × ℕ)}
    (hcf : cert f = .stat [] ⟨B, []⟩ ks) : TotalLeB S P fs f fun _ => B :=
  fun _ _ _ _ hn hv hb => by
    have := totalB_le_of_stat hchk hX hcf hn hv hb (fun _ h => (List.not_mem_nil h).elim)
    simpa [Aff.eval] using this

/-! ## At the deployed semantics -/

section Deployed

variable {P : Core.Program}

/-- At the deployed semantics, `HandOkB` is `StaticWords.lean`'s `HandOk`. -/
theorem handOkB_deployed (fs : String → ℕ) (cert : String → Cert) (X : String → Prop) :
    HandOkB blakeDeployed P fs cert X = HandOk P fs cert X := by
  simp only [HandOkB, HandOk, validB_deployed]

end Deployed

end
end LeanVM.Guest.Memory
