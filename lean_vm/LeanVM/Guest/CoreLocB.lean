/-
  LeanVM.Guest.CoreLocB

  The located call relation (`CoreLoc.lean`) under any semantics of `BLAKE2S`.
-/

module

public import LeanVM.Guest.CoreLoc
public import LeanVM.Guest.CoreB

/-!
# The located call relation under any `BLAKE2S` semantics

`CoreLoc.lean` over `CoreB.lean`: `Program.locNB S`, `Program.RelLB S`, `relLB_le_rel`,
`relLB_iff`, proved as there.
-/

namespace LeanVM.Guest.Core

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

variable {S : BlakeSem}

variable {rd : Reader} {σ : Val}

variable (S) in
/-- The located call relation of depth `n`: calls nested at most `n` deep, each callee `f` at a
frame `fp` with `A fp` under the valuation `vf f fp`. -/
def Program.locNB (P : Program) (rd : Reader) (vf : String → K → Val) (A : K → Prop) :
    Nat → CallRel
  | 0 => fun _ _ _ => False
  | n + 1 => fun f args rets => ∃ fn fp, P.find? f = some fn ∧ A fp ∧
      fn.params.map (vf f fp) = args ∧
      Stmt.HoldsListB S (P.locNB rd vf A n) rd (vf f fp) fn.body False (fun rs => rs = rets)

variable (S) in
/-- **The located call relation**: every finite depth. -/
def Program.RelLB (P : Program) (rd : Reader) (vf : String → K → Val) (A : K → Prop) : CallRel :=
  fun f args rets => ∃ n, P.locNB S rd vf A n f args rets

variable {vf : String → K → Val} {A : K → Prop}

theorem locNB_succ (P : Program) : ∀ n, CallRel.Le (P.locNB S rd vf A n) (P.locNB S rd vf A (n + 1))
  | 0 => fun _ _ _ h => h.elim
  | n + 1 => fun _ _ _ ⟨fn, fp, hf, hA, hp, h⟩ =>
      ⟨fn, fp, hf, hA, hp, holdsListB_mono (locNB_succ P n) fn.body id (fun _ h => h) h⟩

theorem locNB_mono (P : Program) {m n : Nat} (h : m ≤ n) :
    CallRel.Le (P.locNB S rd vf A m) (P.locNB S rd vf A n) := by
  induction h with
  | refl => exact fun _ _ _ h => h
  | step _ ih => exact fun f a r h => locNB_succ P _ f a r (ih f a r h)

theorem locNB_le_relL (P : Program) (n : Nat) : CallRel.Le (P.locNB S rd vf A n) (P.RelLB S rd vf A) :=
  fun _ _ _ h => ⟨n, h⟩

theorem locNB_le_relN (P : Program) : ∀ n, CallRel.Le (P.locNB S rd vf A n) (P.relNB S rd n)
  | 0 => fun _ _ _ h => h
  | n + 1 => fun f _ _ ⟨fn, fp, hf, _, hp, h⟩ =>
      ⟨fn, hf, vf f fp, hp, holdsListB_mono (locNB_le_relN P n) fn.body id (fun _ h => h) h⟩

/-- The located relation implies the relation. -/
theorem relLB_le_rel (P : Program) : CallRel.Le (P.RelLB S rd vf A) (P.RelB S rd) :=
  fun _ _ _ ⟨n, h⟩ => ⟨n, locNB_le_relN P n _ _ _ h⟩

/-! ## The fixed point -/

variable (S) in
/-- A family of continuations, monotone in the call relation and reached at a finite depth of
the located relation. -/
structure FinitaryLB (P : Program) (rd : Reader) (vf : String → K → Val) (A : K → Prop)
    (F : CallRel → Prop) : Prop where
  mono : ∀ C C', CallRel.Le C C' → F C → F C'
  finite : F (P.RelLB S rd vf A) → ∃ n, F (P.locNB S rd vf A n)

mutual
theorem holdsB_finiteL (P : Program) :
    ∀ (s : Stmt) (F : CallRel → Prop) (kret : List E → Prop), FinitaryLB S P rd vf A F →
      Stmt.HoldsB S (P.RelLB S rd vf A) rd σ s (F (P.RelLB S rd vf A)) kret →
        ∃ n, Stmt.HoldsB S (P.locNB S rd vf A n) rd σ s (F (P.locNB S rd vf A n)) kret
  | .atom _, F, _, hF, h => (hF.finite h.2).imp fun _ hn => ⟨h.1, hn⟩
  | .ite c z n', F, kret, hF, h => by
      by_cases hc : σ c = 0
      · obtain ⟨n, hn⟩ := holdsListB_finiteL P z F kret hF (h.2.1 hc)
        exact ⟨n, h.1, fun _ => hn, fun hc' => absurd hc hc'⟩
      · obtain ⟨n, hn⟩ := holdsListB_finiteL P n' F kret hF (h.2.2 hc)
        exact ⟨n, h.1, fun hc' => absurd hc' hc, fun _ => hn⟩
  | .match_ x arms, F, kret, hF, h => holdsArmsB_finiteL P x arms 0 F kret hF h
  | .call f args rets, F, _, hF, h => by
      obtain ⟨n1, h1⟩ := h.1
      obtain ⟨n2, h2⟩ := hF.finite h.2
      exact ⟨max n1 n2, locNB_mono P (le_max_left _ _) _ _ _ h1,
        hF.mono _ _ (locNB_mono P (le_max_right _ _)) h2⟩
  | .callIf c f args, F, _, hF, h => by
      obtain ⟨n2, h2⟩ := hF.finite h.2.2
      by_cases hc : σ c ≠ 0
      · obtain ⟨n1, h1⟩ := h.2.1 hc
        exact ⟨max n1 n2, h.1, fun _ => locNB_mono P (le_max_left _ _) _ _ _ h1,
          hF.mono _ _ (locNB_mono P (le_max_right _ _)) h2⟩
      · exact ⟨n2, h.1, fun hc' => absurd hc' hc, h2⟩
  | .dispatch x fs args rets, F, _, hF, h => by
      obtain ⟨j, hj, hx, n1, h1⟩ := h.1
      obtain ⟨n2, h2⟩ := hF.finite h.2
      exact ⟨max n1 n2, ⟨j, hj, hx, locNB_mono P (le_max_left _ _) _ _ _ h1⟩,
        hF.mono _ _ (locNB_mono P (le_max_right _ _)) h2⟩
  | .ret _, _, _, _, h => ⟨0, h⟩

theorem holdsListB_finiteL (P : Program) :
    ∀ (ss : List Stmt) (F : CallRel → Prop) (kret : List E → Prop), FinitaryLB S P rd vf A F →
      Stmt.HoldsListB S (P.RelLB S rd vf A) rd σ ss (F (P.RelLB S rd vf A)) kret →
        ∃ n, Stmt.HoldsListB S (P.locNB S rd vf A n) rd σ ss (F (P.locNB S rd vf A n)) kret
  | [], _, _, hF, h => hF.finite h
  | s :: ss, F, kret, hF, h =>
      holdsB_finiteL P s (fun C => Stmt.HoldsListB S C rd σ ss (F C) kret) kret
        ⟨fun C C' hC h => holdsListB_mono hC ss (hF.mono C C' hC) (fun _ h => h) h,
          holdsListB_finiteL P ss F kret hF⟩ h

theorem holdsArmsB_finiteL (P : Program) (x : V) :
    ∀ (arms : List (List Stmt)) (j : Nat) (F : CallRel → Prop) (kret : List E → Prop),
      FinitaryLB S P rd vf A F → Stmt.HoldsArmsB S (P.RelLB S rd vf A) rd σ x j arms (F (P.RelLB S rd vf A)) kret →
        ∃ n, Stmt.HoldsArmsB S (P.locNB S rd vf A n) rd σ x j arms (F (P.locNB S rd vf A n)) kret
  | [], _, _, _, _, h => h.elim
  | a :: as, j, F, kret, hF, h => by
      rcases h with ⟨hx, ha⟩ | ha
      · exact (holdsListB_finiteL P a F kret hF ha).imp fun _ hn => Or.inl ⟨hx, hn⟩
      · exact (holdsArmsB_finiteL P x as (j + 1) F kret hF ha).imp fun _ hn => Or.inr hn
end

/-- **`Program.RelLB` is a fixed point**: a call holds exactly when the callee's body does at some
frame `fp` with `A fp`, under that frame's valuation, its own calls located. -/
theorem relLB_iff (P : Program) (f : String) (args rets : List E) :
    P.RelLB S rd vf A f args rets ↔ ∃ fn fp, P.find? f = some fn ∧ A fp ∧
      fn.params.map (vf f fp) = args ∧
      Stmt.HoldsListB S (P.RelLB S rd vf A) rd (vf f fp) fn.body False (fun rs => rs = rets) := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => exact hn.elim
    | succ n =>
        obtain ⟨fn, fp, hf, hA, hp, h⟩ := hn
        exact ⟨fn, fp, hf, hA, hp, holdsListB_mono (locNB_le_relL P n) fn.body id (fun _ h => h) h⟩
  · rintro ⟨fn, fp, hf, hA, hp, h⟩
    obtain ⟨n, hn⟩ := holdsListB_finiteL (σ := vf f fp) P fn.body (fun _ => False)
      (fun rs => rs = rets) ⟨fun _ _ _ h => h, fun h => h.elim⟩ h
    exact ⟨n + 1, fn, fp, hf, hA, hp, hn⟩

/-- At the deployed semantics, the located relation of depth `n` is `CoreLoc.lean`'s. -/
theorem locNB_deployed (P : Program) (rd : Reader) (vf : String → K → Val) (A : K → Prop) :
    ∀ n, P.locNB blakeDeployed rd vf A n = P.locN rd vf A n
  | 0 => rfl
  | n + 1 => by
    funext f args rets
    simp only [Program.locNB, Program.locN, locNB_deployed P rd vf A n, holdsListB_deployed]

/-- **At the deployed semantics, the located relation is `CoreLoc.lean`'s.** -/
theorem relLB_deployed (P : Program) (rd : Reader) (vf : String → K → Val) (A : K → Prop) :
    P.RelLB blakeDeployed rd vf A = P.RelL rd vf A := by
  funext f args rets
  simp only [Program.RelLB, Program.RelL, locNB_deployed]

end
end LeanVM.Guest.Core
