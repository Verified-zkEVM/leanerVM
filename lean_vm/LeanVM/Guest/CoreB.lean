/-
  LeanVM.Guest.CoreB

  The core IR's relational semantics under any semantics of `BLAKE2S` (`BlakeSem`): the relation
  of `Core.lean` and the lemmas of `CoreLemmas.lean` with the `BLAKE2S` atom's relation a
  parameter, the deployed ones at `blakeDeployed`.
-/

module

public import LeanVM.Guest.CoreLemmas
public import LeanVM.Spec.IsaWith

/-!
# The core semantics under any `BLAKE2S` semantics

`Core.lean` gives a `BLAKE2S` atom the deployed relation, `CompressCells`. The guest's end-to-end
security theorem (`docs/roadmap/e2e-security.md`, T2) needs its proofs under a hash model's
semantics (`Value.HashModel.sem`), so every definition here is `Core.lean`'s with the relation a
parameter `S : BlakeSem` (`Atom.HoldsB`, `Stmt.HoldsB`, `Fn.SemB`, `Program.relNB`,
`Program.RelB`, named as `Spec/IsaWith.lean` names `executeWithB`, `runB`), and every lemma of
`CoreLemmas.lean` about them is restated (`holdsListB_append`, `holdsB_mono`, `relB_iff`, …),
proved as there.

* `relB_deployed`: at `blakeDeployed`, `Program.RelB` is `Program.Rel` (and the same for
  statements and functions), so a lemma proved here for every `S` gives the deployed lemma.
* `relB_monoS`: a semantics whose relation implies another's gives the other's relations.
* `relB_iff_rel_of_freeOn`: a function free of `BLAKE2S`, calling only such functions
  (`Program.FreeOn`, checked by the kernel), has its deployed relation under every semantics, so
  a B1 lemma about it carries over unchanged.

The deployed modules are not changed: the generated kernel-checked families import `Core.lean`,
and this module only adds beside it (`docs/roadmap/w2-guest-model.md`).
-/

namespace LeanVM.Guest.Core

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

variable {S : BlakeSem}

/-! ## Semantics -/

variable (S) in
/-- The relation of an atom. -/
def Atom.HoldsB (rd : Reader) (σ : Val) : Atom → Prop
  | .const d c => σ d = c
  | .add d a b => σ d = σ a + σ b
  | .mul d a b => σ d = σ a * σ b
  | .copy d s => σ d = σ s
  | .load d p off => LoadHolds rd (σ p) off (σ d)
  | .assertEq a b => σ a + σ b = 0
  | .assertNe x inv p => σ p = σ x * σ inv ∧ σ p = 1
  | .rangeCheck x y t1 t2 k =>
      LoadHolds rd (σ x) 0 (σ t1) ∧ σ k = σ x * σ y ∧ LoadHolds rd (σ y) 0 (σ t2)
  | .assertInK a b => IsInK (σ a) ∧ IsInK (σ b)
  | .blake2s m0 m1 m2 m3 cv0 cv1 o0 o1 md =>
      S.check ![σ m0, σ m1, σ m2, σ m3] (σ cv0) (σ cv1) (σ o0) (σ o1) (σ md)
  | .frameAddr p run =>
      IsInK (σ p) ∧ ∀ (k : Nat) (hk : k < run.length) (w : E),
        rd ((σ p).limb 0 * gpow k) = some w → w = σ run[k]
  | .hint _ => True

variable (S)
mutual
/-- A statement holds, then `next` (the rest of its block) holds; a `ret` hands its words to
`kret` instead. -/
def Stmt.HoldsB (C : CallRel) (rd : Reader) (σ : Val) :
    Stmt → Prop → (List E → Prop) → Prop
  | .atom a, next, _ => a.HoldsB S rd σ ∧ next
  | .ite c z n, next, kret =>
      IsInK (σ c) ∧ (σ c = 0 → Stmt.HoldsListB C rd σ z next kret) ∧
        (σ c ≠ 0 → Stmt.HoldsListB C rd σ n next kret)
  | .match_ x arms, next, kret => Stmt.HoldsArmsB C rd σ x 0 arms next kret
  | .call f args rets, next, _ => C f (args.map σ) (rets.map σ) ∧ next
  | .callIf c f args, next, _ => IsInK (σ c) ∧ (σ c ≠ 0 → C f (args.map σ) []) ∧ next
  | .dispatch x fs args rets, next, _ =>
      (∃ (j : Nat) (h : j < fs.length), σ x = ofK (gpow j) ∧ C fs[j] (args.map σ) (rets.map σ)) ∧
        next
  | .ret vs, _, kret => kret (vs.map σ)

/-- A block holds, then `next`. -/
def Stmt.HoldsListB (C : CallRel) (rd : Reader) (σ : Val) :
    List Stmt → Prop → (List E → Prop) → Prop
  | [], next, _ => next
  | s :: ss, next, kret => Stmt.HoldsB C rd σ s (Stmt.HoldsListB C rd σ ss next kret) kret

/-- Arm `j + i` holds at `x = g^(j + i)`, for some arm `i` of the list. -/
def Stmt.HoldsArmsB (C : CallRel) (rd : Reader) (σ : Val) (x : V) :
    Nat → List (List Stmt) → Prop → (List E → Prop) → Prop
  | _, [], _, _ => False
  | j, a :: as, next, kret =>
      (σ x = ofK (gpow j) ∧ Stmt.HoldsListB C rd σ a next kret) ∨
        Stmt.HoldsArmsB C rd σ x (j + 1) as next kret
end
variable {S}

variable (S) in
/-- A function's relation: some valuation takes the parameters to the arguments and its body to
a `ret` of the return words. -/
def Fn.SemB (C : CallRel) (rd : Reader) (f : Fn) (args rets : List E) : Prop :=
  ∃ σ : Val, f.params.map σ = args ∧ Stmt.HoldsListB S C rd σ f.body False (fun rs => rs = rets)

variable (S) in
/-- The call relation of depth `n`: calls nested at most `n` deep. -/
def Program.relNB (P : Program) (rd : Reader) : Nat → CallRel
  | 0 => fun _ _ _ => False
  | n + 1 => fun f args rets => ∃ fn, P.find? f = some fn ∧ fn.SemB S (P.relNB rd n) rd args rets

variable (S) in
/-- A program's call relation: every finite depth. -/
def Program.RelB (P : Program) (rd : Reader) : CallRel :=
  fun f args rets => ∃ n, P.relNB S rd n f args rets

/-! ## Lemmas (`CoreLemmas.lean`) -/

section Lemmas

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## Sequencing -/

theorem holdsListB_append (xs ys : List Stmt) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsListB S C rd σ (xs ++ ys) next kret =
      Stmt.HoldsListB S C rd σ xs (Stmt.HoldsListB S C rd σ ys next kret) kret := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, Stmt.HoldsListB, ih]

mutual
theorem holdsB_noRet : ∀ (s : Stmt), Stmt.noRet s = true → ∀ (next : Prop) (kret : List E → Prop),
    (Stmt.HoldsB S C rd σ s next kret ↔ Stmt.HoldsB S C rd σ s True kret ∧ next)
  | .atom _, _, _, _ => by simp [Stmt.HoldsB]
  | .ite c z n, h, next, kret => by
      simp only [Stmt.noRet, Bool.and_eq_true] at h
      simp only [Stmt.HoldsB]
      rw [holdsListB_noRet z h.1 next kret, holdsListB_noRet n h.2 next kret,
        holdsListB_noRet z h.1 True kret, holdsListB_noRet n h.2 True kret]
      by_cases hc : σ c = 0 <;> simp [hc] <;> tauto
  | .match_ x arms, h, next, kret => by
      simp only [Stmt.noRet] at h
      simp only [Stmt.HoldsB]
      exact holdsArmsB_noRet x arms h 0 next kret
  | .call .., _, _, _ => by simp [Stmt.HoldsB]
  | .callIf .., _, _, _ => by simp [Stmt.HoldsB, and_assoc]
  | .dispatch .., _, _, _ => by simp [Stmt.HoldsB]
  | .ret _, h, _, _ => by simp [Stmt.noRet] at h

theorem holdsListB_noRet : ∀ (ss : List Stmt), Stmt.noRetList ss = true →
    ∀ (next : Prop) (kret : List E → Prop),
    (Stmt.HoldsListB S C rd σ ss next kret ↔ Stmt.HoldsListB S C rd σ ss True kret ∧ next)
  | [], _, _, _ => by simp [Stmt.HoldsListB]
  | s :: ss, h, next, kret => by
      simp only [Stmt.noRetList, Bool.and_eq_true] at h
      simp only [Stmt.HoldsListB]
      rw [holdsB_noRet s h.1 (Stmt.HoldsListB S C rd σ ss next kret) kret,
        holdsB_noRet s h.1 (Stmt.HoldsListB S C rd σ ss True kret) kret, holdsListB_noRet ss h.2 next kret]
      tauto

theorem holdsArmsB_noRet (x : V) : ∀ (arms : List (List Stmt)), Stmt.noRetArms arms = true →
    ∀ (j : Nat) (next : Prop) (kret : List E → Prop),
    (Stmt.HoldsArmsB S C rd σ x j arms next kret ↔ Stmt.HoldsArmsB S C rd σ x j arms True kret ∧ next)
  | [], _, _, _, _ => by simp [Stmt.HoldsArmsB]
  | a :: as, h, j, next, kret => by
      simp only [Stmt.noRetArms, Bool.and_eq_true] at h
      simp only [Stmt.HoldsArmsB]
      rw [holdsListB_noRet a h.1 next kret, holdsArmsB_noRet x as h.2 (j + 1) next kret]
      tauto
end

/-- Return-free blocks in sequence hold exactly when each does: the semantics of an expanded
`unroll` is the conjunction over its counter of the iterations'. -/
theorem holdsListB_flatten (bs : List (List Stmt)) (h : ∀ b ∈ bs, Stmt.noRetList b = true)
    (next : Prop) (kret : List E → Prop) :
    (Stmt.HoldsListB S C rd σ bs.flatten next kret ↔
      (∀ b ∈ bs, Stmt.HoldsListB S C rd σ b True kret) ∧ next) := by
  induction bs with
  | nil => simp [Stmt.HoldsListB]
  | cons b bs ih =>
      simp only [List.flatten_cons, holdsListB_append, List.mem_cons, forall_eq_or_imp]
      rw [holdsListB_noRet b (h b (by simp)) _ kret, ih (fun b hb => h b (by simp [hb]))]
      tauto

/-! ## `match` -/

theorem holdsArmsB_iff (x : V) : ∀ (arms : List (List Stmt)) (j : Nat) (next : Prop)
    (kret : List E → Prop),
    Stmt.HoldsArmsB S C rd σ x j arms next kret ↔
      ∃ (i : Nat) (h : i < arms.length), σ x = ofK (gpow (j + i)) ∧
        Stmt.HoldsListB S C rd σ arms[i] next kret
  | [], _, _, _ => by simp [Stmt.HoldsArmsB]
  | a :: as, j, next, kret => by
      simp only [Stmt.HoldsArmsB, holdsArmsB_iff x as (j + 1) next kret]
      constructor
      · rintro (⟨hx, ha⟩ | ⟨i, hi, hx, ha⟩)
        · exact ⟨0, by simp, by simpa using hx, by simpa using ha⟩
        · exact ⟨i + 1, by simp; omega, by rw [hx]; congr 2; omega, by simpa using ha⟩
      · rintro ⟨i, hi, hx, ha⟩
        cases i with
        | zero => exact Or.inl ⟨by simpa using hx, by simpa using ha⟩
        | succ i =>
            exact Or.inr ⟨i, by simp at hi; omega, by rw [hx]; congr 2; omega, by simpa using ha⟩

/-- A `match` holds of one arm `j < arms.length`, at `x = g^j`. -/
theorem holdsB_match_iff (x : V) (arms : List (List Stmt)) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsB S C rd σ (.match_ x arms) next kret ↔
      ∃ (j : Nat) (h : j < arms.length), σ x = ofK (gpow j) ∧
        Stmt.HoldsListB S C rd σ arms[j] next kret := by
  simp only [Stmt.HoldsB, holdsArmsB_iff, Nat.zero_add]

/-- A fused `match` of calls holds of one callee `j < fs.length`, at `x = g^j`. -/
theorem holdsB_dispatch_iff (x : V) (fs : List String) (args rets : List V) (next : Prop)
    (kret : List E → Prop) :
    Stmt.HoldsB S C rd σ (.dispatch x fs args rets) next kret ↔
      (∃ (j : Nat) (h : j < fs.length), σ x = ofK (gpow j) ∧
        C fs[j] (args.map σ) (rets.map σ)) ∧ next := Iff.rfl

/-- A call holds exactly when the call relation relates its argument and return words. -/
theorem holdsB_call_iff (f : String) (args rets : List V) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsB S C rd σ (.call f args rets) next kret ↔ C f (args.map σ) (rets.map σ) ∧ next :=
  Iff.rfl

/-! ## Calls -/

mutual
theorem holdsB_mono {C C' : CallRel} (hC : CallRel.Le C C') :
    ∀ (s : Stmt) {next next' : Prop} {kret kret' : List E → Prop}, (next → next') →
      (∀ r, kret r → kret' r) → Stmt.HoldsB S C rd σ s next kret → Stmt.HoldsB S C' rd σ s next' kret'
  | .atom _, _, _, _, _, hn, _, h => ⟨h.1, hn h.2⟩
  | .ite _ z n, _, _, _, _, hn, hk, h =>
      ⟨h.1, fun hc => holdsListB_mono hC z hn hk (h.2.1 hc),
        fun hc => holdsListB_mono hC n hn hk (h.2.2 hc)⟩
  | .match_ x arms, _, _, _, _, hn, hk, h => holdsArmsB_mono hC x arms 0 hn hk h
  | .call .., _, _, _, _, hn, _, h => ⟨hC _ _ _ h.1, hn h.2⟩
  | .callIf .., _, _, _, _, hn, _, h => ⟨h.1, fun hc => hC _ _ _ (h.2.1 hc), hn h.2.2⟩
  | .dispatch .., _, _, _, _, hn, _, h =>
      ⟨let ⟨j, hj, hx, hc⟩ := h.1; ⟨j, hj, hx, hC _ _ _ hc⟩, hn h.2⟩
  | .ret _, _, _, _, _, _, hk, h => hk _ h

theorem holdsListB_mono {C C' : CallRel} (hC : CallRel.Le C C') :
    ∀ (ss : List Stmt) {next next' : Prop} {kret kret' : List E → Prop}, (next → next') →
      (∀ r, kret r → kret' r) → Stmt.HoldsListB S C rd σ ss next kret →
        Stmt.HoldsListB S C' rd σ ss next' kret'
  | [], _, _, _, _, hn, _, h => hn h
  | s :: ss, _, _, _, _, hn, hk, h => holdsB_mono hC s (holdsListB_mono hC ss hn hk) hk h

theorem holdsArmsB_mono {C C' : CallRel} (hC : CallRel.Le C C') (x : V) :
    ∀ (arms : List (List Stmt)) (j : Nat) {next next' : Prop} {kret kret' : List E → Prop},
      (next → next') → (∀ r, kret r → kret' r) → Stmt.HoldsArmsB S C rd σ x j arms next kret →
        Stmt.HoldsArmsB S C' rd σ x j arms next' kret'
  | [], _, _, _, _, _, _, _, h => h
  | a :: as, j, _, _, _, _, hn, hk, h =>
      h.imp (fun h => ⟨h.1, holdsListB_mono hC a hn hk h.2⟩) (holdsArmsB_mono hC x as (j + 1) hn hk)
end

theorem fnSemB_mono {C C' : CallRel} (hC : CallRel.Le C C') (f : Fn) (args rets : List E) :
    f.SemB S C rd args rets → f.SemB S C' rd args rets := fun ⟨σ, hp, h⟩ =>
  ⟨σ, hp, holdsListB_mono hC f.body id (fun _ h => h) h⟩

theorem relNB_succ (P : Program) : ∀ n, CallRel.Le (P.relNB S rd n) (P.relNB S rd (n + 1))
  | 0 => fun _ _ _ h => h.elim
  | n + 1 => fun _ _ _ ⟨fn, hf, h⟩ => ⟨fn, hf, fnSemB_mono (relNB_succ P n) fn _ _ h⟩

theorem relNB_mono (P : Program) {m n : Nat} (h : m ≤ n) : CallRel.Le (P.relNB S rd m) (P.relNB S rd n) := by
  induction h with
  | refl => exact fun _ _ _ h => h
  | step _ ih => exact fun f a r h => relNB_succ P _ f a r (ih f a r h)

theorem relNB_le_rel (P : Program) (n : Nat) : CallRel.Le (P.relNB S rd n) (P.RelB S rd) :=
  fun _ _ _ h => ⟨n, h⟩

variable (S) in
/-- A family of continuations, monotone in the call relation and reached at a finite depth. -/
structure FinitaryB (P : Program) (rd : Reader) (F : CallRel → Prop) : Prop where
  mono : ∀ C C', CallRel.Le C C' → F C → F C'
  finite : F (P.RelB S rd) → ∃ n, F (P.relNB S rd n)

mutual
theorem holdsB_finite (P : Program) :
    ∀ (s : Stmt) (F : CallRel → Prop) (kret : List E → Prop), FinitaryB S P rd F →
      Stmt.HoldsB S (P.RelB S rd) rd σ s (F (P.RelB S rd)) kret →
        ∃ n, Stmt.HoldsB S (P.relNB S rd n) rd σ s (F (P.relNB S rd n)) kret
  | .atom _, F, _, hF, h => (hF.finite h.2).imp fun _ hn => ⟨h.1, hn⟩
  | .ite c z n', F, kret, hF, h => by
      by_cases hc : σ c = 0
      · obtain ⟨n, hn⟩ := holdsListB_finite P z F kret hF (h.2.1 hc)
        exact ⟨n, h.1, fun _ => hn, fun hc' => absurd hc hc'⟩
      · obtain ⟨n, hn⟩ := holdsListB_finite P n' F kret hF (h.2.2 hc)
        exact ⟨n, h.1, fun hc' => absurd hc' hc, fun _ => hn⟩
  | .match_ x arms, F, kret, hF, h => holdsArmsB_finite P x arms 0 F kret hF h
  | .call f args rets, F, _, hF, h => by
      obtain ⟨n1, h1⟩ := h.1
      obtain ⟨n2, h2⟩ := hF.finite h.2
      exact ⟨max n1 n2, relNB_mono P (le_max_left _ _) _ _ _ h1,
        hF.mono _ _ (relNB_mono P (le_max_right _ _)) h2⟩
  | .callIf c f args, F, _, hF, h => by
      obtain ⟨n2, h2⟩ := hF.finite h.2.2
      by_cases hc : σ c ≠ 0
      · obtain ⟨n1, h1⟩ := h.2.1 hc
        exact ⟨max n1 n2, h.1, fun _ => relNB_mono P (le_max_left _ _) _ _ _ h1,
          hF.mono _ _ (relNB_mono P (le_max_right _ _)) h2⟩
      · exact ⟨n2, h.1, fun hc' => absurd hc' hc, h2⟩
  | .dispatch x fs args rets, F, _, hF, h => by
      obtain ⟨j, hj, hx, n1, h1⟩ := h.1
      obtain ⟨n2, h2⟩ := hF.finite h.2
      exact ⟨max n1 n2, ⟨j, hj, hx, relNB_mono P (le_max_left _ _) _ _ _ h1⟩,
        hF.mono _ _ (relNB_mono P (le_max_right _ _)) h2⟩
  | .ret _, _, _, _, h => ⟨0, h⟩

theorem holdsListB_finite (P : Program) :
    ∀ (ss : List Stmt) (F : CallRel → Prop) (kret : List E → Prop), FinitaryB S P rd F →
      Stmt.HoldsListB S (P.RelB S rd) rd σ ss (F (P.RelB S rd)) kret →
        ∃ n, Stmt.HoldsListB S (P.relNB S rd n) rd σ ss (F (P.relNB S rd n)) kret
  | [], _, _, hF, h => hF.finite h
  | s :: ss, F, kret, hF, h =>
      holdsB_finite P s (fun C => Stmt.HoldsListB S C rd σ ss (F C) kret) kret
        ⟨fun C C' hC h => holdsListB_mono hC ss (hF.mono C C' hC) (fun _ h => h) h,
          holdsListB_finite P ss F kret hF⟩ h

theorem holdsArmsB_finite (P : Program) (x : V) :
    ∀ (arms : List (List Stmt)) (j : Nat) (F : CallRel → Prop) (kret : List E → Prop),
      FinitaryB S P rd F → Stmt.HoldsArmsB S (P.RelB S rd) rd σ x j arms (F (P.RelB S rd)) kret →
        ∃ n, Stmt.HoldsArmsB S (P.relNB S rd n) rd σ x j arms (F (P.relNB S rd n)) kret
  | [], _, _, _, _, h => h.elim
  | a :: as, j, F, kret, hF, h => by
      rcases h with ⟨hx, ha⟩ | ha
      · exact (holdsListB_finite P a F kret hF ha).imp fun _ hn => Or.inl ⟨hx, hn⟩
      · exact (holdsArmsB_finite P x as (j + 1) F kret hF ha).imp fun _ hn => Or.inr hn
end

/-- `Program.RelB` is a fixed point: a call holds exactly when the callee's body does, its own
calls under `Program.RelB`. -/
theorem relB_iff (P : Program) (f : String) (args rets : List E) :
    P.RelB S rd f args rets ↔ ∃ fn, P.find? f = some fn ∧ fn.SemB S (P.RelB S rd) rd args rets := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => exact hn.elim
    | succ n =>
        obtain ⟨fn, hf, h⟩ := hn
        exact ⟨fn, hf, fnSemB_mono (relNB_le_rel P n) fn args rets h⟩
  · rintro ⟨fn, hf, σ, hp, h⟩
    obtain ⟨n, hn⟩ := holdsListB_finite (σ := σ) P fn.body (fun _ => False) (fun rs => rs = rets)
      ⟨fun _ _ _ h => h, fun h => h.elim⟩ h
    exact ⟨n + 1, fn, hf, σ, hp, hn⟩

/-! ## Range checks -/

/-- The range-check atom, its auxiliary values chosen freely, is `rangeCheck_iff`'s relation. -/
theorem holdsB_rangeCheck (x y t1 t2 k : V) :
    (Atom.rangeCheck x y t1 t2 k).HoldsB S rd σ ↔
      LoadHolds rd (σ x) 0 (σ t1) ∧ σ k = σ x * σ y ∧ LoadHolds rd (σ y) 0 (σ t2) := Iff.rfl

end Lemmas


/-- A function's relation is its body's, once it is found by name. -/
theorem relB_iff_sem {P : Program} {rd : Reader} {f : String} {fn : Fn}
    (h : P.find? f = some fn) (args rets : List E) :
    P.RelB S rd f args rets ↔
      ∃ σ : Val, fn.params.map σ = args ∧
        Stmt.HoldsListB S (P.RelB S rd) rd σ fn.body False (fun rs => rs = rets) := by
  rw [relB_iff]
  simp only [h, Option.some.injEq, exists_eq_left', Fn.SemB]

/-- The same at a finite depth: the body's calls one level shallower. -/
theorem relNB_succ_iff {P : Program} {rd : Reader} {f : String} {fn : Fn}
    (h : P.find? f = some fn) (n : ℕ) (args rets : List E) :
    P.relNB S rd (n + 1) f args rets ↔
      ∃ σ : Val, fn.params.map σ = args ∧
        Stmt.HoldsListB S (P.relNB S rd n) rd σ fn.body False (fun rs => rs = rets) := by
  simp only [Program.relNB, h, Option.some.injEq, exists_eq_left', Fn.SemB]

/-! ## The deployed semantics

At `blakeDeployed` every definition above is the deployed one (`Core.lean`): `relB_deployed`
rewrites a generic statement at the deployed semantics into the deployed statement. -/

section Deployed

variable {rd : Reader} {σ : Val}

theorem atom_holdsB_deployed (a : Atom) : a.HoldsB blakeDeployed rd σ = a.Holds rd σ := by
  cases a <;> rfl

mutual
theorem holdsB_deployed (C : CallRel) :
    ∀ (s : Stmt) (next : Prop) (kret : List E → Prop),
      Stmt.HoldsB blakeDeployed C rd σ s next kret = Stmt.Holds C rd σ s next kret
  | .atom a, _, _ => by simp only [Stmt.HoldsB, Stmt.Holds, atom_holdsB_deployed]
  | .ite c z n, next, kret => by
      simp only [Stmt.HoldsB, Stmt.Holds, holdsListB_deployed C z, holdsListB_deployed C n]
  | .match_ x arms, next, kret => by
      simp only [Stmt.HoldsB, Stmt.Holds, holdsArmsB_deployed C x arms]
  | .call .., _, _ => rfl
  | .callIf .., _, _ => rfl
  | .dispatch .., _, _ => rfl
  | .ret _, _, _ => rfl

theorem holdsListB_deployed (C : CallRel) :
    ∀ (ss : List Stmt) (next : Prop) (kret : List E → Prop),
      Stmt.HoldsListB blakeDeployed C rd σ ss next kret = Stmt.HoldsList C rd σ ss next kret
  | [], _, _ => rfl
  | s :: ss, next, kret => by
      simp only [Stmt.HoldsListB, Stmt.HoldsList, holdsListB_deployed C ss, holdsB_deployed C s]

theorem holdsArmsB_deployed (C : CallRel) (x : V) :
    ∀ (arms : List (List Stmt)) (j : Nat) (next : Prop) (kret : List E → Prop),
      Stmt.HoldsArmsB blakeDeployed C rd σ x j arms next kret =
        Stmt.HoldsArms C rd σ x j arms next kret
  | [], _, _, _ => rfl
  | a :: as, j, next, kret => by
      simp only [Stmt.HoldsArmsB, Stmt.HoldsArms, holdsListB_deployed C a,
        holdsArmsB_deployed C x as (j + 1)]
end

theorem fnSemB_deployed (C : CallRel) (f : Fn) :
    f.SemB blakeDeployed C rd = f.Sem C rd := by
  funext args rets
  simp only [Fn.SemB, Fn.Sem, holdsListB_deployed]

theorem relNB_deployed (P : Program) : ∀ n, P.relNB blakeDeployed rd n = P.relN rd n
  | 0 => rfl
  | n + 1 => by
      funext f args rets
      simp only [Program.relNB, Program.relN, relNB_deployed P n, fnSemB_deployed]

/-- **The deployed call relation**: `Program.RelB` at the deployed semantics. -/
theorem relB_deployed (P : Program) : P.RelB blakeDeployed rd = P.Rel rd := by
  funext f args rets
  simp only [Program.RelB, Program.Rel, relNB_deployed]

end Deployed

/-! ## Weaker semantics

A semantics whose relation implies another's gives the other's relations (`relB_monoS`): the
deployed semantics' are the Flock-blind one's (`blakeDeployed` checks canonical cells). -/

section MonoS

/-- `S`'s relation implies `S'`'s. -/
def _root_.LeanVM.Semantics.BlakeSem.Le (S S' : BlakeSem) : Prop :=
  ∀ m cv0 cv1 out0 out1 md, S.check m cv0 cv1 out0 out1 md → S'.check m cv0 cv1 out0 out1 md

variable {S' : BlakeSem} {rd : Reader} {σ : Val}

theorem atom_holdsB_monoS (hS : S.Le S') {a : Atom} (h : a.HoldsB S rd σ) : a.HoldsB S' rd σ := by
  cases a <;> first | exact h | exact hS _ _ _ _ _ _ h

mutual
theorem holdsB_monoS (hS : S.Le S') {C C' : CallRel} (hC : CallRel.Le C C') :
    ∀ (s : Stmt) {next next' : Prop} {kret kret' : List E → Prop}, (next → next') →
      (∀ r, kret r → kret' r) → Stmt.HoldsB S C rd σ s next kret →
        Stmt.HoldsB S' C' rd σ s next' kret'
  | .atom _, _, _, _, _, hn, _, h => ⟨atom_holdsB_monoS hS h.1, hn h.2⟩
  | .ite _ z n, _, _, _, _, hn, hk, h =>
      ⟨h.1, fun hc => holdsListB_monoS hS hC z hn hk (h.2.1 hc),
        fun hc => holdsListB_monoS hS hC n hn hk (h.2.2 hc)⟩
  | .match_ x arms, _, _, _, _, hn, hk, h => holdsArmsB_monoS hS hC x arms 0 hn hk h
  | .call .., _, _, _, _, hn, _, h => ⟨hC _ _ _ h.1, hn h.2⟩
  | .callIf .., _, _, _, _, hn, _, h => ⟨h.1, fun hc => hC _ _ _ (h.2.1 hc), hn h.2.2⟩
  | .dispatch .., _, _, _, _, hn, _, h =>
      ⟨let ⟨j, hj, hx, hc⟩ := h.1; ⟨j, hj, hx, hC _ _ _ hc⟩, hn h.2⟩
  | .ret _, _, _, _, _, _, hk, h => hk _ h

theorem holdsListB_monoS (hS : S.Le S') {C C' : CallRel} (hC : CallRel.Le C C') :
    ∀ (ss : List Stmt) {next next' : Prop} {kret kret' : List E → Prop}, (next → next') →
      (∀ r, kret r → kret' r) → Stmt.HoldsListB S C rd σ ss next kret →
        Stmt.HoldsListB S' C' rd σ ss next' kret'
  | [], _, _, _, _, hn, _, h => hn h
  | s :: ss, _, _, _, _, hn, hk, h =>
      holdsB_monoS hS hC s (holdsListB_monoS hS hC ss hn hk) hk h

theorem holdsArmsB_monoS (hS : S.Le S') {C C' : CallRel} (hC : CallRel.Le C C') (x : V) :
    ∀ (arms : List (List Stmt)) (j : Nat) {next next' : Prop} {kret kret' : List E → Prop},
      (next → next') → (∀ r, kret r → kret' r) → Stmt.HoldsArmsB S C rd σ x j arms next kret →
        Stmt.HoldsArmsB S' C' rd σ x j arms next' kret'
  | [], _, _, _, _, _, _, _, h => h
  | a :: as, j, _, _, _, _, hn, hk, h =>
      h.imp (fun h => ⟨h.1, holdsListB_monoS hS hC a hn hk h.2⟩)
        (holdsArmsB_monoS hS hC x as (j + 1) hn hk)
end

theorem relNB_monoS (hS : S.Le S') (P : Program) :
    ∀ n, CallRel.Le (P.relNB S rd n) (P.relNB S' rd n)
  | 0 => fun _ _ _ h => h.elim
  | n + 1 => fun _ _ _ ⟨fn, hf, σ, hp, h⟩ =>
      ⟨fn, hf, σ, hp, holdsListB_monoS hS (relNB_monoS hS P n) fn.body id (fun _ h => h) h⟩

/-- **A weaker semantics' relation**: `S`'s relation implying `S'`'s, a program's calls under
`S` hold under `S'`. -/
theorem relB_monoS (hS : S.Le S') (P : Program) : CallRel.Le (P.RelB S rd) (P.RelB S' rd) :=
  fun _ _ _ ⟨n, h⟩ => ⟨n, relNB_monoS hS P n _ _ _ h⟩

end MonoS

/-! ## Functions without `BLAKE2S`

A function with no `BLAKE2S` atom, calling only such functions, has the same relation under every
semantics (`relB_eq_of_freeOn`), so a lemma about its deployed relation is one about its relation
under any semantics (`relB_iff_rel_of_freeOn`). `Program.FreeOn P F` checks a set `F` of names
closed under calls, each function of `F` free of `BLAKE2S`; the kernel evaluates it for the
guest's (`decide +kernel`). -/

section Free

mutual
/-- A statement with no `BLAKE2S` atom, every function it calls in `F`. -/
def Stmt.freeIn (F : List String) : Stmt → Bool
  | .atom (.blake2s ..) => false
  | .atom _ => true
  | .ite _ z n => Stmt.freeInList F z && Stmt.freeInList F n
  | .match_ _ arms => Stmt.freeInArms F arms
  | .call f _ _ => F.contains f
  | .callIf _ f _ => F.contains f
  | .dispatch _ fs _ _ => fs.all F.contains
  | .ret _ => true

/-- A block with no `BLAKE2S` atom, every function it calls in `F`. -/
def Stmt.freeInList (F : List String) : List Stmt → Bool
  | [] => true
  | s :: ss => Stmt.freeIn F s && Stmt.freeInList F ss

/-- Arms with no `BLAKE2S` atom, every function they call in `F`. -/
def Stmt.freeInArms (F : List String) : List (List Stmt) → Bool
  | [] => true
  | a :: as => Stmt.freeInList F a && Stmt.freeInArms F as
end

/-- Every function of `F` that `P` has is free of `BLAKE2S` and calls only functions of `F`. -/
def Program.FreeOn (P : Program) (F : List String) : Bool :=
  F.all fun f => match P.find? f with
    | some fn => Stmt.freeInList F fn.body
    | none => true

variable {S' : BlakeSem} {rd : Reader} {σ : Val} {F : List String}

/-- Two call relations agreeing on the names of `F`. -/
def CallRel.AgreeOn (F : List String) (C C' : CallRel) : Prop :=
  ∀ f, F.contains f = true → ∀ a r, C f a r ↔ C' f a r

mutual
theorem holdsB_freeIn {C C' : CallRel} (hC : CallRel.AgreeOn F C C') :
    ∀ (s : Stmt), Stmt.freeIn F s = true → ∀ (next : Prop) (kret : List E → Prop),
      (Stmt.HoldsB S C rd σ s next kret ↔ Stmt.HoldsB S' C' rd σ s next kret)
  | .atom a, h, _, _ => by
      cases a <;> first | exact Iff.rfl | simp [Stmt.freeIn] at h
  | .ite c z n, h, next, kret => by
      simp only [Stmt.freeIn, Bool.and_eq_true] at h
      simp only [Stmt.HoldsB, holdsListB_freeIn hC z h.1, holdsListB_freeIn hC n h.2]
  | .match_ x arms, h, next, kret => by
      simp only [Stmt.freeIn] at h
      exact holdsArmsB_freeIn hC x arms h 0 next kret
  | .call f args rets, h, next, kret => by
      simp only [Stmt.freeIn] at h
      simp only [Stmt.HoldsB, hC f h]
  | .callIf c f args, h, next, kret => by
      simp only [Stmt.freeIn] at h
      simp only [Stmt.HoldsB, hC f h]
  | .dispatch x fs args rets, h, next, kret => by
      simp only [Stmt.freeIn, List.all_eq_true] at h
      simp only [Stmt.HoldsB]
      constructor
      · rintro ⟨⟨j, hj, hx, hc⟩, hn⟩
        exact ⟨⟨j, hj, hx, (hC _ (h _ (List.getElem_mem hj)) _ _).mp hc⟩, hn⟩
      · rintro ⟨⟨j, hj, hx, hc⟩, hn⟩
        exact ⟨⟨j, hj, hx, (hC _ (h _ (List.getElem_mem hj)) _ _).mpr hc⟩, hn⟩
  | .ret _, _, _, _ => Iff.rfl

theorem holdsListB_freeIn {C C' : CallRel} (hC : CallRel.AgreeOn F C C') :
    ∀ (ss : List Stmt), Stmt.freeInList F ss = true → ∀ (next : Prop) (kret : List E → Prop),
      (Stmt.HoldsListB S C rd σ ss next kret ↔ Stmt.HoldsListB S' C' rd σ ss next kret)
  | [], _, _, _ => Iff.rfl
  | s :: ss, h, next, kret => by
      simp only [Stmt.freeInList, Bool.and_eq_true] at h
      simp only [Stmt.HoldsListB]
      rw [holdsB_freeIn hC s h.1, holdsListB_freeIn hC ss h.2]

theorem holdsArmsB_freeIn {C C' : CallRel} (hC : CallRel.AgreeOn F C C') (x : V) :
    ∀ (arms : List (List Stmt)), Stmt.freeInArms F arms = true →
      ∀ (j : Nat) (next : Prop) (kret : List E → Prop),
      (Stmt.HoldsArmsB S C rd σ x j arms next kret ↔ Stmt.HoldsArmsB S' C' rd σ x j arms next kret)
  | [], _, _, _, _ => Iff.rfl
  | a :: as, h, j, next, kret => by
      simp only [Stmt.freeInArms, Bool.and_eq_true] at h
      simp only [Stmt.HoldsArmsB]
      rw [holdsListB_freeIn hC a h.1, holdsArmsB_freeIn hC x as h.2 (j + 1)]
end

theorem relNB_agreeOn {P : Program} (hP : P.FreeOn F = true) :
    ∀ n, CallRel.AgreeOn F (P.relNB S rd n) (P.relNB S' rd n)
  | 0 => fun _ _ _ _ => Iff.rfl
  | n + 1 => fun f hf a r => by
      simp only [Program.relNB]
      have hfn := List.all_eq_true.mp hP f (List.contains_iff_mem.mp hf)
      constructor
      · rintro ⟨fn, hfind, σ, hp, h⟩
        rw [hfind] at hfn
        exact ⟨fn, hfind, σ, hp, (holdsListB_freeIn (relNB_agreeOn hP n) fn.body hfn _ _).mp h⟩
      · rintro ⟨fn, hfind, σ, hp, h⟩
        rw [hfind] at hfn
        exact ⟨fn, hfind, σ, hp, (holdsListB_freeIn (relNB_agreeOn hP n) fn.body hfn _ _).mpr h⟩

/-- **A function free of `BLAKE2S`** has the same relation under every semantics. -/
theorem relB_eq_of_freeOn {P : Program} (hP : P.FreeOn F = true) {f : String} (hf : f ∈ F)
    (args rets : List E) : P.RelB S rd f args rets ↔ P.RelB S' rd f args rets := by
  constructor
  · rintro ⟨n, h⟩
    exact ⟨n, (relNB_agreeOn hP n f (List.contains_iff_mem.mpr hf) args rets).mp h⟩
  · rintro ⟨n, h⟩
    exact ⟨n, (relNB_agreeOn hP n f (List.contains_iff_mem.mpr hf) args rets).mpr h⟩

/-- A function free of `BLAKE2S`: its relation under any semantics is its deployed one. -/
theorem relB_iff_rel_of_freeOn {P : Program} (hP : P.FreeOn F = true) {f : String} (hf : f ∈ F)
    (args rets : List E) : P.RelB S rd f args rets ↔ P.Rel rd f args rets := by
  rw [relB_eq_of_freeOn (S' := blakeDeployed) hP hf, relB_deployed]

end Free

end
end LeanVM.Guest.Core
