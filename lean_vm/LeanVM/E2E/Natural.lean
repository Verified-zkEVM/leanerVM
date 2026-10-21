/-
  LeanVM.E2E.Natural

  V_I in two monads, related query by query: a relation between the computations of two monads,
  closed under `pure` and `bind` and holding of the two hashes' queries, holds of V_I's two runs;
  so V_I commutes with every monad morphism.
-/

module

public import LeanVM.E2E.Statement

/-!
# V_I is natural in its monad

`Engine.lean`'s `closed_idealVerify`: a predicate on computations closed under `pure` and `bind`
holds of V_I when it holds of every hash query. Here the same for a relation `R` between the
computations of two monads `m`, `n`, closed under `pure` and `bind` (`R (pure a) (pure a)`;
`R x y` and `R (f a) (g a)` for every `a` give `R (x >>= f) (y >>= g)`): if `R (H x) (H' x)` for
every string, `R` relates V_I with `H` to V_I with `H'` (`rel_idealVerify`), and every helper on the
way (`rel_nodeStep`, `rel_closure`, `rel_runProof`, `rel_outerChecksWith`, …).

The main instance is a **monad morphism** `φ : m → n` (`IsMorphism`: it preserves `pure` and
`bind`), with `R x y := φ x = y`: V_I commutes with it (`idealVerify_natural`),
`φ (idealVerify H …) = idealVerify (φ ∘ H) …`. `Budget.lean` instantiates it to the game's
budgeted run.
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom

@[expose] public section

section Rel
variable {m n : Type → Type} [Monad m] [Monad n] (R : ∀ {α : Type}, m α → n α → Prop)
  (hpure : ∀ {α : Type} (a : α), R (pure a) (pure a))
  (hbind : ∀ {α β : Type} (x : m α) (y : n α) (f : α → m β) (g : α → n β), R x y →
    (∀ a, R (f a) (g a)) → R (x >>= f) (y >>= g))
include hpure hbind

/-- A closed relation relates two maps. -/
theorem rel_map [LawfulMonad m] [LawfulMonad n] {α β : Type} (f : α → β) (x : m α) (y : n α)
    (hx : R x y) : R (f <$> x) (f <$> y) := by
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]; exact hbind _ _ _ _ hx fun _ ↦ hpure _

/-- A closed relation relates two `mapM`s of related computations. -/
theorem rel_mapM [LawfulMonad m] [LawfulMonad n] {α β : Type} (f : α → m β) (g : α → n β)
    (hf : ∀ a, R (f a) (g a)) : ∀ l : List α, R (l.mapM f) (l.mapM g)
  | [] => by rw [List.mapM_nil, List.mapM_nil]; exact hpure _
  | a :: l => by
    rw [List.mapM_cons, List.mapM_cons]
    exact hbind _ _ _ _ (hf a) fun _ ↦ hbind _ _ _ _ (rel_mapM f g hf l) fun _ ↦ hpure _

/-- A closed relation relates two `allM`s of related computations. -/
theorem rel_allM {α : Type} (f : α → m Bool) (g : α → n Bool) (hf : ∀ a, R (f a) (g a)) :
    ∀ l : List α, R (l.allM f) (l.allM g)
  | [] => by rw [List.allM_nil, List.allM_nil]; exact hpure _
  | a :: l => by
    rw [List.allM_cons, List.allM_cons]
    exact hbind _ _ _ _ (hf a) fun b ↦ by
      cases b
      · exact hpure _
      · exact rel_allM f g hf l

/-- A closed relation relates two `for` loops over a list with related bodies. -/
theorem rel_forIn {α β : Type} (f : α → β → m (ForInStep β)) (g : α → β → n (ForInStep β))
    (hf : ∀ a b, R (f a b) (g a b)) : ∀ (l : List α) (b : β), R (forIn l b f) (forIn l b g)
  | [], _ => hpure _
  | a :: l, b => by
    rw [List.forIn_cons, List.forIn_cons]
    exact hbind _ _ _ _ (hf a b) fun s ↦ by
      cases s
      · exact hpure _
      · exact rel_forIn f g hf l _

variable (H : Bytes → m Digest) (H' : Bytes → n Digest) (hH : ∀ x, R (H x) (H' x))
include hH

/-- A closed relation relates two Merkle roots computed with related hashes. -/
theorem rel_rootOfLevelM [LawfulMonad m] [LawfulMonad n] :
    ∀ (k : ℕ) (level : List Digest), R (rootOfLevelM H k level) (rootOfLevelM H' k level)
  | 0, _ => hpure _
  | k + 1, _ =>
    hbind _ _ _ _ (rel_mapM R hpure hbind _ _ (fun _ ↦ hH _) _) fun _ ↦ rel_rootOfLevelM k _

/-- A closed relation relates two table checks with related hashes. -/
theorem rel_tableOKWith (rows : List BlakeRow) : R (tableOKWith H rows) (tableOKWith H' rows) := by
  unfold tableOKWith
  repeat' first
    | exact hpure _
    | (refine rel_allM R hpure hbind _ _ (fun _ ↦ ?_) _)
    | (refine hbind _ _ _ _ (hH _) fun _ ↦ ?_)
    | split

/-- A closed relation relates one node of V_I with related hashes. -/
theorem rel_nodeStep [LawfulMonad m] [LawfulMonad n] (prog : Program) (seed : Digest)
    (ip : IdealProof) (ν : Node) :
    R (nodeStep H prog seed ip ν) (nodeStep H' prog seed ip ν) := by
  unfold nodeStep
  repeat' first
    | exact hpure _
    | exact hH _
    | exact rel_mapM R hpure hbind _ _ (fun _ ↦ hH _) _
    | exact rel_rootOfLevelM R hpure hbind H H' hH _ _
    | exact rel_tableOKWith R hpure hbind H H' hH _
    | (refine hbind _ _ _ _ ?_ fun _ ↦ ?_)
    | (refine rel_forIn R hpure hbind _ _ (fun _ _ ↦ ?_) _ _)
    | split
    | dsimp only

/-- A closed relation relates V_I's closures with related hashes. -/
theorem rel_closure [LawfulMonad m] [LawfulMonad n] (prog : Program) (seed : Digest)
    (ip : IdealProof) : ∀ (fuel : ℕ) (todo done : List Node),
      R (closure H prog seed ip fuel todo done) (closure H' prog seed ip fuel todo done)
  | _, [], _ => by unfold closure; exact hpure _
  | 0, _ :: _, _ => by unfold closure; exact hpure _
  | fuel + 1, ν :: todo, done => by
    unfold closure
    split
    · exact rel_closure prog seed ip fuel _ _
    · refine hbind _ _ _ _ (rel_nodeStep R hpure hbind H H' hH prog seed ip ν) fun o ↦ ?_
      split
      · exact hpure _
      · exact rel_closure prog seed ip fuel _ _

/-- A closed relation relates two climbs of a Merkle path with related hashes. -/
theorem rel_climb : ∀ (node : Digest) (q : ℕ) (path : List Digest),
    R (climb H node q path) (climb H' node q path)
  | _, _, [] => hpure _
  | _, _, _ :: _ => by
    unfold climb
    dsimp only
    split <;> exact hbind _ _ _ _ (hH _) fun _ ↦ rel_climb _ _ _

/-- A closed relation relates two checks of the openings with related hashes. -/
theorem rel_openAll (root : Digest) (height width : ℕ) :
    ∀ (qs : List ℕ) (os : List Opening),
      R (openAll H root height width qs os) (openAll H' root height width qs os)
  | [], _ => hpure _
  | _ :: _, [] => hpure _
  | q :: qs, o :: os => by
    unfold openAll
    refine hbind _ _ _ _ ?_ fun b ↦ ?_
    · unfold openOne
      split
      · exact hbind _ _ _ _ (hH _) fun _ ↦
          hbind _ _ _ _ (rel_climb R hpure hbind H H' hH _ _ _) fun _ ↦ hpure _
      · exact hpure _
    · split
      · exact hbind _ _ _ _ (rel_openAll root height width qs os) fun _ ↦ hpure _
      · exact hpure _

/-- A closed relation relates the compiled readings of every program with related hashes. -/
theorem rel_run {α : Type} (P : Prog α) : ∀ s : St, R (run H P s) (run H' P s) := by
  induction P with
  | ret a => intro s; exact hpure _
  | fail => intro s; exact hpure _
  | read k ih =>
    intro s; unfold Compile.run; split
    · exact hpure _
    · exact hbind _ _ _ _ (hH _) fun _ ↦ ih _ _
  | sample k ih => intro s; exact hbind _ _ _ _ (hH _) fun _ ↦ ih _ _
  | grind bits k ih =>
    intro s; unfold Compile.run; split
    · exact hpure _
    · refine hbind _ _ _ _ (hH _) fun _ ↦ hbind _ _ _ _ (hH _) fun _ ↦
        hbind _ _ _ _ (hH _) fun _ ↦ ?_
      split
      · exact ih _
      · exact hpure _
  | commit height width k ih =>
    intro s; unfold Compile.run; split
    · refine hbind _ _ _ _ (hH _) fun _ ↦ hbind _ _ _ _ (hH _) fun _ ↦ ?_
      split
      · exact ih _
      · exact hpure _
    · exact hpure _
  | query i ps k ih =>
    intro s; unfold Compile.run; split
    · exact hpure _
    · refine hbind _ _ _ _ (rel_openAll R hpure hbind H H' hH _ _ _ _ _) fun o ↦ ?_
      split
      · exact ih _ _
      · exact hpure _

/-- A closed relation relates a program's runs on a proof with related hashes. -/
theorem rel_runProof (P : Prog Bool) (seed : Digest) (π : Proof) :
    R (runProof H P seed π) (runProof H' P seed π) := by
  unfold runProof
  refine hbind _ _ _ _ (rel_run R hpure hbind H H' hH P _) fun o ↦ ?_
  split <;> exact hpure _

omit hH in
/-- A closed relation relates the DA squeezes with related hashes. -/
theorem rel_squeezesWith (HD : List UInt8 → m LeanDa.Digest) (HD' : List UInt8 → n LeanDa.Digest)
    (hHD : ∀ x, R (HD x) (HD' x)) :
    ∀ (k : ℕ) (state : LeanDa.Digest), R (Da.squeezesWith HD k state) (Da.squeezesWith HD' k state)
  | 0, _ => hpure _
  | k + 1, _ => hbind _ _ _ _ (hHD _) fun _ ↦
      hbind _ _ _ _ (rel_squeezesWith HD HD' hHD k _) fun _ ↦ hpure _

/-- A closed relation relates V_I's outer checks with related hashes. -/
theorem rel_outerChecksWith [LawfulMonad m] [LawfulMonad n] (prog : Program) (s : NodeStatement) :
    R (outerChecksWith H prog s) (outerChecksWith H' prog s) := by
  have hHD : ∀ x, R (Da.daHash H x) (Da.daHash H' x) := fun x ↦
    rel_map R hpure hbind _ _ _ (hH x)
  unfold outerChecksWith
  refine hbind _ _ _ _ (rel_allM R hpure hbind _ _ (fun c ↦ ?_) _) fun _ ↦ hpure _
  refine hbind _ _ _ _ ?_ fun _ ↦ hpure _
  unfold Da.vectorDigestOfWith Da.membershipVectorWith Da.membershipChallengesWith
  exact hbind _ _ _ _ (rel_map R hpure hbind _ _ _ (hbind _ _ _ _ (hHD _) fun _ ↦
    hbind _ _ _ _ (hHD _) fun _ ↦ hbind _ _ _ _ (hHD _) fun _ ↦
      rel_squeezesWith R hpure hbind _ _ hHD _ _)) fun _ ↦ hHD _

/-- **V_I with related hashes is related**: a relation between two monads' computations closed
under `pure` and `bind` and relating the two hashes' queries relates V_I's two runs. -/
theorem rel_idealVerify [LawfulMonad m] [LawfulMonad n] (prog : Program) (ip : IdealProof)
    (fuel : ℕ) (s : NodeStatement) :
    R (idealVerify H prog ip fuel s) (idealVerify H' prog ip fuel s) := by
  unfold idealVerify verifyBlindWith seedWith
  repeat' first
    | exact hpure _
    | exact hH _
    | exact rel_runProof R hpure hbind H H' hH _ _ _
    | exact rel_outerChecksWith R hpure hbind H H' hH _ _
    | exact rel_closure R hpure hbind H H' hH _ _ _ _ _ _
    | (refine hbind _ _ _ _ ?_ fun _ ↦ ?_)
    | split

end Rel

/-! ## Monad morphisms -/

/-- **A monad morphism**: a map of computations preserving `pure` and `bind`. -/
structure IsMorphism {m n : Type → Type} [Monad m] [Monad n] (φ : ∀ {α : Type}, m α → n α) :
    Prop where
  /-- It preserves `pure`. -/
  pure : ∀ {α : Type} (a : α), φ (pure a) = pure a
  /-- It preserves `bind`. -/
  bind : ∀ {α β : Type} (x : m α) (f : α → m β), φ (x >>= f) = φ x >>= fun a ↦ φ (f a)

/-- **V_I is natural in its monad**: a monad morphism maps V_I with `H` to V_I with the image of
`H`. -/
theorem idealVerify_natural {m n : Type → Type} [Monad m] [Monad n] [LawfulMonad m]
    [LawfulMonad n] {φ : ∀ {α : Type}, m α → n α} (hφ : IsMorphism @φ) (H : Bytes → m Digest)
    (prog : Program) (ip : IdealProof) (fuel : ℕ) (s : NodeStatement) :
    φ (idealVerify H prog ip fuel s) = idealVerify (fun x ↦ φ (H x)) prog ip fuel s :=
  rel_idealVerify (fun {α : Type} (x : m α) (y : n α) ↦ φ x = y) (fun a ↦ hφ.pure a)
    (fun x _ f _ hx hf ↦ by rw [hφ.bind, hx]; exact congrArg _ (funext hf)) H _
    (fun _ ↦ rfl) prog ip fuel s

end
end LeanVM.E2E
