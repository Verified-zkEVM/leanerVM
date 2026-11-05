/-
  LeanerVM.Protocol.ToArkLib.RunCodecHom

  A prover's run against a wire, carried along a monad morphism: mapping the run is running
  against the mapped wire. Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.RunCodec

/-!
# Running against a mapped wire

`RoundCodec.map ψ c` is the wire `c` with every encoder's and every source's computation mapped
along the monad morphism `ψ : w →ᵐ w'`. `Prover.runWith_hom`: mapping the run of a prover with no
shared oracle against `c` is its run against `c.map ψ`. The wires of
`LeanerVM.Protocol.ToArkLib.RunCodec` map to the same wires over the mapped encoders and sources
(`RoundCodec.map_append`, `map_msg`, `map_chal`, `map_rounds`, `map_gkr`, …); `map_append` rests on
`Fin.fappend₂` commuting with a map applied at every index (`Fin.fappend₂_map`). The `_of` forms
(`map_append_of`, …) conclude at a given target wire, so that `apply` unfolds a composite wire.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec

@[expose] public section

/-! ## Appending tuples commutes with a pointwise map -/

namespace Fin

universe u v w₁ w₂

variable {A : Sort u} {B : Sort v} {F : A → B → Sort w₁} {G : A → B → Sort w₂}
  (g : ∀ a b, F a b → G a b)

theorem fcons₂_map {n : ℕ} {α₁ : A} {β₁ : Fin n → A} {α₂ : B} {β₂ : Fin n → B}
    (a : F α₁ α₂) (b : (i : Fin n) → F (β₁ i) (β₂ i)) (i : Fin (n + 1)) :
    g _ _ (Fin.fcons₂ (F := F) a b i) =
      Fin.fcons₂ (F := G) (g _ _ a) (fun i ↦ g _ _ (b i)) i := by
  cases n with
  | zero => match i with | ⟨0, _⟩ => rfl
  | succ n => match i with | ⟨0, _⟩ => rfl | ⟨k + 1, _⟩ => rfl

theorem fconcat₂_map {n : ℕ} {α₁ : Fin n → A} {β₁ : A} {α₂ : Fin n → B} {β₂ : B}
    (u : (i : Fin n) → F (α₁ i) (α₂ i)) (a : F β₁ β₂) (i : Fin (n + 1)) :
    g _ _ (Fin.fconcat₂ (F := F) u a i) =
      Fin.fconcat₂ (F := G) (fun i ↦ g _ _ (u i)) (g _ _ a) i := by
  induction n with
  | zero => match i with | ⟨0, _⟩ => rfl
  | succ n ih =>
    have h := fcons₂_map g (u 0) (Fin.fconcat₂ (F := F) (fun i ↦ u (Fin.succ i)) a) i
    have h' : (fun j ↦ g _ _ (Fin.fconcat₂ (F := F) (fun i ↦ u (Fin.succ i)) a j)) =
        Fin.fconcat₂ (F := G) (fun i ↦ g _ _ (u (Fin.succ i))) (g _ _ a) :=
      funext fun j ↦ ih _ j
    rw [h'] at h
    exact h

theorem fappend₂_map {m n : ℕ} {α₁ : Fin m → A} {β₁ : Fin n → A} {α₂ : Fin m → B}
    {β₂ : Fin n → B} (u : (i : Fin m) → F (α₁ i) (α₂ i)) (v : (i : Fin n) → F (β₁ i) (β₂ i))
    (i : Fin (m + n)) :
    g _ _ (Fin.fappend₂ (F := F) u v i) =
      Fin.fappend₂ (F := G) (fun i ↦ g _ _ (u i)) (fun i ↦ g _ _ (v i)) i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h := fconcat₂_map g (Fin.fappend₂ (F := F) u fun i ↦ v (Fin.castSucc i))
      (v (Fin.last n)) i
    have h' : (fun j ↦ g _ _ (Fin.fappend₂ (F := F) u (fun i ↦ v (Fin.castSucc i)) j)) =
        Fin.fappend₂ (F := G) (fun i ↦ g _ _ (u i)) (fun i ↦ g _ _ (v (Fin.castSucc i))) :=
      funext fun j ↦ ih _ j
    rw [h'] at h
    rw [Fin.fappend₂_succ, Fin.fappend₂_succ]
    exact h

end Fin

/-! ## The mapped wire -/

namespace RoundCodec

variable {w w' : Type → Type} [Monad w] [Monad w'] (ψ : w →ᵐ w')

/-- The wire with every encoder's and every source's computation mapped along `ψ`. -/
def map {n : ℕ} {pSpec : ProtocolSpec n} (c : RoundCodec w pSpec) : RoundCodec w' pSpec where
  send i h x := ψ (c.send i h x)
  draw i h := ψ (c.draw i h)

omit [Monad w] in
theorem ext' {n : ℕ} {pSpec : ProtocolSpec n} {c c' : RoundCodec w pSpec}
    (hs : ∀ i h x, c.send i h x = c'.send i h x) (hd : ∀ i h, c.draw i h = c'.draw i h) :
    c = c' := by
  cases c; cases c'
  congr
  · funext i h x; exact hs i h x
  · funext i h; exact hd i h

theorem map_empty : (empty : RoundCodec w !p[]).map ψ = empty :=
  ext' (fun i ↦ i.elim0) fun i ↦ i.elim0

theorem map_append {m n : ℕ} {p₁ : ProtocolSpec m} {p₂ : ProtocolSpec n} (c₁ : RoundCodec w p₁)
    (c₂ : RoundCodec w p₂) : (c₁.append c₂).map ψ = (c₁.map ψ).append (c₂.map ψ) := by
  refine ext' (fun i h x ↦ ?_) fun i h ↦ ?_
  · exact congrFun (congrFun (Fin.fappend₂_map (A := Direction) (B := Type)
      (F := fun dir type ↦ dir = .P_to_V → type → w Unit)
      (G := fun dir type ↦ dir = .P_to_V → type → w' Unit) (α₁ := p₁.dir) (β₁ := p₂.dir)
      (α₂ := p₁.Type) (β₂ := p₂.Type)
      (fun _ _ f h x ↦ ψ (f h x)) c₁.send c₂.send i) h) x
  · exact congrFun (Fin.fappend₂_map (A := Direction) (B := Type)
      (F := fun dir type ↦ dir = .V_to_P → w type)
      (G := fun dir type ↦ dir = .V_to_P → w' type) (α₁ := p₁.dir) (β₁ := p₂.dir)
      (α₂ := p₁.Type) (β₂ := p₂.Type)
      (fun _ _ f h ↦ ψ (f h)) c₁.draw c₂.draw i) h

theorem map_msg {M : Type} (enc : M → w Unit) : (msg enc).map ψ = msg fun x ↦ ψ (enc x) :=
  ext' (fun | ⟨0, _⟩, _, _ => rfl) fun | ⟨0, _⟩, h => nomatch h

theorem map_sendOne {M : Type} (enc : M → w Unit) :
    (sendOne enc).map ψ = sendOne fun x ↦ ψ (enc x) :=
  ext' (fun | ⟨0, _⟩, _, _ => rfl) fun | ⟨0, _⟩, h => nomatch h

theorem map_chal {C : Type} (smp : w C) : (chal smp).map ψ = chal (ψ smp) :=
  ext' (fun | ⟨0, _⟩, h, _ => nomatch h) fun | ⟨0, _⟩, _ => rfl

theorem map_chals {C : Type} (smp : w C) (k : ℕ) : (chals smp k).map ψ = chals (ψ smp) k := by
  induction k with
  | zero => exact map_empty ψ
  | succ k ih => exact (map_append ψ (chals smp k) (chal smp)).trans (by rw [ih, map_chal]; rfl)

theorem map_round {C : Type} {d : ℕ} (enc : Vector C (d + 1) → w Unit) (smp : w C) :
    (round enc smp).map ψ = round (fun x ↦ ψ (enc x)) (ψ smp) := by
  exact (map_append ψ _ _).trans (by rw [map_msg, map_chal]; rfl)

theorem map_rounds {C : Type} {d : ℕ} (enc : Vector C (d + 1) → w Unit) (smp : w C) (k : ℕ) :
    (rounds enc smp k).map ψ = rounds (fun x ↦ ψ (enc x)) (ψ smp) k := by
  induction k with
  | zero => exact map_empty ψ
  | succ k ih =>
    exact (map_append ψ (round enc smp) (rounds enc smp k)).trans (by rw [ih, map_round]; rfl)

theorem map_step {C : Type} {nside : ℕ} (ρ m : ℕ) (enc : Vector C (2 ^ ρ + 1) → w Unit)
    (children : (Fin nside → Vector C (2 ^ ρ)) → w Unit) (smp : w C) :
    (step ρ m enc children smp).map ψ =
      step ρ m (fun x ↦ ψ (enc x)) (fun x ↦ ψ (children x)) (ψ smp) := by
  exact (map_append ψ _ _).trans (by
    rw [map_append, map_append, map_chal, map_rounds, map_msg, map_chals]; rfl)

theorem map_steps {C : Type} {nside : ℕ} (enc : Vector C (2 ^ 2 + 1) → w Unit)
    (children : (Fin nside → Vector C (2 ^ 2)) → w Unit) (smp : w C) (k m : ℕ) :
    (steps enc children smp k m).map ψ =
      steps (fun x ↦ ψ (enc x)) (fun x ↦ ψ (children x)) (ψ smp) k m := by
  induction k generalizing m with
  | zero => exact map_empty ψ
  | succ k ih =>
    exact (map_append ψ (step 2 m enc children smp) (steps enc children smp k (m + 2))).trans
      (by rw [ih, map_step]; rfl)

theorem map_odd {C : Type} {nside : ℕ} (enc : Vector C (2 ^ 1 + 1) → w Unit)
    (children : (Fin nside → Vector C (2 ^ 1)) → w Unit) (smp : w C) (r : ℕ) :
    (odd enc children smp r).map ψ =
      odd (fun x ↦ ψ (enc x)) (fun x ↦ ψ (children x)) (ψ smp) r := by
  cases r with
  | zero => exact map_empty ψ
  | succ r => exact map_step ψ 1 0 enc children smp

theorem map_gkr {C : Type} {nside : ℕ} (μ : ℕ)
    (enc₁ : Vector C (2 ^ 1 + 1) → w Unit) (children₁ : (Fin nside → Vector C (2 ^ 1)) → w Unit)
    (enc₂ : Vector C (2 ^ 2 + 1) → w Unit) (children₂ : (Fin nside → Vector C (2 ^ 2)) → w Unit)
    (smp : w C) :
    (gkr μ enc₁ children₁ enc₂ children₂ smp).map ψ =
      gkr μ (fun x ↦ ψ (enc₁ x)) (fun x ↦ ψ (children₁ x)) (fun x ↦ ψ (enc₂ x))
        (fun x ↦ ψ (children₂ x)) (ψ smp) := by
  exact (map_append ψ _ _).trans (by rw [map_append, map_odd, map_steps, map_chal]; rfl)

/-! ### The mapped wire, stated at the target wire

Each lemma concludes `c.map ψ = c'` for a wire `c'` of the same shape over the mapped parts, so
that `apply` unfolds a composite wire on either side. -/

section Of

theorem map_append_of {m n : ℕ} {p₁ : ProtocolSpec m} {p₂ : ProtocolSpec n}
    {c₁ : RoundCodec w p₁} {c₂ : RoundCodec w p₂} {c₁' : RoundCodec w' p₁}
    {c₂' : RoundCodec w' p₂} (h₁ : c₁.map ψ = c₁') (h₂ : c₂.map ψ = c₂') :
    (c₁.append c₂).map ψ = c₁'.append c₂' := by
  rw [map_append, h₁, h₂]

theorem map_empty_of : (empty : RoundCodec w !p[]).map ψ = empty := map_empty ψ

theorem map_msg_of {M : Type} {enc : M → w Unit} {enc' : M → w' Unit}
    (h : ∀ x, ψ (enc x) = enc' x) : (msg enc).map ψ = msg enc' := by
  rw [map_msg]; congr; funext x; exact h x

theorem map_sendOne_of {M : Type} {enc : M → w Unit} {enc' : M → w' Unit}
    (h : ∀ x, ψ (enc x) = enc' x) : (sendOne enc).map ψ = sendOne enc' := by
  rw [map_sendOne]; congr; funext x; exact h x

theorem map_chal_of {C : Type} {smp : w C} {smp' : w' C} (h : ψ smp = smp') :
    (chal smp).map ψ = chal smp' := by
  rw [map_chal, h]

theorem map_chals_of {C : Type} {smp : w C} {smp' : w' C} (h : ψ smp = smp') (k : ℕ) :
    (chals smp k).map ψ = chals smp' k := by
  rw [map_chals, h]

theorem map_rounds_of {C : Type} {d : ℕ} {enc : Vector C (d + 1) → w Unit}
    {enc' : Vector C (d + 1) → w' Unit} {smp : w C} {smp' : w' C}
    (h : ∀ x, ψ (enc x) = enc' x) (h' : ψ smp = smp') (k : ℕ) :
    (rounds enc smp k).map ψ = rounds enc' smp' k := by
  rw [map_rounds, h']; congr; funext x; exact h x

theorem map_odd_of {C : Type} {nside : ℕ} {enc : Vector C (2 ^ 1 + 1) → w Unit}
    {children : (Fin nside → Vector C (2 ^ 1)) → w Unit} {smp : w C}
    {enc' : Vector C (2 ^ 1 + 1) → w' Unit} {children' : (Fin nside → Vector C (2 ^ 1)) → w' Unit}
    {smp' : w' C} (h₁ : ∀ x, ψ (enc x) = enc' x) (h₂ : ∀ x, ψ (children x) = children' x)
    (h₃ : ψ smp = smp') (r : ℕ) :
    (odd enc children smp r).map ψ = odd enc' children' smp' r := by
  rw [map_odd, h₃]
  congr <;> funext x
  exacts [h₁ x, h₂ x]

theorem map_steps_of {C : Type} {nside : ℕ} {enc : Vector C (2 ^ 2 + 1) → w Unit}
    {children : (Fin nside → Vector C (2 ^ 2)) → w Unit} {smp : w C}
    {enc' : Vector C (2 ^ 2 + 1) → w' Unit} {children' : (Fin nside → Vector C (2 ^ 2)) → w' Unit}
    {smp' : w' C} (h₁ : ∀ x, ψ (enc x) = enc' x) (h₂ : ∀ x, ψ (children x) = children' x)
    (h₃ : ψ smp = smp') (k m : ℕ) :
    (steps enc children smp k m).map ψ = steps enc' children' smp' k m := by
  rw [map_steps, h₃]
  congr <;> funext x
  exacts [h₁ x, h₂ x]

theorem map_gkr_of {C : Type} {nside : ℕ} (μ : ℕ)
    {enc₁ : Vector C (2 ^ 1 + 1) → w Unit} {children₁ : (Fin nside → Vector C (2 ^ 1)) → w Unit}
    {enc₂ : Vector C (2 ^ 2 + 1) → w Unit} {children₂ : (Fin nside → Vector C (2 ^ 2)) → w Unit}
    {smp : w C} {enc₁' : Vector C (2 ^ 1 + 1) → w' Unit}
    {children₁' : (Fin nside → Vector C (2 ^ 1)) → w' Unit}
    {enc₂' : Vector C (2 ^ 2 + 1) → w' Unit}
    {children₂' : (Fin nside → Vector C (2 ^ 2)) → w' Unit} {smp' : w' C}
    (h₁ : ∀ x, ψ (enc₁ x) = enc₁' x) (h₂ : ∀ x, ψ (children₁ x) = children₁' x)
    (h₃ : ∀ x, ψ (enc₂ x) = enc₂' x) (h₄ : ∀ x, ψ (children₂ x) = children₂' x)
    (h₅ : ψ smp = smp') :
    (gkr μ enc₁ children₁ enc₂ children₂ smp).map ψ =
      gkr μ enc₁' children₁' enc₂' children₂' smp' := by
  rw [map_gkr, h₅]
  congr <;> funext x
  exacts [h₁ x, h₂ x, h₃ x, h₄ x]

end Of

end RoundCodec

/-! ## The run along a morphism -/

namespace Prover

variable {w w' : Type → Type} [Monad w] [Monad w'] [LawfulMonad w] [LawfulMonad w']
  (ψ : w →ᵐ w') {S W S' W' : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  (c : RoundCodec w pSpec) (P : Prover []ₒ S W S' W' pSpec)

theorem runNoOracle_hom {α : Type} (oa : OracleComp []ₒ α) :
    ψ (runNoOracle (w := w) oa) = runNoOracle oa := by
  rw [runNoOracle_eq_pure, runNoOracle_eq_pure (w := w'), MonadHom.mmap_pure]

theorem stepWith_hom (j : Fin n) (tr : pSpec.Transcript j.castSucc) (st : P.PrvState j.castSucc) :
    ψ (stepWith c P j tr st) = stepWith (c.map ψ) P j tr st := by
  unfold stepWith
  split
  · simp only [MonadHom.mmap_bind, MonadHom.mmap_pure, runNoOracle_hom, RoundCodec.map]
  · simp only [MonadHom.mmap_bind, MonadHom.mmap_pure, runNoOracle_hom, RoundCodec.map]

theorem runToRoundWith_hom (i : Fin (n + 1)) (stmt : S) (wit : W) :
    ψ (runToRoundWith c P i stmt wit) = runToRoundWith (c.map ψ) P i stmt wit := by
  induction i using Fin.induction with
  | zero => simp only [runToRoundWith, Fin.induction_zero, MonadHom.mmap_pure]
  | succ j ih =>
    rw [runToRoundWith_succ, runToRoundWith_succ, processRoundWith, processRoundWith,
      MonadHom.mmap_bind, ih]
    simp only [stepWith_hom]

/-- **The run along a monad morphism**: mapping a run against a wire is the run against the
mapped wire. -/
theorem runWith_hom (stmt : S) (wit : W) :
    ψ (runWith c P stmt wit) = runWith (c.map ψ) P stmt wit := by
  simp only [runWith, MonadHom.mmap_bind, MonadHom.mmap_pure, runToRoundWith_hom,
    runNoOracle_hom]

end Prover

end
end LeanerVM.Protocol
