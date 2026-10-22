/-
  LeanVM.E2E.Vis.PerKey.Defs

  W-vis, P7: the per-key events of T5's hybrid over the honest keys, the class of inputs a
  reduction answers itself, the key coincidences it aborts on, and moving one key's generation to
  the front in the schemes' lazy random oracle.
-/

module

public import LeanVM.E2E.Vis.ShapeFacts
public import LeanVM.E2E.Reduction.Commute

/-!
# T5 per key: definitions (W-vis, P7)

T5 bounds a forgery against some honest key by a sum over the keys (`prEvent_or_exists_le_sum`).
For key `j`, a reduction plays the scheme's single-key game: the challenger holds key `j`, the
reduction generates every other key itself and answers their hash inputs from a private lazy
oracle. Those inputs are a static class given key `j`'s parameter `pj` (`PrivJ pj`): address-
shaped, not shaped as a derivation, and not prefixed by `pj`. The challenger never queries it (its
inputs are `pj`-prefixed or derivations, `Vis/WalkXmss.lean`, `Vis/WalkSphincs.lean`), so one
private lazy oracle on `PrivJ pj` and the challenger's on the rest are one random oracle
(`Vis/PerKey/Partition.lean`). The reduction aborts when a key's parameter is another's or zero
(`KeyColl`); otherwise every other key's input after its parameter derivation is in `PrivJ pj`,
and the reduction forwards only the adversary's and V_I's queries and the other keys' two
derivations.

* `ForgedXAt j`, `ForgedSAt j`: a forgery against leanXMSS key `j`, leanSPHINCS key `j`;
  `Forged` is their disjunction over the keys (`forged_iff_exists`).
* `XWinAt j z tr`, `SWinAt j z tr`: V_I accepts and a forged claim of key `j` has a signature
  valid under the trace `tr`, what the reduction outputs.
* `AdvXmssAt j`, `AdvSphincsAt j`: the adversary's signing requests to key `j`.
* `romRun_sequenceFin_front`: in the lazy random oracle, a sequence of computations is its `j`-th
  computation first, then the rest (a port of lean_xmss's lemma to the lean_vm module system).
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom
open OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

/-! ## The class a reduction answers itself -/

/-- **The private class of reduction `j`**: address-shaped, not shaped as a derivation, and not
prefixed by key `j`'s parameter `pj`. -/
def PrivJ (pj : Bytes) (x : Bytes) : Prop := AddrShaped x ∧ ¬ DerivShape x ∧ ¬ pj <+: x

instance (pj x : Bytes) : Decidable (PrivJ pj x) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

variable {nx ns : ℕ}

/-! ## The adversary's requests to one key -/

/-- The adversary's leanXMSS signing requests to key `j`. -/
def AdvXmssAt (j : Fin nx) : (AdvSpec nx ns).Domain → Prop
  | .inl (.inr q) => q.1 = j
  | _ => False

/-- The adversary's leanSPHINCS signing requests to key `j`. -/
def AdvSphincsAt (j : Fin ns) : (AdvSpec nx ns).Domain → Prop
  | .inr q => q.1 = j
  | _ => False

instance (j : Fin nx) : DecidablePred (AdvXmssAt (ns := ns) j)
  | .inl (.inr q) => inferInstanceAs (Decidable (q.1 = j))
  | .inl (.inl _) => isFalse id
  | .inr _ => isFalse id

instance (j : Fin ns) : DecidablePred (AdvSphincsAt (nx := nx) j)
  | .inr q => inferInstanceAs (Decidable (q.1 = j))
  | .inl _ => isFalse id

variable [Sphincs.Params]

/-! ## Per-key forgeries and wins -/

/-- **A forgery against leanXMSS key `j`**: a claim of the root statement for key `j` on a message
no request to key `j` was answered for. -/
def ForgedXAt (j : Fin nx) (z : GameOutcome nx ns) : Prop :=
  ∃ msg, ((z.keys.xmss j).1, msg) ∈ z.statement.claims.xmss ∧
    ∀ e ∈ z.state.xlog j, e.1.2 = msg → e.2 = none

/-- **A forgery against leanSPHINCS key `j`.** -/
def ForgedSAt (j : Fin ns) (z : GameOutcome nx ns) : Prop :=
  ∃ msg, ((z.keys.sphincs j).1, msg) ∈ z.statement.claims.sphincs ∧
    ∀ e ∈ z.state.slog j, e.1 = msg → e.2 = none

/-- A forgery is one against some key. -/
theorem forged_iff_exists (z : GameOutcome nx ns) :
    Forged z ↔ (∃ j, ForgedXAt j z) ∨ ∃ j, ForgedSAt j z := Iff.rfl

/-- **Reduction `j`'s win (leanXMSS)**: V_I accepts, and a forged claim of key `j` has a signature
valid under the trace `tr`. -/
def XWinAt (j : Fin nx) (z : GameOutcome nx ns) (tr : Log) : Prop :=
  z.accepted = true ∧ ∃ msg σ, ((z.keys.xmss j).1, msg) ∈ z.statement.claims.xmss ∧
    (∀ e ∈ z.state.xlog j, e.1.2 = msg → e.2 = none) ∧
    xmssVerifyWith (look tr) (z.keys.xmss j).1 msg σ = some true

/-- **Reduction `j`'s win (leanSPHINCS).** -/
def SWinAt (j : Fin ns) (z : GameOutcome nx ns) (tr : Log) : Prop :=
  z.accepted = true ∧ ∃ msg σ, ((z.keys.sphincs j).1, msg) ∈ z.statement.claims.sphincs ∧
    (∀ e ∈ z.state.slog j, e.1 = msg → e.2 = none) ∧
    sphincsVerifyWith (look tr) (z.keys.sphincs j).1 msg σ = some true

/-! ## Key coincidences -/

/-- **A key coincidence**: two honest keys share a parameter, or one is zero. -/
def KeyColl (keys : Keys nx ns) : Prop :=
  ¬ (keyParams keys).Nodup ∨ List.replicate 16 0 ∈ keyParams keys

/-- **A coincidence at key `idx`** (the leanXMSS keys first, then the leanSPHINCS keys): another
key shares its parameter, or some parameter is zero. Reduction `idx` routes by class exactly
when there is none. -/
def KeyCollAt (keys : Keys nx ns) (idx : Fin (nx + ns)) : Prop :=
  (∃ i : Fin (nx + ns), i ≠ idx ∧ (keyParams keys)[i]? = (keyParams keys)[idx]?) ∨
    List.replicate 16 0 ∈ keyParams keys

/-! ## The hybrid's union bound -/

omit [Sphincs.Params] in
/-- **The union bound over the keys.** -/
theorem prEvent_or_exists_le_sum {α : Type} (mx : ProbComp α) (P : Fin nx → α → Prop)
    (R : Fin ns → α → Prop) :
    Pr{let x ← mx}[(∃ j, P j x) ∨ ∃ j, R j x] ≤
      ∑ j, Pr{let x ← mx}[P j x] + ∑ j, Pr{let x ← mx}[R j x] :=
  (prEvent_or_le _ _ _).trans (add_le_add (prEvent_exists_le _ _) (prEvent_exists_le _ _))

end

/-! ## One key first -/

@[expose] public section

/-- **One computation of a sequence first**: in the schemes' lazy random oracle, running the
`j`-th computation first and the sequence with its result in place is running the sequence. -/
theorem romRun_sequenceFin_front {α γ : Type} :
    ∀ (n : ℕ) (f : Fin n → OracleComp OW α) (j : Fin n)
      (k : α → (Fin n → α) → OracleComp OW γ) (c : QueryCache LeanXmss.HashSpec),
      romRun (f j >>= fun a ↦
          LeanXmss.Concrete.sequenceFin (fun i : Fin n ↦ if i = j then pure a else f i) >>= k a) c =ᵈ
        romRun (LeanXmss.Concrete.sequenceFin f >>= fun keys ↦ k (keys j) keys) c
  | 0, _, j, _, _ => j.elim0
  | n + 1, f, j, k, c => by
      cases j using Fin.cases with
      | zero =>
          simp only [LeanXmss.Concrete.sequenceFin, Fin.succ_ne_zero, ↓reduceIte, bind_assoc,
            pure_bind, Fin.cases_zero]
          exact .rfl
      | succ j =>
          simp only [LeanXmss.Concrete.sequenceFin, bind_assoc, pure_bind,
            show ((0 : Fin (n + 1)) = j.succ) = False from
              propext ⟨fun h ↦ Fin.succ_ne_zero j h.symm, False.elim⟩, ↓reduceIte, Fin.succ_inj,
            Fin.cases_succ]
          refine (romRun_bind_comm (f j.succ) (f 0) _ c).trans ?_
          rw [romRun_bind, romRun_bind]
          exact EvalDistEq.bind_right _ fun r ↦
            romRun_sequenceFin_front n (fun i ↦ f i.succ) j
              (fun a t ↦ k a (Fin.cases r.1 t)) r.2

end

end LeanVM.E2E
