module

public import LeanVM.Cost.Spec
public import LeanVM.Cost.Encoding

/-!
# The compiler's rules

One lemma per Lean construct the compiler translates: from runs of the parts (their code and
price are whatever the compiler found for them) to a run of the whole, its value the encoding of
the Lean expression. The compiler (`Cost/Compiler.lean`) applies them by unification on the Lean
expression, so the code and the price of the whole are what the rule's conclusion names.

* `machineCost`: the price of a function's run, when it has one (`machineCost_eq`: every run has
  that price), the time function of every compiled definition;
* the rules for variables, literals, `let`, constructors, fields, `match` on `Option`, `List`,
  `Bool` and pairs, `if`, and the primitives on `ℕ`, `UInt64`, `K` and `Bool`.
-/

namespace LeanVM.Cost

open LeanVM.Parameters

@[expose] public section

/-! ## The price of a run -/

/-- The price of function `f`'s run on `vs`, if it has one; `0` otherwise. -/
noncomputable def machineCost (P : MachineProgram) (f : ℕ) (vs : List MachineValue) : ℕ :=
  open Classical in
  if h : ∃ r : MachineValue × ℕ, ∃ n, evaluateFunctionBody P n f vs = some r then (Classical.choose h).2 else 0

theorem RunsBody.unique {P : MachineProgram} {f : ℕ} {vs : List MachineValue} {v v' : MachineValue} {c c' : ℕ}
    (h : RunsBody P f vs v c) (h' : RunsBody P f vs v' c') : v = v' ∧ c = c' := by
  obtain ⟨n, h⟩ := h
  obtain ⟨n', h'⟩ := h'
  have e := (evalBody_le (le_max_left n n') h).symm.trans (evalBody_le (le_max_right n n') h')
  simp only [Option.some.injEq, Prod.mk.injEq] at e
  exact e

/-- **Every run has the machine's price.** -/
theorem machineCost_eq {P : MachineProgram} {f : ℕ} {vs : List MachineValue} {v : MachineValue} {c : ℕ}
    (h : RunsBody P f vs v c) : machineCost P f vs = c := by
  have hex : ∃ r : MachineValue × ℕ, ∃ n, evaluateFunctionBody P n f vs = some r := ⟨(v, c), h⟩
  simp only [machineCost, hex, ↓reduceDIte]
  have hs := Classical.choose_spec hex
  exact (RunsBody.unique (v := (Classical.choose hex).1) (c := (Classical.choose hex).2) hs h).2

theorem RunsBody.withMachineCost {P : MachineProgram} {f : ℕ} {vs : List MachineValue} {v : MachineValue} {c : ℕ}
    (h : RunsBody P f vs v c) : RunsBody P f vs v (machineCost P f vs) := by
  rw [machineCost_eq h]; exact h

/-- **Specs by strong induction**: if each run's step uses the spec only at arguments of smaller
measure, the spec holds at every argument, at the machine's price. -/
theorem RunsBody.induction {P : MachineProgram} {i : ℕ} {α : Type} (args : α → List MachineValue) (val : α → MachineValue)
    (m : α → ℕ)
    (step : ∀ x, (∀ y, m y < m x → RunsBody P i (args y) (val y) (machineCost P i (args y))) →
      ∃ c, RunsBody P i (args x) (val x) c) :
    ∀ x, RunsBody P i (args x) (val x) (machineCost P i (args x)) := by
  intro x
  induction h : m x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    obtain ⟨c, hc⟩ := step x fun y hy ↦ ih (m y) (h ▸ hy) y rfl
    exact hc.withMachineCost

/-! ## Closures -/

/-- The price of applying the closure `v` to `vs`: its function's price on its values and `vs`. -/
noncomputable def appCost (P : MachineProgram) : MachineValue → List MachineValue → ℕ
  | .closure j us, vs => machineCost P j (us ++ vs)
  | _, _ => 0

/-- The closure `v` applied to `vs` returns `w`. -/
def RunsApp (P : MachineProgram) (v : MachineValue) (vs : List MachineValue) (w : MachineValue) : Prop :=
  ∃ j us, v = .closure j us ∧ RunsBody P j (us ++ vs) w (machineCost P j (us ++ vs))

theorem RunsApp.of_spec {P : MachineProgram} {j : ℕ} {us vs : List MachineValue} {w : MachineValue}
    (h : RunsBody P j (us ++ vs) w (machineCost P j (us ++ vs))) : RunsApp P (.closure j us) vs w :=
  ⟨j, us, rfl, h⟩

/-! ## Encodings -/

section MachineEncoding

variable {α β : Type} [MachineEncoding α] [MachineEncoding β]

@[simp] theorem enc_none : encodeValue (none : Option α) = .ctor 0 [] := rfl
@[simp] theorem enc_some (a : α) : encodeValue (some a) = .ctor 1 [encodeValue a] := rfl
@[simp] theorem enc_nil : encodeValue ([] : List α) = .ctor 0 [] := rfl
@[simp] theorem enc_cons (a : α) (l : List α) : encodeValue (a :: l) = .ctor 1 [encodeValue a, encodeValue l] := rfl
@[simp] theorem enc_pair (a : α) (b : β) : encodeValue (a, b) = .ctor 0 [encodeValue a, encodeValue b] := rfl
@[simp] theorem enc_true : encodeValue true = .ctor 1 [] := rfl
@[simp] theorem enc_false : encodeValue false = .ctor 0 [] := rfl
@[simp] theorem enc_nat (n : ℕ) : encodeValue n = .nat n := rfl
@[simp] theorem enc_word (x : UInt64) : encodeValue x = .word x := rfl
@[simp] theorem enc_k (x : K) : encodeValue x = .word x.lane := rfl
@[simp] theorem enc_array (a : Array α) : encodeValue a = .arr (a.map encodeValue) := rfl

theorem enc_bool (b : Bool) : encodeValue b = MachineValue.ofBool b := rfl

end MachineEncoding

/-! ## Rules -/

namespace Rule

variable {P : MachineProgram} {env : List MachineValue} {α β γ : Type} [MachineEncoding α] [MachineEncoding β] [MachineEncoding γ]

theorem var {i : ℕ} {x : α} (h : env[i]? = some (encodeValue x)) : Runs P env (.var i) (encodeValue x) 1 :=
  Runs.var h

theorem natLit (n : ℕ) : Runs P env (.val (.nat n)) (encodeValue n) 1 := Runs.val _

theorem wordLit (x : UInt64) : Runs P env (.val (.word x)) (encodeValue x) 1 := Runs.val _

theorem kLit (x : K) : Runs P env (.val (.word x.lane)) (encodeValue x) 1 := Runs.val _

theorem boolLit (b : Bool) : Runs P env (.val (MachineValue.ofBool b)) (encodeValue b) 1 := Runs.val _

theorem letIn {t b : Term} {v : α} {f : α → β} {c : ℕ} {d : α → ℕ} (h : Runs P env t (encodeValue v) c)
    (hb : ∀ x, x = v → Runs P (encodeValue x :: env) b (encodeValue (f x)) (d x)) :
    Runs P env (.letIn t b) (encodeValue (f v)) (c + d v + 1) :=
  Runs.letIn h (hb v rfl)

/-- `let`, the body run with the value itself in front of the environment. -/
theorem letV {t b : Term} {v : α} {w : β} {c d : ℕ} (h : Runs P env t (encodeValue v) c)
    (hb : Runs P (encodeValue v :: env) b (encodeValue w) d) : Runs P env (.letIn t b) (encodeValue w) (c + d + 1) :=
  Runs.letIn h hb

/-! ### Constructors and fields -/

theorem none : Runs P env (.ctor 0 []) (encodeValue (none : Option α)) 1 :=
  (Runs.ctor (k := 0) RunsList.nil).cost_eq (by simp)

theorem some {t : Term} {a : α} {c : ℕ} (h : Runs P env t (encodeValue a) c) :
    Runs P env (.ctor 1 [t]) (encodeValue (some a)) (c + 2) :=
  (Runs.ctor (k := 1) (RunsList.cons h RunsList.nil)).cost_eq (by simp)

theorem nil : Runs P env (.ctor 0 []) (encodeValue ([] : List α)) 1 :=
  (Runs.ctor (k := 0) RunsList.nil).cost_eq (by simp)

theorem cons {t u : Term} {a : α} {l : List α} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hl : Runs P env u (encodeValue l) d) : Runs P env (.ctor 1 [t, u]) (encodeValue (a :: l)) (c + d + 3) :=
  (Runs.ctor (k := 1) (RunsList.cons h (RunsList.cons hl RunsList.nil))).cost_eq (by simp)

theorem pair {t u : Term} {a : α} {b : β} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) : Runs P env (.ctor 0 [t, u]) (encodeValue (a, b)) (c + d + 3) :=
  (Runs.ctor (k := 0) (RunsList.cons h (RunsList.cons hb RunsList.nil))).cost_eq (by simp)

theorem fst {t : Term} {p : α × β} {c : ℕ} (h : Runs P env t (encodeValue p) c) :
    Runs P env (.field 0 t) (encodeValue p.1) (c + 1) :=
  Runs.field (k := 0) (fs := [encodeValue p.1, encodeValue p.2]) h rfl

theorem snd {t : Term} {p : α × β} {c : ℕ} (h : Runs P env t (encodeValue p) c) :
    Runs P env (.field 1 t) (encodeValue p.2) (c + 1) :=
  Runs.field (k := 0) (fs := [encodeValue p.1, encodeValue p.2]) h rfl

/-! ### Matches -/

theorem caseOption {t a b : Term} {o : Option α} {e₀ : β} {e₁ : α → β} {c c₀ : ℕ} {c₁ : α → ℕ}
    (h : Runs P env t (encodeValue o) c) (h₀ : o = .none → Runs P env a (encodeValue e₀) c₀)
    (h₁ : ∀ x, o = .some x → Runs P (encodeValue x :: env) b (encodeValue (e₁ x)) (c₁ x)) :
    Runs P env (.case t [a, b]) (encodeValue (Option.casesOn (motive := fun _ ↦ β) o e₀ e₁))
      (c + Option.casesOn (motive := fun _ ↦ ℕ) o c₀ c₁ + 1) := by
  cases o with
  | none => exact Runs.case (k := 0) (fs := []) h rfl (h₀ rfl)
  | some x => exact Runs.case (k := 1) (fs := [encodeValue x]) h rfl (h₁ x rfl)

theorem caseList {t a b : Term} {l : List α} {e₀ : β} {e₁ : α → List α → β} {c c₀ : ℕ}
    {c₁ : α → List α → ℕ} (h : Runs P env t (encodeValue l) c) (h₀ : l = [] → Runs P env a (encodeValue e₀) c₀)
    (h₁ : ∀ x xs, l = x :: xs → Runs P (encodeValue x :: encodeValue xs :: env) b (encodeValue (e₁ x xs)) (c₁ x xs)) :
    Runs P env (.case t [a, b]) (encodeValue (List.casesOn (motive := fun _ ↦ β) l e₀ e₁))
      (c + List.casesOn (motive := fun _ ↦ ℕ) l c₀ c₁ + 1) := by
  cases l with
  | nil => exact Runs.case (k := 0) (fs := []) h rfl (h₀ rfl)
  | cons x xs => exact Runs.case (k := 1) (fs := [encodeValue x, encodeValue xs]) h rfl (h₁ x xs rfl)

theorem casePair {t b : Term} {p : α × β} {e : α → β → γ} {c : ℕ} {c₁ : α → β → ℕ}
    (h : Runs P env t (encodeValue p) c)
    (h₁ : ∀ x y, p = (x, y) → Runs P (encodeValue x :: encodeValue y :: env) b (encodeValue (e x y)) (c₁ x y)) :
    Runs P env (.case t [b]) (encodeValue (Prod.casesOn (motive := fun _ ↦ γ) p e))
      (c + Prod.casesOn (motive := fun _ ↦ ℕ) p c₁ + 1) := by
  obtain ⟨x, y⟩ := p
  exact Runs.case (k := 0) (fs := [encodeValue x, encodeValue y]) h rfl (h₁ x y rfl)

theorem ite {tc ta tb : Term} {p : Prop} [Decidable p] {a b : α} {c ca cb : ℕ}
    (h : Runs P env tc (encodeValue (decide p)) c) (ha : p → Runs P env ta (encodeValue a) ca)
    (hb : ¬p → Runs P env tb (encodeValue b) cb) :
    Runs P env (.case tc [tb, ta]) (encodeValue (if p then a else b)) (c + (if p then ca else cb) + 1) := by
  by_cases hp : p
  · exact Runs.case (k := 1) (fs := []) (by simpa [hp] using h) rfl (by simpa [hp] using ha hp)
  · exact Runs.case (k := 0) (fs := []) (by simpa [hp] using h) rfl (by simpa [hp] using hb hp)

theorem dite {tc ta tb : Term} {p : Prop} [Decidable p] {a : p → α} {b : ¬p → α} {c : ℕ}
    {ca : p → ℕ} {cb : ¬p → ℕ}
    (h : Runs P env tc (encodeValue (decide p)) c) (ha : ∀ hp : p, Runs P env ta (encodeValue (a hp)) (ca hp))
    (hb : ∀ hp : ¬p, Runs P env tb (encodeValue (b hp)) (cb hp)) :
    Runs P env (.case tc [tb, ta]) (encodeValue (if hp : p then a hp else b hp))
      (c + (if hp : p then ca hp else cb hp) + 1) := by
  by_cases hp : p
  · exact Runs.case (k := 1) (fs := []) (by simpa [hp] using h) rfl (by simpa [hp] using ha hp)
  · exact Runs.case (k := 0) (fs := []) (by simpa [hp] using h) rfl (by simpa [hp] using hb hp)

theorem cond {tc ta tb : Term} {b : Bool} {x y : α} {c ca cb : ℕ}
    (h : Runs P env tc (encodeValue b) c) (ha : b = true → Runs P env ta (encodeValue x) ca)
    (hb : b = false → Runs P env tb (encodeValue y) cb) :
    Runs P env (.case tc [tb, ta]) (encodeValue (bif b then x else y))
      (c + (bif b then ca else cb) + 1) := by
  cases b
  · exact Runs.case (k := 0) (fs := []) h rfl (by simpa using hb rfl)
  · exact Runs.case (k := 1) (fs := []) h rfl (by simpa using ha rfl)

theorem caseNat {t a b : Term} {n : ℕ} {e₀ : α} {e₁ : ℕ → α} {c c₀ : ℕ} {c₁ : ℕ → ℕ}
    (h : Runs P env t (encodeValue n) c) (h₀ : n = 0 → Runs P env a (encodeValue e₀) c₀)
    (h₁ : ∀ k, n = k + 1 → Runs P (encodeValue k :: env) b (encodeValue (e₁ k)) (c₁ k)) :
    Runs P env (.case (.op .naturalEqual [t, .val (.nat 0)]) [.letIn (.op .naturalSubtract [t, .val (.nat 1)]) b, a])
      (encodeValue (Nat.casesOn (motive := fun _ ↦ α) n e₀ e₁))
      (c + 1 + (max (limbCount n) (limbCount 0) + 1) +
        Nat.casesOn (motive := fun _ ↦ ℕ) n c₀ (fun k ↦ c + 1 + (max (limbCount n) (limbCount 1) + 1) +
          c₁ k + 1) + 1) := by
  have hz : Runs P env (.op .naturalEqual [t, .val (.nat 0)]) (encodeValue (decide (n = 0)))
      (c + 1 + (max (limbCount n) (limbCount 0) + 1)) :=
    Runs.op (RunsList.cons h (RunsList.cons (Runs.val _) RunsList.nil))
      (by simp [PrimitiveOperation.apply, enc_bool, MachineValue.ofBool])
  cases n with
  | zero => exact Runs.case (k := 1) (fs := []) (by simpa using hz) rfl (h₀ rfl)
  | succ k =>
    have hs : Runs P env (.op .naturalSubtract [t, .val (.nat 1)]) (encodeValue k)
        (c + 1 + (max (limbCount (k + 1)) (limbCount 1) + 1)) :=
      Runs.op (RunsList.cons h (RunsList.cons (Runs.val _) RunsList.nil)) (by simp [PrimitiveOperation.apply, naturalOperation])
    exact Runs.case (k := 0) (fs := []) (by simpa using hz) rfl (Runs.letIn hs (h₁ k rfl))

/-- A closure of function `j` with the values of `ts`. -/
theorem closure {j : ℕ} {ts : List Term} {vs : List MachineValue} {c : ℕ} (h : RunsList P env ts vs c) :
    Runs P env (.closure j ts) (.closure j vs) (c + vs.length + 1) := Runs.closure h

/-- A closure applied to the values of `ts`. -/
theorem applyClosure {t : Term} {ts : List Term} {f : MachineValue} {vs : List MachineValue} {w : MachineValue} {c d : ℕ}
    (h : Runs P env t f c) (hl : RunsList P env ts vs d) (ha : RunsApp P f vs w) :
    Runs P env (.applyClosure t ts) w (c + d + appCost P f vs + 1) := by
  obtain ⟨j, us, rfl, hb⟩ := ha
  exact Runs.applyClosure h hl hb

/-- A raw value of the environment. -/
theorem rawVar {i : ℕ} {v : MachineValue} (h : env[i]? = .some v) : Runs P env (.var i) v 1 := Runs.var h

/-- A call of a function on the encodings of its arguments. -/
theorem call {f : ℕ} {ts : List Term} {vs : List MachineValue} {w : MachineValue} {c d : ℕ}
    (h : RunsList P env ts vs c) (hb : RunsBody P f vs w d) :
    Runs P env (.call f ts) w (c + d + 1) := Runs.call h hb

/-- `a || b`, short-circuit. -/
theorem boolOr {t u : Term} {a b : Bool} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : a = false → Runs P env u (encodeValue b) d) :
    Runs P env (.case t [u, .ctor 1 []]) (encodeValue (a || b)) (c + (if a then 1 else d) + 1) := by
  cases a
  · exact Runs.case (k := 0) (fs := []) h rfl (by simpa using hb rfl)
  · exact Runs.case (k := 1) (fs := []) h rfl (by simpa using (Runs.ctor (k := 1) (P := P) (env := env) RunsList.nil))

/-- `a && b`, short-circuit. -/
theorem boolAnd {t u : Term} {a b : Bool} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : a = true → Runs P env u (encodeValue b) d) :
    Runs P env (.case t [.ctor 0 [], u]) (encodeValue (a && b)) (c + (if a then d else 1) + 1) := by
  cases a
  · exact Runs.case (k := 0) (fs := []) h rfl (by simpa using (Runs.ctor (k := 0) (P := P) (env := env) RunsList.nil))
  · exact Runs.case (k := 1) (fs := []) h rfl (by simpa using hb rfl)

theorem boolNot {t : Term} {a : Bool} {c : ℕ} (h : Runs P env t (encodeValue a) c) :
    Runs P env (.case t [.ctor 1 [], .ctor 0 []]) (encodeValue (!a)) (c + 1 + 1) := by
  cases a
  · exact Runs.case (k := 0) (fs := []) h rfl (by simpa using (Runs.ctor (k := 1) (P := P) (env := env) RunsList.nil))
  · exact Runs.case (k := 1) (fs := []) h rfl (by simpa using (Runs.ctor (k := 0) (P := P) (env := env) RunsList.nil))

/-! ### Primitives -/

/-- A primitive of two arguments, from the runs of its arguments. -/
theorem op₂ {o : PrimitiveOperation} {t u : Term} {a : α} {b : β} {v : MachineValue} {c d e : ℕ}
    (h : Runs P env t (encodeValue a) c) (hb : Runs P env u (encodeValue b) d)
    (ho : o.apply [encodeValue a, encodeValue b] = .some (v, e)) : Runs P env (.op o [t, u]) v (c + d + e) :=
  (Runs.op (RunsList.cons h (RunsList.cons hb RunsList.nil)) ho).cost_eq (by omega)

/-- A primitive of one argument. -/
theorem op₁ {o : PrimitiveOperation} {t : Term} {a : α} {v : MachineValue} {c e : ℕ} (h : Runs P env t (encodeValue a) c)
    (ho : o.apply [encodeValue a] = .some (v, e)) : Runs P env (.op o [t]) v (c + e) :=
  (Runs.op (RunsList.cons h RunsList.nil) ho).cost_eq (by omega)

theorem natAdd {t u : Term} {a b : ℕ} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) :
    Runs P env (.op .naturalAdd [t, u]) (encodeValue (a + b)) (c + d + (max (limbCount a) (limbCount b) + 1)) :=
  op₂ h hb rfl

theorem natSub {t u : Term} {a b : ℕ} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) :
    Runs P env (.op .naturalSubtract [t, u]) (encodeValue (a - b)) (c + d + (max (limbCount a) (limbCount b) + 1)) :=
  op₂ h hb rfl

theorem natMul {t u : Term} {a b : ℕ} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) :
    Runs P env (.op .naturalMultiply [t, u]) (encodeValue (a * b)) (c + d + (limbCount a * limbCount b + 1)) :=
  op₂ h hb rfl

theorem natDiv {t u : Term} {a b : ℕ} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) :
    Runs P env (.op .naturalDivide [t, u]) (encodeValue (a / b)) (c + d + (limbCount a * limbCount b + 1)) :=
  op₂ h hb rfl

theorem natMod {t u : Term} {a b : ℕ} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) :
    Runs P env (.op .naturalModulo [t, u]) (encodeValue (a % b)) (c + d + (limbCount a * limbCount b + 1)) :=
  op₂ h hb rfl

theorem natLt {t u : Term} {a b : ℕ} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) :
    Runs P env (.op .naturalLessThan [t, u]) (encodeValue (decide (a < b))) (c + d + (max (limbCount a) (limbCount b) + 1)) :=
  op₂ h hb rfl

theorem natLe {t u : Term} {a b : ℕ} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) :
    Runs P env (.op .naturalLessOrEqual [t, u]) (encodeValue (decide (a ≤ b))) (c + d + (max (limbCount a) (limbCount b) + 1)) :=
  op₂ h hb rfl

theorem natEq {t u : Term} {a b : ℕ} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) :
    Runs P env (.op .naturalEqual [t, u]) (encodeValue (decide (a = b))) (c + d + (max (limbCount a) (limbCount b) + 1)) :=
  op₂ h hb (by simp [PrimitiveOperation.apply, enc_bool, MachineValue.ofBool])

theorem wordLt {t u : Term} {a b : UInt64} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) :
    Runs P env (.op .wordLessThan [t, u]) (encodeValue (decide (a < b))) (c + d + 1) := op₂ h hb rfl

theorem wordLe {t u : Term} {a b : UInt64} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) :
    Runs P env (.op .wordLessOrEqual [t, u]) (encodeValue (decide (a ≤ b))) (c + d + 1) := op₂ h hb rfl

theorem wordEq {t u : Term} {a b : UInt64} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) :
    Runs P env (.op .wordEqual [t, u]) (encodeValue (decide (a = b))) (c + d + 1) :=
  op₂ h hb (by simp [PrimitiveOperation.apply, wordOperation, enc_bool, MachineValue.ofBool])

/-- `decide (b = true)` is `b`. -/
theorem decideEqTrue {t : Term} {b : Bool} {c : ℕ} (h : Runs P env t (encodeValue b) c) :
    Runs P env t (encodeValue (decide (b = true))) c := by
  cases b <;> exact h

theorem uint8Eq {t u : Term} {a b : UInt8} {inst : Decidable (a = b)} {c d : ℕ}
    (h : Runs P env t (encodeValue a) c) (hb : Runs P env u (encodeValue b) d) :
    Runs P env (.op .wordEqual [t, u]) (encodeValue (@decide (a = b) inst)) (c + d + 1) :=
  op₂ h hb (by
    have : (a.toUInt64 == b.toUInt64) = @decide (a = b) inst := by
      by_cases hab : a = b
      · simp [hab]
      · have : a.toUInt64 ≠ b.toUInt64 := fun e ↦ hab (UInt8.toUInt64_inj.1 e)
        simp [hab, this]
    show PrimitiveOperation.apply .wordEqual [.word a.toUInt64, .word b.toUInt64] = _
    simp [PrimitiveOperation.apply, wordOperation, enc_bool, this])

theorem natBEq {t u : Term} {a b : ℕ} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) :
    Runs P env (.op .naturalEqual [t, u]) (encodeValue (a == b)) (c + d + (max (limbCount a) (limbCount b) + 1)) :=
  op₂ h hb (by simp [PrimitiveOperation.apply, enc_bool, MachineValue.ofBool])

theorem wordBEq {t u : Term} {a b : UInt64} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) : Runs P env (.op .wordEqual [t, u]) (encodeValue (a == b)) (c + d + 1) :=
  op₂ h hb (by simp [PrimitiveOperation.apply, wordOperation, enc_bool])

theorem kEq {t u : Term} {a b : K} {inst : Decidable (a = b)} {c d : ℕ}
    (h : Runs P env t (encodeValue a) c) (hb : Runs P env u (encodeValue b) d) :
    Runs P env (.op .wordEqual [t, u]) (encodeValue (@decide (a = b) inst)) (c + d + 1) :=
  op₂ h hb (by
    have : (a.lane == b.lane) = @decide (a = b) inst := by
      by_cases hab : a = b
      · simp [hab]
      · have : a.lane ≠ b.lane := fun e ↦ hab (by
          rw [← show K.ofLane a.lane = a from rfl, ← show K.ofLane b.lane = b from rfl, e])
        simp [hab, this]
    simp [PrimitiveOperation.apply, wordOperation, enc_bool, this])

theorem kBEq {t u : Term} {a b : K} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) : Runs P env (.op .wordEqual [t, u]) (encodeValue (a == b)) (c + d + 1) :=
  op₂ h hb (by
    have : (a.lane == b.lane) = (a == b) := by
      obtain ⟨x⟩ := a
      obtain ⟨y⟩ := b
      by_cases hxy : x = y
      · subst hxy; simp [K.lane]
      · have h1 : (⟨x⟩ : UInt64) ≠ ⟨y⟩ := fun e ↦ hxy (by cases e; rfl)
        have h2 : ((⟨x⟩ : K) == ⟨y⟩) = false := by
          show (x == y) = false
          simp [hxy]
        simp [K.lane, h1, h2]
    simp [PrimitiveOperation.apply, wordOperation, enc_bool, this])

/-! ### Words -/

theorem wXor {t u : Term} {a b : UInt64} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) : Runs P env (.op .wordXor [t, u]) (encodeValue (a ^^^ b)) (c + d + 1) :=
  op₂ h hb rfl
theorem wAnd {t u : Term} {a b : UInt64} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) : Runs P env (.op .wordAnd [t, u]) (encodeValue (a &&& b)) (c + d + 1) :=
  op₂ h hb rfl
theorem wOr {t u : Term} {a b : UInt64} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) : Runs P env (.op .wordOr [t, u]) (encodeValue (a ||| b)) (c + d + 1) :=
  op₂ h hb rfl
theorem wNot {t : Term} {a : UInt64} {c : ℕ} (h : Runs P env t (encodeValue a) c) :
    Runs P env (.op .wordNot [t]) (encodeValue (~~~a)) (c + 1) := op₁ h rfl
theorem wShl {t u : Term} {a b : UInt64} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) : Runs P env (.op .wordShiftLeft [t, u]) (encodeValue (a <<< b)) (c + d + 1) :=
  op₂ h hb rfl
theorem wShr {t u : Term} {a b : UInt64} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) : Runs P env (.op .wordShiftRight [t, u]) (encodeValue (a >>> b)) (c + d + 1) :=
  op₂ h hb rfl
theorem wAdd {t u : Term} {a b : UInt64} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) : Runs P env (.op .wordAdd [t, u]) (encodeValue (a + b)) (c + d + 1) :=
  op₂ h hb rfl
theorem wSub {t u : Term} {a b : UInt64} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) : Runs P env (.op .wordSubtract [t, u]) (encodeValue (a - b)) (c + d + 1) :=
  op₂ h hb rfl
theorem wMul {t u : Term} {a b : UInt64} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) : Runs P env (.op .wordMultiply [t, u]) (encodeValue (a * b)) (c + d + 1) :=
  op₂ h hb rfl
theorem wToNat {t : Term} {a : UInt64} {c : ℕ} (h : Runs P env t (encodeValue a) c) :
    Runs P env (.op .wordToNatural [t]) (encodeValue a.toNat) (c + 1) := op₁ h rfl
theorem natToUInt64 {t : Term} {n : ℕ} {c : ℕ} (h : Runs P env t (encodeValue n) c) :
    Runs P env (.op .wordOfNatural [t]) (encodeValue n.toUInt64) (c + 1) := op₁ h (by simp [PrimitiveOperation.apply])

/-- `K.lane`: the same word. -/
theorem kLane {t : Term} {a : K} {c : ℕ} (h : Runs P env t (encodeValue a) c) :
    Runs P env t (encodeValue a.lane) c := h

theorem u8Xor {t u : Term} {a b : UInt8} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) : Runs P env (.op .wordXor [t, u]) (encodeValue (a ^^^ b)) (c + d + 1) :=
  op₂ h hb (by
    show PrimitiveOperation.apply .wordXor [.word a.toUInt64, .word b.toUInt64] = _
    simp [PrimitiveOperation.apply, wordOperation]; rfl)
theorem u8And {t u : Term} {a b : UInt8} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) : Runs P env (.op .wordAnd [t, u]) (encodeValue (a &&& b)) (c + d + 1) :=
  op₂ h hb (by
    show PrimitiveOperation.apply .wordAnd [.word a.toUInt64, .word b.toUInt64] = _
    simp [PrimitiveOperation.apply, wordOperation]; rfl)
theorem u8Or {t u : Term} {a b : UInt8} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) : Runs P env (.op .wordOr [t, u]) (encodeValue (a ||| b)) (c + d + 1) :=
  op₂ h hb (by
    show PrimitiveOperation.apply .wordOr [.word a.toUInt64, .word b.toUInt64] = _
    simp [PrimitiveOperation.apply, wordOperation]; rfl)
/-- A byte as a word: the same word. -/
theorem u8ToUInt64 {t : Term} {a : UInt8} {c : ℕ} (h : Runs P env t (encodeValue a) c) :
    Runs P env t (encodeValue a.toUInt64) c := h
theorem u64ToUInt8 {t : Term} {a : UInt64} {c : ℕ} (h : Runs P env t (encodeValue a) c) :
    Runs P env (.op .wordAnd [t, .val (.word 255)]) (encodeValue a.toUInt8) (c + 1 + 1) :=
  (Runs.op (RunsList.cons h (RunsList.cons (Runs.val _) RunsList.nil)) (v := encodeValue a.toUInt8) (d := 1)
    (by
      show PrimitiveOperation.apply .wordAnd [.word a, .word 255] = .some (.word a.toUInt8.toUInt64, 1)
      simp only [PrimitiveOperation.apply, wordOperation, Option.some.injEq, Prod.mk.injEq, MachineValue.word.injEq, and_true]
      apply UInt64.toNat_inj.1
      rw [UInt64.toNat_and, UInt8.toNat_toUInt64, UInt64.toNat_toUInt8,
        show (255 : UInt64).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod])).cost_eq
        (by omega)

theorem natAnd {t u : Term} {a b : ℕ} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) :
    Runs P env (.op .naturalAnd [t, u]) (encodeValue (a &&& b)) (c + d + (max (limbCount a) (limbCount b) + 1)) :=
  op₂ h hb rfl
theorem natShiftRight {t u : Term} {a k : ℕ} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue k) d) :
    Runs P env (.op .naturalShiftRight [t, u]) (encodeValue (a >>> k)) (c + d + (limbCount a + limbCount k + 1)) :=
  op₂ h hb rfl

/-- `decide (p ∧ q)`, short-circuit. -/
theorem decideAnd {t u : Term} {p q : Prop} [Decidable p] [Decidable q] {inst : Decidable (p ∧ q)}
    {c d : ℕ} (h : Runs P env t (encodeValue (decide p)) c) (hq : p → Runs P env u (encodeValue (decide q)) d) :
    Runs P env (.case t [.ctor 0 [], u]) (encodeValue (@decide (p ∧ q) inst))
      (c + (if p then d else 1) + 1) := by
  by_cases hp : p
  · have := Runs.case (k := 1) (fs := []) (alts := [.ctor 0 [], u]) (by simpa [hp] using h) rfl (hq hp)
    simpa [hp] using this
  · have := Runs.case (k := 0) (fs := []) (alts := [.ctor 0 [], u]) (by simpa [hp] using h) rfl
      (Runs.ctor (k := 0) (P := P) (env := env) RunsList.nil)
    simpa [hp, enc_bool, MachineValue.ofBool] using this

/-- `decide (p ∨ q)`, short-circuit. -/
theorem decideOr {t u : Term} {p q : Prop} [Decidable p] [Decidable q] {inst : Decidable (p ∨ q)}
    {c d : ℕ} (h : Runs P env t (encodeValue (decide p)) c) (hq : ¬p → Runs P env u (encodeValue (decide q)) d) :
    Runs P env (.case t [u, .ctor 1 []]) (encodeValue (@decide (p ∨ q) inst))
      (c + (if p then 1 else d) + 1) := by
  by_cases hp : p
  · have := Runs.case (k := 1) (fs := []) (alts := [u, .ctor 1 []]) (by simpa [hp] using h) rfl
      (Runs.ctor (k := 1) (P := P) (env := env) RunsList.nil)
    simpa [hp, enc_bool, MachineValue.ofBool] using this
  · have := Runs.case (k := 0) (fs := []) (alts := [u, .ctor 1 []]) (by simpa [hp] using h) rfl (hq hp)
    simpa [hp] using this

/-- `decide ¬p`. -/
theorem decideNot {t : Term} {p : Prop} [Decidable p] {inst : Decidable ¬p} {c : ℕ}
    (h : Runs P env t (encodeValue (decide p)) c) :
    Runs P env (.case t [.ctor 1 [], .ctor 0 []]) (encodeValue (@decide (¬p) inst)) (c + 1 + 1) := by
  by_cases hp : p
  · have := Runs.case (k := 1) (fs := []) (alts := [.ctor 1 [], .ctor 0 []]) (by simpa [hp] using h) rfl
      (Runs.ctor (k := 0) (P := P) (env := env) RunsList.nil)
    simpa [hp, enc_bool, MachineValue.ofBool] using this
  · have := Runs.case (k := 0) (fs := []) (alts := [.ctor 1 [], .ctor 0 []]) (by simpa [hp] using h) rfl
      (Runs.ctor (k := 1) (P := P) (env := env) RunsList.nil)
    simpa [hp, enc_bool, MachineValue.ofBool] using this

/-! ### Arrays -/

theorem arrSize {t : Term} {a : Array α} {c : ℕ} (h : Runs P env t (encodeValue a) c) :
    Runs P env (.op .arraySize [t]) (encodeValue a.size) (c + 1) := op₁ h (by simp [PrimitiveOperation.apply])

theorem arrAppend {t u : Term} {a b : Array α} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) :
    Runs P env (.op .arrayAppend [t, u]) (encodeValue (a ++ b)) (c + d + (a.size + b.size + 1)) :=
  op₂ h hb (by simp [PrimitiveOperation.apply])

theorem arrReplicate {t u : Term} {n : ℕ} {x : α} {c d : ℕ} (h : Runs P env t (encodeValue n) c)
    (hb : Runs P env u (encodeValue x) d) :
    Runs P env (.op .arrayReplicate [t, u]) (encodeValue (Array.replicate n x)) (c + d + (n + 1)) :=
  op₂ h hb (by simp [PrimitiveOperation.apply])

theorem arrToList {t : Term} {a : Array α} {c : ℕ} (h : Runs P env t (encodeValue a) c) :
    Runs P env (.op .arrayToList [t]) (encodeValue a.toList) (c + (3 * a.size + 1)) :=
  op₁ h (by simp [PrimitiveOperation.apply]; rfl)

theorem valToList_ofList (l : List MachineValue) : MachineValue.toList? (.ofList l) = .some l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [MachineValue.ofList, MachineValue.toList?, ih]

theorem listToArray {t : Term} {l : List α} {c : ℕ} (h : Runs P env t (encodeValue l) c) :
    Runs P env (.op .arrayOfList [t]) (encodeValue l.toArray) (c + (l.length + 1)) :=
  op₁ h (by
    show PrimitiveOperation.apply .arrayOfList [.ofList (l.map encodeValue)] = _
    simp [PrimitiveOperation.apply, valToList_ofList])

theorem arrGetD {t u w : Term} {a : Array α} {i : ℕ} {x : α} {c d e : ℕ}
    (h : Runs P env t (encodeValue a) c) (hi : Runs P env u (encodeValue i) d) (hx : Runs P env w (encodeValue x) e) :
    Runs P env (.op .arrayGet [t, u, w]) (encodeValue (a.getD i x)) (c + d + e + 1) :=
  (Runs.op (RunsList.cons h (RunsList.cons hi (RunsList.cons hx RunsList.nil)))
    (v := encodeValue (a.getD i x)) (d := 1) (by
      simp only [enc_array, enc_nat, PrimitiveOperation.apply, Option.some.injEq, Prod.mk.injEq, and_true]
      simp [Array.getD_eq_getD_getElem?])).cost_eq (by omega)

theorem arrGetElem? {t u : Term} {a : Array α} {i : ℕ} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hi : Runs P env u (encodeValue i) d) :
    Runs P env (.case (.op .naturalLessThan [u, .op .arraySize [t]]) [.ctor 0 [], .ctor 1 [.op .arrayGet [t, u, .val (.ctor 0 [])]]])
      (encodeValue a[i]?) (d + (c + 1) + (max (limbCount i) (limbCount a.size) + 1) +
        (if i < a.size then c + d + 1 + 1 + 2 else 1) + 1) := by
  have hlt := natLt hi (arrSize h)
  by_cases hia : i < a.size
  · have hg : Runs P env (.op .arrayGet [t, u, .val (.ctor 0 [])]) (encodeValue a[i]) (c + d + 1 + 1) :=
      (Runs.op (RunsList.cons h (RunsList.cons hi (RunsList.cons (Runs.val _) RunsList.nil)))
        (v := encodeValue a[i]) (d := 1) (by simp [PrimitiveOperation.apply, hia])).cost_eq (by omega)
    have := Runs.case (k := 1) (fs := []) (alts := [.ctor 0 [], .ctor 1 [.op .arrayGet [t, u, .val (.ctor 0 [])]]])
      (by simpa [hia] using hlt) rfl (some hg)
    simpa [hia, Array.getElem?_eq_getElem hia] using this
  · have := Runs.case (k := 0) (fs := []) (alts := [.ctor 0 [], .ctor 1 [.op .arrayGet [t, u, .val (.ctor 0 [])]]])
      (by simpa [hia] using hlt) rfl (none (P := P) (env := env) (α := α))
    simpa [hia, Array.getElem?_eq_none (Nat.le_of_not_lt hia)] using this

/-- A subtype's value: the same value. -/
theorem subtypeVal {t : Term} {p : α → Prop} {x : Subtype p} {c : ℕ} (h : Runs P env t (encodeValue x) c) :
    Runs P env t (encodeValue x.val) c := h

/-- A subtype's element: the same value. -/
theorem subtypeMk {t : Term} {p : α → Prop} {x : α} {hx : p x} {c : ℕ} (h : Runs P env t (encodeValue x) c) :
    Runs P env t (encodeValue (⟨x, hx⟩ : Subtype p)) c := h

/-- `a[i]'h`: an entry in bounds. -/
theorem arrGetElem {t u : Term} {a : Array α} {i : ℕ} {h : i < a.size} {c d : ℕ}
    (ha : Runs P env t (encodeValue a) c) (hi : Runs P env u (encodeValue i) d) :
    Runs P env (.op .arrayGet [t, u, .val (.ctor 0 [])]) (encodeValue (a[i]'h)) (c + d + 1 + 1) :=
  (Runs.op (RunsList.cons ha (RunsList.cons hi (RunsList.cons (Runs.val _) RunsList.nil)))
    (v := encodeValue (a[i]'h)) (d := 1) (by simp [PrimitiveOperation.apply, h])).cost_eq (by omega)

/-- A function of a finite domain at `i`: entry `i` of its array. -/
theorem finFunApp {t u : Term} {n : ℕ} {f : Fin n → α} {i : Fin n} {c d : ℕ}
    (h : Runs P env t (encodeValue f) c) (hi : Runs P env u (encodeValue i) d) :
    Runs P env (.op .arrayGet [t, u, .val (.ctor 0 [])]) (encodeValue (f i)) (c + d + 1 + 1) :=
  (Runs.op (RunsList.cons h (RunsList.cons hi (RunsList.cons (Runs.val _) RunsList.nil)))
    (v := encodeValue (f i)) (d := 1) (by
      show PrimitiveOperation.apply .arrayGet [.arr (Array.ofFn fun j ↦ encodeValue (f j)), .nat i.val, _] = _
      simp [PrimitiveOperation.apply])).cost_eq (by omega)

/-- A function of a finite domain as data: the array of its values. -/
theorem finFunOfArray {t : Term} {n : ℕ} {f : Fin n → α} {c : ℕ}
    (h : Runs P env t (encodeValue (Array.ofFn f)) c) : Runs P env t (encodeValue f) c := by
  have : encodeValue (Array.ofFn f) = encodeValue f := by
    show MachineValue.arr ((Array.ofFn f).map encodeValue) = MachineValue.arr (Array.ofFn fun i ↦ encodeValue (f i))
    rw [Array.map_ofFn]; rfl
  exact this ▸ h

/-- A vector's `get`: its array. -/
theorem vecGet {t : Term} {n : ℕ} {v : Vector α n} {c : ℕ} (h : Runs P env t (encodeValue v) c) :
    Runs P env t (encodeValue v.get) c := by
  have : encodeValue v.get = encodeValue v := by
    show MachineValue.arr (Array.ofFn fun i ↦ encodeValue (v.get i)) = MachineValue.arr (v.toArray.map encodeValue)
    congr 1
    apply Array.ext
    · simp
    · intro i h1 h2; simp [Vector.get]
  rw [this]; exact h

/-- A vector's array: the same value. -/
theorem vecToArray {t : Term} {n : ℕ} {v : Vector α n} {c : ℕ} (h : Runs P env t (encodeValue v) c) :
    Runs P env t (encodeValue v.toArray) c := h

/-- `v[i]'h` of a vector: an entry in bounds. -/
theorem vecGetElem {t u : Term} {n : ℕ} {v : Vector α n} {i : ℕ} {h : i < n} {c d : ℕ}
    (hv : Runs P env t (encodeValue v) c) (hi : Runs P env u (encodeValue i) d) :
    Runs P env (.op .arrayGet [t, u, .val (.ctor 0 [])]) (encodeValue (v[i]'h)) (c + d + 1 + 1) :=
  (Runs.op (RunsList.cons hv (RunsList.cons hi (RunsList.cons (Runs.val _) RunsList.nil)))
    (v := encodeValue (v[i]'h)) (d := 1) (by
      show PrimitiveOperation.apply .arrayGet [.arr (v.toArray.map encodeValue), .nat i, _] = _
      simp [PrimitiveOperation.apply, h])).cost_eq (by omega)

theorem u8Lit (x : UInt8) : Runs P env (.val (.word x.toUInt64)) (encodeValue x) 1 := Runs.val _

theorem u8Lt {t u : Term} {a b : UInt8} {inst : Decidable (a < b)} {c d : ℕ}
    (h : Runs P env t (encodeValue a) c) (hb : Runs P env u (encodeValue b) d) :
    Runs P env (.op .wordLessThan [t, u]) (encodeValue (@decide (a < b) inst)) (c + d + 1) :=
  op₂ h hb (by
    have : decide (a.toUInt64 < b.toUInt64) = @decide (a < b) inst := by
      by_cases hab : a < b
      · simp [hab, UInt8.toUInt64_lt.2 hab]
      · simp [hab, show ¬ a.toUInt64 < b.toUInt64 from fun e ↦ hab (UInt8.toUInt64_lt.1 e)]
    show PrimitiveOperation.apply .wordLessThan [.word a.toUInt64, .word b.toUInt64] = _
    simp only [PrimitiveOperation.apply, wordOperation, enc_bool]
    rw [this])

/-- Limb `i` of a word of `E`: field `i`. -/
theorem eLimb0 {t : Term} {x : E} {c : ℕ} (h : Runs P env t (encodeValue x) c) :
    Runs P env (.field 0 t) (encodeValue (x.limb 0)) (c + 1) :=
  Runs.field (k := 0) (fs := [encodeValue (x.limb 0), encodeValue (x.limb 1), encodeValue (x.limb 2)]) h rfl
theorem eLimb1 {t : Term} {x : E} {c : ℕ} (h : Runs P env t (encodeValue x) c) :
    Runs P env (.field 1 t) (encodeValue (x.limb 1)) (c + 1) :=
  Runs.field (k := 0) (fs := [encodeValue (x.limb 0), encodeValue (x.limb 1), encodeValue (x.limb 2)]) h rfl
theorem eLimb2 {t : Term} {x : E} {c : ℕ} (h : Runs P env t (encodeValue x) c) :
    Runs P env (.field 2 t) (encodeValue (x.limb 2)) (c + 1) :=
  Runs.field (k := 0) (fs := [encodeValue (x.limb 0), encodeValue (x.limb 1), encodeValue (x.limb 2)]) h rfl

/-- A word of `E` from its limbs. -/
theorem eOfLimbs {ta tb tc : Term} {a b c : K} {ca cb cc : ℕ} (ha : Runs P env ta (encodeValue a) ca)
    (hb : Runs P env tb (encodeValue b) cb) (hc : Runs P env tc (encodeValue c) cc) :
    Runs P env (.ctor 0 [ta, tb, tc]) (encodeValue (E.ofLimbs a b c)) (ca + cb + cc + 4) :=
  (Runs.ctor (k := 0) (RunsList.cons ha (RunsList.cons hb (RunsList.cons hc RunsList.nil)))).cost_eq
    (by simp; omega)

/-- `K.ofLane`: the same word. -/
theorem kOfLane {t : Term} {w : UInt64} {c : ℕ} (h : Runs P env t (encodeValue w) c) :
    Runs P env t (encodeValue (K.ofLane w)) c := h

theorem uint8ToNat {t : Term} {x : UInt8} {c : ℕ} (h : Runs P env t (encodeValue x) c) :
    Runs P env (.op .wordToNatural [t]) (encodeValue x.toNat) (c + 1) := op₁ h (by simp [PrimitiveOperation.apply]; rfl)

theorem uint64OfNat {t : Term} {n : ℕ} {c : ℕ} (h : Runs P env t (encodeValue n) c) :
    Runs P env (.op .wordOfNatural [t]) (encodeValue (UInt64.ofNat n)) (c + 1) := op₁ h (by simp [PrimitiveOperation.apply])

theorem natShiftLeft {t u : Term} {a k : ℕ} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue k) d) :
    Runs P env (.op .naturalShiftLeft [t, u]) (encodeValue (a <<< k)) (c + d + (limbCount (a <<< k) + limbCount k + 1)) :=
  op₂ h hb rfl

theorem vecToList {t : Term} {n : ℕ} {v : Vector α n} {c : ℕ} (h : Runs P env t (encodeValue v) c) :
    Runs P env (.op .arrayToList [t]) (encodeValue v.toList) (c + (3 * v.toArray.size + 1)) :=
  op₁ h (by
    show PrimitiveOperation.apply .arrayToList [.arr (v.toArray.map encodeValue)] = _
    simp [PrimitiveOperation.apply, Vector.toList]
    rfl)

/-- A vector of an array: the same value. -/
theorem vecMk {t : Term} {n : ℕ} {a : Array α} {ha : a.size = n} {c : ℕ}
    (h : Runs P env t (encodeValue a) c) : Runs P env t (encodeValue (Vector.mk a ha)) c := h

theorem arrPush {t u : Term} {a : Array α} {x : α} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hx : Runs P env u (encodeValue x) d) :
    Runs P env (.op .arrayPush [t, u]) (encodeValue (a.push x)) (c + d + (a.size + 2)) :=
  op₂ h hx (by simp [PrimitiveOperation.apply])

theorem arrayMk {t : Term} {l : List α} {c : ℕ} (h : Runs P env t (encodeValue l) c) :
    Runs P env (.op .arrayOfList [t]) (encodeValue (Array.mk l)) (c + (l.length + 1)) := listToArray h

theorem arrSetIfInBounds {t u w : Term} {a : Array α} {i : ℕ} {x : α} {c d e : ℕ}
    (h : Runs P env t (encodeValue a) c) (hi : Runs P env u (encodeValue i) d) (hx : Runs P env w (encodeValue x) e) :
    Runs P env (.op .arraySet [t, u, w]) (encodeValue (a.setIfInBounds i x)) (c + d + e + (a.size + 1)) :=
  (Runs.op (RunsList.cons h (RunsList.cons hi (RunsList.cons hx RunsList.nil)))
    (v := encodeValue (a.setIfInBounds i x)) (d := a.size + 1) (by
      simp [PrimitiveOperation.apply, Array.map_setIfInBounds])).cost_eq (by omega)

theorem arrExtract {t u w : Term} {a : Array α} {i j : ℕ} {c d e : ℕ}
    (h : Runs P env t (encodeValue a) c) (hi : Runs P env u (encodeValue i) d) (hj : Runs P env w (encodeValue j) e) :
    Runs P env (.op .arrayExtract [t, u, w]) (encodeValue (a.extract i j))
      (c + d + e + ((a.extract i j).size + 1)) :=
  (Runs.op (RunsList.cons h (RunsList.cons hi (RunsList.cons hj RunsList.nil)))
    (v := encodeValue (a.extract i j)) (d := (a.extract i j).size + 1) (by
      simp [PrimitiveOperation.apply])).cost_eq (by omega)

/-- `Fin.val`: the same number. -/
theorem finVal {t : Term} {n : ℕ} {i : Fin n} {c : ℕ} (h : Runs P env t (encodeValue i) c) :
    Runs P env t (encodeValue i.val) c := h

/-- `Fin.mk`: the same number. -/
theorem finMk {t : Term} {n i : ℕ} {hi : i < n} {c : ℕ} (h : Runs P env t (encodeValue i) c) :
    Runs P env t (encodeValue (⟨i, hi⟩ : Fin n)) c := h

theorem kSub {t u : Term} {a b : K} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) : Runs P env (.op .wordXor [t, u]) (encodeValue (a - b)) (c + d + 1) :=
  op₂ h hb rfl

theorem kAdd {t u : Term} {a b : K} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) : Runs P env (.op .wordXor [t, u]) (encodeValue (a + b)) (c + d + 1) :=
  op₂ h hb rfl

theorem kMul {t u : Term} {a b : K} {c d : ℕ} (h : Runs P env t (encodeValue a) c)
    (hb : Runs P env u (encodeValue b) d) : Runs P env (.op .binaryFieldMultiply [t, u]) (encodeValue (a * b)) (c + d + 256) :=
  op₂ h hb rfl

end Rule

/-! ## Rewrites: library functions compiled through equal forms -/

namespace Rewrite

theorem arrayZipWith {α β γ : Type} (f : α → β → γ) (a : Array α) (b : Array β) :
    Array.zipWith f a b = (List.zipWith f a.toList b.toList).toArray := by
  apply Array.ext'
  simp [Array.toList_zipWith]

theorem natTwoPow (k : ℕ) : 2 ^ k = 1 <<< k := by simp [Nat.shiftLeft_eq]

/-- Equality of lists, decided by their elements' equality. -/
theorem decideEqList {α : Type} [DecidableEq α] (l₁ l₂ : List α) {inst : Decidable (l₁ = l₂)} :
    @decide (l₁ = l₂) inst = @List.beq α instBEqOfDecidableEq l₁ l₂ := by
  rw [show @List.beq α instBEqOfDecidableEq l₁ l₂ = (l₁ == l₂) from rfl]
  by_cases h : l₁ = l₂ <;> simp [h]

/-- A cast along an equation with a constant motive (a literal pattern's `h ▸`): the value. -/
theorem eqNdrecConst {α β : Sort _} {a b : α} (x : β) (h : a = b) :
    @Eq.ndrec α a (fun _ ↦ β) x b h = x := by
  subst h; rfl

/-- The last element: the head of the reversal (`List.getLast` carries a proof). -/
theorem listGetLastD {α : Type} (l : List α) (d : α) : l.getLastD d = l.reverse.headD d := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_head?_reverse, List.headD_eq_head?_getD]

theorem uint64Default : (default : UInt64) = 0 := rfl

theorem uint8Default : (default : UInt8) = 0 := rfl

/-- `K.ofBits`: the word of the number modulo `2^64`. -/
theorem kOfBits (n : ℕ) : K.ofBits n = K.ofLane n.toUInt64 := rfl

/-- Addition in `E`, limb by limb. -/
theorem eAdd (x y : E) : x + y =
    E.ofLimbs (x.limb 0 + y.limb 0) (x.limb 1 + y.limb 1) (x.limb 2 + y.limb 2) := by
  rw [← ofLimbs_limb x, ← ofLimbs_limb y, add_limbs]; simp

/-- Multiplication in `E`: nine products of limbs, `y^3 = y + 1`. -/
theorem eMul (x y : E) : x * y =
    let x0 := x.limb 0; let x1 := x.limb 1; let x2 := x.limb 2
    let y0 := y.limb 0; let y1 := y.limb 1; let y2 := y.limb 2
    let c3 := x1 * y2 + x2 * y1; let c4 := x2 * y2
    E.ofLimbs (x0 * y0 + c3) (x0 * y1 + x1 * y0 + c3 + c4) (x0 * y2 + x1 * y1 + x2 * y0 + c4) := by
  conv_lhs => rw [← ofLimbs_limb x, ← ofLimbs_limb y, mul_limbs]
  simp only []
  congr 1 <;> ring

theorem eZero : (0 : E) = E.ofLimbs 0 0 0 := by
  apply E.ext; intro i; fin_cases i <;> simp [limb_zero]

theorem eOfK (a : K) : ofK a = E.ofLimbs a 0 0 := ofK_eq_ofLimbs a

/-- Equality in `E`: of the limbs. -/
theorem decideEqE (x y : E) {inst : Decidable (x = y)} :
    @decide (x = y) inst = decide (x.limb 0 = y.limb 0 ∧ x.limb 1 = y.limb 1 ∧ x.limb 2 = y.limb 2) := by
  have : x = y ↔ (x.limb 0 = y.limb 0 ∧ x.limb 1 = y.limb 1 ∧ x.limb 2 = y.limb 2) := by
    constructor
    · rintro rfl; simp
    · rintro ⟨h0, h1, h2⟩; apply E.ext; intro i; fin_cases i <;> assumption
  simp only [this]

/-- The values `f i, …, f (n - 1)`. -/
def ofFnFrom {α : Type} {n : ℕ} (f : Fin n → α) (i : ℕ) : List α :=
  if h : i < n then f ⟨i, h⟩ :: ofFnFrom f (i + 1) else []
termination_by n - i

theorem ofFnFrom_eq {α : Type} {n : ℕ} (f : Fin n → α) :
    ∀ k i, n - i = k → ofFnFrom f i = (List.ofFn f).drop i := by
  intro k
  induction k with
  | zero =>
    intro i hi
    rw [ofFnFrom, dite_eq_right_iff.2 (fun h ↦ absurd h (by omega))]
    simp [show n ≤ i by omega]
  | succ k ih =>
    intro i hi
    have hin : i < n := by omega
    rw [ofFnFrom]
    simp only [hin, ↓reduceDIte]
    rw [ih (i + 1) (by omega)]
    have hl : i < (List.ofFn f).length := by simp; omega
    rw [List.drop_eq_getElem_cons hl]
    simp

/-- The indices `i, …, n - 1` of `Fin n` (`List.finRange`'s, without a type parameter: its
element type depends on `n`). -/
def finRangeFrom (n i : ℕ) : List (Fin n) :=
  if h : i < n then ⟨i, h⟩ :: finRangeFrom n (i + 1) else []
termination_by n - i

theorem finRangeFrom_eq (n : ℕ) : ∀ i, finRangeFrom n i = ofFnFrom (fun j : Fin n ↦ j) i := by
  intro i
  induction h : n - i generalizing i with
  | zero =>
    rw [finRangeFrom, ofFnFrom]
    simp [show ¬ i < n by omega]
  | succ k ih =>
    rw [finRangeFrom, ofFnFrom]
    simp only [show i < n by omega, ↓reduceDIte, ih (i + 1) (by omega)]

theorem listFinRange (n : ℕ) : List.finRange n = finRangeFrom n 0 := by
  rw [finRangeFrom_eq, ofFnFrom_eq _ n 0 (by omega), List.drop_zero, List.finRange]

/-- `Array.ofFn` through a list. -/
theorem arrOfFn {α : Type} {n : ℕ} (f : Fin n → α) : Array.ofFn f = (ofFnFrom f 0).toArray := by
  apply Array.ext'
  rw [Array.toList_ofFn, List.toList_toArray, ofFnFrom_eq f n 0 (by omega), List.drop_zero]

/-- `Nat.log2` by halving. -/
def log2Rec (n : ℕ) : ℕ := if 2 ≤ n then log2Rec (n / 2) + 1 else 0
termination_by n
decreasing_by omega

theorem natLog2 (n : ℕ) : Nat.log2 n = log2Rec n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [Nat.log2_def, log2Rec]
    split
    · rw [ih (n / 2) (by omega)]
    · rfl

/-- The product `f 0 * … * f (n - 1)`, from the left. -/
def prodRange {M : Type} [CommMonoid M] (f : ℕ → M) : ℕ → M
  | 0 => 1
  | n + 1 => prodRange f n * f n

/-- A product over `range n`: `prodRange`. -/
theorem finsetProdRange {M : Type} [CommMonoid M] (n : ℕ) (f : ℕ → M) :
    ∏ v ∈ Finset.range n, f v = prodRange f n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Finset.prod_range_succ, ih, prodRange]

theorem listOfFn {α : Type} {n : ℕ} (f : Fin n → α) : List.ofFn f = ofFnFrom f 0 := by
  rw [ofFnFrom_eq f n 0 (by omega), List.drop_zero]

theorem vecOfFn {α : Type} {n : ℕ} (f : Fin n → α) : Vector.ofFn f = ⟨Array.ofFn f, by simp⟩ := rfl

theorem arrMap {α β : Type} (f : α → β) (a : Array α) : a.map f = (a.toList.map f).toArray := by
  apply Array.ext'; simp

theorem arrFoldl {α β : Type} (f : β → α → β) (b : β) (a : Array α) :
    a.foldl f b = a.toList.foldl f b := by simp [Array.foldl_toList]

theorem arrFoldr {α β : Type} (f : α → β → β) (b : β) (a : Array α) :
    a.foldr f b = a.toList.foldr f b := by simp [Array.foldr_toList]

theorem arrFilter {α : Type} (p : α → Bool) (a : Array α) :
    a.filter p = (a.toList.filter p).toArray := by
  apply Array.ext'; simp

theorem arrIsEqv {α : Type} [BEq α] (a b : Array α) (r : α → α → Bool) :
    a.isEqv b r = a.toList.isEqv b.toList r := (Array.isEqv_toList a b).symm

theorem arrBEq {α : Type} [BEq α] (a b : Array α) : (a == b) = (a.toList == b.toList) :=
  (Array.beq_toList a b).symm

theorem arrAny {α : Type} (p : α → Bool) (a : Array α) : a.any p = a.toList.any p := by simp

theorem arrAll {α : Type} (p : α → Bool) (a : Array α) : a.all p = a.toList.all p := by simp

theorem arrZipIdx {α : Type} (a : Array α) (k : ℕ) : a.zipIdx k = (a.toList.zipIdx k).toArray := by
  apply Array.ext'; simp

theorem arrMapIdx {α β : Type} (f : ℕ → α → β) (a : Array α) :
    a.mapIdx f = ((a.toList.zipIdx).map fun p ↦ f p.2 p.1).toArray := by
  apply Array.ext'; simp [List.mapIdx_eq_zipIdx_map]

theorem listMapIdx {α β : Type} (f : ℕ → α → β) (l : List α) :
    l.mapIdx f = (l.zipIdx).map fun p ↦ f p.2 p.1 := List.mapIdx_eq_zipIdx_map

/-- `a ^ n` by squaring. -/
def powSq {M : Type} [Monoid M] (a : M) (n : ℕ) : M :=
  if n = 0 then 1 else
    let r := powSq (a * a) (n / 2)
    if n % 2 = 1 then a * r else r
termination_by n
decreasing_by omega

theorem powSq_eq {M : Type} [Monoid M] : ∀ (n : ℕ) (a : M), powSq a n = a ^ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a
    rw [powSq]
    by_cases h : n = 0
    · simp [h]
    · simp only [h, ↓reduceIte]
      rw [ih (n / 2) (by omega), ← pow_two, ← pow_mul]
      conv_rhs => rw [← Nat.mod_add_div n 2]
      rcases Nat.mod_two_eq_zero_or_one n with h2 | h2 <;> simp [h2, pow_succ', pow_add]

theorem pow_eq_powSq {M : Type} [Monoid M] (a : M) (n : ℕ) : a ^ n = powSq a n :=
  (powSq_eq n a).symm

theorem natSucc (n : ℕ) : Nat.succ n = n + 1 := rfl

/-- A limb of `E` at a variable index: from the list of the three. -/
theorem eLimbVar (x : E) (i : Fin 3) : x.limb i = [x.limb 0, x.limb 1, x.limb 2].getD i.val 0 := by
  fin_cases i <;> rfl

/-- An `if` of functions, applied: each branch applied. -/
theorem iteApp {α β : Type} (c : Prop) [Decidable c] (f g : α → β) (x : α) :
    (if c then f else g) x = if c then f x else g x := by
  split <;> rfl

theorem diteApp {α β : Type} (c : Prop) [Decidable c] (f : c → α → β) (g : ¬c → α → β) (x : α) :
    (if h : c then f h else g h) x = if h : c then f h x else g h x := by
  split <;> rfl

/-- Equality of a subtype's elements: of their values. -/
theorem decideEqSubtype {α : Type} {p : α → Prop} [DecidableEq α] (a b : Subtype p)
    {inst : Decidable (a = b)} : @decide (a = b) inst = decide (a.val = b.val) := by
  simp only [Subtype.ext_iff]

/-- A statement for every `i : Fin n`, decided by `Array.all` over the indices. -/
theorem decideForallFin {n : ℕ} (p : Fin n → Prop) [DecidablePred p] {inst : Decidable (∀ i, p i)} :
    @decide (∀ i, p i) inst = (Array.ofFn (n := n) id).all fun i ↦ decide (p i) := by
  rw [Bool.eq_iff_iff, Array.all_iff_forall]
  simp only [Array.size_ofFn, Array.getElem_ofFn, id, decide_eq_true_eq]
  exact ⟨fun h i hi _ ↦ h _, fun h i ↦ h i.val i.isLt ⟨Nat.zero_le _, i.isLt⟩⟩

/-- Equality in `Fin n`: of the values. -/
theorem decideEqFin {n : ℕ} (a b : Fin n) {inst : Decidable (a = b)} :
    @decide (a = b) inst = decide (a.val = b.val) :=
  decide_eq_decide.2 Fin.val_inj.symm

/-- A statement for every member of a list, decided by `List.all`. -/
theorem decideBAll {α : Type} (l : List α) (p : α → Prop) [DecidablePred p]
    {inst : Decidable (∀ x ∈ l, p x)} : @decide (∀ x ∈ l, p x) inst = l.all fun x ↦ decide (p x) := by
  rw [Bool.eq_iff_iff]; simp [List.all_eq_true]

/-- Membership in a list, decided by `List.elem`. -/
theorem decideMemList {α : Type} [BEq α] [LawfulBEq α] (a : α) (l : List α)
    {inst : Decidable (a ∈ l)} : @decide (a ∈ l) inst = l.elem a := by
  rw [Bool.eq_iff_iff]; simp

/-- Equality of arrays, decided by their lists. -/
theorem decideEqArray {α : Type} [DecidableEq α] (a b : Array α) {inst : Decidable (a = b)} :
    @decide (a = b) inst = @List.beq α instBEqOfDecidableEq a.toList b.toList := by
  rw [show @List.beq α instBEqOfDecidableEq a.toList b.toList = (a.toList == b.toList) from rfl]
  by_cases h : a = b
  · subst h; simp
  · simp [h]

end Rewrite

end

end LeanVM.Cost
