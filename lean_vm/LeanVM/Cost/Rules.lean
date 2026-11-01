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
noncomputable def machineCost (P : Program) (f : ℕ) (vs : List Val) : ℕ :=
  open Classical in
  if h : ∃ r : Val × ℕ, ∃ n, evalBody P n f vs = some r then (Classical.choose h).2 else 0

theorem RunsBody.unique {P : Program} {f : ℕ} {vs : List Val} {v v' : Val} {c c' : ℕ}
    (h : RunsBody P f vs v c) (h' : RunsBody P f vs v' c') : v = v' ∧ c = c' := by
  obtain ⟨n, h⟩ := h
  obtain ⟨n', h'⟩ := h'
  have e := (evalBody_le (le_max_left n n') h).symm.trans (evalBody_le (le_max_right n n') h')
  simp only [Option.some.injEq, Prod.mk.injEq] at e
  exact e

/-- **Every run has the machine's price.** -/
theorem machineCost_eq {P : Program} {f : ℕ} {vs : List Val} {v : Val} {c : ℕ}
    (h : RunsBody P f vs v c) : machineCost P f vs = c := by
  have hex : ∃ r : Val × ℕ, ∃ n, evalBody P n f vs = some r := ⟨(v, c), h⟩
  simp only [machineCost, hex, ↓reduceDIte]
  have hs := Classical.choose_spec hex
  exact (RunsBody.unique (v := (Classical.choose hex).1) (c := (Classical.choose hex).2) hs h).2

theorem RunsBody.withMachineCost {P : Program} {f : ℕ} {vs : List Val} {v : Val} {c : ℕ}
    (h : RunsBody P f vs v c) : RunsBody P f vs v (machineCost P f vs) := by
  rw [machineCost_eq h]; exact h

/-- **Specs by strong induction**: if each run's step uses the spec only at arguments of smaller
measure, the spec holds at every argument, at the machine's price. -/
theorem RunsBody.induction {P : Program} {i : ℕ} {α : Type} (args : α → List Val) (val : α → Val)
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
noncomputable def appCost (P : Program) : Val → List Val → ℕ
  | .fn j us, vs => machineCost P j (us ++ vs)
  | _, _ => 0

/-- The closure `v` applied to `vs` returns `w`. -/
def RunsApp (P : Program) (v : Val) (vs : List Val) (w : Val) : Prop :=
  ∃ j us, v = .fn j us ∧ RunsBody P j (us ++ vs) w (machineCost P j (us ++ vs))

theorem RunsApp.of_spec {P : Program} {j : ℕ} {us vs : List Val} {w : Val}
    (h : RunsBody P j (us ++ vs) w (machineCost P j (us ++ vs))) : RunsApp P (.fn j us) vs w :=
  ⟨j, us, rfl, h⟩

/-! ## Encodings -/

section Enc

variable {α β : Type} [Enc α] [Enc β]

@[simp] theorem enc_none : enc (none : Option α) = .ctor 0 [] := rfl
@[simp] theorem enc_some (a : α) : enc (some a) = .ctor 1 [enc a] := rfl
@[simp] theorem enc_nil : enc ([] : List α) = .ctor 0 [] := rfl
@[simp] theorem enc_cons (a : α) (l : List α) : enc (a :: l) = .ctor 1 [enc a, enc l] := rfl
@[simp] theorem enc_pair (a : α) (b : β) : enc (a, b) = .ctor 0 [enc a, enc b] := rfl
@[simp] theorem enc_true : enc true = .ctor 1 [] := rfl
@[simp] theorem enc_false : enc false = .ctor 0 [] := rfl
@[simp] theorem enc_nat (n : ℕ) : enc n = .nat n := rfl
@[simp] theorem enc_word (x : UInt64) : enc x = .word x := rfl
@[simp] theorem enc_k (x : K) : enc x = .word x.lane := rfl
@[simp] theorem enc_array (a : Array α) : enc a = .arr (a.map enc) := rfl

theorem enc_bool (b : Bool) : enc b = Val.ofBool b := rfl

end Enc

/-! ## Rules -/

namespace Rule

variable {P : Program} {env : List Val} {α β γ : Type} [Enc α] [Enc β] [Enc γ]

theorem var {i : ℕ} {x : α} (h : env[i]? = some (enc x)) : Runs P env (.var i) (enc x) 1 :=
  Runs.var h

theorem natLit (n : ℕ) : Runs P env (.val (.nat n)) (enc n) 1 := Runs.val _

theorem wordLit (x : UInt64) : Runs P env (.val (.word x)) (enc x) 1 := Runs.val _

theorem kLit (x : K) : Runs P env (.val (.word x.lane)) (enc x) 1 := Runs.val _

theorem boolLit (b : Bool) : Runs P env (.val (Val.ofBool b)) (enc b) 1 := Runs.val _

theorem letE {t b : Term} {v : α} {f : α → β} {c : ℕ} {d : α → ℕ} (h : Runs P env t (enc v) c)
    (hb : ∀ x, x = v → Runs P (enc x :: env) b (enc (f x)) (d x)) :
    Runs P env (.letE t b) (enc (f v)) (c + d v + 1) :=
  Runs.letE h (hb v rfl)

/-! ### Constructors and fields -/

theorem none : Runs P env (.ctor 0 []) (enc (none : Option α)) 1 :=
  (Runs.ctor (k := 0) RunsList.nil).cost_eq (by simp)

theorem some {t : Term} {a : α} {c : ℕ} (h : Runs P env t (enc a) c) :
    Runs P env (.ctor 1 [t]) (enc (some a)) (c + 2) :=
  (Runs.ctor (k := 1) (RunsList.cons h RunsList.nil)).cost_eq (by simp)

theorem nil : Runs P env (.ctor 0 []) (enc ([] : List α)) 1 :=
  (Runs.ctor (k := 0) RunsList.nil).cost_eq (by simp)

theorem cons {t u : Term} {a : α} {l : List α} {c d : ℕ} (h : Runs P env t (enc a) c)
    (hl : Runs P env u (enc l) d) : Runs P env (.ctor 1 [t, u]) (enc (a :: l)) (c + d + 3) :=
  (Runs.ctor (k := 1) (RunsList.cons h (RunsList.cons hl RunsList.nil))).cost_eq (by simp)

theorem pair {t u : Term} {a : α} {b : β} {c d : ℕ} (h : Runs P env t (enc a) c)
    (hb : Runs P env u (enc b) d) : Runs P env (.ctor 0 [t, u]) (enc (a, b)) (c + d + 3) :=
  (Runs.ctor (k := 0) (RunsList.cons h (RunsList.cons hb RunsList.nil))).cost_eq (by simp)

theorem fst {t : Term} {p : α × β} {c : ℕ} (h : Runs P env t (enc p) c) :
    Runs P env (.proj 0 t) (enc p.1) (c + 1) :=
  Runs.proj (k := 0) (fs := [enc p.1, enc p.2]) h rfl

theorem snd {t : Term} {p : α × β} {c : ℕ} (h : Runs P env t (enc p) c) :
    Runs P env (.proj 1 t) (enc p.2) (c + 1) :=
  Runs.proj (k := 0) (fs := [enc p.1, enc p.2]) h rfl

/-! ### Matches -/

theorem caseOption {t a b : Term} {o : Option α} {e₀ : β} {e₁ : α → β} {c c₀ : ℕ} {c₁ : α → ℕ}
    (h : Runs P env t (enc o) c) (h₀ : o = .none → Runs P env a (enc e₀) c₀)
    (h₁ : ∀ x, o = .some x → Runs P (enc x :: env) b (enc (e₁ x)) (c₁ x)) :
    Runs P env (.case t [a, b]) (enc (Option.casesOn (motive := fun _ ↦ β) o e₀ e₁))
      (c + Option.casesOn (motive := fun _ ↦ ℕ) o c₀ c₁ + 1) := by
  cases o with
  | none => exact Runs.case (k := 0) (fs := []) h rfl (h₀ rfl)
  | some x => exact Runs.case (k := 1) (fs := [enc x]) h rfl (h₁ x rfl)

theorem caseList {t a b : Term} {l : List α} {e₀ : β} {e₁ : α → List α → β} {c c₀ : ℕ}
    {c₁ : α → List α → ℕ} (h : Runs P env t (enc l) c) (h₀ : l = [] → Runs P env a (enc e₀) c₀)
    (h₁ : ∀ x xs, l = x :: xs → Runs P (enc x :: enc xs :: env) b (enc (e₁ x xs)) (c₁ x xs)) :
    Runs P env (.case t [a, b]) (enc (List.casesOn (motive := fun _ ↦ β) l e₀ e₁))
      (c + List.casesOn (motive := fun _ ↦ ℕ) l c₀ c₁ + 1) := by
  cases l with
  | nil => exact Runs.case (k := 0) (fs := []) h rfl (h₀ rfl)
  | cons x xs => exact Runs.case (k := 1) (fs := [enc x, enc xs]) h rfl (h₁ x xs rfl)

theorem casePair {t b : Term} {p : α × β} {e : α → β → γ} {c : ℕ} {c₁ : α → β → ℕ}
    (h : Runs P env t (enc p) c)
    (h₁ : ∀ x y, p = (x, y) → Runs P (enc x :: enc y :: env) b (enc (e x y)) (c₁ x y)) :
    Runs P env (.case t [b]) (enc (Prod.casesOn (motive := fun _ ↦ γ) p e))
      (c + Prod.casesOn (motive := fun _ ↦ ℕ) p c₁ + 1) := by
  obtain ⟨x, y⟩ := p
  exact Runs.case (k := 0) (fs := [enc x, enc y]) h rfl (h₁ x y rfl)

theorem ite {tc ta tb : Term} {p : Prop} [Decidable p] {a b : α} {c ca cb : ℕ}
    (h : Runs P env tc (enc (decide p)) c) (ha : p → Runs P env ta (enc a) ca)
    (hb : ¬p → Runs P env tb (enc b) cb) :
    Runs P env (.case tc [tb, ta]) (enc (if p then a else b)) (c + (if p then ca else cb) + 1) := by
  by_cases hp : p
  · exact Runs.case (k := 1) (fs := []) (by simpa [hp] using h) rfl (by simpa [hp] using ha hp)
  · exact Runs.case (k := 0) (fs := []) (by simpa [hp] using h) rfl (by simpa [hp] using hb hp)

theorem dite {tc ta tb : Term} {p : Prop} [Decidable p] {a : p → α} {b : ¬p → α} {c : ℕ}
    {ca : p → ℕ} {cb : ¬p → ℕ}
    (h : Runs P env tc (enc (decide p)) c) (ha : ∀ hp : p, Runs P env ta (enc (a hp)) (ca hp))
    (hb : ∀ hp : ¬p, Runs P env tb (enc (b hp)) (cb hp)) :
    Runs P env (.case tc [tb, ta]) (enc (if hp : p then a hp else b hp))
      (c + (if hp : p then ca hp else cb hp) + 1) := by
  by_cases hp : p
  · exact Runs.case (k := 1) (fs := []) (by simpa [hp] using h) rfl (by simpa [hp] using ha hp)
  · exact Runs.case (k := 0) (fs := []) (by simpa [hp] using h) rfl (by simpa [hp] using hb hp)

theorem cond {tc ta tb : Term} {b : Bool} {x y : α} {c ca cb : ℕ}
    (h : Runs P env tc (enc b) c) (ha : b = true → Runs P env ta (enc x) ca)
    (hb : b = false → Runs P env tb (enc y) cb) :
    Runs P env (.case tc [tb, ta]) (enc (bif b then x else y))
      (c + (bif b then ca else cb) + 1) := by
  cases b
  · exact Runs.case (k := 0) (fs := []) h rfl (by simpa using hb rfl)
  · exact Runs.case (k := 1) (fs := []) h rfl (by simpa using ha rfl)

theorem caseNat {t a b : Term} {n : ℕ} {e₀ : α} {e₁ : ℕ → α} {c c₀ : ℕ} {c₁ : ℕ → ℕ}
    (h : Runs P env t (enc n) c) (h₀ : n = 0 → Runs P env a (enc e₀) c₀)
    (h₁ : ∀ k, n = k + 1 → Runs P (enc k :: env) b (enc (e₁ k)) (c₁ k)) :
    Runs P env (.case (.op .neq [t, .val (.nat 0)]) [.letE (.op .nsub [t, .val (.nat 1)]) b, a])
      (enc (Nat.casesOn (motive := fun _ ↦ α) n e₀ e₁))
      (c + 1 + (max (limbs n) (limbs 0) + 1) +
        Nat.casesOn (motive := fun _ ↦ ℕ) n c₀ (fun k ↦ c + 1 + (max (limbs n) (limbs 1) + 1) +
          c₁ k + 1) + 1) := by
  have hz : Runs P env (.op .neq [t, .val (.nat 0)]) (enc (decide (n = 0)))
      (c + 1 + (max (limbs n) (limbs 0) + 1)) :=
    Runs.op (RunsList.cons h (RunsList.cons (Runs.val _) RunsList.nil))
      (by simp [Op.apply, enc_bool, Val.ofBool])
  cases n with
  | zero => exact Runs.case (k := 1) (fs := []) (by simpa using hz) rfl (h₀ rfl)
  | succ k =>
    have hs : Runs P env (.op .nsub [t, .val (.nat 1)]) (enc k)
        (c + 1 + (max (limbs (k + 1)) (limbs 1) + 1)) :=
      Runs.op (RunsList.cons h (RunsList.cons (Runs.val _) RunsList.nil)) (by simp [Op.apply, natOp])
    exact Runs.case (k := 0) (fs := []) (by simpa using hz) rfl (Runs.letE hs (h₁ k rfl))

/-- A closure of function `j` with the values of `ts`. -/
theorem closure {j : ℕ} {ts : List Term} {vs : List Val} {c : ℕ} (h : RunsList P env ts vs c) :
    Runs P env (.fn j ts) (.fn j vs) (c + vs.length + 1) := Runs.fn h

/-- A closure applied to the values of `ts`. -/
theorem app {t : Term} {ts : List Term} {f : Val} {vs : List Val} {w : Val} {c d : ℕ}
    (h : Runs P env t f c) (hl : RunsList P env ts vs d) (ha : RunsApp P f vs w) :
    Runs P env (.app t ts) w (c + d + appCost P f vs + 1) := by
  obtain ⟨j, us, rfl, hb⟩ := ha
  exact Runs.app h hl hb

/-- A raw value of the environment. -/
theorem rawVar {i : ℕ} {v : Val} (h : env[i]? = .some v) : Runs P env (.var i) v 1 := Runs.var h

/-- A call of a function on the encodings of its arguments. -/
theorem call {f : ℕ} {ts : List Term} {vs : List Val} {w : Val} {c d : ℕ}
    (h : RunsList P env ts vs c) (hb : RunsBody P f vs w d) :
    Runs P env (.call f ts) w (c + d + 1) := Runs.call h hb

/-- `a || b`, short-circuit. -/
theorem boolOr {t u : Term} {a b : Bool} {c d : ℕ} (h : Runs P env t (enc a) c)
    (hb : a = false → Runs P env u (enc b) d) :
    Runs P env (.case t [u, .ctor 1 []]) (enc (a || b)) (c + (if a then 1 else d) + 1) := by
  cases a
  · exact Runs.case (k := 0) (fs := []) h rfl (by simpa using hb rfl)
  · exact Runs.case (k := 1) (fs := []) h rfl (by simpa using (Runs.ctor (k := 1) (P := P) (env := env) RunsList.nil))

/-- `a && b`, short-circuit. -/
theorem boolAnd {t u : Term} {a b : Bool} {c d : ℕ} (h : Runs P env t (enc a) c)
    (hb : a = true → Runs P env u (enc b) d) :
    Runs P env (.case t [.ctor 0 [], u]) (enc (a && b)) (c + (if a then d else 1) + 1) := by
  cases a
  · exact Runs.case (k := 0) (fs := []) h rfl (by simpa using (Runs.ctor (k := 0) (P := P) (env := env) RunsList.nil))
  · exact Runs.case (k := 1) (fs := []) h rfl (by simpa using hb rfl)

theorem boolNot {t : Term} {a : Bool} {c : ℕ} (h : Runs P env t (enc a) c) :
    Runs P env (.case t [.ctor 1 [], .ctor 0 []]) (enc (!a)) (c + 1 + 1) := by
  cases a
  · exact Runs.case (k := 0) (fs := []) h rfl (by simpa using (Runs.ctor (k := 1) (P := P) (env := env) RunsList.nil))
  · exact Runs.case (k := 1) (fs := []) h rfl (by simpa using (Runs.ctor (k := 0) (P := P) (env := env) RunsList.nil))

/-! ### Primitives -/

/-- A primitive of two arguments, from the runs of its arguments. -/
theorem op₂ {o : Op} {t u : Term} {a : α} {b : β} {v : Val} {c d e : ℕ}
    (h : Runs P env t (enc a) c) (hb : Runs P env u (enc b) d)
    (ho : o.apply [enc a, enc b] = .some (v, e)) : Runs P env (.op o [t, u]) v (c + d + e) :=
  (Runs.op (RunsList.cons h (RunsList.cons hb RunsList.nil)) ho).cost_eq (by omega)

/-- A primitive of one argument. -/
theorem op₁ {o : Op} {t : Term} {a : α} {v : Val} {c e : ℕ} (h : Runs P env t (enc a) c)
    (ho : o.apply [enc a] = .some (v, e)) : Runs P env (.op o [t]) v (c + e) :=
  (Runs.op (RunsList.cons h RunsList.nil) ho).cost_eq (by omega)

theorem natAdd {t u : Term} {a b : ℕ} {c d : ℕ} (h : Runs P env t (enc a) c)
    (hb : Runs P env u (enc b) d) :
    Runs P env (.op .nadd [t, u]) (enc (a + b)) (c + d + (max (limbs a) (limbs b) + 1)) :=
  op₂ h hb rfl

theorem natSub {t u : Term} {a b : ℕ} {c d : ℕ} (h : Runs P env t (enc a) c)
    (hb : Runs P env u (enc b) d) :
    Runs P env (.op .nsub [t, u]) (enc (a - b)) (c + d + (max (limbs a) (limbs b) + 1)) :=
  op₂ h hb rfl

theorem natMul {t u : Term} {a b : ℕ} {c d : ℕ} (h : Runs P env t (enc a) c)
    (hb : Runs P env u (enc b) d) :
    Runs P env (.op .nmul [t, u]) (enc (a * b)) (c + d + (limbs a * limbs b + 1)) :=
  op₂ h hb rfl

theorem natDiv {t u : Term} {a b : ℕ} {c d : ℕ} (h : Runs P env t (enc a) c)
    (hb : Runs P env u (enc b) d) :
    Runs P env (.op .ndiv [t, u]) (enc (a / b)) (c + d + (limbs a * limbs b + 1)) :=
  op₂ h hb rfl

theorem natMod {t u : Term} {a b : ℕ} {c d : ℕ} (h : Runs P env t (enc a) c)
    (hb : Runs P env u (enc b) d) :
    Runs P env (.op .nmod [t, u]) (enc (a % b)) (c + d + (limbs a * limbs b + 1)) :=
  op₂ h hb rfl

theorem natLt {t u : Term} {a b : ℕ} {c d : ℕ} (h : Runs P env t (enc a) c)
    (hb : Runs P env u (enc b) d) :
    Runs P env (.op .nlt [t, u]) (enc (decide (a < b))) (c + d + (max (limbs a) (limbs b) + 1)) :=
  op₂ h hb rfl

theorem natLe {t u : Term} {a b : ℕ} {c d : ℕ} (h : Runs P env t (enc a) c)
    (hb : Runs P env u (enc b) d) :
    Runs P env (.op .nle [t, u]) (enc (decide (a ≤ b))) (c + d + (max (limbs a) (limbs b) + 1)) :=
  op₂ h hb rfl

theorem natEq {t u : Term} {a b : ℕ} {c d : ℕ} (h : Runs P env t (enc a) c)
    (hb : Runs P env u (enc b) d) :
    Runs P env (.op .neq [t, u]) (enc (decide (a = b))) (c + d + (max (limbs a) (limbs b) + 1)) :=
  op₂ h hb (by simp [Op.apply, enc_bool, Val.ofBool])

theorem wordLt {t u : Term} {a b : UInt64} {c d : ℕ} (h : Runs P env t (enc a) c)
    (hb : Runs P env u (enc b) d) :
    Runs P env (.op .wlt [t, u]) (enc (decide (a < b))) (c + d + 1) := op₂ h hb rfl

theorem wordLe {t u : Term} {a b : UInt64} {c d : ℕ} (h : Runs P env t (enc a) c)
    (hb : Runs P env u (enc b) d) :
    Runs P env (.op .wle [t, u]) (enc (decide (a ≤ b))) (c + d + 1) := op₂ h hb rfl

theorem wordEq {t u : Term} {a b : UInt64} {c d : ℕ} (h : Runs P env t (enc a) c)
    (hb : Runs P env u (enc b) d) :
    Runs P env (.op .weq [t, u]) (enc (decide (a = b))) (c + d + 1) :=
  op₂ h hb (by simp [Op.apply, wordOp, enc_bool, Val.ofBool])

/-- `decide (b = true)` is `b`. -/
theorem decideEqTrue {t : Term} {b : Bool} {c : ℕ} (h : Runs P env t (enc b) c) :
    Runs P env t (enc (decide (b = true))) c := by
  cases b <;> exact h

theorem uint8Eq {t u : Term} {a b : UInt8} {inst : Decidable (a = b)} {c d : ℕ}
    (h : Runs P env t (enc a) c) (hb : Runs P env u (enc b) d) :
    Runs P env (.op .weq [t, u]) (enc (@decide (a = b) inst)) (c + d + 1) :=
  op₂ h hb (by
    have : (a.toUInt64 == b.toUInt64) = @decide (a = b) inst := by
      by_cases hab : a = b
      · simp [hab]
      · have : a.toUInt64 ≠ b.toUInt64 := fun e ↦ hab (UInt8.toUInt64_inj.1 e)
        simp [hab, this]
    show Op.apply .weq [.word a.toUInt64, .word b.toUInt64] = _
    simp [Op.apply, wordOp, enc_bool, this])

theorem natBEq {t u : Term} {a b : ℕ} {c d : ℕ} (h : Runs P env t (enc a) c)
    (hb : Runs P env u (enc b) d) :
    Runs P env (.op .neq [t, u]) (enc (a == b)) (c + d + (max (limbs a) (limbs b) + 1)) :=
  op₂ h hb (by simp [Op.apply, enc_bool, Val.ofBool])

theorem wordBEq {t u : Term} {a b : UInt64} {c d : ℕ} (h : Runs P env t (enc a) c)
    (hb : Runs P env u (enc b) d) : Runs P env (.op .weq [t, u]) (enc (a == b)) (c + d + 1) :=
  op₂ h hb (by simp [Op.apply, wordOp, enc_bool])

theorem kEq {t u : Term} {a b : K} {inst : Decidable (a = b)} {c d : ℕ}
    (h : Runs P env t (enc a) c) (hb : Runs P env u (enc b) d) :
    Runs P env (.op .weq [t, u]) (enc (@decide (a = b) inst)) (c + d + 1) :=
  op₂ h hb (by
    have : (a.lane == b.lane) = @decide (a = b) inst := by
      by_cases hab : a = b
      · simp [hab]
      · have : a.lane ≠ b.lane := fun e ↦ hab (by
          rw [← show K.ofLane a.lane = a from rfl, ← show K.ofLane b.lane = b from rfl, e])
        simp [hab, this]
    simp [Op.apply, wordOp, enc_bool, this])

theorem kBEq {t u : Term} {a b : K} {c d : ℕ} (h : Runs P env t (enc a) c)
    (hb : Runs P env u (enc b) d) : Runs P env (.op .weq [t, u]) (enc (a == b)) (c + d + 1) :=
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
    simp [Op.apply, wordOp, enc_bool, this])

/-! ### Words -/

theorem wXor {t u : Term} {a b : UInt64} {c d : ℕ} (h : Runs P env t (enc a) c)
    (hb : Runs P env u (enc b) d) : Runs P env (.op .wxor [t, u]) (enc (a ^^^ b)) (c + d + 1) :=
  op₂ h hb rfl
theorem wAnd {t u : Term} {a b : UInt64} {c d : ℕ} (h : Runs P env t (enc a) c)
    (hb : Runs P env u (enc b) d) : Runs P env (.op .wand [t, u]) (enc (a &&& b)) (c + d + 1) :=
  op₂ h hb rfl
theorem wOr {t u : Term} {a b : UInt64} {c d : ℕ} (h : Runs P env t (enc a) c)
    (hb : Runs P env u (enc b) d) : Runs P env (.op .wor [t, u]) (enc (a ||| b)) (c + d + 1) :=
  op₂ h hb rfl
theorem wNot {t : Term} {a : UInt64} {c : ℕ} (h : Runs P env t (enc a) c) :
    Runs P env (.op .wnot [t]) (enc (~~~a)) (c + 1) := op₁ h rfl
theorem wShl {t u : Term} {a b : UInt64} {c d : ℕ} (h : Runs P env t (enc a) c)
    (hb : Runs P env u (enc b) d) : Runs P env (.op .wshl [t, u]) (enc (a <<< b)) (c + d + 1) :=
  op₂ h hb rfl
theorem wShr {t u : Term} {a b : UInt64} {c d : ℕ} (h : Runs P env t (enc a) c)
    (hb : Runs P env u (enc b) d) : Runs P env (.op .wshr [t, u]) (enc (a >>> b)) (c + d + 1) :=
  op₂ h hb rfl
theorem wAdd {t u : Term} {a b : UInt64} {c d : ℕ} (h : Runs P env t (enc a) c)
    (hb : Runs P env u (enc b) d) : Runs P env (.op .wadd [t, u]) (enc (a + b)) (c + d + 1) :=
  op₂ h hb rfl
theorem wSub {t u : Term} {a b : UInt64} {c d : ℕ} (h : Runs P env t (enc a) c)
    (hb : Runs P env u (enc b) d) : Runs P env (.op .wsub [t, u]) (enc (a - b)) (c + d + 1) :=
  op₂ h hb rfl
theorem wMul {t u : Term} {a b : UInt64} {c d : ℕ} (h : Runs P env t (enc a) c)
    (hb : Runs P env u (enc b) d) : Runs P env (.op .wmul [t, u]) (enc (a * b)) (c + d + 1) :=
  op₂ h hb rfl
theorem wToNat {t : Term} {a : UInt64} {c : ℕ} (h : Runs P env t (enc a) c) :
    Runs P env (.op .wtoNat [t]) (enc a.toNat) (c + 1) := op₁ h rfl
theorem natToUInt64 {t : Term} {n : ℕ} {c : ℕ} (h : Runs P env t (enc n) c) :
    Runs P env (.op .wofNat [t]) (enc n.toUInt64) (c + 1) := op₁ h (by simp [Op.apply])

/-- `K.lane`: the same word. -/
theorem kLane {t : Term} {a : K} {c : ℕ} (h : Runs P env t (enc a) c) :
    Runs P env t (enc a.lane) c := h

theorem u8Xor {t u : Term} {a b : UInt8} {c d : ℕ} (h : Runs P env t (enc a) c)
    (hb : Runs P env u (enc b) d) : Runs P env (.op .wxor [t, u]) (enc (a ^^^ b)) (c + d + 1) :=
  op₂ h hb (by
    show Op.apply .wxor [.word a.toUInt64, .word b.toUInt64] = _
    simp [Op.apply, wordOp]; rfl)
theorem u8And {t u : Term} {a b : UInt8} {c d : ℕ} (h : Runs P env t (enc a) c)
    (hb : Runs P env u (enc b) d) : Runs P env (.op .wand [t, u]) (enc (a &&& b)) (c + d + 1) :=
  op₂ h hb (by
    show Op.apply .wand [.word a.toUInt64, .word b.toUInt64] = _
    simp [Op.apply, wordOp]; rfl)
theorem u8Or {t u : Term} {a b : UInt8} {c d : ℕ} (h : Runs P env t (enc a) c)
    (hb : Runs P env u (enc b) d) : Runs P env (.op .wor [t, u]) (enc (a ||| b)) (c + d + 1) :=
  op₂ h hb (by
    show Op.apply .wor [.word a.toUInt64, .word b.toUInt64] = _
    simp [Op.apply, wordOp]; rfl)
/-- A byte as a word: the same word. -/
theorem u8ToUInt64 {t : Term} {a : UInt8} {c : ℕ} (h : Runs P env t (enc a) c) :
    Runs P env t (enc a.toUInt64) c := h
theorem u64ToUInt8 {t : Term} {a : UInt64} {c : ℕ} (h : Runs P env t (enc a) c) :
    Runs P env (.op .wand [t, .val (.word 255)]) (enc a.toUInt8) (c + 1 + 1) :=
  (Runs.op (RunsList.cons h (RunsList.cons (Runs.val _) RunsList.nil)) (v := enc a.toUInt8) (d := 1)
    (by
      show Op.apply .wand [.word a, .word 255] = .some (.word a.toUInt8.toUInt64, 1)
      simp only [Op.apply, wordOp, Option.some.injEq, Prod.mk.injEq, Val.word.injEq, and_true]
      apply UInt64.toNat_inj.1
      rw [UInt64.toNat_and, UInt8.toNat_toUInt64, UInt64.toNat_toUInt8,
        show (255 : UInt64).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod])).cost_eq
        (by omega)

theorem natAnd {t u : Term} {a b : ℕ} {c d : ℕ} (h : Runs P env t (enc a) c)
    (hb : Runs P env u (enc b) d) :
    Runs P env (.op .nand [t, u]) (enc (a &&& b)) (c + d + (max (limbs a) (limbs b) + 1)) :=
  op₂ h hb rfl
theorem natShiftRight {t u : Term} {a k : ℕ} {c d : ℕ} (h : Runs P env t (enc a) c)
    (hb : Runs P env u (enc k) d) :
    Runs P env (.op .nshr [t, u]) (enc (a >>> k)) (c + d + (limbs a + limbs k + 1)) :=
  op₂ h hb rfl

/-- `decide (p ∧ q)`, short-circuit. -/
theorem decideAnd {t u : Term} {p q : Prop} [Decidable p] [Decidable q] {inst : Decidable (p ∧ q)}
    {c d : ℕ} (h : Runs P env t (enc (decide p)) c) (hq : p → Runs P env u (enc (decide q)) d) :
    Runs P env (.case t [.ctor 0 [], u]) (enc (@decide (p ∧ q) inst))
      (c + (if p then d else 1) + 1) := by
  by_cases hp : p
  · have := Runs.case (k := 1) (fs := []) (alts := [.ctor 0 [], u]) (by simpa [hp] using h) rfl (hq hp)
    simpa [hp] using this
  · have := Runs.case (k := 0) (fs := []) (alts := [.ctor 0 [], u]) (by simpa [hp] using h) rfl
      (Runs.ctor (k := 0) (P := P) (env := env) RunsList.nil)
    simpa [hp, enc_bool, Val.ofBool] using this

/-- `decide ¬p`. -/
theorem decideNot {t : Term} {p : Prop} [Decidable p] {inst : Decidable ¬p} {c : ℕ}
    (h : Runs P env t (enc (decide p)) c) :
    Runs P env (.case t [.ctor 1 [], .ctor 0 []]) (enc (@decide (¬p) inst)) (c + 1 + 1) := by
  by_cases hp : p
  · have := Runs.case (k := 1) (fs := []) (alts := [.ctor 1 [], .ctor 0 []]) (by simpa [hp] using h) rfl
      (Runs.ctor (k := 0) (P := P) (env := env) RunsList.nil)
    simpa [hp, enc_bool, Val.ofBool] using this
  · have := Runs.case (k := 0) (fs := []) (alts := [.ctor 1 [], .ctor 0 []]) (by simpa [hp] using h) rfl
      (Runs.ctor (k := 1) (P := P) (env := env) RunsList.nil)
    simpa [hp, enc_bool, Val.ofBool] using this

/-! ### Arrays -/

theorem arrSize {t : Term} {a : Array α} {c : ℕ} (h : Runs P env t (enc a) c) :
    Runs P env (.op .asize [t]) (enc a.size) (c + 1) := op₁ h (by simp [Op.apply])

theorem arrAppend {t u : Term} {a b : Array α} {c d : ℕ} (h : Runs P env t (enc a) c)
    (hb : Runs P env u (enc b) d) :
    Runs P env (.op .aappend [t, u]) (enc (a ++ b)) (c + d + (a.size + b.size + 1)) :=
  op₂ h hb (by simp [Op.apply])

theorem arrReplicate {t u : Term} {n : ℕ} {x : α} {c d : ℕ} (h : Runs P env t (enc n) c)
    (hb : Runs P env u (enc x) d) :
    Runs P env (.op .areplicate [t, u]) (enc (Array.replicate n x)) (c + d + (n + 1)) :=
  op₂ h hb (by simp [Op.apply])

theorem arrToList {t : Term} {a : Array α} {c : ℕ} (h : Runs P env t (enc a) c) :
    Runs P env (.op .atoList [t]) (enc a.toList) (c + (3 * a.size + 1)) :=
  op₁ h (by simp [Op.apply]; rfl)

theorem valToList_ofList (l : List Val) : Val.toList? (.ofList l) = .some l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [Val.ofList, Val.toList?, ih]

theorem listToArray {t : Term} {l : List α} {c : ℕ} (h : Runs P env t (enc l) c) :
    Runs P env (.op .aofList [t]) (enc l.toArray) (c + (l.length + 1)) :=
  op₁ h (by
    show Op.apply .aofList [.ofList (l.map enc)] = _
    simp [Op.apply, valToList_ofList])

theorem arrGetD {t u w : Term} {a : Array α} {i : ℕ} {x : α} {c d e : ℕ}
    (h : Runs P env t (enc a) c) (hi : Runs P env u (enc i) d) (hx : Runs P env w (enc x) e) :
    Runs P env (.op .aget [t, u, w]) (enc (a.getD i x)) (c + d + e + 1) :=
  (Runs.op (RunsList.cons h (RunsList.cons hi (RunsList.cons hx RunsList.nil)))
    (v := enc (a.getD i x)) (d := 1) (by
      simp only [enc_array, enc_nat, Op.apply, Option.some.injEq, Prod.mk.injEq, and_true]
      simp [Array.getD_eq_getD_getElem?])).cost_eq (by omega)

theorem arrGetElem? {t u : Term} {a : Array α} {i : ℕ} {c d : ℕ} (h : Runs P env t (enc a) c)
    (hi : Runs P env u (enc i) d) :
    Runs P env (.case (.op .nlt [u, .op .asize [t]]) [.ctor 0 [], .ctor 1 [.op .aget [t, u, .val (.ctor 0 [])]]])
      (enc a[i]?) (d + (c + 1) + (max (limbs i) (limbs a.size) + 1) +
        (if i < a.size then c + d + 1 + 1 + 2 else 1) + 1) := by
  have hlt := natLt hi (arrSize h)
  by_cases hia : i < a.size
  · have hg : Runs P env (.op .aget [t, u, .val (.ctor 0 [])]) (enc a[i]) (c + d + 1 + 1) :=
      (Runs.op (RunsList.cons h (RunsList.cons hi (RunsList.cons (Runs.val _) RunsList.nil)))
        (v := enc a[i]) (d := 1) (by simp [Op.apply, hia])).cost_eq (by omega)
    have := Runs.case (k := 1) (fs := []) (alts := [.ctor 0 [], .ctor 1 [.op .aget [t, u, .val (.ctor 0 [])]]])
      (by simpa [hia] using hlt) rfl (some hg)
    simpa [hia, Array.getElem?_eq_getElem hia] using this
  · have := Runs.case (k := 0) (fs := []) (alts := [.ctor 0 [], .ctor 1 [.op .aget [t, u, .val (.ctor 0 [])]]])
      (by simpa [hia] using hlt) rfl (none (P := P) (env := env) (α := α))
    simpa [hia, Array.getElem?_eq_none (Nat.le_of_not_lt hia)] using this

/-- A subtype's value: the same value. -/
theorem subtypeVal {t : Term} {p : α → Prop} {x : Subtype p} {c : ℕ} (h : Runs P env t (enc x) c) :
    Runs P env t (enc x.val) c := h

/-- A subtype's element: the same value. -/
theorem subtypeMk {t : Term} {p : α → Prop} {x : α} {hx : p x} {c : ℕ} (h : Runs P env t (enc x) c) :
    Runs P env t (enc (⟨x, hx⟩ : Subtype p)) c := h

/-- `a[i]'h`: an entry in bounds. -/
theorem arrGetElem {t u : Term} {a : Array α} {i : ℕ} {h : i < a.size} {c d : ℕ}
    (ha : Runs P env t (enc a) c) (hi : Runs P env u (enc i) d) :
    Runs P env (.op .aget [t, u, .val (.ctor 0 [])]) (enc (a[i]'h)) (c + d + 1 + 1) :=
  (Runs.op (RunsList.cons ha (RunsList.cons hi (RunsList.cons (Runs.val _) RunsList.nil)))
    (v := enc (a[i]'h)) (d := 1) (by simp [Op.apply, h])).cost_eq (by omega)

/-- `K.ofLane`: the same word. -/
theorem kOfLane {t : Term} {w : UInt64} {c : ℕ} (h : Runs P env t (enc w) c) :
    Runs P env t (enc (K.ofLane w)) c := h

theorem uint8ToNat {t : Term} {x : UInt8} {c : ℕ} (h : Runs P env t (enc x) c) :
    Runs P env (.op .wtoNat [t]) (enc x.toNat) (c + 1) := op₁ h (by simp [Op.apply]; rfl)

theorem uint64OfNat {t : Term} {n : ℕ} {c : ℕ} (h : Runs P env t (enc n) c) :
    Runs P env (.op .wofNat [t]) (enc (UInt64.ofNat n)) (c + 1) := op₁ h (by simp [Op.apply])

theorem natShiftLeft {t u : Term} {a k : ℕ} {c d : ℕ} (h : Runs P env t (enc a) c)
    (hb : Runs P env u (enc k) d) :
    Runs P env (.op .nshl [t, u]) (enc (a <<< k)) (c + d + (limbs (a <<< k) + limbs k + 1)) :=
  op₂ h hb rfl

theorem vecToList {t : Term} {n : ℕ} {v : Vector α n} {c : ℕ} (h : Runs P env t (enc v) c) :
    Runs P env (.op .atoList [t]) (enc v.toList) (c + (3 * v.toArray.size + 1)) :=
  op₁ h (by
    show Op.apply .atoList [.arr (v.toArray.map enc)] = _
    simp [Op.apply, Vector.toList]
    rfl)

/-- A vector of an array: the same value. -/
theorem vecMk {t : Term} {n : ℕ} {a : Array α} {ha : a.size = n} {c : ℕ}
    (h : Runs P env t (enc a) c) : Runs P env t (enc (Vector.mk a ha)) c := h

theorem arrSetIfInBounds {t u w : Term} {a : Array α} {i : ℕ} {x : α} {c d e : ℕ}
    (h : Runs P env t (enc a) c) (hi : Runs P env u (enc i) d) (hx : Runs P env w (enc x) e) :
    Runs P env (.op .aset [t, u, w]) (enc (a.setIfInBounds i x)) (c + d + e + (a.size + 1)) :=
  (Runs.op (RunsList.cons h (RunsList.cons hi (RunsList.cons hx RunsList.nil)))
    (v := enc (a.setIfInBounds i x)) (d := a.size + 1) (by
      simp [Op.apply, Array.map_setIfInBounds])).cost_eq (by omega)

theorem arrExtract {t u w : Term} {a : Array α} {i j : ℕ} {c d e : ℕ}
    (h : Runs P env t (enc a) c) (hi : Runs P env u (enc i) d) (hj : Runs P env w (enc j) e) :
    Runs P env (.op .aextract [t, u, w]) (enc (a.extract i j))
      (c + d + e + ((a.extract i j).size + 1)) :=
  (Runs.op (RunsList.cons h (RunsList.cons hi (RunsList.cons hj RunsList.nil)))
    (v := enc (a.extract i j)) (d := (a.extract i j).size + 1) (by
      simp [Op.apply])).cost_eq (by omega)

/-- `Fin.val`: the same number. -/
theorem finVal {t : Term} {n : ℕ} {i : Fin n} {c : ℕ} (h : Runs P env t (enc i) c) :
    Runs P env t (enc i.val) c := h

/-- `Fin.mk`: the same number. -/
theorem finMk {t : Term} {n i : ℕ} {hi : i < n} {c : ℕ} (h : Runs P env t (enc i) c) :
    Runs P env t (enc (⟨i, hi⟩ : Fin n)) c := h

theorem kSub {t u : Term} {a b : K} {c d : ℕ} (h : Runs P env t (enc a) c)
    (hb : Runs P env u (enc b) d) : Runs P env (.op .wxor [t, u]) (enc (a - b)) (c + d + 1) :=
  op₂ h hb rfl

theorem kAdd {t u : Term} {a b : K} {c d : ℕ} (h : Runs P env t (enc a) c)
    (hb : Runs P env u (enc b) d) : Runs P env (.op .wxor [t, u]) (enc (a + b)) (c + d + 1) :=
  op₂ h hb rfl

theorem kMul {t u : Term} {a b : K} {c d : ℕ} (h : Runs P env t (enc a) c)
    (hb : Runs P env u (enc b) d) : Runs P env (.op .gfmul [t, u]) (enc (a * b)) (c + d + 256) :=
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

end Rewrite

end

end LeanVM.Cost
