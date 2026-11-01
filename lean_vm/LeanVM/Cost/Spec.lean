module

public import LeanVM.Cost.Machine

/-!
# Runs of the cost machine

`Runs P env t v c`: the term `t` evaluates in `env` to `v` at price `c`, for some fuel. More fuel
never changes a run that succeeds (`eval_mono`), so runs compose: one rule per construct
(`Runs.var`, `Runs.op`, `Runs.call`, …), the steps the compiler's proofs chain.
-/

namespace LeanVM.Cost

@[expose] public section

/-- `t` evaluates in `env` to `v` at price `c`. -/
def Runs (P : Program) (env : List Val) (t : Term) (v : Val) (c : ℕ) : Prop :=
  ∃ n, eval P n env t = some (v, c)

/-- The terms evaluate in `env` to `vs` at total price `c`. -/
def RunsList (P : Program) (env : List Val) (ts : List Term) (vs : List Val) (c : ℕ) : Prop :=
  ∃ n, evalList P n env ts = some (vs, c)

/-- Function `f` on the arguments `vs` returns `v` at price `c`. -/
def RunsBody (P : Program) (f : ℕ) (vs : List Val) (v : Val) (c : ℕ) : Prop :=
  ∃ n, evalBody P n f vs = some (v, c)

/-! ## More fuel -/

theorem eval_mono (P : Program) :
    (∀ n env t r, eval P n env t = some r → eval P (n + 1) env t = some r) ∧
    (∀ n env ts r, evalList P n env ts = some r → evalList P (n + 1) env ts = some r) ∧
    (∀ n env fs k as r, evalAlt P n env fs k as = some r → evalAlt P (n + 1) env fs k as = some r) ∧
    (∀ n f vs r, evalBody P n f vs = some r → evalBody P (n + 1) f vs = some r) := by
  have h := eval.mutual_induct P
    (fun n env t ↦ ∀ r, eval P n env t = some r → eval P (n + 1) env t = some r)
    (fun n f vs ↦ ∀ r, evalBody P n f vs = some r → evalBody P (n + 1) f vs = some r)
    (fun n env fs k as ↦ ∀ r, evalAlt P n env fs k as = some r →
      evalAlt P (n + 1) env fs k as = some r)
    (fun n env ts ↦ ∀ r, evalList P n env ts = some r → evalList P (n + 1) env ts = some r)
    (fun _ _ _ _ h ↦ by simpa [eval] using h)
    (fun _ _ _ _ h ↦ by simpa [eval] using h)
    (fun n env o ts ih r h ↦ by
      simp only [eval] at h ⊢
      obtain ⟨⟨vs, c⟩, hl, h⟩ := Option.bind_eq_some_iff.1 h
      rw [ih _ hl]
      simp only [Option.bind_eq_bind, Option.bind_some]
      simpa using h)
    (fun n env k ts ih r h ↦ by
      simp only [eval] at h ⊢
      obtain ⟨⟨vs, c⟩, hl, h⟩ := Option.bind_eq_some_iff.1 h
      rw [ih _ hl]
      simp only [Option.bind_eq_bind, Option.bind_some]
      simpa using h)
    (fun n env i t ih r h ↦ by
      simp only [eval] at h ⊢
      obtain ⟨⟨v, c⟩, hl, h⟩ := Option.bind_eq_some_iff.1 h
      rw [ih _ hl]
      simp only [Option.bind_eq_bind, Option.bind_some]
      simpa using h)
    (fun n env t alts ih iha r h ↦ by
      simp only [eval] at h ⊢
      obtain ⟨⟨v, c⟩, hl, h⟩ := Option.bind_eq_some_iff.1 h
      rw [ih _ hl]
      simp only [Option.bind_eq_bind, Option.bind_some]
      cases v with
      | ctor k fs =>
        simp only at h ⊢
        obtain ⟨⟨w, d⟩, ha, h⟩ := Option.bind_eq_some_iff.1 h
        rw [iha k fs _ ha]
        simpa using h
      | _ => simp at h)
    (fun n env t b ih ihb r h ↦ by
      simp only [eval] at h ⊢
      obtain ⟨⟨v, c⟩, hl, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨⟨w, d⟩, hb, h⟩ := Option.bind_eq_some_iff.1 h
      rw [ih _ hl]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [ihb v _ hb]
      simpa using h)
    (fun n env f ts ih ihb r h ↦ by
      simp only [eval] at h ⊢
      obtain ⟨⟨vs, c⟩, hl, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨⟨w, d⟩, hb, h⟩ := Option.bind_eq_some_iff.1 h
      rw [ih _ hl]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [ihb vs _ hb]
      simpa using h)
    (fun n env f ts ih r h ↦ by
      simp only [eval] at h ⊢
      obtain ⟨⟨vs, c⟩, hl, h⟩ := Option.bind_eq_some_iff.1 h
      rw [ih _ hl]
      simp only [Option.bind_eq_bind, Option.bind_some]
      simpa using h)
    (fun n env t ts ih ihl ihb r h ↦ by
      simp only [eval] at h ⊢
      obtain ⟨⟨g, c⟩, hg, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨⟨vs, d⟩, hl, h⟩ := Option.bind_eq_some_iff.1 h
      rw [ih _ hg]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [ihl _ hl]
      simp only [Option.bind_some]
      cases g with
      | fn f us =>
        simp only at h ⊢
        obtain ⟨⟨w, e⟩, hb, h⟩ := Option.bind_eq_some_iff.1 h
        rw [ihb vs f us _ hb]
        simpa using h
      | _ => simp at h)
    (fun _ _ _ h ↦ by simp [evalBody] at h)
    (fun n f vs b hb ih r h ↦ by
      simp only [evalBody, hb] at h ⊢
      exact ih _ h)
    (fun n f vs hb r h ↦ by simp [evalBody, hb] at h)
    (fun _ _ _ _ r h ↦ by simp [evalAlt] at h)
    (fun n env fs a tail ih r h ↦ by
      simp only [evalAlt] at h ⊢
      exact ih _ h)
    (fun n env fs k head as ih r h ↦ by
      simp only [evalAlt] at h ⊢
      exact ih _ h)
    (fun _ _ r h ↦ by simpa [evalList] using h)
    (fun n env t ts ih ihl r h ↦ by
      simp only [evalList] at h ⊢
      obtain ⟨⟨v, c⟩, hv, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨⟨vs, d⟩, hl, h⟩ := Option.bind_eq_some_iff.1 h
      rw [ih _ hv]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [ihl _ hl]
      simp only [Option.bind_some]
      simpa using h)
  exact ⟨h.1, h.2.2.2, h.2.2.1, h.2.1⟩

section Mono

variable {P : Program}

theorem eval_le {n m : ℕ} (h : n ≤ m) {env : List Val} {t : Term} {r : Val × ℕ}
    (he : eval P n env t = some r) : eval P m env t = some r := by
  induction m, h using Nat.le_induction with
  | base => exact he
  | succ m _ ih => exact (eval_mono P).1 _ _ _ _ ih

theorem evalList_le {n m : ℕ} (h : n ≤ m) {env : List Val} {ts : List Term} {r : List Val × ℕ}
    (he : evalList P n env ts = some r) : evalList P m env ts = some r := by
  induction m, h using Nat.le_induction with
  | base => exact he
  | succ m _ ih => exact (eval_mono P).2.1 _ _ _ _ ih

theorem evalBody_le {n m : ℕ} (h : n ≤ m) {f : ℕ} {vs : List Val} {r : Val × ℕ}
    (he : evalBody P n f vs = some r) : evalBody P m f vs = some r := by
  induction m, h using Nat.le_induction with
  | base => exact he
  | succ m _ ih => exact (eval_mono P).2.2.2 _ _ _ _ ih

end Mono

/-! ## One rule per construct -/

namespace Runs

variable {P : Program} {env : List Val}

theorem var {i : ℕ} {v : Val} (h : env[i]? = some v) : Runs P env (.var i) v 1 :=
  ⟨0, by simp [eval, h]⟩

theorem val (v : Val) : Runs P env (.val v) v 1 := ⟨0, by simp [eval]⟩

theorem op {o : Op} {ts : List Term} {vs : List Val} {v : Val} {c d : ℕ}
    (h : RunsList P env ts vs c) (ho : o.apply vs = some (v, d)) :
    Runs P env (.op o ts) v (c + d) := by
  obtain ⟨n, h⟩ := h
  exact ⟨n, by simp [eval, h, ho]⟩

theorem ctor {k : ℕ} {ts : List Term} {vs : List Val} {c : ℕ} (h : RunsList P env ts vs c) :
    Runs P env (.ctor k ts) (.ctor k vs) (c + vs.length + 1) := by
  obtain ⟨n, h⟩ := h
  exact ⟨n, by simp [eval, h]⟩

theorem proj {i k : ℕ} {t : Term} {fs : List Val} {v : Val} {c : ℕ}
    (h : Runs P env t (.ctor k fs) c) (hi : fs[i]? = some v) :
    Runs P env (.proj i t) v (c + 1) := by
  obtain ⟨n, h⟩ := h
  exact ⟨n, by simp [eval, h, hi]⟩

theorem evalAlt_of {n : ℕ} {fs : List Val} :
    ∀ {k : ℕ} {alts : List Term} {a : Term}, alts[k]? = some a →
      evalAlt P n env fs k alts = eval P n (fs ++ env) a
  | 0, a' :: _, a, h => by simp at h; subst h; simp [evalAlt]
  | k + 1, _ :: as, a, h => by
    simp only [List.getElem?_cons_succ] at h
    simp only [evalAlt]
    exact evalAlt_of h
  | _, [], _, h => by simp at h

theorem case {t : Term} {alts : List Term} {k : ℕ} {fs : List Val} {a : Term} {v : Val}
    {c d : ℕ} (h : Runs P env t (.ctor k fs) c) (ha : alts[k]? = some a)
    (hb : Runs P (fs ++ env) a v d) : Runs P env (.case t alts) v (c + d + 1) := by
  obtain ⟨n, h⟩ := h
  obtain ⟨m, hb⟩ := hb
  refine ⟨max n m, ?_⟩
  simp [eval, eval_le (le_max_left n m) h, evalAlt_of ha, eval_le (le_max_right n m) hb]

theorem letE {t b : Term} {v w : Val} {c d : ℕ} (h : Runs P env t v c)
    (hb : Runs P (v :: env) b w d) : Runs P env (.letE t b) w (c + d + 1) := by
  obtain ⟨n, h⟩ := h
  obtain ⟨m, hb⟩ := hb
  refine ⟨max n m, ?_⟩
  simp [eval, eval_le (le_max_left n m) h, eval_le (le_max_right n m) hb]

theorem call {f : ℕ} {ts : List Term} {vs : List Val} {w : Val} {c d : ℕ}
    (h : RunsList P env ts vs c) (hb : RunsBody P f vs w d) :
    Runs P env (.call f ts) w (c + d + 1) := by
  obtain ⟨n, h⟩ := h
  obtain ⟨m, hb⟩ := hb
  refine ⟨max n m, ?_⟩
  simp [eval, evalList_le (le_max_left n m) h, evalBody_le (le_max_right n m) hb]

theorem fn {f : ℕ} {ts : List Term} {vs : List Val} {c : ℕ} (h : RunsList P env ts vs c) :
    Runs P env (.fn f ts) (.fn f vs) (c + vs.length + 1) := by
  obtain ⟨n, h⟩ := h
  exact ⟨n, by simp [eval, h]⟩

theorem app {t : Term} {ts : List Term} {f : ℕ} {us vs : List Val} {w : Val} {c d e : ℕ}
    (h : Runs P env t (.fn f us) c) (hl : RunsList P env ts vs d)
    (hb : RunsBody P f (us ++ vs) w e) : Runs P env (.app t ts) w (c + d + e + 1) := by
  obtain ⟨n, h⟩ := h
  obtain ⟨m, hl⟩ := hl
  obtain ⟨k, hb⟩ := hb
  refine ⟨max n (max m k), ?_⟩
  simp [eval, eval_le (show n ≤ max n (max m k) by omega) h,
    evalList_le (show m ≤ max n (max m k) by omega) hl,
    evalBody_le (show k ≤ max n (max m k) by omega) hb]

theorem cost_eq {t : Term} {v : Val} {c c' : ℕ} (h : Runs P env t v c) (hc : c = c') :
    Runs P env t v c' := hc ▸ h

end Runs

theorem RunsList.nil {P : Program} {env : List Val} : RunsList P env [] [] 0 := ⟨0, by simp [evalList]⟩

theorem RunsList.cons {P : Program} {env : List Val} {t : Term} {ts : List Term} {v : Val}
    {vs : List Val} {c d : ℕ} (h : Runs P env t v c) (hl : RunsList P env ts vs d) :
    RunsList P env (t :: ts) (v :: vs) (c + d) := by
  obtain ⟨n, h⟩ := h
  obtain ⟨m, hl⟩ := hl
  refine ⟨max n m, ?_⟩
  simp [evalList, eval_le (le_max_left n m) h, evalList_le (le_max_right n m) hl]

theorem RunsBody.intro {P : Program} {f : ℕ} {b : Term} {vs : List Val} {v : Val} {c : ℕ}
    (hf : P[f]? = some b) (h : Runs P vs b v c) : RunsBody P f vs v c := by
  obtain ⟨n, h⟩ := h
  exact ⟨n + 1, by simp [evalBody, hf, h]⟩

/-- The program holds the bodies `l` at their indices. -/
def Includes (P : Program) (l : List (ℕ × Term)) : Prop := ∀ p ∈ l, P[p.1]? = some p.2

theorem Includes.get {P : Program} {l : List (ℕ × Term)} (h : Includes P l) {i : ℕ} {b : Term}
    (hm : (i, b) ∈ l) : P[i]? = some b := h _ hm

theorem Includes.mono {P : Program} {l l' : List (ℕ × Term)} (h : Includes P l)
    (hl : ∀ p ∈ l', p ∈ l) : Includes P l' := fun p hp ↦ h p (hl p hp)

theorem Includes.ofForall {P : Program} {l l' : List (ℕ × Term)} (h : Includes P l)
    (hl : List.Forall (· ∈ l) l') : Includes P l' :=
  h.mono fun _ hp ↦ List.forall_iff_forall_mem.1 hl _ hp

/-- The program holding the bodies `l` at their indices (the last body given an index wins), the
other entries a literal `0`. -/
def Program.ofList (l : List (ℕ × Term)) : Program :=
  let n := (l.map (·.1)).foldr max 0 + 1
  l.foldl (fun P p ↦ P.setIfInBounds p.1 p.2) (Array.replicate n (.val (.nat 0)))

theorem RunsBody.cost_eq {P : Program} {f : ℕ} {vs : List Val} {v : Val} {c c' : ℕ}
    (h : RunsBody P f vs v c) (hc : c = c') : RunsBody P f vs v c' := hc ▸ h

/-! ## The price bounds the fuel -/

/-- A run of price `c` needs at most `c` nested calls. -/
theorem eval_fuel (P : Program) :
    (∀ n env t v c, eval P n env t = some (v, c) → eval P c env t = some (v, c)) ∧
    (∀ n env ts vs c, evalList P n env ts = some (vs, c) → evalList P c env ts = some (vs, c)) ∧
    (∀ n env fs k as v c, evalAlt P n env fs k as = some (v, c) →
      evalAlt P c env fs k as = some (v, c)) ∧
    (∀ n f vs v c, evalBody P n f vs = some (v, c) → evalBody P (c + 1) f vs = some (v, c)) := by
  have h := eval.mutual_induct P
    (fun n env t ↦ ∀ v c, eval P n env t = some (v, c) → eval P c env t = some (v, c))
    (fun n f vs ↦ ∀ v c, evalBody P n f vs = some (v, c) → evalBody P (c + 1) f vs = some (v, c))
    (fun n env fs k as ↦ ∀ v c, evalAlt P n env fs k as = some (v, c) →
      evalAlt P c env fs k as = some (v, c))
    (fun n env ts ↦ ∀ vs c, evalList P n env ts = some (vs, c) → evalList P c env ts = some (vs, c))
    (fun _ _ _ v c h ↦ by simpa [eval] using h)
    (fun _ _ _ v c h ↦ by simpa [eval] using h)
    (fun n env o ts ih v c h ↦ by
      simp only [eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists,
        Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨vs, c₁, hl, w, d, ho, rfl, rfl⟩ := h
      simp [eval, evalList_le (m := c₁ + d) (by omega) (ih _ _ hl), ho])
    (fun n env k ts ih v c h ↦ by
      simp only [eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists,
        Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨vs, c₁, hl, rfl, rfl⟩ := h
      simp [eval, evalList_le (m := c₁ + vs.length + 1) (by omega) (ih _ _ hl)])
    (fun n env i t ih v c h ↦ by
      simp only [eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at h
      obtain ⟨w, c₁, hl, h⟩ := h
      cases w with
      | ctor k fs =>
        simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
        obtain ⟨x, hx, rfl, rfl⟩ := h
        simp [eval, eval_le (m := c₁ + 1) (by omega) (ih _ _ hl), hx]
      | _ => simp at h)
    (fun n env t alts ih iha v c h ↦ by
      simp only [eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at h
      obtain ⟨w, c₁, hl, h⟩ := h
      cases w with
      | ctor k fs =>
        simp only [Option.bind_eq_some_iff, Prod.exists, Option.pure_def, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨w', d, ha, rfl, rfl⟩ := h
        have ha' := iha k fs _ _ ha
        have ha'' : evalAlt P (c₁ + d + 1) env fs k alts = some (w', d) := by
          clear * - ha'
          induction alts generalizing k with
          | nil => simp [evalAlt] at ha'
          | cons a as ih =>
            cases k with
            | zero => simp only [evalAlt] at ha' ⊢; exact eval_le (by omega) ha'
            | succ k => simp only [evalAlt] at ha' ⊢; exact ih k ha'
        simp [eval, eval_le (m := c₁ + d + 1) (by omega) (ih _ _ hl), ha'']
      | _ => simp at h)
    (fun n env t b ih ihb v c h ↦ by
      simp only [eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists,
        Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨w, c₁, hl, w', d, hb, rfl, rfl⟩ := h
      simp [eval, eval_le (m := c₁ + d + 1) (by omega) (ih _ _ hl),
        eval_le (m := c₁ + d + 1) (by omega) (ihb _ _ _ hb)])
    (fun n env f ts ih ihb v c h ↦ by
      simp only [eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists,
        Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨vs, c₁, hl, w, d, hb, rfl, rfl⟩ := h
      simp [eval, evalList_le (m := c₁ + d + 1) (by omega) (ih _ _ hl),
        evalBody_le (m := c₁ + d + 1) (by omega) (ihb _ _ _ hb)])
    (fun n env f ts ih v c h ↦ by
      simp only [eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists,
        Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨vs, c₁, hl, rfl, rfl⟩ := h
      simp [eval, evalList_le (m := c₁ + vs.length + 1) (by omega) (ih _ _ hl)])
    (fun n env t ts ih ihl ihb v c h ↦ by
      simp only [eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at h
      obtain ⟨g, c₁, hg, vs, d, hl, h⟩ := h
      cases g with
      | fn f us =>
        simp only [Option.bind_eq_some_iff, Prod.exists, Option.pure_def, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨w, e, hb, rfl, rfl⟩ := h
        simp [eval, eval_le (m := c₁ + d + e + 1) (by omega) (ih _ _ hg),
          evalList_le (m := c₁ + d + e + 1) (by omega) (ihl _ _ hl),
          evalBody_le (m := c₁ + d + e + 1) (by omega) (ihb vs f us _ _ hb)]
      | _ => simp at h)
    (fun _ _ _ _ h ↦ by simp [evalBody] at h)
    (fun n f vs b hb ih v c h ↦ by
      simp only [evalBody, hb] at h ⊢
      exact ih _ _ h)
    (fun n f vs hb v c h ↦ by simp [evalBody, hb] at h)
    (fun _ _ _ _ v c h ↦ by simp [evalAlt] at h)
    (fun n env fs a tail ih v c h ↦ by
      simp only [evalAlt] at h ⊢
      exact ih _ _ h)
    (fun n env fs k head as ih v c h ↦ by
      simp only [evalAlt] at h ⊢
      exact ih _ _ h)
    (fun _ _ vs c h ↦ by simpa [evalList] using h)
    (fun n env t ts ih ihl vs c h ↦ by
      simp only [evalList, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists,
        Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨v, c₁, hv, vs', d, hl, rfl, rfl⟩ := h
      simp [evalList, eval_le (m := c₁ + d) (by omega) (ih _ _ hv),
        evalList_le (m := c₁ + d) (by omega) (ihl _ _ hl)])
  exact ⟨h.1, h.2.2.2, h.2.2.1, h.2.1⟩

/-- **A run within the budget outputs its value.** -/
theorem outputWithin_of_runs {P : Program} {x v : Val} {c b : ℕ} (h : RunsBody P 0 [x] v c)
    (hc : c ≤ b) : outputWithin P x b = some v := by
  obtain ⟨n, h⟩ := h
  have := evalBody_le (show c + 1 ≤ b + 1 by omega) ((eval_fuel P).2.2.2 _ _ _ _ _ h)
  simp [outputWithin, run, this, hc]

end

end LeanVM.Cost
