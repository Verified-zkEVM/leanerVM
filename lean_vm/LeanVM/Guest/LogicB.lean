/-
  LeanVM.Guest.LogicB

  The program logic of `Logic.lean` under any semantics of `BLAKE2S`: the same lemmas over
  `runB S`, the deployed ones at `blakeDeployed`.
-/

module

public import LeanVM.Guest.Logic
public import LeanVM.Spec.IsaWith

/-!
# The program logic under any `BLAKE2S` semantics

`Logic.lean` over the run of `Spec/IsaWith.lean` (`runB S`), each definition and lemma renamed
with a `B` (`HoldsB`, `SafeB`, `FunSpecLtB`, `funSpecB_induction`, `ReachB`, …) and proved as
there. Only `HoldsB`'s `BLAKE2S` case differs: it asks `S.check` of the nine cells. A run of a
valid execution under `S` starts at `(g^0, 1)` (`safeB_of_validExecutionB`).
-/

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-! ## The run under `S` -/

/-- `execute` under the semantics `S`. -/
noncomputable def executeB (S : BlakeSem) {κ : ℕ} (L : MemImage κ) (r : Regs K) :
    Instr → Option (Regs K) :=
  executeWithB S L.read r

section RunB

variable {S : BlakeSem} {κ : ℕ} {prog : Program} {L : MemImage κ}

theorem stepB_of_fetch_eq_some {r : Regs K} {ins : Instr} (h : prog.fetch r.pc = some ins) :
    stepB S prog L r = executeB S L r ins := by
  rw [stepB, h]; rfl

theorem runB_succ (n : ℕ) (r : Regs K) :
    runB S prog L (n + 1) r =
      if r.pc = prog.finalPc then none else stepB S prog L r >>= runB S prog L n :=
  rfl

theorem runB_succ_of_ne {r : Regs K} (h : r.pc ≠ prog.finalPc) (n : ℕ) :
    runB S prog L (n + 1) r = stepB S prog L r >>= runB S prog L n := by
  rw [runB_succ, ite_eq_right h]

theorem runB_succ_of_eq {r : Regs K} (h : r.pc = prog.finalPc) (n : ℕ) :
    runB S prog L (n + 1) r = none := by
  rw [runB_succ, ite_eq_left h]

theorem runB_add (m n : ℕ) (r : Regs K) :
    runB S prog L (m + n) r = runB S prog L m r >>= runB S prog L n := by
  induction m generalizing r with
  | zero => simp [runB]
  | succ m ih =>
    rw [show m + 1 + n = m + n + 1 by omega, runB_succ, runB_succ]
    split_ifs
    · rfl
    · rw [bind_assoc]
      exact bind_congr fun r' ↦ ih r'

end RunB

variable {S : BlakeSem}

/-! ## Definitions -/

section

variable {κ : ℕ} (prog : Program) (L : MemImage κ)

variable (S) in
/-- The run from `r` halts after exactly `k` steps. -/
def SafeB (k : ℕ) (r : Regs K) : Prop := runB S prog L k r = some (Regs.final prog)

variable (S) in
/-- What a non-`JUMP` instruction at `(g^pc, fp)` checks of the memory. -/
def HoldsB (pc : ℕ) (fp : K) : OInstr → Prop
  | .xor a b c => ∃ vA vB, L.read (fp * gpow a) = some vA ∧ L.read (fp * gpow b) = some vB ∧
      L.read (fp * gpow c) = some (vA + vB)
  | .mul a b c => ∃ vA vB, L.read (fp * gpow a) = some vA ∧ L.read (fp * gpow b) = some vB ∧
      L.read (fp * gpow c) = some (vA * vB)
  | .set o k0 k1 k2 => L.read (fp * gpow o) = some (OInstr.imm k0 k1 k2)
  | .deref o1 o2 o3 mode => ∃ p v3, L.read (fp * gpow o1) = some p ∧ IsInK p ∧
      L.read (fp * gpow o3) = some v3 ∧
      L.read (p.limb 0 * gpow o2) = some (derefSource mode ⟨gpow pc, fp⟩ v3)
  | .jump .. => False
  | .blake2s m0 m1 m2 m3 cv out md => ∃ w0 w1 w2 w3 c0 c1 d0 d1 v,
      L.read (fp * gpow m0) = some w0 ∧ L.read (fp * gpow m1) = some w1 ∧
      L.read (fp * gpow m2) = some w2 ∧ L.read (fp * gpow m3) = some w3 ∧
      L.read (fp * gpow cv) = some c0 ∧ L.read (fp * (g * gpow cv)) = some c1 ∧
      L.read (fp * gpow out) = some d0 ∧ L.read (fp * (g * gpow out)) = some d1 ∧
      L.read (fp * gpow md) = some v ∧ S.check ![w0, w1, w2, w3] c0 c1 d0 d1 v

variable (S) in
/-- **A function's contract, for runs shorter than `n`**: from `(g^entry, fp)` with `P fp`, a
run halting after `k < n` steps returns first, after fewer steps, to `retRegs L fp`, and
`Q fp` holds. -/
def FunSpecLtB (n entry : ℕ) (P Q : K → Prop) : Prop :=
  ∀ fp k, k < n → P fp → SafeB S prog L k ⟨gpow entry, fp⟩ →
    ∃ k' < k, ∃ r, retRegs L fp = some r ∧ Q fp ∧ SafeB S prog L k' r

variable (S) in
/-- **A function's contract**: from `(g^entry, fp)` with `P fp`, a run that halts returns first,
after fewer steps, to `retRegs L fp`, and `Q fp` holds. -/
def FunSpecB (entry : ℕ) (P Q : K → Prop) : Prop :=
  ∀ fp k, P fp → SafeB S prog L k ⟨gpow entry, fp⟩ →
    ∃ k' < k, ∃ r, retRegs L fp = some r ∧ Q fp ∧ SafeB S prog L k' r

variable (S) in
/-- Some run goes from `s` to `t`. -/
def ReachB (s t : Regs K) : Prop := ∃ n, runB S prog L n s = some t

variable (S) in
/-- From `(g^entry, fp)`, a run returns to `retRegs L fp`. -/
def ReturnsB (entry : ℕ) (fp : K) : Prop :=
  ∃ r, retRegs L fp = some r ∧ ReachB S prog L ⟨gpow entry, fp⟩ r

end

/-! ## Instructions -/

section

variable {κ : ℕ} {prog : Program} {L : MemImage κ}

private theorem guard_eq_some_iff {p : Prop} [Decidable p] {u : Unit} :
    (guard p : Option Unit) = some u ↔ p := by
  unfold guard
  split_ifs with h <;> simp [h]

/-- A non-`JUMP` instruction executes exactly when it `HoldsB`, and falls through. -/
theorem executeB_iff_holds {pc : ℕ} {fp : K} {ins : OInstr} (hj : ins.isJump = false)
    {r : Regs K} :
    executeB S L ⟨gpow pc, fp⟩ ins.toInstr = some r ↔ HoldsB S L pc fp ins ∧ r = ⟨gpow (pc + 1), fp⟩ := by
  have hnext : (⟨gpow pc, fp⟩ : Regs K).next = ⟨gpow (pc + 1), fp⟩ := by
    rw [Regs.next, gpow_succ]
  cases ins with
  | jump => simp [OInstr.isJump] at hj
  | xor a b c =>
    simp only [executeB, executeWithB, OInstr.toInstr, HoldsB, Option.bind_eq_bind,
      Option.bind_eq_some_iff, guard_eq_some_iff, exists_const, Option.pure_def, Option.some.injEq, hnext]
    constructor
    · rintro ⟨vA, hA, vB, hB, vC, hC, rfl, rfl⟩
      exact ⟨⟨vA, vB, hA, hB, hC⟩, rfl⟩
    · rintro ⟨⟨vA, vB, hA, hB, hC⟩, rfl⟩
      exact ⟨vA, hA, vB, hB, _, hC, rfl, rfl⟩
  | mul a b c =>
    simp only [executeB, executeWithB, OInstr.toInstr, HoldsB, Option.bind_eq_bind,
      Option.bind_eq_some_iff, guard_eq_some_iff, exists_const, Option.pure_def, Option.some.injEq, hnext]
    constructor
    · rintro ⟨vA, hA, vB, hB, vC, hC, rfl, rfl⟩
      exact ⟨⟨vA, vB, hA, hB, hC⟩, rfl⟩
    · rintro ⟨⟨vA, vB, hA, hB, hC⟩, rfl⟩
      exact ⟨vA, hA, vB, hB, _, hC, rfl, rfl⟩
  | set o k0 k1 k2 =>
    simp only [executeB, executeWithB, OInstr.toInstr, HoldsB, Option.bind_eq_bind,
      Option.bind_eq_some_iff, guard_eq_some_iff, exists_const, Option.pure_def, Option.some.injEq, hnext]
    constructor
    · rintro ⟨v, hv, rfl, rfl⟩
      exact ⟨hv, rfl⟩
    · rintro ⟨hv, rfl⟩
      exact ⟨_, hv, rfl, rfl⟩
  | deref o1 o2 o3 mode =>
    simp only [executeB, executeWithB, OInstr.toInstr, HoldsB, Option.bind_eq_bind,
      Option.bind_eq_some_iff, guard_eq_some_iff, exists_const, Option.pure_def, Option.some.injEq, hnext]
    constructor
    · rintro ⟨p, hp, hpK, v3, h3, v2, h2, rfl, rfl⟩
      exact ⟨⟨p, v3, hp, hpK, h3, h2⟩, rfl⟩
    · rintro ⟨⟨p, v3, hp, hpK, h3, h2⟩, rfl⟩
      exact ⟨p, hp, hpK, v3, h3, _, h2, rfl, rfl⟩
  | blake2s m0 m1 m2 m3 cv out md =>
    simp only [executeB, executeWithB, OInstr.toInstr, HoldsB, Option.bind_eq_bind,
      Option.bind_eq_some_iff, guard_eq_some_iff, exists_const, Option.pure_def, Option.some.injEq, hnext,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons]
    constructor
    · rintro ⟨w0, h0, w1, h1, w2, h2, w3, h3, c0, hc0, c1, hc1, d0, hd0, d1, hd1, v, hv, hcomp,
        rfl⟩
      exact ⟨⟨w0, w1, w2, w3, c0, c1, d0, d1, v, h0, h1, h2, h3, hc0, hc1, hd0, hd1, hv, hcomp⟩,
        rfl⟩
    · rintro ⟨⟨w0, w1, w2, w3, c0, c1, d0, d1, v, h0, h1, h2, h3, hc0, hc1, hd0, hd1, hv, hcomp⟩,
        rfl⟩
      exact ⟨w0, h0, w1, h1, w2, h2, w3, h3, c0, hc0, c1, hc1, d0, hd0, d1, hd1, v, hv, hcomp,
        rfl⟩

/-- A `JUMP` executes exactly when its reads are in `K`, to where `JumpsTo` says. -/
theorem executeB_jump_iff {pc : ℕ} {fp : K} {oc od of : ℕ} {r : Regs K} :
    executeB S L ⟨gpow pc, fp⟩ (OInstr.jump oc od of).toInstr = some r ↔
      JumpsTo L pc fp oc od of r := by
  have hnext : (⟨gpow pc, fp⟩ : Regs K).next = ⟨gpow (pc + 1), fp⟩ := by
    rw [Regs.next, gpow_succ]
  simp only [executeB, executeWithB, OInstr.toInstr, JumpsTo, Option.bind_eq_bind,
    Option.bind_eq_some_iff, guard_eq_some_iff, exists_const, Option.pure_def, Option.some.injEq, hnext]
  constructor
  · rintro ⟨c, hc, d, hd, f, hf, ⟨hcK, hdK, hfK⟩, rfl⟩
    exact ⟨c, d, f, hc, hd, hf, hcK, hdK, hfK, rfl⟩
  · rintro ⟨c, d, f, hc, hd, hf, hcK, hdK, hfK, rfl⟩
    exact ⟨c, hc, d, hd, f, hf, ⟨hcK, hdK, hfK⟩, rfl⟩

end

/-! ## Soundness: stepping a halting run -/

section

variable {κ : ℕ} {prog : Program} {L : MemImage κ}

theorem safeB_zero_iff {r : Regs K} : SafeB S prog L 0 r ↔ r = Regs.final prog := by
  simp [SafeB, runB]

theorem safeB_succ_iff {k : ℕ} {r : Regs K} :
    SafeB S prog L (k + 1) r ↔
      r.pc ≠ prog.finalPc ∧ ∃ r', stepB S prog L r = some r' ∧ SafeB S prog L k r' := by
  unfold SafeB
  by_cases h : r.pc = prog.finalPc
  · simp [runB_succ_of_eq h, h]
  · simp [runB_succ_of_ne h, h, Option.bind_eq_some_iff]

/-- A halting run from a fetched instruction away from the last slot takes a step. -/
theorem SafeB.step {pc k : ℕ} {fp : K} {ins : OInstr}
    (hf : prog.fetch (gpow pc) = some ins.toInstr) (hpc : pc < 2 ^ prog.logSize - 1)
    (h : SafeB S prog L k ⟨gpow pc, fp⟩) :
    ∃ k' r, k = k' + 1 ∧ executeB S L ⟨gpow pc, fp⟩ ins.toInstr = some r ∧ SafeB S prog L k' r := by
  cases k with
  | zero =>
    have := congrArg Regs.pc (safeB_zero_iff.mp h)
    exact absurd this (gpow_ne_finalPc hpc)
  | succ k =>
    obtain ⟨-, r, hr, hs⟩ := safeB_succ_iff.mp h
    rw [stepB_of_fetch_eq_some hf] at hr
    exact ⟨k, r, rfl, hr, hs⟩

/-- Through a non-`JUMP`: it `HoldsB`, and the run goes on at the next pc. -/
theorem SafeB.fallThrough {pc k : ℕ} {fp : K} {ins : OInstr}
    (hf : prog.fetch (gpow pc) = some ins.toInstr) (hpc : pc < 2 ^ prog.logSize - 1)
    (hj : ins.isJump = false) (h : SafeB S prog L k ⟨gpow pc, fp⟩) :
    ∃ k', k = k' + 1 ∧ HoldsB S L pc fp ins ∧ SafeB S prog L k' ⟨gpow (pc + 1), fp⟩ := by
  obtain ⟨k', r, rfl, hr, hs⟩ := h.step hf hpc
  obtain ⟨hh, rfl⟩ := (executeB_iff_holds hj).mp hr
  exact ⟨k', rfl, hh, hs⟩

/-- Through a `JUMP`: the run goes on where it `JumpsTo`. -/
theorem SafeB.jump {pc k : ℕ} {fp : K} {oc od of : ℕ}
    (hf : prog.fetch (gpow pc) = some (OInstr.jump oc od of).toInstr)
    (hpc : pc < 2 ^ prog.logSize - 1) (h : SafeB S prog L k ⟨gpow pc, fp⟩) :
    ∃ k' r, k = k' + 1 ∧ JumpsTo L pc fp oc od of r ∧ SafeB S prog L k' r := by
  obtain ⟨k', r, rfl, hr, hs⟩ := h.step hf hpc
  exact ⟨k', r, rfl, executeB_jump_iff.mp hr, hs⟩

/-- Through a taken `JUMP` whose target cells hold `a` and `b`: the run goes on at `(a, b)`. The
facts about the cells may come from anywhere: the code before, a precondition, a callee's
postcondition (a dispatch's target read from a table at a selector bounded by any of them). -/
theorem SafeB.jumpTo {pc k oc od of : ℕ} {fp a b : K} {c : E}
    (hf : prog.fetch (gpow pc) = some (OInstr.jump oc od of).toInstr)
    (hpc : pc < 2 ^ prog.logSize - 1) (hc : L.read (fp * gpow oc) = some c) (hc0 : c ≠ 0)
    (hd : L.read (fp * gpow od) = some (ofK a)) (hf' : L.read (fp * gpow of) = some (ofK b))
    (h : SafeB S prog L k ⟨gpow pc, fp⟩) : ∃ k', k = k' + 1 ∧ SafeB S prog L k' ⟨a, b⟩ := by
  obtain ⟨k', r, rfl, ⟨c', d, f, hc', hd', hf'', -, -, -, rfl⟩, hs⟩ := h.jump hf hpc
  obtain rfl : c' = c := Option.some.inj (hc'.symm.trans hc)
  obtain rfl : d = ofK a := Option.some.inj (hd'.symm.trans hd)
  obtain rfl : f = ofK b := Option.some.inj (hf''.symm.trans hf')
  rw [ite_eq_right hc0] at hs
  exact ⟨k', rfl, by simpa using hs⟩

/-- Through a `JUMP` not taken, `fp[oc] = 0`: the run goes on at the next pc. -/
theorem SafeB.jumpNot {pc k oc od of : ℕ} {fp : K}
    (hf : prog.fetch (gpow pc) = some (OInstr.jump oc od of).toInstr)
    (hpc : pc < 2 ^ prog.logSize - 1) (hc : L.read (fp * gpow oc) = some 0)
    (h : SafeB S prog L k ⟨gpow pc, fp⟩) : ∃ k', k = k' + 1 ∧ SafeB S prog L k' ⟨gpow (pc + 1), fp⟩ := by
  obtain ⟨k', r, rfl, ⟨c', d, f, hc', -, -, -, -, -, rfl⟩, hs⟩ := h.jump hf hpc
  obtain rfl : c' = 0 := Option.some.inj (hc'.symm.trans hc)
  rw [ite_eq_left rfl] at hs
  exact ⟨k', rfl, hs⟩

/-- Through a return, `JUMP fp[oc], fp[0], fp[1]` with `fp[oc] ≠ 0`: the run goes on at
`retRegs L fp`. -/
theorem SafeB.ret {pc k oc : ℕ} {fp : K} {c : E}
    (hf : prog.fetch (gpow pc) = some (OInstr.jump oc 0 1).toInstr)
    (hpc : pc < 2 ^ prog.logSize - 1) (hc : L.read (fp * gpow oc) = some c) (hc0 : c ≠ 0)
    (h : SafeB S prog L k ⟨gpow pc, fp⟩) :
    ∃ k', k = k' + 1 ∧ ∃ r, retRegs L fp = some r ∧ SafeB S prog L k' r := by
  obtain ⟨k', r, rfl, ⟨c', d, f, hc', hd, hf', -, -, -, rfl⟩, hs⟩ := h.jump hf hpc
  obtain rfl : c' = c := Option.some.inj (hc'.symm.trans hc)
  rw [ite_eq_right hc0] at hs
  exact ⟨k', rfl, _, retRegs_eq_some_iff.mpr ⟨d, f, hd, hf', rfl⟩, hs⟩

/-- A halting run of a valid execution starts at `(g^0, 1)`. -/
theorem safeB_of_validExecution {input : PublicInput} {t : Trace prog}
    (h : ValidExecutionB S prog input t) : SafeB S prog t.image t.steps ⟨gpow 0, 1⟩ := by
  have : (⟨gpow 0, 1⟩ : Regs K) = Regs.initial := by rw [gpow, pow_zero]; rfl
  rw [this]
  exact h.2

end

/-! ## Soundness: contracts -/

section

variable {κ : ℕ} {prog : Program} {L : MemImage κ} {entry : ℕ} {P Q : K → Prop}

theorem FunSpecB.lt (h : FunSpecB S prog L entry P Q) (n : ℕ) : FunSpecLtB S prog L n entry P Q :=
  fun fp k _ hP hs ↦ h fp k hP hs

theorem FunSpecB.of_lt (h : ∀ n, FunSpecLtB S prog L n entry P Q) : FunSpecB S prog L entry P Q :=
  fun fp k hP hs ↦ h (k + 1) fp k (Nat.lt_succ_self k) hP hs

theorem FunSpecLtB.mono {m n : ℕ} (hmn : m ≤ n) (h : FunSpecLtB S prog L n entry P Q) :
    FunSpecLtB S prog L m entry P Q :=
  fun fp k hk hP hs ↦ h fp k (Nat.lt_of_lt_of_le hk hmn) hP hs

/-- **Strong induction on the steps left**, for a family of contracts proved together: assuming
every contract for runs shorter than `n`, prove each for runs shorter than `n + 1`. -/
theorem funSpecB_induction {ι : Type} {entry : ι → ℕ} {P Q : ι → K → Prop}
    (h : ∀ n, (∀ j, FunSpecLtB S prog L n (entry j) (P j) (Q j)) →
      ∀ i, FunSpecLtB S prog L (n + 1) (entry i) (P i) (Q i))
    (i : ι) : FunSpecB S prog L (entry i) (P i) (Q i) := by
  have hall : ∀ n j, FunSpecLtB S prog L n (entry j) (P j) (Q j) := by
    intro n
    induction n with
    | zero => exact fun _ _ _ hk ↦ absurd hk (Nat.not_lt_zero _)
    | succ n ih => exact h n ih
  exact FunSpecB.of_lt (fun n ↦ hall n i)

/-- **A call**: a halting run entering a function at frame `fp'` after the caller stored the
return registers `r` in `fp'[0]`, `fp'[1]` comes back to `r`, in fewer steps, with `Q fp'`. -/
theorem FunSpecLtB.call {n k : ℕ} {fp' : K} {r : Regs K} (hS : FunSpecLtB S prog L n entry P Q)
    (hk : k < n) (hP : P fp') (hret : retRegs L fp' = some r)
    (h : SafeB S prog L k ⟨gpow entry, fp'⟩) : ∃ k' < k, Q fp' ∧ SafeB S prog L k' r := by
  obtain ⟨k', hk', r', hr', hQ, hs⟩ := hS fp' k hk hP h
  obtain rfl : r' = r := Option.some.inj (hr'.symm.trans hret)
  exact ⟨k', hk', hQ, hs⟩

/-- **A tail call**: a loop iteration at frame `fp` jumping to the loop's entry at the next
frame `fp'`, which returns where `fp` does, returns where `fp` does. -/
theorem FunSpecLtB.tail {n k : ℕ} {fp fp' : K} (hS : FunSpecLtB S prog L n entry P Q) (hk : k < n)
    (hP : P fp') (hret : retRegs L fp' = retRegs L fp) (h : SafeB S prog L k ⟨gpow entry, fp'⟩) :
    ∃ k' < k, ∃ r, retRegs L fp = some r ∧ Q fp' ∧ SafeB S prog L k' r := by
  obtain ⟨k', hk', r, hr, hQ, hs⟩ := hS fp' k hk hP h
  exact ⟨k', hk', r, hret ▸ hr, hQ, hs⟩

/-- `FunSpecLtB.call` for a contract already proved. -/
theorem FunSpecB.call {k : ℕ} {fp' : K} {r : Regs K} (hS : FunSpecB S prog L entry P Q)
    (hP : P fp') (hret : retRegs L fp' = some r) (h : SafeB S prog L k ⟨gpow entry, fp'⟩) :
    ∃ k' < k, Q fp' ∧ SafeB S prog L k' r :=
  (hS.lt (k + 1)).call (Nat.lt_succ_self k) hP hret h

end

/-! ## Completeness: building a run -/

section

variable {κ : ℕ} {prog : Program} {L : MemImage κ}

theorem ReachB.refl (s : Regs K) : ReachB S prog L s s := ⟨0, rfl⟩

theorem ReachB.trans {s t u : Regs K} (h₁ : ReachB S prog L s t) (h₂ : ReachB S prog L t u) :
    ReachB S prog L s u := by
  obtain ⟨m, hm⟩ := h₁
  obtain ⟨n, hn⟩ := h₂
  exact ⟨m + n, by rw [runB_add, hm]; exact hn⟩

/-- One step from a fetched instruction away from the last slot. -/
theorem reachB_step {pc : ℕ} {fp : K} {ins : OInstr} {r : Regs K}
    (hf : prog.fetch (gpow pc) = some ins.toInstr) (hpc : pc < 2 ^ prog.logSize - 1)
    (h : executeB S L ⟨gpow pc, fp⟩ ins.toInstr = some r) : ReachB S prog L ⟨gpow pc, fp⟩ r := by
  refine ⟨1, ?_⟩
  rw [runB_succ_of_ne (gpow_ne_finalPc hpc), stepB_of_fetch_eq_some hf, h]
  rfl

/-- A non-`JUMP` that `HoldsB` falls through. -/
theorem reachB_fallThrough {pc : ℕ} {fp : K} {ins : OInstr}
    (hf : prog.fetch (gpow pc) = some ins.toInstr) (hpc : pc < 2 ^ prog.logSize - 1)
    (hj : ins.isJump = false) (h : HoldsB S L pc fp ins) :
    ReachB S prog L ⟨gpow pc, fp⟩ ⟨gpow (pc + 1), fp⟩ :=
  reachB_step hf hpc ((executeB_iff_holds hj).mpr ⟨h, rfl⟩)

/-- A `JUMP` goes where it `JumpsTo`. -/
theorem reachB_jump {pc : ℕ} {fp : K} {oc od of : ℕ} {r : Regs K}
    (hf : prog.fetch (gpow pc) = some (OInstr.jump oc od of).toInstr)
    (hpc : pc < 2 ^ prog.logSize - 1) (h : JumpsTo L pc fp oc od of r) :
    ReachB S prog L ⟨gpow pc, fp⟩ r :=
  reachB_step hf hpc (executeB_jump_iff.mpr h)

/-- A taken `JUMP` whose target cells hold `a` and `b` goes to `(a, b)`. -/
theorem reachB_jumpTo {pc oc od of : ℕ} {fp a b : K} {c : E}
    (hf : prog.fetch (gpow pc) = some (OInstr.jump oc od of).toInstr)
    (hpc : pc < 2 ^ prog.logSize - 1) (hc : L.read (fp * gpow oc) = some c) (hcK : IsInK c)
    (hc0 : c ≠ 0) (hd : L.read (fp * gpow od) = some (ofK a))
    (hf' : L.read (fp * gpow of) = some (ofK b)) : ReachB S prog L ⟨gpow pc, fp⟩ ⟨a, b⟩ := by
  have hK : ∀ x : K, IsInK (ofK x) := fun x ↦ (isInK_iff _).mpr ⟨x, rfl⟩
  have := reachB_jump (S := S) (L := L) hf hpc ⟨c, _, _, hc, hd, hf', hcK, hK a, hK b, rfl⟩
  rw [ite_eq_right hc0] at this
  simpa using this

/-- A return, `JUMP fp[oc], fp[0], fp[1]` with `fp[oc]` a nonzero `K` word and `fp[0]`,
`fp[1]` words of `K`, goes to `retRegs L fp`. -/
theorem reachB_ret {pc oc : ℕ} {fp : K} {c d f : E} {r : Regs K}
    (hf : prog.fetch (gpow pc) = some (OInstr.jump oc 0 1).toInstr)
    (hpc : pc < 2 ^ prog.logSize - 1) (hc : L.read (fp * gpow oc) = some c) (hcK : IsInK c)
    (hc0 : c ≠ 0) (hd : L.read (fp * gpow 0) = some d) (hdK : IsInK d)
    (hf' : L.read (fp * gpow 1) = some f) (hfK : IsInK f) (hr : retRegs L fp = some r) :
    ReachB S prog L ⟨gpow pc, fp⟩ r := by
  obtain ⟨d', f', hd', hf'', rfl⟩ := retRegs_eq_some_iff.mp hr
  obtain rfl : d' = d := Option.some.inj (hd'.symm.trans hd)
  obtain rfl : f' = f := Option.some.inj (hf''.symm.trans hf')
  exact reachB_jump hf hpc ⟨c, d', f', hc, hd, hf', hcK, hdK, hfK, by rw [ite_eq_right hc0]⟩

/-- **A call**, for completeness: a function that returns from frame `fp'`, whose `fp'[0]`,
`fp'[1]` hold `r`, reaches `r`. -/
theorem ReturnsB.reach {entry : ℕ} {fp' : K} {r : Regs K} (h : ReturnsB S prog L entry fp')
    (hret : retRegs L fp' = some r) : ReachB S prog L ⟨gpow entry, fp'⟩ r := by
  obtain ⟨r', hr', hreach⟩ := h
  obtain rfl : r' = r := Option.some.inj (hr'.symm.trans hret)
  exact hreach

/-- **Strong induction on a measure**, for a family of functions shown to return together:
assuming every call of a smaller measure returns, show that each call returns. -/
theorem returnsB_induction {ι : Type} {entry : ι → ℕ} {P : ι → K → Prop} (μ : ι → K → ℕ)
    (h : ∀ i fp, P i fp → (∀ j fp', μ j fp' < μ i fp → P j fp' → ReturnsB S prog L (entry j) fp') →
      ReturnsB S prog L (entry i) fp)
    (i : ι) (fp : K) (hP : P i fp) : ReturnsB S prog L (entry i) fp := by
  have hall : ∀ m j fp', μ j fp' < m → P j fp' → ReturnsB S prog L (entry j) fp' := by
    intro m
    induction m with
    | zero => exact fun _ _ hm ↦ absurd hm (Nat.not_lt_zero _)
    | succ m ih =>
      exact fun j fp' hm hP' ↦ h j fp' hP' fun j' fp'' hlt hP'' ↦ ih j' fp'' (by omega) hP''
  exact hall _ i fp (Nat.lt_succ_self _) hP

/-- A run from `(g^0, 1)` to the final registers, on a memory holding the public input, is a
valid execution. -/
theorem validExecutionB_of_reach {input : PublicInput}
    (hb : HasPublicBoundary input (⟨κ, L, 0⟩ : Trace prog))
    (h : ReachB S prog L ⟨gpow 0, 1⟩ (Regs.final prog)) :
    ∃ n, ValidExecutionB S prog input ⟨κ, L, n⟩ := by
  obtain ⟨n, hn⟩ := h
  have : (⟨gpow 0, 1⟩ : Regs K) = Regs.initial := by rw [gpow, pow_zero]; rfl
  rw [this] at hn
  exact ⟨n, hb, hn⟩

end

end
end LeanVM.Guest
