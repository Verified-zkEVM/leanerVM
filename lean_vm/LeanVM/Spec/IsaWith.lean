/-
  LeanVM.Spec.IsaWith

  leanISA with the relation `BLAKE2S` checks a parameter: the deployed machine at the compression
  function, the Flock-blind machine at canonical cells.
-/

module

public import LeanVM.Spec.Isa

namespace LeanVM.Semantics

open LeanVM.Parameters

@[expose] public section

/-!
# Executions under any `BLAKE2S` semantics

The relation `BLAKE2S` checks of its nine cells is a parameter of the machine here (`BlakeSem`):
the deployed one, `blakeDeployed`, is `CompressCells`; the Flock-blind one, `blakeFree`, only
asks the cells to be canonical (what the bus enforces of a `BLAKE2S` row when the proof does not
bind the row to the compression function). Every definition
below is the one above with the check replaced, and is the one above at `blakeDeployed`
(`executeWithB_deployed`, `runB_deployed`, `validExecutionB_deployed`). -/

/-- **A semantics of `BLAKE2S`**: the relation of the message, chaining-value, output and
metadata cells, decidable. -/
structure BlakeSem where
  /-- The relation. -/
  check : (Fin 4 → E) → E → E → E → E → E → Prop
  /-- It is decidable. -/
  dec : ∀ m cv0 cv1 out0 out1 md, Decidable (check m cv0 cv1 out0 out1 md)

/-- The deployed semantics: the compression function (`CompressCells`). -/
def blakeDeployed : BlakeSem := ⟨CompressCells, fun _ _ _ _ _ _ ↦ inferInstance⟩

/-- The nine cells are canonical (no `y²` term): all `blakeFree` asks. -/
def CanonicalCells (m : Fin 4 → E) (cv0 cv1 out0 out1 md : E) : Prop :=
  (∀ i, IsCanonical128 (m i)) ∧ IsCanonical128 cv0 ∧ IsCanonical128 cv1 ∧
    IsCanonical128 out0 ∧ IsCanonical128 out1 ∧ IsCanonical128 md

instance {m : Fin 4 → E} {cv0 cv1 out0 out1 md : E} :
    Decidable (CanonicalCells m cv0 cv1 out0 out1 md) := by
  unfold CanonicalCells; infer_instance

/-- **The Flock-blind semantics**: any canonical output. -/
def blakeFree : BlakeSem := ⟨CanonicalCells, fun _ _ _ _ _ _ ↦ inferInstance⟩

/-- The deployed check implies the Flock-blind one. -/
theorem canonicalCells_of_compressCells {m : Fin 4 → E} {cv0 cv1 out0 out1 md : E}
    (h : CompressCells m cv0 cv1 out0 out1 md) : CanonicalCells m cv0 cv1 out0 out1 md :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

/-- `executeWith` under the semantics `S`. -/
def executeWithB (S : BlakeSem) (read : K → Option E) (r : Regs K) : Instr → Option (Regs K)
  | .xor oA oB oC => do
    let vA ← read (r.fp * oA)
    let vB ← read (r.fp * oB)
    let vC ← read (r.fp * oC)
    guard (vC = vA + vB)
    pure r.next
  | .mulNative oA oB oC => do
    let vA ← read (r.fp * oA)
    let vB ← read (r.fp * oB)
    let vC ← read (r.fp * oC)
    guard (vC = vA * vB)
    pure r.next
  | .setConstant o k => do
    let v ← read (r.fp * o)
    guard (v = k)
    pure r.next
  | .deref o1 o2 o3 mode => do
    let p ← read (r.fp * o1)
    guard (IsInK p)
    let v3 ← read (r.fp * o3)
    let v2 ← read (p.limb 0 * o2)
    guard (v2 = derefSource mode r v3)
    pure r.next
  | .jump oc od of => do
    let c ← read (r.fp * oc)
    let d ← read (r.fp * od)
    let f ← read (r.fp * of)
    guard (IsInK c ∧ IsInK d ∧ IsInK f)
    pure (if c = 0 then r.next else ⟨d.limb 0, f.limb 0⟩)
  | .blake2s om ocv oout omd => do
    let m0 ← read (r.fp * om 0)
    let m1 ← read (r.fp * om 1)
    let m2 ← read (r.fp * om 2)
    let m3 ← read (r.fp * om 3)
    let cv0 ← read (r.fp * ocv)
    let cv1 ← read (r.fp * (g * ocv))
    let out0 ← read (r.fp * oout)
    let out1 ← read (r.fp * (g * oout))
    let md ← read (r.fp * omd)
    @guard Option _ (S.check ![m0, m1, m2, m3] cv0 cv1 out0 out1 md)
      (S.dec ![m0, m1, m2, m3] cv0 cv1 out0 out1 md)
    pure r.next

/-- One step under the semantics `S`. -/
noncomputable def stepB (S : BlakeSem) {κ : ℕ} (prog : Program) (L : MemImage κ) (r : Regs K) :
    Option (Regs K) :=
  prog.fetch r.pc >>= executeWithB S L.read r

/-- `n` steps under the semantics `S`. -/
noncomputable def runB (S : BlakeSem) {κ : ℕ} (prog : Program) (L : MemImage κ) :
    ℕ → Regs K → Option (Regs K)
  | 0, r => some r
  | n + 1, r => if r.pc = prog.finalPc then none else stepB S prog L r >>= runB S prog L n

/-- **A valid execution under the semantics `S`.** -/
def ValidExecutionB (S : BlakeSem) (prog : Program) (input : PublicInput) (t : Trace prog) :
    Prop :=
  HasPublicBoundary input t ∧ runB S prog t.image t.steps Regs.initial = some (Regs.final prog)

theorem executeWithB_deployed (read : K → Option E) (r : Regs K) (i : Instr) :
    executeWithB blakeDeployed read r i = executeWith read r i := by
  cases i <;> rfl

theorem stepB_deployed {κ : ℕ} (prog : Program) (L : MemImage κ) (r : Regs K) :
    stepB blakeDeployed prog L r = step prog L r := by
  have : executeWithB blakeDeployed L.read r = executeWith L.read r :=
    funext (executeWithB_deployed L.read r)
  simp only [stepB, step, execute, this]

theorem runB_deployed {κ : ℕ} (prog : Program) (L : MemImage κ) :
    ∀ (n : ℕ) (r : Regs K), runB blakeDeployed prog L n r = run prog L n r
  | 0, _ => rfl
  | n + 1, r => by
    have : runB blakeDeployed prog L n = run prog L n := funext (runB_deployed prog L n)
    simp only [runB, run, stepB_deployed, this]

/-- **The deployed semantics gives the deployed valid executions.** -/
theorem validExecutionB_deployed (prog : Program) (input : PublicInput) (t : Trace prog) :
    ValidExecutionB blakeDeployed prog input t ↔ ValidExecution prog input t := by
  simp only [ValidExecutionB, ValidExecution, runB_deployed]

end
end LeanVM.Semantics
