/-
  LeanerVM.Semantics.Executable

  Computable checking of the fixed-image leanISA semantics.
-/

module

public import LeanerVM.Semantics.Execution

/-!
# Executable fixed-image checking

A finite address search implements the bounded logarithm of `Semantics.Memory`.
The instruction evaluator uses that reader and is proved equal to the reference `execute`
for every instruction, register pair and image within the address bound. These are
implementation/refinement results for the leanISA semantics at leanVM revision
`a386121f84292f6fa663aaa3e570c15bc0240ea2`, not correctness of Rust witness generation.
The search is deliberately exhaustive; an absent cache entry cannot reject a valid address.
-/

namespace LeanerVM.Semantics

open LeanerVM.Parameters

@[expose] public section

/-- Search the selected finite address domain, returning its unique matching index.
The zero address is rejected before search. Running time is linear in the domain size,
with one generator-power comparison per candidate. -/
def addressIndex (κ : ℕ) (a : K) : Option (Fin (2 ^ κ)) :=
  if a = 0 then none else Fin.find? fun i ↦ decide (a = gpow i)

/-- Read a fixed image by exhaustive bounded-address lookup. -/
def readImage {κ : ℕ} (image : MemImage κ) (a : K) : Option E :=
  (addressIndex κ a).map image

/-- Fetch the typed instruction at a bounded program address. -/
def fetchInstruction (prog : Program) (pc : K) : Option Instr :=
  (addressIndex prog.logSize pc).map prog.code

/-- Execute the six instruction checks using a supplied memory reader. This computational
core is related to the reference semantics by `evaluateInstruction_read`; its reader never
allocates, fills, or changes memory. -/
def evaluateInstruction (read : K → Option E) (r : Regs K) : Instr → Option (Regs K)
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
    guard (CompressCells ![m0, m1, m2, m3] cv0 cv1 out0 out1 md)
    pure r.next


/-- Execute one instruction using the computable fixed-image reader. -/
def executeChecked {κ : ℕ} (image : MemImage κ) (r : Regs K) (ins : Instr) :
    Option (Regs K) :=
  evaluateInstruction (readImage image) r ins

/-- Fetch and check one step. Halting remains the responsibility of the execution loop. -/
def stepChecked {κ : ℕ} (prog : Program) (image : MemImage κ) (r : Regs K) :
    Option (Regs K) :=
  fetchInstruction prog r.pc >>= executeChecked image r

/-- Check exactly `n` transitions, failing if the sentinel is encountered earlier.
Zero steps always return the starting registers, including at the sentinel. -/
def runChecked {κ : ℕ} (prog : Program) (image : MemImage κ) :
    ℕ → Regs K → Option (Regs K)
  | 0, r => some r
  | n + 1, r =>
    if r.pc = prog.finalPc then none else stepChecked prog image r >>= runChecked prog image n

/-- The executable checks of the memory-size window and the two public words. -/
def checkBoundary {prog : Program} (input : PublicInput) (t : Trace prog) : Bool :=
  decide (minLogMem ≤ t.κ ∧ t.κ ≤ maxLogMem) &&
    decide (readImage t.image (gpow 0) = some input.word0 ∧
      readImage t.image (gpow 1) = some input.word1)

/-- Validate a claimed exact-length execution, including its public memory and final frame.
A successful witness generator must still establish that its output passes these checks. -/
def checkTrace (prog : Program) (input : PublicInput) (t : Trace prog) : Bool :=
  checkBoundary input t &&
    decide (runChecked prog t.image t.steps Regs.initial = some (Regs.final prog))

/-! ## Refinement to the reference semantics -/

/-- Bounded exhaustive search agrees with the chosen reference logarithm whenever the
address representation is injective on the selected domain. -/
theorem addressIndex_eq_gLog {κ : ℕ} (hκ : κ < 64) (a : K) :
    addressIndex κ a = gLog? κ a := by
  unfold addressIndex
  split_ifs with ha
  · rw [ha, gLog?_zero]
  · apply Option.ext
    intro i
    rw [gLog?_spec hκ, Fin.find?_eq_some_iff]
    simp only [decide_eq_true_eq, decide_eq_false_iff_not]
    refine ⟨And.left, fun hi ↦ ⟨hi, ?_⟩⟩
    intro j hji hj
    have bound : 2 ^ κ ≤ 2 ^ 63 :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have ib : (i : ℕ) < 2 ^ 64 - 1 := by have := i.isLt; omega
    have jb : (j : ℕ) < 2 ^ 64 - 1 := by have := j.isLt; omega
    have hji' : j = i := Fin.ext (gpow_injOn jb ib (hj.symm.trans hi))
    exact (ne_of_lt hji) hji'

/-- Executable reads preserve success, failure, and the exact word returned. -/
theorem readImage_eq_read {κ : ℕ} (hκ : κ < 64) (image : MemImage κ) (a : K) :
    readImage image a = image.read a := by
  rw [readImage, MemImage.read, addressIndex_eq_gLog hκ]

/-- Executable fetch agrees with typed reference fetch on every field address. -/
theorem fetchInstruction_eq_fetch (prog : Program) (pc : K) :
    fetchInstruction prog pc = prog.fetch pc := by
  have hκ : prog.logSize < 64 := lt_of_le_of_lt prog.logSize_le (by decide)
  rw [fetchInstruction, Program.fetch, addressIndex_eq_gLog hκ]

/-- The parameterized evaluator specializes exactly to the reference instruction relation. -/
theorem evaluateInstruction_read {κ : ℕ} (image : MemImage κ) (r : Regs K) (ins : Instr) :
    evaluateInstruction image.read r ins = execute image r ins := by
  cases ins <;> rfl

/-- Each executable instruction check is equal to the reference semantics. -/
theorem executeChecked_eq_execute {κ : ℕ} (hκ : κ < 64) (image : MemImage κ)
    (r : Regs K) (ins : Instr) : executeChecked image r ins = execute image r ins := by
  unfold executeChecked
  rw [show readImage image = image.read from funext (readImage_eq_read hκ image)]
  exact evaluateInstruction_read image r ins

/-- The checked program step has exactly the reference step's behavior. -/
theorem stepChecked_eq_step {κ : ℕ} (hκ : κ < 64) (prog : Program) (image : MemImage κ)
    (r : Regs K) : stepChecked prog image r = step prog image r := by
  unfold stepChecked step
  rw [fetchInstruction_eq_fetch,
    show executeChecked image r = execute image r from
      funext (executeChecked_eq_execute hκ image r)]

/-- Exact-step checking agrees with `run`, including zero steps and early halting. -/
theorem runChecked_eq_run {κ : ℕ} (hκ : κ < 64) (prog : Program) (image : MemImage κ)
    (n : ℕ) (r : Regs K) : runChecked prog image n r = run prog image n r := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    simp only [runChecked, run, stepChecked_eq_step hκ]
    rw [show runChecked prog image n = run prog image n from funext ih]

/-- Boundary checking is equivalent to the reference public boundary, including size caps. -/
theorem checkBoundary_eq_true_iff {prog : Program} (input : PublicInput) (t : Trace prog) :
    checkBoundary input t = true ↔ HasPublicBoundary input t := by
  simp only [checkBoundary, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hmin, hmax⟩, hwords⟩
    have hκ : t.κ < 64 := lt_of_le_of_lt hmax (by decide)
    rw [readImage_eq_read hκ, readImage_eq_read hκ] at hwords
    exact ⟨hmin, hmax, hwords⟩
  · rintro ⟨hmin, hmax, hwords⟩
    have hκ : t.κ < 64 := lt_of_le_of_lt hmax (by decide)
    rw [readImage_eq_read hκ, readImage_eq_read hκ]
    exact ⟨⟨hmin, hmax⟩, hwords⟩

/-- Exact checking accepts precisely the valid reference executions. The equivalence is
unconditional: the checker itself rejects sizes outside the public boundary. -/
theorem checkTrace_eq_true_iff (prog : Program) (input : PublicInput) (t : Trace prog) :
    checkTrace prog input t = true ↔ ValidExecution prog input t := by
  simp only [checkTrace, Bool.and_eq_true, checkBoundary_eq_true_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨hb, hr⟩
    have hκ : t.κ < 64 := lt_of_le_of_lt hb.2.1 (by decide)
    exact ⟨hb, (runChecked_eq_run hκ prog t.image t.steps Regs.initial) ▸ hr⟩
  · rintro ⟨hb, hr⟩
    have hκ : t.κ < 64 := lt_of_le_of_lt hb.2.1 (by decide)
    exact ⟨hb, (runChecked_eq_run hκ prog t.image t.steps Regs.initial).symm ▸ hr⟩

end
end LeanerVM.Semantics
